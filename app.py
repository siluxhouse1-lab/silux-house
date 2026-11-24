"""SILUX HOUSE (nom technique : SILUX HOUSE) : moteur Flask central.

Modules : Chat & Négociation, RFQ, Trade Assurance (séquestre CinetPay),
Sourcing IA (NLP SQLite), profils B2B, MOQ, suggestions prédictives.

Variables d'environnement :
  FLASK_SECRET_KEY, BASE_URL (https public), CINETPAY_API_KEY,
  CINETPAY_SITE_ID, CINETPAY_SECRET_KEY, SAHEL_DB_FILE, TRUST_PROXY=1,
  PENDING_PAYMENT_TTL_MINUTES (défaut 120), PASSWORD_ITERATIONS, PORT.
"""
import hashlib
import hmac
import json
import logging
import math
import os
import re
import secrets
import smtplib
import sqlite3
import threading
import time
import unicodedata
import uuid
from collections import defaultdict, deque
from contextlib import contextmanager
from datetime import datetime
from email.message import EmailMessage
from functools import wraps
from urllib.parse import urlparse

import requests
from flask import (
    Flask, render_template, request, redirect, url_for,
    flash, session, jsonify, abort, make_response
)
from itsdangerous import BadSignature, SignatureExpired, URLSafeTimedSerializer
from werkzeug.utils import secure_filename

# ============================================================================
# 1. CONFIGURATION
# ============================================================================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
UPLOAD_DIR = os.path.join(BASE_DIR, "static", "uploads")


def resolve_db_file():
    """Chemin de la base. Compatible avec l'ancien nom SAHEL_BOX_real.db."""
    explicit = os.environ.get("SAHEL_DB_FILE", "").strip()
    if explicit:
        return explicit
    for name in ("SAHEL_BOX_real.db", "sahel_box_real.db"):
        path = os.path.join(BASE_DIR, name)
        if os.path.exists(path):
            return path
    return os.path.join(BASE_DIR, "sahel_box_real.db")


DB_FILE = resolve_db_file()


def load_secret_key():
    """Clé de session stable : variable d'environnement, sinon fichier privé."""
    env_key = os.environ.get("FLASK_SECRET_KEY", "").strip()
    if env_key:
        return env_key
    path = os.path.join(BASE_DIR, ".flask_secret_key")
    try:
        with open(path, "r", encoding="utf-8") as fh:
            value = fh.read().strip()
        if len(value) >= 32:
            return value
    except OSError:
        pass
    value = secrets.token_hex(32)
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write(value)
    except OSError:
        logging.getLogger(__name__).warning(
            "Impossible d'enregistrer .flask_secret_key : définissez FLASK_SECRET_KEY.")
    return value


app = Flask(__name__)
app.config.update(
    SECRET_KEY=load_secret_key(),
    MAX_CONTENT_LENGTH=5 * 1024 * 1024,
    CINETPAY_API_KEY=os.environ.get("CINETPAY_API_KEY", ""),
    CINETPAY_SITE_ID=os.environ.get("CINETPAY_SITE_ID", ""),
    CINETPAY_SECRET_KEY=os.environ.get("CINETPAY_SECRET_KEY", ""),
    BASE_URL=os.environ.get("BASE_URL", "http://127.0.0.1:5000").rstrip("/"),
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.environ.get("BASE_URL", "").lower().startswith("https://"),
    PERMANENT_SESSION_LIFETIME=60 * 60 * 24 * 14,
)

if os.environ.get("TRUST_PROXY") == "1":
    from werkzeug.middleware.proxy_fix import ProxyFix
    app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1)

logging.basicConfig(level=logging.INFO)

CINETPAY_API_URL = "https://api-checkout.cinetpay.com/v2"
TRANSACTION_ID_RE = re.compile(r"^[A-Za-z0-9_-]{6,64}$")
PHONE_RE = re.compile(r"^[0-9+\s().-]{6,20}$")
# Routes appelées par CinetPay (serveur à serveur) : pas de jeton CSRF possible.
CSRF_EXEMPT_ENDPOINTS = {"payment_notify", "payment_return"}
UNSAFE_METHODS = {"POST", "PUT", "PATCH", "DELETE"}

os.makedirs(UPLOAD_DIR, exist_ok=True)
ALLOWED_EXTENSIONS = {"png", "jpg", "jpeg", "webp"}

MIN_PASSWORD_LEN = 8
PER_PAGE = 24
PASSWORD_ITERATIONS = int(os.environ.get("PASSWORD_ITERATIONS", "600000"))
LEGACY_ITERATIONS = 120000
PENDING_PAYMENT_TTL_MINUTES = int(os.environ.get("PENDING_PAYMENT_TTL_MINUTES", "120"))
QUOTE_VALIDITY_DAYS = 7
ESC = "ESCAPE '\\'"

COMPANY_TYPES = (
    "Grossiste", "Fabricant", "Distributeur", "Importateur",
    "Détaillant en ligne", "Détaillant en boutique", "Particulier",
)
SOURCING_PURPOSES = (
    "Revente", "Production", "Usage professionnel",
    "Usage personnel", "Cadeaux et événements",
)

# Cycle de vie financier (Trade Assurance)
#   pending -> escrowed -> released          (paiement en ligne)
#   pending -> paid                          (espèces encaissées à la livraison)
#   escrowed -> refund_due                   (annulation : remboursement à traiter)
PAID_STATES = frozenset({"paid", "escrowed", "released"})
FINAL_PAYMENT_STATES = PAID_STATES | {"refund_due"}
ORDER_STATUSES = ("pending", "confirmed", "processing", "shipped", "delivered", "cancelled")
SELLER_ALLOWED_STATUSES = frozenset({"processing", "shipped", "delivered", "cancelled"})
STATUS_LABELS = {
    "pending": "en attente", "confirmed": "confirmée", "processing": "en préparation",
    "shipped": "expédiée", "delivered": "livrée", "cancelled": "annulée",
}
MESSAGE_TABS = {"orders": "quote", "notification": "system", "other": "text"}
DISPUTE_REASONS = {
    "not_received": "Colis non reçu",
    "not_as_described": "Produit non conforme",
    "damaged": "Produit endommagé",
    "other": "Autre problème",
}

# ============================================================================
# 2. OUTILS GÉNÉRAUX
# ============================================================================


def fold_text(value):
    """Minuscule sans accents (utilisée aussi comme fonction SQLite fold())."""
    if value is None:
        return ""
    text = unicodedata.normalize("NFKD", str(value))
    return "".join(ch for ch in text if not unicodedata.combining(ch)).lower()


def get_db_connection():
    conn = sqlite3.connect(DB_FILE, timeout=15)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    conn.execute("PRAGMA busy_timeout = 15000")
    conn.create_function("fold", 1, fold_text, deterministic=True)
    return conn


@contextmanager
def connection():
    conn = get_db_connection()
    try:
        yield conn
    finally:
        conn.close()


@contextmanager
def immediate(conn):
    """Transaction à verrou d'écriture immédiat : tout ou rien."""
    conn.execute("BEGIN IMMEDIATE")
    try:
        yield conn
    except BaseException:
        conn.rollback()
        raise
    else:
        conn.commit()


def to_int(value, default=0):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def parse_amount(value):
    """Nombre fini ou None."""
    try:
        number = float(str(value).replace(" ", "").replace(",", "."))
    except (TypeError, ValueError):
        return None
    if not math.isfinite(number):
        return None
    return number


def clean_text(value, max_len):
    text = "".join(ch for ch in str(value or "") if ch == "\n" or ch >= " ")
    return text.strip()[:max_len]


def like_escape(value):
    return value.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")


def format_fcfa(value):
    try:
        return "{:,.0f}".format(float(value)).replace(",", " ")
    except (TypeError, ValueError):
        return "0"


app.add_template_filter(format_fcfa, "fcfa")


def valid_email(email):
    return len(email) <= 254 and bool(re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", email))


def allowed_file(filename):
    return "." in filename and filename.rsplit(".", 1)[1].lower() in ALLOWED_EXTENSIONS


def sniff_image_type(stream):
    """Vérifie la signature binaire réelle du fichier (pas seulement l'extension)."""
    head = stream.read(16)
    stream.seek(0)
    if head.startswith(b"\x89PNG\r\n\x1a\n"):
        return "png"
    if head[:3] == b"\xff\xd8\xff":
        return "jpg"
    if head[:4] == b"RIFF" and head[8:12] == b"WEBP":
        return "webp"
    return None


def safe_back(endpoint="home", **values):
    """Redirection vers la page précédente, uniquement si elle est sur ce site."""
    ref = request.referrer
    if ref:
        parsed = urlparse(ref)
        if parsed.netloc == request.host:
            target = parsed.path or "/"
            if parsed.query:
                target += "?" + parsed.query
            return redirect(target)
    return redirect(url_for(endpoint, **values))


def client_ip():
    return request.remote_addr or "unknown"


_rate_lock = threading.Lock()
_rate_hits = defaultdict(deque)


def rate_limited_shared(bucket, limit, window_seconds):
    """Limiteur partagé entre tous les processus (SQLite). True si dépassé."""
    now = time.time()
    try:
        with connection() as conn:
            with immediate(conn):
                if secrets.randbelow(100) == 0:
                    conn.execute("DELETE FROM rate_hits WHERE ts < ?", (now - 86400,))
                count = conn.execute(
                    "SELECT COUNT(*) FROM rate_hits WHERE bucket=? AND ts>?",
                    (bucket, now - window_seconds)).fetchone()[0]
                if count >= limit:
                    return True
                conn.execute("INSERT INTO rate_hits(bucket, ts) VALUES(?,?)", (bucket, now))
    except sqlite3.Error:
        return rate_limited(bucket, limit, window_seconds)
    return False


def rate_limited(bucket, limit, window_seconds, shared=False):
    """Limiteur en mémoire (par processus), ou partagé si shared=True."""
    if shared:
        return rate_limited_shared(bucket, limit, window_seconds)
    now = time.monotonic()
    with _rate_lock:
        hits = _rate_hits[bucket]
        while hits and now - hits[0] > window_seconds:
            hits.popleft()
        if len(hits) >= limit:
            return True
        hits.append(now)
        if len(_rate_hits) > 20000:
            for key in [k for k, v in _rate_hits.items() if not v]:
                del _rate_hits[key]
    return False


# ============================================================================
# 3. BASE DE DONNÉES
# ============================================================================
SCHEMA_ADDITIONS = {
    "users": [
        ("company_name", "TEXT NOT NULL DEFAULT ''"),
        ("company_type", "TEXT NOT NULL DEFAULT ''"),
        ("sourcing_purpose", "TEXT NOT NULL DEFAULT ''"),
        ("years_active", "INTEGER NOT NULL DEFAULT 0"),
        ("reorder_rate", "REAL NOT NULL DEFAULT 0"),
    ],
    "product": [
        ("old_price", "REAL"),
        ("moq", "INTEGER NOT NULL DEFAULT 1"),
        ("deleted", "INTEGER NOT NULL DEFAULT 0"),
    ],
    "orders": [
        ("delivery_fee", "REAL NOT NULL DEFAULT 0"),
        ("shipped_at", "TIMESTAMP"),
        ("released_at", "TIMESTAMP"),
    ],
    "order_items": [
        ("quote_id", "INTEGER"),
    ],
}


def init_db():
    conn = get_db_connection()
    conn.execute("PRAGMA journal_mode = WAL")
    conn.execute("PRAGMA synchronous = NORMAL")

    conn.executescript("""
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            email TEXT NOT NULL UNIQUE,
            phone TEXT NOT NULL,
            password TEXT NOT NULL,
            role TEXT NOT NULL DEFAULT 'customer'
                CHECK(role IN ('customer','seller','admin')),
            address TEXT DEFAULT '',
            city TEXT DEFAULT 'Niamey',
            company_name TEXT NOT NULL DEFAULT '',
            company_type TEXT NOT NULL DEFAULT '',
            sourcing_purpose TEXT NOT NULL DEFAULT '',
            years_active INTEGER NOT NULL DEFAULT 0,
            reorder_rate REAL NOT NULL DEFAULT 0,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS categories (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL UNIQUE
        );

        CREATE TABLE IF NOT EXISTS product (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            seller_id INTEGER NOT NULL,
            category_id INTEGER NOT NULL,
            name TEXT NOT NULL,
            description TEXT DEFAULT '',
            price REAL NOT NULL CHECK(price >= 0),
            old_price REAL,
            moq INTEGER NOT NULL DEFAULT 1,
            stock INTEGER NOT NULL DEFAULT 0 CHECK(stock >= 0),
            image_url TEXT DEFAULT '',
            active INTEGER NOT NULL DEFAULT 1,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(seller_id) REFERENCES users(id),
            FOREIGN KEY(category_id) REFERENCES categories(id)
        );

        CREATE TABLE IF NOT EXISTS orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            total REAL NOT NULL,
            status TEXT NOT NULL DEFAULT 'pending',
            payment_method TEXT NOT NULL DEFAULT 'cash',
            payment_status TEXT NOT NULL DEFAULT 'pending',
            transaction_id TEXT UNIQUE,
            delivery_address TEXT DEFAULT '',
            delivery_city TEXT DEFAULT 'Niamey',
            customer_phone TEXT DEFAULT '',
            delivery_fee REAL NOT NULL DEFAULT 0,
            shipped_at TIMESTAMP,
            released_at TIMESTAMP,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(user_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS order_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            order_id INTEGER NOT NULL,
            product_id INTEGER NOT NULL,
            quantity INTEGER NOT NULL CHECK(quantity > 0),
            unit_price REAL NOT NULL,
            quote_id INTEGER,
            FOREIGN KEY(order_id) REFERENCES orders(id) ON DELETE CASCADE,
            FOREIGN KEY(product_id) REFERENCES product(id)
        );

        CREATE TABLE IF NOT EXISTS payment_attempts (
            transaction_id TEXT PRIMARY KEY,
            order_id INTEGER NOT NULL,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(order_id) REFERENCES orders(id) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS conversations (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            product_id INTEGER NOT NULL,
            buyer_id INTEGER NOT NULL,
            seller_id INTEGER NOT NULL,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            last_message_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(product_id, buyer_id, seller_id),
            FOREIGN KEY(product_id) REFERENCES product(id),
            FOREIGN KEY(buyer_id) REFERENCES users(id),
            FOREIGN KEY(seller_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS quotes (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            conversation_id INTEGER NOT NULL,
            product_id INTEGER NOT NULL,
            buyer_id INTEGER NOT NULL,
            seller_id INTEGER NOT NULL,
            custom_price REAL NOT NULL CHECK(custom_price > 0),
            quantity INTEGER NOT NULL CHECK(quantity > 0),
            note TEXT NOT NULL DEFAULT '',
            status TEXT NOT NULL DEFAULT 'pending'
                CHECK(status IN ('pending','accepted','declined','withdrawn','superseded','ordered')),
            expires_at TIMESTAMP NOT NULL,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            responded_at TIMESTAMP,
            FOREIGN KEY(conversation_id) REFERENCES conversations(id) ON DELETE CASCADE,
            FOREIGN KEY(product_id) REFERENCES product(id),
            FOREIGN KEY(buyer_id) REFERENCES users(id),
            FOREIGN KEY(seller_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS messages (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            conversation_id INTEGER NOT NULL,
            sender_id INTEGER NOT NULL,
            kind TEXT NOT NULL DEFAULT 'text' CHECK(kind IN ('text','quote','system')),
            body TEXT NOT NULL DEFAULT '',
            quote_id INTEGER,
            is_read INTEGER NOT NULL DEFAULT 0,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(conversation_id) REFERENCES conversations(id) ON DELETE CASCADE,
            FOREIGN KEY(sender_id) REFERENCES users(id),
            FOREIGN KEY(quote_id) REFERENCES quotes(id)
        );

        CREATE TABLE IF NOT EXISTS notifications (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            kind TEXT NOT NULL DEFAULT 'info',
            title TEXT NOT NULL,
            body TEXT NOT NULL DEFAULT '',
            link TEXT NOT NULL DEFAULT '',
            is_read INTEGER NOT NULL DEFAULT 0,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(user_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS rfq (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            buyer_id INTEGER NOT NULL,
            title TEXT NOT NULL,
            description TEXT NOT NULL DEFAULT '',
            quantity INTEGER NOT NULL CHECK(quantity > 0),
            moq INTEGER NOT NULL DEFAULT 1,
            budget_max REAL,
            delivery_city TEXT NOT NULL DEFAULT 'Niamey',
            status TEXT NOT NULL DEFAULT 'open' CHECK(status IN ('open','closed')),
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(buyer_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS rfq_quotes (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            rfq_id INTEGER NOT NULL,
            seller_id INTEGER NOT NULL,
            unit_price REAL NOT NULL CHECK(unit_price > 0),
            lead_time_days INTEGER NOT NULL DEFAULT 0,
            comment TEXT NOT NULL DEFAULT '',
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(rfq_id, seller_id),
            FOREIGN KEY(rfq_id) REFERENCES rfq(id) ON DELETE CASCADE,
            FOREIGN KEY(seller_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS search_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            keywords TEXT NOT NULL,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(user_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS disputes (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            order_id INTEGER NOT NULL,
            opened_by INTEGER NOT NULL,
            reason TEXT NOT NULL,
            details TEXT NOT NULL DEFAULT '',
            status TEXT NOT NULL DEFAULT 'open' CHECK(status IN ('open','released','refunded')),
            resolution_note TEXT NOT NULL DEFAULT '',
            resolved_by INTEGER,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            resolved_at TIMESTAMP,
            FOREIGN KEY(order_id) REFERENCES orders(id),
            FOREIGN KEY(opened_by) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS outbox (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            to_email TEXT NOT NULL,
            subject TEXT NOT NULL,
            body TEXT NOT NULL,
            sent INTEGER NOT NULL DEFAULT 0,
            attempts INTEGER NOT NULL DEFAULT 0,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS rate_hits (
            bucket TEXT NOT NULL,
            ts REAL NOT NULL
        );

        CREATE TABLE IF NOT EXISTS product_views (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            product_id INTEGER NOT NULL,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(user_id) REFERENCES users(id),
            FOREIGN KEY(product_id) REFERENCES product(id)
        );
    """)

    for name in ("Mode", "Électronique", "Téléphones", "Maison", "Beauté"):
        conn.execute("INSERT OR IGNORE INTO categories(name) VALUES (?)", (name,))

    # Migrations légères et idempotentes pour les bases existantes.
    for table, columns in SCHEMA_ADDITIONS.items():
        existing = {row[1] for row in conn.execute(f"PRAGMA table_info({table})").fetchall()}
        for column, ddl in columns:
            if column not in existing:
                conn.execute(f"ALTER TABLE {table} ADD COLUMN {column} {ddl}")

    conn.executescript("""
        CREATE INDEX IF NOT EXISTS idx_product_seller ON product(seller_id);
        CREATE INDEX IF NOT EXISTS idx_product_category ON product(category_id, active);
        CREATE INDEX IF NOT EXISTS idx_orders_user ON orders(user_id);
        CREATE INDEX IF NOT EXISTS idx_orders_pay ON orders(payment_method, payment_status, status);
        CREATE INDEX IF NOT EXISTS idx_items_order ON order_items(order_id);
        CREATE INDEX IF NOT EXISTS idx_items_product ON order_items(product_id);
        CREATE INDEX IF NOT EXISTS idx_attempts_order ON payment_attempts(order_id);
        CREATE INDEX IF NOT EXISTS idx_conv_buyer ON conversations(buyer_id, last_message_at);
        CREATE INDEX IF NOT EXISTS idx_conv_seller ON conversations(seller_id, last_message_at);
        CREATE INDEX IF NOT EXISTS idx_msg_conv ON messages(conversation_id, id);
        CREATE INDEX IF NOT EXISTS idx_msg_unread ON messages(conversation_id, is_read, sender_id);
        CREATE INDEX IF NOT EXISTS idx_quotes_conv ON quotes(conversation_id, status);
        CREATE INDEX IF NOT EXISTS idx_quotes_buyer ON quotes(buyer_id, status);
        CREATE INDEX IF NOT EXISTS idx_notif_user ON notifications(user_id, is_read, id);
        CREATE INDEX IF NOT EXISTS idx_rfq_status ON rfq(status, id);
        CREATE INDEX IF NOT EXISTS idx_rfq_buyer ON rfq(buyer_id);
        CREATE INDEX IF NOT EXISTS idx_rfqq_rfq ON rfq_quotes(rfq_id, unit_price);
        CREATE INDEX IF NOT EXISTS idx_search_user ON search_history(user_id, id);
        CREATE INDEX IF NOT EXISTS idx_views_user ON product_views(user_id, id);
        CREATE UNIQUE INDEX IF NOT EXISTS idx_dispute_open ON disputes(order_id) WHERE status='open';
        CREATE INDEX IF NOT EXISTS idx_dispute_status ON disputes(status, id);
        CREATE INDEX IF NOT EXISTS idx_outbox_pending ON outbox(sent, attempts, id);
        CREATE INDEX IF NOT EXISTS idx_rate_bucket ON rate_hits(bucket, ts);
    """)
    conn.commit()
    conn.close()


# ============================================================================
# 4. SÉCURITÉ : MOTS DE PASSE, CSRF, ACCÈS, EN-TÊTES
# ============================================================================
def hash_password(password, salt=None, iterations=None):
    """Format : pbkdf2$<itérations>$<sel>$<empreinte>."""
    salt = salt or secrets.token_hex(16)
    iterations = iterations or PASSWORD_ITERATIONS
    digest = hashlib.pbkdf2_hmac(
        "sha256", password.encode(), salt.encode(), iterations).hex()
    return f"pbkdf2${iterations}${salt}${digest}"


def verify_password(password, stored):
    """Accepte le nouveau format et l'ancien (sel$empreinte, 120 000 itérations)."""
    try:
        if stored.startswith("pbkdf2$"):
            _, iterations, salt, digest = stored.split("$", 3)
            iterations = int(iterations)
        else:
            salt, digest = stored.split("$", 1)
            iterations = LEGACY_ITERATIONS
        calculated = hashlib.pbkdf2_hmac(
            "sha256", password.encode(), salt.encode(), iterations).hex()
        return hmac.compare_digest(calculated, digest)
    except (ValueError, AttributeError):
        return False


def needs_rehash(stored):
    if not stored.startswith("pbkdf2$"):
        return True
    try:
        return int(stored.split("$", 3)[1]) < PASSWORD_ITERATIONS
    except (ValueError, IndexError):
        return True


DUMMY_HASH = hash_password("sahel-box-dummy-password")


def csrf_token():
    if "csrf_token" not in session:
        session["csrf_token"] = secrets.token_urlsafe(32)
    return session["csrf_token"]


def csrf_protect():
    if request.method in UNSAFE_METHODS:
        sent = request.form.get("_csrf", "") or request.headers.get("X-CSRF-Token", "")
        expected = session.get("csrf_token", "")
        if not sent or not expected or not hmac.compare_digest(sent, expected):
            return False
    return True


def login_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if "user_id" not in session:
            flash("Connectez-vous pour continuer.", "warning")
            return redirect(url_for("login"))
        return view(*args, **kwargs)
    return wrapped


def role_required(*roles):
    def decorator(view):
        @wraps(view)
        def wrapped(*args, **kwargs):
            if session.get("user_role") not in roles:
                flash("Accès non autorisé.", "danger")
                return redirect(url_for("home"))
            return view(*args, **kwargs)
        return wrapped
    return decorator


CSP = (
    "default-src 'self'; "
    "img-src 'self' data: https:; "
    "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
    "font-src 'self' data: https://fonts.gstatic.com; "
    "script-src 'self' 'unsafe-inline'; "
    "connect-src 'self'; "
    "object-src 'none'; base-uri 'self'; frame-ancestors 'none'"
)


@app.after_request
def security_headers(response):
    response.headers.setdefault("X-Content-Type-Options", "nosniff")
    response.headers.setdefault("X-Frame-Options", "DENY")
    response.headers.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")
    response.headers.setdefault(
        "Permissions-Policy", "geolocation=(), microphone=(), camera=(), payment=()")
    response.headers.setdefault("Content-Security-Policy", CSP)
    if app.config["SESSION_COOKIE_SECURE"]:
        response.headers.setdefault(
            "Strict-Transport-Security", "max-age=31536000; includeSubDomains")
    return response


@app.before_request
def guard_request():
    if request.endpoint == "static":
        return None
    if (request.method in UNSAFE_METHODS
            and request.endpoint not in CSRF_EXEMPT_ENDPOINTS
            and not csrf_protect()):
        return render_template(
            "error.html", code=400,
            message="Requête invalide (CSRF). Rechargez la page et réessayez."), 400

    uid = session.get("user_id")
    if uid:
        try:
            with connection() as conn:
                row = conn.execute(
                    "SELECT id, name, role FROM users WHERE id=?", (uid,)).fetchone()
        except sqlite3.Error:
            row = False
        if row is None:
            session.clear()
        elif row:
            # Le rôle est toujours relu en base : une rétrogradation est immédiate.
            if session.get("user_role") != row["role"]:
                session["user_role"] = row["role"]
            if session.get("user_name") != row["name"]:
                session["user_name"] = row["name"]
    return None


def unread_counts(conn, uid):
    messages = conn.execute("""
        SELECT COUNT(*) FROM messages m
        JOIN conversations c ON c.id=m.conversation_id
        WHERE m.is_read=0 AND m.sender_id!=?
          AND (c.buyer_id=? OR c.seller_id=?)""", (uid, uid, uid)).fetchone()[0]
    notifications = conn.execute(
        "SELECT COUNT(*) FROM notifications WHERE user_id=? AND is_read=0",
        (uid,)).fetchone()[0]
    return messages, notifications


@app.context_processor
def inject_globals():
    cart = session.get("cart", {})
    count = sum(to_int(q) for q in cart.values())
    data = {
        "cart_count": count,
        "csrf_token": csrf_token,
        "nav_categories": [],
        "unread_messages": 0,
        "unread_notifications": 0,
        "company_types": COMPANY_TYPES,
        "sourcing_purposes": SOURCING_PURPOSES,
    }
    try:
        with connection() as conn:
            data["nav_categories"] = conn.execute(
                "SELECT id, name FROM categories ORDER BY name").fetchall()
            uid = session.get("user_id")
            if uid:
                data["unread_messages"], data["unread_notifications"] = unread_counts(conn, uid)
    except sqlite3.Error:
        pass
    return data


# ============================================================================
# 5. NOTIFICATIONS, STOCK, STATUTS DE COMMANDE
# ============================================================================
def smtp_configured():
    return bool(os.environ.get("SMTP_HOST", "").strip())


def queue_email(conn, to_email, subject, body):
    """Dépose un e-mail dans la boîte d'envoi (même transaction que l'événement)."""
    if not smtp_configured() or not to_email:
        return
    subject = " ".join(str(subject).split())[:200]
    conn.execute("INSERT INTO outbox(to_email, subject, body) VALUES(?,?,?)",
                 (to_email[:254], subject, str(body)[:5000]))


def notify(conn, user_id, kind, title, body="", link=""):
    """Notification interne + e-mail (si SMTP configuré)."""
    conn.execute(
        "INSERT INTO notifications(user_id, kind, title, body, link) VALUES(?,?,?,?,?)",
        (user_id, kind[:30], title[:200], body[:500], link[:300]))
    if smtp_configured():
        row = conn.execute("SELECT email FROM users WHERE id=?", (user_id,)).fetchone()
        if row:
            url = app.config["BASE_URL"] + link if link.startswith("/") else ""
            text = f"{title}\n\n{body}\n\n" + (f"Voir : {url}\n\n" if url else "") + "SILUX HOUSE"
            queue_email(conn, row["email"], f"[SILUX HOUSE] {title}", text)


def send_email_now(to_email, subject, body):
    host = os.environ["SMTP_HOST"].strip()
    port = int(os.environ.get("SMTP_PORT", "587"))
    user = os.environ.get("SMTP_USER", "").strip()
    password = os.environ.get("SMTP_PASSWORD", "")
    sender = os.environ.get("MAIL_FROM", "").strip() or user or "no-reply@localhost"
    msg = EmailMessage()
    msg["From"], msg["To"], msg["Subject"] = sender, to_email, subject
    msg.set_content(body)
    if port == 465:
        with smtplib.SMTP_SSL(host, port, timeout=20) as smtp:
            if user:
                smtp.login(user, password)
            smtp.send_message(msg)
    else:
        with smtplib.SMTP(host, port, timeout=20) as smtp:
            smtp.ehlo()
            if os.environ.get("SMTP_STARTTLS", "1") == "1":
                smtp.starttls()
                smtp.ehlo()
            if user:
                smtp.login(user, password)
            smtp.send_message(msg)


def flush_outbox(limit=20):
    """Envoie les e-mails en attente. Chaque message est réservé avant l'envoi
    (un seul processus l'envoie, même avec plusieurs workers)."""
    if not smtp_configured():
        return 0
    sent = 0
    with connection() as conn:
        conn.execute("""UPDATE outbox SET sent=0 WHERE sent=3
                        AND created_at < datetime('now','-10 minutes')""")
        conn.commit()
        ids = [r[0] for r in conn.execute(
            "SELECT id FROM outbox WHERE sent=0 AND attempts<5 ORDER BY id LIMIT ?",
            (limit,)).fetchall()]
    for mail_id in ids:
        with connection() as conn:
            cur = conn.execute("UPDATE outbox SET sent=3 WHERE id=? AND sent=0", (mail_id,))
            conn.commit()
            if cur.rowcount != 1:
                continue
            mail = conn.execute("SELECT * FROM outbox WHERE id=?", (mail_id,)).fetchone()
        ok = False
        try:
            send_email_now(mail["to_email"], mail["subject"], mail["body"])
            ok = True
            sent += 1
        except Exception as exc:  # noqa: BLE001
            app.logger.error("Envoi e-mail #%s impossible : %s", mail_id, exc)
        with connection() as conn:
            conn.execute("UPDATE outbox SET sent=?, attempts=attempts+1 WHERE id=?",
                         (1 if ok else 0, mail_id))
            conn.commit()
    return sent


def release_stock(conn, order_id):
    for it in conn.execute(
        "SELECT product_id, quantity FROM order_items WHERE order_id=?", (order_id,)
    ).fetchall():
        conn.execute("UPDATE product SET stock=stock+? WHERE id=?",
                     (it["quantity"], it["product_id"]))


def reserve_stock(conn, order_id):
    items = conn.execute(
        "SELECT product_id, quantity FROM order_items WHERE order_id=?", (order_id,)
    ).fetchall()
    for it in items:
        row = conn.execute("SELECT stock FROM product WHERE id=?",
                           (it["product_id"],)).fetchone()
        if not row or row["stock"] < it["quantity"]:
            return False
    for it in items:
        conn.execute("UPDATE product SET stock=stock-? WHERE id=?",
                     (it["quantity"], it["product_id"]))
    return True


def cancel_order_in_tx(conn, order):
    """Annulation idempotente : le stock n'est restitué qu'au passage vers 'cancelled'.

    À appeler dans une transaction ouverte. Retourne True si l'annulation vient
    d'être effectuée, False si la commande était déjà annulée.
    """
    cur = conn.execute(
        "UPDATE orders SET status='cancelled' WHERE id=? AND status!='cancelled'",
        (order["id"],))
    if cur.rowcount != 1:
        return False
    release_stock(conn, order["id"])
    if order["payment_status"] in ("escrowed", "paid"):
        conn.execute("UPDATE orders SET payment_status='refund_due' WHERE id=?",
                     (order["id"],))
    elif order["payment_method"] == "cinetpay" and order["payment_status"] == "pending":
        conn.execute("UPDATE orders SET payment_status='failed' WHERE id=?",
                     (order["id"],))
    return True


def order_seller_ids(conn, order_id):
    return [r[0] for r in conn.execute("""
        SELECT DISTINCT p.seller_id FROM order_items oi
        JOIN product p ON p.id=oi.product_id WHERE oi.order_id=?""", (order_id,))]


def refresh_seller_metrics(conn, seller_id):
    """Taux de fidélité = part des acheteurs ayant reçu au moins 2 commandes."""
    rows = conn.execute("""
        SELECT o.user_id, COUNT(DISTINCT o.id) AS n
        FROM orders o
        JOIN order_items oi ON oi.order_id=o.id
        JOIN product p ON p.id=oi.product_id
        WHERE p.seller_id=? AND o.status='delivered'
        GROUP BY o.user_id""", (seller_id,)).fetchall()
    if rows:
        repeat = sum(1 for r in rows if r["n"] >= 2)
        conn.execute("UPDATE users SET reorder_rate=? WHERE id=?",
                     (round(100.0 * repeat / len(rows), 1), seller_id))


def apply_order_status(conn, order_id, new_status, actor_role):
    """Changement de statut avec règles métier. Retourne (ok, message, catégorie)."""
    if new_status not in ORDER_STATUSES:
        return False, "Statut invalide.", "danger"
    is_admin = actor_role == "admin"
    with immediate(conn):
        order = conn.execute("SELECT * FROM orders WHERE id=?", (order_id,)).fetchone()
        if not order:
            return False, "Commande introuvable.", "danger"
        current, pay, method = order["status"], order["payment_status"], order["payment_method"]
        if current == new_status:
            return True, "Statut déjà à jour.", "success"
        if pay == "released" and new_status == "cancelled":
            return False, "Fonds déjà libérés : annulation impossible.", "warning"
        open_dispute = conn.execute(
            "SELECT id FROM disputes WHERE order_id=? AND status='open'", (order_id,)).fetchone()
        if open_dispute and not is_admin:
            return False, "Un litige est ouvert : l'administration doit le trancher.", "warning"

        if not is_admin:
            if new_status not in SELLER_ALLOWED_STATUSES:
                return False, "Statut invalide.", "danger"
            if current in ("delivered", "cancelled"):
                return False, "Cette commande est clôturée.", "warning"
            if (method == "cinetpay" and pay not in ("escrowed", "paid")
                    and new_status != "cancelled"):
                return False, ("Paiement en ligne non confirmé : "
                               "la commande ne peut pas être traitée."), "warning"
            if new_status == "delivered" and pay == "escrowed":
                return False, ("Trade Assurance : seule la cliente peut confirmer "
                               "la réception et libérer les fonds."), "warning"
            if new_status == "delivered" and current not in ("confirmed", "processing", "shipped"):
                return False, "Préparez et expédiez la commande avant de la livrer.", "warning"
            if new_status == "cancelled" and current == "shipped":
                return False, "Commande déjà expédiée : contactez l'administration.", "warning"
            if new_status == "processing" and current == "shipped":
                return False, "Commande déjà expédiée.", "warning"

        if new_status == "cancelled":
            cancel_order_in_tx(conn, order)
        else:
            if current == "cancelled" and not reserve_stock(conn, order_id):
                return False, "Stock insuffisant pour rouvrir la commande.", "danger"
            if new_status == "shipped":
                conn.execute(
                    "UPDATE orders SET status='shipped', shipped_at=CURRENT_TIMESTAMP WHERE id=?",
                    (order_id,))
            elif new_status == "delivered":
                if pay == "escrowed":  # arbitrage administrateur
                    conn.execute("""UPDATE orders SET status='delivered',
                                    payment_status='released', released_at=CURRENT_TIMESTAMP
                                    WHERE id=?""", (order_id,))
                elif method == "cash" and pay == "pending":
                    conn.execute(
                        "UPDATE orders SET status='delivered', payment_status='paid' WHERE id=?",
                        (order_id,))
                else:
                    conn.execute("UPDATE orders SET status='delivered' WHERE id=?", (order_id,))
                for sid in order_seller_ids(conn, order_id):
                    refresh_seller_metrics(conn, sid)
            else:
                conn.execute("UPDATE orders SET status=? WHERE id=?", (new_status, order_id))
        if open_dispute and new_status in ("cancelled", "delivered"):
            conn.execute("""UPDATE disputes SET status=?, resolution_note='Décision administrateur',
                            resolved_by=?, resolved_at=CURRENT_TIMESTAMP WHERE id=?""",
                         ("refunded" if new_status == "cancelled" else "released",
                          session.get("user_id"), open_dispute["id"]))
        notify(conn, order["user_id"], "order",
               f"Commande #{order_id} : {STATUS_LABELS.get(new_status, new_status)}",
               "Le statut de votre commande a été mis à jour.",
               url_for("order_detail", order_id=order_id))
    return True, "Statut de commande mis à jour.", "success"


# ----- Maintenance : annulation des commandes en ligne jamais payées --------


def expire_stale_orders():
    with connection() as conn:
        stale = conn.execute("""
            SELECT id, transaction_id FROM orders
            WHERE payment_method='cinetpay' AND payment_status='pending' AND status='pending'
              AND created_at < datetime('now', ?)
            ORDER BY id LIMIT 20""",
            (f"-{max(5, PENDING_PAYMENT_TTL_MINUTES)} minutes",)).fetchall()
    for row in stale:
        try:
            if cinetpay_configured() and row["transaction_id"]:
                ok, _state = update_payment_from_cinetpay(row["transaction_id"])
                if not ok:
                    continue  # CinetPay injoignable : on réessaiera plus tard
            with connection() as conn:
                with immediate(conn):
                    fresh = conn.execute("SELECT * FROM orders WHERE id=?",
                                         (row["id"],)).fetchone()
                    if (fresh and fresh["payment_status"] == "pending"
                            and fresh["status"] == "pending"):
                        cancel_order_in_tx(conn, fresh)
                        notify(conn, fresh["user_id"], "order",
                               f"Commande #{fresh['id']} annulée",
                               "Le paiement en ligne n'a pas été finalisé à temps.",
                               url_for("order_detail", order_id=fresh["id"], _external=False))
        except Exception as exc:  # noqa: BLE001 - la maintenance ne doit jamais casser le site
            app.logger.error("Maintenance commande #%s : %s", row["id"], exc)


_workers_started = False


def start_workers():
    """Tâche de fond : envoi des e-mails (5 s) et nettoyage des commandes (5 min).

    À lancer sans --preload avec gunicorn. SAHEL_NO_WORKERS=1 la désactive."""
    global _workers_started
    if _workers_started or os.environ.get("SAHEL_NO_WORKERS") == "1":
        return
    _workers_started = True

    def loop():
        last_maintenance = 0.0
        while True:
            try:
                flush_outbox()
                if time.monotonic() - last_maintenance > 300:
                    last_maintenance = time.monotonic()
                    with app.test_request_context():
                        expire_stale_orders()
            except Exception as exc:  # noqa: BLE001
                app.logger.error("Tâche de fond : %s", exc)
            time.sleep(5)
    threading.Thread(target=loop, daemon=True, name="sahel-worker").start()


# ============================================================================
# 6. PANIER (MOQ + PRIX NÉGOCIÉS)
# ============================================================================
def cart_items():
    cart = session.get("cart", {})
    quote_map = session.get("cart_quotes", {})
    ids = []
    for key in cart:
        pid = to_int(key, -1)
        if pid > 0:
            ids.append(pid)
    if not ids:
        return [], 0

    placeholders = ",".join("?" for _ in ids)
    uid = session.get("user_id")
    with connection() as conn:
        rows = conn.execute(
            f"""SELECT p.*, c.name AS category_name
                FROM product p JOIN categories c ON c.id=p.category_id
                WHERE p.id IN ({placeholders}) AND p.active=1""", ids).fetchall()
        quotes = {}
        qids = [to_int(v) for v in quote_map.values() if to_int(v) > 0]
        if uid and qids:
            qph = ",".join("?" for _ in qids)
            for q in conn.execute(
                f"""SELECT * FROM quotes WHERE id IN ({qph}) AND buyer_id=?
                    AND status='accepted' AND expires_at >= datetime('now')""",
                qids + [uid]).fetchall():
                quotes[q["id"]] = q

    items, subtotal = [], 0
    for row in rows:
        pid = str(row["id"])
        product = dict(row)
        quote = quotes.get(to_int(quote_map.get(pid))) if pid in quote_map else None
        if quote is not None and quote["product_id"] != row["id"]:
            quote = None
        if quote is not None:
            if row["stock"] < quote["quantity"]:
                continue
            quantity = quote["quantity"]
            product["old_price"] = max(row["price"], row["old_price"] or 0) or None
            product["price"] = quote["custom_price"]
            product["negotiated"] = True
            product["quote_id"] = quote["id"]
        else:
            quantity = min(max(to_int(cart.get(pid)), 0), row["stock"])
            product["negotiated"] = False
            product["quote_id"] = None
        if quantity <= 0:
            continue
        total = quantity * product["price"]
        subtotal += total
        items.append({"product": product, "quantity": quantity, "line_total": total})
    return items, subtotal


def cinetpay_configured():
    return bool(app.config["CINETPAY_API_KEY"] and app.config["CINETPAY_SITE_ID"])


def new_transaction_id():
    return f"SAHEL{datetime.now():%Y%m%d%H%M%S}{uuid.uuid4().hex[:8].upper()}"


def delivery_fee_for_city(city):
    city_norm = (city or "").strip().lower()
    if city_norm in ("niamey", "niamey ville"):
        return 1000
    return 2500


# ============================================================================
# 7. CINETPAY : VÉRIFICATION ET SÉQUESTRE (IDEMPOTENT)
# ============================================================================
def find_order_by_transaction(conn, transaction_id):
    row = conn.execute("""
        SELECT o.* FROM payment_attempts a
        JOIN orders o ON o.id = a.order_id
        WHERE a.transaction_id=?
    """, (transaction_id,)).fetchone()
    if row:
        return row
    return conn.execute(
        "SELECT * FROM orders WHERE transaction_id=?", (transaction_id,)
    ).fetchone()


def verify_cinetpay(transaction_id):
    """Interroge CinetPay : seule source de vérité sur l'état d'un paiement."""
    if not cinetpay_configured():
        return None, "CinetPay n'est pas configuré."
    try:
        response = requests.post(
            f"{CINETPAY_API_URL}/payment/check",
            json={
                "apikey": app.config["CINETPAY_API_KEY"],
                "site_id": app.config["CINETPAY_SITE_ID"],
                "transaction_id": transaction_id,
            },
            timeout=15,
        )
        response.raise_for_status()
        return response.json(), None
    except (requests.RequestException, ValueError) as exc:
        return None, str(exc)


def update_payment_from_cinetpay(transaction_id):
    """Met à jour la commande à partir de l'état réel chez CinetPay.

    Paiement accepté -> fonds sous séquestre (payment_status='escrowed',
    status='processing'). Retourne (ok, état) ; ok=False = erreur temporaire
    (le webhook répond 500 et CinetPay renvoie la notification). Idempotent.
    """
    with connection() as conn:
        order = find_order_by_transaction(conn, transaction_id)
    if not order:
        return True, "unknown"
    if order["payment_status"] in FINAL_PAYMENT_STATES:
        return True, "paid"
    if order["payment_method"] != "cinetpay":
        return True, "ignored"

    result, error = verify_cinetpay(transaction_id)
    if error or not result:
        app.logger.error("Vérification CinetPay impossible (%s) : %s", transaction_id, error)
        return False, "error"

    data = result.get("data") or {}
    status = str(data.get("status", "")).upper()

    if status == "ACCEPTED":
        try:
            paid_amount = int(float(data.get("amount")))
        except (TypeError, ValueError):
            paid_amount = None
        currency = str(data.get("currency") or "XOF").upper()
        if paid_amount != int(round(order["total"])) or currency != "XOF":
            app.logger.error(
                "Montant/devise inattendus pour la commande #%s : reçu %s %s, attendu %s XOF.",
                order["id"], data.get("amount"), currency, int(round(order["total"])))
            return True, "amount_mismatch"

        try:
            with connection() as conn:
                with immediate(conn):
                    fresh = conn.execute("SELECT * FROM orders WHERE id=?",
                                         (order["id"],)).fetchone()
                    if fresh["payment_status"] in FINAL_PAYMENT_STATES:
                        return True, "paid"
                    new_pay, new_status = "escrowed", fresh["status"]
                    if fresh["status"] == "pending":
                        new_status = "processing"
                    elif fresh["status"] == "cancelled":
                        # Paiement arrivé après annulation : on tente de re-réserver le stock.
                        if reserve_stock(conn, fresh["id"]):
                            new_status = "processing"
                        else:
                            new_pay = "refund_due"
                            app.logger.error(
                                "Paiement reçu pour la commande #%s annulée et stock épuisé : "
                                "remboursement à traiter.", fresh["id"])
                    conn.execute(
                        "UPDATE orders SET payment_status=?, status=?, transaction_id=? WHERE id=?",
                        (new_pay, new_status, transaction_id, fresh["id"]))
                    notify(conn, fresh["user_id"], "order",
                           f"Paiement sécurisé : commande #{fresh['id']}",
                           "Vos fonds sont protégés par Trade Assurance jusqu'à la réception.",
                           url_for("order_detail", order_id=fresh["id"]))
                    for sid in order_seller_ids(conn, fresh["id"]):
                        notify(conn, sid, "order",
                               f"Commande #{fresh['id']} payée (séquestre)",
                               "Préparez et expédiez la commande : les fonds seront libérés "
                               "à la confirmation de réception.",
                               url_for("seller_orders"))
        except sqlite3.Error as exc:
            app.logger.error("Erreur base de données (paiement #%s) : %s", order["id"], exc)
            return False, "error"
        return True, "paid"

    if status in ("REFUSED", "CANCELLED", "CANCELED"):
        try:
            with connection() as conn:
                with immediate(conn):
                    fresh = conn.execute("SELECT * FROM orders WHERE id=?",
                                         (order["id"],)).fetchone()
                    if fresh["payment_status"] == "pending":
                        cancel_order_in_tx(conn, fresh)  # restockage une seule fois
                        conn.execute(
                            "UPDATE orders SET payment_status='failed' WHERE id=?",
                            (fresh["id"],))
                        notify(conn, fresh["user_id"], "order",
                               f"Paiement refusé : commande #{fresh['id']}",
                               "La commande a été annulée et le stock libéré.",
                               url_for("order_detail", order_id=fresh["id"]))
        except sqlite3.Error as exc:
            app.logger.error("Erreur base de données (échec #%s) : %s", order["id"], exc)
            return False, "error"
        return True, "failed"

    return True, (status or "pending").lower()


NOTIFY_TOKEN_FIELDS = (
    "cpm_site_id", "cpm_trans_id", "cpm_trans_date", "cpm_amount", "cpm_currency",
    "signature", "payment_method", "cel_phone_num", "cpm_phone_prefixe",
    "cpm_language", "cpm_version", "cpm_payment_config", "cpm_page_action",
    "cpm_custom", "cpm_designation", "cpm_error_message",
)


def check_notify_token():
    """Contrôle supplémentaire de l'en-tête x-token (HMAC-SHA256, clé secrète).

    Non bloquant : la sécurité repose sur la revérification serveur à serveur
    auprès de l'API CinetPay. Un écart est journalisé.
    """
    secret = app.config["CINETPAY_SECRET_KEY"]
    sent = request.headers.get("x-token", "")
    if not secret or not sent:
        return
    payload = "".join(request.form.get(f, "") for f in NOTIFY_TOKEN_FIELDS)
    expected = hmac.new(secret.encode(), payload.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected, sent):
        app.logger.warning("x-token CinetPay non conforme (transaction %s).",
                           request.form.get("cpm_trans_id", "?"))


# ============================================================================
# 8. SOURCING IA (NLP SQLITE)
# ============================================================================
_STOPWORDS_RAW = """
a au aux avec ce ces cet cette ceci cela ca c ci celui celle ceux celles chez comme comment
dans de des du donc dont d elle elles en entre et etc eux il ils je j la le les leur leurs lui
ma mais me meme mes moi mon ne ni nos notre nous on ou ou par parce pas pour pourquoi qu que
quel quelle quels quelles qui quoi sa sans se ses si sur ta te tes toi ton tous tout toute toutes
tres tu un une vos votre vous y ete etre est sont suis sommes etes ai as avons avez ont avoir
fait faire peut peux veux veut voudrais cherche chercher recherche rechercher trouve trouver
besoin souhaite souhaiter voudrait acheter achat vendre cherchons proposer propose propositions
bonjour salut svp stp merci plus moins bien bon bonne tres assez aussi ainsi alors apres avant
cet cela deja encore jamais toujours rien quelque quelques quelqu autre autres meilleur meilleurs
the a an and or of for to in on with without is are be been am i me my we our you your it its
this that these those looking look want need find search buy get any some from at by as
please cheap best good
"""
STOPWORDS = frozenset(fold_text(w) for w in _STOPWORDS_RAW.split())
TOKEN_RE = re.compile(r"[a-z0-9]{2,}")


def extract_keywords_detail(text, limit=8):
    """Retourne (mots_retenus, mots_éliminés) : accents retirés, mots vides supprimés."""
    folded = fold_text(clean_text(text, 300))
    kept, ignored = [], []
    for token in TOKEN_RE.findall(folded):
        if token in STOPWORDS:
            if token not in ignored:
                ignored.append(token)
            continue
        if len(token) > 4 and token.endswith(("s", "x")):
            token = token[:-1]  # pluriel simple : robes -> robe, bijoux -> bijou
        token = token[:30]
        if token not in kept and len(kept) < limit:
            kept.append(token)
    return kept, ignored


def extract_keywords(text, limit=8):
    return extract_keywords_detail(text, limit)[0]


def relevance_sql(keywords):
    """Score cumulé calculé par SQLite : nom = 2 points, description = 1 point."""
    parts, params = [], []
    for kw in keywords:
        pattern = f"%{like_escape(kw)}%"
        parts.append(
            f"(CASE WHEN fold(p.name) LIKE ? {ESC} THEN 2 ELSE 0 END"
            f" + CASE WHEN fold(p.description) LIKE ? {ESC} THEN 1 ELSE 0 END)")
        params += [pattern, pattern]
    return (" + ".join(parts) if parts else "0"), params


def search_products(conn, keywords, limit=40, exclude_ids=()):
    if not keywords:
        return []
    expr, params = relevance_sql(keywords)
    sql = f"""
        SELECT * FROM (
            SELECT p.*, c.name AS category_name, u.name AS seller_name,
                   u.company_name, u.company_type, u.years_active, u.reorder_rate,
                   ({expr}) AS score
            FROM product p
            JOIN categories c ON c.id = p.category_id
            JOIN users u ON u.id = p.seller_id
            WHERE p.active = 1
        ) WHERE score > 0"""
    exclude = [to_int(i) for i in exclude_ids if to_int(i) > 0]
    if exclude:
        sql += " AND id NOT IN (" + ",".join("?" for _ in exclude) + ")"
        params += exclude
    sql += " ORDER BY score DESC, (stock > 0) DESC, id DESC LIMIT ?"
    return conn.execute(sql, params + [int(limit)]).fetchall()


def product_card(row, score=None):
    price, old = row["price"], row["old_price"]
    discount = int(round((old - price) / old * 100)) if old and old > price else 0
    card = {
        "id": row["id"],
        "name": row["name"],
        "price": price,
        "old_price": old if discount else None,
        "discount": discount,
        "image_url": row["image_url"] or "",
        "category": row["category_name"],
        "stock": row["stock"],
        "moq": to_int(row["moq"], 1),
        "url": url_for("product_detail", product_id=row["id"]),
    }
    if score is not None:
        card["score"] = round(score, 2)
    return card


def record_search(conn, user_id, keywords):
    if not keywords:
        return
    joined = " ".join(keywords)
    last = conn.execute(
        "SELECT keywords FROM search_history WHERE user_id=? ORDER BY id DESC LIMIT 1",
        (user_id,)).fetchone()
    if last and last["keywords"] == joined:
        return
    conn.execute("INSERT INTO search_history(user_id, keywords) VALUES(?,?)",
                 (user_id, joined))
    conn.execute("""DELETE FROM search_history WHERE user_id=? AND id NOT IN
                    (SELECT id FROM search_history WHERE user_id=? ORDER BY id DESC LIMIT 200)""",
                 (user_id, user_id))
    conn.commit()


def interest_profile(conn, user_id, current_query=""):
    """Pondère les mots-clés : recherche en cours, historique, achats, consultations."""
    weights = defaultdict(float)
    for kw in extract_keywords(current_query):
        weights[kw] += 6
    for i, row in enumerate(conn.execute(
            "SELECT keywords FROM search_history WHERE user_id=? ORDER BY id DESC LIMIT 60",
            (user_id,))):
        recency = 1.0 if i < 10 else 0.6
        for kw in row["keywords"].split():
            weights[kw] += 3 * recency
    for row in conn.execute("""
            SELECT p.name FROM order_items oi
            JOIN orders o ON o.id=oi.order_id
            JOIN product p ON p.id=oi.product_id
            WHERE o.user_id=? AND o.status!='cancelled'
            ORDER BY o.id DESC LIMIT 30""", (user_id,)):
        for kw in extract_keywords(row["name"], 4):
            weights[kw] += 4
    for row in conn.execute("""
            SELECT p.name, COUNT(*) AS n FROM product_views v
            JOIN product p ON p.id=v.product_id
            WHERE v.user_id=? GROUP BY p.id ORDER BY n DESC LIMIT 15""", (user_id,)):
        for kw in extract_keywords(row["name"], 4):
            weights[kw] += min(row["n"], 5)
    return sorted(weights.items(), key=lambda kv: (-kv[1], kv[0]))[:8]


def personalized_suggestions(conn, user_id, current_query="", limit=8):
    profile = interest_profile(conn, user_id, current_query)
    keywords = [kw for kw, _ in profile]
    if keywords:
        weights = dict(profile)
        rows = search_products(conn, keywords, limit=40)
        ranked = []
        for row in rows:
            name, desc = fold_text(row["name"]), fold_text(row["description"])
            affinity = sum(
                w * (2 if kw in name else 1 if kw in desc else 0)
                for kw, w in weights.items())
            ranked.append((affinity + row["score"], row))
        ranked.sort(key=lambda t: (-t[0], -t[1]["id"]))
        cards = [product_card(r, s) for s, r in ranked[:limit] if r["stock"] > 0]
        if cards:
            return keywords, cards, "personalized"
    rows = conn.execute("""
        SELECT p.*, c.name AS category_name, COALESCE(SUM(oi.quantity),0) AS sold
        FROM product p
        JOIN categories c ON c.id=p.category_id
        LEFT JOIN order_items oi ON oi.product_id=p.id
        WHERE p.active=1 AND p.stock>0
        GROUP BY p.id ORDER BY sold DESC, p.id DESC LIMIT ?""", (limit,)).fetchall()
    return keywords, [product_card(r, r["sold"]) for r in rows], "trending"


# ============================================================================
# 9. BOUTIQUE, COMPTES
# ============================================================================
@app.get("/healthz")
def healthz():
    with connection() as conn:
        conn.execute("SELECT 1").fetchone()
    return jsonify({"status": "ok"})


@app.route("/")
def home():
    query = clean_text(request.args.get("q", ""), 100)
    category_id = request.args.get("cat_id", "").strip()
    company_type = request.args.get("company_type", "").strip()

    sql = """SELECT p.*, c.name AS category_name, u.name AS seller_name,
                    u.company_name, u.company_type, u.years_active, u.reorder_rate
             FROM product p
             JOIN categories c ON c.id=p.category_id
             JOIN users u ON u.id=p.seller_id
             WHERE p.active=1"""
    params = {}
    if query:
        sql += (f" AND (fold(p.name) LIKE :q {ESC} OR fold(p.description) LIKE :q {ESC})")
        params["q"] = f"%{like_escape(fold_text(query))}%"
    if category_id.isdigit():
        sql += " AND p.category_id=:cat"
        params["cat"] = int(category_id)
    if company_type in COMPANY_TYPES:
        sql += " AND u.company_type=:ctype"
        params["ctype"] = company_type
    page = max(1, to_int(request.args.get("page"), 1))
    sql += " ORDER BY p.id DESC LIMIT :limit OFFSET :offset"
    params["limit"] = PER_PAGE + 1
    params["offset"] = (page - 1) * PER_PAGE

    with connection() as conn:
        categories = conn.execute("SELECT * FROM categories ORDER BY name").fetchall()
        rows = conn.execute(sql, params).fetchall()
    return render_template("home.html", products=rows[:PER_PAGE], categories=categories,
                           query=query, page=page, has_next=len(rows) > PER_PAGE)


@app.route("/manufacturers")
def manufacturers():
    return redirect(url_for("home", company_type="Fabricant"))


@app.route("/mondial")
def mondial():
    if session.get("user_role") in ("seller", "admin"):
        return redirect(url_for("rfq_marketplace"))
    return redirect(url_for("rfq_new"))


@app.route("/register", methods=["GET", "POST"])
def register():
    if request.method == "POST":
        if rate_limited(f"register:{client_ip()}", 10, 3600, shared=True):
            abort(429)
        name = clean_text(request.form.get("name"), 100)
        email = request.form.get("email", "").strip().lower()
        phone = request.form.get("phone", "").strip()
        password = request.form.get("password", "")
        password_confirm = request.form.get("password_confirm", "")
        role = request.form.get("role", "customer")
        address = clean_text(request.form.get("address"), 200)
        city = clean_text(request.form.get("city"), 80) or "Niamey"
        company_name = clean_text(request.form.get("company_name"), 120)
        company_type = request.form.get("company_type", "")
        sourcing_purpose = request.form.get("sourcing_purpose", "")
        years_active = min(max(to_int(request.form.get("years_active"), 0), 0), 100)

        if role not in ("customer", "seller"):
            role = "customer"
        if company_type not in COMPANY_TYPES:
            company_type = ""
        if sourcing_purpose not in SOURCING_PURPOSES:
            sourcing_purpose = ""
        if role != "seller":
            years_active = 0

        if (not name or not valid_email(email) or not phone or not PHONE_RE.match(phone)
                or len(password) < 10 or len(password) > 128):
            flash("Vérifiez le nom, l'e-mail, le téléphone et le mot de passe (10 caractères minimum).", "danger")
            return redirect(url_for("register"))
        if password != password_confirm:
            flash("Les mots de passe ne correspondent pas.", "danger")
            return redirect(url_for("register"))
        if role == "seller" and not company_name:
            flash("Indiquez le nom de votre entreprise ou de votre boutique.", "danger")
            return redirect(url_for("register"))

        with connection() as conn:
            try:
                conn.execute("""
                    INSERT INTO users(name,email,phone,password,role,address,city,
                                      company_name,company_type,sourcing_purpose,years_active)
                    VALUES(?,?,?,?,?,?,?,?,?,?,?)
                """, (name, email, phone, hash_password(password), role, address, city,
                      company_name, company_type, sourcing_purpose, years_active))
                conn.commit()
            except sqlite3.IntegrityError:
                flash("Cet e-mail est déjà associé à un compte.", "danger")
                return redirect(url_for("register"))
        flash("Compte créé avec succès. Connectez-vous.", "success")
        return redirect(url_for("login"))
    return render_template(
        "register.html",
        company_types=COMPANY_TYPES,
        sourcing_purposes=SOURCING_PURPOSES,
    )


@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        email = request.form.get("email", "").strip().lower()[:254]
        password = request.form.get("password", "")[:128]
        if (rate_limited(f"login:{client_ip()}", 30, 300, shared=True)
                or rate_limited(f"login:{client_ip()}:{email}", 8, 300, shared=True)):
            flash("Trop de tentatives. Patientez quelques minutes.", "danger")
            return redirect(url_for("login"))
        with connection() as conn:
            user = conn.execute("SELECT * FROM users WHERE email=?", (email,)).fetchone()
            valid = verify_password(password, user["password"] if user else DUMMY_HASH)
            if user and valid:
                if needs_rehash(user["password"]):
                    conn.execute("UPDATE users SET password=? WHERE id=?",
                                 (hash_password(password), user["id"]))
                    conn.commit()
                session.clear()
                session.permanent = True
                session["user_id"] = user["id"]
                session["user_name"] = user["name"]
                session["user_role"] = user["role"]
                session["csrf_token"] = secrets.token_urlsafe(32)
                flash("Ravi de vous revoir.", "success")
                return redirect(url_for("home"))
        flash("Identifiants incorrects.", "danger")
    return render_template("login.html")


@app.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("home"))


@app.route("/product/<int:product_id>")
def product_detail(product_id):
    with connection() as conn:
        product = conn.execute("""
            SELECT p.*, c.name AS category_name, u.id AS seller_user_id,
                   u.name AS seller_name, u.company_name, u.company_type,
                   u.years_active, u.reorder_rate
            FROM product p
            JOIN categories c ON c.id=p.category_id
            JOIN users u ON u.id=p.seller_id
            WHERE p.id=? AND p.active=1
        """, (product_id,)).fetchone()
        if not product:
            flash("Produit introuvable.", "warning")
            return redirect(url_for("home"))
        uid = session.get("user_id")
        if uid:
            conn.execute("INSERT INTO product_views(user_id, product_id) VALUES(?,?)",
                         (uid, product_id))
            conn.execute("""DELETE FROM product_views WHERE user_id=? AND id NOT IN
                            (SELECT id FROM product_views WHERE user_id=?
                             ORDER BY id DESC LIMIT 200)""", (uid, uid))
            conn.commit()
    return render_template("product.html", product=product)


# ============================================================================
# 10. PANIER ET COMMANDE
# ============================================================================
@app.post("/cart/add/<int:product_id>")
def add_to_cart(product_id):
    with connection() as conn:
        product = conn.execute(
            "SELECT id, name, stock, moq FROM product WHERE id=? AND active=1",
            (product_id,)).fetchone()

    if not product:
        flash("Produit introuvable.", "danger")
        return redirect(url_for("home"))
    if product["stock"] <= 0:
        flash("Produit en rupture de stock.", "warning")
        return safe_back()

    moq = max(1, to_int(product["moq"], 1))
    raw = request.form.get("quantity", "")
    quantity = to_int(raw, moq) if raw != "" else moq
    quantity = min(max(quantity, 1), 1_000_000)

    cart = dict(session.get("cart", {}))
    quotes = session.get("cart_quotes", {})
    if str(product_id) in quotes:
        flash("Ce produit est déjà dans votre panier au prix négocié.", "warning")
        return safe_back()
    if product["stock"] < moq:
        flash(f"Stock inférieur à la quantité minimale de commande ({moq}).", "warning")
        return safe_back()

    new_qty = to_int(cart.get(str(product_id))) + quantity
    if new_qty < moq:
        flash(f"Quantité minimale de commande (MOQ) : {moq} unités pour ce produit.", "danger")
        return safe_back()

    cart[str(product_id)] = min(new_qty, product["stock"])
    session["cart"] = cart
    session.modified = True
    flash("Produit ajouté au panier.", "success")
    return safe_back()


@app.route("/cart")
def view_cart():
    items, subtotal = cart_items()
    return render_template("cart.html", items=items, subtotal=subtotal)


@app.post("/cart/update")
def update_cart():
    cart = dict(session.get("cart", {}))
    quotes = dict(session.get("cart_quotes", {}))
    with connection() as conn:
        for key in list(cart):
            pid = to_int(key, -1)
            if pid <= 0:
                cart.pop(key, None)
                quotes.pop(key, None)
                continue
            quantity = to_int(request.form.get(f"quantity_{key}", "0"))
            product = conn.execute(
                "SELECT stock, moq FROM product WHERE id=? AND active=1", (pid,)).fetchone()
            if not product or quantity <= 0:
                cart.pop(key, None)
                quotes.pop(key, None)
            elif key in quotes:
                continue  # quantité figée par le devis accepté
            else:
                moq = max(1, to_int(product["moq"], 1))
                if quantity < moq:
                    flash(f"MOQ : au moins {moq} unités pour ce produit.", "warning")
                    continue
                cart[key] = min(quantity, product["stock"])
    session["cart"] = cart
    session["cart_quotes"] = quotes
    session.modified = True
    flash("Panier mis à jour.", "success")
    return redirect(url_for("view_cart"))


@app.post("/cart/remove/<int:product_id>")
def remove_from_cart(product_id):
    cart = dict(session.get("cart", {}))
    quotes = dict(session.get("cart_quotes", {}))
    cart.pop(str(product_id), None)
    quotes.pop(str(product_id), None)
    session["cart"] = cart
    session["cart_quotes"] = quotes
    session.modified = True
    return redirect(url_for("view_cart"))


@app.route("/checkout", methods=["GET", "POST"])
@login_required
def checkout():
    items, subtotal = cart_items()
    if not items:
        flash("Votre panier est vide.", "warning")
        return redirect(url_for("view_cart"))

    with connection() as conn:
        user = conn.execute("SELECT * FROM users WHERE id=?", (session["user_id"],)).fetchone()

    if request.method == "GET":
        delivery_fee = delivery_fee_for_city(user["city"])
        return render_template("checkout.html", items=items, subtotal=subtotal,
                               delivery_fee=delivery_fee, total=subtotal + delivery_fee,
                               user=user)

    address = clean_text(request.form.get("address"), 200)
    city = clean_text(request.form.get("city"), 80) or "Niamey"
    phone = request.form.get("phone", "").strip()
    payment_method = request.form.get("payment_method", "cinetpay")
    delivery_fee = delivery_fee_for_city(city)
    total_amount = subtotal + delivery_fee

    if not address or not phone or not PHONE_RE.match(phone):
        flash("Adresse de livraison et téléphone valides obligatoires.", "danger")
        return redirect(url_for("checkout"))
    if payment_method not in ("cash", "cinetpay"):
        payment_method = "cinetpay"

    transaction_id = new_transaction_id()
    try:
        with connection() as conn:
            with immediate(conn):
                for item in items:
                    product = item["product"]
                    moq = max(1, to_int(product.get("moq"), 1))
                    if not product["negotiated"] and item["quantity"] < moq:
                        raise ValueError(
                            f"Quantité minimale (MOQ) de {moq} unités : {product['name']}.")
                    cur = conn.execute(
                        "UPDATE product SET stock=stock-? WHERE id=? AND stock>=? AND active=1",
                        (item["quantity"], product["id"], item["quantity"]))
                    if cur.rowcount != 1:
                        raise ValueError(f"Stock insuffisant : {product['name']}.")

                cur = conn.execute("""
                    INSERT INTO orders(
                        user_id,total,status,payment_method,payment_status,
                        transaction_id,delivery_address,delivery_city,customer_phone,delivery_fee
                    ) VALUES(?,?,?,?,?,?,?,?,?,?)
                """, (session["user_id"], total_amount, "pending", payment_method, "pending",
                      transaction_id, address, city, phone, delivery_fee))
                order_id = cur.lastrowid

                seller_ids = set()
                for item in items:
                    product = item["product"]
                    conn.execute("""
                        INSERT INTO order_items(order_id,product_id,quantity,unit_price,quote_id)
                        VALUES(?,?,?,?,?)
                    """, (order_id, product["id"], item["quantity"],
                          product["price"], product["quote_id"]))
                    seller_ids.add(product["seller_id"])
                    if product["quote_id"]:
                        cur = conn.execute(
                            """UPDATE quotes SET status='ordered' WHERE id=?
                               AND status='accepted' AND buyer_id=?""",
                            (product["quote_id"], session["user_id"]))
                        if cur.rowcount != 1:
                            raise ValueError("Une offre négociée n'est plus valable.")
                for sid in seller_ids:
                    notify(conn, sid, "order", f"Nouvelle commande #{order_id}",
                           "Une cliente a commandé vos produits.", url_for("seller_orders"))
    except ValueError as exc:
        flash(str(exc), "danger")
        return redirect(url_for("checkout"))
    except sqlite3.Error as exc:
        app.logger.error("Création de commande impossible : %s", exc)
        flash("Erreur interne, veuillez réessayer.", "danger")
        return redirect(url_for("checkout"))

    session["cart"] = {}
    session["cart_quotes"] = {}
    session.modified = True

    if payment_method == "cash":
        flash(f"Commande #{order_id} enregistrée. Paiement à la livraison.", "success")
        return redirect(url_for("my_orders"))
    return redirect(url_for("payment_initiate", order_id=order_id))


@app.route("/payment/initiate/<int:order_id>", methods=["GET", "POST"])
@login_required
def payment_initiate(order_id):
    """Envoie la cliente vers la page de paiement sécurisée CinetPay (séquestre)."""
    with connection() as conn:
        order = conn.execute("SELECT * FROM orders WHERE id=? AND user_id=?",
                             (order_id, session["user_id"])).fetchone()
        user = conn.execute("SELECT * FROM users WHERE id=?", (session["user_id"],)).fetchone()
    if not order or not user:
        flash("Commande introuvable.", "danger")
        return redirect(url_for("my_orders"))

    back = redirect(url_for("order_detail", order_id=order_id))

    if (order["payment_method"] != "cinetpay"
            or order["payment_status"] != "pending"
            or order["status"] == "cancelled"):
        flash("Cette commande ne peut pas être payée en ligne.", "warning")
        return back

    if not cinetpay_configured():
        flash("Le paiement en ligne est momentanément indisponible. "
              "Votre commande est enregistrée.", "warning")
        app.logger.error("CINETPAY_API_KEY / CINETPAY_SITE_ID manquants.")
        return back

    # Le montant vient TOUJOURS de la base, jamais du navigateur.
    amount = int(round(order["total"]))
    if amount < 100 or amount % 5 != 0:
        flash("Le montant de cette commande n'est pas éligible au paiement en ligne "
              "(minimum 100 FCFA, multiple de 5).", "danger")
        return back

    transaction_id = new_transaction_id()
    try:
        with connection() as conn:
            with immediate(conn):
                conn.execute("INSERT INTO payment_attempts(transaction_id, order_id) VALUES(?,?)",
                             (transaction_id, order_id))
                conn.execute("UPDATE orders SET transaction_id=? WHERE id=?",
                             (transaction_id, order_id))
    except sqlite3.Error as exc:
        app.logger.error("Enregistrement tentative de paiement impossible : %s", exc)
        flash("Erreur interne, veuillez réessayer.", "danger")
        return back

    names = (user["name"] or "Cliente").split() or ["Cliente"]
    first = names[0]
    surname = " ".join(names[1:]) or first
    payload = {
        "apikey": app.config["CINETPAY_API_KEY"],
        "site_id": app.config["CINETPAY_SITE_ID"],
        "transaction_id": transaction_id,
        "amount": amount,
        "currency": "XOF",
        "description": f"Commande SILUX HOUSE {order_id}",
        "customer_id": str(user["id"]),
        "customer_name": first,
        "customer_surname": surname,
        "customer_email": user["email"],
        "customer_phone_number": order["customer_phone"] or user["phone"],
        "customer_address": order["delivery_address"] or "Niamey",
        "customer_city": order["delivery_city"] or "Niamey",
        "customer_country": "NE",
        "customer_state": "NE",
        "customer_zip_code": "00000",
        "notify_url": f"{app.config['BASE_URL']}/payment/notify",
        "return_url": f"{app.config['BASE_URL']}/payment/return",
        "channels": "ALL",
        "lang": "FR",
        "metadata": str(order_id),
    }

    try:
        response = requests.post(f"{CINETPAY_API_URL}/payment", json=payload, timeout=15)
        response.raise_for_status()
        result = response.json()
    except (requests.RequestException, ValueError) as exc:
        app.logger.error("Initialisation CinetPay échouée (commande #%s) : %s", order_id, exc)
        flash("Impossible de joindre le service de paiement. Réessayez dans un instant.", "danger")
        return back

    payment_url = (result.get("data") or {}).get("payment_url")
    if str(result.get("code")) == "201" and payment_url:
        return redirect(payment_url)

    app.logger.error("CinetPay a refusé l'initialisation (commande #%s) : %s", order_id, result)
    flash("Le service de paiement a refusé la demande. Réessayez ou choisissez "
          "le paiement à la livraison.", "danger")
    return back


@app.route("/cinetpay/notify", methods=["GET", "POST"])  # ancien chemin, paiements en cours
@app.route("/payment/notify", methods=["GET", "POST"])
def payment_notify():
    """Webhook CinetPay : met la commande sous séquestre dès que le paiement est réussi.

    Rien dans la notification n'est cru sur parole : l'état et le montant sont
    revérifiés auprès de l'API CinetPay. Traitement idempotent.
    """
    if request.method == "GET":  # test d'accessibilité de l'URL par CinetPay
        return "OK", 200

    transaction_id = (
        request.form.get("cpm_trans_id") or request.form.get("transaction_id") or ""
    ).strip()
    if not TRANSACTION_ID_RE.match(transaction_id):
        return "OK", 200

    check_notify_token()
    ok, _state = update_payment_from_cinetpay(transaction_id)
    if not ok:
        return "ERROR", 500  # erreur temporaire : CinetPay réessaiera
    return "OK", 200


@app.route("/cinetpay/return", methods=["GET", "POST"])  # ancien chemin
@app.route("/payment/return", methods=["GET", "POST"])
def payment_return():
    """Retour de la cliente depuis CinetPay (GET ou POST selon le cas)."""
    transaction_id = (
        request.values.get("transaction_id") or request.values.get("cpm_trans_id") or ""
    ).strip()
    if not TRANSACTION_ID_RE.match(transaction_id):
        return redirect(url_for("my_orders"))

    if request.method == "POST":
        # Requête venue d'un autre site : le cookie de session n'est pas envoyé.
        update_payment_from_cinetpay(transaction_id)
        return redirect(url_for("payment_return", transaction_id=transaction_id), 303)

    _ok, state = update_payment_from_cinetpay(transaction_id)
    with connection() as conn:
        order = find_order_by_transaction(conn, transaction_id)

    if state == "paid":
        flash("Paiement confirmé et sécurisé par Trade Assurance. Merci pour votre commande !",
              "success")
    elif state == "failed":
        flash("Le paiement a été refusé ou annulé. La commande n'a pas été validée.", "danger")
    else:
        flash("Paiement en cours de vérification. Le statut sera mis à jour automatiquement.",
              "warning")

    if order and session.get("user_id") == order["user_id"]:
        return redirect(url_for("order_detail", order_id=order["id"]))
    return redirect(url_for("my_orders"))


# ============================================================================
# 11. COMMANDES CLIENT ET LIBÉRATION DU SÉQUESTRE
# ============================================================================
@app.route("/orders")
@login_required
def my_orders():
    with connection() as conn:
        orders = conn.execute(
            "SELECT * FROM orders WHERE user_id=? ORDER BY id DESC",
            (session["user_id"],)).fetchall()
    return render_template("orders.html", orders=orders)


@app.route("/orders/<int:order_id>")
@login_required
def order_detail(order_id):
    with connection() as conn:
        order = conn.execute("SELECT * FROM orders WHERE id=? AND user_id=?",
                             (order_id, session["user_id"])).fetchone()
        if not order:
            flash("Commande introuvable.", "danger")
            return redirect(url_for("my_orders"))
        items = conn.execute("""
            SELECT oi.*, p.name, p.seller_id
            FROM order_items oi JOIN product p ON p.id=oi.product_id
            WHERE oi.order_id=?
        """, (order_id,)).fetchall()
        dispute = conn.execute(
            "SELECT * FROM disputes WHERE order_id=? ORDER BY id DESC LIMIT 1",
            (order_id,)).fetchone()
    dispute_open = bool(dispute and dispute["status"] == "open")
    return render_template(
        "order_detail.html", order=order, items=items,
        dispute=dispute, dispute_reasons=DISPUTE_REASONS,
        can_dispute=(order["payment_status"] == "escrowed"
                     and order["status"] in ("processing", "shipped") and not dispute_open),
        can_confirm_receipt=(order["payment_status"] == "escrowed"
                             and order["status"] == "shipped"),
        escrow_active=(order["payment_status"] == "escrowed"),
        funds_released=(order["payment_status"] == "released"),
        can_cancel=(order["status"] == "pending"
                    and order["payment_status"] == "pending"),
        can_pay=(order["payment_method"] == "cinetpay"
                 and order["payment_status"] == "pending"
                 and order["status"] != "cancelled"),
    )


@app.post("/orders/<int:order_id>/confirm-receipt")
@login_required
def confirm_receipt(order_id):
    """Libération des fonds séquestre : réservée à l'acheteuse, idempotente."""
    try:
        with connection() as conn:
            with immediate(conn):
                order = conn.execute("SELECT * FROM orders WHERE id=? AND user_id=?",
                                     (order_id, session["user_id"])).fetchone()
                if not order:
                    flash("Commande introuvable.", "danger")
                    return redirect(url_for("my_orders"))
                if order["payment_status"] == "released":
                    flash("Les fonds ont déjà été libérés au vendeur.", "success")
                    return redirect(url_for("order_detail", order_id=order_id))
                if order["payment_status"] != "escrowed" or order["status"] != "shipped":
                    flash("Cette commande n'est pas prête pour la confirmation de réception.",
                          "warning")
                    return redirect(url_for("order_detail", order_id=order_id))
                cur = conn.execute("""
                    UPDATE orders SET payment_status='released', status='delivered',
                                      released_at=CURRENT_TIMESTAMP
                    WHERE id=? AND payment_status='escrowed' AND status='shipped'
                """, (order_id,))
                if cur.rowcount != 1:
                    flash("La commande a déjà été traitée.", "warning")
                    return redirect(url_for("order_detail", order_id=order_id))
                conn.execute("""UPDATE disputes SET status='released',
                                resolution_note='Réception confirmée par l''acheteuse',
                                resolved_at=CURRENT_TIMESTAMP
                                WHERE order_id=? AND status='open'""", (order_id,))
                for sid in order_seller_ids(conn, order_id):
                    refresh_seller_metrics(conn, sid)
                    notify(conn, sid, "order", f"Fonds libérés : commande #{order_id}",
                           "L'acheteuse a confirmé la réception. Les fonds vous sont acquis.",
                           url_for("seller_orders"))
    except sqlite3.Error as exc:
        app.logger.error("Libération séquestre #%s impossible : %s", order_id, exc)
        flash("Erreur interne, veuillez réessayer.", "danger")
        return redirect(url_for("order_detail", order_id=order_id))
    flash("Réception confirmée : les fonds ont été libérés au vendeur. Merci !", "success")
    return redirect(url_for("order_detail", order_id=order_id))


@app.post("/orders/<int:order_id>/cancel")
@login_required
def order_cancel(order_id):
    """Annulation par la cliente d'une commande non encore payée ni traitée."""
    with connection() as conn:
        with immediate(conn):
            order = conn.execute("SELECT * FROM orders WHERE id=? AND user_id=?",
                                 (order_id, session["user_id"])).fetchone()
            if not order:
                flash("Commande introuvable.", "danger")
                return redirect(url_for("my_orders"))
            if order["status"] == "cancelled":
                flash("Commande déjà annulée.", "success")
            elif order["status"] != "pending" or order["payment_status"] != "pending":
                flash("Cette commande ne peut plus être annulée en ligne.", "warning")
            else:
                cancel_order_in_tx(conn, order)
                flash("Commande annulée.", "success")
    return redirect(url_for("order_detail", order_id=order_id))


# ============================================================================
# 12. ESPACE VENDEUR
# ============================================================================
@app.route("/seller/products", methods=["GET", "POST"])
@login_required
@role_required("seller", "admin")
def seller_products():
    if request.method == "POST":
        name = clean_text(request.form.get("name"), 150)
        description = clean_text(request.form.get("description"), 3000)
        image_url = request.form.get("image_url", "").strip()[:500]
        category_id = to_int(request.form.get("category_id"), -1)
        price = parse_amount(request.form.get("price", "0"))
        stock = to_int(request.form.get("stock", "0"), -1)
        moq = to_int(request.form.get("moq", "1") or "1", -1)

        if price is None or stock < 0 or category_id < 0 or moq < 1:
            flash("Prix, stock, MOQ ou catégorie invalide.", "danger")
            return redirect(url_for("seller_products"))
        if not name or price < 0 or price > 1e10 or stock > 10_000_000 or moq > 1_000_000:
            flash("Informations produit invalides.", "danger")
            return redirect(url_for("seller_products"))

        old_price = None
        old_raw = request.form.get("old_price", "").strip()
        if old_raw:
            old_price = parse_amount(old_raw)
            if old_price is None or old_price > 1e10:
                flash("Ancien prix invalide.", "danger")
                return redirect(url_for("seller_products"))
            if old_price <= price:
                old_price = None

        if image_url and not image_url.lower().startswith(("http://", "https://")):
            image_url = ""

        upload = request.files.get("image")
        if upload and upload.filename:
            kind = sniff_image_type(upload.stream)
            if not allowed_file(upload.filename) or kind is None:
                flash("Format d'image non autorisé. Utilisez JPG, PNG ou WEBP.", "danger")
                return redirect(url_for("seller_products"))
            filename = f"{uuid.uuid4().hex}.{kind}"
            upload.save(os.path.join(UPLOAD_DIR, secure_filename(filename)))
            image_url = url_for("static", filename=f"uploads/{filename}")

        with connection() as conn:
            if not conn.execute("SELECT 1 FROM categories WHERE id=?",
                                (category_id,)).fetchone():
                flash("Catégorie invalide.", "danger")
                return redirect(url_for("seller_products"))
            conn.execute("""
                INSERT INTO product(
                    seller_id,category_id,name,description,price,old_price,moq,stock,image_url
                ) VALUES(?,?,?,?,?,?,?,?,?)
            """, (session["user_id"], category_id, name, description,
                  price, old_price, moq, stock, image_url))
            conn.commit()
        flash("Produit ajouté avec succès.", "success")
        return redirect(url_for("seller_products"))

    with connection() as conn:
        categories = conn.execute("SELECT * FROM categories ORDER BY name").fetchall()
        products = conn.execute("""
            SELECT p.*, c.name AS category_name
            FROM product p JOIN categories c ON c.id=p.category_id
            WHERE p.seller_id=? ORDER BY p.id DESC
        """, (session["user_id"],)).fetchall()
    return render_template("seller_products.html", categories=categories, products=products)


@app.route("/seller/orders")
@login_required
@role_required("seller", "admin")
def seller_orders():
    uid = session["user_id"]
    with connection() as conn:
        orders = conn.execute("""
            SELECT DISTINCT o.*, u.name AS customer_name,
                (SELECT COALESCE(SUM(oi2.quantity*oi2.unit_price),0)
                   FROM order_items oi2 JOIN product p2 ON p2.id=oi2.product_id
                  WHERE oi2.order_id=o.id AND p2.seller_id=:uid) AS seller_total,
                (SELECT COUNT(*) FROM disputes d
                  WHERE d.order_id=o.id AND d.status='open') AS dispute_open
            FROM orders o
            JOIN users u ON u.id=o.user_id
            JOIN order_items oi ON oi.order_id=o.id
            JOIN product p ON p.id=oi.product_id
            WHERE p.seller_id=:uid
            ORDER BY o.id DESC
        """, {"uid": uid}).fetchall()
        row = conn.execute("""
            SELECT
              COALESCE(SUM(CASE WHEN o.payment_status='escrowed'
                                THEN oi.quantity*oi.unit_price END),0) AS escrow,
              COALESCE(SUM(CASE WHEN o.payment_status='released'
                                THEN oi.quantity*oi.unit_price END),0) AS released,
              COALESCE(SUM(CASE WHEN o.payment_status='paid'
                                THEN oi.quantity*oi.unit_price END),0) AS cash_collected,
              COALESCE(SUM(CASE WHEN o.payment_status='refund_due'
                                THEN oi.quantity*oi.unit_price END),0) AS refund_due,
              COALESCE(SUM(CASE WHEN o.payment_method='cash' AND o.payment_status='pending'
                                 AND o.status!='cancelled'
                                THEN oi.quantity*oi.unit_price END),0) AS cash_pending
            FROM order_items oi
            JOIN orders o ON o.id=oi.order_id
            JOIN product p ON p.id=oi.product_id
            WHERE p.seller_id=?
        """, (uid,)).fetchone()
    balances = dict(row)
    balances["total_secured"] = balances["escrow"] + balances["released"]
    return render_template("seller_orders.html", orders=orders, balances=balances)


@app.post("/seller/orders/<int:order_id>/status")
@login_required
@role_required("seller", "admin")
def seller_order_status(order_id):
    status = request.form.get("status", "processing")
    if status not in SELLER_ALLOWED_STATUSES:
        flash("Statut invalide.", "danger")
        return redirect(url_for("seller_orders"))
    with connection() as conn:
        owns = conn.execute("""
            SELECT 1 FROM order_items oi JOIN product p ON p.id=oi.product_id
            WHERE oi.order_id=? AND p.seller_id=? LIMIT 1
        """, (order_id, session["user_id"])).fetchone()
        if not owns and session.get("user_role") != "admin":
            flash("Commande non autorisée.", "danger")
            return redirect(url_for("seller_orders"))
        try:
            ok, message, category = apply_order_status(
                conn, order_id, status, session.get("user_role"))
        except sqlite3.Error as exc:
            app.logger.error("Statut commande #%s : %s", order_id, exc)
            ok, message, category = False, "Erreur interne, veuillez réessayer.", "danger"
    flash(message, category)
    return redirect(url_for("seller_orders"))


# ============================================================================
# 13. ADMINISTRATION
# ============================================================================
@app.route("/admin/users")
@login_required
@role_required("admin")
def admin_users():
    with connection() as conn:
        users = conn.execute("""
            SELECT id,name,email,phone,role,city,company_name,company_type,
                   sourcing_purpose,years_active,reorder_rate,created_at
            FROM users ORDER BY id DESC""").fetchall()
    return render_template("admin_users.html", users=users)


@app.post("/admin/users/<int:user_id>/role")
@login_required
@role_required("admin")
def admin_user_role(user_id):
    role = request.form.get("role", "customer")
    if role not in {"customer", "seller", "admin"}:
        flash("Rôle invalide.", "danger")
        return redirect(url_for("admin_users"))
    if user_id == session.get("user_id") and role != "admin":
        flash("Vous ne pouvez pas retirer votre propre rôle administrateur ici.", "warning")
        return redirect(url_for("admin_users"))
    with connection() as conn:
        conn.execute("UPDATE users SET role=? WHERE id=?", (role, user_id))
        conn.commit()
    flash("Rôle utilisateur mis à jour.", "success")
    return redirect(url_for("admin_users"))


@app.post("/admin/users/<int:user_id>/metrics")
@login_required
@role_required("admin")
def admin_user_metrics(user_id):
    """Ancienneté vérifiée par l'administration (le taux de fidélité est calculé)."""
    years = min(max(to_int(request.form.get("years_active"), 0), 0), 100)
    with connection() as conn:
        conn.execute("UPDATE users SET years_active=? WHERE id=?", (years, user_id))
        conn.commit()
    flash("Ancienneté du vendeur mise à jour.", "success")
    return redirect(url_for("admin_users"))


@app.post("/admin/products/<int:product_id>/toggle")
@login_required
@role_required("admin")
def admin_product_toggle(product_id):
    with connection() as conn:
        conn.execute(
            "UPDATE product SET active = CASE active WHEN 1 THEN 0 ELSE 1 END "
            "WHERE id=? AND deleted=0",
            (product_id,))
        conn.commit()
    flash("Visibilité du produit mise à jour.", "success")
    return redirect(url_for("admin"))


@app.route("/admin")
@login_required
@role_required("admin")
def admin():
    with connection() as conn:
        stats = {
            "users": conn.execute("SELECT COUNT(*) c FROM users").fetchone()["c"],
            "products": conn.execute(
                "SELECT COUNT(*) c FROM product WHERE active=1").fetchone()["c"],
            "orders": conn.execute("SELECT COUNT(*) c FROM orders").fetchone()["c"],
            "revenue": conn.execute(
                "SELECT COALESCE(SUM(total),0) s FROM orders "
                "WHERE payment_status IN ('paid','released')").fetchone()["s"],
            "escrow": conn.execute(
                "SELECT COALESCE(SUM(total),0) s FROM orders "
                "WHERE payment_status='escrowed'").fetchone()["s"],
            "refunds_due": conn.execute(
                "SELECT COUNT(*) c FROM orders WHERE payment_status='refund_due'"
            ).fetchone()["c"],
            "open_rfq": conn.execute(
                "SELECT COUNT(*) c FROM rfq WHERE status='open'").fetchone()["c"],
            "open_disputes": conn.execute(
                "SELECT COUNT(*) c FROM disputes WHERE status='open'").fetchone()["c"],
        }
        orders = conn.execute("""
            SELECT o.*,u.name AS customer_name
            FROM orders o JOIN users u ON u.id=o.user_id
            ORDER BY o.id DESC LIMIT 50
        """).fetchall()
    return render_template("admin.html", stats=stats, orders=orders)


@app.post("/admin/orders/<int:order_id>/status")
@login_required
@role_required("admin")
def admin_order_status(order_id):
    status = request.form.get("status", "pending")
    with connection() as conn:
        try:
            ok, message, category = apply_order_status(conn, order_id, status, "admin")
        except sqlite3.Error as exc:
            app.logger.error("Statut commande #%s : %s", order_id, exc)
            ok, message, category = False, "Erreur interne, veuillez réessayer.", "danger"
    flash(message, category)
    return redirect(url_for("admin"))


# ============================================================================
# 14. MESSAGERIE ET NÉGOCIATION
# ============================================================================
def load_conversation(conn, conversation_id, user_id):
    """Conversation visible uniquement par ses deux participants (anti-IDOR)."""
    row = conn.execute("""
        SELECT c.*, p.name AS product_name, p.image_url AS product_image,
               p.price AS product_price, p.old_price AS product_old_price,
               p.stock AS product_stock, p.moq AS product_moq, p.active AS product_active,
               ub.name AS buyer_name, ub.company_name AS buyer_company,
               us.name AS seller_name, us.company_name AS seller_company,
               us.company_type AS seller_company_type,
               us.years_active AS seller_years_active,
               us.reorder_rate AS seller_reorder_rate
        FROM conversations c
        JOIN product p ON p.id=c.product_id
        JOIN users ub ON ub.id=c.buyer_id
        JOIN users us ON us.id=c.seller_id
        WHERE c.id=? AND (c.buyer_id=? OR c.seller_id=?)
    """, (conversation_id, user_id, user_id)).fetchone()
    if not row:
        abort(404)
    return row


def quote_state(quote):
    if quote["status"] in ("pending", "accepted") and quote["expired"]:
        return "expired"
    return quote["status"]


@app.route("/messages")
@login_required
def messages_hub():
    uid = session["user_id"]
    tab = request.args.get("tab", "")
    if tab not in MESSAGE_TABS:
        tab = ""
    q = clean_text(request.args.get("q", ""), 80)

    sql = """
        SELECT * FROM (
            SELECT c.id, c.product_id, c.last_message_at, c.buyer_id, c.seller_id,
                   p.name AS product_name, p.image_url AS product_image,
                   CASE WHEN c.buyer_id=:uid THEN us.id ELSE ub.id END AS other_id,
                   CASE WHEN c.buyer_id=:uid THEN us.name ELSE ub.name END AS other_name,
                   CASE WHEN c.buyer_id=:uid
                        THEN COALESCE(NULLIF(us.company_name,''), us.name)
                        ELSE COALESCE(NULLIF(ub.company_name,''), ub.name) END AS other_company,
                   (SELECT m.body FROM messages m WHERE m.conversation_id=c.id
                     ORDER BY m.id DESC LIMIT 1) AS last_body,
                   (SELECT m.kind FROM messages m WHERE m.conversation_id=c.id
                     ORDER BY m.id DESC LIMIT 1) AS last_kind,
                   (SELECT COUNT(*) FROM messages m WHERE m.conversation_id=c.id
                      AND m.sender_id!=:uid AND m.is_read=0) AS unread,
                   (SELECT COUNT(*) FROM quotes qq WHERE qq.conversation_id=c.id) AS quote_count
            FROM conversations c
            JOIN product p ON p.id=c.product_id
            JOIN users ub ON ub.id=c.buyer_id
            JOIN users us ON us.id=c.seller_id
            WHERE c.buyer_id=:uid OR c.seller_id=:uid
        ) t WHERE 1=1"""
    params = {"uid": uid}
    if q:
        sql += (f" AND (fold(t.product_name) LIKE :q {ESC} OR fold(t.other_name) LIKE :q {ESC}"
                f" OR fold(t.other_company) LIKE :q {ESC}"
                f" OR EXISTS (SELECT 1 FROM messages mm WHERE mm.conversation_id=t.id"
                f" AND fold(mm.body) LIKE :q {ESC}))")
        params["q"] = f"%{like_escape(fold_text(q))}%"
    sql += " ORDER BY t.last_message_at DESC, t.id DESC LIMIT 200"

    with connection() as conn:
        conversations = [dict(r) for r in conn.execute(sql, params).fetchall()]
        notifications = [dict(r) for r in conn.execute(
            "SELECT * FROM notifications WHERE user_id=? ORDER BY id DESC LIMIT 100",
            (uid,)).fetchall()]
        notif_unread = sum(1 for n in notifications if not n["is_read"])
        if tab == "notification" and notif_unread:
            conn.execute("UPDATE notifications SET is_read=1 WHERE user_id=? AND is_read=0",
                         (uid,))
            conn.commit()

    counts = {
        "orders": sum(1 for c in conversations if c["quote_count"] > 0),
        "notification": notif_unread,
        "other": sum(1 for c in conversations if c["quote_count"] == 0),
        "unread_total": sum(c["unread"] for c in conversations),
    }
    if tab == "orders":
        conversations = [c for c in conversations if c["quote_count"] > 0]
    elif tab == "other":
        conversations = [c for c in conversations if c["quote_count"] == 0]
    elif tab == "notification":
        conversations = []
    return render_template("messages.html", conversations=conversations,
                           notifications=notifications, tab=tab, q=q, counts=counts)


@app.post("/chat/start/<int:product_id>")
@login_required
def chat_start(product_id):
    uid = session["user_id"]
    if rate_limited(f"chatstart:{uid}", 20, 3600, shared=True):
        abort(429)
    with connection() as conn:
        product = conn.execute(
            "SELECT id, seller_id, name FROM product WHERE id=? AND active=1",
            (product_id,)).fetchone()
        if not product:
            flash("Produit introuvable.", "danger")
            return redirect(url_for("home"))
        if product["seller_id"] == uid:
            flash("Vous ne pouvez pas vous écrire à vous-même.", "warning")
            return redirect(url_for("product_detail", product_id=product_id))
        conn.execute("""INSERT OR IGNORE INTO conversations(product_id, buyer_id, seller_id)
                        VALUES(?,?,?)""", (product_id, uid, product["seller_id"]))
        conv = conn.execute("""SELECT id FROM conversations
                               WHERE product_id=? AND buyer_id=? AND seller_id=?""",
                            (product_id, uid, product["seller_id"])).fetchone()
        first = clean_text(request.form.get("body"), 2000)
        if first:
            conn.execute("INSERT INTO messages(conversation_id, sender_id, body) VALUES(?,?,?)",
                         (conv["id"], uid, first))
            conn.execute("UPDATE conversations SET last_message_at=CURRENT_TIMESTAMP WHERE id=?",
                         (conv["id"],))
        conn.commit()
    return redirect(url_for("chat_view", conversation_id=conv["id"]))


@app.route("/chat/<int:conversation_id>")
@login_required
def chat_view(conversation_id):
    uid = session["user_id"]
    tab = request.args.get("tab", "")
    if tab not in MESSAGE_TABS:
        tab = ""
    q = clean_text(request.args.get("q", ""), 80)

    with connection() as conn:
        conv = load_conversation(conn, conversation_id, uid)
        conn.execute("""UPDATE messages SET is_read=1
                        WHERE conversation_id=? AND sender_id!=? AND is_read=0""",
                     (conversation_id, uid))
        conn.commit()

        sql = """SELECT m.*, u.name AS sender_name,
                        COALESCE(NULLIF(u.company_name,''), u.name) AS sender_company
                 FROM messages m JOIN users u ON u.id=m.sender_id
                 WHERE m.conversation_id=:cid"""
        params = {"cid": conversation_id}
        if tab:
            sql += " AND m.kind=:kind"
            params["kind"] = MESSAGE_TABS[tab]
        if q:
            sql += f" AND fold(m.body) LIKE :q {ESC}"
            params["q"] = f"%{like_escape(fold_text(q))}%"
        sql += " ORDER BY m.id DESC LIMIT 300"
        rows = list(reversed(conn.execute(sql, params).fetchall()))

        quotes = {}
        for qrow in conn.execute(
                """SELECT *, (expires_at < datetime('now')) AS expired
                   FROM quotes WHERE conversation_id=? ORDER BY id DESC""",
                (conversation_id,)).fetchall():
            d = dict(qrow)
            d["state"] = quote_state(qrow)
            d["total"] = d["custom_price"] * d["quantity"]
            d["can_accept"] = (uid == conv["buyer_id"] and d["state"] in ("pending", "accepted"))
            d["can_decline"] = (uid == conv["buyer_id"] and d["state"] == "pending")
            d["can_withdraw"] = (uid == conv["seller_id"] and d["state"] == "pending")
            quotes[d["id"]] = d

    messages = []
    for r in rows:
        m = dict(r)
        m["mine"] = m["sender_id"] == uid
        m["quote"] = quotes.get(m["quote_id"]) if m["quote_id"] else None
        messages.append(m)

    with connection() as conn:
        last_id = conn.execute(
            "SELECT COALESCE(MAX(id),0) FROM messages WHERE conversation_id=?",
            (conversation_id,)).fetchone()[0]
    is_seller = uid == conv["seller_id"]
    other = ({"id": conv["buyer_id"], "name": conv["buyer_name"],
              "company": conv["buyer_company"] or conv["buyer_name"]}
             if is_seller else
             {"id": conv["seller_id"], "name": conv["seller_name"],
              "company": conv["seller_company"] or conv["seller_name"],
              "company_type": conv["seller_company_type"],
              "years_active": conv["seller_years_active"],
              "reorder_rate": conv["seller_reorder_rate"]})
    return render_template(
        "chat.html", conversation=conv, messages=messages, quotes=list(quotes.values()),
        last_id=last_id,
        other=other, is_seller=is_seller, can_quote=is_seller, tab=tab, q=q,
        quote_validity_days=QUOTE_VALIDITY_DAYS)


@app.post("/chat/<int:conversation_id>/send")
@login_required
def chat_send(conversation_id):
    uid = session["user_id"]
    if rate_limited(f"chatsend:{uid}", 40, 60):
        flash("Vous écrivez trop vite. Patientez un instant.", "warning")
        return redirect(url_for("chat_view", conversation_id=conversation_id))
    body = clean_text(request.form.get("body"), 2000)
    with connection() as conn:
        load_conversation(conn, conversation_id, uid)
        if not body:
            flash("Écrivez un message.", "warning")
        else:
            conn.execute("INSERT INTO messages(conversation_id, sender_id, body) VALUES(?,?,?)",
                         (conversation_id, uid, body))
            conn.execute("UPDATE conversations SET last_message_at=CURRENT_TIMESTAMP WHERE id=?",
                         (conversation_id,))
            conn.commit()
    return redirect(url_for("chat_view", conversation_id=conversation_id) + "#bas")


@app.post("/chat/<int:conversation_id>/quote")
@login_required
def chat_quote(conversation_id):
    """Devis chiffré (custom_price) émis par le vendeur propriétaire du produit."""
    uid = session["user_id"]
    if rate_limited(f"quote:{uid}", 30, 3600):
        abort(429)
    with connection() as conn:
        conv = load_conversation(conn, conversation_id, uid)
        if uid != conv["seller_id"]:
            abort(403)
        back = redirect(url_for("chat_view", conversation_id=conversation_id) + "#bas")
        product = conn.execute(
            "SELECT id, price, stock, active FROM product WHERE id=? AND seller_id=?",
            (conv["product_id"], uid)).fetchone()
        if not product or not product["active"]:
            flash("Produit indisponible.", "danger")
            return back
        custom_price = parse_amount(request.form.get("custom_price"))
        quantity = to_int(request.form.get("quantity"), 0)
        note = clean_text(request.form.get("note"), 500)
        if custom_price is None or custom_price <= 0 or custom_price > product["price"]:
            flash("Le prix négocié doit être positif et ne pas dépasser le prix catalogue.",
                  "danger")
            return back
        custom_price = int(round(custom_price))
        if custom_price % 5 != 0 or custom_price < 5:
            flash("Le prix négocié doit être un multiple de 5 FCFA (paiement en ligne).",
                  "danger")
            return back
        if quantity < 1 or quantity > product["stock"]:
            flash(f"Quantité invalide (stock disponible : {product['stock']}).", "danger")
            return back
        with immediate(conn):
            conn.execute("""UPDATE quotes SET status='superseded'
                            WHERE conversation_id=? AND status='pending'""",
                         (conversation_id,))
            cur = conn.execute(f"""
                INSERT INTO quotes(conversation_id, product_id, buyer_id, seller_id,
                                   custom_price, quantity, note, expires_at)
                VALUES(?,?,?,?,?,?,?, datetime('now', '+{QUOTE_VALIDITY_DAYS} days'))
            """, (conversation_id, conv["product_id"], conv["buyer_id"], uid,
                  custom_price, quantity, note))
            qid = cur.lastrowid
            conn.execute("""INSERT INTO messages(conversation_id, sender_id, kind, body, quote_id)
                            VALUES(?,?,?,?,?)""",
                         (conversation_id, uid, "quote", note or "Offre spéciale", qid))
            conn.execute("UPDATE conversations SET last_message_at=CURRENT_TIMESTAMP WHERE id=?",
                         (conversation_id,))
            notify(conn, conv["buyer_id"], "quote",
                   f"Offre spéciale : {conv['product_name']}",
                   f"{format_fcfa(custom_price)} FCFA l'unité pour {quantity} unité(s).",
                   url_for("chat_view", conversation_id=conversation_id))
    flash("Offre envoyée à l'acheteur.", "success")
    return back


def load_quote_for_buyer(conn, quote_id, user_id):
    return conn.execute("""
        SELECT q.*, (q.expires_at < datetime('now')) AS expired,
               p.name AS product_name, p.stock AS product_stock, p.active AS product_active
        FROM quotes q JOIN product p ON p.id=q.product_id
        WHERE q.id=? AND q.buyer_id=?""", (quote_id, user_id)).fetchone()


@app.post("/quote/<int:quote_id>/accept")
@login_required
def quote_accept(quote_id):
    """Accepter l'offre : le panier serveur reçoit le produit au prix négocié."""
    uid = session["user_id"]
    with connection() as conn:
        quote = load_quote_for_buyer(conn, quote_id, uid)
        if not quote:
            abort(404)
        chat = redirect(url_for("chat_view", conversation_id=quote["conversation_id"]))
        if quote["status"] not in ("pending", "accepted"):
            flash("Cette offre n'est plus disponible.", "warning")
            return chat
        if quote["expired"]:
            flash("Cette offre a expiré.", "warning")
            return chat
        if not quote["product_active"] or quote["product_stock"] < quote["quantity"]:
            flash("Stock insuffisant pour cette offre.", "danger")
            return chat
        with immediate(conn):
            cur = conn.execute("""UPDATE quotes SET status='accepted', responded_at=CURRENT_TIMESTAMP
                                  WHERE id=? AND status IN ('pending','accepted')""",
                               (quote_id,))
            if cur.rowcount != 1:
                flash("Cette offre n'est plus disponible.", "warning")
                return chat
            if quote["status"] == "pending":
                conn.execute("""INSERT INTO messages(conversation_id, sender_id, kind, body)
                                VALUES(?,?,?,?)""",
                             (quote["conversation_id"], uid, "system",
                              f"Offre acceptée : {format_fcfa(quote['custom_price'])} FCFA "
                              f"x {quote['quantity']}."))
                conn.execute(
                    "UPDATE conversations SET last_message_at=CURRENT_TIMESTAMP WHERE id=?",
                    (quote["conversation_id"],))
                notify(conn, quote["seller_id"], "quote",
                       f"Offre acceptée : {quote['product_name']}",
                       "L'acheteur a ajouté votre offre à son panier.",
                       url_for("chat_view", conversation_id=quote["conversation_id"]))
    cart = dict(session.get("cart", {}))
    quotes = dict(session.get("cart_quotes", {}))
    cart[str(quote["product_id"])] = quote["quantity"]
    quotes[str(quote["product_id"])] = quote["id"]
    session["cart"] = cart
    session["cart_quotes"] = quotes
    session.modified = True
    flash("Offre acceptée : le produit est dans votre panier au prix négocié.", "success")
    return redirect(url_for("view_cart"))


@app.post("/quote/<int:quote_id>/decline")
@login_required
def quote_decline(quote_id):
    """L'acheteur refuse l'offre, ou le vendeur la retire."""
    uid = session["user_id"]
    with connection() as conn:
        quote = conn.execute("SELECT * FROM quotes WHERE id=? AND (buyer_id=? OR seller_id=?)",
                             (quote_id, uid, uid)).fetchone()
        if not quote:
            abort(404)
        new_status = "declined" if uid == quote["buyer_id"] else "withdrawn"
        with immediate(conn):
            cur = conn.execute(
                """UPDATE quotes SET status=?, responded_at=CURRENT_TIMESTAMP
                   WHERE id=? AND status='pending'""", (new_status, quote_id))
            if cur.rowcount == 1:
                text = "Offre refusée." if new_status == "declined" else "Offre retirée."
                conn.execute("""INSERT INTO messages(conversation_id, sender_id, kind, body)
                                VALUES(?,?,?,?)""",
                             (quote["conversation_id"], uid, "system", text))
                conn.execute(
                    "UPDATE conversations SET last_message_at=CURRENT_TIMESTAMP WHERE id=?",
                    (quote["conversation_id"],))
                other = quote["seller_id"] if uid == quote["buyer_id"] else quote["buyer_id"]
                notify(conn, other, "quote", text, "",
                       url_for("chat_view", conversation_id=quote["conversation_id"]))
    return redirect(url_for("chat_view", conversation_id=quote["conversation_id"]))


# ============================================================================
# 15. RFQ : APPELS D'OFFRES
# ============================================================================
@app.route("/rfq/new", methods=["GET", "POST"])
@login_required
def rfq_new():
    if request.method == "POST":
        uid = session["user_id"]
        if rate_limited(f"rfq:{uid}", 10, 3600, shared=True):
            abort(429)
        title = clean_text(request.form.get("title"), 150)
        description = clean_text(request.form.get("description"), 3000)
        quantity = to_int(request.form.get("quantity"), 0)
        moq = to_int(request.form.get("moq") or "1", 0)
        city = clean_text(request.form.get("delivery_city"), 80) or "Niamey"
        budget_raw = request.form.get("budget_max", "").strip()
        budget = parse_amount(budget_raw) if budget_raw else None

        if len(title) < 5 or len(description) < 10:
            flash("Précisez un titre (5 caractères min.) et le détail de votre besoin.", "danger")
        elif quantity < 1 or quantity > 10_000_000:
            flash("Quantité invalide.", "danger")
        elif moq < 1 or moq > quantity:
            flash("Le MOQ doit être compris entre 1 et la quantité demandée.", "danger")
        elif budget_raw and (budget is None or budget < 0 or budget > 1e11):
            flash("Budget invalide.", "danger")
        else:
            with connection() as conn:
                cur = conn.execute("""
                    INSERT INTO rfq(buyer_id,title,description,quantity,moq,budget_max,delivery_city)
                    VALUES(?,?,?,?,?,?,?)""",
                    (uid, title, description, quantity, moq, budget, city))
                for seller in conn.execute(
                        "SELECT id FROM users WHERE role='seller' AND id!=?", (uid,)):
                    notify(conn, seller["id"], "rfq", f"Nouvel appel d'offres : {title}",
                           f"{quantity} unité(s), livraison à {city}.",
                           url_for("rfq_marketplace"))
                conn.commit()
                rfq_id = cur.lastrowid
            flash(f"Appel d'offres #{rfq_id} publié. Les vendeurs vont vous répondre.",
                  "success")
            return redirect(url_for("my_rfq"))
        return redirect(url_for("rfq_new"))
    return render_template("rfq_new.html")


@app.route("/rfq/mine")
@login_required
def my_rfq():
    uid = session["user_id"]
    with connection() as conn:
        rfqs = [dict(r) for r in conn.execute(
            "SELECT * FROM rfq WHERE buyer_id=? ORDER BY id DESC LIMIT 100", (uid,))]
        offers_by_rfq = defaultdict(list)
        if rfqs:
            ids = [r["id"] for r in rfqs]
            ph = ",".join("?" for _ in ids)
            for o in conn.execute(f"""
                SELECT rq.*, u.name AS seller_name,
                       COALESCE(NULLIF(u.company_name,''), u.name) AS seller_company,
                       u.company_type, u.years_active, u.reorder_rate, u.phone AS seller_phone
                FROM rfq_quotes rq JOIN users u ON u.id=rq.seller_id
                WHERE rq.rfq_id IN ({ph})
                ORDER BY rq.unit_price ASC, rq.created_at ASC""", ids):
                offers_by_rfq[o["rfq_id"]].append(dict(o))
    for r in rfqs:
        offers = offers_by_rfq.get(r["id"], [])
        for rank, offer in enumerate(offers, start=1):
            offer["rank"] = rank
            offer["total_price"] = offer["unit_price"] * r["quantity"]
            offer["within_budget"] = (r["budget_max"] is None
                                      or offer["total_price"] <= r["budget_max"])
        r["offers"] = offers
        r["best_price"] = offers[0]["unit_price"] if offers else None
    return render_template("my_rfq.html", rfqs=rfqs)


@app.post("/rfq/<int:rfq_id>/close")
@login_required
def rfq_close(rfq_id):
    with connection() as conn:
        conn.execute("UPDATE rfq SET status='closed' WHERE id=? AND buyer_id=?",
                     (rfq_id, session["user_id"]))
        conn.commit()
    flash("Appel d'offres clôturé.", "success")
    return redirect(url_for("my_rfq"))


@app.route("/rfq/marketplace")
@login_required
@role_required("seller", "admin")
def rfq_marketplace():
    uid = session["user_id"]
    q = clean_text(request.args.get("q", ""), 80)
    city = clean_text(request.args.get("city", ""), 80)
    page = max(1, to_int(request.args.get("page"), 1))
    per_page = 30

    sql = """
        SELECT r.*, u.name AS buyer_name,
               COALESCE(NULLIF(u.company_name,''), u.name) AS buyer_company,
               u.company_type AS buyer_company_type, u.sourcing_purpose AS buyer_purpose,
               (SELECT COUNT(*) FROM rfq_quotes x WHERE x.rfq_id=r.id) AS offers_count,
               mq.id AS my_quote_id, mq.unit_price AS my_unit_price,
               mq.lead_time_days AS my_lead_time, mq.comment AS my_comment
        FROM rfq r
        JOIN users u ON u.id=r.buyer_id
        LEFT JOIN rfq_quotes mq ON mq.rfq_id=r.id AND mq.seller_id=:uid
        WHERE r.status='open' AND r.buyer_id!=:uid"""
    params = {"uid": uid, "limit": per_page + 1, "offset": (page - 1) * per_page}
    if q:
        sql += f" AND (fold(r.title) LIKE :q {ESC} OR fold(r.description) LIKE :q {ESC})"
        params["q"] = f"%{like_escape(fold_text(q))}%"
    if city:
        sql += f" AND fold(r.delivery_city) LIKE :city {ESC}"
        params["city"] = f"%{like_escape(fold_text(city))}%"
    sql += " ORDER BY r.id DESC LIMIT :limit OFFSET :offset"
    with connection() as conn:
        rows = [dict(r) for r in conn.execute(sql, params).fetchall()]
    has_next = len(rows) > per_page
    return render_template("rfq_marketplace.html", rfqs=rows[:per_page], q=q, city=city,
                           page=page, has_next=has_next)


@app.post("/rfq/<int:rfq_id>/quote")
@login_required
@role_required("seller", "admin")
def rfq_quote(rfq_id):
    """Soumettre ou rééditer une cotation chiffrée (une par vendeur et par appel d'offres)."""
    uid = session["user_id"]
    if rate_limited(f"rfqquote:{uid}", 60, 3600):
        abort(429)
    unit_price = parse_amount(request.form.get("unit_price"))
    lead_time = to_int(request.form.get("lead_time_days"), 0)
    comment = clean_text(request.form.get("comment"), 1000)
    back = redirect(url_for("rfq_marketplace"))
    if unit_price is None or unit_price <= 0 or unit_price > 1e10:
        flash("Prix unitaire invalide.", "danger")
        return back
    if lead_time < 0 or lead_time > 365:
        flash("Délai invalide (0 à 365 jours).", "danger")
        return back
    with connection() as conn:
        with immediate(conn):
            rfq = conn.execute("SELECT * FROM rfq WHERE id=?", (rfq_id,)).fetchone()
            if not rfq or rfq["status"] != "open":
                flash("Cet appel d'offres n'est plus ouvert.", "warning")
                return back
            if rfq["buyer_id"] == uid:
                flash("Vous ne pouvez pas coter votre propre appel d'offres.", "warning")
                return back
            existing = conn.execute(
                "SELECT id FROM rfq_quotes WHERE rfq_id=? AND seller_id=?",
                (rfq_id, uid)).fetchone()
            conn.execute("""
                INSERT INTO rfq_quotes(rfq_id, seller_id, unit_price, lead_time_days, comment)
                VALUES(?,?,?,?,?)
                ON CONFLICT(rfq_id, seller_id) DO UPDATE SET
                    unit_price=excluded.unit_price,
                    lead_time_days=excluded.lead_time_days,
                    comment=excluded.comment,
                    updated_at=CURRENT_TIMESTAMP
            """, (rfq_id, uid, unit_price, lead_time, comment))
            notify(conn, rfq["buyer_id"], "rfq",
                   f"{'Offre mise à jour' if existing else 'Nouvelle offre'} : {rfq['title']}",
                   f"{format_fcfa(unit_price)} FCFA l'unité.", url_for("my_rfq"))
    flash("Votre cotation a été mise à jour." if existing else "Votre cotation a été envoyée.",
          "success")
    return back


# ============================================================================
# 16. SOURCING IA
# ============================================================================
@app.route("/ai-sourcing")
def ai_sourcing():
    query = clean_text(request.args.get("q", ""), 300)
    keywords, ignored = extract_keywords_detail(query)
    results = []
    with connection() as conn:
        if keywords:
            results = [dict(r) for r in search_products(conn, keywords, limit=40)]
            if session.get("user_id"):
                record_search(conn, session["user_id"], keywords)
    return render_template("ai_sourcing.html", query=query, keywords=keywords,
                           ignored_words=ignored, results=results,
                           logged_in=bool(session.get("user_id")))


@app.get("/api/sourcing-suggestions")
def api_sourcing_suggestions():
    """Suggestions prédictives (JSON) : historique d'achat, recherches et consultations."""
    uid = session.get("user_id")
    if not uid:
        return jsonify({"error": "auth_required", "suggestions": [], "keywords": []}), 401
    if rate_limited(f"suggest:{uid}", 90, 60):
        return jsonify({"error": "rate_limited", "suggestions": [], "keywords": []}), 429
    current = clean_text(request.args.get("q", ""), 300)
    with connection() as conn:
        keywords, cards, mode = personalized_suggestions(conn, uid, current)
    body = json.dumps({"mode": mode, "keywords": keywords, "suggestions": cards},
                      ensure_ascii=False, sort_keys=True)
    response = make_response(body)
    response.mimetype = "application/json"
    response.headers["Cache-Control"] = "private, no-cache"
    response.headers["Vary"] = "Cookie"
    response.add_etag()
    return response.make_conditional(request)


# ============================================================================
# 17. API PUBLIQUE ET ERREURS
# ============================================================================
@app.get("/api/products")
def api_products():
    with connection() as conn:
        rows = conn.execute("""
            SELECT p.id,p.name,p.description,p.price,p.old_price,p.moq,p.stock,p.image_url,
                   c.name AS category
            FROM product p JOIN categories c ON c.id=p.category_id
            WHERE p.active=1 ORDER BY p.id DESC
        """).fetchall()
    return jsonify([dict(row) for row in rows])


def render_error(code, message):
    return render_template("error.html", code=code, message=message), code


@app.errorhandler(400)
def error_400(_):
    return render_error(400, "Requête invalide.")


@app.errorhandler(403)
def error_403(_):
    return render_error(403, "Accès non autorisé.")


@app.errorhandler(404)
def error_404(_):
    return render_error(404, "Page introuvable.")


@app.errorhandler(405)
def error_405(_):
    return render_error(405, "Action non autorisée.")


@app.errorhandler(413)
def error_413(_):
    return render_error(413, "Image trop volumineuse (5 Mo maximum).")


@app.errorhandler(429)
def error_429(_):
    return render_error(429, "Trop de requêtes. Patientez quelques instants.")


@app.errorhandler(500)
def error_500(_):
    return render_error(500, "Erreur interne du serveur.")


init_db()

start_workers()

if not cinetpay_configured():
    app.logger.warning("CinetPay non configuré : définissez CINETPAY_API_KEY et CINETPAY_SITE_ID.")

if __name__ == "__main__":
    app.run(
        host="0.0.0.0",
        port=int(os.environ.get("PORT", 5000)),
        debug=os.environ.get("FLASK_DEBUG", "0") == "1"
    )
