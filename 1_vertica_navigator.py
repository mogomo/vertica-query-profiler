# =============================================================================
# File name: 1_vertica_navigator.py
# Author: Maya Goldberg
#
# Vertica Navigator - browser-based SQL workspace and query profiler for Vertica Analytic Database.
#
# Purpose: Multi-user Vertica Navigator as a single-file Python server that authenticates end-users against Vertica,
#          lets them browse schemas, run SQL, and profile a query into an interactive
#          execution tree, a cross-node skew view, and a rule-based scorecard -
#          all in the browser over HTTPS.
#
# Usage:
#   As user dbadmin:   python3 1_vertica_navigator.py
# 
# Install:  pip install vertica-python cryptography
#           
#           Or before running this script on RHEL:
#           sudo python3 -m pip install vertica-python cryptography
#
# Docs:     see README.md
# License:  MIT (see LICENSE)
#
#
#
#
#
# Optional environment variables:
#   export VERTICA_NAVIGATOR_HOST=<server_bind_ip>
#   export VERTICA_NAVIGATOR_PUBLIC_HOST=<server_host_or_dns_name>
#   export VERTICA_NAVIGATOR_HTTP_PORT=8002
#   export VERTICA_NAVIGATOR_HTTPS_PORT=8444
#   export VERTICA_NAVIGATOR_HTTPS_ENABLED=1
#   export VERTICA_NAVIGATOR_HTTP_REDIRECT_TO_HTTPS=1
#   export VERTICA_NAVIGATOR_SSL_CERTFILE=/path/to/server.crt
#   export VERTICA_NAVIGATOR_SSL_KEYFILE=/path/to/server.key
#
# Notes:
# - If HTTPS is enabled and the certificate/key files do not exist, the program
#   can auto-generate a self-signed certificate for local/internal use.
# - Self-signed certificates encrypt traffic but may trigger a browser warning.
# - Developers or operators can later replace the generated certificate and key
#   with organization-approved TLS files if needed.
# =============================================================================

DEBUG_LOGGING = True

import vertica_python
import http.server
import socketserver
from socketserver import ThreadingMixIn
from urllib.parse import urlparse, parse_qs
import json
import os
import logging
from typing import Dict, Optional, List, Tuple, Any
import time
import uuid
import html
from http import cookies
import ssl
import socket
import threading
import ipaddress
import datetime
import re
import copy
import tempfile
import subprocess
import shutil
from pathlib import Path

try:
    from cryptography import x509
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import rsa
    from cryptography.x509.oid import NameOID
    CRYPTOGRAPHY_AVAILABLE = True
except Exception:
    x509 = None
    hashes = None
    serialization = None
    rsa = None
    NameOID = None
    CRYPTOGRAPHY_AVAILABLE = False

# SEC-001: session credentials (username + password) are encrypted the
# moment they leave the login handler and stay encrypted in SESSIONS until the
# exact point a Vertica connection is being opened. Fernet is AES-128-CBC +
# HMAC-SHA-256 with versioning and padding; the API is tiny and hard to misuse.
# The key is generated once per process via os.urandom under the hood and held
# in a module-level variable; it never touches disk. When the process dies,
# every encrypted credential dies with it. This is by design: a restart must
# invalidate all sessions because there is no way to recover them.
try:
    from cryptography.fernet import Fernet as _Fernet, InvalidToken as _FernetInvalidToken
    _SESSION_FERNET = _Fernet(_Fernet.generate_key())
    SESSION_CRYPTO_AVAILABLE = True
except Exception:
    _Fernet = None
    _FernetInvalidToken = Exception
    _SESSION_FERNET = None
    SESSION_CRYPTO_AVAILABLE = False


# -----------------------------------------------------------------------------
# Logging
# -----------------------------------------------------------------------------
if DEBUG_LOGGING:
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - [%(name)s] - %(message)s',
        handlers=[
            logging.FileHandler('vertica_navigator.log'),
            logging.StreamHandler()
        ]
    )
else:
    logging.basicConfig(
        level=logging.ERROR,
        format='%(asctime)s - %(levelname)s - [%(name)s] - %(message)s',
        handlers=[logging.StreamHandler()]
    )

logger = logging.getLogger('VerticaNavigator')


def log_info(message: str):
    if DEBUG_LOGGING:
        logger.info(message)


# -----------------------------------------------------------------------------
# Credentials / session config
# -----------------------------------------------------------------------------
def read_credentials():
    log_info('Reading credentials file...')
    base_dir = os.path.dirname(__file__)
    candidate_paths = [
        os.path.join(base_dir, 'ASSETS', 'vertica_credentials.json'),
        os.path.join(base_dir, 'vertica_credentials.json'),
        os.path.join('/mnt/data', 'vertica_credentials.json'),
    ]
    for credentials_path in candidate_paths:
        if os.path.exists(credentials_path):
            with open(credentials_path, 'r', encoding='utf-8') as f:
                creds = json.load(f)
                log_info(f'Credentials loaded successfully from {credentials_path}')
                return creds
    raise FileNotFoundError('vertica_credentials.json was not found in ASSETS or next to the script')


BASE_DB_CONFIG = read_credentials()
SESSION_COOKIE_NAME = 'vertica_navigator_session'
SESSION_MAX_AGE_SECONDS = 12 * 60 * 60

# In-memory session store. Suitable for one Python process serving multiple users.
SESSIONS: Dict[str, Dict] = {}

PROFILE_RUNS: Dict[str, Dict] = {}
PROFILE_MAX_AGE_SECONDS = 12 * 60 * 60
SESSIONS_LOCK = threading.RLock()
PROFILE_RUNS_LOCK = threading.RLock()
QPROF_TEMP_ROOT = os.environ.get('VERTICA_NAVIGATOR_QPROF_TEMP_ROOT', os.path.join(tempfile.gettempdir(), 'vertica_navigator_qprof'))


def resolve_qprof_script_path() -> str:
    base_dir = os.path.dirname(__file__)
    candidates = [
        os.environ.get('VERTICA_NAVIGATOR_QPROF_SCRIPT', '').strip(),
        os.path.join(base_dir, 'qprof.sh'),
        os.path.join(base_dir, 'qprof(2).sh'),
        os.path.join('/mnt/data', 'qprof.sh'),
        os.path.join('/mnt/data', 'qprof(2).sh'),
    ]
    for candidate in candidates:
        if candidate and os.path.isfile(candidate):
            return candidate
    raise FileNotFoundError('qprof.sh was not found. Set VERTICA_NAVIGATOR_QPROF_SCRIPT or place qprof.sh next to the script.')


def ensure_qprof_temp_root() -> str:
    os.makedirs(QPROF_TEMP_ROOT, exist_ok=True)
    return QPROF_TEMP_ROOT


def _cleanup_temp_paths(paths: List[str]):
    for path in paths or []:
        try:
            if path and os.path.exists(path):
                os.remove(path)
        except Exception as exc:
            logger.warning(f'Failed cleaning temp file {path}: {exc}')


def _register_session_temp_file(session_id: str, path: str):
    if not session_id or not path:
        return
    with SESSIONS_LOCK:
        session = SESSIONS.get(session_id)
        if not session:
            return
        session.setdefault('temp_files', []).append(path)


# -----------------------------------------------------------------------------
# Web server / HTTPS config
# -----------------------------------------------------------------------------
SERVER_HOST = os.environ.get('VERTICA_NAVIGATOR_HOST', '0.0.0.0')
HTTP_PORT = int(os.environ.get('VERTICA_NAVIGATOR_HTTP_PORT', '8001'))
HTTPS_ENABLED = os.environ.get('VERTICA_NAVIGATOR_HTTPS_ENABLED', '1').lower() in ('1', 'true', 'yes', 'on')
HTTPS_PORT = int(os.environ.get('VERTICA_NAVIGATOR_HTTPS_PORT', '8443'))
HTTP_REDIRECT_TO_HTTPS = os.environ.get('VERTICA_NAVIGATOR_HTTP_REDIRECT_TO_HTTPS', '1').lower() in ('1', 'true', 'yes', 'on')
CERTS_DIR = os.environ.get('VERTICA_NAVIGATOR_TLS_DIR', os.path.join(os.path.dirname(__file__), 'ASSETS', 'generated_tls'))
HTTPS_CERTFILE = os.environ.get('VERTICA_NAVIGATOR_SSL_CERTFILE', os.path.join(CERTS_DIR, 'server.crt'))
HTTPS_KEYFILE = os.environ.get('VERTICA_NAVIGATOR_SSL_KEYFILE', os.path.join(CERTS_DIR, 'server.key'))
TLS_CERT_VALID_DAYS = int(os.environ.get('VERTICA_NAVIGATOR_TLS_VALID_DAYS', '365'))
TLS_COOKIE_SECURE = False
TLS_AUTO_GENERATED = False
TLS_ACTIVE = False


def get_preferred_host_for_display() -> str:
    env_host = os.environ.get('VERTICA_NAVIGATOR_PUBLIC_HOST', '').strip()
    if env_host:
        return env_host
    if SERVER_HOST not in ('0.0.0.0', '::'):
        return SERVER_HOST
    try:
        hostname = socket.gethostname()
        fqdn = socket.getfqdn()
        if fqdn and fqdn not in ('localhost', 'localhost.localdomain'):
            return fqdn
        if hostname and hostname != 'localhost':
            return hostname
    except Exception:
        pass
    return 'localhost'


def cert_files_exist() -> bool:
    return os.path.exists(HTTPS_CERTFILE) and os.path.exists(HTTPS_KEYFILE)


def build_subject_alt_names(hostname: str):
    names = [x509.DNSName('localhost')]
    seen = {'localhost'}

    def add_dns(name: str):
        if name and name not in seen:
            names.append(x509.DNSName(name))
            seen.add(name)

    def add_ip(value: str):
        try:
            names.append(x509.IPAddress(ipaddress.ip_address(value)))
        except Exception:
            pass

    add_dns(hostname)
    add_dns(socket.gethostname())
    add_dns(socket.getfqdn())
    add_ip('127.0.0.1')
    add_ip('::1')

    if SERVER_HOST not in ('0.0.0.0', '::'):
        add_dns(SERVER_HOST)
        add_ip(SERVER_HOST)

    public_host = os.environ.get('VERTICA_NAVIGATOR_PUBLIC_HOST', '').strip()
    if public_host:
        add_dns(public_host)
        add_ip(public_host)

    return x509.SubjectAlternativeName(names)


def ensure_self_signed_certificate(display_host: str):
    global TLS_AUTO_GENERATED

    if cert_files_exist():
        return True

    if not CRYPTOGRAPHY_AVAILABLE:
        logger.warning('cryptography is not installed; cannot auto-generate TLS certificate files')
        return False

    os.makedirs(os.path.dirname(HTTPS_CERTFILE), exist_ok=True)
    os.makedirs(os.path.dirname(HTTPS_KEYFILE), exist_ok=True)

    private_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    subject = issuer = x509.Name([
        x509.NameAttribute(NameOID.COUNTRY_NAME, 'US'),
        x509.NameAttribute(NameOID.ORGANIZATION_NAME, 'Vertica Navigator'),
        x509.NameAttribute(NameOID.COMMON_NAME, display_host),
    ])
    now = time.time()
    cert = (
        x509.CertificateBuilder()
        .subject_name(subject)
        .issuer_name(issuer)
        .public_key(private_key.public_key())
        .serial_number(x509.random_serial_number())
        .not_valid_before(datetime.datetime.utcfromtimestamp(now - 300))
        .not_valid_after(datetime.datetime.utcfromtimestamp(now + (TLS_CERT_VALID_DAYS * 24 * 60 * 60)))
        .add_extension(build_subject_alt_names(display_host), critical=False)
        .add_extension(x509.BasicConstraints(ca=True, path_length=None), critical=True)
        .sign(private_key, hashes.SHA256())
    )

    with open(HTTPS_KEYFILE, 'wb') as f:
        f.write(private_key.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.TraditionalOpenSSL,
            encryption_algorithm=serialization.NoEncryption(),
        ))

    with open(HTTPS_CERTFILE, 'wb') as f:
        f.write(cert.public_bytes(serialization.Encoding.PEM))

    TLS_AUTO_GENERATED = True
    log_info(f'Auto-generated self-signed TLS certificate at {HTTPS_CERTFILE}')
    return True


def print_startup_banner(mode: str, app_url: str, redirect_url: Optional[str] = None, startup_note: Optional[str] = None):
    print('')
    print('=' * 78)
    print('Vertica Navigator server startup')
    print('=' * 78)
    print(f'Mode: {mode}')
    print(f'Application URL: {app_url}')
    if redirect_url:
        print(f'HTTP redirect listener: {redirect_url}  ->  {app_url}')
    if startup_note:
        print(startup_note)

    if mode == 'HTTPS':
        print('')
        print('TLS status: HTTPS is enabled for browser-to-server traffic.')
        print(f'Certificate file: {HTTPS_CERTFILE}')
        print(f'Private key file: {HTTPS_KEYFILE}')
        if TLS_AUTO_GENERATED:
            print('Certificate source: auto-generated self-signed certificate created by this program.')
        else:
            print('Certificate source: existing certificate and key files provided by the operator.')
        print('Browser behavior:')
        print('- If this certificate is trusted by the browser/OS, users just open the URL.')
        print('- If it is self-signed or not trusted, the browser will show a warning page.')
        print('- Users may proceed only if they personally trust this server and certificate.')
        print('- Deployers may later replace these files with company or public CA certificates.')
    else:
        print('')
        print('TLS status: running without HTTPS.')
        print('To enable HTTPS, install the Python package and restart:')
        print('  sudo python3 -m pip install cryptography')
        print('Optional environment variables:')
        print('  VERTICA_NAVIGATOR_HTTPS_ENABLED=1')
        print('  VERTICA_NAVIGATOR_SSL_CERTFILE=/path/to/server.crt')
        print('  VERTICA_NAVIGATOR_SSL_KEYFILE=/path/to/server.key')
        print('  VERTICA_NAVIGATOR_HTTPS_PORT=8443')
        print('  VERTICA_NAVIGATOR_HTTP_REDIRECT_TO_HTTPS=1')
        print('')
        print('With cryptography installed, the program can auto-generate a self-signed cert/key pair.')
    print('=' * 78)
    print('')

# -----------------------------------------------------------------------------
# SQL formatting helpers (kept from original behavior)
# -----------------------------------------------------------------------------
def split_sql_statements(sql_text):
    statements = []
    current = []
    in_single = False
    in_double = False
    in_line_comment = False
    in_block_comment = False
    i = 0
    length = len(sql_text)

    while i < length:
        ch = sql_text[i]
        nxt = sql_text[i + 1] if i + 1 < length else ''

        if in_line_comment:
            current.append(ch)
            if ch in ('\n', '\r'):
                in_line_comment = False
            i += 1
            continue

        if in_block_comment:
            current.append(ch)
            if ch == '*' and nxt == '/':
                current.append(nxt)
                in_block_comment = False
                i += 2
            else:
                i += 1
            continue

        if in_single:
            current.append(ch)
            if ch == "'":
                if nxt == "'":
                    current.append(nxt)
                    i += 2
                    continue
                in_single = False
            i += 1
            continue

        if in_double:
            current.append(ch)
            if ch == '"':
                if nxt == '"':
                    current.append(nxt)
                    i += 2
                    continue
                in_double = False
            i += 1
            continue

        if ch == '-' and nxt == '-':
            current.append(ch)
            current.append(nxt)
            in_line_comment = True
            i += 2
            continue

        if ch == '/' and nxt == '*':
            current.append(ch)
            current.append(nxt)
            in_block_comment = True
            i += 2
            continue

        if ch == "'":
            current.append(ch)
            in_single = True
            i += 1
            continue

        if ch == '"':
            current.append(ch)
            in_double = True
            i += 1
            continue

        if ch == ';':
            statement = ''.join(current).strip()
            if statement:
                statements.append(statement)
            current = []
            i += 1
            continue

        current.append(ch)
        i += 1

    tail = ''.join(current).strip()
    if tail:
        statements.append(tail)
    return statements


def beautify_single_statement(sql):
    """Beautify rewrite.

    The previous beautifier was 'basically adding a new
    line before some keywords' and did not deserve the name. Now tokenizer
    is unchanged (it was correct); emission is rewritten to handle the
    things a real SQL formatter must handle:

      * SELECT-list: each column on its own indented line under SELECT,
        aligned, trailing commas. Short single-column SELECT fits on one
        line.
      * JOIN ... ON: JOIN on its own line; ON on the next line indented
        one level; AND/OR conjunctions aligned with ON for readable
        multi-predicate joins.
      * WHERE/HAVING: first predicate on same line; AND/OR conjunctions
        on new lines aligned under the clause.
      * GROUP BY / ORDER BY: comma-separated list inline if short,
        wrapped when long (> 80 chars).
      * CASE / WHEN / THEN / ELSE / END: proper indentation, each WHEN
        on its own line, END back-aligned with CASE.
      * Subqueries: opening paren pushes indent; SELECT inside goes on a
        new indented line; closing paren dedents.
      * Function calls: stay inline regardless of nesting (never break).
      * Keyword casing: comprehensive uppercase set applied to every
        recognized keyword.
      * Comments (-- and /* */): preserved on their own line at current
        indent.
      * String literals and quoted identifiers: preserved verbatim.

    Produces one deterministic output per input (reformatting a formatted
    statement is idempotent). No external dependencies.
    """
    sql = sql.strip()
    if not sql:
        return ''

    # Comprehensive keyword set. Anything here is uppercased regardless
    # of how the user typed it. Extend rather than swap when adding new ones.
    uppercase_keywords = {
        'SELECT', 'FROM', 'WHERE', 'GROUP', 'BY', 'HAVING', 'ORDER', 'INNER', 'LEFT',
        'RIGHT', 'FULL', 'CROSS', 'OUTER', 'JOIN', 'NATURAL', 'LATERAL', 'UNION',
        'INTERSECT', 'EXCEPT', 'ALL', 'WITH', 'RECURSIVE', 'AS', 'ON', 'USING',
        'UPDATE', 'DELETE', 'INSERT', 'INTO', 'VALUES', 'SET', 'LIMIT', 'OFFSET',
        'FETCH', 'FIRST', 'NEXT', 'ROW', 'ROWS', 'ONLY', 'TIES',
        'AND', 'OR', 'NOT', 'DISTINCT', 'CASE', 'WHEN', 'THEN', 'ELSE', 'END',
        'IN', 'IS', 'NULL', 'LIKE', 'ILIKE', 'BETWEEN', 'EXISTS', 'SOME', 'ANY',
        'CAST', 'EXTRACT', 'INTERVAL', 'AT', 'TIME', 'ZONE',
        'PROFILE', 'EXPLAIN', 'LOCAL', 'VERBOSE',
        'PARTITION', 'OVER', 'WINDOW', 'PRECEDING', 'FOLLOWING', 'UNBOUNDED', 'CURRENT',
        'DESC', 'ASC', 'NULLS', 'LAST',
        'TRUE', 'FALSE', 'UNKNOWN',
        'CREATE', 'TABLE', 'VIEW', 'PROJECTION', 'SCHEMA', 'DATABASE', 'FUNCTION',
        'IF', 'REPLACE',
        'PRIMARY', 'FOREIGN', 'KEY', 'REFERENCES', 'UNIQUE', 'CONSTRAINT',
        'SEGMENTED', 'UNSEGMENTED', 'HASH', 'NODE',
        'ANALYZE_STATISTICS', 'ANALYZE_HISTOGRAM',
    }
    # These tokens, when they occur as standalone words, start a new line
    # at the outer (clause) indent. They can be multi-word ("GROUP BY").
    # Note: ON is a clause too (for JOINs) but handled specially.
    multi_word_clauses = [
        'GROUP BY', 'ORDER BY', 'PARTITION BY', 'INSERT INTO', 'UNION ALL',
        'LEFT OUTER JOIN', 'RIGHT OUTER JOIN', 'FULL OUTER JOIN',
        'INNER JOIN', 'LEFT JOIN', 'RIGHT JOIN', 'FULL JOIN', 'CROSS JOIN', 'NATURAL JOIN',
    ]
    single_word_clauses = {
        'SELECT', 'FROM', 'WHERE', 'HAVING', 'UNION', 'INTERSECT', 'EXCEPT',
        'WITH', 'UPDATE', 'DELETE', 'VALUES', 'SET', 'LIMIT', 'OFFSET',
        'RETURNING', 'JOIN', 'ON', 'USING',
    }
    # Inside a SELECT list, commas force a new line; inside a function-call
    # argument list, commas do NOT force a new line.
    # Inside GROUP BY / ORDER BY, we inline unless the line would get too long.

    indent_unit = '    '
    max_line_width = 100  # only used for GROUP BY / ORDER BY wrapping

    # ---- Tokenize ----
    tokens = []
    i = 0
    length = len(sql)

    def is_word_char(ch):
        return ch.isalnum() or ch == '_' or ch == '$'

    while i < length:
        ch = sql[i]
        nxt = sql[i + 1] if i + 1 < length else ''

        if ch.isspace():
            i += 1
            continue

        if ch == '-' and nxt == '-':
            start = i
            i += 2
            while i < length and sql[i] not in ('\n', '\r'):
                i += 1
            tokens.append(('comment', sql[start:i]))
            continue

        if ch == '/' and nxt == '*':
            start = i
            i += 2
            while i < length - 1:
                if sql[i] == '*' and sql[i + 1] == '/':
                    i += 2
                    break
                i += 1
            tokens.append(('comment', sql[start:i]))
            continue

        if ch == "'":
            start = i
            i += 1
            while i < length:
                if sql[i] == "'":
                    i += 1
                    if i < length and sql[i] == "'":
                        i += 1
                        continue
                    break
                i += 1
            tokens.append(('string', sql[start:i]))
            continue

        if ch == '"':
            start = i
            i += 1
            while i < length:
                if sql[i] == '"':
                    i += 1
                    if i < length and sql[i] == '"':
                        i += 1
                        continue
                    break
                i += 1
            tokens.append(('identifier', sql[start:i]))
            continue

        if is_word_char(ch):
            start = i
            i += 1
            while i < length and is_word_char(sql[i]):
                i += 1
            value = sql[start:i]
            upper = value.upper()
            if upper in uppercase_keywords:
                value = upper
            tokens.append(('word', value))
            continue

        # Two-char operators
        if ch in ('<', '>', '!', '|', ':', '=') and nxt:
            two = ch + nxt
            if two in ('<=', '>=', '<>', '!=', '||', '::', '=='):
                tokens.append(('symbol', two))
                i += 2
                continue

        tokens.append(('symbol', ch))
        i += 1

    # ---- Merge multi-word clause tokens ----
    merged = []
    i = 0
    while i < len(tokens):
        matched = False
        # Try 3-word match first (LEFT OUTER JOIN etc.)
        for phrase_len in (3, 2):
            if i + phrase_len <= len(tokens):
                words = []
                ok = True
                for j in range(phrase_len):
                    t = tokens[i + j]
                    if t[0] != 'word':
                        ok = False
                        break
                    words.append(t[1])
                if ok:
                    joined = ' '.join(words)
                    if joined in multi_word_clauses:
                        merged.append(('clause', joined))
                        i += phrase_len
                        matched = True
                        break
        if matched:
            continue
        tok_type, tok_value = tokens[i]
        if tok_type == 'word' and tok_value in single_word_clauses:
            merged.append(('clause', tok_value))
        else:
            merged.append((tok_type, tok_value))
        i += 1

    # ---- Emit ----
    # State:
    #   indent  - current base indent (number of levels)
    #   lines   - output lines so far
    #   current - in-progress line being built
    # paren_stack entries:
    #   {'kind': 'subquery'|'func'|'expr', 'indent_before': int}
    # case_stack entries:
    #   {'indent_before': int}
    # The list-context stack tells comma how to behave:
    #   'select_list'  - comma ends line
    #   'set_list'     - comma ends line
    #   'group_list'   - comma inline (we'll do late-wrap if needed)
    #   'order_list'   - comma inline
    #   'func_args'    - comma inline
    #   'values_row'   - comma inline
    #   None           - no list context
    lines: List[str] = []
    current = ''
    indent = 0
    paren_stack: List[Dict[str, Any]] = []
    case_stack: List[Dict[str, Any]] = []
    list_ctx: Optional[str] = None   # top of the list-context stack
    list_stack: List[Optional[str]] = []

    def push_list(ctx):
        nonlocal list_ctx
        list_stack.append(list_ctx)
        list_ctx = ctx

    def pop_list():
        nonlocal list_ctx
        if list_stack:
            list_ctx = list_stack.pop()
        else:
            list_ctx = None

    def flush():
        nonlocal current
        line = current.rstrip()
        if line:
            lines.append(line)
        current = ''

    def start_line(extra_indent=0):
        nonlocal current
        flush()
        current = indent_unit * max(indent + extra_indent, 0)

    def is_blank_current():
        return not current.strip()

    def append_raw(s):
        nonlocal current
        current += s

    def append_word(value, spaced=True):
        """Append a word/value to current line with a space before unless
        the previous char is '(' or '.' or the line is blank-with-indent."""
        nonlocal current
        if is_blank_current():
            append_raw(value)
            return
        if not spaced:
            append_raw(value)
            return
        if current.endswith('(') or current.endswith('.') or current.endswith(' '):
            append_raw(value)
        else:
            append_raw(' ' + value)

    for idx, (tok_type, tok_value) in enumerate(merged):
        prev = merged[idx - 1] if idx > 0 else None
        nxt = merged[idx + 1] if idx + 1 < len(merged) else None

        # ---- Comments: own line at current indent ----
        if tok_type == 'comment':
            flush()
            lines.append(indent_unit * indent + tok_value)
            continue

        # ---- Clauses ----
        if tok_type == 'clause':
            cv = tok_value

            # ON/USING following a JOIN: indent one deeper than the clause
            # level so ON sits under JOIN, and AND/OR conjunctions later
            # align with ON visually.
            if cv in ('ON', 'USING'):
                start_line(extra_indent=1)
                append_raw(cv + ' ')
                push_list(None)   # ON predicates are not a list
                continue

            # JOIN variants: new line at clause level.
            if 'JOIN' in cv:
                start_line()
                append_raw(cv + ' ')
                pop_list()  # end previous list ctx (e.g. select_list)
                push_list(None)
                continue

            # Start of the statement: no flush needed (current is empty).
            start_line()
            append_raw(cv)

            # Set up list context based on the clause.
            pop_list()
            if cv == 'SELECT':
                push_list('select_list')
            elif cv == 'SET':
                push_list('set_list')
            elif cv == 'VALUES':
                push_list(None)
            elif cv == 'GROUP BY':
                push_list('group_list')
            elif cv == 'ORDER BY':
                push_list('order_list')
            elif cv == 'PARTITION BY':
                push_list('order_list')  # same wrapping rules
            elif cv == 'FROM':
                push_list('from_list')
            elif cv in ('WHERE', 'HAVING'):
                push_list(None)  # AND/OR handled separately
            else:
                push_list(None)

            # For SELECT / SET: open a new indented line ready for columns.
            if cv in ('SELECT', 'SET', 'GROUP BY', 'ORDER BY'):
                # Put a trailing space so the first column goes on the
                # same line as the clause keyword if it's short; we'll
                # wrap to newline after the first column if needed. The
                # simpler, more predictable rule: always put the FIRST
                # column on the same line, COMMA then newline for each
                # subsequent column.
                append_raw(' ')
            elif cv in ('FROM', 'WHERE', 'HAVING', 'VALUES'):
                append_raw(' ')
            else:
                append_raw(' ')
            continue

        # ---- Words (includes keywords that are not clauses) ----
        if tok_type == 'word':
            # AND / OR on their own line when inside WHERE/HAVING/ON at depth 0.
            if tok_value in ('AND', 'OR'):
                # Inside a function call's args, treat like a normal word
                # (e.g. CASE WHEN a AND b THEN ...).
                in_func = any(p['kind'] == 'func' for p in paren_stack)
                in_case = len(case_stack) > 0
                if not in_func and not in_case:
                    # Break the line; align with slight extra indent.
                    start_line(extra_indent=1)
                    append_raw(tok_value + ' ')
                    continue
                # Inside func/case: inline.
                append_word(tok_value)
                continue

            # CASE: remember the VISIBLE indent of the current line (which
            # may be deeper than `indent` because of select-list
            # continuation), so WHEN/ELSE/END nest relative to that. Bump
            # the parser's `indent` var to base+1 for in-CASE expressions.
            if tok_value == 'CASE':
                append_word('CASE')
                # Visible leading spaces of the line we just appended to.
                leading = len(current) - len(current.lstrip(' '))
                base_levels = leading // len(indent_unit)
                case_stack.append({
                    'indent_before': indent,
                    'base':          base_levels,
                })
                indent = base_levels + 1
                continue

            if tok_value == 'WHEN' and case_stack:
                start_line()
                append_raw('WHEN ')
                continue

            if tok_value == 'THEN' and case_stack:
                append_word('THEN')
                continue

            if tok_value == 'ELSE' and case_stack:
                start_line()
                append_raw('ELSE ')
                continue

            if tok_value == 'END' and case_stack:
                frame = case_stack.pop()
                # Emit END on a new line at the CASE's *visible* base indent,
                # then restore `indent` to what it was BEFORE CASE so
                # downstream tokens (like "AS alias" or a comma ending the
                # select-list entry) behave normally.
                indent = frame['base']
                start_line()
                append_raw('END')
                indent = frame['indent_before']
                continue

            append_word(tok_value)
            continue

        # ---- Strings / identifiers ----
        if tok_type in ('string', 'identifier'):
            append_word(tok_value)
            continue

        # ---- Symbols ----
        if tok_type == 'symbol':
            if tok_value == '.':
                append_raw('.')
                continue

            if tok_value == ',':
                # List-context-aware comma handling.
                append_raw(',')
                # Break line for select/set list members.
                if list_ctx in ('select_list', 'set_list', 'from_list'):
                    start_line(extra_indent=1)
                elif list_ctx in ('group_list', 'order_list'):
                    # Inline comma; we rely on later post-process to wrap
                    # if the line exceeds max_line_width.
                    append_raw(' ')
                else:
                    # Func args, values row, etc.: inline comma.
                    append_raw(' ')
                continue

            if tok_value == '(':
                # Is this a subquery, a function call, or a grouping paren?
                # Heuristic:
                #   - If the NEXT meaningful token is SELECT or WITH -> subquery
                #   - If the PREV token is a word that isn't a known keyword
                #     and not an operator -> function call
                #   - Otherwise -> expression grouping
                is_subquery = (nxt is not None and nxt[0] == 'clause'
                               and nxt[1] in ('SELECT', 'WITH'))
                is_func = False
                if not is_subquery and prev is not None:
                    if prev[0] in ('word', 'identifier'):
                        # prev is a function name if it's an identifier or
                        # a word that is not a clause-triggering keyword.
                        pv = prev[1]
                        if prev[0] == 'identifier':
                            is_func = True
                        else:
                            # Exclude control keywords that can precede ( but
                            # not as function names (IN, EXISTS, CASE, etc.).
                            not_func = {'IN', 'EXISTS', 'ANY', 'SOME', 'ALL',
                                        'CASE', 'WHEN', 'THEN', 'ELSE', 'AND',
                                        'OR', 'NOT', 'BETWEEN', 'LIKE', 'ILIKE',
                                        'ON', 'USING', 'VALUES', 'DISTINCT'}
                            if pv not in not_func:
                                is_func = True
                    elif prev[0] == 'symbol' and prev[1] in (')',):
                        # Back-to-back () - still function-ish (call result).
                        pass

                if is_subquery:
                    # Open paren, newline, indent.
                    if current and not current.endswith(' ') and not current.endswith('('):
                        append_raw(' ')
                    append_raw('(')
                    paren_stack.append({'kind': 'subquery', 'indent_before': indent,
                                        'list_before': list_ctx})
                    indent += 1
                    start_line()
                    push_list(None)
                elif is_func:
                    # Function call: no newline. Push arg list context.
                    append_raw('(')
                    paren_stack.append({'kind': 'func', 'indent_before': indent,
                                        'list_before': list_ctx})
                    push_list('func_args')
                else:
                    # Plain grouping paren.
                    if current and not current.endswith(' ') and not current.endswith('(') \
                            and not current.endswith('.'):
                        append_raw(' ')
                    append_raw('(')
                    paren_stack.append({'kind': 'expr', 'indent_before': indent,
                                        'list_before': list_ctx})
                    push_list(None)
                continue

            if tok_value == ')':
                if not paren_stack:
                    append_raw(')')
                    continue
                frame = paren_stack.pop()
                if frame['kind'] == 'subquery':
                    indent = frame['indent_before']
                    start_line()
                    append_raw(')')
                else:
                    # func or expr: inline.
                    current = current.rstrip()
                    append_raw(')')
                pop_list()
                # Restore prior list context (pop_list uses list_stack).
                # Note: push_list at '(' saved the list_before implicitly by
                # pushing the list stack; pop_list handles that.
                continue

            # Operators like =, <, >, +, -, *, /, ::, etc.
            # Binary operators: spaced. Unary or punctuation: tight.
            if tok_value in ('=', '<', '>', '<=', '>=', '<>', '!=', '||', '::',
                             '+', '-', '*', '/', '%'):
                # Tight for '::' (cast) and '.' (already handled). Others spaced.
                if tok_value == '::':
                    current = current.rstrip()
                    append_raw('::')
                else:
                    append_word(tok_value)
                continue

            # Punctuation that should hug the previous token with no space.
            # Semicolon is the main one; keeping a separate branch makes
            # it easy to add others (e.g. array [] later).
            if tok_value in (';',):
                current = current.rstrip()
                append_raw(tok_value)
                continue

            # Default
            append_word(tok_value)
            continue

    flush()

    # --- Post-process: wrap long GROUP BY / ORDER BY lines ---
    # If a line starts with "GROUP BY" or "ORDER BY" and is over max_line_width,
    # break it onto multiple lines with each item on its own.
    wrapped: List[str] = []
    for line in lines:
        stripped = line.lstrip()
        if (len(line) > max_line_width and
                (stripped.startswith('GROUP BY ') or stripped.startswith('ORDER BY ')
                 or stripped.startswith('PARTITION BY '))):
            # Split off the clause head, keep the items comma-separated.
            prefix_len = len(line) - len(stripped)
            if stripped.startswith('GROUP BY '):
                head, tail = 'GROUP BY', stripped[len('GROUP BY '):]
            elif stripped.startswith('ORDER BY '):
                head, tail = 'ORDER BY', stripped[len('ORDER BY '):]
            else:
                head, tail = 'PARTITION BY', stripped[len('PARTITION BY '):]
            items = [item.strip() for item in tail.split(',') if item.strip()]
            wrapped.append(' ' * prefix_len + head)
            inner_indent = ' ' * (prefix_len + len(indent_unit))
            for ii, item in enumerate(items):
                suffix = ',' if ii < len(items) - 1 else ''
                wrapped.append(inner_indent + item + suffix)
        else:
            wrapped.append(line)

    return '\n'.join(wrapped)



def beautify_sql_text(sql_text):
    statements = split_sql_statements(sql_text)
    formatted = []
    for statement in statements:
        beautified = beautify_single_statement(statement)
        if beautified:
            formatted.append(beautified)
    if not formatted:
        return ''
    return ';\n\n'.join(formatted) + ';'


# -----------------------------------------------------------------------------
# Session helpers
# -----------------------------------------------------------------------------
def build_connection_info(username: str, password: str) -> Dict:
    conn_info = dict(BASE_DB_CONFIG)
    conn_info['user'] = username
    conn_info['password'] = password
    return conn_info



def test_login(username: str, password: str):
    conn_info = build_connection_info(username, password)
    with vertica_python.connect(**conn_info) as connection:
        with connection.cursor() as cursor:
            cursor.execute('select version();')
            version = cursor.fetchone()[0]
    return version



# SEC-001: encrypt username + password immediately at login-handler exit
# so that plaintext credentials never sit in SESSIONS. The plaintext strings
# only exist for the duration of this function and then go out of scope.
#
# Reads at the 4 former plaintext sites (run_qprof_shell, run_profile_query,
# /api/execute_query, get_tree) go through decrypt_credentials() below.
# For logging (which only needs username, not password) the cheaper
# session_username() helper decrypts just the one field.
#
# Fernet returns bytes; we store bytes. A grep for any handler reading
# session['password'] as if it were a plaintext str is a bug - the only
# legitimate reader is decrypt_credentials().
def _encrypt_credential(value: str) -> bytes:
    if not SESSION_CRYPTO_AVAILABLE:
        raise RuntimeError(
            'cryptography.fernet is required for session credential encryption. '
            'Install the "cryptography" package (already a dependency for self-signed '
            'cert generation) or disable the server.'
        )
    if value is None:
        value = ''
    return _SESSION_FERNET.encrypt(value.encode('utf-8'))


def _decrypt_credential(token) -> str:
    if not SESSION_CRYPTO_AVAILABLE:
        raise RuntimeError('cryptography.fernet is required for session credential decryption.')
    if isinstance(token, str):
        # Defensive: older session entries or migration path. Shouldn't
        # happen post-v81 but we don't want a crash if it does.
        return token
    if token is None:
        return ''
    try:
        return _SESSION_FERNET.decrypt(token).decode('utf-8')
    except _FernetInvalidToken:
        # A session created under a previous process's key was left behind
        # in memory somehow (can't happen with in-memory SESSIONS, but guard
        # against future persistent-session work).
        raise RuntimeError('Session credentials cannot be decrypted; please log in again.')


def decrypt_credentials(session: Dict):
    """Decrypt the per-session encrypted username + password.

    Returns a tuple (username, password). Caller uses the plaintext
    IMMEDIATELY for vertica_python.connect(...) / pgpass file write and
    lets the values go out of scope. Never persist, never log, never pass
    across function boundaries beyond the immediate connection-open call.
    """
    return (
        _decrypt_credential(session.get('username')),
        _decrypt_credential(session.get('password')),
    )


def session_username(session: Dict) -> str:
    """Decrypt just the username (for logging and display purposes).

    Cheaper than decrypt_credentials() because we don't also materialize the
    password in memory. Used at the ~10 log sites that previously read
    session['username'] directly as a plaintext str.
    """
    return _decrypt_credential(session.get('username'))


def create_session(username: str, password: str) -> str:
    sid = uuid.uuid4().hex
    # v81 SEC-001: encrypt both credentials BEFORE storing. The plaintext
    # `username` and `password` parameters go out of scope when this function
    # returns; after that, the only in-memory copy is the ciphertext bytes.
    enc_user = _encrypt_credential(username)
    enc_pw = _encrypt_credential(password)
    with SESSIONS_LOCK:
        SESSIONS[sid] = {
            'username': enc_user,
            'password': enc_pw,
            'created_at': time.time(),
            'last_seen': time.time(),
            'temp_files': [],
        }
    return sid


def delete_session(session_id: Optional[str]):
    if not session_id:
        return
    temp_files = []
    with SESSIONS_LOCK:
        session = SESSIONS.pop(session_id, None)
        if session:
            temp_files = list(session.get('temp_files') or [])
    _cleanup_temp_paths(temp_files)


def get_session(session_id: Optional[str]):
    if not session_id:
        return None
    temp_files = []
    with SESSIONS_LOCK:
        session = SESSIONS.get(session_id)
        if not session:
            return None
        now = time.time()
        if now - session['last_seen'] > SESSION_MAX_AGE_SECONDS:
            expired = SESSIONS.pop(session_id, None)
            if expired:
                temp_files = list(expired.get('temp_files') or [])
        else:
            session['last_seen'] = now
            payload = copy.deepcopy(session)
            payload['session_id'] = session_id
            return payload
    _cleanup_temp_paths(temp_files)
    return None


def cleanup_sessions():
    now = time.time()
    expired_payloads = []
    with SESSIONS_LOCK:
        expired = [sid for sid, s in SESSIONS.items() if now - s['last_seen'] > SESSION_MAX_AGE_SECONDS]
        for sid in expired:
            payload = SESSIONS.pop(sid, None)
            if payload:
                expired_payloads.append(payload)
    for payload in expired_payloads:
        _cleanup_temp_paths(payload.get('temp_files') or [])


def store_profile_run(profile_id: str, payload: Dict):
    with PROFILE_RUNS_LOCK:
        PROFILE_RUNS[profile_id] = copy.deepcopy(payload)




def save_profile_run(payload: Dict) -> str:
    profile_id = uuid.uuid4().hex
    store_profile_run(profile_id, payload)
    return profile_id
def get_profile_run(profile_id: str) -> Optional[Dict]:
    with PROFILE_RUNS_LOCK:
        payload = PROFILE_RUNS.get(profile_id)
        return copy.deepcopy(payload) if payload else None


def cleanup_profile_runs():
    now = time.time()
    with PROFILE_RUNS_LOCK:
        expired = [pid for pid, p in PROFILE_RUNS.items() if now - p.get('created_at', now) > PROFILE_MAX_AGE_SECONDS]
        for pid in expired:
            PROFILE_RUNS.pop(pid, None)


def ensure_single_statement(sql_text: str) -> str:
    statements = split_sql_statements(sql_text or '')
    if len(statements) != 1:
        raise ValueError('Profile requires exactly one SQL statement in the editor or selected text.')
    statement = statements[0].strip()
    if not statement:
        raise ValueError('Profile requires one non-empty SQL statement.')
    if statement.lower().startswith('profile '):
        raise ValueError('Do not include the PROFILE keyword. The profiler adds it automatically.')
    return statement


def infer_path_depth(path_line: str) -> int:
    prefix = ''
    for ch in path_line or '':
        if ch.isalpha():
            break
        prefix += ch
    return max(prefix.count('|') + prefix.count('+') + prefix.count('>') // 2, 0)


def _clean_plan_display_text(plan_text: str) -> str:
    text = re.sub(r'^[-+|> ]+', '', str(plan_text or '')).strip()
    text = re.sub(r'\s+', ' ', text)
    text = re.sub(r'(\(PATH ID:\s*\d+\))(?:\s*\[PATH ID:\s*\d+\])+$', r'\1', text, flags=re.I)
    text = re.sub(r'\[PATH ID:\s*(\d+)\]\s*$', r'(PATH ID: \1)', text, flags=re.I)
    return text.strip()


def _strip_path_suffix(text: str) -> str:
    value = _clean_plan_display_text(text)
    value = re.sub(r'\s*\(PATH ID:\s*\d+\)\s*$', '', value, flags=re.I)
    value = re.sub(r'\s*\[PATH ID:\s*\d+\]\s*$', '', value, flags=re.I)
    return value.strip()


def _is_detail_plan_line(text: str) -> bool:
    value = _strip_path_suffix(text).lower()
    # fix (PATH 2 title bug): 'join cond' was missing, so the "Join Cond:
    # (f.online_page_key = d.online_page_key)" line on the user's path 2 was
    # scored as an operator line and beat the real "Outer -> JOIN HASH" line by
    # 3 points. Also added 'materialize' (covers both 'Materialize at' and
    # 'Materialize:' - the latter appears on nearly every STORAGE ACCESS path)
    # and 'aggregates' which appears under GROUPBY NOTHING paths.
    detail_prefixes = (
        'sort key', 'execute on', 'predicate', 'runtime filter',
        'materialize', 'projection:',
        'output only', 'filter:', 'join filter', 'join cond',
        'group by:', 'order by:', 'target list', 'cost:',
        'aggregates',
    )
    return value.startswith(detail_prefixes)


def _summarize_plan_title(plan_text: str) -> str:
    value = _strip_path_suffix(plan_text)
    compact = re.sub(r'\s+', ' ', value).strip()
    # strip "Outer -> " / "Inner -> " so the startswith() operator checks
    # below match "Outer -> JOIN HASH" and "Inner -> SELECT" too - previously
    # those lines fell through to the bare `compact` return path and the card
    # showed the whole plan-line text instead of a clean "JOIN HASH" / "SELECT".
    # The STORAGE ACCESS branch already used `in` (not startswith) so it was
    # unaffected and kept reducing "Outer -> STORAGE ACCESS for f ..." correctly.
    bare = re.sub(r'^(Outer|Inner)\s*->\s*', '', compact, flags=re.I)
    upper = bare.upper()
    if upper.startswith('SORT [TOP-K]'):
        return 'SORT [TOP-K]'
    if upper.startswith('SORT'):
        return 'SORT'
    if upper.startswith('GROUPBY HASH'):
        return 'GROUPBY HASH'
    # simplify the rest of the GROUPBY family ("GROUPBY NOTHING",
    # "GROUPBY PIPELINED", "GROUPBY MERGE", etc.) to two-word titles
    # instead of leaking the full "[Cost: ... Rows: ...]" tail.
    if upper.startswith('GROUPBY'):
        m = re.match(r'^(GROUPBY\s+[A-Z]+)', upper)
        return m.group(1) if m else 'GROUPBY'
    if upper.startswith('JOIN HASH'):
        return 'JOIN HASH'
    # (N5 from Step 99 QA): Vertica plan text for merge-joins can read
    # as "JOIN MERGEJOIN(inputs presorted)" - starts with "JOIN", not
    # "MERGE" or "MERGEJOIN", so the next two tests missed it and PATH 22
    # fell through with the whole raw title as short_title. Catch the
    # "JOIN MERGEJOIN" prefix explicitly and collapse to "MERGE JOIN".
    if upper.startswith('JOIN MERGEJOIN') or upper.startswith('JOIN MERGE JOIN'):
        return 'MERGE JOIN'
    if upper.startswith('MERGEJOIN') or upper.startswith('MERGE JOIN'):
        return 'MERGE JOIN'
    if upper.startswith('SELECT LIMIT'):
        m = re.match(r'^(SELECT\s+LIMIT\s+\d+)', bare, flags=re.I)
        return m.group(1).upper() if m else 'SELECT LIMIT'
    if upper.startswith('SELECT'):
        return 'SELECT'
    if upper.startswith('INSERT'):
        return 'INSERT'
    if upper.startswith('DELETE'):
        return 'DELETE'
    if upper.startswith('UPDATE'):
        return 'UPDATE'
    if 'STORAGE ACCESS' in upper:
        table_name = ''
        m = re.search(r'(?:for|on)\s+([A-Za-z0-9_\."]+)', compact, flags=re.I)
        if m:
            table_name = m.group(1).strip('"')
        return f'{table_name} STORAGE ACCESS'.strip() if table_name else 'STORAGE ACCESS'
    if upper.startswith('ANALYTICAL'):
        return 'ANALYTICAL'
    if upper.startswith('UNION'):
        return 'UNION'
    return compact


def _plan_line_priority(text: str) -> int:
    value = _strip_path_suffix(text)
    lower = value.lower()
    if not value:
        return -100
    if _is_detail_plan_line(value):
        return -10
    score = 0
    if lower.startswith('select limit'):
        score += 110
    elif lower.startswith('select'):
        score += 100
    if lower.startswith('join hash'):
        score += 98
    if lower.startswith('groupby hash'):
        score += 96
    if lower.startswith('mergejoin') or lower.startswith('merge join'):
        score += 94
    if lower.startswith('sort [top-k]'):
        score += 92
    elif lower.startswith('sort'):
        score += 90
    if 'storage access' in lower:
        score += 88
    if lower.startswith('analytical'):
        score += 86
    if lower.startswith('union'):
        score += 84
    if '[cost:' in lower:
        score += 8
    if 'rows:' in lower:
        score += 4
    score += max(0, 40 - len(value) // 4)
    return score


def _choose_primary_plan_line(path_lines: List[str]) -> Tuple[str, List[str]]:
    cleaned = [_clean_plan_display_text(line) for line in (path_lines or []) if str(line or '').strip()]
    if not cleaned:
        return '', []
    primary = max(cleaned, key=_plan_line_priority)
    details = []
    for line in cleaned:
        if line == primary:
            continue
        base = _strip_path_suffix(line)
        if not base:
            continue
        if base not in details:
            details.append(base)
    return primary, details


# (F-CARD-EXECON-PLAN-01): find the plan's "Execute on:" decision
# for a path. dc_explain_plans.plan_line contains lines like:
#     "|  Execute on: All Nodes"
#     "| | |      Execute on: v_eevdb_node0001, v_eevdb_node0003"
# This is the plan's decision about where to run the path - always
# cluster-wide and always complete (unlike execution_engine_profiles
# which is per-node). Returns the exact "Execute on: ..." payload or
# None if the plan didn't say. Authoritative source for the card's
# EXECUTE ON label starting in v69; EEP stays the source for the
# "observed counters" coverage indicator next to it.
def _extract_plan_execute_on(path_lines: List[str]) -> Optional[str]:
    for raw in (path_lines or []):
        text = str(raw or '')
        # Strip the leading "| | " tree-indent chars and any leading spaces.
        stripped = re.sub(r'^[\s|+\-]+', '', text).strip()
        low = stripped.lower()
        if low.startswith('execute on:'):
            return stripped[len('Execute on:'):].strip() or None
    return None



def score_profile_node(title: str, events, metrics: Optional[Dict[str, Any]] = None, total_duration_us: int = 0):
    #   The old status output here tried to cover everything at once -
    #   title keywords + duration share + memory + events - and would
    #   often end up with "everything orange or red" on a tree with
    #   many cards. Maya: "The main reason for red is to take the
    #   user's attention to that card with high probability there is
    #   something the user can do... Prevent situations where everything
    #   is orange or red."
    #
    #   Resolution: this function still returns (status, badges), but
    #   the STATUS is now ADVISORY ONLY for downstream consumers that
    #   want a per-card heuristic score in isolation (QA/logging). The
    #   card's DISPLAYED color is assigned cross-card by
    #   apply_card_status_rules() below, which overrides node['status']
    #   based on three narrow, actionable criteria (bad query events,
    #   massive time skew, near-slowest time). Badges produced here are
    #   still shown on the card as informational chips (Broadcast,
    #   Hash Join, Memory Pressure, etc) - they explain WHAT the card
    #   is doing, while the new cross-card status says WHETHER the user
    #   should focus on it.
    haystack = ' '.join([title or ''] + [
        ' '.join([
            str(item.get('event_type') or ''),
            str(item.get('event_description') or ''),
            str(item.get('suggested_action') or ''),
        ])
        for item in (events or [])
    ]).lower()
    metrics = metrics or {}

    runtime_us = 0.0
    running_us_field = metrics.get('running_time_us')
    if running_us_field is not None:
        try:
            runtime_us = float(running_us_field)
        except (TypeError, ValueError):
            runtime_us = 0.0
    if runtime_us <= 0:
        running_text = str(metrics.get('running_time') or '')
        ms_match = re.search(r'([0-9]+(?:\.[0-9]+)?)\s*ms', running_text, flags=re.I)
        sec_match = re.search(r'([0-9]+(?:\.[0-9]+)?)\s*s', running_text, flags=re.I)
        if ms_match:
            runtime_us = float(ms_match.group(1)) * 1000.0
        elif sec_match:
            runtime_us = float(sec_match.group(1)) * 1_000_000.0
    share = (runtime_us / float(total_duration_us)) if total_duration_us else 0.0
    memory_mb = float(metrics.get('memory_mb') or 0.0)

    badges = []
    score = 0
    if 'did not fit in memory' in haystack or 'spill' in haystack:
        badges.append(('bad', 'Memory Pressure')); score += 5
    if 'broadcast' in haystack:
        badges.append(('warn', 'Broadcast')); score += 2
    if 'resegment' in haystack or 'global resegment' in haystack:
        badges.append(('bad', 'Resegment')); score += 3
    if 'hash join' in haystack:
        badges.append(('warn', 'Hash Join')); score += 1
    if 'mergejoin' in haystack or 'merge join' in haystack:
        badges.append(('good', 'Merge Join')); score -= 1
    if 'co-located' in haystack or 'co located' in haystack or 'colocated' in haystack:
        badges.append(('good', 'Co-located')); score -= 2
    if memory_mb >= 256:
        badges.append(('bad', 'High Memory')); score += 2
    elif memory_mb >= 64:
        badges.append(('warn', 'Memory Heavy')); score += 1
    if share >= 0.30:
        badges.append(('bad', 'Hot Path')); score += 4
    elif share >= 0.15:
        badges.append(('warn', 'Heavy')); score += 2
    elif share > 0 and share <= 0.03:
        badges.append(('good', 'Light')); score -= 1

    if score >= 4:
        status = 'bad'
    elif score >= 2:
        status = 'warn'
    elif score <= -1 and badges:
        status = 'good'
    else:
        status = 'neutral'
    labels = []
    for kind, label in badges:
        if label not in labels:
            labels.append(label)
    return status, labels


def _rows_to_dicts(cursor, rows) -> List[Dict[str, Any]]:
    columns = [d.name if hasattr(d, 'name') else d[0] for d in (cursor.description or [])]
    return [{columns[i]: row[i] for i in range(len(columns))} for row in rows]



_CANONICAL_EVENT_CATALOG_PY = {
    'DELETE_WITH_NON_OPTIMIZED_PROJECTION': ('bad',  'DELETE NON-OPT PROJ'),
    'MEMORY_LIMIT_HIT':                     ('bad',  'OPT MEM LIMIT'),
    'NO_HISTOGRAM':                         ('bad',  'NO HISTOGRAM'),
    'GROUPBY_PUSHDOWN':                     ('good', 'GROUPBY PUSHDOWN'),
    'NODE_PRUNING':                         ('good', 'NODE PRUNING'),
    'TRANSITIVE_PREDICATE':                 ('good', 'TRANS. PREDICATE'),
    'NO_GROUPBY_PUSHDOWN':                  ('warn', 'NO GROUPBY PD'),
    'GROUP_BY_SPILLED':                     ('bad',  'GROUPBY SPILLED'),
    'JOIN_SPILLED':                         ('bad',  'JOIN SPILLED'),
    'RESEGMENTED_MANY_ROWS':                ('bad',  'RESEG MANY ROWS'),
    'WOS_SPILL':                            ('bad',  'WOS SPILL'),
    'GROUP_BY_PREPASS_FALLBACK':            ('good', 'PREPASS FALLBACK'),
    'MERGE_CONVERTED_TO_UNION':             ('good', 'MERGE->UNION'),
    'PARTITIONS_ELIMINATED':                ('good', 'PARTITIONS ELIM'),
}


def _derive_visible_badges_for_qa(events) -> List[str]:
    """Return the deduplicated list of badge labels the card actually
    displays, in first-seen event order. Matches the client-side
    deriveBadges() output so the QA appendix is consistent with the UI."""
    seen: List[str] = []
    for ev in events or []:
        evtype = str((ev or {}).get('event_type') or '')
        entry = _CANONICAL_EVENT_CATALOG_PY.get(evtype)
        if not entry:
            continue
        _kind, label = entry
        if label not in seen:
            seen.append(label)
    return seen



_RED_BAD_EVENT_TYPES = frozenset(
    evtype for evtype, (kind, _label) in _CANONICAL_EVENT_CATALOG_PY.items()
    if kind == 'bad'
)

# Exposed as constants so tuning is a single-line change if Maya later
# wants tighter or looser thresholds.
ORANGE_TIME_FRACTION = 0.90   # time >= 90% of max time -> orange
RED_SKEW_RATIO       = 5.0    # time / next-highest >= 5x -> red (80%+ gap)


def _node_running_time_us_for_status(node: Dict[str, Any]) -> float:
    """Extract a numeric microseconds value for this card, preferring
    the clean int in metrics.running_time_us (set at profile_rows build
    time) and falling back to card_metrics.exec_time_ms * 1000. Returns
    0.0 when neither source has a value. Matches the extraction logic
    used by the slowest-path calculation downstream so the status
    banner and the bottom summary card agree on what 'slowest' means."""
    metrics = node.get('metrics') or {}
    rt = metrics.get('running_time_us')
    if rt is not None:
        try:
            v = float(rt)
            if v > 0:
                return v
        except (TypeError, ValueError):
            pass
    cm = node.get('card_metrics') or {}
    ms_val = cm.get('exec_time_ms')
    if ms_val is not None:
        try:
            v = float(ms_val) * 1000.0
            if v > 0:
                return v
        except (TypeError, ValueError):
            pass
    return 0.0


def apply_card_status_rules(nodes: List[Dict[str, Any]]) -> None:
    """v76: cross-card status assignment. Mutates each node in-place,
    overriding node['status'] (set earlier by score_profile_node in
    isolation) and writing a new node['status_reason'] string.

    See the module-level comment above _RED_BAD_EVENT_TYPES for the
    full rule set.

    Safe to call with an empty list. O(N) per card for bad-event
    detection; O(N) once for top-two time extraction; total O(N) in
    the number of cards."""
    if not nodes:
        return

    # Collect per-card time once; order matches `nodes`.
    card_times: List[float] = [_node_running_time_us_for_status(n) for n in nodes]

    # Top-1 and top-2 card times across the whole tree. Used to compute
    # the skew ratio and the "% of slowest card" figure without an
    # inner loop per card.
    max_time: float = 0.0
    second_max_time: float = 0.0
    for t in card_times:
        if t >= max_time:
            second_max_time = max_time
            max_time = t
        elif t > second_max_time:
            second_max_time = t

    for idx, node in enumerate(nodes):
        this_time = card_times[idx]
        events = node.get('events') or []

        # Which bad events (by canonical event_type) fired on this card.
        # Deduplicated so "GROUP_BY_SPILLED" appearing on 16 nodes is
        # reported as one event, not sixteen.
        bad_event_types: List[str] = []
        seen: set = set()
        for ev in events:
            et = str((ev or {}).get('event_type') or '').upper()
            if et in _RED_BAD_EVENT_TYPES and et not in seen:
                seen.add(et)
                bad_event_types.append(et)

        # Compute max time among all OTHER cards (not this one). Because
        # we already know the top-two globally, max_other is second_max
        # if this card is the unique max, else it's max itself.
        if this_time >= max_time and this_time > 0:
            max_other_time = second_max_time
        else:
            max_other_time = max_time

        # Skew ratio: how many times bigger is this card than the next?
        if max_other_time > 0:
            skew_ratio = this_time / max_other_time
        else:
            skew_ratio = 0.0

        # Time fraction: this card's share of the slowest card.
        if max_time > 0 and this_time > 0:
            time_fraction = this_time / max_time
        else:
            time_fraction = 0.0

        # Apply rules in priority order.
        status = 'neutral'
        reason = ''

        if bad_event_types:
            status = 'bad'
            if len(bad_event_types) == 1:
                reason = (
                    f"Query event: {bad_event_types[0]}. "
                    f"See the Query Events section below for the suggested action."
                )
            elif len(bad_event_types) == 2:
                reason = (
                    f"Query events: {bad_event_types[0]}, {bad_event_types[1]}. "
                    f"See the Query Events section below for suggested actions."
                )
            else:
                reason = (
                    f"{len(bad_event_types)} query events flagged "
                    f"(including {bad_event_types[0]}). "
                    f"See the Query Events section below for suggested actions."
                )
        elif this_time > 0 and max_other_time > 0 and skew_ratio >= RED_SKEW_RATIO:
            status = 'bad'
            gap_pct = (1.0 - max_other_time / this_time) * 100.0
            reason = (
                f"This card's time ({_us_to_ms_text(int(this_time))}) is "
                f"~{skew_ratio:.1f}x the next-highest card "
                f"(~{gap_pct:.0f}% gap). It dominates the query - "
                f"start any optimization here."
            )
        elif this_time > 0 and max_time > 0 and time_fraction >= ORANGE_TIME_FRACTION:
            status = 'warn'
            if time_fraction >= 0.999:
                reason = (
                    f"Slowest card in the tree ({_us_to_ms_text(int(this_time))}). "
                    f"No bad query events were raised on this path."
                )
            else:
                reason = (
                    f"Time ({_us_to_ms_text(int(this_time))}) is "
                    f"{time_fraction * 100.0:.0f}% of the slowest card's time - "
                    f"close to the top. No bad query events were raised."
                )
        else:
            status = 'neutral'
            if this_time <= 0:
                reason = (
                    "No bad query events; no per-path timing data was "
                    "captured for this card."
                )
            elif max_time > 0:
                reason = (
                    f"No bad query events; time ({_us_to_ms_text(int(this_time))}) "
                    f"is {time_fraction * 100.0:.0f}% of the slowest card - "
                    f"not a focus card."
                )
            else:
                reason = "No bad query events detected on this card."

        node['status'] = status
        node['status_reason'] = reason


def _safe_text(value: Any) -> str:
    if value is None:
        return '(null)'
    return str(value)


# Small formatting helpers used by build_profile_text to present
# microsecond intervals as human-readable milliseconds (so users don't have
# to mentally divide by 1000 or decode "relativedelta(microseconds=+N)")
# and to strip trailing zeros from Vertica NUMERIC values (so 5.589 shows
# as "5.589" instead of "5.589000000000000000").

def _us_to_ms_text(value: Any) -> str:

    if value is None:
        return '(null)'
    us = _interval_to_us(value)
    if us is None:
        return str(value)
    ms = us / 1000.0
    if ms < 1:
        return f"{ms:.3f} ms"
    if ms < 10000:
        return f"{ms:.2f} ms"
    sec = ms / 1000.0
    if sec < 60:
        return f"{sec:.3f} s"
    return f"{sec:.2f} s"


def _trim_trailing_zeros(value: Any) -> str:
    """Trim trailing zeros and a trailing dot from Vertica NUMERIC output
    like '5.589000000000000000' -> '5.589', '1000.000000000' -> '1000'.
    Returns the input unchanged if it's not a numeric-looking string."""
    if value is None:
        return '(null)'
    s = str(value)
    # Only act on pure numeric forms (optional -, digits, optional ., digits)
    if not re.fullmatch(r'-?\d+\.\d+', s):
        return s
    s = s.rstrip('0').rstrip('.')
    return s or '0'


def _shorten_timestamp(value: Any) -> str:
    """Shorten a Vertica timestamp to 'YYYY-MM-DD HH:MM:SS.ffff' (drop the
    last two microsecond digits and the timezone). Returns original on
    non-matching inputs."""
    if value is None:
        return '(null)'
    s = str(value)
    # Match 'YYYY-MM-DD HH:MM:SS.ffffff+TZ' or 'YYYY-MM-DD HH:MM:SS.ffffff-TZ'
    m = re.match(r'^(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}\.\d{4})\d*([+-]\d{2}:?\d{2})?$', s)
    if m:
        return m.group(1)
    return s


def _interval_to_us(value: Any) -> Optional[int]:
    """Convert a Vertica INTERVAL (returned by the driver in any of several
    forms) into a plain integer number of microseconds. Returns None on failure
    or when the input was None.

    vertica-python may return an interval as:
      - dateutil.relativedelta.relativedelta(microseconds=+N)   (most common)
      - datetime.timedelta(...)
      - str like 'relativedelta(microseconds=+N)' (after round-trip through str)
      - str like '0:00:00.002698' or '00:00:00.002698'
      - int / float (already numeric)
    """
    if value is None:
        return None
    # Numeric: assume caller already has microseconds.
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        try:
            return int(value)
        except Exception:
            return None
    # datetime.timedelta
    try:
        import datetime as _dt
        if isinstance(value, _dt.timedelta):
            return int(round(value.total_seconds() * 1_000_000))
    except Exception:
        pass
    # dateutil.relativedelta.relativedelta
    try:
        from dateutil.relativedelta import relativedelta  # type: ignore
        if isinstance(value, relativedelta):
            total_us = 0
            total_us += int(value.microseconds or 0)
            total_us += int(value.seconds or 0) * 1_000_000
            total_us += int(value.minutes or 0) * 60 * 1_000_000
            total_us += int(value.hours or 0) * 3600 * 1_000_000
            total_us += int(value.days or 0) * 86400 * 1_000_000
            return total_us
    except Exception:
        pass
    # String parsing: two common shapes.
    text = str(value).strip()
    if not text:
        return None
    # "relativedelta(microseconds=+2698)" or similar kw=val pairs
    if text.startswith('relativedelta('):
        total_us = 0
        try:
            body = text[len('relativedelta('):-1] if text.endswith(')') else text[len('relativedelta('):]
            for part in body.split(','):
                if '=' not in part:
                    continue
                k, v = part.split('=', 1)
                k = k.strip().lower()
                v = v.strip().lstrip('+')
                try:
                    nv = int(v)
                except Exception:
                    try:
                        nv = int(float(v))
                    except Exception:
                        continue
                if k == 'microseconds':
                    total_us += nv
                elif k == 'seconds':
                    total_us += nv * 1_000_000
                elif k in ('minutes',):
                    total_us += nv * 60 * 1_000_000
                elif k in ('hours',):
                    total_us += nv * 3600 * 1_000_000
                elif k in ('days',):
                    total_us += nv * 86400 * 1_000_000
            return total_us
        except Exception:
            return None
    # "HH:MM:SS[.ffffff]" (Vertica interval in string form)
    m = re.match(r'^(\d+):(\d{1,2}):(\d{1,2})(?:\.(\d{1,6}))?$', text)
    if m:
        h, mi, s = int(m.group(1)), int(m.group(2)), int(m.group(3))
        frac = m.group(4) or ''
        frac_us = int((frac + '000000')[:6]) if frac else 0
        return (h * 3600 + mi * 60 + s) * 1_000_000 + frac_us
    # Fallback: raw number in a string
    try:
        return int(float(text))
    except Exception:
        return None


def _format_us_human(us: Optional[int]) -> str:
    """Human-readable duration for a microsecond count. Matches the JS
    formatDurationUs(): >=60s uses '<x>s' w/ 2 decimals; >=1s uses '<x>s' w/
    3 decimals; otherwise milliseconds with 2 decimals."""
    if us is None:
        return '(n/a)'
    try:
        sec = float(us) / 1_000_000.0
    except Exception:
        return '(n/a)'
    if sec >= 60:
        return f"{sec:.2f}s"
    if sec >= 1:
        return f"{sec:.3f}s"
    return f"{sec * 1000:.2f}ms"


def _format_table(rows: List[Dict[str, Any]], max_cell_width: int = 400) -> str:
    """Format a list of dicts as an aligned pipe table.

    max_cell_width caps each cell's width so pathological single-line values
    don't blow up the whole table. 400 is wide enough for most plan_line
    values; callers that need truly wide values (like sql_text) should render
    those outside the table as a separate block."""
    if not rows:
        return '(no rows)'
    headers = list(rows[0].keys())
    widths = {h: len(str(h)) for h in headers}
    for row in rows:
        for h in headers:
            widths[h] = min(max(widths[h], len(_safe_text(row.get(h)))), max_cell_width)

    def fmt_row(row_dict):
        return ' | '.join(_safe_text(row_dict.get(h))[:max_cell_width].ljust(widths[h]) for h in headers)

    divider = '-+-'.join('-' * widths[h] for h in headers)
    return '\n'.join([fmt_row({h: h for h in headers}), divider] + [fmt_row(r) for r in rows])


def _append_profile_section(blocks: List[str], step_no: int, title: str, rows: List[Dict[str, Any]], note: Optional[str] = None, step_label: Optional[str] = None):
    # v68: step_label lets a step use a non-numeric label like "03b" for
    # sub-sections added between existing numbered steps. If omitted, the
    # zero-padded step_no is used as before.
    label = step_label if step_label else f'{step_no:02d}'
    blocks.append(f'>>> Step {label}: {title}')
    blocks.append(_format_table(rows))
    if note:
        blocks.append(note)
    blocks.append('')


def _safe_append_profile_section(blocks: List[str], step_no: int, title: str,
                                  cursor, sql: str, params=None,
                                  note: Optional[str] = None,
                                  post_process=None,
                                  step_label: Optional[str] = None):

    label = step_label if step_label else f'{step_no:02d}'
    blocks.append(f'>>> Step {label}: {title}')
    try:
        rows = _execute_dict_query(cursor, sql, params)
        if post_process is not None:
            rows = post_process(rows) or rows
        blocks.append(_format_table(rows))
        if note:
            blocks.append(note)
    except Exception as e:
        # Log server-side so a DBA can inspect full traceback, but render a
        # compact visible marker in the profile text so users know what's
        # missing and can still read the rest of the tab.
        logger.error(f'Profile step {label} ({title}) failed: {e}')
        blocks.append(f'(section failed: {type(e).__name__}: {str(e)[:200]})')
    blocks.append('')


def _execute_dict_query(cursor, sql: str, params=None) -> List[Dict[str, Any]]:
    cursor.execute(sql, params or [])
    return _rows_to_dicts(cursor, cursor.fetchall())




def _normalize_sql_for_match(sql_text: str) -> str:
    sql_text = re.sub(r'/\*.*?\*/', ' ', sql_text or '', flags=re.S)
    sql_text = re.sub(r'--.*?(\r?\n|$)', ' ', sql_text)
    sql_text = re.sub(r'^\s*profile\s+', '', sql_text, flags=re.I)
    sql_text = re.sub(r'\s+', ' ', sql_text).strip().rstrip(';')
    return sql_text.lower()


def _is_monitor_lookup_request(request_text: str) -> bool:
    hay = (request_text or '').lower()
    monitor_signatures = [
        'from query_requests',
        'from v_internal.dc_requests',
        'from v_internal.dc_requests_issued',
        'from v_monitor.query_profiles',
        'current_trans_id()',
        'current_statement()',
    ]
    return any(sig in hay for sig in monitor_signatures)


def locate_profile_ids_same_session(cursor, original_query: str) -> Tuple[int, int, str]:
    normalized_original = _normalize_sql_for_match(original_query)
    candidate_sql = """
        SELECT transaction_id, statement_id, request
        FROM query_requests
        WHERE transaction_id = current_trans_id()
          AND statement_id IN (1, current_statement() - 1, current_statement() - 2)
        ORDER BY CASE
                   WHEN statement_id = 1 THEN 0
                   WHEN statement_id = current_statement() - 1 THEN 1
                   WHEN statement_id = current_statement() - 2 THEN 2
                   ELSE 9
                 END,
                 start_timestamp DESC
    """
    cursor.execute(candidate_sql)
    rows = cursor.fetchall() or []
    if not rows:
        raise RuntimeError('Could not locate the profiled statement in query_requests for current_trans_id().')

    def score(row):
        transaction_id, statement_id, request_text = row[0], row[1], str(row[2] or '')
        normalized_request = _normalize_sql_for_match(request_text)
        score_value = 0
        if int(statement_id) == 1:
            score_value += 100
        if not _is_monitor_lookup_request(request_text):
            score_value += 50
        if normalized_original and normalized_original in normalized_request:
            score_value += 40
        elif normalized_original:
            original_head = normalized_original[:120]
            if original_head and original_head in normalized_request:
                score_value += 25
            else:
                original_tokens = [t for t in re.split(r'\W+', normalized_original) if len(t) >= 4][:12]
                overlap = sum(1 for t in original_tokens if t in normalized_request)
                score_value += min(overlap, 10)
        return score_value

    best = max(rows, key=score)
    transaction_id, statement_id, request_text = int(best[0]), int(best[1]), str(best[2] or '')
    if _is_monitor_lookup_request(request_text):
        raise RuntimeError(
            f'Profile lookup matched a monitor query instead of the profiled statement. Candidates: {rows!r}'
        )
    return transaction_id, statement_id, request_text

def locate_profile_ids(cursor, marker: str) -> Tuple[int, int, str]:
    attempts = 10
    last_rows = []
    lookup_sql = """
        SELECT transaction_id, statement_id, request
        FROM v_internal.dc_requests_issued
        WHERE request ILIKE %s
        ORDER BY time DESC
        LIMIT 5
    """
    for _ in range(attempts):
        cursor.execute(lookup_sql, [f'%{marker}%'])
        rows = cursor.fetchall()
        last_rows = rows
        for row in rows:
            if row[0] is not None and row[1] is not None:
                return int(row[0]), int(row[1]), str(row[2] or '')
        time.sleep(0.25)
    raise RuntimeError(
        f'Could not locate the profiled statement in dc_requests_issued for marker {marker!r}. Rows seen: {last_rows!r}'
    )



def _choose_full_profile_request_text(submitted_sql: str, observed_request_text: Optional[str]) -> str:
    submitted = (submitted_sql or '').strip().rstrip(';')
    observed = (observed_request_text or '').strip().rstrip(';')
    if not observed:
        return submitted + (';' if submitted else '')
    normalized_submitted = _normalize_sql_for_match(submitted)
    normalized_observed = _normalize_sql_for_match(observed)
    if submitted and normalized_submitted and normalized_submitted in normalized_observed and len(observed) >= len(submitted):
        return observed + (';' if observed and not observed.endswith(';') else '')
    if submitted and len(submitted) >= len(observed):
        return submitted + (';' if submitted and not submitted.endswith(';') else '')
    return observed + (';' if observed and not observed.endswith(';') else '')


def build_profile_text(cursor, transaction_id: int, statement_id: int, full_query_text: Optional[str] = None, query_file_label: str = '(editor)') -> str:
    blocks: List[str] = []
    blocks.append('+-------------------------------------------------------------------')
    blocks.append(f'| Date: {datetime.datetime.now()} :python qprof')
    blocks.append(f'| Transaction ID: {transaction_id}')
    blocks.append(f'| Statement ID: {statement_id}')
    blocks.append('| Clear Cache: 0')
    blocks.append(f'| Query File: {query_file_label}')
    blocks.append('+-------------------------------------------------------------------')
    blocks.append('')

    _append_profile_section(blocks, 0, 'Vertica version', _execute_dict_query(cursor, 'SELECT VERSION() AS version'))


    full_query_text = (full_query_text or '').strip()
    if full_query_text:
        _append_profile_section(blocks, 1, 'Query text', [{'request': full_query_text}])
    else:
        _append_profile_section(blocks, 1, 'Query text', _execute_dict_query(cursor, """
            SELECT request
            FROM v_internal.dc_requests_issued
            WHERE transaction_id=%s AND statement_id=%s
            ORDER BY time DESC
            LIMIT 1
        """, [transaction_id, statement_id]))
    # v63 item 2: present Step 02 as milliseconds, not raw microseconds.
    step2_rows = _execute_dict_query(cursor, """
        SELECT query_duration_us
        FROM v_monitor.query_profiles
        WHERE transaction_id=%s AND statement_id=%s
    """, [transaction_id, statement_id])
    for r in step2_rows:
        us = r.get('query_duration_us')
        r['query_duration_ms'] = _us_to_ms_text(us) if us is not None else '(null)'
        r.pop('query_duration_us', None)
    _append_profile_section(blocks, 2, 'Query duration', step2_rows)

    # v63 item 3: show Step 03 elapsed in a readable "N.NN ms" form
    # instead of "relativedelta(microseconds=+67038)".
    step3_rows = _execute_dict_query(cursor, """
        SELECT execution_step, MAX(completion_time - time) AS elapsed
        FROM v_internal.dc_query_executions
        WHERE transaction_id=%s AND statement_id=%s
        GROUP BY 1
        ORDER BY 2 DESC
    """, [transaction_id, statement_id])
    for r in step3_rows:
        r['elapsed'] = _us_to_ms_text(r.get('elapsed'))
    _append_profile_section(blocks, 3, 'Query execution steps', step3_rows)


    step3b_rows = _execute_dict_query(cursor, """
        WITH maxi AS (
            SELECT execution_step,
                   MAX(qe."time") AS last_start,
                   MIN(qe."time") AS first_start
            FROM v_internal.dc_query_executions qe
            WHERE transaction_id=%s AND statement_id=%s
            GROUP BY 1
        )
        SELECT qe.execution_step,
               qe.node_name,
               TIMESTAMPDIFF('millisecond', qe."time", qe.completion_time) AS elapsed_ms,
               CASE WHEN qe."time" = m.last_start AND m.first_start != m.last_start
                    THEN TIMESTAMPDIFF('millisecond', m.first_start, m.last_start)
                    ELSE NULL END AS skew_ms,
               CASE WHEN qe."time" = m.last_start
                         AND m.first_start != m.last_start
                         AND (m.last_start - m.first_start) = (
                             SELECT MAX(last_start - first_start) FROM maxi
                         ) THEN '>>'
                    WHEN qe."time" = m.last_start AND m.first_start != m.last_start
                         THEN '>'
                    ELSE '' END AS straggler
        FROM v_internal.dc_query_executions qe
        INNER JOIN maxi m USING(execution_step)
        WHERE qe.transaction_id=%s AND qe.statement_id=%s
        ORDER BY qe."time"
    """, [transaction_id, statement_id, transaction_id, statement_id])
    # Put straggler marker in front of node_name for readability in the
    # aligned-table output: "   v_eevdb_node0001", " > v_eevdb_node0004",
    # ">> v_eevdb_node0004".
    for r in step3b_rows:
        mark = r.pop('straggler', '') or ''
        node = r.get('node_name') or ''
        pad = {'>>': '>> ', '>': ' > ', '': '   '}.get(mark, '   ')
        r['node_name'] = pad + node
        if r.get('elapsed_ms') is not None:
            r['elapsed_ms'] = f"{int(r['elapsed_ms'])} ms"
        else:
            r['elapsed_ms'] = '(null)'
        if r.get('skew_ms') is not None:
            r['skew_ms'] = f"{int(r['skew_ms'])} ms"
        else:
            r['skew_ms'] = ''
    _append_profile_section(blocks, 3, 'Per-node execution steps with cross-node skew', step3b_rows,
        "Please note: each row shows ONE node's time for ONE step. 'skew_ms' is the spread "
        "between the fastest and slowest node on that step (shown only on the slowest row). "
        "The '>>' marker points to the node+step pair with the biggest skew across the whole "
        "query; '>' marks the slowest node on any other step that had skew. "
        "Steps with no skew marker ran on the initiator only.",
        step_label='03b')

    # v63 item 4: shorten timestamps and express queue_wait_time in ms.
    step4_rows = _execute_dict_query(cursor, """
        SELECT a.node_name, a.queue_entry_timestamp, a.acquisition_timestamp,
               (a.acquisition_timestamp - a.queue_entry_timestamp) AS queue_wait_time,
               a.pool_name, a.memory_inuse_kb AS mem_kb,
               (b.reserved_extra_memory_b/1000)::INTEGER AS emem_kb,
               (a.memory_inuse_kb-b.reserved_extra_memory_b/1000)::INTEGER AS rmem_kb,
               a.open_file_handle_count AS fhc, a.thread_count AS threads
        FROM v_monitor.resource_acquisitions a
        INNER JOIN query_profiles b ON a.transaction_id = b.transaction_id AND a.statement_id = b.statement_id
        WHERE a.transaction_id=%s AND a.statement_id=%s
        ORDER BY 1,2
    """, [transaction_id, statement_id])
    for r in step4_rows:
        r['queue_entry_timestamp'] = _shorten_timestamp(r.get('queue_entry_timestamp'))
        r['acquisition_timestamp'] = _shorten_timestamp(r.get('acquisition_timestamp'))
        r['queue_wait_time']       = _us_to_ms_text(r.get('queue_wait_time'))
    _append_profile_section(blocks, 4, 'Resource Acquisition', step4_rows,
        'Please note: mem_kb=memory acquired, emem_kb=unused acquired memory, rmem_kb=used memory.')

    _append_profile_section(blocks, 5, 'Query execution plan', _execute_dict_query(cursor, """
        SELECT statement_id AS stmtid, path_line
        FROM v_internal.dc_explain_plans
        WHERE transaction_id=%s AND statement_id=%s
        ORDER BY statement_id, path_id, path_line_index
    """, [transaction_id, statement_id]))

    # v63 item 6b: Step 06 running_time shown as readable ms.
    step6_rows = _execute_dict_query(cursor, """
        SELECT statement_id AS stmtid, path_id, running_time,
               (memory_allocated_bytes//(1024*1024))::numeric(18,2) AS mem_mb,
               (read_from_disk_bytes//(1024*1024))::numeric(18,2) AS read_mb,
               (received_bytes//(1024*1024))::numeric(18,2) AS in_mb,
               (sent_bytes//(1024*1024))::numeric(18,2) AS out_mb,
               LEFT(path_line, 80) AS path_line
        FROM v_monitor.query_plan_profiles
        WHERE transaction_id=%s AND statement_id=%s
        ORDER BY statement_id, path_id, path_line_index
    """, [transaction_id, statement_id])
    for r in step6_rows:
        rt = r.get('running_time')
        # running_time is None for most rows (sub-lines of a path); only
        # the first row of each path has a value.
        if rt is not None:
            r['running_time'] = _us_to_ms_text(rt)
    _append_profile_section(blocks, 6, 'Query plan profile', step6_rows)

    # v63 item 7: Step 07 is very wide (27 cols). Render in vsql's \x
    # expanded form (one field per line) so the output is readable.
    step7_rows = _execute_dict_query(cursor, """
        SELECT *
        FROM v_monitor.query_consumption
        WHERE transaction_id=%s AND statement_id=%s
        ORDER BY statement_id
    """, [transaction_id, statement_id])
    blocks.append('>>> Step 07: Query consumption')
    if not step7_rows:
        blocks.append('(no rows)')
    else:
        # Find the max key-column width across all rows so every record's
        # key-field column lines up.
        keys_all = list(step7_rows[0].keys())
        key_w = max(len(k) for k in keys_all)
        for idx, row in enumerate(step7_rows):
            blocks.append(f'-[ RECORD {idx+1} ]' + '-' * max(0, key_w - 10))
            for k in keys_all:
                v = row.get(k)
                # Shorten any timestamps we recognize.
                v_text = _shorten_timestamp(v) if isinstance(v, (str,))  else _safe_text(v)
                if v is not None and not isinstance(v, str):
                    # Non-string values: see if it's a datetime we should shorten
                    try:
                        import datetime as _dt
                        if isinstance(v, _dt.datetime):
                            v_text = _shorten_timestamp(str(v))
                        else:
                            v_text = _safe_text(v)
                    except Exception:
                        v_text = _safe_text(v)
                blocks.append(f"{k.ljust(key_w)} | {v_text}")
    blocks.append('')
    _append_profile_section(blocks, 8, 'Elapsed & memory allocated by node, path_id and activity', _execute_dict_query(cursor, """
        SELECT a.node_name, a.path_id, a.baseplan_id::VARCHAR || ',' || a.localplan_id::VARCHAR AS bl_id,
               b.path_line, a.description,
               (a.assigned_memory_bytes/(1024*1024))::numeric(18,2) AS mem_mb
        FROM v_internal.dc_plan_resources a
        INNER JOIN (
            SELECT path_id, regexp_replace(path_line,'^[^A-Z]*(.*)\\[.*$','\\1') AS path_line
            FROM v_internal.dc_explain_plans
            WHERE path_line_index = 1 AND transaction_id=%s AND statement_id=%s
        ) b ON a.path_id = b.path_id
        WHERE a.transaction_id=%s AND a.statement_id=%s
        ORDER BY 1,2,5 DESC
    """, [transaction_id, statement_id, transaction_id, statement_id]),
    # v64 item 1: clarify "(no rows)" is often the expected result. The same
    # empty output appears in qprof.sh's own output for this query shape -
    # dc_plan_resources is only populated when Vertica actually assigned
    # incremental per-operator memory (mostly large group-by / big joins).
    # For short queries with no spill, this table legitimately stays empty.
    'Please note: bl_id = baseplan_id,localplan_id.\n'
    'An empty result here is normal for queries that did not trigger '
    'per-operator memory assignment in dc_plan_resources (short / '
    'no-spill queries). Step 14 and Step 15 have the authoritative '
    'per-operator profile data.')
    _append_profile_section(blocks, 9, 'Elapsed, exec_time and I/O by node, activity & path_id', _execute_dict_query(cursor, """
        SELECT node_name, path_id, activity,
               activity_id::VARCHAR || ',' || baseplan_id::VARCHAR || ',' || localplan_id::VARCHAR AS abl_id,
               TIMESTAMPDIFF(us, start_time, end_time) AS elaps_us,
               execution_time_us AS exec_us,
               CASE WHEN associated_oid IS NOT NULL THEN description ELSE NULL END AS input,
               input_size_rows AS input_rows, ROUND(input_size_bytes/1000000, 2.0) AS input_mb,
               processed_rows AS proc_rows, ROUND(processed_bytes/1000000, 2.0) AS proc_mb
        FROM v_internal.dc_plan_activities
        WHERE transaction_id=%s AND statement_id=%s
        ORDER BY 1,2,4
    """, [transaction_id, statement_id]), 'Please note: abl_id = activity_id,baseplan_id,localplan_id')
    _append_profile_section(blocks, 10, 'Query events', _execute_dict_query(cursor, """
        SELECT event_timestamp, node_name, event_category, event_type, event_description, operator_name,
               path_id, event_details, suggested_action
        FROM v_monitor.query_events
        WHERE transaction_id=%s AND statement_id=%s
        ORDER BY 1
    """, [transaction_id, statement_id]))
    _append_profile_section(blocks, 11, 'Suggested Action Summary', _execute_dict_query(cursor, """
        SELECT path_id, MAX(suggested_action) AS suggested_action
        FROM v_monitor.query_events
        WHERE suggested_action <> '' AND transaction_id=%s AND statement_id=%s
        GROUP BY 1
        ORDER BY 1
    """, [transaction_id, statement_id]))
    _append_profile_section(blocks, 12, 'CPU Time by node and path_id', _execute_dict_query(cursor, """
        SELECT node_name, path_id, cet,
               (100*cet/(SUM(cet) over(partition by node_name)))::numeric(6,3) AS tot_node_cpu_perc
        FROM (
            SELECT node_name, path_id, SUM(counter_value) AS cet
            FROM v_monitor.execution_engine_profiles
            WHERE counter_name = 'execution time (us)' AND transaction_id=%s AND statement_id=%s
            GROUP BY 1,2
        ) x
        ORDER BY 1,2
    """, [transaction_id, statement_id]), 'Please note: tot_node_cpu_perc is the percent of CPU cycles spent on this node.')
    _append_profile_section(blocks, 13, 'Threads by node and path_id', _execute_dict_query(cursor, """
        SELECT node_name, path_id, operator_name, COUNT(DISTINCT operator_id) AS threads
        FROM v_monitor.execution_engine_profiles
        WHERE transaction_id=%s AND statement_id=%s
        GROUP BY 1,2,3
        ORDER BY 1,2,3
    """, [transaction_id, statement_id]))
    # v63 item 9: trim trailing zeros from Step 14 numeric columns.
    # exec_time_ms "5.589000000000000000" -> "5.589"; same for mem_res_mb etc.
    step14_rows = _execute_dict_query(cursor, """
        SELECT node_name, operator_name, path_id,
               ROUND(SUM(CASE counter_name WHEN 'execution time (us)' THEN counter_value ELSE NULL END)/1000,3.0) AS exec_time_ms,
               SUM(CASE counter_name WHEN 'estimated rows produced' THEN counter_value ELSE NULL END) AS est_rows,
               SUM(CASE counter_name WHEN 'rows processed' THEN counter_value ELSE NULL END) AS proc_rows,
               SUM(CASE counter_name WHEN 'rows produced' THEN counter_value ELSE NULL END) AS prod_rows,
               SUM(CASE counter_name WHEN 'rle rows produced' THEN counter_value ELSE NULL END) AS rle_prod_rows,
               SUM(CASE counter_name WHEN 'consumer stall (us)' THEN counter_value ELSE NULL END) AS cstall_us,
               SUM(CASE counter_name WHEN 'producer stall (us)' THEN counter_value ELSE NULL END) AS pstall_us,
               ROUND(SUM(CASE counter_name WHEN 'memory reserved (bytes)' THEN counter_value ELSE NULL END)/1000000,1.0) AS mem_res_mb,
               ROUND(SUM(CASE counter_name WHEN 'memory allocated (bytes)' THEN counter_value ELSE NULL END)/1000000,1.0) AS mem_all_mb,
               -- v71.5.3: modern non-deprecated counter alongside qprof.sh's
               -- two deprecated columns. Vertica engineer Jim Knicely on the
               -- forum: "memory allocated (bytes) was deprecated years ago";
               -- Vertica 24.3 docs explicitly mark "memory reserved (bytes)"
               -- as Deprecated. The current populated counter is
               -- 'peak memory requested (bytes)'. Step 14 keeps mem_res/mem_all
               -- for qprof.sh format compatibility but adds mem_peak_req_mb so
               -- the user can see the actually-populated value.
               ROUND(SUM(CASE counter_name WHEN 'peak memory requested (bytes)' THEN counter_value ELSE NULL END)/1000000,1.0) AS mem_peak_req_mb
        FROM v_monitor.execution_engine_profiles
        WHERE transaction_id=%s AND statement_id=%s AND counter_value/1000000 > 0
        GROUP BY 1,2,3
        -- v71.5.3 (Maya's Profile Text TAB QA): without HAVING, every group
        -- that has ANY surviving counter shows up, even if its only kept
        -- counters are ones we don't project (e.g. 'bytes received'). Result:
        -- 446 rows with every metric column showing (null). Filter to keep
        -- only groups where at least ONE of our projected metric columns is
        -- non-NULL, so the report actually has data to read.
        HAVING SUM(CASE counter_name WHEN 'execution time (us)'  THEN counter_value ELSE NULL END) IS NOT NULL
            OR SUM(CASE counter_name WHEN 'estimated rows produced' THEN counter_value ELSE NULL END) IS NOT NULL
            OR SUM(CASE counter_name WHEN 'rows processed'       THEN counter_value ELSE NULL END) IS NOT NULL
            OR SUM(CASE counter_name WHEN 'rows produced'        THEN counter_value ELSE NULL END) IS NOT NULL
            OR SUM(CASE counter_name WHEN 'memory reserved (bytes)' THEN counter_value ELSE NULL END) IS NOT NULL
            OR SUM(CASE counter_name WHEN 'peak memory requested (bytes)' THEN counter_value ELSE NULL END) IS NOT NULL
        ORDER BY (exec_time_ms IS NULL), exec_time_ms DESC
    """, [transaction_id, statement_id])
    for r in step14_rows:
        for col in ('exec_time_ms', 'mem_res_mb', 'mem_all_mb'):
            if r.get(col) is not None:
                r[col] = _trim_trailing_zeros(r[col])
    _append_profile_section(blocks, 14, 'Query execution report', step14_rows)


    _safe_append_profile_section(blocks, 15, 'Top 20 operators by execution time', cursor, """
        SELECT operator_name,
               path_id,
               ROUND(SUM(counter_value) / 1000, 3) AS total_exec_ms,
               COUNT(DISTINCT node_name)           AS nodes,
               COUNT(DISTINCT operator_id)         AS threads
        FROM v_monitor.execution_engine_profiles
        WHERE transaction_id=%s AND statement_id=%s
          AND counter_name = 'execution time (us)'
        GROUP BY 1, 2
        ORDER BY 3 DESC
        LIMIT 20
    """, [transaction_id, statement_id],
    note=('Please note: total_exec_ms is the wall-clock work summed across nodes and threads, '
          'not real elapsed time. The top row is usually where to focus tuning; '
          'if Scan dominates, look at projection segmentation and stats; '
          'if Join dominates, look at join order and resegment vs broadcast; '
          'if NetworkSend/NetworkRecv dominates, look at distribution cost. '
          'EMPTY result: Vertica probably purged the EEP execution-time counters '
          'before profiling could read them - dc_execution_engine_profiles has a '
          'short default retention on many clusters. Raise retention via '
          "SELECT set_data_collector_time_policy('ExecutionEngineProfiles','1 day'); "
          'to keep per-operator execution-time counters long enough to be useful. '
          'In the graph page, cluster-wide per-path running_time from '
          'query_plan_profiles is already shown on every card as a fallback.'),
    # v63 item 10: trim trailing zeros on the NUMERIC total_exec_ms column
    post_process=lambda rows: [{**r, 'total_exec_ms': _trim_trailing_zeros(r.get('total_exec_ms'))} for r in rows])

    _safe_append_profile_section(blocks, 16, 'Projections used by query', cursor, """
        SELECT node_name,
               anchor_table_schema || '.' || anchor_table_name AS anchor_table,
               projection_name
        FROM v_monitor.projection_usage
        WHERE transaction_id=%s AND statement_id=%s
        ORDER BY 2, 3, 1
    """, [transaction_id, statement_id],
    note=('Please note: If the same anchor_table shows two projections with different '
          'suffixes (_b0 vs _b1), the cluster likely ran in a degraded state for this query. '
          'If an unexpected projection is chosen, check whether your tuned projection is '
          'usable for this query shape (joins, filters, sort order).'))


    _STATS_STALE_DAYS = 30
    def _flag_stats(rows: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        now = datetime.datetime.now(datetime.timezone.utc)
        out: List[Dict[str, Any]] = []
        for r in rows:
            r = dict(r)
            st = r.get('statistics_type')
            ts = r.get('statistics_updated_timestamp')
            flag = ''
            if not st or str(st).upper() in ('NONE', 'ROWCOUNT'):
                flag = '(NO STATS)'
            elif ts is not None:
                try:
                    ts_dt = ts if isinstance(ts, datetime.datetime) else None
                    if ts_dt is not None:
                        if ts_dt.tzinfo is None:
                            ts_dt = ts_dt.replace(tzinfo=datetime.timezone.utc)
                        age_days = (now - ts_dt).days
                        if age_days > _STATS_STALE_DAYS:
                            flag = f'(STALE: {age_days}d)'
                except Exception:
                    pass
            r['age_flag'] = flag
            # v63 item 11: shorten statistics_updated_timestamp to
            # "YYYY-MM-DD HH:MM:SS.ffff" (drop last 2 microsecond digits
            # and the timezone). Easier to scan at a glance.
            if ts is not None:
                r['statistics_updated_timestamp'] = _shorten_timestamp(str(ts))
            out.append(r)
        return out

    _safe_append_profile_section(blocks, 17, 'Sort-column statistics age (for projections used by this query)', cursor, """
        SELECT DISTINCT
               p.anchor_table_schema || '.' || p.anchor_table_name AS anchor_table,
               pc.projection_name,
               pc.projection_column_name                            AS column_name,
               pc.sort_position,
               pc.encoding_type,
               pc.statistics_type,
               pc.statistics_updated_timestamp
        FROM v_monitor.projection_usage p
        INNER JOIN v_catalog.projection_columns pc
                ON p.projection_id = pc.projection_id
        WHERE p.transaction_id=%s AND p.statement_id=%s
          AND pc.sort_position >= 0
        ORDER BY 1, 2, 4
    """, [transaction_id, statement_id],
    note=(f'Please note: Columns flagged (STALE: Nd) have statistics older than '
          f'{_STATS_STALE_DAYS} days; (NO STATS) means statistics_type is NONE or ROWCOUNT only. '
          f'Stale/missing stats are a common cause of bad join plans (broadcast vs resegment) '
          f'and of RESEGMENTED_MANY_ROWS events. Remediate with '
          f"ANALYZE_STATISTICS('<schema>.<table>') or ANALYZE_HISTOGRAM for higher accuracy."),
    post_process=_flag_stats)

    # Step 18 (F-STEP18-LOCKS-01): transaction lock attempts. Most
    # queries show zero rows here. Rows appear when the transaction
    # had to wait on or was blocked by another session's lock. Useful
    # to diagnose "query was inexplicably slow today" where the plan
    # didn't change but the system was loaded.
    _safe_append_profile_section(blocks, 18, 'Transaction locks', cursor, """
        SELECT node_name,
               (time - start_time) AS lock_wait,
               object_name,
               mode,
               promoted_mode,
               scope,
               result,
               description
        FROM v_internal.dc_lock_attempts
        WHERE transaction_id=%s
        ORDER BY node_name, time
    """, [transaction_id],
    note=('Please note: Rows here mean the transaction had to negotiate a lock. '
          'lock_wait is how long it waited before acquiring; result other than '
          '"granted" means the lock attempt failed. In a healthy, contention-free '
          'run this section is (no rows).'))

    # v68 NEW Step 19 (F-STEP19-ISOLATED-PROJ-01): find projections used by
    # THIS query whose segment_expression does not align with any other
    # cluster projection's segmentation. Isolated projections guarantee
    # a resegment/broadcast on any join against another table -- exactly
    # the cause of RESEGMENTED_MANY_ROWS events. For each isolated
    # projection we also suggest concrete re-segment candidates: the
    # most frequently used hash columns across the cluster that align
    # with a column the projection already has.
    #
    # Adapted from user's uploaded test.sh Query 5. Scoped to the
    # projections this query actually touched (projection_usage filter)
    # so the Profile tab doesn't dump every projection in the cluster.
    _safe_append_profile_section(blocks, 19, 'Isolated projections with suggested segmentation', cursor, """
        WITH base AS (
            SELECT p.projection_id,
                   p.projection_schema,
                   p.projection_name,
                   SUBSTR(p.segment_expression, 1, 500) AS seg_sub,
                   REGEXP_REPLACE(SUBSTR(p.segment_expression, 1, 500), '\\w+\\.') AS seg_norm,
                   REPLACE(
                       SUBSTR(REGEXP_REPLACE(SUBSTR(p.segment_expression, 1, 500), '\\w+\\.'), 6),
                       ')',
                       ''
                   ) AS hash_expr,
                   p.is_segmented
            FROM v_catalog.projections p
        ),
        this_query_projections AS (
            SELECT DISTINCT projection_id
            FROM v_monitor.projection_usage
            WHERE transaction_id=%s AND statement_id=%s
        ),
        isolated_segmentation AS (
            SELECT seg_norm
            FROM base
            WHERE projection_name NOT ILIKE '%%b1'
              AND is_segmented
            GROUP BY seg_norm
            HAVING COUNT(*) = 1
        ),
        top_hash AS (
            SELECT hash_expr
            FROM base
            WHERE projection_name NOT ILIKE '%%b1'
              AND is_segmented
            GROUP BY hash_expr
            ORDER BY COUNT(*) DESC
            LIMIT 20
        )
        SELECT b.projection_schema || '.' || b.projection_name AS isolated_projection,
               b.seg_norm AS current_segmentation,
               'SEGMENTED BY hash(' || pc.projection_column_name || ')' AS suggested_segmentation
        FROM base b
        INNER JOIN this_query_projections tq ON b.projection_id = tq.projection_id
        INNER JOIN v_catalog.projection_columns pc ON pc.projection_id = b.projection_id
        INNER JOIN isolated_segmentation iseg ON b.seg_norm = iseg.seg_norm
        INNER JOIN top_hash th ON pc.projection_column_name = th.hash_expr
        WHERE b.projection_name NOT ILIKE '%%b1'
        ORDER BY 1, 2, 3
    """, [transaction_id, statement_id],
    note=('Please note: an "isolated projection" is one whose segmentation expression is '
          'not shared by any other projection in the cluster. Joins against isolated '
          'projections cannot be Local and will trigger Resegment or Broadcast - the '
          'common cause of RESEGMENTED_MANY_ROWS events. Each suggested_segmentation '
          'column is one of the 20 most-shared hash keys cluster-wide; re-segmenting '
          'the isolated projection on one of these can convert the join to Local. '
          'Empty result means all projections this query used are already aligned '
          'with cluster-wide segmentation patterns.'))

    return '\n'.join(blocks)


def _parse_cost_from_plan_text(plan_text: str) -> str:
    text = str(plan_text or '')
    match = re.search(r'\[Cost:\s*([^\],]+)', text, flags=re.I)
    return match.group(1).strip() if match else ''


def _parse_rows_from_plan_text(plan_text: str) -> int:
    text = str(plan_text or '')
    match = re.search(r'Rows:\s*([0-9][0-9,]*(?:\.[0-9]+)?)([KMBT]?)', text, flags=re.I)
    if not match:
        return 0
    value = float(match.group(1).replace(',', ''))
    suffix = match.group(2).upper()
    factor = {'': 1, 'K': 1_000, 'M': 1_000_000, 'B': 1_000_000_000, 'T': 1_000_000_000_000}.get(suffix, 1)
    try:
        return int(value * factor)
    except Exception:
        return 0


def _parse_cost_from_text(text_value: str) -> str:
    text = str(text_value or '')
    match = re.search(r'Cost:\s*([0-9][0-9,]*(?:\.[0-9]+)?[KMBT]?)', text, flags=re.I)
    return match.group(1).replace(',', '').strip() if match else ''


def _parse_best_cost_from_lines(lines: List[str]) -> str:
    for line in (lines or []):
        cost = _parse_cost_from_text(line)
        if cost:
            return cost
    return ''


def _operator_display_name(operator_name: str) -> str:
    value = str(operator_name or '').strip()
    if not value:
        return ''
    upper = value.upper()
    mapping = {
        'GROUPBYHASH': 'GROUPBY HASH',
        'GROUPBYPIPELINED': 'GROUPBY PIPELINED',
        'JOINHASH': 'JOIN HASH',
        'MERGEJOIN': 'MERGE JOIN',
        'STORAGEACCESS': 'STORAGE ACCESS',
        'NETWORKRECV': 'NETWORK RECV',
        'NETWORKSEND': 'NETWORK SEND',
        'TOPK': 'SORT [TOP-K]',
        'SORT': 'SORT',
        'SELECT': 'SELECT',
        'ANALYTICAL': 'ANALYTICAL',
        'UNION': 'UNION',
        'INSERT': 'INSERT',
        'UPDATE': 'UPDATE',
        'DELETE': 'DELETE',
    }
    if upper in mapping:
        return mapping[upper]
    value = re.sub(r'([a-z0-9])([A-Z])', r'\1 \2', value)
    value = re.sub(r'\s+', ' ', value).strip()
    return value.upper()


def fetch_profile_graph_data(cursor, transaction_id: int, statement_id: int, full_query_text: Optional[str] = None, observed_request_text: Optional[str] = None) -> Dict:
    cursor.execute("SELECT VERSION() AS version")
    version_row = cursor.fetchone()
    version_text = str(version_row[0]) if version_row and version_row[0] is not None else ''

    cursor.execute("""
        SELECT query_duration_us
        FROM v_monitor.query_profiles
        WHERE transaction_id = %s AND statement_id = %s
        LIMIT 1
    """, [transaction_id, statement_id])
    duration_row = cursor.fetchone()
    duration_us = int(duration_row[0]) if duration_row and duration_row[0] is not None else 0

    cursor.execute("""
        SELECT execution_step, MAX(completion_time - time) AS elapsed
        FROM v_internal.dc_query_executions
        WHERE transaction_id = %s AND statement_id = %s
        GROUP BY 1
        ORDER BY 2 DESC
    """, [transaction_id, statement_id])
    execution_steps = [{'execution_step': row[0], 'elapsed': str(row[1])} for row in cursor.fetchall()]

    cursor.execute("""
        SELECT path_id, path_line_index, path_line
        FROM v_internal.dc_explain_plans
        WHERE transaction_id = %s AND statement_id = %s
        ORDER BY path_id, path_line_index
    """, [transaction_id, statement_id])
    explain_path_lines: Dict[int, List[str]] = {}
    # v55: track the FIRST line per path_id (the operator line with "+-" marker)
    # and its global line index. Used to infer tree topology - depth comes from
    # the leading '|' count, outer/inner from the "Outer -> " / "Inner -> "
    # prefix, and parent-child order comes from DFS ordering by line index.
    path_first_line: Dict[int, Tuple[int, str]] = {}
    for r in cursor.fetchall():
        if r[0] is None:
            continue
        path_id = int(r[0])
        line_index = int(r[1]) if r[1] is not None else 0
        raw_line = str(r[2] or '')
        explain_path_lines.setdefault(path_id, []).append(raw_line)
        cur = path_first_line.get(path_id)
        if cur is None or line_index < cur[0]:
            path_first_line[path_id] = (line_index, raw_line)

    # v55: infer tree topology. For each path_id with a known operator line,
    # count leading '|' before the first '+' to determine depth, and look for
    # "Outer -> " / "Inner -> " to tag which side of its parent's join it came
    # from. Then walk paths in DFS order (sorted by global line index) with a
    # depth-indexed stack to assign parent_path_id.
    def _path_depth_from_line(line: str) -> int:
        # "| | +-- Outer -> ..." -> depth 3 (two leading pipes + the + marker)
        # "+-JOIN HASH..."        -> depth 1
        m = re.match(r'^\s*((?:\|\s*)*)(\+[-+>]*)', line or '')
        if not m:
            return 0
        return m.group(1).count('|') + 1

    def _path_side_from_line(line: str) -> Optional[str]:
        t = (line or '')
        if re.search(r'\bOuter\s*->', t):
            return 'outer'
        if re.search(r'\bInner\s*->', t):
            return 'inner'
        return None

    path_depths: Dict[int, int] = {
        p: _path_depth_from_line(v[1]) for p, v in path_first_line.items()
    }
    path_sides: Dict[int, Optional[str]] = {
        p: _path_side_from_line(v[1]) for p, v in path_first_line.items()
    }
    # Walk paths in DFS order so the stack-based parent inference is correct.
    paths_dfs = sorted(
        (p for p in path_first_line if p >= 0),
        key=lambda p: path_first_line[p][0],
    )
    parent_path_id: Dict[int, Optional[int]] = {}
    _stack: List[Tuple[int, int]] = []  # [(path_id, depth), ...]
    for p in paths_dfs:
        d = path_depths.get(p, 0)
        while _stack and _stack[-1][1] >= d:
            _stack.pop()
        parent_path_id[p] = _stack[-1][0] if _stack else None
        _stack.append((p, d))

    # v58 (F-EDGE-LABEL-01): derive the distribution + modifier info for
    # each non-root child path from its parent's plan-line suffix. For a
    # JOIN node Vertica prints a suffix after "(PATH ID: N)" of the form
    # "<Side> (<Modifier>)(<Modifier>)..." where <Side> is Outer or Inner
    # and each <Modifier> is BROADCAST / RESEGMENT / LOCAL RESEGMENT /
    # LOCAL ROUND ROBIN / GLOBAL RESEGMENT. These modifiers describe HOW
    # that side's input is distributed TO this JOIN. We look up the
    # parent's first line, find the group matching the child's side, and
    # collapse the modifier bag into one of the canonical distribution
    # codes the mockup uses: "" (Local), B, LR, GLR, R. The child's
    # operator side ('outer'/'inner') comes from path_sides; the child's
    # parent JOIN kind (HASH/MERGE/Pipe/Filter/Cross) is inferred from
    # the parent's primary line and used by the frontend to build the
    # join-kind letter suffix.
    # Mapping rules (case-insensitive on the modifier bag):
    #   'BROADCAST'                             -> B
    #   'GLOBAL' + ('LOCAL RESEGMENT'|'LOCAL ROUND ROBIN')  -> GLR
    #   'LOCAL RESEGMENT' or 'LOCAL ROUND ROBIN' (no global) -> LR
    #   'RESEGMENT' or 'GLOBAL' (no local)      -> R
    #   otherwise                                -> '' (Local)
    def _extract_suffix_after_path_id(plan_line: str) -> str:
        m = re.search(r'\(PATH\s+ID:\s*-?\d+\)\s*', plan_line or '', re.IGNORECASE)
        return (plan_line or '')[m.end():] if m else ''

    def _parse_side_modifiers(suffix: str, side: str) -> Optional[List[str]]:
        # Find "<Side> (mod1)(mod2)..." with that exact side word; return
        # the list of modifier strings, or None if the side isn't mentioned.
        pattern = rf'\b{re.escape(side)}\b((?:\s*\([^()]*\))+)'
        m = re.search(pattern, suffix, re.IGNORECASE)
        if not m:
            return None
        mods = re.findall(r'\(([^()]+)\)', m.group(1))
        return [mod.strip() for mod in mods if mod.strip()]

    def _distribution_code_from_mods(mods: List[str]) -> str:
        hay = ' '.join(m.upper() for m in (mods or []))
        if 'BROADCAST' in hay:
            return 'B'
        has_global = 'GLOBAL' in hay
        has_local  = ('LOCAL RESEGMENT' in hay) or ('LOCAL ROUND ROBIN' in hay)
        if has_global and has_local:
            return 'GLR'
        if has_local:
            return 'LR'
        if has_global or 'RESEGMENT' in hay:
            return 'R'
        return ''

    _DISTRIBUTION_NAMES = {
        'B':   'Broadcast',
        'LR':  'Local Resegment',
        'GLR': 'Global+Local Resegment',
        'R':   'Resegment',
        '':    'Local',
    }

    def _join_kind_letter_from_title(line: str) -> str:
        hay = (line or '').upper()
        if 'JOIN HASH'   in hay: return 'H'
        if 'JOIN MERGE'  in hay: return 'M'
        if 'JOIN PIPELINED' in hay or 'JOIN PIPE' in hay: return 'P'
        if 'JOIN FILTER' in hay: return 'F'
        if 'JOIN CROSS'  in hay or 'CROSS JOIN' in hay: return 'X'
        return ''

    # Build one edge descriptor per non-root path, keyed by child path_id.
    # The frontend reads these directly instead of trying to re-derive the
    # code from free-text titles. Non-JOIN parents fall back to kind=''
    # and distribution=''; the frontend can render those as plain 'FLOW'.
    edge_from_parent: Dict[int, Dict[str, Any]] = {}
    for child_id, par_id in parent_path_id.items():
        if par_id is None:
            continue
        parent_line = (path_first_line.get(par_id) or (0, ''))[1]
        child_side  = path_sides.get(child_id)
        join_kind   = _join_kind_letter_from_title(parent_line)
        mods: List[str] = []
        code = ''
        if child_side and join_kind:
            suffix = _extract_suffix_after_path_id(parent_line)
            parsed = _parse_side_modifiers(suffix, child_side)
            if parsed is not None:
                mods = parsed
                code = _distribution_code_from_mods(parsed)
        # Build the full label like "I-B-H", "O-H" (middle collapses when
        # distribution code is empty), "GLR-H" (no side for non-join
        # contexts that still have a distribution), or "FLOW".
        parts: List[str] = []
        if child_side == 'outer':
            parts.append('O')
        elif child_side == 'inner':
            parts.append('I')
        if code:
            parts.append(code)
        if join_kind:
            parts.append(join_kind)
        label = '-'.join(parts) if parts else 'FLOW'
        # Pick the coarse kind the frontend uses for edge coloring:
        # 'broadcast' (purple), 'resegment' (orange), 'local' (white).
        if code == 'B':
            coarse = 'broadcast'
        elif code in ('LR', 'GLR', 'R'):
            coarse = 'resegment'
        else:
            coarse = 'local'
        edge_from_parent[child_id] = {
            'label': label,
            'code': code,
            'distribution_name': _DISTRIBUTION_NAMES.get(code, 'Local'),
            'modifiers': mods,
            'side': child_side,                 # 'outer'|'inner'|None
            'join_kind': join_kind,             # 'H'|'M'|'P'|'F'|'X'|''
            'coarse_kind': coarse,              # for CSS class on the pill
        }

    cursor.execute("""
        SELECT path_id,
               MAX(running_time) AS running_time,
               MAX((memory_allocated_bytes/(1024*1024))::numeric(18,2)) AS memory_mb,
               MAX((read_from_disk_bytes/(1024*1024))::numeric(18,2)) AS read_mb,
               MAX((received_bytes/(1024*1024))::numeric(18,2)) AS received_mb,
               MAX((sent_bytes/(1024*1024))::numeric(18,2)) AS sent_mb,
               MAX(path_line) AS plan_line
        FROM v_monitor.query_plan_profiles
        WHERE transaction_id = %s AND statement_id = %s
        GROUP BY 1
        ORDER BY 1
    """, [transaction_id, statement_id])
    profile_rows = {}
    for r in cursor.fetchall():
        path_id = int(r[0])
        # F-CARD-CLOCKTIME-PRE: keep the driver's native interval as the
        # source of truth and extract an int microsecond count too so the
        # frontend can format it cleanly (the driver's str() gives ugly
        # output like "relativedelta(microseconds=+2698)").
        running_time_us = _interval_to_us(r[1])
        profile_rows[path_id] = {
            'running_time': str(r[1]) if r[1] is not None else None,  # legacy
            'running_time_us': running_time_us,                        # new, clean int
            'memory_mb': float(r[2]) if r[2] is not None else 0.0,
            'read_mb': float(r[3]) if r[3] is not None else 0.0,
            'received_mb': float(r[4]) if r[4] is not None else 0.0,
            'sent_mb': float(r[5]) if r[5] is not None else 0.0,
            'received_rows': 0,
            'produced_rows': 0,
            'plan_line': str(r[6] or ''),
            'path_description': '',
        }

    # v56: also pull 'clock time (us)' (elapsed wall-clock per operator) and
    # COUNT(DISTINCT operator_id) (threads assigned to the operator across all
    # nodes). Used by the new popup OPERATORS section to render:
    #   "Exec: Xms   Clock: Yms   Thr: N"
    # under each operator row (mockup slide 11/15).
    cursor.execute("""
        SELECT path_id,
               operator_name,
               ROUND(SUM(CASE counter_name WHEN 'execution time (us)' THEN counter_value ELSE NULL END)/1000,3.0) AS exec_time_ms,
               ROUND(SUM(CASE counter_name WHEN 'clock time (us)'     THEN counter_value ELSE NULL END)/1000,3.0) AS clock_time_ms,
               SUM(CASE counter_name WHEN 'rows processed' THEN counter_value ELSE NULL END) AS proc_rows,
               SUM(CASE counter_name WHEN 'rows produced' THEN counter_value ELSE NULL END) AS prod_rows,
               SUM(CASE counter_name WHEN 'rows received' THEN counter_value ELSE NULL END) AS recv_rows,
               ROUND(SUM(CASE counter_name WHEN 'peak memory requested (bytes)' THEN counter_value ELSE NULL END)/1000000,1.0) AS mem_peak_req_mb,
               ROUND(SUM(CASE counter_name WHEN 'peak memory capacity (bytes)'  THEN counter_value ELSE NULL END)/1000000,1.0) AS mem_peak_cap_mb,
               ROUND(SUM(CASE counter_name WHEN 'memory allocated (bytes)' THEN counter_value ELSE NULL END)/1000000,1.0) AS mem_all_mb,
               ROUND(SUM(CASE counter_name WHEN 'memory reserved (bytes)'  THEN counter_value ELSE NULL END)/1000000,1.0) AS mem_res_mb,
               COUNT(DISTINCT operator_id) AS op_threads
        FROM v_monitor.execution_engine_profiles
        WHERE transaction_id = %s AND statement_id = %s
        GROUP BY 1, 2
        ORDER BY 1, 3 DESC
    """, [transaction_id, statement_id])
    engine_by_path = {}
    total_rows = 0
    max_memory_mb = 0.0
    for row in cursor.fetchall():
        path_id = int(row[0]) if row[0] is not None else -1
        mem_peak_req = float(row[7])  if row[7]  is not None else 0.0
        mem_peak_cap = float(row[8])  if row[8]  is not None else 0.0
        mem_all      = float(row[9])  if row[9]  is not None else 0.0
        mem_res      = float(row[10]) if row[10] is not None else 0.0
        if   mem_peak_req > 0: mem_memory_mb = mem_peak_req
        elif mem_peak_cap > 0: mem_memory_mb = mem_peak_cap
        elif mem_res      > 0: mem_memory_mb = mem_res
        else:                  mem_memory_mb = mem_all
        entry = {
            'operator_name': row[1],
            'exec_time_ms': float(row[2]) if row[2] is not None else 0.0,
            # v56: new per-operator fields for popup OPERATORS section
            'clock_time_ms': float(row[3]) if row[3] is not None else 0.0,
            'processed_rows': int(row[4]) if row[4] is not None else 0,
            'produced_rows': int(row[5]) if row[5] is not None else 0,
            'received_rows': int(row[6]) if row[6] is not None else 0,
            'memory_allocated_mb': mem_memory_mb,  # kept name for JS compat; value is peak_req|peak_cap|res|all
            'threads': int(row[11]) if row[11] is not None else 0,
        }
        total_rows = max(total_rows, entry['produced_rows'], entry['processed_rows'], entry['received_rows'])
        max_memory_mb = max(max_memory_mb, entry['memory_allocated_mb'])
        engine_by_path.setdefault(path_id, []).append(entry)

    # --- F-CARD-EXECON-01: Per-path EXECUTE-ON aggregation ---
    # For each path_id we compute:
    #   node_count   = COUNT(DISTINCT node_name) of nodes that did work on this path
    #   max_node_ms  = MAX over nodes of SUM of 'execution time (us)' / 1000
    #   per_node_ms  = array [{node_name, ms, threads}] used by the popup EXECUTION section
    # Source table: v_monitor.execution_engine_profiles
    # Counter:      'execution time (us)' (see "System Tables for Query Performance",
    #               Execution Engine Profiles counter list).
    # v56: also expose per-node thread count so the popup EXECUTION section
    # can render "v_eevdb_node0001  N thr * T ms" (matches mockup slide 11/15).
    cursor.execute("""
        SELECT path_id,
               node_name,
               SUM(CASE counter_name WHEN 'execution time (us)'
                                     THEN counter_value ELSE 0 END)/1000.0 AS node_sum_ms,
               COUNT(DISTINCT operator_id) AS node_threads
        FROM v_monitor.execution_engine_profiles
        WHERE transaction_id = %s AND statement_id = %s
        GROUP BY 1, 2
    """, [transaction_id, statement_id])
    execon_by_path: Dict[int, Dict[str, Any]] = {}
    for row in cursor.fetchall():
        if row[0] is None:
            continue
        pid = int(row[0])
        node_name = str(row[1] or '')
        node_ms = float(row[2]) if row[2] is not None else 0.0
        threads = int(row[3]) if row[3] is not None else 0
        bucket = execon_by_path.setdefault(pid, {'per_node': [], 'node_count': 0, 'max_node_ms': 0.0})
        bucket['per_node'].append({'node_name': node_name, 'ms': round(node_ms, 3), 'threads': threads})
    for pid, bucket in execon_by_path.items():
        bucket['per_node'].sort(key=lambda r: (-r['ms'], r['node_name']))
        bucket['node_count'] = len(bucket['per_node'])
        nonzero_ms = [r['ms'] for r in bucket['per_node']]
        bucket['max_node_ms'] = round(max(nonzero_ms, default=0.0), 3)
        bucket['min_node_ms'] = round(min(nonzero_ms, default=0.0), 3)


    cursor.execute("""
        SELECT path_id,
               node_name,
               operator_name,
               SUM(CASE counter_name WHEN 'rows produced' THEN counter_value ELSE NULL END) AS rows_produced,
               MAX(operator_id) AS max_op_id
        FROM v_monitor.execution_engine_profiles
        WHERE transaction_id = %s AND statement_id = %s
        GROUP BY 1, 2, 3
    """, [transaction_id, statement_id])
    per_node_ops_raw: Dict[int, Dict[str, List[Dict[str, Any]]]] = {}
    for row in cursor.fetchall():
        if row[0] is None or row[1] is None or row[2] is None:
            continue
        pid = int(row[0])
        node_name = str(row[1])
        operator_name = str(row[2])
        rows_produced = int(row[3]) if row[3] is not None else 0
        op_id = int(row[4]) if row[4] is not None else 0
        per_node_ops_raw.setdefault(pid, {}).setdefault(node_name, []).append({
            'operator_name': operator_name,
            'rows_produced': rows_produced,
            'operator_id': op_id,
        })
    per_node_last_op: Dict[int, List[Dict[str, Any]]] = {}
    for pid, by_node in per_node_ops_raw.items():
        items: List[Dict[str, Any]] = []
        for node_name, ops in by_node.items():
            # Priority 1: NetworkSend with rows - the actual upstream output
            # when the edge crosses the network (Broadcast / Resegment).
            net_send = [o for o in ops if o['operator_name'] == 'NetworkSend' and o['rows_produced'] > 0]
            if net_send:
                chosen = max(net_send, key=lambda o: (o['rows_produced'], o['operator_id']))
            else:
                # Priority 2: any op that actually produced rows; take the one
                # with the most rows (tie-break by later operator_id).
                with_rows = [o for o in ops if o['rows_produced'] > 0]
                if with_rows:
                    chosen = max(with_rows, key=lambda o: (o['rows_produced'], o['operator_id']))
                else:
                    # Priority 3: no row counters at all (pure pass-through paths);
                    # just report the last operator by operator_id as "0 rows".
                    chosen = max(ops, key=lambda o: o['operator_id'])
            items.append({
                'node_name': node_name,
                'operator_name': chosen['operator_name'],
                'rows': int(chosen['rows_produced']),
            })
        # Sort by rows desc so the popup shows the heaviest node first - that's
        # where the reader's eye should land when looking for skew.
        items.sort(key=lambda r: (-r['rows'], r['node_name']))
        per_node_last_op[pid] = items

    cursor.execute("""
        SELECT path_id, event_type, event_description, operator_name, event_details, suggested_action
        FROM v_monitor.query_events
        WHERE transaction_id = %s AND statement_id = %s
        ORDER BY event_timestamp
    """, [transaction_id, statement_id])
    event_rows = cursor.fetchall()
    events_by_path = {}
    for row in event_rows:
        path_id = int(row[0]) if row[0] is not None else -1
        events_by_path.setdefault(path_id, []).append({
            'event_type': row[1],
            'event_description': row[2],
            'operator_name': row[3],
            'event_details': row[4],
            'suggested_action': row[5],
        })

    sql_text = _choose_full_profile_request_text(full_query_text or '', observed_request_text)
    nodes = []

    plan_authoritative_ids = set(explain_path_lines.keys()) | set(profile_rows.keys())
    all_path_ids = sorted(plan_authoritative_ids)
    for path_id in all_path_ids:
        path_lines = explain_path_lines.get(path_id, [])
        if path_id < 0:
            continue
        # v54 fix (PATH 0 phantom card): execution_engine_profiles synthesizes
        # rows with path_id=0 for the initiator's final NetworkRecv/NetworkSend/
        # ExprEval on queries without an explicit SELECT LIMIT. These are not
        # real plan operators - dc_explain_plans never references path_id=0 for
        # them - but v53 was creating a "NETWORK RECV" card anyway, inflating
        # node_count. Skip path_id=0 unless the plan actually has it (as in the
        # mockup's SELECT LIMIT 100 which has a legitimate path 0).
        if (
            path_id == 0
            and path_id not in explain_path_lines
            and path_id not in profile_rows
        ):
            continue
        primary_line, detail_lines = _choose_primary_plan_line(path_lines)
        profile_metrics = dict(profile_rows.get(path_id, {}))
        node_operators = engine_by_path.get(path_id, [])
        operator_title = _operator_display_name(node_operators[0].get('operator_name')) if node_operators else ''
        merged_line = primary_line or profile_metrics.get('plan_line') or (path_lines[0] if path_lines else '')
        detail_title = _clean_plan_display_text(merged_line or '')
        title = _summarize_plan_title(detail_title) if detail_title else ''
        if (not title or _is_detail_plan_line(detail_title) or title.upper().startswith('SORT KEY')) and operator_title:
            title = operator_title
            if detail_title and _strip_path_suffix(detail_title).upper() == title.upper():
                detail_title = ''
        if not detail_title:
            detail_title = title
        events = events_by_path.get(path_id, [])

        eep_primary_ms = max((op.get('exec_time_ms') or 0.0) for op in node_operators) if node_operators else 0.0
        plan_running_us = float(profile_metrics.get('running_time_us') or 0.0)
        if eep_primary_ms > 0:
            primary_exec_ms = eep_primary_ms
            exec_source = 'eep'       # operator-level, per-node, eventually-consistent
        elif plan_running_us > 0:
            primary_exec_ms = plan_running_us / 1000.0
            exec_source = 'plan'      # path-level, cluster-wide, always reliable
        else:
            primary_exec_ms = 0.0
            exec_source = 'none'      # genuinely no data (path did not run)
        row_candidates = [
            profile_metrics.get('produced_rows') or 0,
            profile_metrics.get('received_rows') or 0,
            _parse_rows_from_plan_text(detail_title),
            _parse_rows_from_plan_text(' '.join(path_lines or [])),
        ]
        if node_operators:
            row_candidates.extend([
                max((op.get('processed_rows') or 0) for op in node_operators),
                max((op.get('produced_rows') or 0) for op in node_operators),
                max((op.get('received_rows') or 0) for op in node_operators),
            ])
        primary_rows = max(row_candidates) if row_candidates else 0
        node_memory_mb = float(profile_metrics.get('memory_mb') or 0.0)
        if node_operators:
            node_memory_mb = max(node_memory_mb, max((op.get('memory_allocated_mb') or 0.0) for op in node_operators))
        total_rows = max(total_rows, primary_rows)
        max_memory_mb = max(max_memory_mb, node_memory_mb)
        cost_text = _parse_best_cost_from_lines([detail_title] + list(path_lines or []) + list(detail_lines or []) + [str(profile_metrics.get('plan_line') or '')]) or '(n/a)'
        profile_metrics['plan_details'] = detail_lines
        status, badges = score_profile_node(detail_title, events, profile_metrics, duration_us)
        subtitle = ''
        stripped = _strip_path_suffix(detail_title)
        if stripped and stripped != title and not _is_detail_plan_line(stripped) and not stripped.lower().startswith('sort key'):
            subtitle = stripped
        execon = execon_by_path.get(path_id) or {'node_count': 0, 'max_node_ms': 0.0, 'per_node': []}
        nodes.append({
            'path_id': path_id,
            'title': detail_title,
            'short_title': title,
            'depth': infer_path_depth(path_lines[0] if path_lines else detail_title),
            'status': status,
            'badges': badges,
            'metrics': profile_metrics,
            'operators': node_operators,
            'events': events,
            'plan_details': detail_lines,
            'card_subtitle': subtitle,
            # v55: tree topology - parent_path_id and side (outer/inner) fed to
            # the frontend so it can render a branching tree instead of a linear
            # column. parent_path_id=None means this node is a tree root. side
            # is 'outer' / 'inner' / None depending on the Outer -> / Inner ->
            # marker Vertica prints on the path's first line.
            'parent_path_id': parent_path_id.get(path_id),
            'side': path_sides.get(path_id),
            # v58 (F-EDGE-LABEL-01): parent->this edge descriptor for this
            # path. Frontend consumes this directly instead of trying to
            # re-parse the child/parent titles. None for the tree root
            # (no incoming edge).
            'edge_from_parent': edge_from_parent.get(path_id),
            # v58 (Q-EDGE-LASTOPROWS-01): per-node "last operator rows" list
            # for THIS path's upstream side. Used by the edge popup: when an
            # edge connects child_path -> parent_path, the popup reads this
            # list from the CHILD so each node-row shows what the upstream
            # actually sent. [{node_name, operator_name, rows}, ...] or [].
            'per_node_last_op': per_node_last_op.get(path_id, []),
            'card_metrics': {
                'exec_time_ms': round(primary_exec_ms, 3),
                # v71.2: exec_source tells the client which table the
                # exec_time_ms came from. 'eep'  = execution_engine_profiles
                # operator sum (per-node, eventually-consistent);
                # 'plan' = query_plan_profiles.running_time (cluster-wide,
                # always reliable); 'none' = neither source had data.
                # Client shows a small "plan-level" footnote next to the
                # value when exec_source == 'plan' so the user knows
                # it's wall-clock not operator-sum.
                'exec_source': exec_source,
                'rows': primary_rows,
                'memory_mb': round(node_memory_mb, 2),
                'cost_text': cost_text,
                # F-CARD-EXECON-01: per-path EXECUTE-ON aggregate
                'exec_on_node_count': int(execon.get('node_count') or 0),
                'exec_on_max_ms': float(execon.get('max_node_ms') or 0.0),
                # v71.5.3 (Maya's feedback): min across nodes for THIS path,
                # same source as exec_on_max_ms. Lets the card render
                # "5 nodes, MIN: 23.9ms, MAX: 24.92ms" so skew across nodes
                # on this specific path is visible at a glance.
                'exec_on_min_ms': float(execon.get('min_node_ms') or 0.0),
                'exec_on_per_node': list(execon.get('per_node') or []),
                # v69 F-CARD-EXECON-PLAN-01: the plan's authoritative
                # "Execute on:" decision for this path, parsed from
                # dc_explain_plans.plan_line. None if the plan didn't
                # include an Execute-on clause for this path. Card
                # prefers this as its primary source of truth; the
                # EEP-derived exec_on_node_count/per_node is moved
                # to a secondary "monitoring coverage" line below.
                'exec_on_plan': _extract_plan_execute_on(path_lines),
            },
        })

    # Override per-card status with
    # the cross-card rule set. score_profile_node() above assigned
    # each card an isolated-score status; that produced "everything
    # orange/red" on trees with many cards because thresholds tuned
    # for 4-card queries would cascade on 27-card queries. The new
    # rules (see apply_card_status_rules comment) keep BLUE as the
    # default and reserve ORANGE/RED for cards where the user has
    # a concrete reason to focus. Status reason is also written
    # into node['status_reason'] for the popup banner.
    apply_card_status_rules(nodes)

    def _running_time_us(node: Dict[str, Any]) -> float:
        metrics = node.get('metrics') or {}
        # Prefer the clean int we stashed during profile_rows build.
        rt_us = metrics.get('running_time_us')
        if rt_us is not None:
            try:
                return float(rt_us)
            except Exception:
                pass
        value = metrics.get('running_time')
        if value is None:
            return 0.0
        text = str(value).strip()
        if not text:
            return 0.0
        try:
            return float(text)
        except Exception:
            pass
        match = re.search(r'([-+]?[0-9]*\.?[0-9]+)', text)
        return float(match.group(1)) if match else 0.0

    def _looks_like_storage(node: Dict[str, Any]) -> bool:
        hay = ' '.join([
            str(node.get('short_title') or ''),
            str(node.get('title') or ''),
            str(node.get('card_subtitle') or ''),
            ' '.join(str(x or '') for x in (node.get('plan_details') or [])),
        ]).upper()
        return 'STORAGE ACCESS' in hay

    def _looks_like_join(node: Dict[str, Any]) -> bool:
        hay = ' '.join([
            str(node.get('short_title') or ''),
            str(node.get('title') or ''),
            str(node.get('card_subtitle') or ''),
            ' '.join(str(x or '') for x in (node.get('plan_details') or [])),
        ]).upper()
        return 'JOIN HASH' in hay or 'JOIN MERGE' in hay or 'JOIN NEST' in hay

    path_times = [
        {'path_id': n.get('path_id'), 'time_us': _running_time_us(n)}
        for n in nodes
        if n.get('path_id') is not None and _running_time_us(n) > 0
    ]
    total_path_time_us = sum(item['time_us'] for item in path_times)
    slowest_path = max(path_times, key=lambda x: x['time_us']) if path_times else {'path_id': None, 'time_us': 0.0}
    slowest_pct = round((slowest_path['time_us'] / total_path_time_us) * 100.0, 1) if total_path_time_us > 0 else 0.0

    storage_nodes = [n for n in nodes if _looks_like_storage(n)]
    storage_scan_count = len({n.get('path_id') for n in storage_nodes if n.get('path_id') is not None})
    storage_rows_scanned = sum(int((n.get('card_metrics') or {}).get('rows') or 0) for n in storage_nodes)

    join_nodes = [n for n in nodes if _looks_like_join(n)]
    join_op_count = len({n.get('path_id') for n in join_nodes if n.get('path_id') is not None})
    join_combined_us = sum(_running_time_us(n) for n in join_nodes)

    # v64/v65: measure per-operator profile-data coverage ONCE. Used for
    # both the dynamic findings (tree_analysis) AND for the frontend's
    # partial-data indicators on each card.
    eep_cov = _measure_eep_coverage(cursor, transaction_id, statement_id)
    # v68: measure cross-node execution-step skew ONCE. Independent from
    # EEP coverage because dc_query_executions is cluster-wide even when
    # EEP isn't.
    step_skew = _measure_step_skew(cursor, transaction_id, statement_id)
    # v71: new measurements for the actionable findings introduced in the
    # post-v70 philosophy shift.
    #   resource_pool    - flags `general`-pool runs (F-RESOURCE-POOL-01)
    #   stats_gaps       - summarizes missing-stats columns (F-STATS-GAPS-01)
    #   isolated_projs   - concrete re-segmentation candidates pulled into
    #                      the BROADCAST / RESEGMENTED_MANY_ROWS findings
    #   projections_used - lets AUTO_PROJECTION_USED name the projection(s)
    #   cluster_nodes_detail - node_name/state/type list from v_catalog.nodes,
    #                      moved out of user-facing Step 00b and into Step 99
    #                      (QA appendix) + ?debug=1 surface on the graph page.
    resource_pool    = _measure_resource_pool(cursor, transaction_id, statement_id)
    stats_gaps       = _measure_stats_gaps(cursor, transaction_id, statement_id)
    # v71.3: per-node ExecutePlan:EEexecute timing from dc_query_executions
    # (cluster-wide, always reliable; same source qprof.sh uses). Fed to
    # _build_tree_analysis for the new F-QUERY-NODE-TIMES-01 finding and
    # to summary for the graph page's per-node context.
    query_node_times = _measure_query_node_times(cursor, transaction_id, statement_id)
    # v71.5.2: cluster-wide peak memory from resource_acquisitions. Fills
    # the "Peak Memory" hero tile so Maya sees memory data even when the
    # per-path memory columns are all NULL (common on queries where Vertica
    # does not populate query_plan_profiles.memory_allocated_bytes or the
    # EEP memory counters). Source is qprof.sh Step 04.
    peak_memory      = _measure_peak_memory(cursor, transaction_id, statement_id)
    cluster_nodes_detail: List[Dict[str, Any]] = []
    try:
        cursor.execute("""
            SELECT node_name, node_state, node_type
            FROM v_catalog.nodes
            ORDER BY node_name
        """)
        for row in cursor.fetchall() or []:
            cluster_nodes_detail.append({
                'node_name':  str(row[0] or ''),
                'node_state': str(row[1] or ''),
                'node_type':  str(row[2] or ''),
            })
    except Exception:
        pass
    isolated_projs: List[Dict[str, Any]] = []
    try:
        cursor.execute("""
            WITH base AS (
                SELECT p.projection_id,
                       p.projection_schema,
                       p.projection_name,
                       REGEXP_REPLACE(SUBSTR(p.segment_expression, 1, 500), '\\w+\\.') AS seg_norm,
                       p.is_segmented
                FROM v_catalog.projections p
            ),
            this_query_projections AS (
                SELECT DISTINCT projection_id
                FROM v_monitor.projection_usage
                WHERE transaction_id=%s AND statement_id=%s
            ),
            isolated_segmentation AS (
                SELECT seg_norm
                FROM base
                WHERE projection_name NOT ILIKE '%%b1'
                  AND is_segmented
                GROUP BY seg_norm
                HAVING COUNT(*) = 1
            ),
            top_hash AS (
                SELECT REPLACE(SUBSTR(seg_norm, 6), ')', '') AS hash_expr
                FROM base
                WHERE projection_name NOT ILIKE '%%b1'
                  AND is_segmented
                GROUP BY 1
                ORDER BY COUNT(*) DESC
                LIMIT 20
            )
            SELECT DISTINCT
                   b.projection_schema || '.' || b.projection_name AS isolated_projection,
                   b.seg_norm AS current_segmentation,
                   'SEGMENTED BY hash(' || pc.projection_column_name || ')' AS suggested_segmentation
            FROM base b
            INNER JOIN this_query_projections tq ON b.projection_id = tq.projection_id
            INNER JOIN v_catalog.projection_columns pc ON pc.projection_id = b.projection_id
            INNER JOIN isolated_segmentation iseg ON b.seg_norm = iseg.seg_norm
            INNER JOIN top_hash th ON pc.projection_column_name = th.hash_expr
            WHERE b.projection_name NOT ILIKE '%%b1'
            ORDER BY 1, 3
        """, [transaction_id, statement_id])
        for row in cursor.fetchall() or []:
            isolated_projs.append({
                'isolated_projection':    str(row[0] or ''),
                'current_segmentation':   str(row[1] or ''),
                'suggested_segmentation': str(row[2] or ''),
            })
    except Exception:
        pass
    projections_used: List[Dict[str, Any]] = []
    try:
        cursor.execute("""
            SELECT DISTINCT
                   anchor_table_schema || '.' || anchor_table_name AS anchor_table,
                   projection_name
            FROM v_monitor.projection_usage
            WHERE transaction_id=%s AND statement_id=%s
        """, [transaction_id, statement_id])
        for row in cursor.fetchall() or []:
            projections_used.append({
                'anchor_table':    str(row[0] or ''),
                'projection_name': str(row[1] or ''),
            })
    except Exception:
        pass

    # v71: server-side logging when coverage is incomplete. Keeps the
    # triage trail when a user reports weirdness without polluting the
    # user-facing UI. One INFO line per profile run.
    _cluster_nodes = int(eep_cov.get('cluster_nodes') or 0)
    _eep_seen      = int(eep_cov.get('eep_nodes_seen') or 0)
    _dpa_seen      = int(eep_cov.get('dpa_nodes_seen') or 0)
    if _cluster_nodes > 0 and (_eep_seen < _cluster_nodes or _dpa_seen < _cluster_nodes):
        try:
            log_info(
                f"v71 partial coverage: tx={transaction_id} stmt={statement_id} "
                f"cluster_nodes={_cluster_nodes} eep_nodes_seen={_eep_seen} "
                f"dpa_nodes_seen={_dpa_seen} "
                f"eep_total_rows={eep_cov.get('eep_total_rows')} "
                f"dpa_total_rows={eep_cov.get('dpa_total_rows')}"
            )
        except Exception:
            pass

    summary = {

        'transaction_id': str(transaction_id),
        'statement_id': str(statement_id),
        'query_duration_us': duration_us,
        'node_count': len(nodes),
        'event_count': len(event_rows),
        'bad_nodes': sum(1 for n in nodes if n['status'] == 'bad'),
        'warn_nodes': sum(1 for n in nodes if n['status'] == 'warn'),
        'good_nodes': sum(1 for n in nodes if n['status'] == 'good'),
        'execution_steps': execution_steps,
        'total_rows': total_rows,
        'max_memory_mb': round(max_memory_mb, 2),
        # v71.5.2 (F-PEAK-MEMORY-01): cluster-wide peak memory from
        # v_monitor.resource_acquisitions. Fallback for queries where
        # per-path memory is NULL everywhere (common on this cluster).
        # Frontend reads summary.peak_memory_mb and displays in the
        # third hero tile alongside Total Duration / Total Rows.
        'peak_memory_mb':     float(peak_memory.get('peak_memory_mb') or 0.0),
        'peak_memory_kb':     int(peak_memory.get('peak_memory_kb') or 0),
        'peak_memory_detail': peak_memory.get('per_node') or [],
        'version': version_text,
        'label': 'qprof',
        'sql_text': sql_text,
        'summary_metrics': {
            'slowest_path': slowest_path.get('path_id'),
            'slowest_path_us': slowest_path.get('time_us', 0.0),
            'slowest_path_pct': slowest_pct,
            'storage_scan_count': storage_scan_count,
            'storage_rows_scanned': storage_rows_scanned,
            'join_op_count': join_op_count,
            'join_combined_us': join_combined_us,
        },
        # v65: coverage metrics exposed to the frontend so each graph card
        # can show "1 of 5 nodes (partial)" when EEP was starved. Frontend
        # reads summary.coverage.cluster_nodes and compares to the card's
        # own exec_on_node_count.
        # v71: still exposed, but ONLY consumed by the ?debug=1 surfaces
        # and by Step 99. The default UI ignores it.
        'coverage': {
            'cluster_nodes':      int(eep_cov.get('cluster_nodes') or 0),
            'eep_nodes_seen':     int(eep_cov.get('eep_nodes_seen') or 0),
            'dpa_nodes_seen':     int(eep_cov.get('dpa_nodes_seen') or 0),
            'eep_total_rows':     int(eep_cov.get('eep_total_rows') or 0),
            'eep_exec_time_rows': int(eep_cov.get('eep_exec_time_rows') or 0),
            'dpa_total_rows':     int(eep_cov.get('dpa_total_rows') or 0),
        },
        # v71: resource pool + stats gaps + isolated projections surfaced
        # into summary so Step 99 can cross-reference them and the
        # tree_analysis findings can be re-derived on the client side
        # when needed (debug flag).
        'resource_pool':        resource_pool,
        'stats_gaps':           stats_gaps,
        'isolated_projections': isolated_projs,
        'projections_used':     projections_used,
        'cluster_nodes_detail': cluster_nodes_detail,
        # v71.3: per-node query-level execution time (dc_query_executions,
        # cluster-wide reliable). Surfaced here so the graph page can render
        # a "per-node timing" summary strip even when EEP had no per-path
        # breakdown.
        'query_node_times':     query_node_times,
        # v76: cross-node skew per execution step. This is the full
        # ranked list consumed by the new /skew/<profile_id> page.
        # Only included in the summary - the link in the Profile tab
        # decides whether to show itself based on the client-side
        # threshold (see MEANINGFUL_SKEW_MS_FLOOR / _FRACTION).
        'step_skew':            step_skew,
        # v56: dynamic help-chip for the "Query Execution Tree" title -
        # pre-computed observations about the specific graph shown. Built
        # deterministically from the node/event data; no internet/AI needed.
        # Frontend just joins the list with <br> under the static explanation.
        'tree_analysis': _build_tree_analysis(
            nodes, event_rows, duration_us, slowest_path, slowest_pct,
            storage_nodes, join_nodes, total_path_time_us,
            eep_coverage=eep_cov,
            step_skew=step_skew,
            resource_pool=resource_pool,
            stats_gaps=stats_gaps,
            isolated_projections=isolated_projs,
            projections_used=projections_used,
            query_node_times=query_node_times,
        ),
    }
    return {'summary': summary, 'nodes': nodes}


# v64 item 3 (F-EEP-GAP-01): measure execution_engine_profiles data
# coverage for the profiled transaction. Vertica sometimes ages out EEP
# counter rows before we can scrape them (short queries, busy clusters,
# or large dc_requests retention gaps). When that happens, Steps 12-15
# of the Profile tab show empty/null tables and the graph page shows
# 0-ms per-node values - which looks like a bug in this tool but isn't.
# We run ONE cheap aggregate query here. If coverage is incomplete, we
# emit a finding in _build_tree_analysis so users know what they're
# looking at.
def _measure_eep_coverage(cursor, transaction_id: int, statement_id: int) -> Dict[str, Any]:
    """Return a small dict describing per-operator profile-data
    availability across TWO Vertica tables:

      execution_engine_profiles (feeds Steps 12, 13, 14, 15 and graph cards)
        - eep_nodes_seen:    distinct node_name values present
        - eep_total_rows:    total EEP row count
        - eep_exec_time_rows: rows with counter_name='execution time (us)'

      dc_plan_activities (feeds Step 9)
        - dpa_nodes_seen:    distinct node_name values present
        - dpa_total_rows:    total dc_plan_activities row count

    Plus:
        - cluster_nodes:     number of PERMANENT nodes in the cluster.

    Both EEP and DPA can independently age out counter rows on busy clusters
    before a profile-collection pass scrapes them; we treat them as two
    separate coverage metrics so v65 can report which profile surface is
    incomplete. Never raises - errors return partial/empty dicts so the
    caller treats coverage as 'unknown' and skips the finding."""
    out: Dict[str, Any] = {}
    try:
        cursor.execute("""
            SELECT
                COUNT(DISTINCT node_name)                                             AS nodes_seen,
                COUNT(*)                                                              AS total_rows,
                SUM(CASE WHEN counter_name = 'execution time (us)' THEN 1 ELSE 0 END) AS exec_time_rows
            FROM v_monitor.execution_engine_profiles
            WHERE transaction_id = %s AND statement_id = %s
        """, [transaction_id, statement_id])
        row = cursor.fetchone() or (0, 0, 0)
        out['eep_nodes_seen']     = int(row[0] or 0)
        out['eep_total_rows']     = int(row[1] or 0)
        out['eep_exec_time_rows'] = int(row[2] or 0)
    except Exception:
        pass
    try:
        cursor.execute("""
            SELECT COUNT(DISTINCT node_name), COUNT(*)
            FROM v_internal.dc_plan_activities
            WHERE transaction_id = %s AND statement_id = %s
        """, [transaction_id, statement_id])
        row = cursor.fetchone() or (0, 0)
        out['dpa_nodes_seen'] = int(row[0] or 0)
        out['dpa_total_rows'] = int(row[1] or 0)
    except Exception:
        pass
    try:
        cursor.execute("""
            SELECT COUNT(*) FROM v_catalog.nodes WHERE node_type='PERMANENT'
        """)
        out['cluster_nodes'] = int((cursor.fetchone() or (0,))[0] or 0)
    except Exception:
        out['cluster_nodes'] = 0
    # v65: preserve the legacy field names so existing callers keep working.
    out.setdefault('nodes_seen',     out.get('eep_nodes_seen', 0))
    out.setdefault('total_rows',     out.get('eep_total_rows', 0))
    out.setdefault('exec_time_rows', out.get('eep_exec_time_rows', 0))
    return out


# v77 : expose the exact SQL text that _measure_step_skew
# runs, so the Skew page can show it verbatim in an (i) info-chip. The
# string below is the LITERAL text passed to cursor.execute - keep this
# in sync with the call site below if the query ever changes. The
# %s placeholders remain in the displayed text; the reader will quickly
# recognise them as the bind-param convention of the Vertica driver.
_SKEW_QUERY_SQL = """WITH per_step AS (
    SELECT execution_step,
           MAX("time") AS last_t,
           MIN("time") AS first_t,
           TIMESTAMPDIFF('millisecond', MIN("time"), MAX("time")) AS skew_ms
    FROM v_internal.dc_query_executions
    WHERE transaction_id=%s AND statement_id=%s
    GROUP BY 1
    HAVING COUNT(DISTINCT node_name) > 1
)
SELECT ps.execution_step,
       ps.skew_ms,
       MAX(CASE WHEN qe."time" = ps.last_t  THEN qe.node_name END) AS slowest_node,
       MAX(CASE WHEN qe."time" = ps.first_t THEN qe.node_name END) AS fastest_node,
       ps.first_t,
       ps.last_t
FROM per_step ps
INNER JOIN v_internal.dc_query_executions qe
    ON qe.execution_step = ps.execution_step
WHERE qe.transaction_id=%s AND qe.statement_id=%s
GROUP BY ps.execution_step, ps.skew_ms, ps.first_t, ps.last_t
ORDER BY ps.skew_ms DESC, ps.execution_step ASC"""


# v78 (Maya item #6, revised): SQL for the DURATION toggle view.
# Maya's final shape (preferred): a CTE that first converts the
# (completion_time - time) INTERVAL to milliseconds via
# DATEDIFF(millisecond, '0:00:00', ...) and then GROUPs per
# (node_name, execution_step) taking MAX(elapsed). This avoids
# the cast-semantics fragility of TIMESTAMPDIFF applied to an
# interval expression on older Vertica versions.
_DURATION_QUERY_SQL = """WITH list1 AS (
    SELECT node_name,
           execution_step,
           DATEDIFF(millisecond, '0:00:00', completion_time - time) AS elapsed
    FROM v_internal.dc_query_executions
    WHERE transaction_id=%s AND statement_id=%s
)
SELECT node_name,
       execution_step,
       MAX(elapsed) AS max_elapsed
FROM list1
GROUP BY 1, 2
ORDER BY 2, 3 DESC"""


# v82 item 5 : Query ScoreCard page.
#
# The SQL below is the VERBATIM content of vertica_query_scorecard.sql
# as supplied by Maya, embedded so the whole server is one file.
# It uses vsql-style :t_id / :s_id placeholders which we rewrite to
# vertica_python positional %s at execution time. LOCAL TEMPORARY
# tables make concurrent execution safe (per the file header); we
# still use a FRESH connection per request so no one session shares
# a Vertica cursor across concurrent threads.
_SCORECARD_QUERY_SQL = r"""-- =====================================================================
-- vertica_query_scorecard.sql
-- Scoring card of "bad things" that happened in a profiled query.
--
-- CONCURRENT EXECUTION IS SAFE
-- ----------------------------
-- This script uses LOCAL TEMPORARY tables. In Vertica, LOCAL TEMPORARY
-- tables live in v_temp_schema but are SESSION-PRIVATE: two sessions
-- can each create a table named qscard_plan and they are different
-- objects, invisible to each other. Therefore:
--   * Two dbadmins running this script at the same time       -> safe.
--   * A Python web server giving each HTTP request its own
--     Vertica connection (= its own session)                  -> safe.
--   * Same vsql session running the script sequentially       -> safe
--     (DROP TABLE IF EXISTS at the top wipes any leftovers).
-- The ONLY way to break parallel-safety is to share one Vertica
-- connection across concurrent threads in the Python layer. Don't do
-- that: one connection per request (or a proper single-checkout pool).
--
-- Table names are prefixed qscard_* so they never collide with temp
-- tables created by other tooling (qprof.sh, ad-hoc user work, etc.).
--
-- USAGE
-- -----
-- vsql:
--     \set t_id 45035996274879950
--     \set s_id 1
--     \i vertica_query_scorecard.sql
-- python/vertica_python:
--     Split the file on ';' and execute each statement in order on ONE
--     connection. The LAST SELECT returns the scorecard rows. The
--     trailing DROPs are optional cleanup.
--
-- PREREQUISITE
-- ------------
-- The target query should have been run under PROFILE (or profiling
-- enabled). Without that, EXECUTION_ENGINE_PROFILES is empty for this
-- (trx, stmt), and the script will tell you so loudly in the first
-- scorecard row ("Runtime counters available = no").
--
-- OUTPUT COLUMNS
-- --------------
--   display_order    stable sort key within a severity bucket
--   category         JOIN / GROUPBY / NETWORK / MEMORY / EVENT / ...
--   check_name       what was measured
--   severity         OK | INFO | LOW | MEDIUM | HIGH
--   score            the raw measured value (as VARCHAR so rows align)
--   details          human-readable explanation of the measurement
--   suggested_action remediation hint (empty when severity = OK/INFO)
-- =====================================================================

-- ---------------------------------------------------------------------
-- Drop any leftover temp tables from a previous run in the same session
-- ---------------------------------------------------------------------
DROP TABLE IF EXISTS v_temp_schema.qscard_plan_raw CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_plan    CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_events  CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_eep     CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_skew    CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_res     CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_phase   CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_dur     CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_proj    CASCADE;


-- ---------------------------------------------------------------------
-- 1. Plan shape -- joins, group-bys, broadcast, resegment.
--
--    v_monitor.query_plan_profiles is a VIEW with a complex definition;
--    combining it with COUNT(DISTINCT CASE WHEN ...) in one CTAS makes
--    the optimizer ask for tens of GB even for a 1-row result. We avoid
--    that with two cheap steps:
--      1a. Pull raw filtered plan lines into a temp table using
--          v_internal.dc_explain_plans (a real DC table, not a view --
--          same source qprof.sh step 5 uses).
--      1b. Aggregate from the tiny temp table.
-- ---------------------------------------------------------------------
CREATE LOCAL TEMPORARY TABLE qscard_plan_raw ON COMMIT PRESERVE ROWS AS
SELECT path_id, path_line, path_line_index
FROM   v_internal.dc_explain_plans
WHERE  transaction_id = :t_id AND statement_id = :s_id;

CREATE LOCAL TEMPORARY TABLE qscard_plan ON COMMIT PRESERVE ROWS AS
SELECT
    COUNT(DISTINCT CASE WHEN path_line_index = 1
                         AND path_line ILIKE '%JOIN HASH%'
                        THEN path_id END)                      AS hash_join_cnt,
    COUNT(DISTINCT CASE WHEN path_line_index = 1
                         AND path_line ILIKE '%MERGEJOIN%'
                        THEN path_id END)                      AS merge_join_cnt,
    COUNT(DISTINCT CASE WHEN path_line_index = 1
                         AND path_line ILIKE '%GROUPBY HASH%'
                        THEN path_id END)                      AS gby_hash_cnt,
    COUNT(DISTINCT CASE WHEN path_line_index = 1
                         AND path_line ILIKE '%GROUPBY PIPELINED%'
                        THEN path_id END)                      AS gby_pipe_cnt,
    COUNT(DISTINCT CASE WHEN path_line ILIKE '%BROADCAST%'
                        THEN path_id END)                      AS broadcast_cnt,
    COUNT(DISTINCT CASE WHEN path_line ILIKE '%GLOBAL RESEGMENT%'
                        THEN path_id END)                      AS global_reseg_cnt,
    COUNT(DISTINCT CASE WHEN path_line ILIKE '%RESEGMENT%'
                         AND path_line NOT ILIKE '%GLOBAL RESEGMENT%'
                        THEN path_id END)                      AS local_reseg_cnt,
    COUNT(DISTINCT path_id)                                    AS total_paths
FROM qscard_plan_raw;


-- ---------------------------------------------------------------------
-- 2. Query events (optimizer + execution)
-- ---------------------------------------------------------------------
CREATE LOCAL TEMPORARY TABLE qscard_events ON COMMIT PRESERVE ROWS AS
SELECT
    COUNT(CASE WHEN event_type = 'GROUP_BY_SPILLED'                     THEN 1 END) AS gby_spill_cnt,
    COUNT(CASE WHEN event_type = 'JOIN_SPILLED'                         THEN 1 END) AS join_spill_cnt,
    COUNT(CASE WHEN event_type = 'RESEGMENTED_MANY_ROWS'                THEN 1 END) AS reseg_many_cnt,
    COUNT(CASE WHEN event_type = 'WOS_SPILL'                            THEN 1 END) AS wos_spill_cnt,
    COUNT(CASE WHEN event_type = 'NO_HISTOGRAM'                         THEN 1 END) AS no_hist_cnt,
    COUNT(CASE WHEN event_type = 'PREDICATE_OUTSIDE_HISTOGRAM'          THEN 1 END) AS pred_out_hist_cnt,
    COUNT(CASE WHEN event_type = 'MEMORY_LIMIT_HIT'                     THEN 1 END) AS mem_limit_cnt,
    COUNT(CASE WHEN event_type = 'DELETE_WITH_NON_OPTIMIZED_PROJECTION' THEN 1 END) AS del_nonopt_cnt,
    COUNT(CASE WHEN event_type = 'RLE_OVERRIDDEN'                       THEN 1 END) AS rle_override_cnt,
    COUNT(CASE WHEN event_type = 'SIP_FALLBACK'                         THEN 1 END) AS sip_fallback_cnt,
    COUNT(CASE WHEN event_type = 'MERGE_CONVERTED_TO_UNION'             THEN 1 END) AS merge_to_union_cnt,
    COUNT(CASE WHEN event_type = 'PARTITIONS_ELIMINATED'                THEN 1 END) AS part_elim_cnt
FROM v_monitor.query_events
WHERE transaction_id = :t_id AND statement_id = :s_id;


-- ---------------------------------------------------------------------
-- 3. Execution-engine counters (spill, stalls, network, CPU time).
--    Also records eep_row_cnt so we can detect "query was not profiled".
-- ---------------------------------------------------------------------
CREATE LOCAL TEMPORARY TABLE qscard_eep ON COMMIT PRESERVE ROWS AS
SELECT
    COUNT(*)                                                                                                       AS eep_row_cnt,
    COALESCE(SUM(CASE WHEN counter_name = 'cumulative size of raw temp data (bytes)' THEN counter_value END), 0) AS spill_bytes,
    COALESCE(SUM(CASE WHEN counter_name = 'execution time (us)'    THEN counter_value END), 0) AS exec_time_us,
    COALESCE(SUM(CASE WHEN counter_name = 'clock time (us)'        THEN counter_value END), 0) AS clock_time_us,
    COALESCE(SUM(CASE WHEN counter_name = 'consumer stall (us)'    THEN counter_value END), 0) AS cons_stall_us,
    COALESCE(SUM(CASE WHEN counter_name = 'producer stall (us)'    THEN counter_value END), 0) AS prod_stall_us,
    COALESCE(SUM(CASE WHEN counter_name = 'bytes sent'             THEN counter_value END), 0) AS bytes_sent,
    COALESCE(SUM(CASE WHEN counter_name = 'bytes received'         THEN counter_value END), 0) AS bytes_recv,
    COALESCE(SUM(CASE WHEN counter_name = 'bytes read from disk'   THEN counter_value END), 0) AS bytes_read_disk,
    COALESCE(SUM(CASE WHEN counter_name = 'bytes read from cache'  THEN counter_value END), 0) AS bytes_read_cache,
    COALESCE(SUM(CASE WHEN counter_name = 'rows filtered by SIPs expression'  THEN counter_value END), 0) AS sip_rows_pruned,
    COALESCE(SUM(CASE WHEN counter_name = 'rows processed by SIPs expression' THEN counter_value END), 0) AS sip_rows_processed,
    COALESCE(SUM(CASE WHEN counter_name = 'rle rows produced'      THEN counter_value END), 0) AS rle_rows,
    COALESCE(SUM(CASE WHEN counter_name = 'rows produced'          THEN counter_value END), 0) AS rows_produced
FROM v_monitor.execution_engine_profiles
WHERE transaction_id = :t_id AND statement_id = :s_id;


-- ---------------------------------------------------------------------
-- 4. Per-node execution-time skew
-- ---------------------------------------------------------------------
CREATE LOCAL TEMPORARY TABLE qscard_skew ON COMMIT PRESERVE ROWS AS
WITH node_exec AS (
    SELECT node_name, SUM(counter_value) AS node_us
    FROM   v_monitor.execution_engine_profiles
    WHERE  transaction_id = :t_id AND statement_id = :s_id
      AND  counter_name   = 'execution time (us)'
    GROUP BY node_name
)
SELECT
    COUNT(*)                                          AS num_nodes,
    COALESCE(MAX(node_us), 0)                         AS max_node_us,
    COALESCE(MIN(node_us), 0)                         AS min_node_us,
    COALESCE(AVG(node_us), 0)                         AS avg_node_us,
    COALESCE(STDDEV_POP(node_us), 0)                  AS stddev_node_us,
    CASE WHEN COALESCE(AVG(node_us),0) > 0
         THEN COALESCE(STDDEV_POP(node_us),0) / AVG(node_us)
         ELSE 0 END                                   AS cv_node_us
FROM node_exec;


-- ---------------------------------------------------------------------
-- 5. Resource acquisitions (queue wait, peak memory).
--    The 'succeeded' / 'result' columns existed in Vertica <=12.x but
--    were removed in 23.3+. Memory-grant failures are detected via the
--    MEMORY_LIMIT_HIT event in qscard_events.
-- ---------------------------------------------------------------------
CREATE LOCAL TEMPORARY TABLE qscard_res ON COMMIT PRESERVE ROWS AS
SELECT
    COALESCE(MAX(EXTRACT(EPOCH FROM (acquisition_timestamp - queue_entry_timestamp))), 0) AS max_queue_wait_s,
    COALESCE(MAX(memory_inuse_kb), 0)                 AS max_mem_kb
FROM v_monitor.resource_acquisitions
WHERE transaction_id = :t_id AND statement_id = :s_id;


-- ---------------------------------------------------------------------
-- 6. Phase timings from dc_query_executions (seconds).
--    dc_query_executions has one row per node per phase. The SUM below
--    is CUMULATIVE across nodes, not wall-clock time, so it can exceed
--    query_duration_us. For the severity rule we gate on query_duration
--    in the final SELECT so short queries are not flagged spuriously.
-- ---------------------------------------------------------------------
CREATE LOCAL TEMPORARY TABLE qscard_phase ON COMMIT PRESERVE ROWS AS
SELECT
    COALESCE(SUM(CASE WHEN execution_step =  'ExecutePlan'
                      THEN EXTRACT(EPOCH FROM (completion_time - time))
                      ELSE 0 END), 0) AS exec_phase_s,
    COALESCE(SUM(CASE WHEN execution_step <> 'ExecutePlan'
                      THEN EXTRACT(EPOCH FROM (completion_time - time))
                      ELSE 0 END), 0) AS other_phase_s
FROM v_internal.dc_query_executions
WHERE transaction_id = :t_id AND statement_id = :s_id;


-- ---------------------------------------------------------------------
-- 7. Query duration
-- ---------------------------------------------------------------------
CREATE LOCAL TEMPORARY TABLE qscard_dur ON COMMIT PRESERVE ROWS AS
SELECT COALESCE(MAX(query_duration_us), 0) AS query_duration_us
FROM   v_monitor.query_profiles
WHERE  transaction_id = :t_id AND statement_id = :s_id;


-- ---------------------------------------------------------------------
-- 8. Projection health for the projections this query used
-- ---------------------------------------------------------------------
CREATE LOCAL TEMPORARY TABLE qscard_proj ON COMMIT PRESERVE ROWS AS
SELECT
    COUNT(DISTINCT pj.projection_id)                                                 AS total_proj_cnt,
    COUNT(DISTINCT CASE WHEN NOT pj.has_statistics THEN pj.projection_id END)        AS no_stats_cnt,
    COUNT(DISTINCT CASE WHEN NOT pj.is_up_to_date  THEN pj.projection_id END)        AS stale_proj_cnt
FROM   v_monitor.projection_usage p
JOIN   v_catalog.projections      pj ON pj.projection_id = p.projection_id
WHERE  p.transaction_id = :t_id AND p.statement_id = :s_id;


-- =====================================================================
-- Final scorecard.
-- Each UNION ALL row reads from 1-row temp tables only.
-- =====================================================================
SELECT display_order, category, check_name, severity, score, details, suggested_action
FROM (
    -- ---- PREAMBLE ------------------------------------------------------
    -- Warn loudly if runtime counters are missing for this (trx, stmt).
    SELECT 1 AS display_order, 'INFO' AS category, 'Runtime counters available' AS check_name,
           CASE WHEN eep_row_cnt > 0 THEN 'OK' ELSE 'HIGH' END AS severity,
           CASE WHEN eep_row_cnt > 0 THEN 'yes' ELSE 'no' END  AS score,
           'Whether EXECUTION_ENGINE_PROFILES retained counters for this (trx, stmt). If "no", all runtime checks (spill, stalls, skew, CPU wait, bytes sent) will read 0 and are NOT meaningful.' AS details,
           CASE WHEN eep_row_cnt = 0
                THEN 'Re-run the query with PROFILE <sql>, or enable profiling at session level: SELECT ENABLE_PROFILING(''EE'');'
                ELSE '' END AS suggested_action
    FROM qscard_eep

    UNION ALL SELECT 10, 'INFO', 'Query duration (s)',
           'INFO',
           (ROUND(query_duration_us/1000000.0, 3))::NUMERIC(18,3)::VARCHAR,
           'Total wall-clock duration reported by QUERY_PROFILES', ''
    FROM qscard_dur

    UNION ALL SELECT 11, 'INFO', 'Nodes participating',
           'INFO', num_nodes::VARCHAR,
           'Number of nodes that produced execution counters', ''
    FROM qscard_skew

    -- ---- JOINS ---------------------------------------------------------
    UNION ALL SELECT 20, 'JOIN', 'Hash joins',
           CASE WHEN hash_join_cnt = 0 THEN 'OK'
                WHEN hash_join_cnt <= 2 THEN 'LOW'
                WHEN hash_join_cnt <= 5 THEN 'MEDIUM'
                ELSE 'HIGH' END,
           hash_join_cnt::VARCHAR,
           'JOIN HASH operators in the plan. Hash joins load the inner side into memory and can spill or fail if it does not fit.',
           CASE WHEN hash_join_cnt > 0
                THEN 'Pre-sort both inputs on the join key (ORDER BY) so Vertica picks MERGEJOIN, or force it with hints: SELECT /*+SYNTACTIC_JOIN*/ ... JOIN /*+JTYPE(FM)*/ .... Ensure join columns have identical data types.'
                ELSE '' END
    FROM qscard_plan

    UNION ALL SELECT 21, 'JOIN', 'Merge joins',
           CASE WHEN merge_join_cnt > 0 THEN 'OK' ELSE 'INFO' END,
           merge_join_cnt::VARCHAR,
           'JOIN MERGEJOIN operators. Preferred - less memory, generally faster, no fit-in-RAM risk.',
           ''
    FROM qscard_plan

    UNION ALL SELECT 22, 'JOIN', 'Join spilled to disk',
           CASE WHEN join_spill_cnt = 0 THEN 'OK' ELSE 'HIGH' END,
           join_spill_cnt::VARCHAR,
           'JOIN_SPILLED events: inner did not fit in memory, fell back to external sort-merge.',
           CASE WHEN join_spill_cnt > 0
                THEN 'Increase query memory (resource pool MAXQUERYMEMORYSIZE / MEMORYSIZE), reduce the inner side (predicates, projection), or convert to MERGEJOIN on pre-sorted inputs.'
                ELSE '' END
    FROM qscard_events

    -- ---- GROUP BY ------------------------------------------------------
    UNION ALL SELECT 30, 'GROUPBY', 'GroupBy Hash',
           CASE WHEN gby_hash_cnt = 0 THEN 'OK'
                WHEN gby_hash_cnt = 1 THEN 'LOW'
                WHEN gby_hash_cnt <= 3 THEN 'MEDIUM'
                ELSE 'HIGH' END,
           gby_hash_cnt::VARCHAR,
           'GROUPBY HASH operators - hold all groups in memory, can spill.',
           CASE WHEN gby_hash_cnt > 0
                THEN 'If group-by columns are a prefix of a projection ORDER BY, Vertica can use GROUPBY PIPELINED (less memory, faster). Add /*+GBYTYPE(PIPE)*/ hint after tuning the projection sort order.'
                ELSE '' END
    FROM qscard_plan

    UNION ALL SELECT 31, 'GROUPBY', 'GroupBy Pipelined',
           CASE WHEN gby_pipe_cnt > 0 THEN 'OK' ELSE 'INFO' END,
           gby_pipe_cnt::VARCHAR,
           'GROUPBY PIPELINED operators. Uses sorted input, cheap memory.',
           ''
    FROM qscard_plan

    UNION ALL SELECT 32, 'GROUPBY', 'GroupBy spilled to disk',
           CASE WHEN gby_spill_cnt = 0 THEN 'OK' ELSE 'HIGH' END,
           gby_spill_cnt::VARCHAR,
           'GROUP_BY_SPILLED events: aggregation hash table did not fit in memory.',
           CASE WHEN gby_spill_cnt > 0
                THEN 'Consider a projection sorted on the GROUP BY columns (enables PIPELINED), or increase available query memory. Reducing planned concurrency on the pool also raises per-query budget.'
                ELSE '' END
    FROM qscard_events

    -- ---- NETWORK / DISTRIBUTION ---------------------------------------
    UNION ALL SELECT 40, 'NETWORK', 'Broadcast operations',
           CASE WHEN broadcast_cnt = 0 THEN 'OK'
                WHEN broadcast_cnt = 1 THEN 'LOW'
                WHEN broadcast_cnt <= 3 THEN 'MEDIUM'
                ELSE 'HIGH' END,
           broadcast_cnt::VARCHAR,
           'Paths that broadcast a full copy of an intermediate result to every node.',
           CASE WHEN broadcast_cnt > 0
                THEN 'Unsegment (replicate) small dimension tables < 1M rows; segment fact tables on the join key so broadcast is not needed.'
                ELSE '' END
    FROM qscard_plan

    UNION ALL SELECT 41, 'NETWORK', 'Global resegment groups',
           CASE WHEN global_reseg_cnt = 0 THEN 'OK'
                WHEN global_reseg_cnt = 1 THEN 'MEDIUM'
                ELSE 'HIGH' END,
           global_reseg_cnt::VARCHAR,
           'GLOBAL RESEGMENT GROUPS in the plan: Vertica must re-shuffle rows across the cluster before the GROUP BY / JOIN.',
           CASE WHEN global_reseg_cnt > 0
                THEN 'Align projection segmentation with the GROUP BY / JOIN keys. Ensure GROUP BY contains all segmentation columns of the projection.'
                ELSE '' END
    FROM qscard_plan

    UNION ALL SELECT 42, 'NETWORK', 'Resegmented many rows (event)',
           CASE WHEN reseg_many_cnt = 0 THEN 'OK' ELSE 'HIGH' END,
           reseg_many_cnt::VARCHAR,
           'RESEGMENTED_MANY_ROWS events during execution.',
           CASE WHEN reseg_many_cnt > 0 THEN 'Revisit projection segmentation on the tables involved.' ELSE '' END
    FROM qscard_events

    UNION ALL SELECT 43, 'NETWORK', 'Bytes sent over network (MB)',
           CASE WHEN bytes_sent = 0                       THEN 'OK'
                WHEN bytes_sent < 100*1024*1024           THEN 'LOW'
                WHEN bytes_sent < 1024*1024*1024          THEN 'MEDIUM'
                ELSE 'HIGH' END,
           (ROUND(bytes_sent/1048576.0, 2))::NUMERIC(18,2)::VARCHAR,
           'Total bytes pushed through NetworkSend operators.',
           CASE WHEN bytes_sent > 1024*1024*1024
                THEN 'Large network traffic often signals missing co-location. Segment tables on join keys, unsegment small ones.'
                ELSE '' END
    FROM qscard_eep

    -- ---- SPILL / MEMORY -----------------------------------------------
    UNION ALL SELECT 50, 'SPILL', 'Temp data spilled to disk (MB)',
           CASE WHEN spill_bytes = 0                      THEN 'OK'
                WHEN spill_bytes < 100*1024*1024          THEN 'LOW'
                WHEN spill_bytes < 1024*1024*1024         THEN 'MEDIUM'
                ELSE 'HIGH' END,
           (ROUND(spill_bytes/1048576.0, 2))::NUMERIC(18,2)::VARCHAR,
           'Sum of "cumulative size of raw temp data (bytes)" across operators. Non-zero means at least one operator spilled.',
           CASE WHEN spill_bytes > 0
                THEN 'Increase query memory budget (resource pool tuning), pre-sort inputs to avoid HASH operators, or reduce intermediate cardinality.'
                ELSE '' END
    FROM qscard_eep

    UNION ALL SELECT 52, 'MEMORY', 'Optimizer memory limit hit',
           CASE WHEN mem_limit_cnt = 0 THEN 'OK' ELSE 'HIGH' END,
           mem_limit_cnt::VARCHAR,
           'MEMORY_LIMIT_HIT events: the optimizer exhausted its planning memory (default 100 MB).',
           CASE WHEN mem_limit_cnt > 0
                THEN 'Drop unused projections, simplify the query, or raise config parameter MaxOptMemMB.'
                ELSE '' END
    FROM qscard_events

    UNION ALL SELECT 53, 'MEMORY', 'Max memory used by query (MB)',
           'INFO',
           (ROUND(max_mem_kb/1024.0, 2))::NUMERIC(18,2)::VARCHAR,
           'Largest memory_inuse value observed in resource_acquisitions for this statement.',
           ''
    FROM qscard_res

    -- ---- RESOURCE POOL / QUEUE ----------------------------------------
    UNION ALL SELECT 60, 'RESOURCES', 'Queue wait for resources (s)',
           CASE WHEN max_queue_wait_s < 1   THEN 'OK'
                WHEN max_queue_wait_s < 5   THEN 'LOW'
                WHEN max_queue_wait_s < 30  THEN 'MEDIUM'
                ELSE 'HIGH' END,
           (ROUND(max_queue_wait_s::NUMERIC, 3))::NUMERIC(18,3)::VARCHAR,
           'Longest gap between queue_entry_timestamp and acquisition_timestamp across nodes.',
           CASE WHEN max_queue_wait_s >= 1
                THEN 'Pool is saturated. Raise MAXCONCURRENCY / PLANNEDCONCURRENCY, raise MAXMEMORYSIZE, or offload this workload to a cascaded/secondary pool.'
                ELSE '' END
    FROM qscard_res

    -- ---- STATISTICS ---------------------------------------------------
    UNION ALL SELECT 70, 'STATS', 'Missing histogram (NO_HISTOGRAM)',
           CASE WHEN no_hist_cnt = 0 THEN 'OK'
                WHEN no_hist_cnt <= 2 THEN 'MEDIUM'
                ELSE 'HIGH' END,
           no_hist_cnt::VARCHAR,
           'Optimizer encountered predicates on columns with no statistics.',
           CASE WHEN no_hist_cnt > 0
                THEN 'Run ANALYZE_STATISTICS (or ANALYZE_HISTOGRAM with a larger sample %) on the affected tables/columns.'
                ELSE '' END
    FROM qscard_events

    UNION ALL SELECT 71, 'STATS', 'Predicate outside histogram',
           CASE WHEN pred_out_hist_cnt = 0 THEN 'OK' ELSE 'MEDIUM' END,
           pred_out_hist_cnt::VARCHAR,
           'Predicate value fell outside the histogram range - cardinality estimate is guessed.',
           CASE WHEN pred_out_hist_cnt > 0 THEN 'Refresh statistics so the histogram covers the predicate range.' ELSE '' END
    FROM qscard_events

    UNION ALL SELECT 72, 'STATS', 'Used projections missing stats',
           CASE WHEN no_stats_cnt = 0 THEN 'OK' ELSE 'HIGH' END,
           no_stats_cnt::VARCHAR,
           'Projections accessed by this query whose has_statistics is FALSE.',
           CASE WHEN no_stats_cnt > 0 THEN 'SELECT ANALYZE_STATISTICS(''schema.table''); on the anchor tables.' ELSE '' END
    FROM qscard_proj

    UNION ALL SELECT 73, 'STATS', 'Used projections not up-to-date',
           CASE WHEN stale_proj_cnt = 0 THEN 'OK' ELSE 'HIGH' END,
           stale_proj_cnt::VARCHAR,
           'Projections accessed whose is_up_to_date is FALSE - the projection still needs a refresh.',
           CASE WHEN stale_proj_cnt > 0 THEN 'SELECT START_REFRESH(); then verify with v_monitor.projection_refreshes.' ELSE '' END
    FROM qscard_proj

    -- ---- CPU / STALLS / SKEW ------------------------------------------
    UNION ALL SELECT 80, 'CPU', 'CPU wait (clock - exec time, %)',
           CASE WHEN exec_time_us = 0                           THEN 'INFO'
                WHEN clock_time_us <= exec_time_us              THEN 'OK'
                WHEN clock_time_us  < exec_time_us * 1.2        THEN 'LOW'
                WHEN clock_time_us  < exec_time_us * 2.0        THEN 'MEDIUM'
                ELSE 'HIGH' END,
           CASE WHEN exec_time_us = 0 THEN '0.0'
                ELSE (ROUND(((clock_time_us - exec_time_us)::NUMERIC / NULLIF(exec_time_us,0)) * 100, 1))::NUMERIC(18,1)::VARCHAR
           END,
           'Ratio (clock_time - execution_time) / execution_time, as percent. High = CPU starvation or waiting on other operators.',
           CASE WHEN clock_time_us > exec_time_us * 2 AND exec_time_us > 0
                THEN 'Reduce concurrency on the pool, lower EXECUTIONPARALLELISM, or move this query to a pool with higher RUNTIMEPRIORITY.'
                ELSE '' END
    FROM qscard_eep

    UNION ALL SELECT 81, 'CPU', 'Consumer stall (ms)',
           CASE WHEN cons_stall_us = 0             THEN 'OK'
                WHEN cons_stall_us < 1000000       THEN 'LOW'
                WHEN cons_stall_us < 10000000      THEN 'MEDIUM'
                ELSE 'HIGH' END,
           (ROUND(cons_stall_us/1000.0, 2))::NUMERIC(18,2)::VARCHAR,
           'Total time operators spent waiting for downstream (consumer) to accept data.',
           CASE WHEN cons_stall_us >= 1000000
                THEN 'Downstream operator is the bottleneck - inspect it (often a slow NetworkSend, Sort or GroupByHash).'
                ELSE '' END
    FROM qscard_eep

    UNION ALL SELECT 82, 'CPU', 'Producer stall (ms)',
           CASE WHEN prod_stall_us = 0             THEN 'OK'
                WHEN prod_stall_us < 1000000       THEN 'LOW'
                WHEN prod_stall_us < 10000000      THEN 'MEDIUM'
                ELSE 'HIGH' END,
           (ROUND(prod_stall_us/1000.0, 2))::NUMERIC(18,2)::VARCHAR,
           'Total time operators spent waiting for upstream (producer) to supply data.',
           CASE WHEN prod_stall_us >= 1000000
                THEN 'Upstream operator is slow - usually Scan or an upstream Sort/Join that needs to materialize first.'
                ELSE '' END
    FROM qscard_eep

    UNION ALL SELECT 83, 'SKEW', 'Node execution skew (CV%)',
           CASE WHEN num_nodes < 2            THEN 'INFO'
                WHEN cv_node_us < 0.10        THEN 'OK'
                WHEN cv_node_us < 0.25        THEN 'LOW'
                WHEN cv_node_us < 0.50        THEN 'MEDIUM'
                ELSE 'HIGH' END,
           (ROUND(cv_node_us * 100, 1))::NUMERIC(18,1)::VARCHAR,
           'Coefficient of variation of per-node "execution time (us)". High value = data or work is skewed to one node.',
           CASE WHEN cv_node_us >= 0.25 AND num_nodes >= 2
                THEN 'Check projection segmentation for skew; verify no single node is degraded (disk, CPU). See step 16 of qprof for row_count by node.'
                ELSE '' END
    FROM qscard_skew

    -- ---- PHASE TIMING -------------------------------------------------
    -- Severity gated on query_duration > 1 s: for sub-second queries,
    -- cumulative non-ExecutePlan time across nodes is naturally a large
    -- fraction of total and is not actionable.
    UNION ALL SELECT 90, 'PHASE', 'Non-ExecutePlan time (cumulative, s)',
           CASE WHEN qd.query_duration_us < 1000000            THEN 'INFO'
                WHEN p.exec_phase_s <= 0                       THEN 'INFO'
                WHEN p.other_phase_s <  0.1                    THEN 'OK'
                WHEN p.other_phase_s <  p.exec_phase_s*0.1     THEN 'OK'
                WHEN p.other_phase_s <  p.exec_phase_s*0.3     THEN 'MEDIUM'
                ELSE 'HIGH' END,
           (ROUND(p.other_phase_s::NUMERIC, 3))::NUMERIC(18,3)::VARCHAR,
           'Cumulative time (summed across nodes) in phases OTHER than ExecutePlan (Plan, InitPlan, CompilePlan, SerializePlan, AbandonPlan). For sub-second queries this is flagged INFO because the ratio is naturally high and not actionable.',
           CASE WHEN qd.query_duration_us >= 1000000
                  AND p.other_phase_s > p.exec_phase_s*0.3
                  AND p.exec_phase_s > 0
                THEN 'Planner overhead is high - likely catalog-lock contention (high concurrency), too many projections, or spread/UDP issues between nodes.'
                ELSE '' END
    FROM qscard_phase p CROSS JOIN qscard_dur qd

    -- ---- OTHER NEGATIVE / POSITIVE EVENTS -----------------------------
    UNION ALL SELECT 100, 'EVENT', 'WOS spill',
           CASE WHEN wos_spill_cnt = 0 THEN 'OK' ELSE 'MEDIUM' END,
           wos_spill_cnt::VARCHAR,
           'WOS_SPILL: WOS filled and data was spilled to a new ROS container.',
           CASE WHEN wos_spill_cnt > 0 THEN 'Tune load batch sizes or use DIRECT loads to bypass WOS.' ELSE '' END
    FROM qscard_events

    UNION ALL SELECT 101, 'EVENT', 'Delete with non-optimized projection',
           CASE WHEN del_nonopt_cnt = 0 THEN 'OK' ELSE 'HIGH' END,
           del_nonopt_cnt::VARCHAR,
           'DELETE_WITH_NON_OPTIMIZED_PROJECTION: delete fell back to the slow path.',
           CASE WHEN del_nonopt_cnt > 0
                THEN 'Create an optimized-for-delete projection (all columns used in the delete predicate in the ORDER BY).'
                ELSE '' END
    FROM qscard_events

    UNION ALL SELECT 102, 'EVENT', 'SIPs fallback (ineffective)',
           CASE WHEN sip_fallback_cnt = 0 THEN 'OK' ELSE 'LOW' END,
           sip_fallback_cnt::VARCHAR,
           'SIP_FALLBACK: sidewise-information-passing filter was disabled at runtime because it was not pruning enough rows.',
           ''
    FROM qscard_events

    UNION ALL SELECT 103, 'EVENT', 'Partitions eliminated (positive)',
           CASE WHEN part_elim_cnt > 0 THEN 'OK' ELSE 'INFO' END,
           part_elim_cnt::VARCHAR,
           'PARTITIONS_ELIMINATED events - the optimizer pruned partitions at scan time. Good thing.',
           ''
    FROM qscard_events

) sc
ORDER BY
    CASE severity
        WHEN 'HIGH'   THEN 1
        WHEN 'MEDIUM' THEN 2
        WHEN 'LOW'    THEN 3
        WHEN 'OK'     THEN 4
        WHEN 'INFO'   THEN 5
        ELSE 6
    END,
    display_order
;


-- ---------------------------------------------------------------------
-- Cleanup (optional). LOCAL TEMP tables disappear when the session ends
-- anyway, but dropping them keeps v_temp_schema tidy for the next run.
-- ---------------------------------------------------------------------
DROP TABLE IF EXISTS v_temp_schema.qscard_plan_raw CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_plan    CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_events  CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_eep     CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_skew    CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_res     CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_phase   CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_dur     CASCADE;
DROP TABLE IF EXISTS v_temp_schema.qscard_proj    CASCADE;
"""



def _split_sql_statements(text):
    """Split a SQL script into individual statements, respecting:
       - single-quoted string literals (with SQL '' escape)
       - double-quoted identifiers
       - -- line comments through end-of-line
       - /* ... */ block comments (including nested /* */ on their own lines)

    The v82 initial pass didn't know about -- comments; vertica_query_scorecard.sql
    has `Don't` in its header comment and `';'` earlier, which flipped the
    single-quote state at the wrong moment and swallowed ~90% of the file
    into one giant "string". Comment-aware state machine fixes that.
    """
    statements = []
    buf = []
    in_squote = False        # inside a single-quoted string literal
    in_dquote = False        # inside a double-quoted identifier
    in_line_comment = False  # -- ... \n
    in_block_comment = False # /* ... */
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        nxt = text[i+1] if i + 1 < n else ''
        # Inside -- line comment: consume until newline. Apostrophes inside
        # the comment MUST NOT toggle string state.
        if in_line_comment:
            buf.append(ch)
            if ch == '\n':
                in_line_comment = False
            i += 1
            continue
        # Inside /* */ block comment: consume until closing */.
        if in_block_comment:
            buf.append(ch)
            if ch == '*' and nxt == '/':
                buf.append('/')
                in_block_comment = False
                i += 2
                continue
            i += 1
            continue
        # Outside any quoted string / identifier: comment openers win.
        if not in_squote and not in_dquote:
            if ch == '-' and nxt == '-':
                in_line_comment = True
                buf.append('--')
                i += 2
                continue
            if ch == '/' and nxt == '*':
                in_block_comment = True
                buf.append('/*')
                i += 2
                continue
        # Single-quoted string literal toggle (handle SQL '' escape inside).
        if ch == "'" and not in_dquote:
            if in_squote and nxt == "'":
                buf.append("''")
                i += 2
                continue
            in_squote = not in_squote
            buf.append(ch)
            i += 1
            continue
        # Double-quoted identifier toggle.
        if ch == '"' and not in_squote:
            in_dquote = not in_dquote
            buf.append(ch)
            i += 1
            continue
        # Statement terminator.
        if ch == ';' and not in_squote and not in_dquote:
            stmt = ''.join(buf).strip()
            if stmt:
                statements.append(stmt)
            buf = []
            i += 1
            continue
        buf.append(ch)
        i += 1
    tail = ''.join(buf).strip()
    if tail:
        statements.append(tail)
    return statements


def _rewrite_named_params(stmt):
    """Convert vsql-style :t_id / :s_id placeholders to vertica_python %s
    positional placeholders. Returns (rewritten_sql, param_order). The
    param_order is a list of 't_id' / 's_id' tokens matching the order of
    the %s placeholders in the rewritten SQL. Caller provides the values
    in that order to cursor.execute(stmt, params).

    Comment-aware: :t_id / :s_id inside -- line comments or /* */ block
    comments are left alone and NOT counted, because the scorecard SQL's
    header comment shows `\\set t_id 45035996274879950` as usage documentation
    and that would otherwise be rewritten into bogus %s placeholders.
    """
    order = []
    out = []
    i = 0
    n = len(stmt)
    while i < n:
        ch = stmt[i]
        nxt = stmt[i+1] if i + 1 < n else ''
        # -- line comment: passthrough until newline.
        if ch == '-' and nxt == '-':
            while i < n and stmt[i] != '\n':
                out.append(stmt[i])
                i += 1
            continue
        # /* */ block comment: passthrough until closing */.
        if ch == '/' and nxt == '*':
            out.append('/*')
            i += 2
            while i < n:
                if stmt[i] == '*' and i + 1 < n and stmt[i+1] == '/':
                    out.append('*/')
                    i += 2
                    break
                out.append(stmt[i])
                i += 1
            continue
        # Single-quoted string literal: passthrough whole literal.
        if ch == "'":
            out.append(ch)
            i += 1
            while i < n:
                c2 = stmt[i]
                out.append(c2)
                if c2 == "'":
                    if i + 1 < n and stmt[i+1] == "'":
                        out.append("'")
                        i += 2
                        continue
                    i += 1
                    break
                i += 1
            continue
        # Placeholder rewrites (word-boundary safe: next char after :t_id
        # must not be another identifier character, to avoid eating :t_id_x).
        if ch == ':' and stmt[i:i+5] == ':t_id':
            after = stmt[i+5] if i + 5 < n else ''
            if not (after.isalnum() or after == '_'):
                out.append('%s')
                order.append('t_id')
                i += 5
                continue
        if ch == ':' and stmt[i:i+5] == ':s_id':
            after = stmt[i+5] if i + 5 < n else ''
            if not (after.isalnum() or after == '_'):
                out.append('%s')
                order.append('s_id')
                i += 5
                continue
        out.append(ch)
        i += 1
    return (''.join(out), order)


def _run_scorecard(cursor, transaction_id, statement_id):
    """Execute the full vertica_query_scorecard.sql against an already-open
    vertica_python cursor (one session, one connection - required by the
    LOCAL TEMPORARY table design). Returns a list of dicts, one per
    scorecard row, already sorted by the SQL's own ORDER BY (severity
    bucket then display_order).

    Each dict has: display_order, category, check_name, severity, score,
    details, suggested_action. The schema mirrors the final SELECT in the
    SQL file.
    """
    statements = _split_sql_statements(_SCORECARD_QUERY_SQL)
    rows_out = []
    param_map = {'t_id': int(transaction_id), 's_id': int(statement_id)}
    # The scorecard SQL has exactly ONE statement that returns rows (the
    # big UNION-ALL SELECT near the end). Every other statement is a
    # DDL (DROP or CREATE LOCAL TEMPORARY TABLE ... AS SELECT) whose
    # cursor.description stays None after execute. We collect rows from
    # the statement(s) that DO return a description. If multiple return
    # rows we concatenate in order (the SQL is authored so only one does).
    for stmt in statements:
        rewritten, order = _rewrite_named_params(stmt)
        params = tuple(param_map[k] for k in order)
        try:
            if params:
                cursor.execute(rewritten, params)
            else:
                cursor.execute(rewritten)
        except Exception as e:
            raise RuntimeError(
                'Scorecard SQL failed on statement beginning "' +
                stmt.splitlines()[0][:80].strip() + '": ' + str(e)
            )
        desc = getattr(cursor, 'description', None)
        if desc:
            cols = [d[0] for d in desc]
            for row in cursor.fetchall():
                rows_out.append({cols[i]: row[i] for i in range(len(cols))})
    return rows_out


def _scorecard_summary(rows):
    """Roll up severity counts for the dashboard hero. Severity buckets
    match the scorecard SQL: HIGH / MEDIUM / LOW / OK / INFO. The "score"
    the dashboard displays is a simple 0-100 grade:
        start at 100, subtract 10 per HIGH, 5 per MEDIUM, 2 per LOW.
        (OK and INFO are neutral.)
    This is a heuristic, intentionally crude - a query with 1 HIGH finding
    still scores 90, which is "needs attention but not dire". We spell out
    the math in the UI so the user sees exactly what went into the grade.
    """
    counts = {'HIGH': 0, 'MEDIUM': 0, 'LOW': 0, 'OK': 0, 'INFO': 0}
    for r in rows:
        sev = str(r.get('severity') or '').upper()
        if sev in counts:
            counts[sev] += 1
    score = 100 - (counts['HIGH'] * 10) - (counts['MEDIUM'] * 5) - (counts['LOW'] * 2)
    score = max(0, score)
    return {
        'counts': counts,
        'score': score,
        'total_rows': len(rows),
    }



# v68 (F-STEP03B-SKEW-01): find the one execution step with the largest
# cross-node skew (the "slowest-node minus fastest-node" delta). Used by
# _build_tree_analysis to emit a finding when that skew is material.
# dc_query_executions is cluster-wide (unlike execution_engine_profiles),
# so this always returns something as long as the query actually ran.
def _measure_step_skew(cursor, transaction_id: int, statement_id: int) -> Dict[str, Any]:
    """Return the step with the highest cross-node skew for this
    transaction/statement. Keys:
      - step:          step name (e.g. 'ExecutePlan:EEexecute')
      - skew_ms:       max - min time across nodes, in ms
      - slowest_node:  node that started last on that step
      - fastest_node:  node that started first on that step
      - skew_rows:     v76 NEW - full ranked list of every step with
                       non-zero skew, each row: {step, skew_ms,
                       slowest_node, fastest_node, first_start,
                       last_start, node_times: [{node, time_ms_offset}, ...]}.
                       Ordered by skew_ms DESC. Used by the new /skew/<id>
                       page to show skew across ALL steps, not just the
                       top one.
    Returns an empty dict if no step had non-zero skew or on error."""
    try:
        # v76 post-ship fix #2 (Maya's screenshot: page said "No distributed
        # steps recorded" on a query whose reference test clearly showed 10
        # steps with skew 5-10 ms each). Root cause: the previous version
        # used correlated scalar subqueries with LIMIT 1 inside the SELECT
        # list to pick slowest/fastest node names. Vertica supports that
        # pattern inconsistently - on this version the outer query returned
        # zero rows silently, was caught by the except clause, and the page
        # rendered the "no rows" branch.
        #
        # Fix: match Maya's reference query shape (INNER JOIN + GROUP BY +
        # MAX(CASE WHEN ...)) from skew_query_test.txt. Single SQL pass.
        # MAX(CASE) correctly picks the slowest-node / fastest-node NAME
        # for each step by comparing qe."time" to ps.last_t / ps.first_t.
        # When two nodes share the exact same timestamp (rare at microsecond
        # precision) the alphabetically-last node wins - deterministic.
        #
        # Filter:
        #   HAVING COUNT(DISTINCT node_name) > 1 - keep every step that
        #   actually ran on more than one node, even when its measured skew
        #   is 0 (so the chart never renders empty). Non-distributed steps
        #   (BeforePlan / Plan / InitPlan / SerializePlan / PreparePlan /
        #   CompilePlan / ExecutePlan / ReserveResourceSpotQueue / AbandonPlan
        #   - initiator-only) are still excluded.
        cursor.execute(_SKEW_QUERY_SQL, [transaction_id, statement_id,
              transaction_id, statement_id])
        rows = cursor.fetchall() or []
        if not rows:
            return {}

        skew_rows: List[Dict[str, Any]] = []
        for r in rows:
            skew_rows.append({
                'step':         str(r[0] or ''),
                'skew_ms':      int(r[1] or 0),
                'slowest_node': str(r[2] or ''),
                'fastest_node': str(r[3] or ''),
                # Keep the raw timestamps as strings - the frontend just
                # needs them for the tooltip and doesn't do math on them.
                'first_start':  str(r[4]) if r[4] is not None else '',
                'last_start':   str(r[5]) if r[5] is not None else '',
            })

        # Pass 2: per-step, per-node offsets in ms from the step's first
        # start. This is the data the mobile chart uses for its tooltip
        # "node timeline" micro-breakdown. We issue ONE query for all
        # rows - indexed by (step, node) in Python - to avoid N+1.
        # Only bother if we have skew rows to enrich.
        step_names = [s['step'] for s in skew_rows]
        node_times_by_step: Dict[str, List[Dict[str, Any]]] = {}
        if step_names:
            try:
                # v78 (Maya item #3: duplicate node names in popup).
                # dc_query_executions can record MULTIPLE rows for the
                # same (execution_step, node_name) pair when Vertica re-
                # enters a phase (planning/compilation retries, two-pass
                # execute-plan, etc). The v77 enrichment query returned
                # every raw row, so the popup showed e.g. v_eevdb_node0004
                # twice with +0 ms and +24.77 s - which is true per-row
                # but confusing per-node.
                #
                # Fix: aggregate with GROUP BY (step, node) and return
                # both the FIRST start offset (MIN) and LAST start offset
                # (MAX) plus the attempt count per node. Popup renders
                # one row per node with "+X ms" (first) and a sub-note
                # ", then +Y ms (N attempts)" when the node started more
                # than once. Skew calculation itself is unchanged - it
                # still uses MIN(time) and MAX(time) across nodes, which
                # is what the main query does.
                placeholders = ','.join(['%s'] * len(step_names))
                sql = (
                    "SELECT execution_step, node_name, "
                    "       TIMESTAMPDIFF('millisecond', "
                    "           MIN(MIN(\"time\")) OVER (PARTITION BY execution_step), "
                    "           MIN(\"time\")) AS first_offset_ms, "
                    "       TIMESTAMPDIFF('millisecond', "
                    "           MIN(MIN(\"time\")) OVER (PARTITION BY execution_step), "
                    "           MAX(\"time\")) AS last_offset_ms, "
                    "       COUNT(*) AS attempt_count "
                    "FROM v_internal.dc_query_executions "
                    "WHERE transaction_id=%s AND statement_id=%s "
                    f"  AND execution_step IN ({placeholders}) "
                    "GROUP BY execution_step, node_name"
                )
                params = [transaction_id, statement_id] + step_names
                cursor.execute(sql, params)
                for row in cursor.fetchall() or []:
                    step            = str(row[0] or '')
                    node            = str(row[1] or '')
                    first_offset_ms = int(row[2] or 0)
                    last_offset_ms  = int(row[3] or 0)
                    attempt_count   = int(row[4] or 1)
                    node_times_by_step.setdefault(step, []).append({
                        'node':              node,
                        # Back-compat: the client reads offset_ms as the
                        # primary "when did this node start this step"
                        # value. Use MIN (first attempt) so a retry that
                        # pushed the step to +24 s doesn't mask the
                        # original early start.
                        'offset_ms':         first_offset_ms,
                        'last_offset_ms':    last_offset_ms,
                        'attempt_count':     attempt_count,
                    })
                # Sort each step's node list by offset ASC (fastest first)
                # so the popup reads top-to-bottom fastest-to-slowest.
                for step in node_times_by_step:
                    node_times_by_step[step].sort(key=lambda x: (x['offset_ms'], x['node']))
            except Exception as e:
                # If the enrichment query fails we still return the
                # primary per-step ranking - the chart handles missing
                # node_times gracefully. Log at WARN so the failure is
                # visible in ops but doesn't break the user flow.
                logger.warning(
                    'skew-page: per-node offset enrichment failed for '
                    'transaction_id=%s statement_id=%s: %s: %s',
                    transaction_id, statement_id, type(e).__name__, e,
                )
                node_times_by_step = {}

        # v78 (Maya item #6): second enrichment query for the DURATION
        # toggle view. For each (step, node) pair, duration =
        # MAX(completion_time - time) - the elapsed wall-clock the node
        # actually spent in that step. Same shape as the reference query
        # Maya gave. We aggregate by MAX per (step, node) so if a node
        # entered the step more than once we keep the longest attempt.
        # Then derive per-step "slowest node by duration" (the node with
        # the biggest duration for that step) + full per-step sorted
        # list for the popup + chart.
        node_durations_by_step: Dict[str, List[Dict[str, Any]]] = {}
        if step_names:
            try:
                # v78 (Maya revision): same shape as _DURATION_QUERY_SQL -
                # DATEDIFF(millisecond, '0:00:00', completion_time - time)
                # inside a CTE, then MAX grouped per (node, step). The
                # query shown in the (i) info-chip matches what actually
                # runs on the cluster, minus the execution_step IN (...)
                # filter the runtime form needs for scoping.
                placeholders = ','.join(['%s'] * len(step_names))
                sql = (
                    "WITH list1 AS ( "
                    "    SELECT node_name, execution_step, "
                    "           DATEDIFF(millisecond, '0:00:00', completion_time - \"time\") AS elapsed "
                    "    FROM v_internal.dc_query_executions "
                    "    WHERE transaction_id=%s AND statement_id=%s "
                    f"      AND execution_step IN ({placeholders}) "
                    ") "
                    "SELECT execution_step, node_name, MAX(elapsed) AS duration_ms "
                    "FROM list1 "
                    "GROUP BY execution_step, node_name"
                )
                params = [transaction_id, statement_id] + step_names
                cursor.execute(sql, params)
                for row in cursor.fetchall() or []:
                    step        = str(row[0] or '')
                    node        = str(row[1] or '')
                    duration_ms = int(row[2] or 0)
                    node_durations_by_step.setdefault(step, []).append({
                        'node':        node,
                        'duration_ms': duration_ms,
                    })
                # Sort each step's node list by duration DESC (slowest first).
                for step in node_durations_by_step:
                    node_durations_by_step[step].sort(
                        key=lambda x: (-x['duration_ms'], x['node'])
                    )
            except Exception as e:
                logger.warning(
                    'skew-page: per-node duration enrichment failed for '
                    'transaction_id=%s statement_id=%s: %s: %s',
                    transaction_id, statement_id, type(e).__name__, e,
                )
                node_durations_by_step = {}

        for s in skew_rows:
            s['node_times']     = node_times_by_step.get(s['step'], [])
            # v78 item #6: each step now also carries its per-node
            # DURATION data plus the step-level max duration + the
            # node that owns it. Client toggles between Skew and
            # Duration views from this single payload.
            durations = node_durations_by_step.get(s['step'], [])
            s['node_durations'] = durations
            if durations:
                s['duration_max_ms']      = int(durations[0]['duration_ms'])
                s['duration_max_node']    = str(durations[0]['node'])
            else:
                s['duration_max_ms']      = 0
                s['duration_max_node']    = ''

        # v80 (Maya: "node0003 isn't the slowest, it's node0001"):
        # Option B - compute COMPLETION-TIME stats per step from the
        # two enrichment passes already available:
        #
        #     completion_offset_ms(node) = start_offset_ms(node) + duration_ms(node)
        #
        # The cluster doesn't finish a step until the LAST node's
        # completion_time lands, so "who held the cluster back" is the
        # node that maximises completion_offset, NOT the node that
        # started last. For the user's screenshot of ExecutePlan:EEexecute
        # (5 ms start skew, node0003 started last at +5 ms, but nodes
        # 1 and 5 both ran 56 ms vs node0003's 55 ms), completion
        # offsets work out to node0001=60ms, node0005=60ms, node0003=60ms,
        # node0002=48ms, node0004=46ms. So the TRUE slowest-to-finish
        # is a three-way tie at 60 ms, and completion skew is 14 ms -
        # well over the 5 ms that "start skew" alone reports.
        #
        # The chart still ranks by start-time skew (that's the v79
        # behavior the user wants to keep); completion data is added
        # to each row and surfaced in the popup under dedicated
        # "Last to finish" / "Completion skew" labels. The word
        # "slowest" is reserved for completion semantics from v80
        # onward - start-time fields are relabelled "last to start".
        for s in skew_rows:
            start_by_node = {nt['node']: int(nt.get('offset_ms') or 0)
                             for nt in s.get('node_times') or []}
            dur_by_node   = {nd['node']: int(nd.get('duration_ms') or 0)
                             for nd in s.get('node_durations') or []}
            # Union of nodes seen in either enrichment pass.
            nodes = set(start_by_node) | set(dur_by_node)
            completion_by_node: Dict[str, int] = {}
            for n in nodes:
                # Missing value on either side is treated as 0 so the
                # node still appears with whatever signal we do have.
                completion_by_node[n] = start_by_node.get(n, 0) + dur_by_node.get(n, 0)
            if completion_by_node:
                # Tie-breaker: when multiple nodes share the same max
                # completion offset, the "most honestly slowest" one
                # is the node that spent the most WORK in the step
                # (longest duration), not the one that started last.
                # A node that started late and ran quickly is less
                # indicative of a cluster problem than a node that
                # started on time and ran long. Final tiebreaker is
                # alphabetical (stable, predictable for users).
                def _last_key(kv):
                    # max: prefer higher completion, then longer duration,
                    # then alphabetically EARLIER node (hence reverse via
                    # negative-ord tuple below; we pick the (name,) that
                    # compares SMALLER after inverting the first two).
                    n, comp = kv
                    return (comp, dur_by_node.get(n, 0), tuple(-ord(c) for c in n))
                def _first_key(kv):
                    n, comp = kv
                    return (comp, -dur_by_node.get(n, 0), n)
                last_node, last_ms = max(completion_by_node.items(), key=_last_key)
                first_node, first_ms = min(completion_by_node.items(), key=_first_key)
                s['completion_offsets'] = [
                    {'node': n, 'completion_ms': completion_by_node[n]}
                    for n in sorted(completion_by_node, key=lambda n: (-completion_by_node[n], n))
                ]
                s['completion_skew_ms']     = int(last_ms - first_ms)
                s['last_to_finish_node']    = str(last_node)
                s['last_to_finish_ms']      = int(last_ms)
                s['first_to_finish_node']   = str(first_node)
                s['first_to_finish_ms']     = int(first_ms)
            else:
                s['completion_offsets']     = []
                s['completion_skew_ms']     = 0
                s['last_to_finish_node']    = ''
                s['last_to_finish_ms']      = 0
                s['first_to_finish_node']   = ''
                s['first_to_finish_ms']     = 0

        # First row is the top-skew step; carry its scalar fields for
        # back-compat with _build_tree_analysis and the existing
        # findings that read step / skew_ms / slowest_node / fastest_node
        # directly.
        top = skew_rows[0]
        return {
            'step':         top['step'],
            'skew_ms':      top['skew_ms'],
            'slowest_node': top['slowest_node'],
            'fastest_node': top['fastest_node'],
            'skew_rows':    skew_rows,
        }
    except Exception as e:
        # v76 post-ship fix #2: log the exception at WARN level instead
        # of swallowing it silently. Previous versions returned {} on
        # failure without leaving any trace, which is how the correlated-
        # subquery SQL bug went undetected until Maya compared the UI
        # against her reference-query output. A WARN log line lets future
        # regressions show up in normal operations without interrupting
        # the user's flow (skew data is supplementary; the main Profile
        # tab keeps working).
        logger.warning(
            'skew-page: _measure_step_skew failed for '
            'transaction_id=%s statement_id=%s: %s: %s',
            transaction_id, statement_id, type(e).__name__, e,
        )
        return {}


# v76: thresholds that decide whether the Profile tab shows the
# "Open Skew Between Nodes" link. Pulled out as module-level
# constants so Maya can retune without editing the function body.
#
# Rule (both must be true):
#   top_skew_ms >= MEANINGFUL_SKEW_MS_FLOOR
#     - absolute floor, filters "1ms / 14ms" noise on planning-phase
#       steps that are always tiny. Anchored at 50 ms because that's
#       the boundary below which a user cannot reliably correlate
#       a graph bar with anything actionable.
#   AND top_skew_ms / query_duration_ms >= MEANINGFUL_SKEW_FRACTION
#     - relative floor: on a 100ms query a 50ms skew would dominate,
#       but the same 50ms on a 25s query is half a percent and not
#       worth highlighting. 0.05 = "skew has to be at least 5% of
#       total wall-clock to earn a link".
#
# Both thresholds were tuned against the reference dataset at
# test_results_to_get_info_from_Vertica_system_tables.txt:
#   - the 25s query has top skew 24787 ms (99% of duration) -> LINK SHOWN
#   - the VMart 09 query has max skew ~1 ms (<5%)            -> HIDDEN
MEANINGFUL_SKEW_MS_FLOOR = 50
MEANINGFUL_SKEW_FRACTION = 0.05


def _skew_is_meaningful(step_skew: Dict[str, Any], query_duration_us: int) -> bool:
    """Return True iff the skew data has at least one step whose skew
    is both absolutely large enough to act on (MEANINGFUL_SKEW_MS_FLOOR)
    AND relatively large enough to matter (MEANINGFUL_SKEW_FRACTION of
    the whole-query wall-clock). Used by the client to decide whether
    to render the skew-page link at all - matches Maya's spec 'Only if
    you find for the given profiled query a meaningful skew between
    nodes, then add a link'."""
    if not step_skew:
        return False
    top_ms = int(step_skew.get('skew_ms') or 0)
    if top_ms < MEANINGFUL_SKEW_MS_FLOOR:
        return False
    if query_duration_us and query_duration_us > 0:
        fraction = (top_ms * 1000.0) / float(query_duration_us)
        if fraction < MEANINGFUL_SKEW_FRACTION:
            return False
    return True


# v79 (Maya general feedback): detect Vertica privilege / permission
# errors so the client can show a tailored popup explaining the dbadmin
# role delegation path (GRANT dbadmin TO regular_user + SET ROLE
# dbadmin; the exact workflow shown in Maya's screenshot).
#
# vertica_python doesn't expose a dedicated exception class per SQLSTATE,
# but the generic QueryError carries sqlstate='42501' on privilege
# violations and sqlstate='42000' on some related "not authorised"
# paths. The server-side error message typically contains phrases like
# "permission denied for", "insufficient privilege", or "must be
# superuser". We match on both channels because different Vertica
# versions / catalog tables surface slightly different strings.
_PRIVILEGE_SQLSTATES = {'42501', '42000'}
_PRIVILEGE_PHRASES = (
    'permission denied',
    'insufficient privilege',
    'must be superuser',
    'not authorized',
    'not authorised',
    'access denied',
    'privilege to',
)


def _is_privilege_error(exc: BaseException) -> bool:
    """Return True if `exc` looks like a Vertica privilege / permission
    error. Checks both SQLSTATE (when available on the exception
    object) and the textual message. Never raises."""
    try:
        sqlstate = getattr(exc, 'sqlstate', None)
        if sqlstate and str(sqlstate).strip() in _PRIVILEGE_SQLSTATES:
            return True
        msg = str(exc).lower()
        for phrase in _PRIVILEGE_PHRASES:
            if phrase in msg:
                return True
    except Exception:
        pass
    return False


# v71 (F-RESOURCE-POOL-01): which resource pool did this query run in?
# resource_acquisitions.pool_name is cluster-wide and always complete,
# so this is a safe read. Used by _build_tree_analysis to fire the new
# resource-pool finding when the query ran in the default `general` pool
# (a signal to consider a tuned pool for production workloads).
def _measure_resource_pool(cursor, transaction_id: int, statement_id: int) -> Dict[str, Any]:
    """Return {'pool_name': str} or {} on error. If multiple nodes report
    different pools (rare but possible during policy changes), return the
    most common one."""
    try:
        cursor.execute("""
            SELECT pool_name, COUNT(*) AS n
            FROM v_monitor.resource_acquisitions
            WHERE transaction_id=%s AND statement_id=%s
              AND pool_name IS NOT NULL
            GROUP BY 1
            ORDER BY 2 DESC
            LIMIT 1
        """, [transaction_id, statement_id])
        row = cursor.fetchone()
        if not row:
            return {}
        return {'pool_name': str(row[0] or '').strip()}
    except Exception:
        return {}


# v71.5.2 (F-PEAK-MEMORY-01): cluster-wide peak memory in use for the query,
# sourced from v_monitor.resource_acquisitions.memory_inuse_kb. Maya's
# feedback on the VMart run pointed out that per-path memory columns
# (query_plan_profiles.memory_allocated_bytes, EEP 'memory reserved (bytes)',
# EEP 'memory allocated (bytes)', dc_plan_resources.assigned_memory_bytes)
# were all NULL for that query shape -- so every graph card and the hero
# stats showed zero memory even though the query actually held ~2.85 GB
# per node. resource_acquisitions IS populated (qprof.sh Step 04 is the
# reference) and captures what the pool actually granted the query.
# Peak = MAX across nodes so it reflects the worst-case per-node footprint
# rather than a sum (sum is misleading when all nodes held the same mem).
def _measure_peak_memory(cursor, transaction_id: int, statement_id: int) -> Dict[str, Any]:
    """Return {'peak_memory_kb': int, 'peak_memory_mb': float, 'per_node': [...]}
    or {} on error. per_node = [{'node_name': ..., 'memory_kb': ...}, ...]
    sorted by memory_kb DESC for easy display.

    v71.5.3 (Maya's "did you check elsewhere too?" challenge, round 2):
      She uploaded a test_results file showing that v_monitor.query_requests
      has a column memory_acquired_mb (value 2850.25 on her VMart run) -
      a cluster-wide, already-in-MB, single-row source I had not used. Use
      it as the primary source; resource_acquisitions supplies the per-node
      breakdown for the tooltip. If query_requests.memory_acquired_mb is
      missing (old Vertica versions don't have this column), fall back to
      MAX(memory_inuse_kb) across resource_acquisitions nodes.
    """
    peak_kb = 0
    per_node: List[Dict[str, Any]] = []
    # --- Primary: query_requests.memory_acquired_mb (F-PEAK-MEMORY-01) ---
    try:
        cursor.execute("""
            SELECT memory_acquired_mb
            FROM v_monitor.query_requests
            WHERE transaction_id=%s AND statement_id=%s
              AND memory_acquired_mb IS NOT NULL
            LIMIT 1
        """, [transaction_id, statement_id])
        row = cursor.fetchone()
        if row and row[0] is not None:
            mb = float(row[0])
            peak_kb = int(round(mb * 1024))
    except Exception:
        # Column may not exist on older Vertica - fall through to fallback.
        pass
    # --- Secondary / per-node breakdown: resource_acquisitions ---
    try:
        cursor.execute("""
            SELECT node_name, memory_inuse_kb
            FROM v_monitor.resource_acquisitions
            WHERE transaction_id=%s AND statement_id=%s
              AND memory_inuse_kb IS NOT NULL
            ORDER BY memory_inuse_kb DESC
        """, [transaction_id, statement_id])
        rows = cursor.fetchall() or []
        per_node = [{'node_name': str(r[0] or '?'), 'memory_kb': int(r[1] or 0)}
                    for r in rows]
        # Fallback: if query_requests had no value, use MAX(memory_inuse_kb).
        if peak_kb == 0 and per_node:
            peak_kb = max((pn['memory_kb'] for pn in per_node), default=0)
    except Exception:
        pass
    if peak_kb == 0 and not per_node:
        return {}
    return {
        'peak_memory_kb': peak_kb,
        'peak_memory_mb': round(peak_kb / 1024.0, 1),
        'per_node': per_node,
    }



# v71 (F-STATS-GAPS-01): count sort columns with missing/NONE/ROWCOUNT-only
# statistics across the projections this query actually used. projection_columns
# is cluster-wide so this is always complete. Fires the stats-age finding when
# the ratio is high enough to plausibly be distorting the optimizer's row
# estimates (>= 50% of sort columns or >= 5 absolute columns missing).
def _measure_stats_gaps(cursor, transaction_id: int, statement_id: int) -> Dict[str, Any]:
    """Return a dict like:
      {
        'total_sort_columns': int,
        'no_stats_count':     int,
        'worst_table':        str,   # anchor_table with the most gaps
        'worst_projection':   str,   # projection_name with the most gaps
        'worst_gaps':         int,   # gaps in the worst table
      }
    or {} on error / no projections used."""
    try:
        cursor.execute("""
            SELECT p.anchor_table_schema || '.' || p.anchor_table_name AS anchor_table,
                   pc.projection_name,
                   COUNT(*) AS sort_cols_total,
                   SUM(CASE WHEN pc.statistics_type IS NULL
                              OR UPPER(pc.statistics_type) IN ('NONE','ROWCOUNT')
                            THEN 1 ELSE 0 END) AS no_stats
            FROM v_monitor.projection_usage p
            INNER JOIN v_catalog.projection_columns pc
                    ON p.projection_id = pc.projection_id
            WHERE p.transaction_id=%s AND p.statement_id=%s
              AND pc.sort_position >= 0
            GROUP BY 1, 2
            ORDER BY no_stats DESC, sort_cols_total DESC
        """, [transaction_id, statement_id])
        rows = cursor.fetchall() or []
        if not rows:
            return {}
        total_sort = 0
        total_gaps = 0
        worst = None
        for r in rows:
            tbl, proj, total, gaps = r[0] or '', r[1] or '', int(r[2] or 0), int(r[3] or 0)
            total_sort += total
            total_gaps += gaps
            if worst is None or gaps > worst[3]:
                worst = (tbl, proj, total, gaps)
        out: Dict[str, Any] = {
            'total_sort_columns': total_sort,
            'no_stats_count':     total_gaps,
        }
        if worst and worst[3] > 0:
            out['worst_table']      = worst[0]
            out['worst_projection'] = worst[1]
            out['worst_gaps']       = worst[3]
            out['worst_total']      = worst[2]
        return out
    except Exception:
        return {}


# v71.3 (F-QUERY-NODE-TIMES-01): per-node query-level execution time.
# qprof.sh teaches that dc_query_executions filtered to the
# 'ExecutePlan:EEexecute' step gives CLUSTER-WIDE per-node timings
# for the actual query work (excluding planning / finalize). This is
# always populated on any query that ran, unlike execution_engine_profiles
# which is per-node-locally-replicated. We surface it so the user sees
# which node was slowest even when EEP had no per-path breakdown.
#
# Source pattern from the attached qprof.sh:
#   select node_name, execution_step, max(completion_time-time) as duration
#   from dc_query_executions
#   where transaction_id=... and statement_id=...
#   group by 1, 2
#   order by 2, 3 desc
#
# We narrow to ExecutePlan:EEexecute (the "real" execution phase) and
# sort by duration DESC so the first row is the slowest node. Returns
# a list [{node_name, execute_ms, skew_from_fastest_ms}, ...] or []
# on error.
def _measure_query_node_times(cursor, transaction_id: int, statement_id: int) -> List[Dict[str, Any]]:
    """Return per-node ExecutePlan:EEexecute duration in ms for this
    query. Cluster-wide reliable (dc_query_executions). Used by the
    findings block to surface node-level slowness/skew even when EEP
    has no per-path detail, and by the graph-page summary area to show
    the user where cycles went."""
    try:
        cursor.execute("""
            SELECT node_name,
                   MAX(TIMESTAMPDIFF('millisecond', "time", completion_time)) AS execute_ms
            FROM v_internal.dc_query_executions
            WHERE transaction_id=%s AND statement_id=%s
              AND execution_step = 'ExecutePlan:EEexecute'
            GROUP BY 1
            ORDER BY 2 DESC
        """, [transaction_id, statement_id])
        rows = cursor.fetchall() or []
        if not rows:
            return []
        # Min non-null execute_ms = fastest node; compute skew per node.
        fastest = min((int(r[1] or 0) for r in rows), default=0)
        return [{
            'node_name':           str(r[0] or ''),
            'execute_ms':          int(r[1] or 0),
            'skew_from_fastest_ms': int((r[1] or 0) - fastest),
        } for r in rows]
    except Exception:
        return []


def _build_tree_analysis(
    nodes: List[Dict[str, Any]],
    event_rows: List[Any],
    duration_us: int,
    slowest_path: Dict[str, Any],
    slowest_pct: float,
    storage_nodes: List[Dict[str, Any]],
    join_nodes: List[Dict[str, Any]],
    total_path_time_us: float,
    eep_coverage: Optional[Dict[str, Any]] = None,
    step_skew: Optional[Dict[str, Any]] = None,
    resource_pool: Optional[Dict[str, Any]] = None,
    stats_gaps: Optional[Dict[str, Any]] = None,
    isolated_projections: Optional[List[Dict[str, Any]]] = None,
    projections_used: Optional[List[Dict[str, Any]]] = None,
    query_node_times: Optional[List[Dict[str, Any]]] = None,
) -> List[str]:
    """Build a list of plain-English observations about the specific query
    execution tree. v71 philosophy shift (per Maya's post-v70 feedback): every
    observation must answer "does this help the user tune?". Internal
    plumbing explanations (per-node vs cluster-wide views, replication
    windows, counter aging) live in server logs and the QA appendix (Step 99),
    NOT here. When we fire a finding, we name a concrete knob: a SQL
    statement to run, a projection to re-segment, a resource pool to create,
    a Data Collector policy to increase.

    Categories covered:
      - tree shape (depth, branching factor, slowest path)
      - RESEGMENTED_MANY_ROWS / BROADCAST -> with Step 19 DDL suggestions inline
      - NO_HISTOGRAM -> ANALYZE_STATISTICS + ANALYZE_HISTOGRAM calls
      - AUTO_PROJECTION_USED -> name the specific projection, point to Database Designer
      - Statistics gaps on sort columns -> ANALYZE_STATISTICS on the worst table
      - Resource pool -> flag `general`, suggest a tuned pool
      - Cross-node step skew -> Vertica-specific follow-up (ps/sar/iperf)
      - Storage scan size / join dominance / per-node data skew
      - Data Collector retention knob -> when EEP coverage is truly incomplete
      - Empty observation when the query looks healthy.
    """
    obs: List[str] = []
    if not nodes:
        return ["The query returned no plan nodes - nothing to analyze."]

    # --- Tree shape ---
    max_depth = max((int(n.get('depth') or 0) for n in nodes), default=0)
    n_joins   = len(join_nodes)
    n_scans   = len(storage_nodes)
    shape_parts = [f"{len(nodes)} plan step{'s' if len(nodes) != 1 else ''}"]
    if n_joins:
        shape_parts.append(f"{n_joins} join{'s' if n_joins != 1 else ''}")
    if n_scans:
        shape_parts.append(f"{n_scans} storage scan{'s' if n_scans != 1 else ''}")
    shape_parts.append(f"tree depth {max_depth}")
    obs.append("This plan has " + ", ".join(shape_parts) + ".")

    # --- Slowest path ---
    # v75.2 (Maya feedback on v75.1 image: "24.73s of 25.5s total = 18.1%?
    # does that make sense?"): NO - the 18.1% is deceptive because it's
    # slowest_us / SUM(all_path_us_across_parallel_branches). When paths run
    # in parallel the sum is much larger than wall-clock, so the % looks
    # tiny even though the path dominates elapsed time. Present TWO numbers
    # explicitly labeled:
    #   - wallclock_pct = slowest_us / query_duration_us * 100 (intuitive
    #     "this path is X% of the elapsed query time")
    #   - path_sum_pct  = slowest_us / SUM(path_us) * 100 (original, CPU
    #     effort across parallel branches; preserved for completeness)
    sp_id = slowest_path.get('path_id')
    sp_us = slowest_path.get('time_us') or 0.0
    if sp_id is not None and sp_us > 0:
        sp_node = next((n for n in nodes if n.get('path_id') == sp_id), None)
        sp_title = (sp_node or {}).get('short_title') or f"Path {sp_id}"
        wallclock_pct = (sp_us / duration_us * 100.0) if duration_us else 0.0
        obs.append(
            f"The slowest step is PATH {sp_id} ({sp_title}) at "
            f"{sp_us/1000.0:.2f} ms. That is {wallclock_pct:.1f}% of the query's "
            f"wall-clock duration (primary signal - if this path is fast, the "
            f"whole query is fast) and {slowest_pct:.1f}% of the total work "
            f"summed across all paths (cluster-wide CPU effort across parallel "
            f"branches). Start your investigation here."
        )

    # --- v71 (F-RETENTION-KNOB-01): retention-knob finding.
    # Replaces the v64-v70 EEP-gap paragraph. Maya's post-v70 feedback:
    # the user does not care that execution_engine_profiles is per-node or
    # that Vertica has a replication window; they care about what they can
    # turn. Data Collector retention IS a knob a DBA can turn, so we surface
    # THAT (one sentence, one runnable SQL), not the plumbing explanation.
    # We also log the technical reality server-side so we can still
    # triage if the user reports weirdness.
    cov = eep_coverage or {}
    cluster_nodes  = int(cov.get('cluster_nodes') or 0)
    eep_nodes_seen = int(cov.get('eep_nodes_seen') or cov.get('nodes_seen') or 0)
    dpa_nodes_seen = int(cov.get('dpa_nodes_seen') or 0)
    coverage_is_incomplete = (
        cluster_nodes > 0 and (
            eep_nodes_seen == 0
            or eep_nodes_seen < cluster_nodes
            or dpa_nodes_seen == 0
            or dpa_nodes_seen < cluster_nodes
        )
    )
    if coverage_is_incomplete:
        # v71.5: removed the redundant "tx_stmt unknown at finding-build time"
        # log line Maya flagged - it duplicated the coverage logging already
        # emitted from fetch_profile_graph_data (line ~3224) and added noise
        # without new information. The finding observation below is the only
        # output that matters here.
        obs.append(
            "Some per-operator timings for this query were not captured "
            "(affects the depth of detail in Steps 14/15 and the popup "
            "per-node breakdown; not a query failure). To capture fuller "
            "profile data for future runs, a DBA can widen Data Collector "
            "retention: "
            "SELECT SET_DATA_COLLECTOR_POLICY('ExecutionEngineProfiles', '86400', '256m'); "
            "(24h retention, 256MB max)."
        )

    # --- v68 / v71 upgrade (F-STEP03B-SKEW-01): cross-node step skew.
    # Only flag material skew (>= 5 ms AND >= 5% of query duration) so we
    # don't cry wolf on micro-jitter. v71 rewrite: replace the generic
    # "check that node's health" advice with concrete Vertica-side probes
    # the user can actually run.
    if step_skew:
        skew_ms = int(step_skew.get('skew_ms') or 0)
        step_name = str(step_skew.get('step') or '')
        slow_node = str(step_skew.get('slowest_node') or '')
        fast_node = str(step_skew.get('fastest_node') or '')
        query_ms = float(duration_us or 0) / 1000.0
        if (skew_ms >= 5 and step_name and slow_node and fast_node
                and (query_ms <= 0 or (skew_ms / max(query_ms, 1.0)) >= 0.05)):
            obs.append(
                f"Cross-node step skew: {step_name} started {skew_ms} ms "
                f"later on {slow_node} than on {fast_node}. If {slow_node} "
                f"lags run-to-run, inspect it: "
                f"SELECT node_name, cpu_utilization_pct, memory_usage_percent "
                f"FROM v_monitor.host_resources WHERE host_name ILIKE '%{slow_node.split('_')[-1] if '_' in slow_node else slow_node}%'; "
                f"also check disk latency via v_monitor.disk_storage and "
                f"network via v_monitor.network_interfaces. If the slow node "
                f"varies across runs, it's cluster jitter and not worth fixing."
            )

    # --- v71.3 (F-QUERY-NODE-TIMES-01): per-node query-level timing summary.
    # Cluster-wide reliable (dc_query_executions) - available even when EEP
    # was missing. Two things are actionable here:
    #   1. If slowest-vs-fastest node skew >= 20% of the fastest time AND
    #      >= 10 ms absolute, surface it as a likely hotspot. Thresholds
    #      chosen to avoid crying wolf on normal sub-millisecond jitter.
    #   2. Always include a short per-node one-liner so the user can see
    #      the per-node shape at a glance (cluster-wide reliable). This
    #      replaces what EEP would have shown per-path but at query-level.
    if query_node_times and len(query_node_times) >= 2:
        # Sorted DESC, so [0] is slowest, [-1] is fastest.
        sorted_times = sorted(query_node_times, key=lambda r: -int(r.get('execute_ms') or 0))
        slowest = sorted_times[0]
        fastest = sorted_times[-1]
        slow_ms = int(slowest.get('execute_ms') or 0)
        fast_ms = int(fastest.get('execute_ms') or 0)
        slow_name = str(slowest.get('node_name') or '')
        fast_name = str(fastest.get('node_name') or '')
        skew_abs  = slow_ms - fast_ms
        # Render a short node-list like "node0001 30ms, node0003 29ms, ...
        # node0005 26ms" (first 5 for brevity).
        def _short(n):
            m = re.match(r'^v_[^_]+_(node\d+)$', str(n or ''), flags=re.I)
            return m.group(1) if m else str(n or '')
        preview = ", ".join(
            f"{_short(r.get('node_name'))} {int(r.get('execute_ms') or 0)}ms"
            for r in sorted_times[:5]
        )
        ratio = (skew_abs / fast_ms) if fast_ms > 0 else 0.0
        if skew_abs >= 10 and fast_ms > 0 and ratio >= 0.20:
            obs.append(
                f"Per-node query-level timing (dc_query_executions.ExecutePlan:EEexecute, "
                f"cluster-wide): {preview}. Slowest ({_short(slow_name)}) is "
                f"{skew_abs} ms ({ratio*100:.0f}%) behind fastest ({_short(fast_name)}). "
                f"If {_short(slow_name)} is consistently the laggard, inspect its host "
                f"resources: SELECT node_name, cpu_utilization_pct, memory_usage_percent "
                f"FROM v_monitor.host_resources; disk pressure via v_monitor.disk_storage; "
                f"network via v_monitor.network_interfaces."
            )
        else:
            # Informational only - no action, just the per-node fact.
            obs.append(
                f"Per-node query-level timing (cluster-wide): {preview}. "
                f"Spread {skew_abs} ms - within normal jitter."
            )

    # --- Event-driven observations ---
    # Flatten events once with event_type -> list of (path_id, suggested_action).
    # Normalize event_type to upper-underscore form so "NO HISTOGRAM" (space,
    # as it appears in query_events) and "NO_HISTOGRAM" (underscore, as used
    # in the CANONICAL_EVENT_CATALOG) both land in the same bucket.
    # v56.1 fix: the SELECT at the query_events fetch only pulls 6 columns
    # (path_id, event_type, event_description, operator_name, event_details,
    # suggested_action). v56 mistakenly indexed this using the qprof.sh 9-col
    # layout (r[3]=event_type, r[6]=path_id, r[8]=suggested_action), which
    # silently dropped every event (r[3] was operator_name, usually None).
    # Correct indices for the 6-col SELECT: r[0]=path_id, r[1]=event_type,
    # r[5]=suggested_action.
    ev_by_type: Dict[str, List[Tuple[Optional[int], str]]] = {}
    for r in (event_rows or []):
        try:
            raw = str(r[1] or '').upper().strip()
            et = re.sub(r'\s+', '_', raw)
            pid = r[0]
            sa = str(r[5] or '')
        except Exception:
            continue
        if not et:
            continue
        ev_by_type.setdefault(et, []).append((pid, sa))

    # --- v71: event findings upgraded to carry concrete DDL/SQL.
    # Maya: "every finding must name a knob the user can turn". So:
    #   RESEGMENTED_MANY_ROWS / BROADCAST  -> pull Step 19's isolated-projection
    #       suggestions INTO the finding text so the user doesn't have to
    #       scroll to Step 19 in another tab to find the re-segment DDL.
    #   NO_HISTOGRAM                       -> ANALYZE_STATISTICS (already had)
    #                                         + ANALYZE_HISTOGRAM alternative
    #                                         (higher accuracy).
    #   AUTO_PROJECTION_USED               -> name the specific projection(s)
    #                                         from projections_used; tell the
    #                                         user to run Database Designer.
    #   JOIN_SPILLED / GROUP_BY_SPILLED    -> kept, already actionable (tune
    #                                         the pool or shrink the inner).

    def _isolated_for_event(pids: List[int]) -> List[Dict[str, Any]]:
        """Return the subset of isolated projections likely responsible for
        this event. We don't have a direct path_id -> projection mapping in
        isolated_projections (it's a cluster-level catalog view), so fall
        back to "all isolated projections the query used" which is a small
        set in practice."""
        return list(isolated_projections or [])

    if 'RESEGMENTED_MANY_ROWS' in ev_by_type:
        pids = sorted({pid for pid, _ in ev_by_type['RESEGMENTED_MANY_ROWS'] if pid is not None})
        where = (f" on path{'s' if len(pids) > 1 else ''} "
                 f"{', '.join(str(p) for p in pids)}") if pids else ""
        iso = _isolated_for_event(pids)
        if iso:
            # Pull the first 1-2 concrete suggestions into the finding text.
            suggestions = []
            seen_projs = set()
            for row in iso:
                proj = row.get('isolated_projection') or ''
                ddl  = row.get('suggested_segmentation') or ''
                if proj and ddl and proj not in seen_projs:
                    seen_projs.add(proj)
                    suggestions.append(f"{proj} -> {ddl}")
                if len(suggestions) >= 2:
                    break
            tail = (" Step 19 shows concrete re-segmentation candidates for "
                    "this query's isolated projection(s): "
                    + "; ".join(suggestions) + ". "
                    "Re-segmenting on one of those hash keys aligns the "
                    "projection with the join's other side and converts the "
                    "reshuffle to a local join.")
        else:
            tail = (" Step 19 would suggest concrete re-segmentation "
                    "candidates but found none this time.")
        obs.append(
            f"Vertica resegmented a large number of rows across nodes{where}. "
            "This usually means the projection's segmentation does not "
            "match the join key." + tail
        )

    if 'JOIN_SPILLED' in ev_by_type or 'GROUP_BY_SPILLED' in ev_by_type:
        obs.append(
            "A join or group-by spilled to disk because the hash table did "
            "not fit in memory. Remediate either by enlarging the pool "
            "(ALTER RESOURCE POOL <pool> MAXMEMORYSIZE '<N>%'; or MEMORYSIZE) "
            "or by reducing the inner input size with a tighter filter or "
            "a pre-aggregation."
        )

    if 'NO_HISTOGRAM' in ev_by_type:
        actions = sorted({(sa or '').strip() for _, sa in ev_by_type['NO_HISTOGRAM'] if sa})
        actions = [a.rstrip(';') for a in actions if a]
        # Offer ANALYZE_HISTOGRAM (higher accuracy) alongside each
        # suggested ANALYZE_STATISTICS call. Vertica's ANALYZE_HISTOGRAM
        # is strictly more precise but takes longer and locks more, so
        # we present it as the alternative.
        suffix_parts = []
        if actions:
            suffix_parts.append("Run: " + "; ".join(a + ";" for a in actions))
            # Swap STATISTICS->HISTOGRAM to produce the alt call.
            alt = [re.sub(r'ANALYZE_STATISTICS', 'ANALYZE_HISTOGRAM', a, flags=re.I)
                   for a in actions]
            alt = [a for a in alt if 'ANALYZE_HISTOGRAM' in a.upper()]
            if alt:
                suffix_parts.append(
                    "For higher-accuracy stats (slower, larger locks): "
                    + "; ".join(a + ";" for a in alt)
                )
        suffix = (" " + " ".join(suffix_parts) + ".") if suffix_parts else ""
        obs.append(
            "The optimizer had no histogram for one or more predicates, so "
            "its row estimates may be off and plans can become suboptimal."
            + suffix
        )

    if 'AUTO_PROJECTION_USED' in ev_by_type:
        # Name specific projections from projection_usage so the user has
        # a concrete list, not "some tables".
        named: List[str] = []
        for pu in (projections_used or []):
            proj = str(pu.get('projection_name') or '').strip()
            # Vertica auto-projections suffix with _super or _b<n> on an
            # anchor without DBD output. Heuristic: names ending in
            # '_super' or equal to '<anchor>_b0' when that's the only
            # projection on the anchor.
            if proj and ('_super' in proj or proj.endswith('_b0') or proj.endswith('_b1')):
                if proj not in named:
                    named.append(proj)
        proj_list = ", ".join(named[:3]) if named else None
        lead = (f"The query used auto-projections ({proj_list}). "
                if proj_list else "The query used auto-projections. ")
        obs.append(
            lead +
            "Run Database Designer (admintools -> Run Database Designer -> "
            "Query-specific design) for this query shape to generate a "
            "tuned projection - typically reduces I/O and enables better "
            "join strategies. Step 16 lists the projections chosen and "
            "Step 19 lists any that are isolated from cluster-wide "
            "segmentation patterns."
        )
    if 'BROADCAST' in ev_by_type or any(
        'BROADCAST' in str((n.get('title') or '')).upper() for n in nodes
    ):
        # v71: if we have isolated-projection data, reuse the same
        # concrete suggestion as the RESEGMENTED case.
        iso = list(isolated_projections or [])
        if iso and 'RESEGMENTED_MANY_ROWS' not in ev_by_type:
            # Avoid duplicating suggestions when both events fire.
            suggestions = []
            seen = set()
            for row in iso:
                proj = row.get('isolated_projection') or ''
                ddl  = row.get('suggested_segmentation') or ''
                if proj and ddl and proj not in seen:
                    seen.add(proj)
                    suggestions.append(f"{proj} -> {ddl}")
                if len(suggestions) >= 2:
                    break
            tail = (" Step 19 suggests re-segmenting: "
                    + "; ".join(suggestions) + ". Aligning the isolated "
                    "projection's hash key with the other side of the "
                    "join converts the broadcast to a local join.")
        else:
            tail = ""
        obs.append(
            "A broadcast distribution is in play - one side of a join is "
            "replicated to every node. Cheap when that side is small; "
            "expensive when both sides are large." + tail
        )

    # --- v71 NEW (F-STATS-GAPS-01): stats-age elevated to a top-level
    # finding when many sort columns have no statistics. Step 17 already
    # shows these per-column; this finding summarizes the shape and
    # gives the user a single runnable ANALYZE_STATISTICS call.
    if stats_gaps:
        total = int(stats_gaps.get('total_sort_columns') or 0)
        gaps  = int(stats_gaps.get('no_stats_count') or 0)
        # Fire if >= 50% of sort cols missing OR >= 5 absolute columns,
        # either is a meaningful tuning opportunity.
        if total > 0 and (gaps >= 5 or (gaps / max(total, 1)) >= 0.5):
            worst_tbl  = str(stats_gaps.get('worst_table') or '')
            worst_gaps = int(stats_gaps.get('worst_gaps') or 0)
            worst_total = int(stats_gaps.get('worst_total') or 0)
            if worst_tbl and worst_gaps > 0:
                obs.append(
                    f"{worst_gaps} of {worst_total} sort columns on "
                    f"{worst_tbl} have no statistics (NONE or ROWCOUNT "
                    f"only). Missing stats are one of the biggest tuning "
                    f"levers when unset - they directly drive broadcast "
                    f"vs resegment decisions. "
                    f"Fix: SELECT ANALYZE_STATISTICS('{worst_tbl}'); "
                    f"Full list in Step 17."
                )
            else:
                obs.append(
                    f"{gaps} of {total} sort columns across projections "
                    f"this query used have no statistics. Stale/missing "
                    f"stats drive bad join-distribution choices. "
                    f"Fix: run ANALYZE_STATISTICS on the affected tables "
                    f"(full list in Step 17)."
                )

    # --- v71 NEW (F-RESOURCE-POOL-01): resource-pool awareness. Flag when
    # the query ran in the default `general` pool (signal to consider a
    # tuned pool for production). When it ran in a non-general pool,
    # stay silent - we don't want to nag about something already tuned.
    if resource_pool:
        pool = str(resource_pool.get('pool_name') or '').strip()
        if pool.lower() == 'general':
            obs.append(
                "Query ran in resource pool `general` (the default). For "
                "production workloads, consider a dedicated pool with "
                "MEMORYSIZE / MAXMEMORYSIZE / PLANNEDCONCURRENCY tuned to "
                "this query's shape: "
                "CREATE RESOURCE POOL my_pool MEMORYSIZE '2G' "
                "MAXMEMORYSIZE '8G' PLANNEDCONCURRENCY 4; "
                "then SET SESSION RESOURCE_POOL = my_pool; before re-running."
            )

    # --- Per-node skew flagging ---
    # If any path's worst node is > 1.5x the path's average node time, flag it.
    for n in nodes:
        cm = n.get('card_metrics') or {}
        per_node = cm.get('exec_on_per_node') or []
        if len(per_node) < 2:
            continue
        times = [float((pn or {}).get('ms') or 0.0) for pn in per_node]
        mx = max(times)
        avg = sum(times) / len(times)
        if avg <= 0:
            continue
        if mx >= avg * 1.5 and mx > 1.0:  # only flag if worst-node > 1 ms
            worst_node_name = (per_node[0] or {}).get('node_name') or '?'
            obs.append(
                f"Path {n.get('path_id')} shows data skew - "
                f"{worst_node_name} took {mx:.2f} ms vs the {len(times)}-node "
                f"average of {avg:.2f} ms. Uneven data distribution on this path."
            )
            break  # one skew observation is enough

    # --- Big scans ---
    for sn in storage_nodes:
        rows = int((sn.get('card_metrics') or {}).get('rows') or 0)
        if rows >= 100_000_000:
            tbl = sn.get('short_title') or f"path {sn.get('path_id')}"
            obs.append(
                f"{tbl} scans {rows:,} rows - the biggest reader in this plan. "
                "If filters can push further down, they will."
            )
            break

    # --- Join dominance ---
    if join_nodes and total_path_time_us > 0:
        join_us = sum(
            (n.get('metrics') or {}).get('running_time_us') or 0.0
            for n in join_nodes
        )
        if join_us > 0 and (join_us / total_path_time_us) > 0.6:
            pct = 100.0 * join_us / total_path_time_us
            obs.append(
                f"Joins account for {pct:.0f}% of total path time. "
                "Join order, distribution (broadcast vs. resegment), or the "
                "driving table's projection are the levers here."
            )

    # --- If nothing flagged, say so ---
    if len(obs) <= 2:  # only have shape + slowest path
        obs.append(
            "No negative events were flagged on this query. If performance is "
            "still a concern, look at the slowest path's operators, check "
            "actual-vs-estimated rows, and confirm projections match the "
            "access pattern."
        )

    return obs




def _format_qa_scalar(value: Any) -> str:
    if value is None:
        return '(null)'
    if isinstance(value, float):
        return f"{value:.3f}".rstrip('0').rstrip('.') if not value.is_integer() else str(int(value))
    if isinstance(value, (list, tuple)):
        return ', '.join(_format_qa_scalar(v) for v in value)
    return str(value)


def build_graphical_profile_qa_appendix(graph_data: Dict) -> str:
    summary = dict(graph_data.get('summary') or {})
    nodes = list(graph_data.get('nodes') or [])
    blocks: List[str] = []
    blocks.append('>>> Step 99: Graphical Query Execution Tree QA Appendix')
    blocks.append('This appendix mirrors the data rendered on the graphical Query Execution Tree page for QA comparison.')
    blocks.append('v71: appendix rebuilt as a discrepancy dashboard. Use it to spot differences between what the graph page shows, what the text tab shows, and what the cluster-wide source tables say.')
    blocks.append('')

    # v71 BLOCK 1: Cluster composition (ground truth).
    # Moved from former Step 00b - this is the authoritative node count
    # and state. Every card's "EXECUTE ON" plan value and every coverage
    # indicator is ultimately calibrated against this.
    cluster_detail = summary.get('cluster_nodes_detail') or []
    if cluster_detail:
        blocks.append('Block 1: Cluster composition (ground truth, v_catalog.nodes)')
        blocks.append(_format_table([{
            'node_name':  _format_qa_scalar(r.get('node_name')),
            'node_state': _format_qa_scalar(r.get('node_state')),
            'node_type':  _format_qa_scalar(r.get('node_type')),
        } for r in cluster_detail]))
        non_up = [r for r in cluster_detail
                  if str(r.get('node_state') or '').upper() != 'UP'
                  or str(r.get('node_type') or '').upper() != 'PERMANENT']
        if non_up:
            blocks.append(f"WARNING: {len(non_up)} node(s) not UP/PERMANENT. "
                          "Expect coverage gaps and possibly query reroutes.")
        blocks.append('')

    # v71 BLOCK 2: Per-metric source registry.
    # For every value the user sees on the graph page, this table names
    # the Vertica source, its trust class, and which UI surface consumes
    # it. If a number looks wrong on the graph page, this is the first
    # place to look to know what to cross-check against.
    blocks.append('Block 2: Per-metric source registry')
    blocks.append(_format_table([
        {'metric': 'card.path_id',           'source': 'dc_explain_plans.path_id',                   'trust': 'cluster-wide', 'used_for': 'card header id'},
        {'metric': 'card.title',             'source': 'dc_explain_plans.path_line',                 'trust': 'cluster-wide', 'used_for': 'card title + subtitle'},
        {'metric': 'card.rows',              'source': 'dc_explain_plans.path_line (parsed)',        'trust': 'cluster-wide', 'used_for': 'card Rows, popup Rows'},
        {'metric': 'card.cost',              'source': 'dc_explain_plans.path_line (parsed)',        'trust': 'cluster-wide', 'used_for': 'card Cost, popup Cost'},
        {'metric': 'card.exec_on_plan',      'source': 'dc_explain_plans.path_line (Execute on:)',   'trust': 'cluster-wide', 'used_for': 'card EXECUTE ON, popup EXECUTE ON'},
        {'metric': 'card.exec_time_ms',      'source': "query_plan_profiles.running_time (primary, cluster-wide) | EEP 'execution time (us)' sum (enrichment)", 'trust': 'cluster-wide (primary)', 'used_for': 'card exec bar, popup Exec Time'},
        {'metric': 'card.exec_source',       'source': "derived: 'plan'=query_plan_profiles fallback, 'eep'=EEP sum, 'none'=no data", 'trust': 'derived', 'used_for': 'popup (plan) tag + help'},
        {'metric': 'card.memory_mb',         'source': "EEP 'peak memory requested (bytes)' (primary, non-deprecated) | 'peak memory capacity (bytes)' | deprecated 'reserved'/'allocated' fallback", 'trust': 'per-node, eventually-consistent', 'used_for': 'card Memory, popup Memory'},
        {'metric': 'card.exec_on_per_node',  'source': 'execution_engine_profiles grouped by node_name (only source available)', 'trust': 'per-node, eventually-consistent', 'used_for': 'popup Per-node timings (empty when EEP not replicated)'},
        {'metric': 'summary.query_node_times', 'source': "dc_query_executions step='ExecutePlan:EEexecute' grouped by node (qprof.sh pattern)", 'trust': 'cluster-wide', 'used_for': 'F-QUERY-NODE-TIMES-01 finding'},
        {'metric': 'popup.clock_time',       'source': 'query_plan_profiles.running_time',           'trust': 'cluster-wide', 'used_for': 'popup Clock Time'},
        {'metric': 'hero.query_duration',    'source': 'query_profiles.query_duration_us',           'trust': 'cluster-wide', 'used_for': 'hero Total Duration'},
        {'metric': 'hero.total_rows',        'source': 'query_profiles.rows',                        'trust': 'cluster-wide', 'used_for': 'hero Total Rows'},
        {'metric': 'hero.peak_memory',       'source': 'query_requests.memory_acquired_mb (primary) | resource_acquisitions.memory_inuse_kb (per-node tooltip + fallback)', 'trust': 'cluster-wide', 'used_for': 'hero Peak Memory tile (F-PEAK-MEMORY-01)'},
        {'metric': 'finding.resource_pool',  'source': 'resource_acquisitions.pool_name',            'trust': 'cluster-wide', 'used_for': 'F-RESOURCE-POOL-01 finding'},
        {'metric': 'finding.stats_gaps',     'source': 'projection_columns.statistics_type',         'trust': 'cluster-wide', 'used_for': 'F-STATS-GAPS-01 finding'},
        {'metric': 'finding.isolated_proj',  'source': 'projections + projection_usage',             'trust': 'cluster-wide', 'used_for': 'BROADCAST/RESEGMENTED findings, Step 19'},
        {'metric': 'coverage.cluster_nodes', 'source': 'v_catalog.nodes (PERMANENT count)',          'trust': 'cluster-wide', 'used_for': 'coverage calibration, QA block 1'},
    ]))
    blocks.append('')

    # v71 BLOCK 3: Graph Summary Fields + SQL text (existing content).
    summary_rows = []
    for key in [
        'transaction_id', 'statement_id', 'query_duration_us', 'node_count', 'event_count',
        'good_nodes', 'warn_nodes', 'bad_nodes', 'total_rows',
        'max_memory_mb',    # EEP per-operator max (often 0 if EEP purged)
        'peak_memory_mb',   # v71.5.3: query_requests.memory_acquired_mb (primary) + resource_acquisitions fallback
        'version', 'label'
    ]:
        if key in summary:
            summary_rows.append({'field': key, 'value': _format_qa_scalar(summary.get(key))})
    if summary_rows:
        blocks.append('Block 3a: Graph Summary Fields')
        blocks.append(_format_table(summary_rows))
        blocks.append('')

    sql_text = summary.get('sql_text')
    if sql_text:
        blocks.append('Block 3b: Graph Summary SQL Text (full)')
        blocks.append('-' * 72)
        # v75 (N1 from Step 99 QA): previously dumped raw single-line SQL
        # blob (2500+ chars on one line for Maya's VMart CTE query). Use
        # the same Beautify engine the graph-page "SQL Query" panel uses,
        # so the text tab shows readable multi-line formatted SQL. Fall
        # back to raw text if beautify fails for any reason (defensive -
        # the beautifier is robust but the appendix must never crash).
        try:
            pretty = beautify_sql_text(str(sql_text))
        except Exception:
            pretty = str(sql_text)
        blocks.append(pretty.rstrip())
        blocks.append('-' * 72)
        blocks.append('')

    execution_steps = summary.get('execution_steps') or []
    if execution_steps:
        blocks.append('Block 3c: Graph Execution Steps')
        formatted_steps = []
        for step in execution_steps:
            row = {}
            for k, v in step.items():
                if k == 'elapsed':
                    us = _interval_to_us(v)
                    row['elapsed_us']    = _format_qa_scalar(us)
                    row['elapsed'] = _format_us_human(us) if us is not None else _format_qa_scalar(v)
                else:
                    row[k] = _format_qa_scalar(v)
            formatted_steps.append(row)
        blocks.append(_format_table(formatted_steps))
        blocks.append('')

    summary_metrics = summary.get('summary_metrics') or {}
    if summary_metrics:
        # v74 (Maya feedback on v72 Step 99 QA): Block 3d rendered
        # `slowest_path_us: 24231813` as raw microseconds - unreadable at a
        # glance. Step 02/03 already auto-promote to `25.218 s`-style text;
        # Block 3d should be consistent. Keep the raw _us values visible
        # (they're the authoritative source) and add a sibling *_elapsed
        # field that shows the same value via _us_to_ms_text, which auto-
        # promotes to ms/s/min depending on magnitude. Both fields render
        # side-by-side so power users can still copy the raw number.
        metric_rows = []
        for key in [
            'slowest_path', 'slowest_path_us', 'slowest_path_pct',
            'storage_scan_count', 'storage_rows_scanned',
            'join_op_count', 'join_combined_us'
        ]:
            if key in summary_metrics:
                metric_rows.append({'field': key, 'value': _format_qa_scalar(summary_metrics.get(key))})
                # Append a human-readable sibling row right after any raw-us field.
                if key in ('slowest_path_us', 'join_combined_us'):
                    us_val = summary_metrics.get(key)
                    try:
                        if us_val is not None and float(us_val) > 0:
                            metric_rows.append({
                                'field': key.replace('_us', '_elapsed'),
                                'value': _us_to_ms_text(us_val),
                            })
                    except (TypeError, ValueError):
                        pass
        if metric_rows:
            blocks.append('Block 3d: Bottom Summary Metrics')
            blocks.append(_format_table(metric_rows))
            blocks.append('')

    # v71 BLOCK 4: Discrepancy spot-checks.
    # Cross-checks that compare what the graph page would render against
    # what a cluster-wide source says. If any row shows a delta > tolerance,
    # something is off - screenshot this block when reporting a bug.
    coverage = summary.get('coverage') or {}
    checks: List[Dict[str, Any]] = []
    cluster_nodes = int(coverage.get('cluster_nodes') or 0)
    eep_nodes     = int(coverage.get('eep_nodes_seen') or 0)
    dpa_nodes     = int(coverage.get('dpa_nodes_seen') or 0)
    checks.append({
        'check':        'cluster_nodes matches v_catalog.nodes row count',
        'graph_shows':  str(cluster_nodes),
        'truth_says':   str(len(cluster_detail)) if cluster_detail else '(unknown)',
        'status':       'OK' if (not cluster_detail or cluster_nodes == len(cluster_detail)) else 'MISMATCH',
    })
    checks.append({
        'check':        'EEP covered every node',
        'graph_shows':  f'{eep_nodes} of {cluster_nodes}' if cluster_nodes else '(unknown)',
        'truth_says':   'expected: all nodes',
        'status':       'OK' if cluster_nodes == 0 or eep_nodes == cluster_nodes else 'PARTIAL',
    })
    checks.append({
        'check':        'DPA covered every node',
        'graph_shows':  f'{dpa_nodes} of {cluster_nodes}' if cluster_nodes else '(unknown)',
        'truth_says':   'expected: all nodes',
        'status':       'OK' if cluster_nodes == 0 or dpa_nodes == cluster_nodes else 'PARTIAL',
    })
    # Per-card: EEP node count vs EXECUTE ON plan value
    for node in nodes:
        cm = node.get('card_metrics') or {}
        plan = str(cm.get('exec_on_plan') or '').strip()
        mon  = int(cm.get('exec_on_node_count') or 0)
        if plan.lower() in ('all nodes', 'all', ''):
            expected = cluster_nodes if cluster_nodes else None
        else:
            # Plan named specific nodes - count the commas + 1
            expected = plan.count(',') + 1 if plan else None
        if expected is None:
            status = 'OK'
        elif mon == expected:
            status = 'OK'
        elif mon == 0:
            status = 'NO_EEP'
        elif mon < expected:
            status = 'PARTIAL'
        else:
            status = 'UNEXPECTED'
        checks.append({
            'check':       f"PATH {node.get('path_id')} EXECUTE ON plan vs EEP observation",
            'graph_shows': f'plan="{plan or "(none)"}" / mon={mon}',
            'truth_says':  f'expected mon={expected if expected is not None else "(n/a)"}',
            'status':      status,
        })
    blocks.append('Block 4: Discrepancy spot-checks (graph page vs cluster truth)')
    blocks.append(_format_table(checks))
    blocks.append('Please note: PARTIAL / NO_EEP rows are common and expected on fast queries - EEP is per-node and eventually-consistent. MISMATCH / UNEXPECTED rows are what you want to screenshot.')
    blocks.append('')

    # v71 BLOCK 5: Coverage (cluster-truth vs per-node views, retained from v69).
    if coverage:
        cov_rows = []
        for key in ['cluster_nodes', 'eep_nodes_seen', 'dpa_nodes_seen',
                    'eep_total_rows', 'eep_exec_time_rows', 'dpa_total_rows']:
            if key in coverage:
                cov_rows.append({'field': f'coverage.{key}', 'value': _format_qa_scalar(coverage.get(key))})
        if cov_rows:
            blocks.append('Block 5: Coverage (cluster-truth vs per-node views)')
            blocks.append(_format_table(cov_rows))
            blocks.append('')

    # v71 BLOCK 6: Actionable-finding source data.
    # For each v71 finding, show the underlying values. Lets QA verify
    # that "general pool" finding fired because pool_name was `general`,
    # not because of a bug in the finding logic.
    rp = summary.get('resource_pool') or {}
    sg = summary.get('stats_gaps') or {}
    ip = summary.get('isolated_projections') or []
    pu = summary.get('projections_used') or []
    qnt = summary.get('query_node_times') or []
    if rp or sg or ip or pu or qnt:
        blocks.append('Block 6: v71 actionable-finding source data')
        if rp:
            blocks.append('  resource_pool: ' + _format_qa_scalar(rp.get('pool_name')))
        if sg:
            blocks.append(f"  stats_gaps: {sg.get('no_stats_count')} of {sg.get('total_sort_columns')} "
                          f"sort columns missing stats "
                          f"(worst: {sg.get('worst_table','?')}, {sg.get('worst_gaps',0)} gaps)")
        if qnt:
            # v71.3: per-node query-level ExecutePlan:EEexecute timing (qprof.sh pattern,
            # cluster-wide). Shown here so QA can cross-check the
            # F-QUERY-NODE-TIMES-01 finding values.
            blocks.append(f'  query_node_times ({len(qnt)}, dc_query_executions ExecutePlan:EEexecute):')
            blocks.append(_format_table([{
                'node_name':            _format_qa_scalar(r.get('node_name')),
                'execute_ms':           _format_qa_scalar(r.get('execute_ms')),
                'skew_from_fastest_ms': _format_qa_scalar(r.get('skew_from_fastest_ms')),
            } for r in qnt]))
        if pu:
            blocks.append(f'  projections_used ({len(pu)}):')
            blocks.append(_format_table([{
                'anchor_table':    _format_qa_scalar(r.get('anchor_table')),
                'projection_name': _format_qa_scalar(r.get('projection_name')),
            } for r in pu]))
        if ip:
            blocks.append(f'  isolated_projections ({len(ip)}):')
            blocks.append(_format_table([{
                'isolated_projection':    _format_qa_scalar(r.get('isolated_projection')),
                'current_segmentation':   _format_qa_scalar(r.get('current_segmentation'))[:60],
                'suggested_segmentation': _format_qa_scalar(r.get('suggested_segmentation')),
            } for r in ip]))
        blocks.append('')

    # v71 BLOCK 7: Per-card full data (retained from v69, just renumbered).
    for node in nodes:
        path_id = node.get('path_id')
        blocks.append(f'Block 7: Graph Card PATH {path_id}')
        card_rows = [{
            'field': 'title', 'value': _format_qa_scalar(node.get('title'))
        }, {
            'field': 'short_title', 'value': _format_qa_scalar(node.get('short_title'))
        }, {
            'field': 'status', 'value': _format_qa_scalar(node.get('status'))
        }, {
            'field': 'depth', 'value': _format_qa_scalar(node.get('depth'))
        }, {
            'field': 'parent_path_id', 'value': _format_qa_scalar(node.get('parent_path_id'))
        }, {
            'field': 'side', 'value': _format_qa_scalar(node.get('side'))
        }, {
            'field': 'badges', 'value': _format_qa_scalar(node.get('badges') or [])
        }, {
            # v75 (N6 from Step 99 QA): the existing `badges` field above is
            # the server's HEURISTIC status classification (Memory Pressure /
            # Resegment / Hot Path / ...) used to compute the card color.
            # The card ACTUALLY DISPLAYS a different list - the client-side
            # deriveBadges(events) direct event_type->short-name mapping
            # (GROUPBY SPILLED / RESEG MANY ROWS / PREPASS FALLBACK). Add a
            # parallel `visible_badges` field showing what the user sees on
            # the card, so Step 99 QA matches reality. Derived here by
            # applying the same event-type catalog the JS side uses.
            'field': 'visible_badges',
            'value': _format_qa_scalar(
                _derive_visible_badges_for_qa(node.get('events') or [])
            ),
        }]
        card_metrics = node.get('card_metrics') or {}
        for key in ['exec_time_ms', 'rows', 'memory_mb', 'cost_text', 'score_pct', 'display_name', 'subtitle',
                    'exec_on_node_count', 'exec_on_max_ms', 'exec_on_plan']:
            if key in card_metrics:
                card_rows.append({'field': f'card_metrics.{key}', 'value': _format_qa_scalar(card_metrics.get(key))})
        # F-CARD-EXECON-01: dump the per-node breakdown too, one row per node, so
        # the QA file shows exactly what the graphical card aggregated from.
        per_node = card_metrics.get('exec_on_per_node') or []
        for idx, row in enumerate(per_node):
            card_rows.append({
                'field': f'card_metrics.exec_on_per_node[{idx}]',
                'value': f"{row.get('node_name','')}: {row.get('ms', 0)} ms",
            })
        metrics = node.get('metrics') or {}
        if 'running_time_us' in metrics or 'running_time' in metrics:
            us = metrics.get('running_time_us')
            if us is None:
                us = _interval_to_us(metrics.get('running_time'))
            card_rows.append({'field': 'metrics.running_time_us', 'value': _format_qa_scalar(us)})
            card_rows.append({'field': 'metrics.running_time', 'value': _format_us_human(us) if us is not None else _format_qa_scalar(metrics.get('running_time'))})
        for key in ['memory_mb', 'read_mb', 'received_mb', 'sent_mb', 'plan_line', 'detail_text']:
            if key in metrics:
                card_rows.append({'field': f'metrics.{key}', 'value': _format_qa_scalar(metrics.get(key))})
        blocks.append(_format_table(card_rows))
        blocks.append('')

        operators = node.get('operators') or []
        if operators:
            blocks.append(f'Graph Card PATH {path_id} Operators')
            # v74 (Maya feedback on v72 Step 99 QA): when EEP execution-time
            # counters were purged by short retention, every numeric column
            # in the operators table renders as "0" which is misleading -
            # it looks like the operator took 0ms/0rows/0MB when in fact
            # Vertica simply has no counter data left for it.
            #
            # Detect the all-zero case: if every operator has exec_time_ms,
            # processed_rows, produced_rows, received_rows, and
            # memory_allocated_mb all equal to 0 (or null), surface a note
            # instead of a table full of zeros. If SOME operators have data
            # but others don't, render normally - zeros are genuine there.
            def _op_has_any_data(op):
                for k in ('exec_time_ms', 'clock_time_ms', 'processed_rows',
                         'produced_rows', 'received_rows',
                         'memory_allocated_mb', 'threads'):
                    v = op.get(k)
                    try:
                        if v is not None and float(v) > 0:
                            return True
                    except (TypeError, ValueError):
                        pass
                return False
            all_zero = not any(_op_has_any_data(op) for op in operators)
            if all_zero:
                blocks.append('(no EEP per-operator counters captured for this path - '
                              'probably purged by short dc_execution_engine_profiles retention. '
                              'The plan-level running_time from query_plan_profiles is still shown '
                              'on the card as a fallback. Fix: '
                              "SELECT set_data_collector_time_policy('ExecutionEngineProfiles','1 day');)")
            else:
                # v74 (Step 99 QA N3): column name 'memory_allocated_mb' came
                # from the deprecated Vertica counter name. v72 switched the
                # actual source to 'peak memory requested (bytes)' with
                # waterfall fallback, but the column header still says the
                # old name. Rename on output to 'memory_mb' so the column
                # matches what it actually contains. Internal key stays
                # 'memory_allocated_mb' for JS compat (see line 2844).
                renamed_ops = []
                for op in operators:
                    row = {}
                    for k, v in op.items():
                        out_key = 'memory_mb' if k == 'memory_allocated_mb' else k
                        row[out_key] = _format_qa_scalar(v)
                    renamed_ops.append(row)
                blocks.append(_format_table(renamed_ops))
            blocks.append('')

        events = node.get('events') or []
        if events:
            blocks.append(f'Graph Card PATH {path_id} Events')
            blocks.append(_format_table([{k: _format_qa_scalar(v) for k, v in ev.items()} for ev in events]))
            blocks.append('')

    return '\n'.join(blocks)



def _parse_qprof_header_value(profile_text: str, label: str) -> str:
    match = re.search(rf'^\|\s*{re.escape(label)}:\s*(.*?)\s*$', profile_text, flags=re.M)
    return match.group(1).strip() if match else ''


def _extract_qprof_request_text(profile_text: str) -> str:
    marker = '>>> Step 01: Query text'
    next_marker = '>>> Step 02:'
    start = profile_text.find(marker)
    if start < 0:
        return ''
    segment = profile_text[start:]
    end = segment.find(next_marker)
    if end >= 0:
        segment = segment[:end]
    lines = [line.rstrip() for line in segment.splitlines()]
    data_lines = []
    for line in lines[1:]:
        stripped = line.strip()
        if not stripped or set(stripped) <= {'-', '|', '+'}:
            continue
        if stripped.lower() == 'request':
            continue
        data_lines.append(stripped)
    return '\n'.join(data_lines).strip()


def run_qprof_shell(session: Dict, query: str) -> Dict[str, Any]:
    session_id = session.get('session_id') or ''
    if not session_id:
        raise RuntimeError('Session ID missing for qprof execution.')
    script_path = resolve_qprof_script_path()
    temp_root = ensure_qprof_temp_root()
    run_id = uuid.uuid4().hex
    sql_path = os.path.join(temp_root, f'qprof_{session_id}_{run_id}.sql')
    out_path = os.path.join(temp_root, f'qprof_{session_id}_{run_id}.out')
    with open(sql_path, 'w', encoding='utf-8') as handle:
        handle.write(query.strip().rstrip(';') + ';\n')
    try:
        os.chmod(sql_path, 0o600)
    except Exception:
        pass
    _register_session_temp_file(session_id, sql_path)
    _register_session_temp_file(session_id, out_path)

    # v81 SEC-002: replace env['VSQL_PASSWORD'] with a 0600 pgpass file.
    # Reason: /proc/<pid>/environ exposes a child process's environment to
    # any process running as the same uid (and to root) for the child's
    # entire lifetime. VSQL_PASSWORD in env was a long-lived, visible leak.
    # A 0600 temp file containing hostname:port:database:user:password and
    # referenced via PGPASSFILE env var is strictly less exposure: the file
    # is readable only by our uid, lives for seconds, and is unlinked in a
    # finally: block even on error.
    #
    # vsql (which qprof.sh invokes internally) natively honors PGPASSFILE.
    # If a future change to qprof.sh passes -w $VSQL_PASSWORD to vsql
    # explicitly, this path would need re-review.
    pgpass_path = os.path.join(temp_root, f'qprofcreds_{session_id}_{run_id}')
    # Decrypt at the last moment. u/p go out of scope right after we write
    # them to the 0600 file and clear the local references.
    u, p = decrypt_credentials(session)
    host_val = str(BASE_DB_CONFIG.get('host', '*'))
    port_val = str(BASE_DB_CONFIG.get('port', '*'))
    db_val   = str(BASE_DB_CONFIG.get('database', '*'))
    # Open with os.open so mode bits are applied atomically (not after a
    # window during which the file existed at default perms).
    fd = os.open(pgpass_path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as pgfh:
            pgfh.write(f'{host_val}:{port_val}:{db_val}:{u}:{p}\n')
    except Exception:
        try: os.close(fd)
        except Exception: pass
        raise
    # Also register the pgpass file for session-level cleanup, as a
    # belt-and-braces measure in case the finally: below is bypassed
    # (e.g. process killed mid-subprocess). Normal path unlinks below.
    _register_session_temp_file(session_id, pgpass_path)

    env = os.environ.copy()
    # Username is NOT the secret; keeping it in env is fine and some qprof.sh
    # versions log it. We deliberately do NOT set VSQL_PASSWORD in env.
    env['VSQL_USER'] = u
    env['PGPASSFILE'] = pgpass_path
    # Remove any pre-existing VSQL_PASSWORD inherited from os.environ so
    # vsql unambiguously reads from PGPASSFILE.
    env.pop('VSQL_PASSWORD', None)
    # Clear local plaintext references (best-effort; Python strings are
    # immutable so we can't zero them, but we can shorten their lifetime).
    del u, p

    cmd = ['bash', script_path, '-f', sql_path, '-o', out_path]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=900)
    finally:
        # v81 SEC-002: unlink the pgpass file the instant the subprocess
        # is done, success or failure. Net exposure window: seconds with
        # 0600 perms, uid-bounded. Compare to the v80 env-var approach
        # which was indefinite (/proc/<pid>/environ).
        try:
            os.unlink(pgpass_path)
        except OSError:
            pass
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or proc.stdout or 'qprof.sh failed').strip())
    if not os.path.exists(out_path):
        raise RuntimeError('qprof.sh did not produce an output file.')
    profile_text = Path(out_path).read_text(encoding='utf-8', errors='replace')
    transaction_id_text = _parse_qprof_header_value(profile_text, 'Transaction ID')
    statement_id_text = _parse_qprof_header_value(profile_text, 'Statement ID')
    if not transaction_id_text or not statement_id_text:
        raise RuntimeError('Could not parse transaction/statement IDs from qprof output.')
    return {
        'profile_text': profile_text,
        'transaction_id': int(transaction_id_text),
        'statement_id': int(statement_id_text),
        'request_text': _extract_qprof_request_text(profile_text),
        'sql_path': sql_path,
        'out_path': out_path,
    }


def run_profile_query(session: Dict, query: str) -> Dict:
    profile_query = query.strip().rstrip(';') + ';'
    # v60: measure full collection wall-clock (from PROFILE dispatch through
    # the last qprof-style step) so the client can show it alongside the
    # query-native query_duration_us. The user-visible confusion:
    # the Profile tab's "Duration: 0.087s" is the QUERY time; the ~8s they
    # see on the status bar is DB + 14+ follow-up system-table queries to
    # build this whole text+graph. Distinct numbers, both correct.
    _collection_t0 = time.time()
    # v81 SEC-001: decrypt credentials for the single vertica_python.connect
    # below; plaintext lifetime = the duration of the `with` block.
    _u, _p = decrypt_credentials(session)
    conn_info = build_connection_info(_u, _p)
    del _u, _p
    with vertica_python.connect(**conn_info) as connection:
        with connection.cursor() as cursor:
            cursor.execute('PROFILE ' + profile_query)
            nextset = getattr(cursor, 'nextset', None)
            if callable(nextset):
                while True:
                    try:
                        cursor.fetchall()
                    except Exception:
                        pass
                    try:
                        if not cursor.nextset():
                            break
                    except Exception:
                        break
            transaction_id, statement_id, request_text = locate_profile_ids_same_session(cursor, profile_query)
            canonical_request_text = _choose_full_profile_request_text(profile_query, request_text)
            graph_data = fetch_profile_graph_data(cursor, transaction_id, statement_id, canonical_request_text, request_text)
            profile_text = build_profile_text(cursor, transaction_id, statement_id, canonical_request_text)
            profile_text = profile_text.rstrip() + '\n\n' + build_graphical_profile_qa_appendix(graph_data) + '\n'
            try:
                connection.commit()
            except Exception:
                pass
    collection_sec = time.time() - _collection_t0
    profile_id = save_profile_run({
        'created_at': time.time(),
        'session_id': session.get('session_id'),
        # v81 SEC-001: PROFILE_RUNS keeps username plaintext for display
        # (shown in audit logs / multi-user pages). Username is not the
        # secret; password is. session_username() decrypts at save time.
        'username': session_username(session),
        'transaction_id': transaction_id,
        'statement_id': statement_id,
        'request_text': canonical_request_text,
        'profile_text': profile_text,
        'graph_data': graph_data,
    })
    return {
        'profile_text': profile_text,
        'transaction_id': transaction_id,
        'statement_id': statement_id,
        'graph_data': graph_data,
        'request_text': canonical_request_text,
        # v60: pass the collection wall-clock into the summary string
        'summary_text': format_profile_summary(graph_data.get('summary', {}), collection_sec=collection_sec),
        'profile_id': profile_id,
        # v76: the client uses this boolean to decide whether to render
        # the "Open Skew Between Nodes" link below "Open Graphical
        # Profile". See _skew_is_meaningful() for the threshold rule.
        'skew_meaningful': _skew_is_meaningful(
            (graph_data.get('summary', {}) or {}).get('step_skew') or {},
            int((graph_data.get('summary', {}) or {}).get('query_duration_us') or 0),
        ),
    }

def format_profile_summary(summary: Dict, collection_sec: Optional[float] = None) -> str:
    # v60: two distinct clocks shown side-by-side.
    #   Duration   = query_duration_us from v_monitor.query_profiles - how
    #                long Vertica spent running YOUR query.
    #   Collection = wall-clock for the whole /api/profile_query request,
    #                including all 18 qprof-equivalent steps against
    #                v_internal/v_monitor. This is what the status bar
    #                counts; showing both eliminates the "8s vs 0.087s"
    #                confusion.
    duration_sec = (summary.get('query_duration_us') or 0) / 1_000_000.0
    parts = [f"Duration: {duration_sec:.3f}s"]
    if collection_sec is not None and collection_sec > 0:
        parts.append(f"Collection: {collection_sec:.1f}s")
    head = ' \u00b7 '.join(parts)  # middle-dot separator
    # v75.2 (Maya feedback on v75.1): the old "Nodes: 27" string confused
    # users because "nodes" in Vertica land normally means cluster machines
    # (5 in Maya's cluster), not plan steps (27 in this query). Rename to
    # "Plan steps: N" so the label says what the number actually counts. No
    # semantic change to the data - just a clearer word.
    return (f"{head} | Plan steps: {summary.get('node_count', 0)} | "
            f"Good: {summary.get('good_nodes', 0)} | "
            f"Warning: {summary.get('warn_nodes', 0)} | "
            f"Bad: {summary.get('bad_nodes', 0)}")


# -----------------------------------------------------------------------------
# HTML
# -----------------------------------------------------------------------------
# v59 (F-STATUS-BAR-01): shared activity status bar - CSS + HTML + JS.
# Injected into every HTML template (LOGIN_HTML, PROFILE_HTML, APP_HTML) at
# module load time via simple string .replace() calls on the </style>,
# </body>, and <script> anchors. Keeps one source of truth so future edits
# only touch one place.
#
# JS design:
#   - Monkey-patches window.fetch so every network call is auto-tracked.
#     No callsite changes needed. URL-to-name inference keeps the label
#     human-friendly ("Profiling query..." rather than "POST /api/profile_query").
#   - 150ms debounce: fast requests finish before the bar ever flickers to
#     "busy". Only sustained work surfaces.
#   - Multiple concurrent activities are tracked; the most recently started
#     one is displayed. On finish, the bar falls back to the next most
#     recent, or to "Ready" when none remain.
#   - Error state shows for 5s then auto-clears. Any new activity clears it
#     immediately.
#   - Elapsed counter format:
#       < 10s -> "1.2s" (tenths)
#       < 60s -> "45s"  (whole seconds)
#       >= 60s -> "1:23" (m:ss)
_STATUS_BAR_CSS = r'''
        /* v59 activity status bar */
        .activity-status-bar {
            position: fixed;
            left: 0;
            right: 0;
            bottom: 0;
            height: 26px;
            background: #0a1628;
            border-top: 1px solid rgba(66,120,180,0.28);
            box-shadow: 0 -1px 3px rgba(0,0,0,0.35);
            color: #d4dce5;
            font-size: 12px;
            line-height: 1;
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Helvetica Neue", sans-serif;
            display: flex;
            align-items: center;
            padding: 0 14px;
            z-index: 800;
            user-select: none;
            pointer-events: none;
        }
        .activity-status-bar .status-indicator {
            display: inline-flex;
            align-items: center;
            gap: 9px;
            pointer-events: auto;
        }
        .activity-status-bar .status-dot {
            width: 8px;
            height: 8px;
            border-radius: 50%;
            background: #3fb950;
            box-shadow: 0 0 4px rgba(63,185,80,0.55);
            transition: background-color .18s ease, box-shadow .18s ease;
        }
        .activity-status-bar .status-dot.busy {
            width: 11px;
            height: 11px;
            background: transparent;
            border: 1.6px solid #58a6ff;
            border-top-color: transparent;
            border-radius: 50%;
            animation: activity-bar-spin 0.85s linear infinite;
            box-shadow: none;
        }
        .activity-status-bar .status-dot.error {
            background: #f85149;
            box-shadow: 0 0 4px rgba(248,81,73,0.65);
        }
        @keyframes activity-bar-spin { to { transform: rotate(360deg); } }
        .activity-status-bar .status-label {
            color: #e6edf3;
            font-weight: 500;
            letter-spacing: 0.15px;
        }
        .activity-status-bar .status-counter {
            color: #79c0ff;
            font-family: 'SF Mono', 'Monaco', 'Consolas', 'Menlo', monospace;
            margin-left: 10px;
            font-variant-numeric: tabular-nums;
            min-width: 44px;
            font-size: 11.5px;
            opacity: 0.92;
        }
        .activity-status-bar .status-right {
            margin-left: auto;
            color: #6e7b90;
            font-size: 11px;
            pointer-events: auto;
        }
'''

_STATUS_BAR_HTML = r'''
<div class="activity-status-bar" id="activityBar" role="status" aria-live="polite">
    <div class="status-indicator" title="Activity status">
        <span class="status-dot" id="statusDot"></span>
        <span class="status-label" id="statusLabel">Ready</span>
        <span class="status-counter" id="statusCounter"></span>
    </div>
    <div class="status-right" id="statusRight"></div>
</div>
'''

# The JS IIFE runs BEFORE the existing template script bodies (we insert it
# right after the first `<script>` tag). By the time the page's own code
# starts issuing fetches, window.fetch is already wrapped and ActivityBar
# is exposed as a global. No callsite changes required.
_STATUS_BAR_JS = r'''
// v59 (F-STATUS-BAR-01): Activity status bar state machine + fetch wrapper.
(function(){
    var activities = new Map();
    var nextId = 1;
    var tickHandle = null;
    var errorUntil = 0;
    var lastError = '';
    // v63 item 1: remember the most recently finished visible activity so
    // that when the bar goes idle we can show "Ready · last: 2.3s" instead
    // of just "Ready" - matches VS Code / JetBrains status-bar convention.
    var lastFinished = null;   // {name, durationMs} or null
    var SHOW_AFTER_MS = 150;   // debounce: don't flash on fast requests

    function fmt(ms){
        if(ms < 0) ms = 0;
        var s = ms / 1000;
        if(s < 10) return s.toFixed(1) + 's';
        if(s < 60) return Math.round(s) + 's';
        var m = Math.floor(s / 60);
        var rem = Math.floor(s - m * 60);
        return m + ':' + String(rem).padStart(2, '0');
    }
    function currentActivity(){
        var latest = null;
        activities.forEach(function(a){
            if(!a.shown) return;
            if(!latest || a.startTime > latest.startTime) latest = a;
        });
        return latest;
    }
    function render(){
        var dot = document.getElementById('statusDot');
        var lab = document.getElementById('statusLabel');
        var cnt = document.getElementById('statusCounter');
        if(!dot || !lab || !cnt) return;
        // Error takes priority when nothing is running.
        if(errorUntil > Date.now() && activities.size === 0){
            dot.className = 'status-dot error';
            lab.textContent = lastError || 'Error';
            cnt.textContent = '';
            return;
        }
        var a = currentActivity();
        if(a){
            dot.className = 'status-dot busy';
            lab.textContent = a.name;
            cnt.textContent = fmt(Date.now() - a.startTime);
        } else {
            dot.className = 'status-dot';
            // v63 item 1: idle label shows last activity duration if we have
            // one. Example: "Ready  ·  last: 2.3s".
            if (lastFinished) {
                lab.textContent = 'Ready';
                cnt.textContent = '\u00B7 last: ' + fmt(lastFinished.durationMs);
            } else {
                lab.textContent = 'Ready';
                cnt.textContent = '';
            }
        }
    }
    function ensureTicker(){
        if(tickHandle) return;
        tickHandle = setInterval(function(){
            var stillActive = false;
            activities.forEach(function(a){ if(a.shown) stillActive = true; });
            if(!stillActive && errorUntil < Date.now()){
                clearInterval(tickHandle);
                tickHandle = null;
                render();
                return;
            }
            render();
        }, 100);
    }
    function start(name){
        var id = nextId++;
        var a = { name: name || 'Working...', startTime: Date.now(), shown: false };
        activities.set(id, a);
        // Debounce: only become visible after SHOW_AFTER_MS. Fast requests
        // complete before this timer fires and never touch the bar.
        setTimeout(function(){
            if(!activities.has(id)) return;
            a.shown = true;
            errorUntil = 0;   // new activity clears any stale error
            ensureTicker();
            render();
        }, SHOW_AFTER_MS);
        return id;
    }
    function finish(id){
        // v63 item 1: if this activity was shown on the bar (i.e. it ran
        // long enough to pass the debounce), remember its duration so the
        // idle label can display "Ready  ·  last: X.Xs". Activities that
        // finished before the debounce never became visible and never
        // overwrite the "last activity" memory.
        var a = activities.get(id);
        if (a && a.shown) {
            lastFinished = { name: a.name, durationMs: Date.now() - a.startTime };
        }
        activities.delete(id);
        render();
    }
    function fail(id, msg){
        if(id != null) activities.delete(id);
        errorUntil = Date.now() + 5000;
        lastError = String(msg || 'Error');
        if(lastError.length > 80) lastError = lastError.slice(0, 77) + '...';
        ensureTicker();
        render();
    }
    function inferName(url){
        try {
            var path = (new URL(url, window.location.origin)).pathname;
            if(path.indexOf('/api/profile_query') === 0)   return 'Collecting profile data...';
            if(path.indexOf('/api/execute_query') === 0)   return 'Running query...';
            if(path.indexOf('/api/dbtree') === 0)          return 'Loading database tree...';
            if(path.indexOf('/api/profile_run') === 0)     return 'Loading profile run...';
            if(path.indexOf('/api/beautify_sql') === 0)    return 'Formatting SQL...';
            if(path.indexOf('/api/session') === 0)         return 'Checking session...';
            if(path.indexOf('/api/login') === 0)           return 'Signing in...';
            if(path.indexOf('/api/logout') === 0)          return 'Signing out...';
            if(path.indexOf('/api/') === 0)                return 'Working...';
        } catch(_){}
        return null; // non-API fetches: don't track
    }
    // Wrap window.fetch. Catches every fetch callsite automatically;
    // existing code doesn't need to change. URLs that don't map to a known
    // activity name are left untracked so static asset fetches don't flood
    // the bar.
    var _origFetch = window.fetch;
    window.fetch = function(input, init){
        var url = (typeof input === 'string') ? input
                : (input && input.url) ? input.url
                : '';
        var name = inferName(url);
        if(!name){
            return _origFetch.apply(this, arguments);
        }
        var id = start(name);
        return _origFetch.apply(this, arguments).then(function(resp){
            finish(id);
            return resp;
        }, function(err){
            fail(id, (err && err.message) || String(err));
            throw err;
        });
    };
    // Public API for explicit use (future features, non-fetch work).
    window.ActivityBar = { start: start, finish: finish, fail: fail };

    if(document.readyState === 'loading'){
        document.addEventListener('DOMContentLoaded', render);
    } else {
        render();
    }
})();
'''

LOGIN_HTML = r'''
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>Vertica Navigator Login</title>
    <link rel="icon" type="image/x-icon" href="/ASSETS/verticalogo.png">
    <style>
        :root {
            --bg-0: #050816;
            --bg-1: #0a1023;
            --bg-2: #0f1830;
            --line: rgba(104, 155, 255, 0.16);
            --line-2: rgba(54, 219, 196, 0.14);
            --card: rgba(8, 14, 29, 0.84);
            --card-border: rgba(167, 195, 255, 0.16);
            --text: #eef4ff;
            --muted: #9aa9c7;
            --accent: #53a3ff;
            --accent-2: #31d7b4;
            --danger: #ff7d91;
            --shadow: 0 20px 80px rgba(0,0,0,0.45);
        }
        * { box-sizing: border-box; }
        html, body {
            height: 100%;
            margin: 0;
            font-family: Inter, system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif;
            background: radial-gradient(circle at top left, #0e1a3d 0%, var(--bg-0) 38%, #03050c 100%);
            color: var(--text);
            overflow: hidden;
        }
        body::before {
            content: "";
            position: fixed;
            inset: -20%;
            background:
                radial-gradient(circle at 20% 20%, rgba(83,163,255,0.18), transparent 30%),
                radial-gradient(circle at 80% 30%, rgba(49,215,180,0.12), transparent 26%),
                radial-gradient(circle at 50% 75%, rgba(103,102,255,0.12), transparent 28%);
            filter: blur(40px);
            animation: drift 18s ease-in-out infinite alternate;
            pointer-events: none;
        }
        @keyframes drift {
            from { transform: translate3d(-2%, -1%, 0) scale(1); }
            to { transform: translate3d(2%, 1.5%, 0) scale(1.06); }
        }
        .grid-layer, .svg-layer {
            position: fixed;
            inset: 0;
            pointer-events: none;
        }
        .grid-layer {
            background:
                linear-gradient(rgba(255,255,255,0.025) 1px, transparent 1px),
                linear-gradient(90deg, rgba(255,255,255,0.025) 1px, transparent 1px);
            background-size: 40px 40px;
            mask-image: radial-gradient(circle at center, black 45%, transparent 88%);
        }
        .shell {
            position: relative;
            z-index: 2;
            min-height: 100%;
            display: grid;
            grid-template-columns: minmax(320px, 470px) minmax(320px, 1fr);
        }
        .panel {
            display: flex;
            align-items: center;
            justify-content: center;
            padding: 40px;
        }
        .card {
            width: 100%;
            max-width: 420px;
            background: linear-gradient(180deg, rgba(14,22,43,0.92), rgba(8,13,27,0.9));
            border: 1px solid var(--card-border);
            border-radius: 18px;
            box-shadow: var(--shadow);
            backdrop-filter: blur(16px);
            padding: 28px;
        }
        .eyebrow {
            font-size: 11px;
            letter-spacing: 0.18em;
            text-transform: uppercase;
            color: var(--accent-2);
            margin-bottom: 10px;
        }
        h1 {
            margin: 0 0 8px;
            font-size: 28px;
            line-height: 1.1;
            font-weight: 700;
        }
        .sub {
            color: var(--muted);
            margin: 0 0 24px;
            line-height: 1.5;
            font-size: 14px;
        }
        .field {
            margin-bottom: 14px;
        }
        .label {
            display: block;
            font-size: 12px;
            color: #c9d6f1;
            margin-bottom: 8px;
        }
        .input {
            width: 100%;
            border: 1px solid rgba(156, 182, 239, 0.16);
            background: rgba(7, 11, 23, 0.9);
            color: var(--text);
            border-radius: 12px;
            padding: 14px 14px;
            font-size: 14px;
            outline: none;
            transition: border-color .18s ease, box-shadow .18s ease, transform .18s ease;
        }
        .input:focus {
            border-color: rgba(83,163,255,0.75);
            box-shadow: 0 0 0 4px rgba(83,163,255,0.12);
        }
        .button {
            width: 100%;
            border: 0;
            border-radius: 12px;
            padding: 14px 18px;
            background: linear-gradient(90deg, #2b7fff, #35d2b7);
            color: white;
            font-size: 14px;
            font-weight: 700;
            cursor: pointer;
            transition: transform .15s ease, box-shadow .15s ease, opacity .15s ease;
            box-shadow: 0 12px 30px rgba(24, 90, 201, 0.25);
        }
        .button:hover { transform: translateY(-1px); }
        .button:disabled { opacity: 0.75; cursor: wait; }
        .error {
            min-height: 18px;
            margin: 14px 0 0;
            color: var(--danger);
            font-size: 13px;
        }
        .brand-side {
            padding: 64px;
            display: flex;
            flex-direction: column;
            justify-content: center;
            gap: 28px;
        }
        .brand-title {
            font-size: clamp(34px, 6vw, 62px);
            font-weight: 800;
            line-height: 1.02;
            letter-spacing: -0.03em;
            max-width: 650px;
        }
        .brand-copy {
            max-width: 560px;
            color: #b6c3df;
            font-size: 16px;
            line-height: 1.6;
        }
        .metrics {
            display: grid;
            grid-template-columns: repeat(3, minmax(120px, 1fr));
            gap: 14px;
            max-width: 700px;
        }
        .metric {
            border: 1px solid rgba(163,192,255,0.12);
            background: rgba(10, 16, 34, 0.45);
            border-radius: 14px;
            padding: 16px;
            backdrop-filter: blur(10px);
        }
        .metric .value {
            font-size: 24px;
            font-weight: 700;
            margin-bottom: 6px;
        }
        .metric .label2 {
            color: #93a5ca;
            font-size: 12px;
            text-transform: uppercase;
            letter-spacing: 0.12em;
        }
        @media (max-width: 980px) {
            .shell { grid-template-columns: 1fr; }
            .brand-side { display: none; }
            .panel { padding: 22px; }
        }
    </style>
</head>
<body>
    <div class="grid-layer"></div>
    <svg class="svg-layer" viewBox="0 0 1600 900" preserveAspectRatio="none" aria-hidden="true">
        <defs>
            <linearGradient id="flow" x1="0%" y1="0%" x2="100%" y2="0%">
                <stop offset="0%" stop-color="rgba(83,163,255,0)"/>
                <stop offset="45%" stop-color="rgba(83,163,255,0.35)"/>
                <stop offset="100%" stop-color="rgba(49,215,180,0.05)"/>
            </linearGradient>
            <linearGradient id="flow2" x1="0%" y1="0%" x2="100%" y2="100%">
                <stop offset="0%" stop-color="rgba(49,215,180,0.02)"/>
                <stop offset="50%" stop-color="rgba(49,215,180,0.26)"/>
                <stop offset="100%" stop-color="rgba(83,163,255,0.04)"/>
            </linearGradient>
        </defs>
        <g fill="none" stroke-width="1.5">
            <path d="M0,710 C180,660 220,610 360,610 C520,610 590,760 760,760 C920,760 1020,520 1210,520 C1370,520 1440,610 1600,580" stroke="url(#flow)"/>
            <path d="M0,510 C120,500 210,430 360,430 C520,430 610,570 780,570 C960,570 1050,260 1230,260 C1380,260 1475,380 1600,360" stroke="url(#flow2)"/>
            <path d="M0,290 C160,300 230,180 380,180 C520,180 640,290 800,290 C930,290 1030,130 1180,130 C1320,130 1450,220 1600,210" stroke="url(#flow)"/>
        </g>
        <g fill="rgba(83,163,255,0.65)">
            <circle cx="360" cy="610" r="3.4"/><circle cx="760" cy="760" r="3.4"/><circle cx="1210" cy="520" r="3.4"/>
            <circle cx="380" cy="180" r="3.4"/><circle cx="800" cy="290" r="3.4"/><circle cx="1230" cy="260" r="3.4"/>
        </g>
    </svg>
    <div class="shell">
        <div class="panel">
            <div class="card">
                <div class="eyebrow">Vertica Navigator</div>
                <h1>Secure database access</h1>
                <p class="sub">Sign in with your own Vertica username and password to open a dedicated session for this browser.</p>
                <form id="loginForm">
                    <div class="field">
                        <label class="label" for="username">Username</label>
                        <input class="input" id="username" name="username" autocomplete="username" required>
                    </div>
                    <div class="field">
                        <label class="label" for="password">Password</label>
                        <input class="input" id="password" name="password" type="password" autocomplete="current-password" required>
                    </div>
                    <button id="loginButton" class="button" type="submit">Log in</button>
                    <div id="errorMessage" class="error"></div>
                </form>
            </div>
        </div>
        <div class="brand-side">
            <div class="eyebrow">Analytical workspace</div>
            <div class="brand-title">Navigate schemas. Inspect structures. Run SQL with confidence.</div>
            <div class="brand-copy">A focused interface for serious data work, with authenticated user sessions, schema discovery, and a query editor in one premium, technical workspace.</div>
            <div class="metrics">
                <div class="metric"><div class="value">Live</div><div class="label2">Per-user session</div></div>
                <div class="metric"><div class="value">SQL</div><div class="label2">Editor + results</div></div>
                <div class="metric"><div class="value">Secure</div><div class="label2">Credential prompt</div></div>
            </div>
        </div>
    </div>
    <script>
        document.getElementById('loginForm').addEventListener('submit', async function(event) {
            event.preventDefault();
            const button = document.getElementById('loginButton');
            const error = document.getElementById('errorMessage');
            error.textContent = '';
            button.disabled = true;
            button.textContent = 'Connecting...';

            const payload = {
                username: document.getElementById('username').value,
                password: document.getElementById('password').value
            };

            try {
                const response = await fetch('/api/login', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify(payload)
                });
                const data = await response.json();
                if (!response.ok) {
                    throw new Error(data.error || 'Login failed');
                }
                window.location.href = '/app';
            } catch (err) {
                error.textContent = err.message || 'Login failed';
                button.disabled = false;
                button.textContent = 'Log in';
            }
        });
    </script>
</body>
</html>
'''


PROFILE_HTML = r'''
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>Vertica Query Profile</title>
    <style>
        :root {
            --line: rgba(124, 167, 255, 0.16);
            --text: #e7f0ff;
            --muted: #90a4cf;
            --cyan: #13c7ff;
            --good: #18d586;
            --warn: #ffad33;
            --bad: #ff5c67;
            --blue: #498fff;
            --purple: #9f63ff;
            --shadow: 0 22px 60px rgba(0,0,0,.34);
        }
        * { box-sizing: border-box; }
        html, body { height: 100%; }
        body {
            margin: 0;
            font-family: Inter, system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif;
            color: var(--text);
            background:
                radial-gradient(circle at top left, rgba(28,86,187,.22), transparent 28%),
                radial-gradient(circle at top right, rgba(159,99,255,.14), transparent 26%),
                linear-gradient(90deg,#04102a 0%,#0b1631 26%,#11244a 50%,#0b1631 74%,#04102a 100%);
        }
        body::before {
            content: '';
            position: fixed;
            inset: 0;
            pointer-events: none;
            background:
                linear-gradient(rgba(255,255,255,.015) 1px, transparent 1px),
                linear-gradient(90deg, rgba(255,255,255,.015) 1px, transparent 1px);
            background-size: 56px 56px;
            opacity: .35;
        }
        .page { width: min(1500px, calc(100% - 32px)); margin: 24px auto; display: flex; flex-direction: column; gap: 18px; }
        .glass {
            background: linear-gradient(90deg, rgba(14,30,58,.92), rgba(20,33,60,.74) 45%, rgba(27,42,78,.88));
            border: 1px solid var(--line);
            border-radius: 18px;
            box-shadow: var(--shadow);
            backdrop-filter: blur(14px);
        }
        .hero { padding: 22px 24px; display: grid; grid-template-columns: 1fr auto; gap: 18px; align-items: center; }
        .hero h1 { margin: 0 0 10px; font-size: 22px; color: var(--cyan); }
        .meta-row { display: flex; gap: 12px; flex-wrap: wrap; align-items: center; }
        .meta-label { color: var(--muted); font-size: 12px; }
        .meta-pill {
            display: inline-flex; align-items: center; padding: 4px 8px; border-radius: 8px;
            border: 1px solid rgba(80,131,220,.25); background: rgba(5,12,25,.36); color: #75d6ff;
            font-size: 12px; font-weight: 700;
        }
        .hero-right { display: flex; gap: 12px; align-items: stretch; }
        .big-stat { min-width: 138px; padding: 10px 14px; border-radius: 14px; background: rgba(8,16,34,.56); border: 1px solid rgba(93,124,198,.2); }
        .big-stat .k { font-size: 11px; color: var(--muted); margin-bottom: 6px; }
        .big-stat .v { font-size: 18px; font-weight: 800; line-height: 1; }
        .big-stat.primary .v { color: var(--cyan); font-size: 28px; }
        .big-stat.secondary .v { color: #d46cff; font-size: 28px; }
        .back-btn, .control-btn {
            border: 1px solid rgba(126,154,214,.22); background: rgba(8,16,34,.6); color: var(--text);
            border-radius: 10px; padding: 8px 12px; cursor: pointer; font-weight: 700; text-decoration: none;
        }
        .sql-panel summary, .legend-bar {
            list-style: none; padding: 16px 20px; display: flex; align-items: center; justify-content: space-between; gap: 12px;
        }
        .sql-panel summary::-webkit-details-marker { display: none; }
        .sql-title { display: flex; align-items: center; gap: 10px; font-weight: 700; color: #8fd7ff; }
        .folder { width: 16px; height: 16px; border-radius: 3px; background: linear-gradient(180deg,#14c5ff,#2b79ff); display: inline-block; position: relative; }
        .folder::before { content: ''; position: absolute; left: 2px; top: -2px; width: 8px; height: 4px; border-radius: 2px 2px 0 0; background: #17d0ff; }
        .caret { color: #8fa7cf; font-size: 18px; transition: transform .15s ease; }
        details[open] .caret { transform: rotate(180deg); }
        .sql-wrap { border-top: 1px solid var(--line); padding: 0 18px 18px; }
        .sql-wrap pre {
            margin: 14px 0 0; white-space: pre-wrap; word-break: break-word; background: rgba(4,10,22,.78);
            border: 1px solid rgba(116,146,214,.2); border-radius: 14px; padding: 16px; color: #dce9ff;
            font-size: 13px; line-height: 1.5; max-height: 240px; overflow: auto;
        }
        .legend-bar { display: grid; grid-template-columns: 1.3fr 1.2fr 1fr; }
        .legend-group { display: flex; flex-wrap: wrap; align-items: center; gap: 14px; color: var(--muted); font-size: 12px; }
        .legend-group strong { font-size: 12px; }
        /* v62: consolidated top panel - Query Execution Tree hero + legend + SQL,
           all inside one .glass container. Much shorter overall height so the
           tree cards are visible without scrolling.
           Structure:
               .combined-top
                 ├─ .ct-hero           (title + meta pills + big stats + back btn)
                 ├─ <hr class="ct-div">
                 ├─ .ct-legend-row     (Performance + Data Flow on one flex row)
                 ├─ .ct-legend-keys    (compact Keys line, one line, bold letter codes)
                 ├─ <hr class="ct-div">
                 └─ <details class="ct-sql">   (collapsed by default)
        */
        .combined-top { padding: 16px 22px; }
        .ct-hero { display: grid; grid-template-columns: 1fr auto; gap: 14px; align-items: center; }
        .ct-hero h1 { margin: 0 0 6px; font-size: 20px; color: var(--cyan); }
        .ct-hero .meta-row { gap: 10px; }
        .ct-hero .big-stat { min-width: 128px; padding: 8px 12px; }
        .ct-hero .big-stat.primary .v, .ct-hero .big-stat.secondary .v { font-size: 22px; }
        .ct-div { border: 0; border-top: 1px solid rgba(126,154,214,.15); margin: 12px 0 10px; }
        .ct-legend-row { display: flex; gap: 28px; flex-wrap: wrap; align-items: center;
                         color: var(--muted); font-size: 12px; }
        .ct-legend-keys { margin-top: 6px; font-size: 11px; color: var(--muted);
                          display: flex; flex-wrap: wrap; align-items: center; gap: 8px;
                          white-space: nowrap; }
        .ct-legend-keys code {
            font-family: 'SF Mono','Consolas','Menlo',monospace;
            background: rgba(5,12,25,.55);
            color: #cce7ff;
            font-weight: 800;
            font-size: 11px;
            padding: 1px 5px;
            border-radius: 3px;
            border: 1px solid rgba(126,154,214,.22);
            margin-right: 2px;
        }
        .ct-legend-keys .sep { opacity: .45; margin: 0 4px; }
        /* v62 SQL nested in combined-top: collapsed by default, slim summary row. */
        .ct-sql { margin-top: 12px; }
        .ct-sql summary {
            list-style: none; cursor: pointer; padding: 6px 0;
            display: flex; align-items: center; gap: 10px;
            color: #8fd7ff; font-weight: 600; font-size: 13px;
        }
        .ct-sql summary::-webkit-details-marker { display: none; }
        .ct-sql .caret { color: #8fa7cf; font-size: 15px; transition: transform .15s ease; margin-left: auto; }
        .ct-sql[open] .caret { transform: rotate(180deg); }
        .ct-sql .sql-wrap { border-top: 1px solid rgba(126,154,214,.15); padding: 0; margin-top: 8px; }
        .ct-sql .sql-wrap pre {
            margin: 10px 0 0; white-space: pre-wrap; word-break: break-word;
            background: rgba(4,10,22,.78); border: 1px solid rgba(116,146,214,.2);
            border-radius: 12px; padding: 14px; color: #dce9ff;
            font-size: 13px; line-height: 1.5; max-height: 220px; overflow: auto;
        }
        .dot { width: 10px; height: 10px; border-radius: 2px; display: inline-block; margin-right: 6px; }
        .fast { background: var(--good); }
        .normal { background: var(--blue); }
        .slow { background: var(--warn); }
        .critical { background: var(--bad); }
        .line-icon { width: 18px; height: 2px; border-radius: 999px; display: inline-block; margin-right: 6px; }
        .broadcast { background: linear-gradient(90deg,transparent 0 10%,#9856ff 10% 90%,transparent 90% 100%); background-size: 6px 2px; }
        .resegment { background: linear-gradient(90deg,transparent 0 10%,#ff9f43 10% 90%,transparent 90% 100%); background-size: 6px 2px; }
        .local { background: #8ea4cf; }
        .workspace { position: relative; min-height: 620px; padding: 18px; overflow: hidden; }
        .controls { position: absolute; top: 14px; right: 14px; display: flex; align-items: center; gap: 10px; z-index: 7; }
        .icon-btn { width: 30px; height: 30px; padding: 0; display: grid; place-items: center; font-size: 18px; }
        .scale-label { color: var(--muted); font-size: 12px; min-width: 42px; text-align: center; }
        .tree-scroll {
            position: relative;
            /* v53 fix 5: taller default so more cards fit without scrolling; relaxed
               upper bound so the panel can use most of the viewport. User can still
               drag the three bottom resize handles (rh-b, rh-bl, rh-br) below. */
            min-height: 720px; max-height: calc(100vh - 200px); overflow: auto; padding: 28px;
            border-radius: 18px; border: 1px solid rgba(124,167,255,.10);
            background: radial-gradient(circle at center, rgba(42,72,126,.16), transparent 42%), linear-gradient(90deg, rgba(19,31,56,.58), rgba(26,45,84,.18) 50%, rgba(19,31,56,.58));
        }
        /* v53 fix 5: bottom resize handles so the user can drag the tree viewport taller.
           Three handles - bottom edge and the two bottom corners - match the popup's
           resize pattern. We only expose bottom grip because resizing from the sides
           would fight with the page layout. */
        .tree-scroll-wrap { position: relative; }
        /* v71.5.3: drag-to-pan cursor affordances. Default cursor in empty
           tree space is `grab` to signal the interaction is available;
           .panning (added by JS during a drag) switches to `grabbing`.
           Cards and popup continue to show their own cursors because the
           JS handler only fires on isPanTarget() (scroll container, tree
           stage, SVG edges) - never on .tree-node-card or .floating-popup. */
        .tree-scroll { cursor: grab; }
        .tree-scroll.panning { cursor: grabbing; }
        .tree-scroll.panning * { cursor: grabbing !important; }
        .tree-scroll-wrap .rh-b,
        .tree-scroll-wrap .rh-bl,
        .tree-scroll-wrap .rh-br {
            position: absolute; z-index: 8; user-select: none;
        }
        .tree-scroll-wrap .rh-b  { left: 12px; right: 12px; bottom: -5px; height: 10px; cursor: ns-resize; }
        .tree-scroll-wrap .rh-bl { left: -6px;   bottom: -6px; width: 14px; height: 14px; cursor: nesw-resize; }
        .tree-scroll-wrap .rh-br { right: -6px;  bottom: -6px; width: 14px; height: 14px; cursor: nwse-resize; }
        .tree-scroll-wrap.resizing { cursor: ns-resize; }
        /* Subtle visual grip on the bottom edge so users know the panel is resizable. */
        .tree-scroll-wrap::after {
            content: ''; position: absolute; left: 50%; bottom: 2px; transform: translateX(-50%);
            width: 44px; height: 4px; border-radius: 999px;
            background: linear-gradient(90deg, rgba(125,196,255,.12), rgba(125,196,255,.46), rgba(125,196,255,.12));
            pointer-events: none;
        }
        /* v82 item 6: floating legend pinned to bottom-left of the tree
           viewport. Two states:
             .collapsed  -> only the header is shown (~170x26px). Tiny,
                            out of the way, but visible.
             (expanded)  -> header + body with larger, easy-to-read font.
           Click the box anywhere to toggle between the two. Position is
           absolute inside .tree-scroll-wrap so the legend stays pinned
           while the inner #treeScroll pans beneath it. z-index 9 puts it
           above SVG connectors (z: 0) and cards (z: 1) but below the
           floating popup (z: 50) so it never covers a selected card's
           detail panel.

           Visual language mirrors the .ct-hero / .combined-top glass
           gradient: dark navy glass with a hair-thin light border and a
           soft inner glow. Matches the Skew-page .sk-modal styling so the
           two pages feel like parts of the same app. */
        .floating-legend {
            position: absolute;
            left: 12px;
            bottom: 14px;
            z-index: 9;
            background: linear-gradient(180deg, rgba(16,28,56,.94), rgba(10,18,40,.94));
            border: 1px solid rgba(125,196,255,.28);
            border-radius: 10px;
            box-shadow: 0 10px 28px rgba(0,0,0,.45), inset 0 1px 0 rgba(255,255,255,.06);
            color: #e6edf3;
            user-select: none;
            cursor: pointer;
            transition: max-width .18s ease, padding .18s ease;
            max-width: 640px;
            padding: 6px 10px;
        }
        .floating-legend.collapsed { max-width: 170px; padding: 4px 10px; }
        .floating-legend:hover { border-color: rgba(125,196,255,.48); }
        .floating-legend .fl-header {
            display: flex; align-items: center; gap: 6px;
            font-weight: 700; letter-spacing: .02em;
        }
        .floating-legend .fl-icon  { font-size: 13px; line-height: 1; color: #7dc4ff; }
        .floating-legend .fl-title { font-size: 11px; color: #dbe9ff; }
        .floating-legend .fl-caret { margin-left: auto; font-size: 10px; color: #9fb5d6; transition: transform .18s ease; }
        .floating-legend.collapsed .fl-caret { transform: rotate(180deg); }
        .floating-legend .fl-body {
            display: block;
            margin-top: 8px;
            padding-top: 8px;
            border-top: 1px solid rgba(125,196,255,.18);
            font-size: 13px;   /* easy to read when expanded (was 10-11px in top strip) */
            line-height: 1.5;
        }
        .floating-legend.collapsed .fl-body { display: none; }
        .floating-legend .fl-section + .fl-section { margin-top: 8px; }
        .floating-legend .fl-section-title {
            font-size: 11px; font-weight: 800; letter-spacing: .06em;
            text-transform: uppercase; color: #7dc4ff; margin-bottom: 4px;
        }
        .floating-legend .fl-row {
            display: flex; flex-wrap: wrap; align-items: center;
            gap: 6px 14px;
            color: #dbe9ff;
        }
        .floating-legend .fl-row > span {
            display: inline-flex; align-items: center; gap: 5px;
            white-space: nowrap;
        }
        .floating-legend .fl-keys code {
            background: rgba(125,196,255,.16);
            color: #eaf4ff;
            padding: 1px 5px;
            border-radius: 4px;
            font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
            font-size: 11.5px;
            font-weight: 700;
        }
        .floating-legend .fl-row .sep { color: rgba(159,181,214,.5); margin: 0 2px; }
        /* reuse the existing .dot and .line-icon rules (defined for the top
           legend); they are unchanged, so colors stay consistent. */
        /* v71.5 post-feedback (Maya image 2 at 30% zoom: leftmost cards
           not near left window border, user has to scroll R/L/U/D to find
           the tree). Previous rule centered the tree inside a very wide
           stage (`left: 50%; transform: translateX(-50%)` on .tree and
           `transform-origin: top center` on .tree-stage). When the stage
           grew to match a wide plan, zoom-out scaled from the middle,
           leaving large dead-space columns on both sides of the tree.
           New rule anchors the tree to the top-left corner of the stage
           and pins the scale pivot to the same corner, so at ANY zoom
           the leftmost card stays flush-left against the scroll border.
           Small/narrow plans now render with empty space to the right
           instead of the middle - an acceptable cosmetic trade to fix
           the navigation bug on wide plans. */
        .tree-stage { position: relative; min-width: 1360px; min-height: 1200px; transform-origin: top left; transition: transform .18s ease; padding-right: 620px; }
        /* v55: tree is now a RELATIVE container for absolutely-positioned cards.
           Replaces the v54 flex-column layout - cards are placed by layoutTree()
           (x,y pairs computed from parent_path_id + side) and SVG connectors
           overlay the whole thing. Width/height set via JS after layout.
           v71.5 post-feedback: left-anchored (no translateX) so zoom-out from
           top-left keeps the leftmost card aligned with the viewport edge. */
        .tree { position: absolute; left: 0; top: 44px; padding: 10px 0 80px; }
        .tree-connectors { position: absolute; left: 0; top: 0; pointer-events: none; z-index: 0; }
        /* v71.1 post-feedback fix: Maya flagged the connectors as "almost gone"
           compared to the mockup. Root cause was that the default local-edge
           stroke was rgba(180,198,235,.55) at stroke-width:2 - visually too
           faint on the deep navy background once the cards grew their own
           borders. Bumped opacity to .88 and stroke-width to 2.5 so local
           edges read as clearly as the broadcast/resegment ones. Also added
           a subtle glow via drop-shadow so a 1:1 screenshot/PDF export still
           preserves the edges. Broadcast/resegment already had high opacity
           (.9/.95) so we leave those alone. */
        .tree-connectors .conn { fill: none; stroke-width: 2.5; stroke-linecap: round;
            filter: drop-shadow(0 0 1.5px rgba(120,170,240,.35)); }
        .tree-connectors .conn-local     { stroke: rgba(200,218,250,.88); }
        .tree-connectors .conn-broadcast { stroke: rgba(157,99,255,.92); stroke-dasharray: 6 5; }
        .tree-connectors .conn-resegment { stroke: rgba(255,159,67,.95); stroke-dasharray: 6 5; }
        /* v55: edge label pill - same visual as v54 edge-label but positioned
           absolutely on the child-stub midpoint. Clickable for edge popup. */
        .tree-edge-label {
            padding: 3px 7px; border-radius: 999px;
            font-size: 9px; font-weight: 800; letter-spacing: .04em;
            border: 1px solid rgba(126,154,214,.35);
            background: rgba(7,16,34,.96); color: #bcd4fb;
            cursor: pointer; white-space: nowrap;
            /* v73: edge-label z-index bumped from 2 to 5 - belt-and-braces
               pairing with the badge-overflow cap. If a card ever grows
               past its intended height (e.g. custom CSS in a future theme
               or browser zoom), the edge label stays drawn on top instead
               of being visually consumed by the card body. */
            z-index: 5;
            box-shadow: 0 2px 8px rgba(0,0,0,.3);
        }
        .tree-edge-label:hover { background: rgba(18,38,76,.98); color: #fff; border-color: rgba(126,154,214,.6); }
        .tree-edge-label.edge-broadcast { border-color: rgba(157,99,255,.55); color: #cfa8ff; }
        .tree-edge-label.edge-resegment { border-color: rgba(255,159,67,.6); color: #ffc27e; }
        .node-card { z-index: 1; }
        .edge-button {
            position: relative; width: 64px; height: 76px; border: 0; padding: 0; background: transparent; cursor: pointer;
            display: flex; align-items: center; justify-content: center;
        }
        .edge-button::before {
            content: ''; position: absolute; left: 50%; top: 4px; bottom: 4px; width: 8px; transform: translateX(-50%);
            border-radius: 999px; background: linear-gradient(180deg, rgba(180,198,235,.12), rgba(180,198,235,.74), rgba(180,198,235,.12));
            box-shadow: 0 0 18px rgba(92,132,223,.22);
        }
        .edge-button.broadcast::before {
            background: repeating-linear-gradient(180deg, rgba(157,99,255,.96) 0 5px, rgba(157,99,255,.12) 5px 10px);
            box-shadow: 0 0 14px rgba(159,99,255,.28);
        }
        .edge-button.resegment::before {
            background: repeating-linear-gradient(180deg, rgba(255,159,67,.96) 0 5px, rgba(255,159,67,.12) 5px 10px);
            box-shadow: 0 0 14px rgba(255,159,67,.28);
        }
        .edge-button.local::before {
            background: linear-gradient(180deg, rgba(180,198,235,.2), rgba(180,198,235,.7), rgba(180,198,235,.2));
        }
        .edge-label {
            position: relative; z-index: 1; padding: 3px 6px; border-radius: 999px; font-size: 9px; font-weight: 800;
            border: 1px solid rgba(126,154,214,.22); background: rgba(7,16,34,.95); color: #bcd4fb;
            letter-spacing: .04em;
        }
        .node-card {
            /* v53 post-ship adjust: bumped width 268 -> 300 px because the new
               help-chips (?) pushed labels like "NETWORK RECV" / "EXECUTE ON"
               onto two lines and split big row counts (1,000,000) mid-digit. */
            width: 300px; border-radius: 14px; border: 2px solid rgba(24,213,134,.82);
            background: linear-gradient(180deg, rgba(8,27,40,.985), rgba(7,19,36,.96)); box-shadow: 0 18px 34px rgba(0,0,0,.34);
            cursor: pointer; overflow: hidden; text-align: left; color: #eef6ff;
            /* v74.1 (Maya feedback on v74 screenshot): now that v74 removed the
               EXECUTE ON strip from the card body, cards with fewer badges are
               visibly shorter than TREE_CARD_H (200px). The SVG connector lines
               anchor to TREE_CARD_H below the card top, so a short card leaves
               a gap between its rendered bottom and where the line starts going
               down. Fix by pinning a minimum height equal to TREE_CARD_H so
               every card occupies the same vertical slot and connectors always
               meet a visible card edge. Content stays flex-top-aligned; the
               remainder of the card is empty card-colored space. */
            min-height: 200px;
            display: flex; flex-direction: column;
        }
        .node-card * { color: inherit; }
        .node-card.active { box-shadow: 0 0 0 2px rgba(79,161,255,.9), 0 18px 34px rgba(0,0,0,.38); }
        /* F-CARD-STATUS-01: mockup legend */
        /*   good    = FAST     = green  (rgba(24,213,134) / rgba(18,190,120)) */
        /*   neutral = MODERATE = blue   (rgba(73,143,255) / rgba(55,136,255)) */
        /*   warn    = SLOW     = orange (rgba(255,159,67) / rgba(230,130,40)) */
        /*   bad     = CRITICAL = red    (rgba(255,92,103) / rgba(205,56,68))  */
        .node-card.neutral { border-color: rgba(73,143,255,.85); }
        .node-card.warn    { border-color: rgba(255,159,67,.88); }
        .node-card.bad     { border-color: rgba(255,92,103,.9);  }
        .node-head {
            padding: 8px 10px 7px; background: linear-gradient(180deg, rgba(18,190,120,.95), rgba(8,147,96,.95));
            display: grid; grid-template-columns: 20px 1fr auto; gap: 8px; align-items: start;
        }
        .node-card.neutral .node-head { background: linear-gradient(180deg, rgba(55,136,255,.98), rgba(41,98,207,.98)); }
        .node-card.warn    .node-head { background: linear-gradient(180deg, rgba(255,159,67,.98), rgba(230,130,40,.98)); }
        .node-card.bad     .node-head { background: linear-gradient(180deg, rgba(255,92,103,.98), rgba(205,56,68,.98));  }
        /* v76 (Maya's follow-up): subtle dark drop-shadow on every piece of
           WHITE TEXT that sits on a BLUE / ORANGE / RED gradient, to make
           it easy to read. Explicitly NOT applied to green (good) cards -
           per Maya's spec "only for text with white font on blue or orange
           or red background" - because green is light enough that white
           text already reads cleanly and the shadow would muddy it.
           Values tuned to be barely perceptible: 1px offset, 2px blur,
           .45 alpha. Anything heavier starts to read as "bold" rather
           than "readable". Applies to .node-title, .node-sub, .node-id,
           and .status-pill - every descendant text element of .node-head
           on the three tinted statuses. */
        .node-card.neutral .node-head,
        .node-card.warn    .node-head,
        .node-card.bad     .node-head {
            text-shadow: 0 1px 2px rgba(0, 0, 0, .45);
        }
        .node-id { width: 20px; height: 20px; border-radius: 999px; background: rgba(0,0,0,.2); display: grid; place-items: center; font-size: 11px; font-weight: 800; }
        .node-title { font-size: 13px; font-weight: 900; line-height: 1.22; letter-spacing: .01em; color: #f4fbff; display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; overflow: hidden; word-break: break-word; }
        .node-sub { margin-top: 3px; font-size: 10px; color: rgba(230,244,255,.88); line-height: 1.3; display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; overflow: hidden; word-break: break-word; min-height: 16px; }
        .status-pill { align-self: start; border-radius: 999px; font-size: 9px; padding: 3px 7px; font-weight: 800; background: rgba(0,0,0,.2); }
        /* v82 items 2+3: replaces the old .status-pill with chips. A small,
           low-noise cue in the upper-right of the card head telling the user
           that the card is clickable. Picks up the same blue-glass hit-feel
           the popup uses - semi-transparent dark background, thin light
           border, tiny text, a pointing-finger glyph. The whole card is a
           <button> so no extra click wiring is needed. */
        .more-info-cue {
            align-self: start;
            display: inline-flex;
            align-items: center;
            gap: 4px;
            padding: 3px 7px;
            border-radius: 999px;
            background: rgba(0,0,0,.22);
            border: 1px solid rgba(255,255,255,.14);
            color: #eaf4ff;
            font-size: 9.5px;
            font-weight: 700;
            line-height: 1;
            white-space: nowrap;
            pointer-events: none;  /* card handles the click */
            transition: background .15s ease;
        }
        .node-card:hover .more-info-cue {
            background: rgba(0,0,0,.36);
            border-color: rgba(255,255,255,.28);
        }
        .more-info-cue .mi-finger { font-size: 12px; line-height: 1; }
        .more-info-cue .mi-text   { letter-spacing: .02em; }
        .node-body { padding: 8px 8px 10px; background: rgba(7,15,33,.96); }
        .progress-row { display: flex; align-items: center; gap: 8px; color: #b4c7eb; font-size: 10px; }
        /* v53: keep the ms value and its (i) src-chip on one line without wrapping
           so the progress bar still takes up the middle of the row. */
        .progress-row .progress-time { display: inline-flex; align-items: center; white-space: nowrap; }
        .progress { flex: 1; height: 8px; background: rgba(255,255,255,.08); border-radius: 999px; overflow: hidden; }
        .progress > span { display: block; height: 100%; background: linear-gradient(90deg,#18d586,#13c7ff); }
        .node-card.bad .progress > span { background: linear-gradient(90deg,#ff5c67,#ff8a94); }
        .node-card.warn .progress > span { background: linear-gradient(90deg,#ff9f43,#ffbf7e); }
        .grid3 { display: grid; grid-template-columns: repeat(3,1fr); gap: 6px; margin-top: 8px; }
        .mini { border: 1px solid rgba(104,133,193,.18); border-radius: 8px; background: rgba(8,16,34,.88); padding: 5px 6px; min-height: 42px; overflow: hidden; }
        .mini .k { font-size: 8px; color: #8fa4cd; text-transform: uppercase; white-space: nowrap; }
        /* v53 post-ship: overflow-wrap:normal keeps numbers like 1,000,000 on one
           line. Previous word-break:break-word was splitting the digit group. */
        .mini .v { font-size: 11px; font-weight: 800; margin-top: 2px; line-height: 1.15; overflow-wrap: normal; word-break: normal; color: #edf6ff; }
        .event-strip { margin-top: 8px; display: flex; flex-wrap: wrap; gap: 4px; min-height: 14px; }
        .tiny-badge { font-size: 9px; line-height: 1; padding: 3px 5px; border-radius: 999px; background: rgba(255,255,255,.08); color: #ffdb6b; border: 1px solid rgba(255,255,255,.1); }
        /* F-CARD-BADGES-01: color-coded tiny badges by polarity */
        .tiny-badge.bad  { color: #ff8892; border-color: rgba(255,92,103,.4); background: rgba(255,92,103,.08); }
        .tiny-badge.good { color: #6ee8b4; border-color: rgba(24,213,134,.4); background: rgba(24,213,134,.08); }
        .tiny-badge.warn { color: #ffc27e; border-color: rgba(255,159,67,.4); background: rgba(255,159,67,.08); }
        /* v74 (Maya feedback on v73 image 2): popup event_type names were
           neutral cyan. Color them by polarity so the eye catches the bad
           ones immediately. Same palette as the card tiny-badges.
           v74.1 (Maya feedback on v74 screenshot): the original selectors
           lost the CSS cascade because `.event-card strong` further down
           in this stylesheet has higher specificity (1 class + 1 tag)
           than `.event-type-bad` (1 class alone). Scope the override to
           `.event-card strong.event-type-*` which beats it (2 classes +
           1 tag). Result: GROUP_BY_SPILLED now renders red as intended. */
        .event-type                            { color: #bcd4fb; }
        .event-card strong.event-type-bad      { color: #ff8892; }
        .event-card strong.event-type-warn     { color: #ffc27e; }
        .event-card strong.event-type-good     { color: #6ee8b4; }
        /* v73 (Maya feedback on v72 screenshot: card 40 grew too tall with
           3 stacked badges, causing downstream FLOW edge label to visually
           overlap the card). Badges beyond the first 2 collapse into this
           overflow chip, keeping card height bounded. Click the chip (any
           click on the card body) opens the popup which has the full list. */
        .tiny-badge.badge-overflow {
            color: #9fb4d7; border-color: rgba(159,180,215,.35);
            background: rgba(159,180,215,.08); cursor: pointer;
        }
        .tiny-badge.badge-overflow:hover {
            color: #cdd8ee; border-color: rgba(159,180,215,.6);
        }
        /* F-CARD-EXECON-01 + v69 F-CARD-EXECON-PLAN-01:
           "EXECUTE ON" strip is now two lines:
              row 1: plan decision (authoritative from dc_explain_plans)
              row 2: monitoring observation (from EEP, may be partial) */
        .execon-strip { margin-top: 8px; padding: 6px 6px; border-top: 1px solid rgba(104,133,193,.22); font-size: 10px; color: #b4c7eb; }
        .execon-strip .execon-row1 { display: flex; align-items: center; gap: 6px; }
        .execon-strip .execon-label { color: #8fa4cd; text-transform: uppercase; letter-spacing: .06em; font-size: 9px; font-weight: 800; white-space: nowrap; }
        .execon-strip .execon-val { color: #edf6ff; font-weight: 700; flex: 1 1 auto; min-width: 0; }
        .execon-strip .execon-val .nodes { color: #74d9ff; }
        .execon-strip .execon-val .maxms { color: #ffbf7e; }
        /* v71.1: the EXECUTE ON value lives on its own line under the label,
           matching the MOCKUP_SPEC mockup where the card shows:
              EXECUTE ON  [?]
              16 nodes max:9ms
           Two lines max. v71.0 put the value on the same flex row as the
           label, which wrapped to 4 lines on narrow cards when the suffix
           included a long node name. The .execon-value-line rule sits below
           the label row with small top margin and ellipses anything that
           would still overflow - the full string remains in the popup's
           Per-node timings list so users never lose data. */
        .execon-strip .execon-value-line {
            margin-top: 3px;
            padding-left: 2px;
            font-size: 11px; font-weight: 700;
            color: #edf6ff;
            white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
            line-height: 1.35;
        }
        .execon-strip .execon-value-line .nodes { color: #74d9ff; }
        .execon-strip .execon-value-line .maxms { color: #ffbf7e; }
        /* v71.5.3: MIN renders in cooler color (cyan) to differentiate
           from MAX (warm orange). Pairs help eye spot skew at a glance. */
        .execon-strip .execon-value-line .minms { color: #7ed4ff; }
        /* v69: the plan-text value shown in bright teal to signal it's
           authoritative; the secondary monitoring line uses muted color
           so the plan visually anchors the card. */
        .execon-strip .execon-plan-val { color: #8de4ff; }
        .execon-strip .execon-plan-val.execon-unknown { color: #8fa4cd; font-style: italic; font-weight: 600; }
        /* v71.5.2 post-feedback: single cluster icon (three small circles in
           a triangle) before the "N nodes" label. Replaces v71.5.1 N-dots
           approach which didn't match Maya's explicit spec of ONE icon.
           Uses currentColor so it inherits .execon-plan-val teal and keeps
           color cohesive; vertical-align middle aligns the glyph baseline
           with the text run. */
        .execon-strip .execon-icon {
            color: #8de4ff;
            vertical-align: middle;
            margin-right: 6px;
            margin-top: -2px;
            display: inline-block;
        }
        .execon-strip .execon-monitoring {
            margin-top: 3px; padding-left: 2px;
            color: #9fb4d7; font-size: 9.5px; font-weight: 600;
            display: flex; align-items: center; gap: 4px; flex-wrap: wrap;
        }
        .execon-strip .execon-monitoring .execon-sublabel {
            color: #6f82a8; text-transform: uppercase; letter-spacing: .05em;
            font-size: 8.5px; font-weight: 700;
        }
        .execon-strip .execon-monitoring .nodes { color: #74d9ff; }
        .execon-strip .execon-monitoring .maxms { color: #ffbf7e; }
        /* v65: partial-data indicator on EXECUTE ON strip. When the cluster
           has more nodes than the profile snapshot could see, we want the
           user to notice immediately that "1 node" isn't a plan decision -
           it's a coverage artifact. Amber border + an italic (partial) tag. */
        .execon-strip.execon-partial {
            border-top-color: rgba(255,159,67,.42);
            background: linear-gradient(90deg, rgba(255,159,67,.06), transparent 70%);
        }
        .execon-strip .partial-tag {
            color: #ffad66; font-style: italic; font-weight: 700; margin-left: 4px;
            cursor: help;
        }
        /* v66: "no profile data" flavor - stronger amber tint on the strip
           and the "(no data)" placeholder styling used for Exec bar /
           Memory cells when EEP was totally aged out. These are visually
           distinct from a real 0 so users don't read "0.00ms" as "this
           step executed instantly". */
        .execon-strip.execon-nodata {
            border-top-color: rgba(255,159,67,.55);
            background: linear-gradient(90deg, rgba(255,159,67,.11), transparent 75%);
        }
        .progress-time.progress-time-nodata {
            color: #ffad66; font-style: italic; font-weight: 700; cursor: help;
        }
        .mini .v.v-nodata {
            color: #ffad66; font-style: italic; cursor: help;
        }
        /* v69: Plan-vs-Monitoring micro-table at the top of the popup
           EXECUTION section. Labels both sources so users never have to
           guess which table a number came from. */
        .plan-vs-mon {
            display: grid; grid-template-columns: auto 1fr; gap: 4px 12px;
            padding: 8px 10px; margin: 0;
            background: rgba(70, 110, 180, .08);
            border: 1px solid rgba(116, 217, 255, .22);
            border-radius: 6px;
            font-size: 11.5px; line-height: 1.5;
        }
        .plan-vs-mon .pvm-row { display: contents; }
        .plan-vs-mon .pvm-label {
            color: #8fa4cd; text-transform: uppercase; letter-spacing: .04em;
            font-size: 9.5px; font-weight: 700; white-space: nowrap; cursor: help;
            align-self: center;
        }
        .plan-vs-mon .pvm-val { color: #edf6ff; font-weight: 600; }
        .plan-vs-mon .pvm-val.pvm-plan { color: #8de4ff; }
        .plan-vs-mon .pvm-val.pvm-mon { color: #b4c7eb; }
        /* src-chip: clicking shows the query/formula used to produce the value.
           Registered per F-... / Q-... label in JS SRC_REGISTRY. */
        .src-chip {
            display: inline-flex; align-items: center; justify-content: center;
            width: 14px; height: 14px; border-radius: 999px; margin-left: 4px;
            background: rgba(83,163,255,0.14); color: #7dc4ff;
            border: 1px solid rgba(83,163,255,0.38);
            font-size: 9px; font-weight: 800; cursor: pointer;
            vertical-align: middle; line-height: 1;
        }
        .src-chip:hover { background: rgba(83,163,255,0.28); color: #fff; }
        /* v53: help-chip - plain-English "?" chip next to each value on the graph
           page. Same visual styling as src-chip (user request: match color, font,
           size) so they're consistent; only the glyph differs (? vs ⓘ) and the
           click handler opens openHelpOverlay() which hides the Kind/Formula/
           Columns sections via .help-mode. */
        .help-chip {
            display: inline-flex; align-items: center; justify-content: center;
            width: 14px; height: 14px; border-radius: 999px; margin-left: 4px;
            background: rgba(83,163,255,0.14); color: #7dc4ff;
            border: 1px solid rgba(83,163,255,0.38);
            font-size: 9px; font-weight: 800; cursor: pointer;
            vertical-align: middle; line-height: 1; user-select: none;
        }
        .help-chip:hover { background: rgba(83,163,255,0.28); color: #fff; }
        /* In help-mode the overlay hides the technical Kind/Formula/Columns
           blocks - keep only the title + plain-English description visible.
           v56: label pill is now blue in help-mode too, matching the unified
           blue chip styling (was leftover green from the old distinction). */
        #srcOverlay.help-mode .srcbox .kind,
        #srcOverlay.help-mode .srcbox pre,
        #srcOverlay.help-mode .srcbox #srcKind,
        #srcOverlay.help-mode .srcbox #srcCols { display: none; }
        #srcOverlay.help-mode .srcbox .label { background: rgba(83,163,255,0.14); color: #7dc4ff; border: 1px solid rgba(83,163,255,0.38); padding: 2px 8px; border-radius: 999px; display: inline-block; }
        #srcOverlay {
            position: fixed; z-index: 10000; inset: 0; display: none;
            background: rgba(0,0,0,0.56); align-items: center; justify-content: center;
        }
        #srcOverlay.open { display: flex; }
        #srcOverlay .srcbox {
            width: min(680px, calc(100vw - 32px)); max-height: min(80vh, calc(100vh - 32px));
            overflow: auto; border-radius: 14px;
            background: linear-gradient(180deg, rgba(17,31,59,.99), rgba(16,30,55,.99));
            border: 1px solid rgba(120,180,255,0.55);
            box-shadow: 0 24px 42px rgba(0,0,0,.5), 0 0 18px rgba(83,163,255,0.25);
            padding: 18px 20px; color: #eef4ff; font-size: 12px;
        }
        #srcOverlay h3 { color: var(--cyan); margin: 0 0 6px; font-size: 15px; font-weight: 900; }
        #srcOverlay .srcbox .label { color: #bc88ff; font-size: 11px; letter-spacing: .08em; text-transform: uppercase; margin-bottom: 12px; }
        #srcOverlay .srcbox .kind  { color: #a8badf; font-size: 10px; text-transform: uppercase; letter-spacing: .06em; margin: 10px 0 4px; }
        #srcOverlay .srcbox pre   {
            background: rgba(4,10,22,.78); border: 1px solid rgba(116,146,214,.22); border-radius: 8px;
            padding: 10px 12px; color: #d4e3ff; font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
            font-size: 11px; line-height: 1.45; white-space: pre-wrap; word-break: break-word; max-height: 40vh; overflow: auto;
        }
        #srcOverlay .srcbox .close {
            float: right; border: 1px solid rgba(126,154,214,.25); background: rgba(6,14,30,.9); color: #a8badf;
            border-radius: 999px; width: 26px; height: 26px; font-size: 14px; cursor: pointer;
        }
        .floating-popup {
            /* Narrower profile to match the mockup and not cover the clicked card. */
            position: fixed;
            width: 340px;
            min-width: 260px;
            max-width: calc(100vw - 32px);
            max-height: min(86vh, calc(100vh - 32px));
            display: flex;
            flex-direction: column;
            /* overflow:hidden clips the resize handles to the popup border box.
               The inner .popup-scroll provides content scrolling. */
            overflow: hidden;
            /* Custom resize handles (below) replace the CSS native resize. */
            resize: none;
            border-radius: 14px;
            /* Contrast border + outer blue glow (in addition to drop shadow). */
            border: 1px solid rgba(120,180,255,0.55);
            background: linear-gradient(180deg, rgba(17,31,59,.98), rgba(16,30,55,.985));
            box-shadow: 0 24px 42px rgba(0,0,0,.42), 0 0 18px rgba(83,163,255,0.22);
            z-index: 9999;
            /* v57 fix: popup zoom is done via CSS `zoom` set inline on this
               element (popup.style.zoom = 0.6, etc.) - same spirit as the
               tree's `transform: scale()` on #treeStage, but zoom also scales
               the layout box so positioning stays sane for a position:fixed
               element. Every pixel inside the popup (text, icons, chips,
               padding, borders) scales uniformly from that single property.
               Every font-size rule below uses em units relative to this 11px
               base - em just defines the popup's intrinsic size hierarchy;
               the runtime scaling is the `zoom` property. An earlier attempt
               (also in v57) used a --popup-scale custom property multiplied
               in calc() on each rule: empirically only the header rules
               scaled reliably - the body (metric-list, exec-row, etc) didn't
               track on some browsers. The follow-up attempt scaled font-size
               only, but chips/icons with fixed px widths stayed full size.
               `zoom` covers all of them at once. */
            font-size: 11px;
        }
        .floating-popup.hidden { display: none; }
        .floating-popup.dragging, .floating-popup.resizing { user-select: none; }
        .popup-scroll {
            flex: 1 1 auto;
            min-height: 0;           /* flex child must shrink below content height */
            overflow: auto;
            border-radius: inherit;
        }
        .resize-handle {
            position: absolute;
            background: transparent;
            z-index: 50;
        }
        /* Edges keep clear of the corners so the 12x12 corner handles always win there. */
        .rh-top    { top: 0;    left: 14px; right: 14px;  height: 5px;  cursor: ns-resize; }
        .rh-bottom { bottom: 0; left: 14px; right: 14px;  height: 5px;  cursor: ns-resize; }
        .rh-left   { left: 0;   top: 14px;  bottom: 14px; width: 5px;   cursor: ew-resize; }
        .rh-right  { right: 0;  top: 14px;  bottom: 14px; width: 5px;   cursor: ew-resize; }
        .rh-tl { top: 0;    left: 0;    width: 12px; height: 12px; cursor: nwse-resize; }
        .rh-tr { top: 0;    right: 0;   width: 12px; height: 12px; cursor: nesw-resize; }
        .rh-bl { bottom: 0; left: 0;    width: 12px; height: 12px; cursor: nesw-resize; }
        .rh-br { bottom: 0; right: 0;   width: 12px; height: 12px; cursor: nwse-resize; }
        .popup-head { padding: 14px 16px 12px; border-bottom: 1px solid rgba(125,162,225,.14); position: sticky; top: 0; background: linear-gradient(180deg, rgba(17,31,59,.99), rgba(17,31,59,.94)); cursor: move; }
        .popup-close { position: absolute; right: 10px; top: 10px; width: 26px; height: 26px; border-radius: 999px; border: 1px solid rgba(126,154,214,.18); background: rgba(6,14,30,.9); color: #a8badf; cursor: pointer; z-index: 60; }
        .popup-eyebrow { color: var(--muted); font-size: 0.909em; font-weight: 700; margin-bottom: 6px; padding-right: 28px; text-transform: uppercase; letter-spacing: .05em; }
        .popup-title { color: var(--cyan); font-size: 1.636em; font-weight: 900; line-height: 1.28; padding-right: 24px; }
        .popup-sub { margin-top: 6px; color: #bc88ff; font-size: 1.091em; line-height: 1.45; white-space: normal; word-break: break-word; }
        .popup-body { padding: 12px 16px 16px; }
        /* v76 (Maya's spec post-v75.3): small rounded rectangle at the top
           of the popup body that states WHY the card is red / orange / blue.
           Values below are COPIED VERBATIM from .node-card + .node-head
           (MOCKUP_SPEC sec 3, and .node-card/.node-head CSS above in this
           same stylesheet) so the banner renders as a visual continuation
           of its card - same gradient, same border color, same white
           text, same border-radius family.
           Do NOT "tune" these to improve contrast: Maya's instruction is
           "preserve the exact shape, colors and professional look as
           presented in the mockup", and the mockup uses white text on all
           four status gradients. Keep them in sync with .node-head (lines
           5930-5936) if the mockup palette ever changes. */
        .status-banner {
            display: block;
            margin: 0 0 14px 0;
            padding: 9px 12px 10px;
            border-radius: 10px;
            border: 2px solid rgba(24,213,134,.82); /* good default; status classes override */
            color: #f4fbff;                          /* matches .node-title color */
            font-size: 0.955em;
            font-weight: 600;
            line-height: 1.4;
            letter-spacing: .01em;                    /* matches .node-title letter-spacing */
            word-break: break-word;
            box-shadow: 0 2px 10px rgba(0,0,0,.18);
            background: linear-gradient(180deg, rgba(18,190,120,.95), rgba(8,147,96,.95));
        }
        .status-banner .sb-eyebrow {
            display: block;
            font-size: 0.78em;
            font-weight: 800;
            letter-spacing: .05em;
            text-transform: uppercase;
            color: rgba(244,251,255,.88);    /* matches .node-sub alpha treatment */
            margin-bottom: 4px;
        }
        /* Status classes mirror .node-card.neutral / .warn / .bad head + border.
           Values copied verbatim from the .node-head rules above. */
        .status-banner.sb-neutral {
            border-color: rgba(73,143,255,.85);
            background: linear-gradient(180deg, rgba(55,136,255,.98), rgba(41,98,207,.98));
        }
        .status-banner.sb-warn {
            border-color: rgba(255,159,67,.88);
            background: linear-gradient(180deg, rgba(255,159,67,.98), rgba(230,130,40,.98));
        }
        .status-banner.sb-bad {
            border-color: rgba(255,92,103,.9);
            background: linear-gradient(180deg, rgba(255,92,103,.98), rgba(205,56,68,.98));
        }
        .status-banner.sb-good {
            border-color: rgba(24,213,134,.82);
            background: linear-gradient(180deg, rgba(18,190,120,.95), rgba(8,147,96,.95));
        }
        /* v76 (Maya's follow-up): same dark drop-shadow treatment as
           .node-head, same reasoning, same tuning. Applied ONLY to the
           three tinted status banners (neutral / warn / bad) and not to
           the good one - green is light enough that white text reads
           without help. Kept identical to the .node-head rule so the
           popup banner and the card head read as one continuous piece
           of typography. */
        .status-banner.sb-neutral,
        .status-banner.sb-warn,
        .status-banner.sb-bad {
            text-shadow: 0 1px 2px rgba(0, 0, 0, .45);
        }
        .section-title { color: #a8badf; font-size: 0.909em; font-weight: 800; text-transform: uppercase; margin: 0 0 10px; letter-spacing: .06em; }
        .metric-list { display: grid; grid-template-columns: minmax(120px, 1fr) auto; gap: 7px 12px; font-size: 1em; margin-bottom: 14px; }
        .metric-list .k { color: #a1b0cf; }
        .metric-list .v { color: #eef4ff; font-weight: 700; text-align: right; white-space: nowrap; }
        .event-card, .op-card, .info-card { border-top: 1px solid rgba(125,162,225,.1); padding-top: 10px; margin-top: 10px; }
        .event-card strong, .op-card strong, .info-card strong { color: #74d9ff; display: block; margin-bottom: 4px; }
        /* v53 fix 2: deduped event card header - event_type on the left, compact
           "triggered on N nodes" hint pushed to the right when N > 1. */
        .event-card .event-head { display: flex; align-items: baseline; justify-content: space-between; gap: 10px; margin-bottom: 4px; }
        .event-card .event-head strong { margin-bottom: 0; }
        .event-card .event-count-hint { color: #a8badf; font-size: 0.909em; font-weight: 600; white-space: nowrap; letter-spacing: .02em; }
        .small-copy { color: #c7d8f6; font-size: 1em; line-height: 1.5; white-space: normal; word-break: break-word; }
        .empty { color: var(--muted); font-size: 1.091em; }
        /* v56: popup section redesign per MOCKUP_SPEC sec 5. Each section has
           an icon glyph and a title. PERFORMANCE uses a blue square, ESTIMATES
           an orange star, DETAILS an orange bullet, EXECUTION a blue node icon,
           OPERATORS a blue bullet. Collapsible sections get a chevron. */
        .sec { margin: 14px 0 0; }
        .sec-hdr { display: flex; align-items: center; gap: 8px; margin: 0 0 10px; }
        .sec-hdr .ico { width: 14px; height: 14px; display: inline-block; border-radius: 3px; flex: none; }
        .sec-hdr .ico-perf { background: #4aa3ff; border-radius: 3px; }
        .sec-hdr .ico-est  { color: #ff9f43; font-size: 16px; line-height: 1; width: auto; height: auto; }
        .sec-hdr .ico-det  { background: #ff9f43; border-radius: 999px; width: 8px; height: 8px; margin: 0 3px; }
        .sec-hdr .ico-exec { background: #4aa3ff; border-radius: 3px; }
        .sec-hdr .ico-ops  { background: #4aa3ff; border-radius: 999px; width: 8px; height: 8px; margin: 0 3px; }
        .sec-hdr .ttl { color: #a8badf; font-size: 0.909em; font-weight: 800; text-transform: uppercase; letter-spacing: .06em; }
        .sec-hdr .chev { margin-left: auto; color: #7aa0dd; font-size: 1em; cursor: pointer; user-select: none; transition: transform .15s ease; }
        .sec-hdr.collapsed .chev { transform: rotate(-90deg); }
        .sec.collapsed .sec-body { display: none; }
        .sec-hdr.clickable { cursor: pointer; }
        .sec-hdr.clickable:hover .ttl { color: #cfe0ff; }
        /* PERFORMANCE section colors for % of Query and Ratio status cues. */
        .perf-val-good  { color: #6ee8b4; }
        .perf-val-warn  { color: #ff9f43; }
        .perf-val-bad   { color: #ff8a94; }
        .perf-val-plain { color: #eef4ff; }
        /* EXECUTION row: "v_eevdb_node0001   N thr . T ms" */
        .exec-row { display: flex; align-items: center; justify-content: space-between; gap: 10px; padding: 4px 0; border-bottom: 1px dashed rgba(125,162,225,.08); font-size: 1em; }
        .exec-row:last-child { border-bottom: 0; }
        .exec-row .nn { color: #cfe0ff; font-family: 'JetBrains Mono', monospace; font-size: 0.955em; }
        .exec-row .rt { color: #eef4ff; font-weight: 700; white-space: nowrap; }
        .exec-row .rt .thr { color: #a1b0cf; font-weight: 500; margin-right: 8px; }
        /* OPERATORS block - operator name in cyan, stats underneath */
        .opblk { border-top: 1px solid rgba(125,162,225,.12); padding: 8px 0 10px; }
        .opblk:first-child { border-top: 0; }
        .opblk .op-name { color: #74d9ff; font-weight: 800; font-size: 1.091em; margin-bottom: 3px; }
        .opblk .op-stats { color: #a1b0cf; font-size: 0.955em; font-family: 'JetBrains Mono', monospace; }
        .opblk .op-stats b { color: #eef4ff; font-weight: 700; }
        .opblk .op-rows { color: #c7d8f6; font-size: 0.955em; font-family: 'JetBrains Mono', monospace; margin-top: 2px; }
        .detail-row { font-size: 1em; color: #c7d8f6; padding: 4px 0; border-bottom: 1px dashed rgba(125,162,225,.08); }
        .detail-row:last-child { border-bottom: 0; }
        .detail-row .k { color: #a1b0cf; font-weight: 600; margin-right: 6px; }
        .summary-metrics { display: grid; grid-template-columns: repeat(3, minmax(240px, 1fr)); gap: 16px;
            /* v71.4 fix (Maya regression report): the fixed activity-status-bar
               (26px, position:fixed, bottom:0, z-index:800) was covering the
               bottom of the Slowest Path card. Pushing the bottom summary
               up by 34px keeps its content clear of the status bar even
               at the shortest viewport. */
            margin-bottom: 34px;
        }
        .summary-card { position: relative; padding: 18px 18px 16px; border-radius: 18px; border: 1px solid rgba(133,163,232,.22); overflow: hidden; min-height: 120px; }
        .summary-card::before { content: ''; position: absolute; inset: 0; background: linear-gradient(135deg, rgba(255,255,255,.05), rgba(255,255,255,.015)); pointer-events: none; }
        .summary-card.alert { background: linear-gradient(135deg, rgba(115,22,34,.72), rgba(87,26,36,.42)); border-color: rgba(255,92,103,.45); }
        .summary-card.info { background: linear-gradient(135deg, rgba(26,57,138,.72), rgba(22,48,116,.42)); border-color: rgba(73,143,255,.42); }
        .summary-card.join { background: linear-gradient(135deg, rgba(85,32,138,.72), rgba(72,26,112,.42)); border-color: rgba(159,99,255,.42); }
        .summary-top { display: flex; align-items: center; gap: 12px; position: relative; z-index: 1;
            /* v71.4: let the flex container shrink the label cell if needed
               so the chip doesn't push the label to wrap to a second line. */
            min-width: 0;
        }
        .summary-icon { width: 34px; height: 34px; border-radius: 10px; display: grid; place-items: center; font-weight: 800; font-size: 18px; color: #fff; background: rgba(255,255,255,.16); box-shadow: inset 0 0 0 1px rgba(255,255,255,.12); flex: 0 0 auto; }
        /* v71.4 fix: the Slowest Path / Storage Scans / Join Operations labels
           were wrapping to two lines on narrower windows because the adjacent
           help-chip + src-chip pushed them over the container width. The
           label text itself is short and fits; it was the nowrap-vs-wrap
           policy that failed. Forcing nowrap keeps label + chips on one
           line and protects the rest of the card content from being pushed
           down into the status bar. We deliberately do NOT add overflow:hidden
           + text-overflow:ellipsis here - those would hide the help/src chips
           which live in the same span as the label text. */
        .summary-label { color: rgba(234,241,255,.82); font-size: 14px; font-weight: 600;
            white-space: nowrap;
            min-width: 0; flex: 1 1 auto;
        }
        .summary-value { position: relative; z-index: 1; margin-top: 10px; font-size: 22px; font-weight: 800; color: #ffffff; }
        .summary-sub { position: relative; z-index: 1; margin-top: 4px; color: rgba(225,236,255,.82); font-size: 14px; }
        .summary-foot { position: relative; z-index: 1; margin-top: 2px; color: rgba(225,236,255,.68); font-size: 13px; }
        @media (max-width: 1180px) {
            .page { width: min(100% - 18px, 1500px); margin: 12px auto; }
            .hero { grid-template-columns: 1fr; }
            .legend-bar { grid-template-columns: 1fr; }
            .tree-scroll { padding: 16px; max-height: none; }
            .tree-stage { min-width: 980px; }
            .summary-metrics { grid-template-columns: 1fr; }
        }
    </style>
</head>
<body>
<div class="page">
    <div class="glass combined-top">
        <!-- v62: hero section (title + meta + stats) -->
        <div class="ct-hero">
            <div>
                <h1>Query Execution Tree <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('tree-overview')" style="vertical-align:middle;">?</span></h1>
                <div class="meta-row">
                    <span class="meta-label">Transaction <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('hero-transaction-id')">?</span></span><span id="metaTxn" class="meta-pill">-</span>
                    <span class="meta-label">Statement <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('hero-statement-id')">?</span></span><span id="metaStmt" class="meta-pill">-</span>
                    <span class="meta-label">Label <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('hero-label')">?</span></span><span id="metaLabel" class="meta-pill">qprof</span>
                    <span class="meta-label">Version <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('hero-version')">?</span></span><span id="metaVersion" class="meta-pill">-</span>
                </div>
            </div>
            <div class="hero-right">
                <div class="big-stat primary"><div class="k">Total Duration <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('hero-total-duration')">?</span></div><div class="v" id="statDuration">0s</div></div>
                <div class="big-stat secondary"><div class="k">Total Rows <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('hero-total-rows')">?</span></div><div class="v" id="statRows">0</div></div>
                <!-- v71.5.2: cluster-wide Peak Memory (max across nodes) from
                     v_monitor.resource_acquisitions.memory_inuse_kb. Populated
                     by renderSummary() from summary.peak_memory_mb, with a
                     hover tooltip listing per-node values. Hidden via JS when
                     the source returns no data (rare - resource_acquisitions
                     is cluster-wide reliable; same source qprof.sh Step 04
                     uses). -->
                <div class="big-stat" id="statPeakMemoryBox" style="display:none;"><div class="k">Peak Memory <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('hero-peak-memory')">?</span></div><div class="v" id="statPeakMemory" title="">0</div></div>
                <a class="back-btn" href="/app">Back to app</a>
            </div>
        </div>

        <hr class="ct-div">

        <!-- v82 item 6 (Maya request): the Performance / Data Flow / Keys
             legend that used to live here has been moved to a small,
             collapsible floating box at the BOTTOM-LEFT of the tree
             viewport (see #floatingLegend below). Collapsed by default so
             the top panel is tighter and the graph gets more vertical
             space; click to expand with larger easy-to-read font. -->

        <hr class="ct-div">

        <!-- v62: SQL Query, collapsed by default -->
        <details class="ct-sql">
            <summary><span class="folder"></span><span>SQL Query</span><span class="caret">&#9662;</span></summary>
            <div class="sql-wrap"><pre id="sqlText"></pre></div>
        </details>
    </div>
    <div class="glass workspace">
        <div class="controls">
            <button id="zoomOut" class="control-btn icon-btn" type="button">−</button>
            <div id="scaleLabel" class="scale-label">80%</div>
            <button id="zoomIn" class="control-btn icon-btn" type="button">+</button>
            <button id="zoomReset" class="control-btn" type="button">Reset</button>
        </div>
        <div id="treeScrollWrap" class="tree-scroll-wrap">
            <div id="treeScroll" class="tree-scroll">
                <div id="treeStage" class="tree-stage">
                    <div id="tree" class="tree"></div>
                    <aside id="floatingPopup" class="floating-popup hidden"></aside>
                </div>
            </div>
            <!-- v82 item 6 (Maya request): the Performance / Data Flow / Keys
                 legend, moved from the top panel to a small floating box
                 anchored bottom-left of the tree viewport. Collapsed by
                 default (tiny footprint, ~150x24px); click anywhere on the
                 box to expand with a larger, easy-to-read font. Click
                 again to collapse. Position:absolute inside the
                 treeScrollWrap so it stays pinned while the inner
                 #treeScroll scrolls beneath it. -->
            <div id="floatingLegend" class="floating-legend collapsed"
                 onclick="toggleFloatingLegend(event)"
                 title="Click to expand legend">
                <div class="fl-header">
                    <span class="fl-icon" aria-hidden="true">&#128712;</span>
                    <span class="fl-title">Legend</span>
                    <span class="fl-caret" aria-hidden="true">&#9652;</span>
                </div>
                <div class="fl-body">
                    <div class="fl-section">
                        <div class="fl-section-title">Performance</div>
                        <div class="fl-row">
                            <span><span class="dot fast"></span>Fast</span>
                            <span><span class="dot normal"></span>Moderate</span>
                            <span><span class="dot slow"></span>Slow</span>
                            <span><span class="dot critical"></span>Critical</span>
                        </div>
                    </div>
                    <div class="fl-section">
                        <div class="fl-section-title">Data Flow</div>
                        <div class="fl-row">
                            <span><span class="line-icon broadcast"></span>Broadcast</span>
                            <span><span class="line-icon resegment"></span>Resegment</span>
                            <span><span class="line-icon local"></span>Local</span>
                        </div>
                    </div>
                    <div class="fl-section">
                        <div class="fl-section-title">Keys</div>
                        <div class="fl-row fl-keys">
                            <span title="Outer: driving side of JOIN"><code>O</code>=Outer</span>
                            <span title="Inner: build/probe side of JOIN"><code>I</code>=Inner</span>
                            <span class="sep">|</span>
                            <span title="Broadcast to every node"><code>B</code>=Broadcast</span>
                            <span title="Resegment across cluster by key"><code>R</code>=Resegment</span>
                            <span title="Local Resegment within each node"><code>LR</code>=Local&nbsp;Resegment</span>
                            <span title="Global+Local Resegment"><code>GLR</code>=Global+Local</span>
                            <span class="sep">|</span>
                            <span title="Hash join (inner in memory)"><code>H</code>=Hash</span>
                            <span title="Merge join (pre-sorted inputs)"><code>M</code>=Merge</span>
                            <span title="Pipelined join"><code>P</code>=Pipelined</span>
                            <span title="Filter / semi-join"><code>F</code>=Filter</span>
                            <span title="Cross product (Cartesian)"><code>X</code>=Cross</span>
                        </div>
                    </div>
                </div>
            </div>
            <div class="rh-b"  data-side="bottom" title="Drag to resize viewport"></div>
            <div class="rh-bl" data-side="bl"     title="Drag to resize viewport"></div>
            <div class="rh-br" data-side="br"     title="Drag to resize viewport"></div>
        </div>
    </div>
    <div class="summary-metrics">
        <div class="glass summary-card alert">
            <div class="summary-top"><div class="summary-icon">⚠</div><div class="summary-label">Slowest Path <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('summary-slowest-path')">?</span><span class="src-chip" title="Show source for F-SUMMARY-SLOWEST-01" onclick="event.stopPropagation(); openSrcOverlay('F-SUMMARY-SLOWEST-01')">&#9432;</span></div></div>
            <div class="summary-value" id="slowestPathValue">Path -</div>
            <div class="summary-sub" id="slowestPathTime">0.00s</div>
            <div class="summary-foot" id="slowestPathPct">0.0%</div>
        </div>
        <div class="glass summary-card info">
            <div class="summary-top"><div class="summary-icon" id="storageScanCount">0</div><div class="summary-label">Storage Scans <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('summary-storage-scans')">?</span></div></div>
            <div class="summary-value" id="storageRowsValue">0</div>
            <div class="summary-foot">Rows Scanned</div>
        </div>
        <div class="glass summary-card join">
            <div class="summary-top"><div class="summary-icon" id="joinOpCount">0</div><div class="summary-label">Join Operations <span class="help-chip" title="What does this mean?" onclick="openHelpOverlay('summary-joins')">?</span></div></div>
            <div class="summary-value" id="joinCombinedTime">0.00s</div>
            <div class="summary-foot">Combined Time</div>
        </div>
    </div>
</div>
<!-- Source Inspector overlay: shown when user clicks an (i) src-chip next to a
     derived value. The chip passes a label (e.g. F-CARD-EXECON-01) into
     openSrcOverlay(), which looks it up in SRC_REGISTRY and fills this panel. -->
<div id="srcOverlay" onclick="if(event.target===this)closeSrcOverlay()">
    <div class="srcbox">
        <button class="close" type="button" onclick="closeSrcOverlay()" aria-label="Close">&times;</button>
        <div class="label" id="srcLabel">-</div>
        <h3 id="srcTitle">Source</h3>
        <div id="srcDesc" class="small-copy"></div>
        <div class="kind">Kind</div>
        <div id="srcKind" class="small-copy">-</div>
        <div class="kind">Formula / SQL</div>
        <pre id="srcBody">-</pre>
        <div class="kind">Source columns</div>
        <div id="srcCols" class="small-copy">-</div>
    </div>
</div>
<script>
const profileId='__PROFILE_ID__';

// =============================================================================
// SRC_REGISTRY - "Query source / Formula" inspector
// -----------------------------------------------------------------------------
// Each derived value rendered on the graphical profile has a stable label
// (F-... for formulas, Q-... for queries). Clicking the little (i) src-chip
// next to the value opens an overlay showing the label, the formula / SQL,
// and the source columns. If the user later says "F-CARD-EXECON-01 is wrong",
// we know exactly which entry to edit. The same labels appear in the Step 99
// "Graphical Query Execution Tree QA Appendix" at the bottom of the Profile
// text tab, so a diff between our output and qprof.sh output can flag the
// specific label that disagrees.
// =============================================================================
const SRC_REGISTRY = {
    'F-CARD-STATUS-01': {
        title: 'Card status color (Fast / Moderate / Slow / Critical)',
        desc: 'Maps each path card to one of four status colors matching the mockup legend. '+
              'Currently derived in JS from a combination of event_type severity and exec-time share; '+
              'Phase 3 will reconcile with qprof.sh scoring.',
        kind: 'formula',
        body:
"status = 'bad'  if any canonical-NEGATIVE event on this path,\n"+
"       or if this path's exec-time share >= critical_threshold\n"+
"status = 'warn' if exec-time share >= slow_threshold\n"+
"status = 'good' otherwise (and no negative events)\n"+
"status = 'neutral' if exec info missing\n\n"+
"Color map:  good=green   neutral=blue   warn=orange   bad=red",
        cols: "v_monitor.query_events.event_type, " +
              "v_monitor.execution_engine_profiles(counter_name='execution time (us)').counter_value"
    },
    'F-CARD-EXECON-01': {
        title: 'EXECUTE ON: N nodes * max: T ms',
        desc: 'Per-path aggregate across nodes: how many nodes participated and the slowest '+
              'per-node execution time. Shown on every card bottom and in the popup EXECUTION section.',
        kind: 'query',
        body:
"SELECT path_id, node_name,\n"+
"       SUM(CASE counter_name WHEN 'execution time (us)'\n"+
"                             THEN counter_value ELSE 0 END)/1000.0 AS node_sum_ms\n"+
"FROM v_monitor.execution_engine_profiles\n"+
"WHERE transaction_id = :trxid AND statement_id = :stmtid\n"+
"GROUP BY 1, 2\n"+
"\n"+
"-- then in Python, per path_id:\n"+
"-- node_count  = COUNT(DISTINCT node_name)\n"+
"-- max_node_ms = MAX(node_sum_ms)",
        cols: "v_monitor.execution_engine_profiles.node_name, .path_id, .counter_name, .counter_value"
    },
    'F-CARD-EXECON-PLAN-01': {
        title: "EXECUTE ON: <value> (plan-authoritative, v69+)",
        desc: "The plan's decision about where to execute this path, parsed verbatim from "+
              "dc_explain_plans.plan_line. This is the AUTHORITATIVE source: always cluster-wide, "+
              "always complete. v69 moved it above the monitoring (EEP) observation on every card "+
              "so 'EXECUTE ON: All Nodes' is the headline answer and the EEP-observed node count "+
              "is a secondary coverage line below it. Replaces the v68 behavior where the card "+
              "headline was sourced from EEP (per-node, eventually-consistent) and could disagree "+
              "with the plan text in the same popup.",
        kind: 'query',
        body:
"SELECT path_id, path_line\n"+
"FROM v_internal.dc_explain_plans\n"+
"WHERE transaction_id = :trxid AND statement_id = :stmtid\n"+
"  AND path_line ILIKE '%Execute on:%'\n"+
"ORDER BY path_id, path_line_index;\n"+
"\n"+
"-- Server-side in Python: _extract_plan_execute_on(path_lines) pulls the\n"+
"-- text after 'Execute on:' and strips tree-indent chars. The resulting\n"+
"-- string lands on card_metrics.exec_on_plan and is rendered verbatim.",
        cols: "v_internal.dc_explain_plans.path_id, .path_line, .path_line_index"
    },
    'F-CARD-BADGES-01': {
        title: 'Card event badges from canonical event_type catalog',
        desc: 'Badges are derived deterministically from the Vertica documented event_type '+
              'values ("System Tables for Query Performance", Query Events section). '+
              'No fuzzy string matching; every badge color corresponds to the doc polarity.',
        kind: 'formula',
        body:
"Negative events (red badge):\n"+
"  DELETE_WITH_NON_OPTIMIZED_PROJECTION, MEMORY_LIMIT_HIT, NO_HISTOGRAM,\n"+
"  GROUP_BY_SPILLED, JOIN_SPILLED, RESEGMENTED_MANY_ROWS, WOS_SPILL\n\n"+
"Positive events (green badge):\n"+
"  GROUPBY_PUSHDOWN, NODE_PRUNING, TRANSITIVE_PREDICATE,\n"+
"  GROUP_BY_PREPASS_FALLBACK, MERGE_CONVERTED_TO_UNION, PARTITIONS_ELIMINATED,\n"+
"  RLE_OVERRIDDEN, SMALL_MERGE_REPLACED\n\n"+
"Warning events (orange badge):\n"+
"  NO_GROUPBY_PUSHDOWN, SIP_FALLBACK, SEQUENCE CACHE REFILLED",
        cols: "v_monitor.query_events.event_type"
    },
    // v53: labels for the exec-time numbers the user flagged as confusing to reconcile.
    'F-CARD-EXECTIME-01': {
        title: 'Card "Exec Time" (ms) - max operator SUM across nodes',
        desc: 'The ms value printed on each card (and in the popup PERFORMANCE row) is '+
              'the HOTTEST operator on that path, summed across every node. This is NOT '+
              'the path wall-clock; a path with stalls or coordination waits can have a '+
              'much larger wall-clock time (see F-SUMMARY-SLOWEST-01 / Clock Time) than '+
              'the CPU-work number shown here. Accuracy reconciliation against qprof.sh '+
              'is scheduled for Phase 3 / file 57.',
        kind: 'formula',
        body:
"-- Per-operator roll-up across nodes and threads:\n"+
"SELECT path_id, operator_name,\n"+
"       SUM(CASE counter_name WHEN 'execution time (us)'\n"+
"                             THEN counter_value ELSE NULL END)/1000.0 AS op_sum_ms\n"+
"FROM v_monitor.execution_engine_profiles\n"+
"WHERE transaction_id = :trxid AND statement_id = :stmtid\n"+
"GROUP BY path_id, operator_name, operator_id\n"+
"\n"+
"-- Then in Python:\n"+
"-- card_metrics.exec_time_ms = max(op_sum_ms) for this path_id\n"+
"--                            (the hottest single operator on the path)",
        cols: "v_monitor.execution_engine_profiles.path_id, .operator_name, "+
              ".counter_name='execution time (us)', .counter_value"
    },
    'F-CARD-CLOCKTIME-01': {
        title: 'Card "Clock Time" - path wall-clock from query_plan_profiles',
        desc: 'Path wall-clock running time straight from v_monitor.query_plan_profiles. '+
              'Includes stalls, coordination waits, and any idle time on the path - so it '+
              'can be much larger than the Exec Time (hottest operator CPU work). This '+
              'value is what drives the bottom-summary "Slowest Path" choice '+
              '(F-SUMMARY-SLOWEST-01). The canonical Phase-3 target will switch this to '+
              "the 'clock time (us)' counter in execution_engine_profiles per the System "+
              "Tables doc; for now we surface running_time directly.",
        kind: 'query',
        body:
"SELECT path_id, MAX(running_time) AS running_time\n"+
"FROM v_monitor.query_plan_profiles\n"+
"WHERE transaction_id = :trxid AND statement_id = :stmtid\n"+
"GROUP BY path_id\n"+
"\n"+
"-- running_time is stored as an interval; we convert to microseconds\n"+
"-- in Python via _interval_to_us() before rendering.",
        cols: "v_monitor.query_plan_profiles.path_id, .running_time"
    },
    'F-SUMMARY-SLOWEST-01': {
        title: 'Bottom-summary "Slowest Path" - wall-clock-based',
        desc: 'The Slowest Path card at the bottom of the graphical page picks the path '+
              'with the largest query_plan_profiles.running_time (wall-clock, same metric '+
              'as the Clock Time row in the node popup - F-CARD-CLOCKTIME-01). This is '+
              'deliberately NOT the same as each card\'s "Exec Time" number '+
              "(F-CARD-EXECTIME-01). Example: a path can have small per-operator CPU "+
              "time but a large running_time because of NetworkRecv stalls - it will be "+
              'the slowest wall-clock path while no single operator dominates CPU.',
        kind: 'formula',
        body:
"-- For each card n with a known running_time:\n"+
"--   time_us = _interval_to_us(query_plan_profiles.running_time)\n"+
"-- slowest_path     = argmax(time_us)\n"+
"-- slowest_path_us  = max(time_us)\n"+
"-- slowest_path_pct = slowest_path_us / SUM(time_us across all paths) * 100\n"+
"\n"+
"-- Same counter is used for join_combined_us (sum over JOIN paths).",
        cols: "v_monitor.query_plan_profiles.path_id, .running_time"
    },
    // v58: edge label code derivation. Each tree edge carries a short
    // bracketed code like [I-B-H] (Inner Broadcast Hash), [O-LR-H]
    // (Outer Local-Resegment Hash), [GLR-H] (Global+Local Resegment
    // Hash), [O-H] (Outer no-redistribution Hash), or [FLOW] when the
    // child isn't a join input. The code is computed on the Python
    // side from the parent's plan-line suffix and the child's own
    // "Outer -> " / "Inner -> " marker, not from fuzzy title matching.
    'F-EDGE-LABEL-01': {
        title: 'Edge label code (<JoinSide>-<Distribution>-<JoinKind>)',
        desc: 'Each edge connecting a child path to its parent JOIN gets a compact '+
              'bracketed label. Format: <JoinSide>-<Distribution>-<JoinKind>. The '+
              'Distribution middle letter collapses (is omitted) when data flows '+
              'locally with no redistribution.',
        kind: 'formula',
        body:
"JoinSide:     O = Outer,  I = Inner  (from child's 'Outer ->' / 'Inner ->' marker)\n"+
"Distribution: B   = BROADCAST\n"+
"              LR  = LOCAL RESEGMENT or LOCAL ROUND ROBIN (no GLOBAL)\n"+
"              GLR = GLOBAL + (LOCAL RESEGMENT or LOCAL ROUND ROBIN)\n"+
"              R   = plain RESEGMENT / GLOBAL-only\n"+
"              ''  = Local (no redistribution; middle collapses)\n"+
"JoinKind:     H = Hash, M = Merge, P = Pipelined, F = Filter, X = Cross\n\n"+
"-- Python extracts the parent JOIN's plan-line suffix (the text after\n"+
"--   '(PATH ID: N)'), finds the '<Side> (modifier)(modifier)...' group\n"+
"--   that matches the child's own side, and maps the modifier bag to\n"+
"--   the Distribution letter using the rules above.\n\n"+
"Examples seen in the mockup:\n"+
"   I-B-H   Inner input, Broadcast, Hash join\n"+
"   O-LR-H  Outer input, Local Resegment, Hash join\n"+
"   GLR-H   Global+Local Resegment, Hash join (no side = upstream isn't a join input)\n"+
"   O-H     Outer input, Local (no redistribution), Hash join\n"+
"   FLOW    Non-join pipeline connector (GROUPBY -> STORAGE etc)",
        cols: "v_internal.dc_explain_plans.path_line (suffix after '(PATH ID: N)')"
    },
    // v58: "Rows on Edge" formula on the edge popup DATA FLOW section.
    'F-EDGE-ROWS-01': {
        title: 'Rows on Edge',
        desc: 'Total rows that flowed across this edge, measured on the upstream '+
              '(child) side. Taken from the child path\'s card_metrics.rows, which '+
              'is the upstream output. For a detailed per-node breakdown (what each '+
              'node actually sent), see the PER-NODE LAST OPERATOR ROWS section '+
              'below - that\'s sourced from Q-EDGE-LASTOPROWS-01.',
        kind: 'formula',
        body:
"// rows_on_edge = child.card_metrics.rows  (upstream output)\n"+
"//\n"+
"// Earlier versions took max(child, parent) which picked up the\n"+
"// parent JOIN's output on small-upstream edges (e.g. a scalar\n"+
"// broadcast feeding a 500K-row join would show '500,000' - that\n"+
"// was the JOIN's output, not the edge traffic). Using child-only\n"+
"// matches the actual direction of data flow.",
        cols: "child.card_metrics.rows (derived from execution_engine_profiles counters)"
    },
    // v58: the new per-(path, node) operator-rows query.
    'Q-EDGE-LASTOPROWS-01': {
        title: 'Per-node last operator rows (edge upstream)',
        desc: 'For each edge, one row per node showing WHICH operator produced '+
              'the rows that crossed the edge on that node, and HOW MANY. The '+
              'picker prefers NetworkSend (the actual upstream output when the '+
              'edge crosses the network). If no NetworkSend ran on that node '+
              '(purely local edge), it falls back to the operator with the most '+
              'rows produced, tie-broken by the later operator_id.',
        kind: 'query',
        body:
"SELECT path_id, node_name, operator_name,\n"+
"       SUM(CASE counter_name WHEN 'rows produced' THEN counter_value ELSE NULL END) AS rows_produced,\n"+
"       MAX(operator_id) AS max_op_id\n"+
"FROM v_monitor.execution_engine_profiles\n"+
"WHERE transaction_id = :trxid AND statement_id = :stmtid\n"+
"GROUP BY 1, 2, 3\n"+
"\n"+
"-- Python then, per (path_id, node_name), picks the \"best\" row:\n"+
"--   1) NetworkSend with rows > 0  (networked upstream output)\n"+
"--   2) any op with rows > 0, max rows (tie-break: later operator_id)\n"+
"--   3) else the last op by operator_id, 0 rows (pass-through path)\n"+
"-- List is sorted by rows DESC so the popup surfaces skew at the top.",
        cols: "v_monitor.execution_engine_profiles.path_id, .node_name, .operator_name, "+
              ".operator_id, .counter_name, .counter_value"
    },
    // v71 NEW entries for the post-v70 philosophy-shift findings. Every
    // entry names a concrete knob (SQL the user can run) rather than
    // describing Vertica's internal monitoring topology.
    'F-RESOURCE-POOL-01': {
        title: 'Resource pool finding (v71)',
        desc: 'Fires when the profiled query ran in the default `general` '+
              'resource pool. For production workloads, a dedicated pool with '+
              'tuned MEMORYSIZE / MAXMEMORYSIZE / PLANNEDCONCURRENCY usually '+
              'beats `general`. The finding names the pool and suggests the '+
              'CREATE RESOURCE POOL DDL inline so the user has a one-copy-paste '+
              'remediation path.',
        kind: 'query',
        body:
"SELECT pool_name, COUNT(*) AS n\n"+
"FROM v_monitor.resource_acquisitions\n"+
"WHERE transaction_id = :trxid AND statement_id = :stmtid\n"+
"  AND pool_name IS NOT NULL\n"+
"GROUP BY 1\n"+
"ORDER BY 2 DESC\n"+
"LIMIT 1;",
        cols: "v_monitor.resource_acquisitions.pool_name"
    },
    'F-STATS-GAPS-01': {
        title: 'Sort-column statistics gaps finding (v71)',
        desc: 'Fires when >= 50% of sort columns (or >= 5 absolute) across the '+
              'projections this query used have statistics_type NULL/NONE/ROWCOUNT. '+
              'Missing stats are one of the biggest tuning levers Vertica exposes '+
              'because they drive broadcast-vs-resegment decisions. Finding names '+
              'the worst anchor table and gives the user ANALYZE_STATISTICS DDL.',
        kind: 'query',
        body:
"SELECT p.anchor_table_schema || '.' || p.anchor_table_name AS anchor_table,\n"+
"       pc.projection_name,\n"+
"       COUNT(*) AS sort_cols_total,\n"+
"       SUM(CASE WHEN pc.statistics_type IS NULL\n"+
"                  OR UPPER(pc.statistics_type) IN ('NONE','ROWCOUNT')\n"+
"                THEN 1 ELSE 0 END) AS no_stats\n"+
"FROM v_monitor.projection_usage p\n"+
"INNER JOIN v_catalog.projection_columns pc\n"+
"        ON p.projection_id = pc.projection_id\n"+
"WHERE p.transaction_id = :trxid AND p.statement_id = :stmtid\n"+
"  AND pc.sort_position >= 0\n"+
"GROUP BY 1, 2\n"+
"ORDER BY no_stats DESC;",
        cols: "v_catalog.projection_columns.statistics_type, .statistics_updated_timestamp, "+
              "v_monitor.projection_usage.projection_id"
    },
    'F-RETENTION-KNOB-01': {
        title: 'Data Collector retention finding (v71)',
        desc: 'Replaces v64-v70 F-EEP-GAP-01. When EEP or DPA coverage is '+
              'genuinely incomplete (< cluster_nodes), the finding names the '+
              'ONE knob a DBA can turn: SET_DATA_COLLECTOR_POLICY to widen the '+
              "retention window so counters don't age out before the profile "+
              'scrape. v71 intentionally stops explaining per-node replication '+
              'theory in user-facing text -- the knob is what matters.',
        kind: 'formula',
        body:
"-- Fire when:\n"+
"--   cluster_nodes > 0 AND (eep_nodes_seen < cluster_nodes\n"+
"--                          OR dpa_nodes_seen < cluster_nodes)\n"+
"-- Surface:\n"+
"SELECT SET_DATA_COLLECTOR_POLICY('ExecutionEngineProfiles', '86400', '256m');\n"+
"-- (24h retention, 256MB max)",
        cols: "derived from _measure_eep_coverage()"
    },
    // v71 note on RETIRED user-facing entries:
    //   F-EEP-GAP-01            -> superseded by F-RETENTION-KNOB-01
    //   F-STEP00B-CLUSTER-TRUTH-01 -> still in Step 99 QA appendix (Block 1)
    //                              and under ?debug=1, but no longer in
    //                              user-facing output.
    // Both entries are intentionally omitted from SRC_REGISTRY so the
    // help overlay cannot surface them to normal users.
    'F-STEP03B-SKEW-01': {
        title: 'Cross-node step-skew finding (v71 upgrade)',
        desc: 'Fires when the delta between fastest-node and slowest-node start '+
              'times on any execution step is >= 5 ms AND >= 5% of query duration. '+
              'v71 upgrade: finding now suggests concrete Vertica v_monitor probes '+
              '(host_resources, disk_storage, network_interfaces) instead of the '+
              'generic "check that node health" line v68 shipped with.',
        kind: 'query',
        body:
"WITH per_step AS (\n"+
"    SELECT execution_step,\n"+
"           MAX(\"time\") AS last_t, MIN(\"time\") AS first_t,\n"+
"           TIMESTAMPDIFF('millisecond', MIN(\"time\"), MAX(\"time\")) AS skew_ms\n"+
"    FROM v_internal.dc_query_executions\n"+
"    WHERE transaction_id = :trxid AND statement_id = :stmtid\n"+
"    GROUP BY 1\n"+
"    HAVING MAX(\"time\") != MIN(\"time\")\n"+
")\n"+
"SELECT execution_step, skew_ms, /* slowest_node */, /* fastest_node */\n"+
"FROM per_step ORDER BY skew_ms DESC LIMIT 1;",
        cols: "v_internal.dc_query_executions.execution_step, .node_name, .time"
    },
    'F-QUERY-NODE-TIMES-01': {
        title: 'Per-node query-level execution timing (v71.3)',
        desc: 'Per-node ExecutePlan:EEexecute duration drawn directly from '+
              'the qprof.sh pattern - dc_query_executions is cluster-wide and '+
              'always reliable, unlike execution_engine_profiles which is '+
              'per-node and eventually consistent. Fires as an info line on '+
              'every profile and as an actionable finding when slowest-vs-'+
              'fastest skew >= 20% of the fastest time AND >= 10 ms absolute. '+
              'Replaces what EEP would have shown per-path but at query-level, '+
              'available even when EEP did not replicate in time.',
        kind: 'query',
        body:
"SELECT node_name,\n"+
"       MAX(TIMESTAMPDIFF('millisecond', \"time\", completion_time)) AS execute_ms\n"+
"FROM v_internal.dc_query_executions\n"+
"WHERE transaction_id = :trxid AND statement_id = :stmtid\n"+
"  AND execution_step = 'ExecutePlan:EEexecute'\n"+
"GROUP BY 1\n"+
"ORDER BY 2 DESC;\n"+
"\n"+
"-- Pattern: qprof.sh \"Find the slower node for each execution step\"\n"+
"-- narrowed to the ExecutePlan:EEexecute step (actual query work,\n"+
"-- excludes planning/compile/finalize).",
        cols: "v_internal.dc_query_executions.node_name, .execution_step, .time, .completion_time"
    }
};

function renderSrcChip(label){
    // Compact (i) chip that opens the source inspector overlay for this label.
    return `<span class="src-chip" title="Show source for ${esc(label)}" `+
           `onclick="event.stopPropagation(); openSrcOverlay('${esc(label)}')">&#9432;</span>`;
}

function openSrcOverlay(label){
    const entry = SRC_REGISTRY[label];
    if(!entry){ return; }
    document.getElementById('srcLabel').textContent = label;
    document.getElementById('srcTitle').textContent = entry.title || label;
    document.getElementById('srcDesc').textContent  = entry.desc  || '';
    document.getElementById('srcKind').textContent  = (entry.kind || '').toUpperCase();
    document.getElementById('srcBody').textContent  = entry.body  || '';
    document.getElementById('srcCols').textContent  = entry.cols  || '';
    const overlay = document.getElementById('srcOverlay');
    overlay.classList.remove('help-mode'); // in case a help overlay was last shown
    overlay.classList.add('open');
}
function closeSrcOverlay(){
    const overlay = document.getElementById('srcOverlay');
    overlay.classList.remove('open');
    overlay.classList.remove('help-mode');
}

// =============================================================================
// v53: HELP_REGISTRY + renderHelpChip / openHelpOverlay
// Parallel to SRC_REGISTRY but aimed at users who don't live inside Vertica's
// system tables every day. Each entry is a short, plain-English explanation of
// what a value means and why it's on the screen. Rendered via a green "?" chip
// (distinct from the blue ⓘ src-chip) and displayed in the same overlay DOM
// with the Kind/Formula/Columns sections hidden.
// =============================================================================
const HELP_REGISTRY = {
    // ----- Top-level: how to read the tree, with dynamic observations for THIS query -----
    'tree-overview': {
        title: 'Query Execution Tree - How to read it',
        desc: "This graph shows how Vertica executed your query. Each card is a PATH - a discrete step in the plan (a scan, a join, a group-by, a sort, etc). The card at the TOP is the final step that produces your result; its children below are the inputs that feed it. Joins have TWO children side by side: the outer (driving) side on the LEFT, the inner (lookup) side on the RIGHT. Single-child steps (like GROUPBY->STORAGE ACCESS) stack vertically.\n\nHow to analyze a plan:\n1) Start at the bottom-summary 'Slowest Path' card - that's usually where to look first.\n2) Click any card to open its details panel on the right (PERFORMANCE / ESTIMATES / OPERATORS / EVENTS).\n3) Read the edge labels between cards: O-H / I-H = outer / inner side of a hash join; FLOW = non-join pipeline connector. Line color shows data distribution: gray solid = local, purple dashed = broadcast, orange dashed = resegment.\n4) Orange/red cards (SLOW / CRITICAL) got flagged by the scoring rules - start with those. Green/blue cards (FAST / MODERATE) are fine.\n5) Watch for estimate vs actual mismatches, data skew across nodes, and spill events - each has its own help chip.",
        // v56: dynamic keyword tells openHelpOverlay() to append the server's
        // per-graph observation list (summary.tree_analysis) after the static
        // description above. Works fully offline - observations are built from
        // pre-written Python templates in _build_tree_analysis(), not an LLM.
        dynamic: 'tree_analysis'
    },
    // ----- Hero -----
    'hero-total-duration': {
        title: 'Total Duration',
        desc: "Wall-clock time Vertica spent on this query, from when it was received to when the last row was returned. Pulled from query_profiles.query_duration_us. Includes planning, execution, and any waits. This is the single number you'd quote if someone asked 'how long did the query take?'."
    },
    'hero-total-rows': {
        title: 'Total Rows',
        desc: "Total rows read from storage across every table the query touched. Comes from the 'proc_rows' counter on Scan operators summed across nodes. Big numbers here often point to missing filters or over-broad joins."
    },
    'hero-peak-memory': {
        title: 'Peak Memory',
        desc: "Cluster-wide peak memory the query held, shown as MAX across nodes (not a sum, since every node usually holds a similar amount during execution). Sourced from v_monitor.resource_acquisitions.memory_inuse_kb - this is the actual grant from the resource pool, always populated cluster-wide (unlike per-path memory columns which are commonly NULL). Hover to see the per-node breakdown: an unusual spread across nodes can indicate data skew."
    },
    'hero-transaction-id': {
        title: 'Transaction ID',
        desc: "Unique ID Vertica assigned to this transaction. Use it to look up the query in system tables like query_requests, execution_engine_profiles, query_events. Combined with statement_id it uniquely identifies this exact run."
    },
    'hero-statement-id': {
        title: 'Statement ID',
        desc: "Which statement in the transaction this is. A single transaction can contain many statements; each one has its own plan and profiling data."
    },
    'hero-label': {
        title: 'Query Label',
        desc: "Optional label you can attach to a query using the Vertica /*+label(...)*/ hint. Helpful for grouping related queries in monitoring. Defaults to 'qprof' if none was set."
    },
    'hero-version': {
        title: 'Vertica Version',
        desc: "Vertica server version that executed this query. Useful when comparing profiles across upgrades or when a Vertica bug is suspected."
    },
    // ----- Card -----
    'card-path-id': {
        title: 'Path ID',
        desc: "Vertica splits each query plan into numbered PATHS, one per major operation (scan, join, group-by, sort, etc). Lower path IDs are closer to the final result; higher IDs are leaves. Path -1 is the root / SELECT output wrapper."
    },
    'card-status': {
        title: 'Status (Fast / Moderate / Slow / Critical)',
        desc: "Color flag for how this path behaved. Green Fast = cheap and clean; Blue Moderate = fine; Orange Slow = worth a look; Red Critical = took a meaningful share of query time or tripped a negative event (spill, bad stats, resegment-many-rows, etc). Click ⓘ for the exact rule."
    },
    'card-exec-time': {
        title: 'Card time (ms)',
        desc: "The millisecond number on the card. It's the HOTTEST operator on this path, with its 'execution time (us)' counter summed across every node. Think of it as 'how much CPU work the busiest operator on this step did'. It's NOT wall-clock time - see Clock Time inside the popup for that."
    },
    'card-rows': {
        title: 'Rows',
        desc: "Number of rows this path produced or handled. Comes primarily from produced_rows or received_rows on the path's operators. A huge gap between the estimate (what the optimizer guessed) and this actual number usually means statistics are stale."
    },
    'card-cost': {
        title: 'Cost',
        desc: "Optimizer's cost estimate for this step, taken from the EXPLAIN plan. Vertica uses its own cost unit (not ms, not rows) - it's a relative score the planner uses to pick a plan. Bigger = heavier. Values suffixed with K, M, B are thousands/millions/billions of cost units."
    },
    'card-memory': {
        title: 'Memory (MB)',
        desc: "Memory this path used during execution, in megabytes. v72: sourced from execution_engine_profiles 'peak memory requested (bytes)' - the modern non-deprecated counter that is actually populated in recent Vertica versions (the old 'memory reserved' and 'memory allocated' counters are deprecated per Vertica docs and often return NULL). Falls back to 'peak memory capacity (bytes)' or the deprecated counters only when the primary is missing. Hash joins, group-by-hash, and big sorts dominate here. If a path's memory is surprisingly large, it may have spilled to disk. Cluster-wide total (query-level peak) is shown in the hero Peak Memory tile."
    },
    'card-execute-on': {
        title: 'EXECUTE ON: N nodes, MIN: X, MAX: Y',
        desc: "How many cluster nodes participated in this path, plus the fastest and slowest per-node execution times. v72: MIN and MAX are both shown so cross-node skew on this specific path is visible at a glance - if MIN and MAX are far apart, one node is doing more work than its peers (data skew). Times auto-format to seconds when >= 1s for readability. When per-path per-node data isn't captured (short paths, EEP retention), the card falls back to path-level running_time from query_plan_profiles (cluster-wide) and marks it '(plan)'. Click ⓘ for the SQL behind this."
    },
    'card-badges': {
        title: 'Event badges',
        desc: "Notable things Vertica recorded about this path. Red = bad (spill, bad stats, over-resegment), Orange = caution (SIP fallback, no group-by pushdown), Green = good (predicate pushdown, partition pruning). Hover a badge to see the exact event_type. v73: to keep cards compact, only the first 2 badges are shown inline; additional badges collapse into a '+N more' chip. Click the card to open the popup - the full event list is in the Query Events section there. Click ⓘ for the full classification."
    },
    // ----- Popup -----
    'popup-pct-of-query': {
        title: '% of Query',
        desc: "How much of the query's total card-exec-time was spent on this path. Not a wall-clock share (see Clock Time for that). A path above 15-20% is usually worth investigating first."
    },
    'popup-exec-time': {
        title: 'Exec Time',
        desc: "Same number shown on the card: hottest operator's 'execution time (us)' summed across nodes. Good proxy for 'how much CPU this step burned'. For the true wall-clock path time, look at Clock Time below."
    },
    'popup-clock-time': {
        title: 'Clock Time',
        desc: "Wall-clock running time of this PATH, including any waits or stalls (network, coordination, upstream operator delays). From query_plan_profiles.running_time. If Clock Time is much bigger than Exec Time, the path spent a lot of time waiting rather than computing.\n\nNote: Clock Time shown on INDIVIDUAL OPERATORS in the OPERATORS section is a different value - it's 'clock time (us)' from execution_engine_profiles, summed across all threads on all nodes. So an operator running 6 threads on 5 nodes for 10 ms of real wall-clock will report 300 ms (6*5*10). Not every operator populates this counter (NetworkRecv, NetworkSend, StorageUnion typically report 0 and are hidden); operators that do (Scan, GroupByPipe, ParallelUnion) can show surprisingly large values. Treat it as 'total thread-seconds spent', not elapsed real time."
    },
    'popup-rows': {
        title: 'Rows',
        desc: "Rows this path produced. Big mismatches vs. the optimizer's estimate (shown in EXPLAIN) almost always point to out-of-date statistics. Run ANALYZE_STATISTICS on the table to help."
    },
    'popup-cost': {
        title: 'Cost',
        desc: "Optimizer's estimated cost for this step, from EXPLAIN. Vertica's internal unit, no ms/rows meaning - just a number the optimizer uses to pick plans."
    },
    'popup-memory': {
        title: 'Memory',
        desc: "Memory this path used (MB). Taken from 'memory reserved (bytes)' in execution_engine_profiles, falling back to 'memory allocated (bytes)'. Big hash joins, hash group-bys, and sorts dominate this. Watch for very large values - if the path spilled, you'll see a WOS_SPILL or GROUP_BY_SPILLED event too."
    },
    'popup-read-sent': {
        title: 'Read / Sent',
        desc: "MB read from disk (left) / MB sent across the network (right) for this path. High sent values on Resegment or Broadcast edges are normal for distributed joins but can become a bottleneck on large tables."
    },
    'popup-operators': {
        title: 'Operators',
        desc: "Every operator that ran on this path, with its own exec time, row count, and memory. Useful for drilling past the card's one summary number - you can see which specific operator (Scan, Join, NetworkSend, etc) was the expensive one."
    },
    'popup-events': {
        title: 'Query Events',
        desc: "Everything Vertica flagged about this path. A single event can fire on multiple nodes (one row per node in the system table), so v53 collapses duplicates and shows 'triggered on N nodes' when the same event fired on more than one."
    },
    // ----- Bottom summary -----
    'summary-slowest-path': {
        title: 'Slowest Path',
        desc: "The path with the largest wall-clock running_time in this query. Usually the first place to look when tuning. The percentage is its share of total path running time. Click ⓘ for the exact formula."
    },
    'summary-storage-scans': {
        title: 'Storage Scans',
        desc: "Count of STORAGE ACCESS paths and the total rows they read from projections. Big scans often dominate query time - if this number is surprising, check whether filters can be pushed down or a better projection can be used."
    },
    'summary-joins': {
        title: 'Join Operations',
        desc: "Count of JOIN paths in the plan and their combined wall-clock time. If joins dominate, consider whether the join order, distribution (BROADCAST vs RESEGMENT vs LOCAL), or projection segmentation could be improved."
    },
    // ----- Edge popup (v58) -----
    'edge-distribution': {
        title: 'Edge Distribution',
        desc: "How data moves from this child path up to the parent JOIN across the cluster.\n\n"+
              "- Local: data stays on the same node; no network traffic. Cheapest.\n"+
              "- Broadcast: every node gets a full copy of the child's rows. Cheap only when the child is small.\n"+
              "- Local Resegment (LR): data is reshuffled within each node by the join key. Cheaper than Global Resegment.\n"+
              "- Global+Local Resegment (GLR): full cross-cluster resegment, then a local resegment. Expensive but unavoidable when the child isn't already segmented by the join key.\n"+
              "- Resegment (R): plain resegment across the cluster.\n\n"+
              "Distribution is inferred from the parent JOIN's plan-line suffix (e.g. 'Inner (BROADCAST)' or 'Outer (RESEGMENT)(LOCAL ROUND ROBIN)'). Click ⓘ for the exact mapping rules."
    },
    'edge-join-position': {
        title: 'Join Position (Outer / Inner)',
        desc: "In a Vertica JOIN, the OUTER (driving) side is the one the join iterates over and probes into the inner side. The INNER (probed) side is what the join builds its lookup structure from - for HASH joins that's the hash table. Swapping the two sides is a common tuning tactic when the inner side is unexpectedly large."
    },
    'edge-modifiers': {
        title: 'Raw Plan Modifiers',
        desc: "The exact parenthesized modifier keywords Vertica printed on the parent JOIN's plan line for this child's side (BROADCAST, RESEGMENT, LOCAL RESEGMENT, LOCAL ROUND ROBIN, GLOBAL RESEGMENT). Shown raw so you can cross-reference with the plan text. The Distribution field above collapses these into the canonical code."
    },
    'edge-rows': {
        title: 'Rows on Edge',
        desc: "How many rows flowed across this edge, measured on the upstream side. For a Broadcast edge this is the rows each node received. For Local/Resegment edges it's the total rows from the child path. Large rows on a Broadcast edge combined with many nodes is a classic cause of network-bound query time."
    },
    'edge-per-node-rows': {
        title: 'Per-node Last Operator Rows',
        desc: "For each node in the cluster, the exact operator that produced the rows feeding into this edge on that node, and how many rows it produced. If the numbers per node are roughly equal, work is spread evenly; if one node has much more (or much less), you have data skew - the smallest/largest numbers reveal where.\n\nThe operator shown is the LAST operator on the upstream side of the edge: NetworkSend for edges that cross the network (Broadcast, Resegment), or the last local operator (StorageUnion, ParallelUnion, Scan, etc) for Local edges.\n\nWhen the upstream is an initiator-only operation (like a GROUP BY NOTHING aggregation), only one node will show rows and the others will be zero or missing - that's expected."
    },
    // v61 (F-LEGEND-KEYS-01): master glossary for every letter that can
    // appear on a tree edge. Each edge is labeled with 1-3 groups:
    //   <JoinSide>-<Distribution>-<JoinKind>   e.g. I-B-H, O-LR-H, GLR-H, O-H, FLOW
    // The glossary explains each letter in plain language and - the part
    // that matters for tuning - tells you when each code is bad and what
    // the preferred alternative is.
    'legend-keys': {
        title: 'Reading the edge labels',
        // v62: rich HTML. Accent-colored section bars, code badges for
        // letter codes, and collapsible "When it matters" tuning boxes
        // so novice users can read the big picture first and drill into
        // tuning only when they need it.
        descHtml:
            '<style>'+
              '.lkx{font-size:13px;line-height:1.6;color:#e7f0ff;}'+
              '.lkx p{margin:0 0 14px;}'+
              '.lkx .fmt-banner{background:rgba(14,30,58,.55);border:1px solid rgba(126,154,214,.25);'+
                'border-radius:8px;padding:14px;margin:4px 0 20px;text-align:center;'+
                'font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;font-size:15px;'+
                'letter-spacing:.02em;}'+
              '.lkx .g-pos{color:#74d9ff;font-weight:800;}'+
              '.lkx .g-dist{color:#ff9f43;font-weight:800;}'+
              '.lkx .g-kind{color:#8ed788;font-weight:800;}'+
              '.lkx .dash{opacity:.42;margin:0 8px;}'+
              '.lkx .section{border-left:3px solid #7e9ad6;padding:2px 0 2px 16px;margin:0 0 20px;}'+
              '.lkx .section.pos{border-left-color:#74d9ff;}'+
              '.lkx .section.dist{border-left-color:#ff9f43;}'+
              '.lkx .section.kind{border-left-color:#8ed788;}'+
              '.lkx .section.flow{border-left-color:#90a4cf;}'+
              '.lkx .section h3{margin:0 0 4px;font-size:12px;text-transform:uppercase;'+
                'letter-spacing:.08em;font-weight:800;}'+
              '.lkx .section.pos h3{color:#74d9ff;}'+
              '.lkx .section.dist h3{color:#ffad66;}'+
              '.lkx .section.kind h3{color:#8ed788;}'+
              '.lkx .section.flow h3{color:#90a4cf;}'+
              '.lkx .section .sub{color:#9aa9c7;font-size:11.5px;margin-bottom:10px;'+
                'text-transform:uppercase;letter-spacing:.04em;}'+
              '.lkx .row{display:grid;grid-template-columns:44px 1fr;gap:12px;align-items:start;'+
                'padding:6px 0;border-bottom:1px dashed rgba(126,154,214,.12);}'+
              '.lkx .row:last-of-type{border-bottom:0;}'+
              '.lkx .row .letter{text-align:center;}'+
              '.lkx .row .letter code{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;'+
                'background:rgba(5,12,25,.65);color:#cce7ff;font-weight:800;font-size:13px;'+
                'padding:3px 7px;border-radius:4px;border:1px solid rgba(126,154,214,.28);'+
                'display:inline-block;min-width:22px;}'+
              '.lkx .row .letter code.good{color:#a8eab0;border-color:rgba(63,185,80,.45);}'+
              '.lkx .row .letter code.bad{color:#ffb3b8;border-color:rgba(248,81,73,.45);}'+
              '.lkx .row .body{font-size:12.5px;line-height:1.55;}'+
              '.lkx .row .body b{color:#eef4ff;font-weight:700;}'+
              '.lkx .row .body em{color:#9aa9c7;font-style:normal;}'+
              '.lkx .tuning{background:rgba(255,173,51,.08);border:1px solid rgba(255,173,51,.28);'+
                'border-radius:7px;padding:11px 14px;margin-top:12px;}'+
              '.lkx .tuning .title{color:#ffc17a;font-weight:800;font-size:11px;'+
                'text-transform:uppercase;letter-spacing:.1em;margin-bottom:6px;}'+
              '.lkx .tuning ul{margin:0;padding-left:18px;font-size:12px;line-height:1.65;}'+
              '.lkx .tuning li{margin-bottom:5px;}'+
              '.lkx .tuning li b{color:#fff;}'+
              '.lkx .tuning p{margin:0;font-size:12px;line-height:1.55;}'+
              '.lkx .pill-good{display:inline-block;background:rgba(63,185,80,.16);color:#9aeaa3;'+
                'border:1px solid rgba(63,185,80,.35);border-radius:10px;padding:0 7px;font-size:11px;'+
                'font-weight:700;margin-left:6px;}'+
              '.lkx .pill-bad{display:inline-block;background:rgba(248,81,73,.14);color:#ffb5ba;'+
                'border:1px solid rgba(248,81,73,.38);border-radius:10px;padding:0 7px;font-size:11px;'+
                'font-weight:700;margin-left:6px;}'+
              '.lkx kbd{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;'+
                'background:rgba(5,12,25,.55);color:#cce7ff;font-weight:700;font-size:11.5px;'+
                'padding:1px 5px;border-radius:3px;border:1px solid rgba(126,154,214,.22);}'+
            '</style>'+

            '<div class="lkx">'+
              '<p>Every edge in the tree carries a short bracketed code like '+
                '<kbd>[I-B-H]</kbd>, <kbd>[O-LR-H]</kbd>, <kbd>[GLR-H]</kbd>, or <kbd>[FLOW]</kbd>. '+
                'The format is three groups separated by dashes:</p>'+

              '<div class="fmt-banner">'+
                '<span class="g-pos">Join Position</span>'+
                '<span class="dash">&ndash;</span>'+
                '<span class="g-dist">Distribution</span>'+
                '<span class="dash">&ndash;</span>'+
                '<span class="g-kind">Join Kind</span>'+
              '</div>'+

              '<p style="color:#9aa9c7;font-size:12px;">Any group may be omitted when Vertica collapses it '+
                '(plain Local edges, non-join pipeline edges).</p>'+

              // Section 1 - Join Position
              '<div class="section pos">'+
                '<h3>1. Join Position</h3>'+
                '<div class="sub">Which input is this into the parent JOIN?</div>'+
                '<div class="row"><div class="letter"><code>O</code></div><div class="body">'+
                  '<b>Outer.</b> The driving / probe side. Vertica iterates over this side.</div></div>'+
                '<div class="row"><div class="letter"><code>I</code></div><div class="body">'+
                  '<b>Inner.</b> The build side. For a hash join, the hash table is built from this.</div></div>'+
                '<div class="row"><div class="letter"><em>none</em></div><div class="body">'+
                  '<em>Edge is not a JOIN input (e.g. GROUPBY &rarr; STORAGE).</em></div></div>'+
                '<div class="tuning">'+
                  '<div class="title">Tuning tip</div>'+
                  '<p>If the <b>Inner</b> side is unexpectedly large, the hash table may not fit in memory '+
                    'and can spill. Swap sides via projection design, or switch to Merge Join with '+
                    'pre-sorted inputs.</p>'+
                '</div>'+
              '</div>'+

              // Section 2 - Distribution
              '<div class="section dist">'+
                '<h3>2. Distribution</h3>'+
                '<div class="sub">How data moves across the cluster.</div>'+
                '<div class="row"><div class="letter"><code class="good">none</code></div><div class="body">'+
                  '<b>Local.</b> Data stays on the same node. Cheapest. <em>Always your target.</em>'+
                  '<span class="pill-good">IDEAL</span></div></div>'+
                '<div class="row"><div class="letter"><code>B</code></div><div class="body">'+
                  '<b>Broadcast.</b> Every node gets a full copy of the upstream rows. '+
                  'Cheap <b>only</b> when upstream is small (tens of rows). '+
                  'Bad when &gt;100K rows cross &mdash; triggers <kbd>RESEGMENTED_MANY_ROWS</kbd>.</div></div>'+
                '<div class="row"><div class="letter"><code>LR</code></div><div class="body">'+
                  '<b>Local Resegment.</b> Rows reshuffled <b>within each node</b> only. '+
                  'No cross-cluster traffic. Cheap.</div></div>'+
                '<div class="row"><div class="letter"><code>R</code></div><div class="body">'+
                  '<b>Resegment.</b> Rows reshuffled across the entire cluster by the join key. '+
                  'Moderate cost.</div></div>'+
                '<div class="row"><div class="letter"><code class="bad">GLR</code></div><div class="body">'+
                  '<b>Global + Local Resegment.</b> Full cross-cluster resegment plus a local one. '+
                  '<b>The most expensive distribution.</b> <span class="pill-bad">COSTLY</span></div></div>'+
                '<div class="tuning">'+
                  '<div class="title">Tuning tips</div>'+
                  '<ul>'+
                    '<li><b>Broadcast with large upstream</b> &rarr; Segment the other side on the join key '+
                      'so Vertica picks Resegment or Local.</li>'+
                    '<li><b>GLR</b> &rarr; Neither projection is segmented by the join key. Create a '+
                      'projection segmented by the join key on at least one of the two tables '+
                      '(usually the larger one).</li>'+
                    '<li><b>Aim for Local edges</b> on the hottest joins by matching projection '+
                      'segmentation to join keys. Often the single biggest tuning win.</li>'+
                  '</ul>'+
                '</div>'+
              '</div>'+

              // Section 3 - Join Kind
              '<div class="section kind">'+
                '<h3>3. Join Kind</h3>'+
                '<div class="sub">Which physical join operator Vertica chose.</div>'+
                '<div class="row"><div class="letter"><code>H</code></div><div class="body">'+
                  '<b>Hash.</b> Most common. Builds a hash table on the Inner side. '+
                  'Fast when Inner fits in memory.</div></div>'+
                '<div class="row"><div class="letter"><code class="good">M</code></div><div class="body">'+
                  '<b>Merge.</b> Requires <b>both sides pre-sorted</b> on the join key. '+
                  'Very cheap and memory-light &mdash; the ideal for very large joins, '+
                  'but needs projection design support.<span class="pill-good">EFFICIENT</span></div></div>'+
                '<div class="row"><div class="letter"><code>P</code></div><div class="body">'+
                  '<b>Pipelined.</b> Streams tuples through without materializing. Rare.</div></div>'+
                '<div class="row"><div class="letter"><code>F</code></div><div class="body">'+
                  '<b>Filter.</b> Semi / anti-semi filter join '+
                  '(<kbd>IN</kbd> / <kbd>EXISTS</kbd> / <kbd>NOT IN</kbd>). Normal.</div></div>'+
                '<div class="row"><div class="letter"><code class="bad">X</code></div><div class="body">'+
                  '<b>Cross.</b> Cartesian product (no join predicate). '+
                  '<b>Almost always a bug.</b> <span class="pill-bad">CHECK QUERY</span></div></div>'+
                '<div class="tuning">'+
                  '<div class="title">Tuning tips</div>'+
                  '<ul>'+
                    '<li><b>Hash</b> + <kbd>MEMORY_LIMIT_HIT</kbd> / <kbd>JOIN_SPILLED</kbd> on this path &rarr; '+
                      'Inner didn&#x2019;t fit in RAM. Reduce Inner (better filter pushdown, narrower '+
                      'projection), increase resource pool memory, or refactor to Merge Join.</li>'+
                    '<li><b>Hash on a very large join</b> &rarr; Create sorted projections on the join key '+
                      'so Vertica can use Merge Join.</li>'+
                    '<li><b>Cross (X)</b> &rarr; Check your query. Almost certainly a missing '+
                      '<kbd>ON</kbd> / <kbd>WHERE</kbd> predicate.</li>'+
                  '</ul>'+
                '</div>'+
              '</div>'+

              // FLOW
              '<div class="section flow">'+
                '<h3>Special: FLOW</h3>'+
                '<p style="margin:0;font-size:12px;">The edge is a non-join pipeline connector '+
                  '(e.g. <kbd>GROUPBY &rarr; STORAGE ACCESS</kbd>). '+
                  'No join position and no distribution applies.</p>'+
              '</div>'+
            '</div>'
    }
};

function renderHelpChip(key){
    // Compact (?) chip that opens the friendly explanation overlay for this value.
    // Distinct from renderSrcChip(): green background, "?" glyph. Intended for
    // users who aren't deep in Vertica system tables and just want to know what
    // a number on the screen means.
    return `<span class="help-chip" title="What does this mean?" `+
           `onclick="event.stopPropagation(); openHelpOverlay('${esc(key)}')">?</span>`;
}

function openHelpOverlay(key){
    const entry = HELP_REGISTRY[key];
    if(!entry){ return; }
    document.getElementById('srcLabel').textContent = 'HELP';
    document.getElementById('srcTitle').textContent = entry.title || key;
    // v56: render description as HTML so line breaks (\n) become <br>
    // and dynamic observation lists render as proper bullets.
    // v62: registry entries may now supply a `descHtml` field with
    // pre-authored rich HTML (headings, colored badges, tuning boxes)
    // for content that plain text can't express. The content in
    // descHtml is ALWAYS authored by us in HELP_REGISTRY -- never
    // user-supplied -- so innerHTML is safe here.
    const descEl = document.getElementById('srcDesc');
    descEl.innerHTML = '';
    const staticDiv = document.createElement('div');
    if (entry.descHtml) {
        staticDiv.innerHTML = entry.descHtml;
    } else {
        staticDiv.innerHTML = esc(entry.desc || '').replace(/\n/g, '<br>');
    }
    descEl.appendChild(staticDiv);
    // v56: dynamic tail. If the entry declares a dynamic key, pull the list
    // from state.dynamicHelp and render as a titled bullet list. Built by
    // the server so works fully offline (no LLM).
    if (entry.dynamic){
        const items = (state.dynamicHelp || {})[entry.dynamic] || [];
        if (items.length){
            const hr = document.createElement('hr');
            hr.style.cssText = 'border:0;border-top:1px solid rgba(126,154,214,.22);margin:14px 0 10px;';
            descEl.appendChild(hr);
            const h = document.createElement('div');
            h.style.cssText = 'color:#74d9ff;font-weight:800;letter-spacing:.04em;text-transform:uppercase;font-size:11px;margin-bottom:8px;';
            h.textContent = 'About this specific query';
            descEl.appendChild(h);
            const ul = document.createElement('ul');
            ul.style.cssText = 'margin:0;padding-left:18px;';
            items.forEach(item => {
                const li = document.createElement('li');
                li.style.cssText = 'margin-bottom:6px;line-height:1.5;';
                li.textContent = item;
                ul.appendChild(li);
            });
            descEl.appendChild(ul);
        }
    }
    // Help entries have no Kind/Formula/Columns - hide those sections.
    document.getElementById('srcKind').textContent  = '';
    document.getElementById('srcBody').textContent  = '';
    document.getElementById('srcCols').textContent  = '';
    const overlay = document.getElementById('srcOverlay');
    overlay.classList.add('open');
    overlay.classList.add('help-mode');
}

// Patch closeSrcOverlay via listener below (in DOMContentLoaded) to also clear help-mode.

// -----------------------------------------------------------------------------
// F-CARD-BADGES-01: canonical event_type -> badge definition.
// Source: "System Tables for Query Performance" doc, tables
// "Negative Optimizer Events" + "Positive Optimizer Events" +
// "Negative Execution Engine Events" + "Positive Execution Engine Events".
// -----------------------------------------------------------------------------
const CANONICAL_EVENT_CATALOG = {
    // Negative optimizer
    'DELETE_WITH_NON_OPTIMIZED_PROJECTION': { kind:'bad',  short:'DELETE NON-OPT PROJ' },
    'MEMORY_LIMIT_HIT':                     { kind:'bad',  short:'OPT MEM LIMIT'       },
    'NO_HISTOGRAM':                         { kind:'bad',  short:'NO HISTOGRAM'        },
    // Positive optimizer
    'GROUPBY_PUSHDOWN':                     { kind:'good', short:'GROUPBY PUSHDOWN'    },
    'NODE_PRUNING':                         { kind:'good', short:'NODE PRUNING'        },
    'TRANSITIVE_PREDICATE':                 { kind:'good', short:'TRANS. PREDICATE'    },
    'NO_GROUPBY_PUSHDOWN':                  { kind:'warn', short:'NO GROUPBY PD'       },
    // Negative execution
    'GROUP_BY_SPILLED':                     { kind:'bad',  short:'GROUPBY SPILLED'     },
    'JOIN_SPILLED':                         { kind:'bad',  short:'JOIN SPILLED'        },
    'RESEGMENTED_MANY_ROWS':                { kind:'bad',  short:'RESEG MANY ROWS'     },
    'WOS_SPILL':                            { kind:'bad',  short:'WOS SPILL'           },
    // Positive execution
    'GROUP_BY_PREPASS_FALLBACK':            { kind:'good', short:'PREPASS FALLBACK'    },
    'MERGE_CONVERTED_TO_UNION':             { kind:'good', short:'MERGE->UNION'        },
    'PARTITIONS_ELIMINATED':                { kind:'good', short:'PARTITIONS ELIM'     },
    'RLE_OVERRIDDEN':                       { kind:'good', short:'RLE OVERRIDDEN'      },
    'SEQUENCE CACHE REFILLED':              { kind:'warn', short:'SEQ REFILL'          },
    'SIP_FALLBACK':                         { kind:'warn', short:'SIP FALLBACK'        },
    'SMALL_MERGE_REPLACED':                 { kind:'good', short:'SMALL MERGE REPL'    }
};

function canonicalEventBadge(ev){
    if(!ev) return null;
    const raw = ev.event_type || ev.type || '';
    const key = String(raw).toUpperCase().trim();
    const hit = CANONICAL_EVENT_CATALOG[key];
    if(hit) return { kind: hit.kind, label: hit.short, raw: key };
    // Unknown event_type: keep visible but neutral-color.
    if(key) return { kind: 'warn', label: key.replace(/_/g,' ').slice(0, 22), raw: key };
    return null;
}

// Distill a list of events into at most three displayable badges. Duplicates
// collapsed on event_type; severity ordering bad > warn > good.
function deriveBadges(events){
    if(!Array.isArray(events) || events.length === 0) return [];
    const seen = new Map();
    for(const ev of events){
        const b = canonicalEventBadge(ev);
        if(!b) continue;
        if(!seen.has(b.raw)) seen.set(b.raw, b);
    }
    const sev = { bad:0, warn:1, good:2 };
    return Array.from(seen.values())
        .sort((a,b)=>(sev[a.kind] ?? 9)-(sev[b.kind] ?? 9))
        .slice(0, 3);
}

// v53 fix 2 + v73 (Maya's image-2 feedback): dedupEventsForPopup.
// v_monitor.query_events returns one row per (node, operator instance) that
// tripped an event, so a single path-level event like GROUP_BY_PREPASS_FALLBACK
// on a 5-node cluster with 2 operator-instances/node can repeat up to 10 times.
//
// v53 dedup was too strict: it included event_details AND operator_name in the
// key, but both fields vary across raw rows (details often contain per-node or
// per-operator sub-info). That left 8+ "identical-looking" GROUP_BY_PREPASS_FALLBACK
// cards visible in the popup (Maya screenshot: 12 groups from 25 raw rows).
//
// v73 loosens the key to (event_type, event_description, suggested_action) and
// tracks the SET of distinct node_names rather than a raw counter. Popup now
// shows "triggered on N nodes" using distinct-node count, and flags "M instances"
// when raw count exceeds node count (multiple operator-instances per node).
function dedupEventsForPopup(events){
    if(!Array.isArray(events) || events.length === 0) return [];
    const groups = new Map();
    const order = [];
    for(const ev of events){
        const key = [
            String(ev.event_type || ''),
            String(ev.event_description || ''),
            String(ev.suggested_action || '')
        ].join('\u241f'); // unit-separator char
        if(!groups.has(key)){
            groups.set(key, {
                ev: ev,
                count: 1,
                nodes: new Set([String(ev.node_name || '?')])
            });
            order.push(key);
        } else {
            const g = groups.get(key);
            g.count += 1;
            g.nodes.add(String(ev.node_name || '?'));
        }
    }
    return order.map(k => {
        const g = groups.get(k);
        return {
            ...g.ev,
            _count: g.count,               // raw row count
            _nodeCount: g.nodes.size,      // distinct-node count (v73: this is what "N nodes" should display)
            _nodes: Array.from(g.nodes)    // for debug/tooltip
        };
    });
}

// v71 Maya-philosophy: state.debug gates the v69/v70 internal-plumbing UI
// (Plan-vs-Monitoring micro-table, amber "partial" tag, amber coverage
// banner, Step 00b-style cluster dump). When false (the default, for
// normal users), none of that renders - only actionable content does.
// Flipped true by appending `?debug=1` to the graph-page URL. Read once
// at module load; a deep reload is required to toggle. No UI affordance
// for the flag since users shouldn't flip it.
const __urlParams = (() => {
    try { return new URLSearchParams(window.location.search || ''); }
    catch (e) { return new URLSearchParams(''); }
})();
// v71.4 (Maya feedback): default the tree/popup zoom to 80% so that large
// plan trees (typical for analytic queries with 15+ paths, joins and
// group-bys) fit in the viewport without horizontal scrolling. Users who
// want more detail can zoom in via the +/- buttons. Zoom indicator shows
// "80%" on first load; Reset returns here.
const state={scale:0.8,nodes:[],edges:[],activeType:'node',activeIndex:0,lastAnchor:null,popupManuallyPositioned:false,debug:(__urlParams.get('debug')==='1')};
function esc(v){return String(v??'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;').replace(/'/g,'&#39;')}
function formatInt(v){const n=Number(v||0); return Number.isFinite(n)?n.toLocaleString():'0'}
function formatCompactInt(v){
    const n=Number(v||0);
    if(!Number.isFinite(n)) return '0';
    const abs=Math.abs(n);
    if(abs>=1e12) return `${(n/1e12).toFixed(1)}T`;
    if(abs>=1e9) return `${(n/1e9).toFixed(1)}B`;
    if(abs>=1e6) return `${(n/1e6).toFixed(1)}M`;
    if(abs>=1e3) return `${(n/1e3).toFixed(1)}K`;
    return `${Math.round(n)}`;
}
function formatDurationUs(us){const sec=Number(us||0)/1000000; if(sec>=60) return `${sec.toFixed(2)}s`; if(sec>=1) return `${sec.toFixed(3)}s`; return `${(sec*1000).toFixed(2)}ms`;}
function formatSummarySecondsFromUs(us){
    const sec=Number(us||0)/1000000;
    if(!Number.isFinite(sec)) return '0.00s';
    return `${sec.toFixed(2)}s`;
}
function perfLabel(node){const s=node.status||'neutral'; if(s==='good') return 'FAST'; if(s==='bad') return 'CRITICAL'; if(s==='warn') return 'SLOW'; return 'MODERATE';}
function cleanTitleText(t){return String(t||'').replace(/^[-+|> ]+/,'').replace(/\s+/g,' ').replace(/(\(PATH ID:\s*\d+\))(?:\s*\[PATH ID:\s*\d+\])+/ig,'$1').trim();}
function truncatedTitle(t){const c=cleanTitleText(t); return c.length>34?c.slice(0,34)+'…':c;}
function detailTitle(t){return cleanTitleText(t);}
function nodeSubtitle(node){ return String(node.card_subtitle||'').trim(); }
function prettyTitleParts(t){const clean=cleanTitleText(t); const m=clean.match(/^(.*?)(\s*\(PATH ID:\s*\d+\).*)$/i); return {title:(m?m[1]:clean).trim(), sub:(m?m[2]:'').trim()};}
function nodeProgress(node){const maxExec=Math.max(...state.nodes.map(n=>Number((n.card_metrics||{}).exec_time_ms||0)),1); const cur=Number((node.card_metrics||{}).exec_time_ms||0); return Math.max(6,Math.min(100,(cur/maxExec)*100));}
// v57 fix: clamp widened to [0.50, 1.80] to match the state.scale range set
// by the zoom +/- buttons. Previous clamp [0.60, 1.60] left users wondering
// why the first one or two zoom clicks near the extremes changed the cards
// but left the popup text unchanged ("non-linear" zoom). Now every click
// from 0.5x to 1.8x moves the popup in lockstep with state.scale.
function popupScaleFont(){return Math.max(.50, Math.min(1.80, state.scale));}
// v82 item 6: one-line toggler for the bottom-left floating legend. Flips
// the .collapsed class. Event handler is wired inline in the HTML via
// onclick=toggleFloatingLegend(event); the event param is there so future
// expansions (e.g. "click the caret to close but click the body to do
// nothing") have a hook, but for now any click on the box toggles.
function toggleFloatingLegend(ev){
    const el = document.getElementById('floatingLegend');
    if (!el) return;
    el.classList.toggle('collapsed');
    // Prevent the toggle from bubbling into the tree-scroll drag-pan
    // handler, which would immediately start a pan on mousedown under the
    // legend box.
    if (ev) { ev.stopPropagation(); }
}
function applyScale(){
    document.getElementById('treeStage').style.transform=`scale(${state.scale})`;
    document.getElementById('scaleLabel').textContent=`${Math.round(state.scale*100)}%`;
    const popup=document.getElementById('floatingPopup');
    // v57 fix: use CSS `zoom` so every pixel inside the popup scales
    // uniformly - text, icons (.ico-*, .help-chip, .src-chip), padding,
    // borders, chevrons, metric grid gaps, everything. This is the same
    // idea as the tree's `transform: scale()` on #treeStage, but zoom also
    // updates the layout box so position:fixed hit-testing stays sane
    // (transform: scale keeps the layout box at original size, which would
    // leave an invisible oversize hit-target around a zoomed-out popup).
    // Previous attempts scaled only font-size via --popup-scale + calc() or
    // em cascade; those missed fixed-px widths on chips/icons and failed to
    // cover the body rules at all on some browsers. zoom handles everything.
    popup.style.zoom = popupScaleFont();
    if(!popup.classList.contains('hidden')) requestAnimationFrame(repositionActivePopup);
}
function renderSummary(summary){
    // v69 bug fix: stash the whole summary object on state so downstream
    // render code (cards, popups, coverage banners) can read fields like
    // summary.coverage.cluster_nodes and summary.coverage.eep_nodes_seen.
    // Previously only summary.tree_analysis was stashed (as dynamicHelp),
    // so every callsite reading state.summary.* got undefined and the
    // v65 "(partial)" / v66 "(no profile data)" indicators on graph
    // cards silently never fired. Maya's v68 screenshot showed this:
    // card said "EXECUTE ON 3 nodes" with no "of 5" suffix and no
    // amber tint, even though server-side coverage said 3 of 5.
    state.summary = summary || {};
    document.getElementById('metaTxn').textContent=summary.transaction_id||'-';
    document.getElementById('metaStmt').textContent=summary.statement_id||'-';
    document.getElementById('metaLabel').textContent=summary.label||'qprof';
    document.getElementById('metaVersion').textContent=summary.version||'-';
    document.getElementById('statDuration').textContent=formatDurationUs(summary.query_duration_us||0);
    document.getElementById('statRows').textContent=formatInt(summary.total_rows||0);
    // v71.5.2: populate the Peak Memory hero tile from summary.peak_memory_mb.
    // Format: "2.85 GB" for >=1024 MB, "485 MB" otherwise. Tooltip lists the
    // per-node breakdown from summary.peak_memory_detail so the user can see
    // whether a specific node was skewed (big spread) or the cluster was
    // balanced. The tile box stays hidden when peak_memory_mb is 0 or missing
    // (resource_acquisitions returned no rows, which does happen on canceled
    // queries and some session-reset edge cases).
    const peakMb = Number(summary.peak_memory_mb || 0);
    const peakBox = document.getElementById('statPeakMemoryBox');
    const peakEl  = document.getElementById('statPeakMemory');
    if (peakBox && peakEl) {
        if (peakMb > 0) {
            const peakText = peakMb >= 1024
                ? `${(peakMb / 1024).toFixed(2)} GB`
                : `${peakMb.toFixed(0)} MB`;
            peakEl.textContent = peakText;
            // Build per-node breakdown tooltip.
            const perNode = summary.peak_memory_detail || [];
            if (perNode.length > 0) {
                const shortNode = (name) => {
                    const m = String(name || '').match(/^v_[^_]+_(node\d+)$/i);
                    return m ? m[1] : String(name || '?');
                };
                const lines = perNode.map(pn =>
                    `${shortNode(pn.node_name)}: ${Math.round((pn.memory_kb || 0) / 1024)} MB`);
                peakEl.title = 'Per-node peak memory (MAX across nodes shown):\n' + lines.join('\n');
            } else {
                peakEl.title = 'Cluster-wide peak memory from v_monitor.resource_acquisitions';
            }
            peakBox.style.display = '';
        } else {
            peakBox.style.display = 'none';
        }
    }
    document.getElementById('sqlText').textContent=summary.sql_text||'(no SQL text captured)';
    const sm=summary.summary_metrics||{};
    document.getElementById('slowestPathValue').textContent = sm.slowest_path!=null ? `Path ${sm.slowest_path}` : 'Path -';
    document.getElementById('slowestPathTime').textContent = formatSummarySecondsFromUs(sm.slowest_path_us||0);
    document.getElementById('slowestPathPct').textContent = `${Number(sm.slowest_path_pct||0).toFixed(1)}%`;
    document.getElementById('storageScanCount').textContent = formatInt(sm.storage_scan_count||0);
    document.getElementById('storageRowsValue').textContent = formatCompactInt(sm.storage_rows_scanned||0);
    document.getElementById('joinOpCount').textContent = formatInt(sm.join_op_count||0);
    document.getElementById('joinCombinedTime').textContent = formatSummarySecondsFromUs(sm.join_combined_us||0);
    // v56: stash dynamic help payload for openHelpOverlay() to pick up.
    // Keys under state.dynamicHelp match the `dynamic` field in HELP_REGISTRY
    // entries (currently only 'tree_analysis' for the 'tree-overview' entry).
    state.dynamicHelp = {
        tree_analysis: summary.tree_analysis || []
    };
}
// v58 (F-EDGE-LABEL-01): Python now attaches a per-edge descriptor
// (edge_from_parent) to each non-root path with the canonical label,
// distribution code, human-readable distribution name, modifier list,
// side, join-kind letter, and coarse color class. The frontend used
// to re-derive this from free-text title/badges/events; that was
// fragile (couldn't distinguish B vs LR vs GLR, didn't know about R,
// skipped the distribution middle letter entirely). Now we just read.
function edgeDescFrom(childNode){
    return (childNode && childNode.edge_from_parent) || null;
}
function inferEdgeType(fromNode,toNode){
    const d = edgeDescFrom(toNode);
    return (d && d.coarse_kind) || 'local';
}
function inferEdgeKey(fromNode,toNode){
    const d = edgeDescFrom(toNode);
    return (d && d.label) || 'FLOW';
}

// v55: branching tree edges - one edge per non-root node, connecting it to its
// parent_path_id. Replaces v54's pairwise-by-array-index edges which assumed a
// linear column. Each edge records the parent->child direction so the edge
// popup "From Path X -> Path Y" is meaningful.
function buildParentChildEdges(nodes){
    const byId = {};
    (nodes||[]).forEach(n => { byId[n.path_id] = n; });
    const edges = [];
    (nodes||[]).forEach(child => {
        const parentId = child.parent_path_id;
        if (parentId == null) return;
        const parent = byId[parentId];
        if (!parent) return;
        // v58: descriptor carries label, distribution_name, modifiers, etc.
        const desc = edgeDescFrom(child) || {};
        const kind = desc.coarse_kind || inferEdgeType(parent, child);
        const idx = edges.length;
        edges.push({
            index: idx,
            from_path_id: parent.path_id,
            to_path_id: child.path_id,
            from_title: detailTitle(parent.title),
            to_title: detailTitle(child.title),
            kind,
            label: desc.label || inferEdgeKey(parent, child),
            // v58: full distribution context for the edge popup (mockup §6).
            distribution_code: desc.code || '',
            distribution_name: desc.distribution_name || 'Local',
            modifiers: Array.isArray(desc.modifiers) ? desc.modifiers : [],
            side: desc.side || null,
            join_kind: desc.join_kind || '',
            rows: Number((child.card_metrics||{}).rows||0),
            memory_mb: Number((child.card_metrics||{}).memory_mb||0),
            event_count: (parent.events||[]).length + (child.events||[]).length,
            // v58 (Q-EDGE-LASTOPROWS-01): per-node "last operator rows" for
            // the UPSTREAM side of this edge. Reads from the child (which IS
            // the upstream in data-flow terms - data flows from the child up
            // to the parent JOIN). The popup renders one row per node.
            per_node_last_op: Array.isArray(child.per_node_last_op) ? child.per_node_last_op : [],
        });
    });
    return edges;
}

// v55: naive tidy-tree layout. Leaves are placed left-to-right along the bottom;
// internal nodes' x is the midpoint of their children. Children at a JOIN are
// ordered outer-left, inner-right; nodes with no side marker keep plan order.
// Fixed row height keeps the connector math simple (we don't need to measure
// card heights). For 5-20 cards the result reads cleanly without needing
// Walker's algorithm.
const TREE_CARD_W = 300;
const TREE_COL_GAP = 48;
// v71.5 fix (Maya image 2: card 41 overlaps card 40): TREE_ROW_H was 260
// but card heights for nodes with multiple event badges (e.g. PATH 40 with
// Resegment + Memory Pressure + GROUPBY SPILLED + PREPASS FALLBACK) can
// push past 280px. Bumping to 320 gives a safety margin for the tallest
// realistic card without wasting too much vertical space on compact rows.
const TREE_ROW_H = 320;
const TREE_CARD_H = 200;
const TREE_PAD = 40;

function layoutTree(nodes){
    const byId = {};
    (nodes||[]).forEach(n => { byId[n.path_id] = n; });
    const children = {};
    const roots = [];
    (nodes||[]).forEach(n => {
        const p = n.parent_path_id;
        if (p != null && byId[p]) {
            (children[p] = children[p] || []).push(n);
        } else {
            roots.push(n);
        }
    });
    // Outer-left, inner-right, unknown in the middle. path_id tiebreak.
    function sideRank(n){
        if (n.side === 'outer') return 0;
        if (n.side === 'inner') return 2;
        return 1;
    }
    for (const pid in children) {
        children[pid].sort((a,b) => {
            const ra = sideRank(a), rb = sideRank(b);
            if (ra !== rb) return ra - rb;
            return (a.path_id || 0) - (b.path_id || 0);
        });
    }
    let leafCursor = 0;
    function place(node, depth){
        node._depth = depth;
        const kids = children[node.path_id] || [];
        if (kids.length === 0){
            node._x = leafCursor * (TREE_CARD_W + TREE_COL_GAP);
            leafCursor++;
        } else {
            for (const c of kids) place(c, depth + 1);
            const xs = kids.map(c => c._x);
            node._x = (Math.min.apply(null, xs) + Math.max.apply(null, xs)) / 2;
        }
        node._y = depth * TREE_ROW_H;
    }
    for (const r of roots) place(r, 0);
    // Normalize so min x = 0
    let minX = Infinity, maxX = 0, maxY = 0;
    (nodes||[]).forEach(n => {
        if (n._x < minX) minX = n._x;
    });
    if (!isFinite(minX)) minX = 0;
    (nodes||[]).forEach(n => {
        n._x = (n._x||0) - minX + TREE_PAD;
        if (n._x + TREE_CARD_W > maxX) maxX = n._x + TREE_CARD_W;
        if (n._y + TREE_CARD_H > maxY) maxY = n._y + TREE_CARD_H;
    });
    return {
        byId, children, roots,
        stageW: maxX + TREE_PAD,
        stageH: maxY + TREE_PAD,
    };
}

// v55: draw SVG connectors between each parent and its children. For a node
// with 2+ children we draw an inverted-Y: parent stub + horizontal bar + child
// stubs. For a node with 1 child it's just a vertical line. Line color/style
// is driven by edge kind (broadcast=purple dashed, resegment=orange dashed,
// local=gray solid) - same palette as v52-v54 edge-button visuals. Edge
// labels are HTML overlays (not SVG <text>) so they inherit the popup styling
// and accept clicks to open the edge popup.
function drawTreeConnectors(layout){
    const { byId, children } = layout;
    const halfW = TREE_CARD_W / 2;
    let svgBody = '';
    for (const pid in children) {
        const parent = byId[pid];
        const kids = children[pid];
        const px = parent._x + halfW;
        const py_bot = parent._y + TREE_CARD_H;
        const ky_top = kids[0]._y;
        const midY = (py_bot + ky_top) / 2;
        // Parent stub
        svgBody += `<path d="M${px},${py_bot} L${px},${midY}" class="conn conn-local" />`;
        // Horizontal bar across children
        if (kids.length > 1){
            const lx = Math.min.apply(null, kids.map(c => c._x + halfW));
            const rx = Math.max.apply(null, kids.map(c => c._x + halfW));
            svgBody += `<path d="M${lx},${midY} L${rx},${midY}" class="conn conn-local" />`;
        }
        // Child stubs - colored by edge kind
        for (const c of kids){
            const cx = c._x + halfW;
            const kind = inferEdgeType(parent, c);
            svgBody += `<path d="M${cx},${midY} L${cx},${c._y}" class="conn conn-${kind}" />`;
        }
    }
    return svgBody;
}

function renderTree(nodes){
    state.nodes = nodes || [];
    // v55: edges are now parent->child, one per non-root node.
    state.edges = buildParentChildEdges(state.nodes);
    const host = document.getElementById('tree');
    const popup = document.getElementById('floatingPopup');
    host.innerHTML = '';
    popup.classList.add('hidden');
    const scroll = popup.querySelector('.popup-scroll');
    if (scroll) scroll.innerHTML = '';
    if (!state.nodes.length){
        host.innerHTML = '<div class="empty">No query plan nodes were returned.</div>';
        return;
    }

    // v55: compute tidy-tree layout (assigns _x, _y to every node).
    const layout = layoutTree(state.nodes);
    host.style.width  = layout.stageW + 'px';
    host.style.height = layout.stageH + 'px';
    // v71.5 fix (Maya image 3: leftmost cards trimmed, no way to scroll
    // further left). The CSS rule ".tree-stage { min-width: 1360px; }" is
    // a fixed FLOOR; when layout.stageW exceeds it (tree is wider than
    // 1360px, typical for plans with 7+ sibling leaves), the tree is
    // centered via "transform: translateX(-50%)" and its left edge lands
    // at negative x relative to the stage. The scroll container's scroll
    // range is based on the stage width, not the tree width, so the
    // overflowing left half becomes unreachable. Sync the stage's minWidth
    // to the layout's stageW (plus margin to keep the centered tree clear
    // of the stage's own padding) so horizontal scroll always covers the
    // full tree footprint. Vertical height gets the same treatment.
    const treeStageEl = document.getElementById('treeStage');
    if (treeStageEl){
        const wantedW = Math.max(1360, layout.stageW + 120);
        const wantedH = Math.max(1200, layout.stageH + 80);
        treeStageEl.style.minWidth  = wantedW + 'px';
        treeStageEl.style.minHeight = wantedH + 'px';
    }

    // v55: SVG overlay for connectors. Rendered first so cards stack on top.
    const svgConn = drawTreeConnectors(layout);
    const svgEl = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svgEl.setAttribute('class', 'tree-connectors');
    svgEl.setAttribute('width', layout.stageW);
    svgEl.setAttribute('height', layout.stageH);
    svgEl.innerHTML = svgConn;
    host.appendChild(svgEl);

    state.nodes.forEach((node, index) => {
        const card = document.createElement('button');
        card.type = 'button';
        card.className = `node-card ${node.status||'neutral'}`;
        card.dataset.nodeIndex = String(index);
        // v55: absolute positioning from layoutTree()
        card.style.position = 'absolute';
        card.style.left = node._x + 'px';
        card.style.top  = node._y + 'px';
        const m = node.card_metrics || {};
        const execMs = Number(m.exec_time_ms || 0);
        const badgeDefs = deriveBadges(node.events || []);
        // v73 (Maya feedback on v72 screenshot): card 40 had 3 stacked badges
        // (RESEG MANY ROWS + GROUPBY SPILLED + PREPASS FALLBACK) which pushed
        // the card's rendered height past TREE_CARD_H (200px). The edge-label
        // "FLOW" (positioned at the midpoint between card 40 and card 41)
        // then sat on top of the card's overflowing lower rows visually.
        // Maya's principled rule: cap what goes on the card; overflow goes
        // to the popup via a "+N more" chip. Keeps card size bounded so the
        // edge label always has clean space below the card.
        //
        // Threshold: show up to BADGE_INLINE_MAX badges; the rest collapse
        // into a single neutral chip showing "+N more" which opens the popup
        // (where the full EVENTS section already lives). Clicking the chip
        // uses the same selectNode path as any other click on the card.
        const BADGE_INLINE_MAX = 2;
        const visibleBadges  = badgeDefs.slice(0, BADGE_INLINE_MAX);
        const overflowBadges = badgeDefs.slice(BADGE_INLINE_MAX);
        const badgesHtml = visibleBadges
            .map(b=>`<span class="tiny-badge ${esc(b.kind)}" title="${esc(b.raw)}">${esc(b.label)}</span>`)
            .join('');
        const overflowHtml = overflowBadges.length > 0
            ? `<span class="tiny-badge badge-overflow" title="${esc(overflowBadges.map(b=>b.label).join(', '))} - click card for full event list">+${overflowBadges.length} more</span>`
            : '';
        const badges = badgesHtml + overflowHtml;
        const titleParts = prettyTitleParts(node.title);
        const execOnNodes = Number(m.exec_on_node_count || 0);
        const execOnMax   = Number(m.exec_on_max_ms    || 0);
        // v71 Maya-philosophy: card EXECUTE ON strip collapses to ONE line.
        //   Default (normal users): plan-authoritative value only, with an
        //     optional `. slowest: X ms on <node>` suffix when meaningful.
        //     No `(partial)` tag, no amber tint, no secondary monitoring
        //     line. The user does not need to know that our monitoring
        //     snapshot is partial - they need to know where the plan said
        //     to run.
        //   ?debug=1 (us, debugging): falls back to the full v69/v70
        //     two-line layout with partial/amber indicators and plumbing
        //     tooltips, so we can still triage internally.
        const clusterNodes = Number(((state.summary||{}).coverage||{}).cluster_nodes || 0);
        const eepNodesSeen = Number(((state.summary||{}).coverage||{}).eep_nodes_seen || 0);
        const noEepForPath = (execOnNodes === 0) || (clusterNodes > 0 && eepNodesSeen === 0);
        const isPartial    = !noEepForPath && clusterNodes > 0 && execOnNodes > 0 && execOnNodes < clusterNodes;
        const execOnPlan   = String(m.exec_on_plan || '').trim();
        const execOnNodesText = (execOnNodes === 1 ? '1 node' : execOnNodes + ' nodes');

        // v71.5.3 post-feedback (Maya's explicit spec):
        //   "EXECUTE ON <icon> N nodes, MIN: 23.9ms, MAX: 24.92ms"
        // Show MIN AND MAX so cross-node skew is visible at a glance.
        // Requires exec_on_per_node to carry {node_name, ms}; falls back
        // to path-level when the per-node array is empty.
        const perNodeTimings = m.exec_on_per_node || [];
        let slowestNodeName = '';
        let slowestNodeMs   = 0;
        let fastestNodeMs   = -1;  // -1 = not seen yet (allows genuine 0)
        for (const pn of perNodeTimings) {
            const ms = Number((pn||{}).ms || 0);
            if (ms > slowestNodeMs) {
                slowestNodeMs   = ms;
                slowestNodeName = (pn||{}).node_name || '';
            }
            if (fastestNodeMs < 0 || ms < fastestNodeMs) fastestNodeMs = ms;
        }
        if (fastestNodeMs < 0) fastestNodeMs = 0;

        // Plan-authoritative value (always rendered first).
        // v71.5.2 post-feedback (Maya's explicit spec: "EXECUTE ON <node icon>
        // 16 nodes, max: 57.8ms"). My v71.5.1 attempt used N bullet-dots, one
        // per node. She corrected: ONE node icon, then "N nodes, max: X ms".
        // Rewrite to follow the spec literally.
        // Rules:
        //   "All Nodes"  (case-insensitive) -> "N nodes" using
        //                 summary.coverage.cluster_nodes. isMulti=true so the
        //                 time suffix uses "max:" prefix.
        //   "Query Initiator" -> "Initiator", isMulti=false, no "max:".
        //   any other specific value rendered verbatim, no icon.
        function normalizeExecOnLabel(raw, clusterN){
            const s = String(raw || '').trim();
            if (!s) return { text: '(not in plan)', unknown: true, isMulti: false };
            if (/^all\s*nodes$/i.test(s)){
                const n = Number(clusterN || 0);
                if (n > 0) return { text: `${n} node${n===1?'':'s'}`, unknown: false, isMulti: n > 1 };
                return { text: 'All Nodes', unknown: false, isMulti: true };
            }
            if (/^query\s*initiator$/i.test(s)){
                return { text: 'Initiator', unknown: false, isMulti: false };
            }
            return { text: s, unknown: false, isMulti: false };
        }
        const execOnLbl = normalizeExecOnLabel(execOnPlan, clusterNodes);
        // Single inline SVG icon rendering a three-node cluster (triangle of
        // small circles). currentColor so it inherits .execon-plan-val teal.
        // aria-hidden because the text "N nodes" conveys the same meaning.
        const NODE_ICON_SVG =
            `<svg class="execon-icon" aria-hidden="true" viewBox="0 0 16 16" width="13" height="13">`+
                `<circle cx="4" cy="5.5" r="2" fill="currentColor" opacity="0.85"/>`+
                `<circle cx="12" cy="5.5" r="2" fill="currentColor" opacity="0.85"/>`+
                `<circle cx="8" cy="11.5" r="2" fill="currentColor"/>`+
            `</svg>`;
        const iconHtml = execOnLbl.unknown ? '' : NODE_ICON_SVG;
        const planLineHtml = execOnLbl.unknown
            ? `<span class="execon-plan-val execon-unknown" title="The plan text for this path did not include an Execute-on clause.">${esc(execOnLbl.text)}</span>`
            : `${iconHtml}<span class="execon-plan-val" title="Source: dc_explain_plans.plan_line. The plan's decision for where to execute this path${execOnPlan && execOnPlan !== execOnLbl.text ? '. Raw plan text: '+execOnPlan : ''}.">${esc(execOnLbl.text)}</span>`;

        let execOnStrip;
        if (state.debug) {
            // ---- Debug mode: full v69/v70 two-line layout ----
            let monitoringLineHtml = '';
            if (noEepForPath) {
                monitoringLineHtml =
                    `<div class="execon-monitoring">`+
                        `<span class="execon-sublabel">monitoring:</span> `+
                        `<span class="partial-tag" title="execution_engine_profiles returned no rows from the connected node for this path. Vertica's EEP view is per-node on the connected server; counters from other nodes replicate asynchronously. On fast queries the collection pass can outrun that replication window.">(no profile data)</span>`+
                    `</div>`;
            } else if (isPartial) {
                monitoringLineHtml =
                    `<div class="execon-monitoring">`+
                        `<span class="execon-sublabel">monitoring:</span> `+
                        `<span class="nodes">${esc(execOnNodes)}</span> of ${esc(clusterNodes)} nodes `+
                        `<span class="partial-tag" title="Only ${esc(execOnNodes)} of ${esc(clusterNodes)} nodes' counters reached the connected server for this path. Per-node view, async replication.">(partial)</span> `+
                        `&middot; max: <span class="maxms">${esc(execOnMax.toFixed(2))} ms</span>`+
                    `</div>`;
            } else if (execOnNodes > 1) {
                monitoringLineHtml =
                    `<div class="execon-monitoring">`+
                        `<span class="execon-sublabel">monitoring:</span> `+
                        `<span class="nodes">${execOnNodesText}</span> `+
                        `&middot; max: <span class="maxms">${esc(execOnMax.toFixed(2))} ms</span>`+
                    `</div>`;
            } else if (execOnNodes === 1) {
                monitoringLineHtml =
                    `<div class="execon-monitoring">`+
                        `<span class="execon-sublabel">monitoring:</span> `+
                        `<span class="nodes">1 node</span> `+
                        `&middot; <span class="maxms">${esc(execOnMax.toFixed(2))} ms</span>`+
                    `</div>`;
            }
            const stripClass = noEepForPath ? 'execon-nodata' : (isPartial ? 'execon-partial' : '');
            execOnStrip =
                `<div class="execon-strip${stripClass ? ' '+stripClass : ''}">`+
                    `<div class="execon-row1">`+
                        `<span class="execon-label">EXECUTE ON${renderHelpChip('card-execute-on')}</span>`+
                        `<span class="execon-val">${planLineHtml}</span>`+
                        renderSrcChip('F-CARD-EXECON-PLAN-01')+
                    `</div>`+
                    monitoringLineHtml+
                `</div>`;
        } else {
            // ---- Default mode: v71.2 two-line layout ----
            // Line 1: EXECUTE ON label + help chip + src chip.
            // Line 2: plan value with a compact time suffix.
            //
            // v71.2 fix (Maya's feedback on v71.1 screenshot): when EEP
            // had no per-node data, v71.1 dropped the suffix entirely and
            // the card looked empty. Now we fall back to path-level
            // exec_time_ms (which is itself plan-level when EEP is empty,
            // see card_metrics.exec_source = 'plan' server-side). The
            // card ALWAYS shows a time - either slowest-per-node (when
            // EEP has it) or path-level wall-clock (from
            // query_plan_profiles, cluster-wide).
            //
            // Node-name compaction: "v_<db>_nodeNNNN" -> "nodeNNNN".
            const shortNode = (name) => {
                if (!name) return '';
                const m = String(name).match(/^v_[^_]+_(node\d+)$/i);
                return m ? m[1] : String(name);
            };
            const pathLevelMs = Number(m.exec_time_ms || 0);
            const execSource  = String(m.exec_source || '');
            const minMs       = Number(m.exec_on_min_ms || 0);
            let suffixHtml = '';
            let suffixPlain = '';     // plain text for the tooltip title
            // v71.5.3 spec from Maya:
            //   "EXECUTE ON <icon> N nodes, MIN: 23.9ms, MAX: 24.92ms"
            // Show both MIN and MAX so cross-node skew on this specific path
            // is visible at a glance. Auto-promote each value to seconds when
            // it's >= 1000 ms (matches _us_to_ms_text Python helper).
            const fmtMs = (val) => {
                if (val >= 10000) return (val/1000).toFixed(3) + 's';
                if (val >= 1000)  return (val/1000).toFixed(2) + 's';
                return val.toFixed(2) + 'ms';
            };
            if (execOnLbl.isMulti && slowestNodeMs > 0) {
                // EEP per-node data available -> show MIN AND MAX per node.
                suffixHtml = `, MIN: <span class="minms">${esc(fmtMs(minMs))}</span>` +
                             `, MAX: <span class="maxms">${esc(fmtMs(slowestNodeMs))}</span>`;
                suffixPlain = `, MIN: ${fmtMs(minMs)}, MAX: ${fmtMs(slowestNodeMs)} (slowest node: ${slowestNodeName})`;
            } else if (pathLevelMs > 0) {
                // No per-node breakdown; fall back to path-level (single value
                // - MIN/MAX would be the same number). Keep "(plan)" hint when
                // the value came from query_plan_profiles instead of EEP sum.
                const sep = execOnLbl.isMulti ? ', max: ' : ', ';
                const tag = (execSource === 'plan')
                    ? ` <span class="execon-sublabel" title="Wall-clock running time from query_plan_profiles (cluster-wide). Per-operator breakdown was not captured for this path - cannot compute per-node MIN/MAX.">(plan)</span>`
                    : '';
                suffixHtml = `${sep}<span class="maxms">${esc(fmtMs(pathLevelMs))}</span>${tag}`;
                suffixPlain = `${sep}${fmtMs(pathLevelMs)}${execSource === 'plan' ? ' (plan)' : ''}`;
            }
            execOnStrip =
                `<div class="execon-strip">`+
                    `<div class="execon-row1">`+
                        `<span class="execon-label">EXECUTE ON${renderHelpChip('card-execute-on')}</span>`+
                        renderSrcChip('F-CARD-EXECON-PLAN-01')+
                    `</div>`+
                    `<div class="execon-value-line" title="${esc(execOnPlan || '(not in plan)')}${esc(suffixPlain)}">`+
                        `${planLineHtml}${suffixHtml}`+
                    `</div>`+
                `</div>`;
        }
        // v71.2 fix: exec-bar + MEMORY cells driven by the ACTUAL value, not
        // by an EEP-coverage heuristic. When the server fell back to the
        // query_plan_profiles path-level running_time (card_metrics.exec_source
        // === 'plan'), exec_time_ms > 0 and the cell shows that cluster-wide
        // value. Only when the server genuinely had no data from ANY source
        // (exec_source === 'none') do we show "(n/a)". Same logic for memory.
        //
        // v71.0/v71.1 bug: noEepForPath was gated on cluster_nodes > 0 &&
        // eepNodesSeen === 0, which made every card show "(no data)" even
        // though plan-level running_time/memory were sitting right there.
        const execSourceForCell = String(m.exec_source || '');
        const execTimeHasValue  = execMs > 0;
        const memHasValue       = Number(m.memory_mb || 0) > 0;
        const planLevelNote     = (execSourceForCell === 'plan')
            ? ' (plan)'
            : '';
        const nodataTitle = state.debug
            ? 'No rows in execution_engine_profiles AND query_plan_profiles for this path. Usually means the step did not execute.'
            : 'No timing data captured for this path.';
        const execTimeCell = execTimeHasValue
            ? `<span class="progress-time" title="${esc(execSourceForCell === 'plan' ? 'Path-level running_time from query_plan_profiles (cluster-wide). Per-operator breakdown was not captured.' : '')}">${esc(execMs.toFixed(2))}ms${esc(planLevelNote)}${renderHelpChip('card-exec-time')}${renderSrcChip('F-CARD-EXECTIME-01')}</span>`
            : `<span class="progress-time progress-time-nodata" title="${esc(nodataTitle)}">(n/a)${renderHelpChip('card-exec-time')}${renderSrcChip('F-CARD-EXECTIME-01')}</span>`;
        const memCell = memHasValue
            ? `<div class="v">${esc(Number(m.memory_mb||0).toFixed(1))} MB</div>`
            : `<div class="v v-nodata" title="${esc(nodataTitle)}">(n/a)</div>`;
        // Progress bar width derived from the actual exec_time_ms so
        // plan-level fallbacks also render a proportional bar.
        const progressWidth = execTimeHasValue ? nodeProgress(node) : 0;
        // v82 items 2+3 (Maya feedback on v81 cards): the upper-right of the
        // node-head had a .status-pill showing perfLabel ("CRITICAL"/"SLOW"/
        // "FAST"/"MODERATE") flanked by a (?) help-chip and an (i) src-chip.
        // Two problems:
        //   - the perf label was already rendered right below under the
        //     progress bar (the <span>${node.status}</span>) so the upper
        //     pill was duplicated info, and
        //   - the two chips on every single card drew the eye away from the
        //     graph content and added click targets that competed with the
        //     card's own click-to-open-popup behavior.
        // Replace both with a single "Click for more info.." cue carrying a
        // pointing-finger glyph. The whole card is already a <button> that
        // opens the popup (selectNode), so the cue just reinforces that
        // affordance - no new click handler needed.
        const moreInfoCue =
            `<div class="more-info-cue" title="Click this card to open full details">`+
                `<span class="mi-finger" aria-hidden="true">&#128073;</span>`+
                `<span class="mi-text">Click for more info..</span>`+
            `</div>`;
        card.innerHTML =
            `<div class="node-head">`+
                `<div class="node-id" title="Path ID - click help for what this means">${esc(node.path_id)}${renderHelpChip('card-path-id')}</div>`+
                `<div>`+
                    `<div class="node-title" title="${esc(detailTitle(node.title))}">${esc(truncatedTitle(node.short_title||titleParts.title||node.title))}</div>`+
                    `<div class="node-sub" title="${esc(detailTitle(node.title))}">${esc(nodeSubtitle(node) || titleParts.sub || '')}</div>`+
                `</div>`+
                moreInfoCue+
            `</div>`+
            `<div class="node-body">`+
                `<div class="progress-row">`+
                    execTimeCell+
                    `<div class="progress"><span style="width:${progressWidth}%"></span></div>`+
                    `<span>${esc(node.status||'neutral')}</span>`+
                `</div>`+
                `<div class="grid3">`+
                    `<div class="mini"><div class="k">Rows${renderHelpChip('card-rows')}</div><div class="v">${esc(formatInt(m.rows||0))}</div></div>`+
                    `<div class="mini"><div class="k">Cost${renderHelpChip('card-cost')}</div><div class="v">${esc(m.cost_text||'(n/a)')}</div></div>`+
                    `<div class="mini"><div class="k">Memory${renderHelpChip('card-memory')}</div>${memCell}</div>`+
                `</div>`+
                (badges ? `<div class="event-strip">${badges}${renderHelpChip('card-badges')}${renderSrcChip('F-CARD-BADGES-01')}</div>` : '')+
                (state.debug ? execOnStrip : '')+
            `</div>`;
        card.addEventListener('click',(event)=>selectNode(index,event));
        host.appendChild(card);
    });

    // v55: edge labels as HTML pills positioned at the child-stub midpoint.
    // Separate from SVG so they inherit normal popup styling and accept clicks.
    const halfW = TREE_CARD_W / 2;
    state.edges.forEach((edge, eIdx) => {
        const parent = layout.byId[edge.from_path_id];
        const child  = layout.byId[edge.to_path_id];
        if (!parent || !child) return;
        const cx = child._x + halfW;
        const midY = (parent._y + TREE_CARD_H + child._y) / 2;
        const pill = document.createElement('button');
        pill.type = 'button';
        pill.className = `tree-edge-label edge-${edge.kind}`;
        pill.dataset.edgeIndex = String(eIdx);
        pill.textContent = edge.label;
        pill.title = `${edge.from_path_id} -> ${edge.to_path_id} (${edge.kind})`;
        pill.style.position = 'absolute';
        pill.style.left = (cx) + 'px';
        pill.style.top  = (midY) + 'px';
        pill.style.transform = 'translate(-50%, -50%)';
        pill.addEventListener('click', (event)=>selectEdge(eIdx, event));
        host.appendChild(pill);
    });

    // v74 (Maya feedback on v73 image 1): previously render() ended with
    // selectNode(0), which auto-opened the popup for path 0 / path 20 on
    // load. User arrives at the graph expecting to SEE the graph first; a
    // popup they didn't choose to open takes their attention before they've
    // seen the tree. Do not auto-open any popup.
    //
    // Also (Maya feedback): when the plan is wide (3+ cards in any row),
    // the default 80% zoom hides cards off-screen and the user has to hunt
    // for the minus button. Auto-zoom to 30% in that case so the whole
    // tree fits in one view, and scroll back to top-left so the root card
    // is the first thing the user sees.
    const cardsPerDepth = {};
    (state.nodes || []).forEach(n => {
        const d = Number(n._depth || 0);
        cardsPerDepth[d] = (cardsPerDepth[d] || 0) + 1;
    });
    const depthValues = Object.values(cardsPerDepth);
    const maxRowCards = depthValues.length > 0 ? Math.max.apply(null, depthValues) : 1;
    if (maxRowCards > 3) {
        state.scale = 0.3;
        applyScale();
        const scrollEl = document.getElementById('treeScroll');
        if (scrollEl) { scrollEl.scrollLeft = 0; scrollEl.scrollTop = 0; }
    }
}
// -----------------------------------------------------------------------------
// Popup structure (idempotent builder).
// The popup is outer .floating-popup (overflow:hidden, flex column) containing:
//   - 8 resize handles (4 edges + 4 corners) at z-index 50
//   - inner .popup-scroll (the scrollable content area)
// The inner .popup-scroll is what hidePopup() clears and renderNodePopup() /
// renderEdgePopup() fill. We never clear the outer popup's innerHTML or we'd
// destroy the resize handles.
// -----------------------------------------------------------------------------
function ensurePopupStructure(popup){
    if(!popup.querySelector('.popup-scroll')){
        // First-time build: handles then scroll container.
        const sides = ['top','bottom','left','right','tl','tr','bl','br'];
        for(const side of sides){
            const h = document.createElement('div');
            h.className = `resize-handle rh-${side}`;
            h.dataset.side = side;
            h.addEventListener('mousedown', (ev) => startPopupResize(ev, side, popup));
            popup.appendChild(h);
        }
        const scroll = document.createElement('div');
        scroll.className = 'popup-scroll';
        popup.appendChild(scroll);
    }
    return popup.querySelector('.popup-scroll');
}
function hidePopup(){
    const popup=document.getElementById('floatingPopup');
    popup.classList.add('hidden');
    const scroll = popup.querySelector('.popup-scroll');
    if(scroll) scroll.innerHTML = '';
}

// -----------------------------------------------------------------------------
// v57 fix: read the popup's current CSS `zoom` factor. Used by the resize,
// drag, and positionPopup code to reconcile coordinate spaces:
//   - popup.style.left/top/width/height are LAYOUT (pre-zoom) pixels.
//   - getBoundingClientRect() / offsetWidth / offsetHeight are VISUAL
//     (post-zoom) pixels.
//   - event.clientX/Y are VIEWPORT (same as visual) pixels.
// When we mix them without dividing/multiplying by this factor, positions
// and sizes drift by the zoom ratio on every write - that's what caused
// the popup to jump up-and-left on every resize click at zoomed-out scale.
// -----------------------------------------------------------------------------
function getPopupZoom(){
    const popup = document.getElementById('floatingPopup');
    const z = parseFloat(popup && popup.style ? popup.style.zoom : '');
    return (isFinite(z) && z > 0) ? z : 1;
}

// -----------------------------------------------------------------------------
// 8-direction popup resize. Math is applied to popup.style.{left,top,width,height}.
// isN / isS / isE / isW are derived from the side string. Drag start captures
// the popup bounding rect and the mouse offset so follow-up mousemove events
// can compute deltas exactly. Min size 200x140 to prevent collapse.
// -----------------------------------------------------------------------------
function startPopupResize(ev, side, popup){
    ev.preventDefault();
    ev.stopPropagation();
    // v57 fix: work entirely in LAYOUT coordinates to match what
    // popup.style.* properties are applied in. getBoundingClientRect
    // returns visual (post-zoom) pixels, and event.clientX/Y are visual
    // too, so we divide both by z to convert to layout space.
    const z = getPopupZoom();
    const rect = popup.getBoundingClientRect();
    const startX = ev.clientX, startY = ev.clientY;
    const startLeft = rect.left / z, startTop = rect.top / z;
    const startW    = rect.width / z, startH   = rect.height / z;
    const isN = (side === 'top'    || side === 'tl' || side === 'tr');
    const isS = (side === 'bottom' || side === 'bl' || side === 'br');
    const isW = (side === 'left'   || side === 'tl' || side === 'bl');
    const isE = (side === 'right'  || side === 'tr' || side === 'br');
    const MIN_W = 200, MIN_H = 140;
    // Release the max-height and max-width caps so the user can freely grow
    // the popup in either direction; these caps were just starting-size hints.
    popup.style.maxHeight = 'none';
    popup.style.maxWidth  = 'none';
    popup.classList.add('resizing');
    // Manual resize counts as manual positioning so scroll/zoom don't re-snap.
    state.popupManuallyPositioned = true;
    function move(e){
        let newLeft = startLeft, newTop = startTop, newW = startW, newH = startH;
        // v57 fix: convert the visual mouse delta into layout pixels
        // before adding to the layout-space start values.
        const dx = (e.clientX - startX) / z, dy = (e.clientY - startY) / z;
        if(isE){ newW = Math.max(MIN_W, startW + dx); }
        if(isW){
            const w = Math.max(MIN_W, startW - dx);
            newLeft = startLeft + (startW - w);
            newW = w;
        }
        if(isS){ newH = Math.max(MIN_H, startH + dy); }
        if(isN){
            const h = Math.max(MIN_H, startH - dy);
            newTop = startTop + (startH - h);
            newH = h;
        }
        popup.style.left   = `${newLeft}px`;
        popup.style.top    = `${newTop}px`;
        popup.style.width  = `${newW}px`;
        popup.style.height = `${newH}px`;
    }
    function up(){
        document.removeEventListener('mousemove', move);
        document.removeEventListener('mouseup', up);
        popup.classList.remove('resizing');
    }
    document.addEventListener('mousemove', move);
    document.addEventListener('mouseup', up);
}

// -----------------------------------------------------------------------------
// v53 fix 5: tree-scroll resize
// Drag the bottom/bottom-left/bottom-right handles to change the tree viewport
// height. Drops the max-height cap so the user can freely grow it. In-memory
// only - not persisted across page loads.
// -----------------------------------------------------------------------------
function startTreeScrollResize(ev, side){
    ev.preventDefault();
    ev.stopPropagation();
    const scroll = document.getElementById('treeScroll');
    const wrap   = document.getElementById('treeScrollWrap');
    if(!scroll || !wrap) return;
    const rect = scroll.getBoundingClientRect();
    const startY = ev.clientY;
    const startH = rect.height;
    const MIN_H = 320;
    // Release the max-height cap so drag can grow past calc(100vh - 200px).
    scroll.style.maxHeight = 'none';
    wrap.classList.add('resizing');
    function move(e){
        const dy = e.clientY - startY;
        const newH = Math.max(MIN_H, startH + dy);
        scroll.style.height = `${newH}px`;
    }
    function up(){
        document.removeEventListener('mousemove', move);
        document.removeEventListener('mouseup', up);
        wrap.classList.remove('resizing');
    }
    document.addEventListener('mousemove', move);
    document.addEventListener('mouseup', up);
}

function popupHeader(eyebrow,title,sub){
    return `<div class="popup-head"><button class="popup-close" type="button" onclick="hidePopup()">×</button><div class="popup-eyebrow">${esc(eyebrow)}</div><div class="popup-title">${esc(title)}</div>${sub?`<div class="popup-sub">${esc(sub)}</div>`:''}</div>`;
}
function renderNodePopup(node){
    // v56: popup redesigned per MOCKUP_SPEC sec 5. Sections:
    //   PERFORMANCE        - % of Query, Exec, Clock, Rows, Ratio (status-colored)
    //   ESTIMATES          - Est vs Actual rows comparison
    //   EXECUTION (N nodes)- collapsible; per-node rows "v_eevdb_node0001  N thr . T ms"
    //   DETAILS            - Filter / Runtime Filter / Projection / etc. from plan_details
    //   OPERATORS (N)      - per-op: cyan name, exec/clock/thr line, rows prod->recv
    //   EVENTS             - preserved from v55 (deduped)
    // v76: small rounded rectangle at the TOP of the popup body that
    //   states WHY this card got its color. Server-side
    //   apply_card_status_rules writes node.status_reason; we render it
    //   verbatim in a banner whose gradient matches the card's color.
    const metrics  = node.metrics  || {};
    const operators= node.operators|| [];
    const events   = node.events   || [];
    const cm       = node.card_metrics || {};
    // v76: build the status banner HTML. We take node.status + node.status_reason
    // straight from the server - no client-side recomputation - so the banner
    // can never disagree with the card color. Banner maps status names
    // (bad/warn/neutral/good) to CSS classes sb-bad/sb-warn/sb-neutral/sb-good
    // which in turn pick the gradient and text color.
    const sbStatus   = String(node.status || 'neutral');
    const sbReason   = String(node.status_reason || '');
    const sbClassMap = { bad: 'sb-bad', warn: 'sb-warn', good: 'sb-good', neutral: 'sb-neutral' };
    const sbCssClass = sbClassMap[sbStatus] || 'sb-neutral';
    const sbLabel    = perfLabel(node);   // FAST / MODERATE / SLOW / CRITICAL
    const statusBanner = sbReason
        ? `<div class="status-banner ${sbCssClass}">`+
              `<span class="sb-eyebrow">${esc(sbLabel)} - why this color?</span>`+
              `${esc(sbReason)}`+
          `</div>`
        : '';
    // v65: "% of Query" previously divided by max(exec_time_ms) which
    // turned the hottest card into a misleading "100.0%". Match the help
    // text literally: share of SUM across all cards in the tree. When
    // everything is zero (full EEP gap), render 0.0% so we don't produce
    // NaN.
    const allExec  = state.nodes.map(n=>Number((n.card_metrics||{}).exec_time_ms||0));
    const totalExec = allExec.reduce((a,b)=>a+b, 0);
    const execMs   = Number(cm.exec_time_ms || 0);
    const pct      = totalExec > 0 ? (execMs / totalExec) * 100.0 : 0.0;
    const titleText= node.short_title || detailTitle(node.title);
    const subLine  = `${detailTitle(node.title)} [PATH ID: ${node.path_id}]`;
    const planDetails = (node.plan_details || []);
    const dedupedEvents = dedupEventsForPopup(events);

    // ---------- PERFORMANCE section ----------
    // % of Query: color-shift. pct>80 = bad (red), 40-80 = warn (orange),
    // 20-40 = plain, <20 = good (green).
    let pctClass = 'perf-val-plain';
    if (pct >= 80) pctClass = 'perf-val-bad';
    else if (pct >= 40) pctClass = 'perf-val-warn';
    else if (pct < 20) pctClass = 'perf-val-good';

    // Rows Processed / Produced ratio. If processed > 0 and ratio < 1, tint
    // orange (bottleneck - more consumed than produced).
    const rowsProc  = Number((operators.find(o=>Number(o.processed_rows||0)>0)||{}).processed_rows || 0);
    const rowsProd  = Number(cm.rows || 0) || Number((operators[0]||{}).produced_rows || 0);
    const ratio     = rowsProc > 0 ? (rowsProd / rowsProc) : null;
    let ratioClass  = 'perf-val-plain';
    if (ratio !== null && ratio < 1) ratioClass = 'perf-val-warn';

    const execTimeChip  = renderSrcChip('F-CARD-EXECTIME-01');
    const clockTimeChip = renderSrcChip('F-CARD-CLOCKTIME-01');

    // v71.2 fix (Maya's feedback on v71.1 screenshot): popup metric
    // cells are driven by the ACTUAL value, not by an EEP-coverage
    // heuristic. When card_metrics.exec_time_ms is a plan-level
    // fallback (exec_source === 'plan'), show that value with a small
    // "(plan)" tag so the user knows it's wall-clock not operator-sum.
    // Only show "(no data)" when the server genuinely could not produce
    // a number from any source.
    //
    // Clock Time comes from query_plan_profiles directly (always
    // cluster-wide) so it was never affected.
    //
    // Memory now reads from BOTH sources: cm.memory_mb (server-side
    // already prefers query_plan_profiles, enriches with EEP if
    // available); fall back to metrics.memory_mb; else (n/a).
    const popupExecSource   = String(cm.exec_source || '');
    const popupExecHasValue = Number(cm.exec_time_ms || 0) > 0;
    const popupMemValue     = Number(cm.memory_mb != null ? cm.memory_mb : (metrics.memory_mb || 0));
    const popupMemHasValue  = popupMemValue > 0;
    const popupPlanTag      = (popupExecSource === 'plan')
        ? ' <span style="color:#9fb4d7;font-style:italic;font-size:10px;" title="Value came from query_plan_profiles (cluster-wide). Per-operator breakdown was not captured for this path.">(plan)</span>'
        : '';
    const nodataCell = '<div class="v v-nodata" title="No timing data captured for this path.">(n/a)</div>';
    // Keep a popup-level banner ONLY under ?debug=1 (internal triage).
    // In the default view the "(plan)" tag next to Exec Time tells the
    // user everything they need to know without the amber paragraph.
    const popupNoEepDebugOnly = state.debug && (popupExecSource !== 'eep');
    let coverageBanner = '';
    if (popupNoEepDebugOnly) {
        const popupClusterNodesForBanner = Number(((state.summary||{}).coverage||{}).cluster_nodes || 0);
        const popupEepNodesSeen = Number(((state.summary||{}).coverage||{}).eep_nodes_seen || 0);
        coverageBanner =
            `<div class="coverage-banner" style="margin:4px 0 10px;padding:8px 10px;background:rgba(255,159,67,.10);border:1px solid rgba(255,159,67,.38);border-radius:6px;color:#ffc27e;font-size:11.5px;line-height:1.45;">`+
            `<b>Plan-level timings for this path</b> (debug view). execution_engine_profiles had no operator rows for this path (eep_nodes_seen=${esc(popupEepNodesSeen)} / cluster=${esc(popupClusterNodesForBanner)}); Exec Time and Memory values shown above come from query_plan_profiles.running_time and .memory_allocated_bytes. Clock Time, Rows, Cost are unaffected. Re-profile for operator-level detail.`+
            `</div>`;
    }

    const perfSection =
        `<div class="sec">`+
            `<div class="sec-hdr"><span class="ico ico-perf"></span><span class="ttl">Performance</span></div>`+
            coverageBanner+
            `<div class="sec-body metric-list">`+
                `<div class="k">% of Query ${renderHelpChip('popup-pct-of-query')}</div>`+
                (popupExecHasValue ? `<div class="v ${pctClass}">${esc(pct.toFixed(1))}%</div>` : nodataCell)+
                `<div class="k">Exec Time ${renderHelpChip('popup-exec-time')}${execTimeChip}</div>`+
                (popupExecHasValue ? `<div class="v">${esc(execMs.toFixed(2))} ms${popupPlanTag}</div>` : nodataCell)+
                `<div class="k">Clock Time ${renderHelpChip('popup-clock-time')}${clockTimeChip}</div>`+
                `<div class="v">${esc(metrics.running_time_us!=null?formatDurationUs(metrics.running_time_us):'(n/a)')}</div>`+
                `<div class="k">Rows Processed ${renderHelpChip('popup-rows')}</div>`+
                (rowsProc > 0 ? `<div class="v">${esc(formatInt(rowsProc))}</div>` : nodataCell)+
                (rowsProc > 0 && ratio !== null
                    ? `<div class="k">Ratio (Prod/Proc) ${renderHelpChip('popup-rows')}</div>`+
                      `<div class="v ${ratioClass}">${esc(ratio.toFixed(3))}</div>`
                    : '')+
                `<div class="k">Memory ${renderHelpChip('popup-memory')}</div>`+
                (popupMemHasValue ? `<div class="v">${esc(popupMemValue.toFixed(1))} MB</div>` : nodataCell)+
                `<div class="k">Cost ${renderHelpChip('popup-cost')}</div>`+
                `<div class="v">${esc(cm.cost_text||'(n/a)')}</div>`+
            `</div>`+
        `</div>`;

    // ---------- ESTIMATES section ----------
    // Est vs Actual: operator-level est_rows (capped) vs actual rows produced.
    // The execution_engine_profiles counter 'rows produced' is the actual;
    // est_rows from the plan text was stored on the Cost line. For now we
    // show "est -> actual" if both are non-zero, else hide.
    const estimateLines = [];
    // Try to pull an estimate from the cost_text (e.g. "Rows: 1M (ROW COUNT ONLY)")
    // via a regex; actual is the card's rows count.
    const titleUpper = String(node.title || '').toUpperCase();
    const estMatch = titleUpper.match(/ROWS?:\s*([0-9]+[KMB]?)/);
    const estText  = estMatch ? estMatch[1] : null;
    const actText  = rowsProd > 0 ? formatCompactInt(rowsProd) : null;
    if (estText || actText) {
        estimateLines.push(
            `<div class="detail-row"><span class="k">Est -> Actual Rows:</span>`+
            `${esc(estText||'?')} -> ${esc(actText||'?')}</div>`
        );
    }
    const estSection = estimateLines.length
        ? `<div class="sec">`+
            `<div class="sec-hdr"><span class="ico-est">&#9733;</span><span class="ttl">Estimates</span></div>`+
            `<div class="sec-body">${estimateLines.join('')}</div>`+
          `</div>`
        : '';

    // ---------- EXECUTION section (collapsible) ----------
    // v71: by default the section simply lists per-node timings (which
    // *are* actionable - you can spot skew at a glance) under the title
    // "Per-node timings". The v69 "PLAN (AUTHORITATIVE) / MONITORING
    // (OBSERVED)" micro-table is internal-plumbing language and only
    // renders under ?debug=1.
    const perNode   = cm.exec_on_per_node || [];
    const nodeCount = cm.exec_on_node_count || perNode.length;
    const execDefaultCollapsed = perNode.length > 3 ? 'collapsed' : '';
    const execHdrCollapsed     = perNode.length > 3 ? 'collapsed' : '';
    const popupClusterNodes = Number(((state.summary||{}).coverage||{}).cluster_nodes || 0);
    const popupIsPartial = popupClusterNodes > 0 && nodeCount > 0 && nodeCount < popupClusterNodes;
    const popupExecOnPlan = String(cm.exec_on_plan || '').trim();

    let planVsMonSection = '';
    if (state.debug) {
        // Debug-only: v69 Plan-vs-Monitoring micro-table.
        let monitoringCell;
        if (nodeCount === 0) {
            monitoringCell = `<span style="color:#ffad66;font-style:italic;">(no counters observed)</span>`;
        } else if (popupIsPartial) {
            monitoringCell =
                `<b>${esc(nodeCount)}</b> of <b>${esc(popupClusterNodes)}</b> nodes reported counters `+
                `<span style="color:#ffad66;font-style:italic;">(partial)</span>`;
        } else if (popupClusterNodes > 0 && nodeCount === popupClusterNodes) {
            monitoringCell = `all <b>${esc(popupClusterNodes)}</b> nodes reported counters`;
        } else {
            monitoringCell = `<b>${esc(nodeCount)}</b> ${nodeCount === 1 ? 'node' : 'nodes'} reported counters`;
        }
        planVsMonSection =
            `<div class="plan-vs-mon">`+
                `<div class="pvm-row">`+
                    `<span class="pvm-label" title="dc_explain_plans.plan_line - the plan decision Vertica optimizer emitted. Always cluster-wide and always complete.">Plan (authoritative):</span>`+
                    `<span class="pvm-val pvm-plan">${popupExecOnPlan ? esc(popupExecOnPlan) : '<i>(not in plan)</i>'}</span>`+
                `</div>`+
                `<div class="pvm-row">`+
                    `<span class="pvm-label" title="v_monitor.execution_engine_profiles - per-node view on the connected server. Counters from other nodes replicate asynchronously; on fast queries the collection pass can outrun the replication window, so this may be partial even though the query ran on every node.">Monitoring (observed):</span>`+
                    `<span class="pvm-val pvm-mon">${monitoringCell}</span>`+
                `</div>`+
            `</div>`;
    }

    // v71.5 fix (Maya image 2: popup "PER-NODE TIMINGS (1 NODE) v_eevdb_node0005 0.00 ms"):
    // when every per-path EEP row has ms=0 - which happens whenever EEP did not
    // replicate the 'execution time (us)' counter for this path - the per-node
    // section showed a useless "0.00 ms" line. Replace with cluster-wide
    // query-level timings from dc_query_executions (summary.query_node_times,
    // always populated) and label the section clearly so the user understands
    // this is total query work per node, NOT per-path per-node.
    //
    // v75.1 fix (Maya feedback on v75 image: card 40 EXECUTION section empty):
    // the fallback trigger required perNode.length > 0 AND all zero, so when
    // EEP returned NO per-node rows at all for this path (retention purged),
    // perNodeAllZero was false and useClusterWideFallback was false - result
    // was an EXECUTION section with an empty body. Trigger the fallback also
    // when perNode is EMPTY so the user always sees either a per-path per-node
    // breakdown OR the cluster-wide fallback. Never an empty section.
    const perNodeEmpty    = perNode.length === 0;
    const perNodeAllZero  = perNode.length > 0
        && perNode.every(pn => !(Number(pn.ms || 0) > 0));
    const queryNodeTimes  = ((state.summary || {}).query_node_times) || [];
    const useClusterWideFallback = (perNodeAllZero || perNodeEmpty) && queryNodeTimes.length > 0;
    // v71: default per-node list title is "Per-node timings" (plain
    // English, no labels like "Observed per-node counters" that leak
    // our internal table model). Debug mode keeps the v69 wording.
    // v73 (Maya feedback on v72 screenshot): in fallback mode each node
    // showed ~24s for card 40 and the user reasonably wondered "is that
    // per-path or per-query?". The italic disclaimer was too subtle. Make
    // the title unambiguous - prefix with "WHOLE-QUERY" so there is no
    // risk of reading these as this path's per-node times.
    const execTitle = useClusterWideFallback
        ? `WHOLE-QUERY ExecutePlan timing per node (${esc(queryNodeTimes.length)} nodes, cluster-wide fallback)`
        : (state.debug
            ? (popupIsPartial
                ? `Observed per-node counters (${esc(nodeCount)} of ${esc(popupClusterNodes)} <span style="color:#ffad66;font-style:italic;">&middot; partial</span>)`
                : `Observed per-node counters (${esc(nodeCount)} ${nodeCount === 1 ? 'node' : 'nodes'})`)
            : `Per-node timings (${esc(nodeCount)} ${nodeCount === 1 ? 'node' : 'nodes'})`);
    // v71.5: when falling back to query_node_times, synthesize exec rows
    // from summary data. Short-node render, same row style.
    const perNodeRender = useClusterWideFallback
        ? queryNodeTimes.map(qn => ({
              node_name: qn.node_name || '?',
              threads:   0,
              ms:        Number(qn.execute_ms || 0),
              _fallback: true,
          }))
        : perNode;
    const perNodeHasAnything = perNodeRender.length > 0;
    const execSection =
        `<div class="sec">`+
            `<div class="sec-hdr">`+
                `<span class="ico ico-exec"></span>`+
                `<span class="ttl">Execution ${renderHelpChip('card-execute-on')}${renderSrcChip('F-CARD-EXECON-PLAN-01')}</span>`+
            `</div>`+
            `<div class="sec-body">`+
                planVsMonSection+
                (useClusterWideFallback
                    // v73 (Maya feedback on v72 screenshot): italic gray text
                    // was too subtle - the user read the ~24s-per-node numbers
                    // as path-specific. Switch to a warning-styled amber banner
                    // that is impossible to miss, with bold leading label.
                    ? `<div style="margin:6px 0 10px;padding:8px 10px;border-radius:6px;`+
                              `background:rgba(255,173,102,.08);border-left:3px solid #ffad66;`+
                              `color:#ffd3a8;font-size:11px;line-height:1.5;">`+
                      `<strong style="color:#ffad66;">Note:</strong> These are <strong>WHOLE-QUERY</strong> `+
                      `ExecutePlan timings per node (cluster-wide, from dc_query_executions), `+
                      `<strong>not</strong> the per-node time spent on THIS path. `+
                      `Per-path per-node breakdown from execution_engine_profiles was not captured `+
                      `for this path (short operator or EEP retention).`+
                      `</div>`
                    : '')+
                (perNodeHasAnything
                    ? `<div class="sec ${execDefaultCollapsed}" ${state.debug ? 'style="margin-top:10px;"' : ''}>`+
                        `<div class="sec-hdr clickable ${execHdrCollapsed}" onclick="this.parentNode.classList.toggle('collapsed');this.classList.toggle('collapsed');">`+
                            `<span class="ttl" style="font-size:11px;">${execTitle}</span>`+
                            `<span class="chev">&#9660;</span>`+
                        `</div>`+
                        `<div class="sec-body">`+
                            perNodeRender.map(pn => {
                                const nn  = pn.node_name || '?';
                                const thr = Number(pn.threads || 0);
                                const ms  = Number(pn.ms || 0);
                                return `<div class="exec-row">`+
                                         `<span class="nn">${esc(nn)}</span>`+
                                         `<span class="rt">`+
                                           (thr > 0 ? `<span class="thr">${esc(thr)} thr</span>` : '')+
                                           `${esc(ms.toFixed(2))} ms`+
                                         `</span>`+
                                       `</div>`;
                            }).join('')+
                        `</div>`+
                      `</div>`
                    : '')+
                // v75.1 (Maya feedback): belt-and-braces final fallback so
                // the EXECUTION section never renders with an empty body.
                // This triggers only if (a) not in debug (planVsMonSection
                // empty), (b) no cluster-wide fallback available, AND
                // (c) no per-node rows to render. In that narrow case we
                // explain plainly that no per-node timings were captured.
                ((!state.debug && !useClusterWideFallback && !perNodeHasAnything)
                    ? `<div style="padding:8px 10px;border-radius:6px;`+
                              `background:rgba(255,173,102,.08);border-left:3px solid #ffad66;`+
                              `color:#ffd3a8;font-size:11px;line-height:1.5;">`+
                      `<strong style="color:#ffad66;">Note:</strong> No per-node timing was `+
                      `captured for this path. execution_engine_profiles returned no rows `+
                      `(short operator, skipped by Vertica's monitoring threshold, or retention purged) `+
                      `and dc_query_executions ExecutePlan timing was not available either. `+
                      `Plan-level running_time is shown on the card; the top of this popup has `+
                      `% of Query / Exec Time / Clock Time which remain valid for this path.`+
                      `</div>`
                    : '')+
            `</div>`+
        `</div>`;

    // ---------- DETAILS section ----------
    // Filter / Runtime Filter / Projection / Materialize / Sort Key lines from
    // plan_details. Each line is already a non-operator subline.
    const detailSection = planDetails.length
        ? `<div class="sec">`+
            `<div class="sec-hdr"><span class="ico ico-det"></span><span class="ttl">Details</span></div>`+
            `<div class="sec-body">`+
                planDetails.map(line => `<div class="detail-row">${esc(line)}</div>`).join('')+
            `</div>`+
          `</div>`
        : '';

    // ---------- OPERATORS section ----------
    // Cyan operator name, then "Exec: Xms  Clock: Yms  Thr: N" then
    // "Rows: prod -> recv" line.
    // v74.1 (Maya feedback on v74 screenshot): card 40 popup showed 6
    // operators (GroupByHash/GroupByPipe/NetworkRecv/NetworkSend/
    // ParallelUnion/StorageUnion) all with "Exec: 0.00 ms". That's not
    // a real "0ms" - it's Vertica's 'execution time (us)' counter being
    // purged from EEP by short dc_execution_engine_profiles retention,
    // but other counters (like rows counts) still survived, so the
    // engine_by_path aggregation still produced operator rows with
    // zero timing. Detect this case (all operators have zero exec_time,
    // clock_time, and threads) and swap the per-operator list for a
    // single explanatory banner matching the server-side N2 fix in the
    // Profile Text Tab. Same text, same DDL fix suggestion.
    const allOpsZero = operators.length > 0 && operators.every(op => {
        const ex = Number(op.exec_time_ms || 0);
        const ck = Number(op.clock_time_ms || 0);
        const thr = Number(op.threads || 0);
        const memMb = Number(op.memory_allocated_mb || 0);
        return ex === 0 && ck === 0 && thr === 0 && memMb === 0;
    });
    const opSection = allOpsZero
        ? `<div class="sec">`+
            `<div class="sec-hdr"><span class="ico ico-ops"></span><span class="ttl">Operators (${esc(operators.length)}) ${renderHelpChip('popup-operators')}</span></div>`+
            `<div class="sec-body">`+
              `<div style="padding:8px 10px;border-radius:6px;`+
                      `background:rgba(255,173,102,.08);border-left:3px solid #ffad66;`+
                      `color:#ffd3a8;font-size:11px;line-height:1.5;">`+
                `<strong style="color:#ffad66;">Note:</strong> Vertica returned `+
                esc(operators.length)+` operator rows for this path but every `+
                `execution-time counter is zero - most likely purged by short `+
                `<code>dc_execution_engine_profiles</code> retention before the profile `+
                `was captured. Operator names: `+
                esc(operators.map(op => op.operator_name || '?').join(', '))+`. `+
                `Raise retention with:<br>`+
                `<code style="display:block;margin:6px 0;padding:6px 8px;background:rgba(0,0,0,.25);border-radius:4px;color:#cdd8ee;">`+
                `SELECT set_data_collector_time_policy('ExecutionEngineProfiles','1 day');`+
                `</code>`+
              `</div>`+
            `</div>`+
          `</div>`
        : operators.length
        ? `<div class="sec">`+
            `<div class="sec-hdr"><span class="ico ico-ops"></span><span class="ttl">Operators (${esc(operators.length)}) ${renderHelpChip('popup-operators')}</span></div>`+
            `<div class="sec-body">`+
                operators.map(op => {
                    const name  = esc(op.operator_name || '(unknown)');
                    const exNum = Number(op.exec_time_ms || 0);
                    const ex    = exNum.toFixed(2);
                    const ck    = op.clock_time_ms != null ? Number(op.clock_time_ms).toFixed(2) : null;
                    const thr   = Number(op.threads || 0);
                    const prod  = Number(op.produced_rows || 0);
                    const recv  = Number(op.received_rows || 0);
                    const memMb = Number(op.memory_allocated_mb || 0);
                    // v75.2 (Maya feedback on v75.1 image: "All 4 operators
                    // show Exec: 0.00 ms - does that make sense?"). It does
                    // NOT. In Maya's card 40 run, GroupByHash had Thr: 2
                    // and Mem: 542.7 MB - so the operator clearly ran and
                    // allocated half a GB - but the EEP 'execution time
                    // (us)' counter was purged by retention, so exec_time_ms
                    // was 0. Rendering "Exec: 0.00 ms" was dishonest - it
                    // reads as "this took 0ms" when the truth is "timing
                    // not captured". Per-operator detection: if exec=0 AND
                    // (thr>0 OR mem>0 OR rows>0), render "Exec: (not captured)"
                    // instead. The v74.1 all-operators-zero amber banner
                    // still covers the case where NOTHING is populated; this
                    // handles the mixed case where timing is gone but other
                    // counters survived.
                    const opRan = thr > 0 || memMb > 0 || prod > 0 || recv > 0;
                    const execStr = (exNum === 0 && opRan)
                        ? `<b>Exec:</b> <span title="The EEP 'execution time (us)' counter was not captured for this operator (purged by short dc_execution_engine_profiles retention). Other counters (threads / memory / rows) confirm the operator did run.">(not captured)</span>`
                        : `<b>Exec:</b> ${esc(ex)} ms`;
                    const stats = [
                        execStr,
                        // v56.2: hide Clock when it's 0 ms. Vertica's
                        // 'clock time (us)' counter isn't populated for many
                        // operator kinds (NetworkRecv / NetworkSend /
                        // StorageUnion all report 0). Showing "Clock: 0.00 ms"
                        // next to "Exec: 7.54 ms" suggested the operator
                        // was instantaneous, which it wasn't - it was
                        // actually just not-counter-instrumented. Better to
                        // omit than mislead.
                        (ck !== null && Number(ck) > 0) ? `<b>Clock:</b> ${esc(ck)} ms` : null,
                        thr > 0 ? `<b>Thr:</b> ${esc(thr)}` : null,
                        memMb > 0 ? `<b>Mem:</b> ${esc(memMb.toFixed(1))} MB` : null,
                    ].filter(Boolean).join('  ');
                    const rows = (prod || recv)
                        ? `<div class="op-rows">Rows: ${esc(formatInt(prod))} prod -> ${esc(formatInt(recv))} recv</div>`
                        : '';
                    return `<div class="opblk">`+
                             `<div class="op-name">${name}</div>`+
                             `<div class="op-stats">${stats}</div>`+
                             rows+
                           `</div>`;
                }).join('')+
            `</div>`+
          `</div>`
        : `<div class="sec">`+
            `<div class="sec-hdr"><span class="ico ico-ops"></span><span class="ttl">Operators</span></div>`+
            // v71.4 fix (Maya regression report): v71.2 renamed the
            // popup-level "no EEP" flag to popupNoEepDebugOnly +
            // popupExecHasValue but missed this call site, which threw
            // ReferenceError and broke card-click popups entirely. Now
            // driven by the same popupExecHasValue flag used everywhere
            // else in this function.
            (!popupExecHasValue
                ? `<div class="sec-body"><div class="empty" style="color:#9fb4d7;font-style:italic;">No per-operator breakdown captured for this path. Plan-level metrics above are valid.</div></div>`
                : `<div class="sec-body"><div class="empty">No operators returned for this path.</div></div>`
            )+
          `</div>`;

    // ---------- EVENTS section (preserved) ----------
    const eventsSection = dedupedEvents.length
        ? dedupedEvents.map(ev => {
            // v73: use _nodeCount (distinct nodes) instead of _count (raw rows).
            // Maya image-2 bug: GROUP_BY_SPILLED reported "triggered on 10 nodes"
            // on a 5-node cluster because Vertica had 2 operator-instances per
            // node (one row each = 10 raw rows). Distinct-node count is the
            // meaningful number for a user; raw count is appended as "(N
            // instances)" when it exceeds nodes so power users can still see it.
            const rawCount  = Number(ev._count || 1);
            const nodeCount = Number(ev._nodeCount || rawCount);
            let countHint = '';
            if (nodeCount > 1 || rawCount > 1) {
                const nodesPart = nodeCount > 1 ? `triggered on ${nodeCount} nodes` : 'triggered on 1 node';
                const instancesPart = (rawCount > nodeCount)
                    ? ` (${rawCount} instances)` : '';
                countHint = `<span class="event-count-hint" title="${esc(nodeCount)} distinct node${nodeCount===1?'':'s'} fired this event. ${rawCount > nodeCount ? rawCount+' raw rows in v_monitor.query_events - multiple operator-instances per node.' : 'One row per node.'}">${nodesPart}${instancesPart}</span>`;
            }
            const action = ev.suggested_action
                ? `<div class="small-copy" style="margin-top:6px;"><span style="color:#cdd8ee;font-weight:700;">Suggested action:</span> ${esc(ev.suggested_action)}</div>` : '';
            // v74 (Maya feedback on v73 image 2): bad events like
            // GROUP_BY_SPILLED were rendered in the same neutral cyan-ish
            // color as everything else. Use the CANONICAL_EVENT_CATALOG
            // polarity (bad/warn/good) to color the event_type name red,
            // orange, or green. Same palette as the card tiny-badges so
            // the visual language is consistent: spot the red, look there.
            const evType = String(ev.event_type || '');
            const evKind = (CANONICAL_EVENT_CATALOG[evType] || {}).kind || '';
            const evTypeClass = evKind ? `event-type event-type-${evKind}` : 'event-type';
            return `<div class="event-card"><div class="event-head"><strong class="${evTypeClass}">${esc(evType || '(event)')}</strong>${countHint}</div><div class="small-copy">${esc(ev.event_description||'')}</div>${action}</div>`;
        }).join('')
        : '<div class="empty">No query events were returned for this path.</div>';

    const eventsSec =
        `<div class="sec">`+
            `<div class="sec-hdr"><span class="ico ico-det"></span><span class="ttl">Query Events (${esc(dedupedEvents.length)}${events.length !== dedupedEvents.length ? ` / ${esc(events.length)} raw rows` : ''}) ${renderHelpChip('popup-events')}</span></div>`+
            `<div class="sec-body">${eventsSection}</div>`+
        `</div>`;

    return popupHeader(`Path ${node.path_id}`, titleText, subLine) +
        `<div class="popup-body">`+
            statusBanner +
            perfSection +
            estSection +
            execSection +
            detailSection +
            opSection +
            eventsSec +
        `</div>`;
}
// v58 (F-EDGE-LABEL-01): edge popup per MOCKUP_SPEC section 6.
// Header shows: "Edge: Path X -> Path Y", distribution display name
// in cyan (Broadcast / Local Resegment / Global+Local Resegment /
// Resegment / Local), plus the bracketed code ([I-B-H], [GLR-H], etc.)
// as subline. DATA FLOW section lists:
//   - Distribution (display name, coarse-color-keyed)
//   - Join Position (Outer / Inner, omitted if no side - e.g. GROUPBY)
//   - Modifiers (comma-joined raw plan modifiers, e.g. "BROADCAST"
//     or "RESEGMENT, LOCAL ROUND ROBIN"; omitted when empty)
//   - Rows on Edge
// PER-NODE LAST OPERATOR ROWS (mockup subsection) is deferred to a
// later ship along with the new SQL counter query Q-EDGE-LASTOPROWS-01.
function edgeKindTitle(kind){
    if(kind==='broadcast') return 'Broadcast';
    if(kind==='resegment') return 'Resegment';
    return 'Local';
}
function renderEdgePopup(edge){
    const distributionName = edge.distribution_name || edgeKindTitle(edge.kind);
    const code             = edge.label || 'FLOW';
    const sideDisplay      = edge.side === 'outer' ? 'Outer'
                           : edge.side === 'inner' ? 'Inner'
                           : '';
    const modifiers        = Array.isArray(edge.modifiers) ? edge.modifiers : [];
    const rowsOnEdge       = formatInt(edge.rows || 0);
    const perNodeRows      = Array.isArray(edge.per_node_last_op) ? edge.per_node_last_op : [];
    const edgeLabelChip    = renderSrcChip('F-EDGE-LABEL-01');
    const rowsOnEdgeChip   = renderSrcChip('F-EDGE-ROWS-01');
    const perNodeChip      = renderSrcChip('Q-EDGE-LASTOPROWS-01');

    // --- DATA FLOW section ---
    let dataFlow = '';
    dataFlow += `<div class="k">Distribution ${renderHelpChip('edge-distribution')}${edgeLabelChip}</div>`
             +  `<div class="v">${esc(distributionName)}</div>`;
    if(sideDisplay){
        dataFlow += `<div class="k">Join Position ${renderHelpChip('edge-join-position')}</div>`
                 +  `<div class="v">${esc(sideDisplay)}</div>`;
    }
    if(modifiers.length){
        dataFlow += `<div class="k">Modifiers ${renderHelpChip('edge-modifiers')}</div>`
                 +  `<div class="v">${esc(modifiers.join(', '))}</div>`;
    }
    dataFlow += `<div class="k">Rows on Edge ${renderHelpChip('edge-rows')}${rowsOnEdgeChip}</div>`
             +  `<div class="v">${esc(rowsOnEdge)}</div>`;

    // --- PER-NODE LAST OPERATOR ROWS section (v58) ---
    // v59: default-expanded. The per-node list is the main payload of this
    // popup, so collapsing it by default hid the new feature behind a chevron.
    // A 5-node cluster is fully visible; very wide clusters (>10) still
    // collapse to keep the popup scannable.
    const perNodeDefaultCollapsed = perNodeRows.length > 10 ? 'collapsed' : '';
    const perNodeSection = perNodeRows.length
        ? `<div class="sec ${perNodeDefaultCollapsed}">`+
            `<div class="sec-hdr clickable ${perNodeDefaultCollapsed}" onclick="this.parentNode.classList.toggle('collapsed');this.classList.toggle('collapsed');">`+
                `<span class="ico ico-exec"></span>`+
                `<span class="ttl">Per-node Last Operator Rows (${esc(perNodeRows.length)} nodes) ${renderHelpChip('edge-per-node-rows')}${perNodeChip}</span>`+
                `<span class="chev">&#9660;</span>`+
            `</div>`+
            `<div class="sec-body">`+
                perNodeRows.map(pn => {
                    const nn = pn.node_name || '?';
                    const op = pn.operator_name || '';
                    const rows = formatInt(Number(pn.rows || 0));
                    return `<div class="exec-row">`+
                             `<span class="nn">${esc(nn)}</span>`+
                             `<span class="rt">`+
                               (op ? `<span class="thr">${esc(op)}</span>` : '')+
                               `${esc(rows)}`+
                             `</span>`+
                           `</div>`;
                }).join('')+
            `</div>`+
          `</div>`
        : '';

    // v58: header arrow FLIPPED to match data-flow direction. Internally
    //   from_path_id = parent = the JOIN RECEIVING data (downstream)
    //   to_path_id   = child  = the step PRODUCING data   (upstream)
    // So the arrow reads upstream -> downstream: "Path 5 -> Path 1" means
    // data flows from path 5 into path 1. Connected Steps echoes the same
    // labels so nothing contradicts.
    return popupHeader(
                `Edge: Path ${edge.to_path_id} \u2192 Path ${edge.from_path_id}`,
                distributionName,
                `[${code}]`
           ) +
        `<div class="popup-body">`+
            `<div class="sec">`+
                `<div class="sec-hdr"><span class="ico ico-perf"></span><span class="ttl">Data Flow</span></div>`+
                `<div class="sec-body metric-list">${dataFlow}</div>`+
            `</div>`+
            perNodeSection+
            `<div class="sec">`+
                `<div class="sec-hdr"><span class="ico ico-det"></span><span class="ttl">Connected Steps</span></div>`+
                `<div class="sec-body">`+
                    `<div class="info-card"><strong>Upstream (Path ${esc(edge.to_path_id)})</strong><div class="small-copy">${esc(edge.to_title)}</div></div>`+
                    `<div class="info-card"><strong>Downstream (Path ${esc(edge.from_path_id)})</strong><div class="small-copy">${esc(edge.from_title)}</div></div>`+
                    (edge.to_description?`<div class="small-copy" style="margin-top:8px;">${esc(edge.to_description)}</div>`:'')+
                `</div>`+
            `</div>`+
        `</div>`;
}
function relativeBoxWithinAncestor(el, ancestor){
    if(!el || !ancestor) return null;
    let top=0, left=0;
    let node=el;
    while(node && node !== ancestor){
        top += node.offsetTop || 0;
        left += node.offsetLeft || 0;
        node = node.offsetParent;
    }
    if(node !== ancestor) return null;
    return {top,left,width: el.offsetWidth || 0,height: el.offsetHeight || 0,right:left + (el.offsetWidth || 0),bottom: top + (el.offsetHeight || 0)};
}
// --- Phase 1 popup positioning (v3 - cursor-anchored, body-parented) ---
// The popup is moved to <body> at DOMContentLoaded, so position:fixed
// resolves against the viewport (and is NOT broken by the transform on
// #treeStage). Here we simply place the popup next to the click cursor.
function positionPopup(anchorInfo){
    const popup = document.getElementById('floatingPopup');
    if(!anchorInfo || popup.classList.contains('hidden')) return;

    const el = anchorInfo.el;
    const pointerX = (anchorInfo.pointerX != null) ? anchorInfo.pointerX : null;
    const pointerY = (anchorInfo.pointerY != null) ? anchorInfo.pointerY : null;
    const hasPointer = (pointerX != null && pointerY != null);

    // Reset max-height so measurement is fresh for the new anchor.
    popup.style.maxHeight = '';
    // v57 fix: every measurement and decision below is done in VISUAL
    // (viewport) pixels - rect from getBoundingClientRect is visual,
    // pointerX/Y and vw/vh are visual. At the very end we divide the
    // chosen left/top/maxHeight by the popup's CSS zoom factor before
    // writing to style.*, because style.* values are interpreted in
    // LAYOUT (pre-zoom) pixels. Without this final conversion the popup
    // ends up at layout=visual, meaning its rendered position is
    // visual*zoom - much closer to the top-left than intended at zoom<1.
    const z = getPopupZoom();
    const popupWidth = popup.getBoundingClientRect().width || 560;

    const pad = 12;
    const margin = 14;
    const vw = window.innerWidth;
    // v59: reserve 26px at the bottom for the activity status bar so the
    // popup never clips behind it.
    const vh = window.innerHeight - 26;

    const rect = (el && typeof el.getBoundingClientRect === 'function')
        ? el.getBoundingClientRect()
        : null;

    // Horizontal: prefer to the right of the clicked card so the popup
    // doesn't cover the card. Fall back to the left of the card, then to
    // the cursor, then centered.
    let left;
    if(rect && rect.width > 0){
        if(rect.right + margin + popupWidth <= vw - pad){
            left = rect.right + margin;
        } else if(rect.left - margin - popupWidth >= pad){
            left = rect.left - popupWidth - margin;
        } else if(hasPointer){
            left = pointerX + margin;
            if(left + popupWidth > vw - pad) left = Math.max(pad, pointerX - popupWidth - margin);
        } else {
            left = Math.max(pad, vw - popupWidth - pad);
        }
    } else if(hasPointer){
        left = pointerX + margin;
        if(left + popupWidth > vw - pad) left = Math.max(pad, pointerX - popupWidth - margin);
    } else {
        left = Math.max(pad, (vw - popupWidth) / 2);
    }

    // Vertical: RIGHT AT THE MOUSE CURSOR. No upward shifting. The popup's
    // internal overflow:auto scroll handles any content that extends past
    // the viewport bottom, and the user can freely drag the popup.
    let top;
    if(hasPointer){
        top = pointerY - 10;
    } else if(rect){
        top = rect.top;
    } else {
        top = pad;
    }
    if(top < pad) top = pad;
    if(left < pad) left = pad;
    if(left + popupWidth > vw - pad) left = Math.max(pad, vw - popupWidth - pad);

    // Cap popup max-height so the popup never extends past the viewport
    // bottom. Content overflowing this cap scrolls inside the popup.
    // Floor at 160 px so very-low clicks still show something meaningful;
    // the user can scroll within the popup or drag the popup up.
    const availableBelow = vh - top - pad;
    const floor = 160;
    const capped = Math.max(floor, availableBelow);
    // v57 fix: convert visual left/top/maxHeight to layout units (divide
    // by z) just before writing. See the block comment near the top of
    // this function.
    popup.style.maxHeight = `${Math.min(vh - 2 * pad, capped) / z}px`;

    popup.style.left = `${left / z}px`;
    popup.style.top = `${top / z}px`;
}
function bindPopupChrome(){
    const popup = document.getElementById('floatingPopup');
    const head = popup.querySelector('.popup-head');
    if(!head) return;
    head.onmousedown = (event)=>{
        if(event.target.closest('.popup-close')) return;
        // Freeze auto-reposition the MOMENT the user grabs the header,
        // before any mousemove, so no scroll/resize event can re-snap
        // the popup during the drag.
        state.popupManuallyPositioned = true;

        // v57 fix: rect.height is visual; popup.style.maxHeight is layout.
        // Convert to layout before writing so the rendered height stays
        // at the user's current view - otherwise maxHeight would clamp
        // at visual-height (smaller rendered) and the popup would snap
        // shorter the moment the user grabbed the header at a zoomed-out
        // scale.
        const z = getPopupZoom();
        const lockedVisualHeight = popup.getBoundingClientRect().height;
        popup.style.maxHeight = `${lockedVisualHeight / z}px`;

        const startLeft = parseFloat(popup.style.left || '0') || 0;
        const startTop  = parseFloat(popup.style.top  || '0') || 0;
        const startX = event.clientX;
        const startY = event.clientY;
        popup.classList.add('dragging');

        const move = (e)=>{
            // v57 fix: event.clientX/Y are viewport (visual) pixels;
            // startLeft/startTop are layout (pre-zoom) pixels. Divide
            // the delta by z before adding, so a mouse move of 100
            // visible pixels advances style.left by 100/z layout px -
            // which the browser then renders as 100 visible pixels.
            let newLeft = startLeft + (e.clientX - startX) / z;
            let newTop  = startTop  + (e.clientY - startY) / z;
            // Soft edge clamps: keep at least a strip of header on screen
            // so the user can always grab the popup back. Clamps are
            // written against style.left/top (layout), so convert the
            // visual viewport thresholds into layout units.
            const minVisible = 60;
            const visualWidth = popup.getBoundingClientRect().width;
            const minLeft = (minVisible - visualWidth) / z;
            const maxLeft = (window.innerWidth - minVisible) / z;
            const minTop  = 0;
            // v59: 40px bottom + 26px status bar = 66px reserved.
            const maxTop  = (window.innerHeight - 66) / z;
            if(newLeft < minLeft) newLeft = minLeft;
            if(newLeft > maxLeft) newLeft = maxLeft;
            if(newTop  < minTop)  newTop  = minTop;
            if(newTop  > maxTop)  newTop  = maxTop;
            popup.style.left = `${newLeft}px`;
            popup.style.top  = `${newTop}px`;
        };
        const up = ()=>{
            popup.classList.remove('dragging');
            window.removeEventListener('mousemove', move);
            window.removeEventListener('mouseup', up);
        };
        window.addEventListener('mousemove', move);
        window.addEventListener('mouseup', up);
    };
}
function showPopup(html, anchorInfo){
    const popup = document.getElementById('floatingPopup');
    const scroll = ensurePopupStructure(popup);
    state.lastAnchor = anchorInfo;
    // A fresh card/edge click always re-anchors the popup automatically.
    state.popupManuallyPositioned = false;
    // Writing into .popup-scroll preserves the 8 resize handles (siblings of
    // .popup-scroll), which would otherwise be destroyed by popup.innerHTML=.
    scroll.innerHTML = html;
    // Reset the popup-scroll to top so the new content starts at the header.
    scroll.scrollTop = 0;
    // v57 fix: re-apply CSS `zoom` from the current state.scale every time
    // the popup is shown. Every pixel inside the popup (text, icons, chips,
    // padding, borders) scales uniformly from a single root property - same
    // effect as the tree's `transform: scale()` on #treeStage. Doing this
    // at showPopup() time guarantees even a cold-start popup (one never
    // opened before the user first touched the zoom) paints at the right
    // size on its very first frame, independent of whether inline style
    // survived any prior hide/show cycle.
    popup.style.zoom = popupScaleFont();
    popup.classList.remove('hidden');
    bindPopupChrome();
    requestAnimationFrame(()=>positionPopup(anchorInfo));
}
function selectNode(index,event){
    state.activeType='node'; state.activeIndex=index;
    document.querySelectorAll('.node-card').forEach((el,idx)=>el.classList.toggle('active', idx===index));
    const anchor=document.querySelector(`.node-card[data-node-index="${index}"]`);
    showPopup(renderNodePopup(state.nodes[index]), {el:anchor,pointerX:event?.clientX ?? event?.pageX ?? null,pointerY:event?.clientY ?? event?.pageY ?? null});
}
function selectEdge(index,event){
    state.activeType='edge'; state.activeIndex=index;
    document.querySelectorAll('.node-card').forEach(el=>el.classList.remove('active'));
    const anchor=document.querySelector(`.edge-button[data-edge-index="${index}"]`);
    showPopup(renderEdgePopup(state.edges[index]), {el:anchor,pointerX:event?.clientX ?? event?.pageX ?? null,pointerY:event?.clientY ?? event?.pageY ?? null});
}
function repositionActivePopup(){
    if(state.popupManuallyPositioned) return;
    const selector = state.activeType==='edge'
        ? `.edge-button[data-edge-index="${state.activeIndex}"]`
        : `.node-card[data-node-index="${state.activeIndex}"]`;
    const live = document.querySelector(selector);
    if(live){ positionPopup({el: live}); return; }
    if(state.lastAnchor) positionPopup(state.lastAnchor);
}
function closePopup(){
    const popup=document.getElementById('floatingPopup');
    popup.classList.add('hidden');
    popup.classList.remove('dragging');
}
async function loadProfile(){
    const response=await fetch(`/api/profile_run?profile_id=${encodeURIComponent(profileId)}`);
    if(!response.ok){ document.getElementById('tree').innerHTML='<div class="empty">Failed to load profile data.</div>'; return; }
    const data=await response.json();
    renderSummary(data.summary||{});
    renderTree(data.nodes||[]);
    applyScale();
}
document.getElementById('zoomIn').addEventListener('click',()=>{ state.scale=Math.min(1.8,state.scale+.1); applyScale(); });
// v71.5 fix (Maya feedback: "50% zoom is not enough"): extend the minimum
// zoom from 0.5 down to 0.3 (30%). Wide plans - 7+ leaves per subtree,
// 14+ depth - simply do not fit in viewport at 50%; going to 30% gives
// enough overview to navigate before clicking in to inspect.
document.getElementById('zoomOut').addEventListener('click',()=>{ state.scale=Math.max(.3,state.scale-.1); applyScale(); });
// v71.4: Reset returns to 0.8 (the new default) rather than 1.0, so the
// zoom controls round-trip cleanly from whatever zoom the user picked
// back to the initial fit-the-tree state.
document.getElementById('zoomReset').addEventListener('click',()=>{ state.scale=0.8; applyScale(); });
// v82 item 4 (Maya request): mouse-wheel on the exec-steps graph zooms the
// whole card graph. Wheel DOWN = zoom out (smaller cards); wheel UP = zoom
// in (larger cards). Same clamps and step as the +/- buttons (.1 per notch,
// [0.3, 1.8]). preventDefault() stops the browser from scrolling the page
// in response. When the wheel fires over an element INSIDE the card graph -
// a card, an edge label, the SVG connector layer - the event bubbles up to
// #treeScroll and we treat it as a zoom gesture there.
//
// We do NOT require Ctrl to zoom (the Skew page uses Ctrl+wheel because
// there the default scroll behavior matters - long lists of rows. Here the
// scroll container is bounded so plain-wheel zooming is more natural and
// matches what Maya asked for).
(function setupWheelZoom(){
    const scrollEl = document.getElementById('treeScroll');
    if (!scrollEl) return;
    scrollEl.addEventListener('wheel', function(ev){
        // Don't hijack the wheel when the cursor is over the floating
        // legend box (when expanded it may overflow and need inner scroll).
        const legend = document.getElementById('floatingLegend');
        if (legend && legend.contains(ev.target)) return;
        ev.preventDefault();
        const dir = (ev.deltaY > 0) ? -0.1 : 0.1;  // down=out, up=in
        state.scale = Math.max(0.3, Math.min(1.8, state.scale + dir));
        applyScale();
    }, { passive: false });
})();
// v53 fix 5: wire the three tree-scroll resize handles to startTreeScrollResize.
(function wireTreeScrollResize(){
    const wrap = document.getElementById('treeScrollWrap');
    if(!wrap) return;
    ['rh-b','rh-bl','rh-br'].forEach(cls => {
        const h = wrap.querySelector('.' + cls);
        if(h) h.addEventListener('mousedown', (ev) => startTreeScrollResize(ev, cls));
    });
})();
document.getElementById('treeScroll').addEventListener('scroll',()=>{
    // Intentionally no auto-reposition on tree-scroll. The popup lives on
    // <body> with position:fixed so it stays in the viewport while the user
    // scrolls the tree. Re-anchoring on scroll would snap the popup away
    // from the card the user clicked. A new click cleanly re-anchors.
});
// v71.5.3 (Maya's request): drag-to-pan on the tree viewport. Click and
// hold any empty space inside #treeScroll, drag to pan in any direction.
// Implementation: capture mousedown only when target is the scroll container
// itself or the tree-stage padding (NOT a card or popup). Track delta and
// apply via scrollLeft/scrollTop. Add 'panning' class to set grabbing cursor.
(function setupDragPan(){
    const scrollEl = document.getElementById('treeScroll');
    if (!scrollEl) return;
    let panning = false, startX = 0, startY = 0, startScrollL = 0, startScrollT = 0;
    // Identify "empty" targets safely: the scroll container, the tree-stage
    // wrapper, and the tree itself. NOT cards (.tree-node-card) or the popup.
    const isPanTarget = (el) => {
        if (!el) return false;
        if (el === scrollEl) return true;
        if (el.id === 'treeStage' || el.id === 'tree') return true;
        // SVG layer used to draw the connector lines
        if (el.tagName && el.tagName.toLowerCase() === 'svg' &&
            el.classList && el.classList.contains('tree-edges')) return true;
        return false;
    };
    scrollEl.addEventListener('mousedown', (ev) => {
        if (ev.button !== 0) return;          // left button only
        if (!isPanTarget(ev.target)) return;  // ignore clicks on cards/edges/popup
        panning = true;
        startX = ev.clientX;
        startY = ev.clientY;
        startScrollL = scrollEl.scrollLeft;
        startScrollT = scrollEl.scrollTop;
        scrollEl.classList.add('panning');
        ev.preventDefault();
    });
    // Use document-level mousemove/mouseup so pan continues even if the
    // cursor leaves the scrollEl bounds (typical drag-pan UX).
    document.addEventListener('mousemove', (ev) => {
        if (!panning) return;
        const dx = ev.clientX - startX;
        const dy = ev.clientY - startY;
        scrollEl.scrollLeft = startScrollL - dx;
        scrollEl.scrollTop  = startScrollT - dy;
    });
    const stopPan = () => {
        if (!panning) return;
        panning = false;
        scrollEl.classList.remove('panning');
    };
    document.addEventListener('mouseup', stopPan);
    document.addEventListener('mouseleave', stopPan);
})();
window.addEventListener('resize',()=>{
    // Intentionally no auto-reposition on resize either. Click a card to
    // re-anchor if the layout changed significantly.
});
// v57 workflow fix: the popup now stays open until the user explicitly
// dismisses it. There are only four close paths:
//   1. Click the X button inside the popup header (calls hidePopup()).
//   2. Click a node card or edge button - this doesn't "close" so much as
//      re-fill the popup with the new target's content via showPopup().
//   3. Press Escape (keydown handler below).
//   4. Navigate away / close the tab (browser handles).
// Previously a document-level mousedown handler closed the popup on any
// click outside it. That created a cascade: click a help-chip inside the
// popup to open the #srcOverlay, click the X inside the srcOverlay to
// close help - the same mousedown bubbled to document, saw the target was
// outside #floatingPopup, and closed the popup too. Removing the handler
// eliminates the cascade and matches the user's expectation that clicking
// "something else" on the page (zoom strip, summary cards, legend, help
// overlay chrome) leaves the current popup undisturbed.
document.addEventListener('keydown', (event) => {
    if(event.key !== 'Escape') return;
    // Close whichever overlay is currently visible, topmost first.
    // The help/src overlay (z-index 10000) sits above the popup (z-index
    // 9999); if it's open, Esc dismisses it and leaves the popup alone.
    // Only if no overlay is up does Esc close the popup.
    const srcOverlay = document.getElementById('srcOverlay');
    if(srcOverlay && srcOverlay.classList.contains('open')){
        closeSrcOverlay();
        return;
    }
    closePopup();
});
// CRITICAL FIX: Move the popup out of #treeStage (which has a transform
// applied by the zoom controls) and into <body>. Without this, the popup's
// position:fixed resolves against the transformed #treeStage, not the
// viewport, and the popup lands near the top of the page no matter where
// the user clicks after scrolling. This single line is the fix for the
// "popup opens near card 2 instead of card 6" bug.
(function relocatePopupToBody(){
    const popup = document.getElementById('floatingPopup');
    if(popup && popup.parentElement !== document.body){
        document.body.appendChild(popup);
    }
    // Build the .popup-scroll + 8 resize handles now, so the first call to
    // renderTree() -> hide-without-destroying can find .popup-scroll.
    if(popup) ensurePopupStructure(popup);
})();
loadProfile();
</script>
</body>
</html>
'''

# v77 (Maya's 10 items on v76):
#   1. KPI font size reduced + wrap fixed; zoom (+/-/Reset) buttons added;
#      panel is now full width of viewport.
#   2. Popup appears on CLICK of a bar only (no hover).
#   3. Popup is draggable + resizable using the same .floating-popup
#      infrastructure as PROFILE_HTML (8 resize handles, popup-head drag).
#   4. Drag-to-pan on empty chart area (same pattern as tree page).
#   5. Ctrl+wheel on the chart surface zooms (bar width + height + font
#      scale uniformly via --chart-scale). Plain wheel still scrolls.
#   6. Bars glow (shadowBlur + shadowColor on itemStyle).
#   7. Column titles above chart: "Execution Step", "Skew (ms)", "Vertica Node".
#   8. Bars use a light-to-dark blue glass gradient ramp: bar 0 is the
#      lightest, bar N the darkest. Each bar also has an internal top-
#      light / bottom-dark vertical glass gradient for the illusion.
#   9. (i) info-chip next to the title opens a modal showing the exact
#      SQL text that produced the data (payload.sql_text).
#   10. (?) help-chip opens a modal with a static explanation plus a
#       dynamic per-query summary synthesized from the payload.
SKEW_HTML = r'''
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>Skew in Executers Time Between Nodes</title>
    <style>
        :root {
            --line: rgba(124, 167, 255, 0.16);
            --text: #e7f0ff;
            --muted: #90a4cf;
            --cyan: #13c7ff;
            --shadow: 0 22px 60px rgba(0,0,0,.34);

            --card-bg:
                linear-gradient(90deg,
                    rgba(14,30,58,.92),
                    rgba(20,33,60,.74) 45%,
                    rgba(27,42,78,.88));
            --card-border:  var(--line);
            --card-shadow:  var(--shadow);
            --ink-1:        #eef4ff;
            --ink-2:        #bcd1f4;
            --ink-3:        #8fa4cd;
            --hairline:     rgba(124, 167, 255, 0.12);
            --bar-muted:    rgba(124, 152, 200, 0.32);
            --bar-muted-2:  rgba(8, 16, 34, 0.56);
            --accent:       #4aa3ff;
            --accent-soft:  rgba(74, 163, 255, 0.18);
            --accent-ink:   #cfe4ff;

            /* v77 item 1 + item 5: chart-scale drives bar size, row
               pitch, and label font size. Changed by the +/-/Reset
               buttons and by Ctrl+wheel on the chart container. Clamp
               at the button handlers: 0.5 .. 2.5. */
            --chart-scale:  1.0;
        }
        * { box-sizing: border-box; }
        html, body { height: 100%; }
        body {
            margin: 0;
            font-family: Inter, system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif;
            color: var(--text);
            background:
                radial-gradient(circle at top left, rgba(28,86,187,.22), transparent 28%),
                radial-gradient(circle at top right, rgba(159,99,255,.14), transparent 26%),
                linear-gradient(90deg,#04102a 0%,#0b1631 26%,#11244a 50%,#0b1631 74%,#04102a 100%);
            -webkit-font-smoothing: antialiased;
            -moz-osx-font-smoothing: grayscale;
        }
        body::before {
            content: '';
            position: fixed;
            inset: 0;
            pointer-events: none;
            background:
                linear-gradient(rgba(255,255,255,.015) 1px, transparent 1px),
                linear-gradient(90deg, rgba(255,255,255,.015) 1px, transparent 1px);
            background-size: 56px 56px;
            opacity: .35;
        }
        /* v77 item 1: full viewport width, minus a small gutter. */
        .page {
            width: calc(100% - 24px);
            margin: 20px auto 48px;
            display: flex;
            flex-direction: column;
            gap: 16px;
        }
        .glass {
            background: linear-gradient(90deg, rgba(14,30,58,.92), rgba(20,33,60,.74) 45%, rgba(27,42,78,.88));
            border: 1px solid var(--line);
            border-radius: 18px;
            box-shadow: var(--shadow);
            backdrop-filter: blur(14px);
        }
        .hero {
            padding: 18px 22px;
            display: grid;
            grid-template-columns: 1fr auto;
            gap: 14px;
            align-items: center;
        }
        .hero h1 {
            margin: 0 0 8px;
            font-size: 20px;
            line-height: 1.2;
            color: var(--cyan);
            font-weight: 800;
            letter-spacing: .005em;
            display: inline-flex;
            align-items: center;
            gap: 8px;
        }
        .meta-row { display: flex; gap: 10px; flex-wrap: wrap; align-items: center; }
        .meta-label { color: var(--muted); font-size: 12px; }
        .meta-pill {
            display: inline-flex; align-items: center;
            padding: 4px 8px; border-radius: 8px;
            border: 1px solid rgba(80,131,220,.25);
            background: rgba(5,12,25,.36);
            color: #75d6ff;
            font-size: 12px; font-weight: 700;
        }
        .back-btn, .control-btn {
            border: 1px solid rgba(126,154,214,.22);
            background: rgba(8,16,34,.6);
            color: var(--text);
            border-radius: 10px;
            padding: 8px 12px;
            cursor: pointer;
            font-weight: 700;
            text-decoration: none;
            font-size: 13px;
        }
        .back-btn:hover, .control-btn:hover { background: rgba(20,35,66,.8); }
        .icon-btn {
            width: 34px; padding: 0; text-align: center;
            font-size: 18px; line-height: 32px;
        }

        /* v77 item 9 + 10: small chip buttons next to the title and
           title-row items. Same visual language as PROFILE_HTML's
           .help-chip so the two pages feel like one app. */
        .sk-chip {
            display: inline-flex; align-items: center; justify-content: center;
            width: 20px; height: 20px;
            border-radius: 999px;
            background: rgba(83,163,255,.18);
            color: #bcd4fb;
            font-size: 11px; font-weight: 800;
            cursor: pointer;
            border: 1px solid rgba(83,163,255,.25);
            user-select: none;
        }
        .sk-chip:hover { background: rgba(83,163,255,.3); color: #fff; }
        .sk-chip.info-chip { font-family: serif; font-style: italic; }

        /* Dark report card - the main BI surface. */
        .report-card {
            background: var(--card-bg);
            border: 1px solid var(--card-border);
            border-radius: 20px;
            box-shadow: var(--card-shadow);
            overflow: hidden;
        }
        .report-head {
            padding: 20px 24px 14px;
            border-bottom: 1px solid var(--hairline);
        }
        .report-eyebrow {
            color: var(--ink-3);
            font-size: 11px;
            font-weight: 700;
            letter-spacing: .14em;
            text-transform: uppercase;
            margin-bottom: 8px;
        }
        .report-title {
            color: var(--ink-1);
            font-size: 20px;
            font-weight: 800;
            line-height: 1.22;
            letter-spacing: -0.01em;
            margin: 0;
            display: inline;
        }
        .report-title-row {
            display: flex; align-items: center; gap: 10px; flex-wrap: wrap;
        }
        .report-sub {
            color: var(--ink-2);
            font-size: 13px;
            line-height: 1.55;
            margin-top: 10px;
            max-width: 90ch;
        }

        /* v77 item 1: reduced KPI font sizes; "Worst Step" long text
           now wraps cleanly instead of bursting its tile. */
        .kpi-row {
            display: grid;
            grid-template-columns: repeat(3, 1fr);
            gap: 12px;
            padding: 14px 24px 4px;
        }
        .kpi {
            padding: 10px 14px;
            border-radius: 12px;
            background: var(--bar-muted-2);
            border: 1px solid var(--hairline);
            min-width: 0;
        }
        .kpi .k {
            font-size: 10px;
            color: var(--ink-3);
            font-weight: 700;
            letter-spacing: .1em;
            text-transform: uppercase;
            margin-bottom: 5px;
        }
        .kpi .v {
            font-size: 15px;          /* was 20 - Maya: "too big, lines warped" */
            font-weight: 800;
            color: var(--ink-1);
            letter-spacing: -0.005em;
            line-height: 1.25;
            word-break: break-word;
            overflow-wrap: anywhere;
        }
        .kpi.accent {
            background: var(--accent-soft);
            border-color: rgba(74,163,255,0.3);
        }
        .kpi.accent .v { color: var(--accent-ink); }

        /* v77 item 1: zoom controls row. Small, right-aligned. */
        .chart-controls {
            display: flex; align-items: center; justify-content: flex-end;
            gap: 6px; padding: 4px 24px 0;
            color: var(--ink-3); font-size: 11px;
        }
        .chart-controls .spacer { flex: 1; }
        .chart-controls .hint {
            color: var(--ink-3); font-size: 11px; margin-right: 6px;
            font-weight: 500;
        }

        /* v77 item 7: column-title row above the chart. Three
           semantic labels so the user knows what each column is. */
        .chart-col-titles {
            display: grid;
            grid-template-columns: minmax(160px, 22%) 1fr minmax(160px, 22%);
            gap: 10px;
            padding: 10px 24px 6px;
            border-top: 1px solid var(--hairline);
            border-bottom: 1px solid var(--hairline);
            background: rgba(8,16,34,.4);
            font-size: 10.5px;
            font-weight: 800;
            letter-spacing: .11em;
            text-transform: uppercase;
            color: var(--ink-3);
        }
        .chart-col-titles .c1 { text-align: left; }
        .chart-col-titles .c2 { text-align: center; }
        .chart-col-titles .c3 { text-align: right; }

        /* Chart panel. v77 item 4 + 5: container is the pan & zoom
           target. `cursor: grab` (and `.panning` -> grabbing) echoes
           PROFILE_HTML's tree viewport convention.
           v78 (Maya items 1, 2, 4): max-height was 100vh-240px which
           caused vertical scroll on short viewports. Chart-wrap now
           scrolls both axes only when the chart's intrinsic size
           exceeds the wrap - at scale 1.0 the chart fits the wrap
           width exactly so no scroll is shown by default. */
        .chart-wrap {
            padding: 6px 10px 22px;
            overflow: auto;
            max-height: calc(100vh - 200px);
            min-height: 320px;
            cursor: grab;
        }
        .chart-wrap.panning { cursor: grabbing; }
        .chart-wrap.panning * { cursor: grabbing !important; }
        /* v78 (Maya item 1): skewChart width is ALWAYS exactly 100% of
           its parent (chart-wrap) at scale 1.0, and grows proportionally
           above 1.0. Width/height are set INLINE by drawChart from JS
           state, so the old CSS var trick is gone. min-width:100% means
           at scale<1 the chart still fills the wrap; it just has more
           whitespace on the right. */
        #skewChart {
            width: 100%;
            min-width: 100%;
            min-height: 300px;
        }

        /* v78 (Maya item 6): toggle buttons + flip-card shell. The
           flip animation is w3schools-style: two faces, 3D rotation,
           .flipped on the inner wrapper switches sides in 0.7s. The
           "front" shows the skew chart, the "back" shows the duration
           chart - same visual language, different data + palette. */
        .sk-toggle-row {
            display: flex; align-items: center; gap: 8px;
            padding: 12px 24px 0;
        }
        .sk-toggle {
            display: inline-flex;
            border: 1px solid rgba(124,167,255,.22);
            border-radius: 10px;
            overflow: hidden;
            background: rgba(8,16,34,.5);
        }
        .sk-toggle button {
            border: 0;
            padding: 7px 16px;
            background: transparent;
            color: var(--ink-2);
            font-weight: 700;
            font-size: 12.5px;
            letter-spacing: .03em;
            cursor: pointer;
            transition: background .15s, color .15s;
        }
        .sk-toggle button.active {
            background: rgba(74,163,255,.22);
            color: #eef4ff;
            box-shadow: inset 0 0 0 1px rgba(124,167,255,.35);
        }
        .sk-toggle button:not(.active):hover {
            background: rgba(20,35,66,.6); color: #d3e0f7;
        }
        .sk-toggle-caption {
            color: var(--ink-3); font-size: 11.5px; font-weight: 500;
            margin-left: 4px;
        }

        .flip-card {
            perspective: 1800px;
        }
        .flip-card-inner {
            position: relative;
            width: 100%;
            /* Height is set by JS so the card matches the taller of the
               two faces and the flip doesn't jump. */
            transform-style: preserve-3d;
            transition: transform 0.75s cubic-bezier(0.4, 0.1, 0.2, 1);
        }
        .flip-card-inner.flipped { transform: rotateY(180deg); }
        .flip-card-face {
            position: absolute;
            inset: 0;
            width: 100%;
            backface-visibility: hidden;
            -webkit-backface-visibility: hidden;
        }
        .flip-card-face.back { transform: rotateY(180deg); }

        /* Status bar at bottom. */
        .footer-note {
            color: var(--muted);
            font-size: 11px;
            text-align: center;
            padding: 2px 4px 0;
            letter-spacing: .02em;
        }

        /* -----------------------------------------------------------
           v77 items 2 + 3: floating popup that shows bar details on
           click, draggable via its head, resizable via 8 handles.
           Structure matches PROFILE_HTML's .floating-popup exactly so
           the two pages feel the same. CSS copied verbatim where it
           can be, slightly adapted for this page's content.
           ----------------------------------------------------------- */
        .sk-popup {
            position: fixed;
            width: 360px;
            min-width: 240px;
            max-width: calc(100vw - 32px);
            max-height: min(86vh, calc(100vh - 32px));
            display: flex;
            flex-direction: column;
            overflow: hidden;
            resize: none;
            border-radius: 14px;
            border: 1px solid rgba(120,180,255,0.55);
            background: linear-gradient(180deg, rgba(17,31,59,.98), rgba(16,30,55,.985));
            box-shadow: 0 24px 42px rgba(0,0,0,.42), 0 0 18px rgba(83,163,255,0.22);
            z-index: 9999;
            font-size: 12px;
            color: var(--text);
        }
        .sk-popup.hidden { display: none; }
        .sk-popup.dragging, .sk-popup.resizing { user-select: none; }
        .sk-popup-scroll {
            flex: 1 1 auto;
            min-height: 0;
            overflow: auto;
            border-radius: inherit;
        }
        .sk-resize-handle {
            position: absolute; background: transparent; z-index: 50;
        }
        .sk-rh-top    { top: 0;    left: 14px; right: 14px;  height: 5px;  cursor: ns-resize; }
        .sk-rh-bottom { bottom: 0; left: 14px; right: 14px;  height: 5px;  cursor: ns-resize; }
        .sk-rh-left   { left: 0;   top: 14px;  bottom: 14px; width: 5px;   cursor: ew-resize; }
        .sk-rh-right  { right: 0;  top: 14px;  bottom: 14px; width: 5px;   cursor: ew-resize; }
        .sk-rh-tl { top: 0;    left: 0;    width: 12px; height: 12px; cursor: nwse-resize; }
        .sk-rh-tr { top: 0;    right: 0;   width: 12px; height: 12px; cursor: nesw-resize; }
        .sk-rh-bl { bottom: 0; left: 0;    width: 12px; height: 12px; cursor: nesw-resize; }
        .sk-rh-br { bottom: 0; right: 0;   width: 12px; height: 12px; cursor: nwse-resize; }

        .sk-popup-head {
            padding: 12px 14px 10px;
            border-bottom: 1px solid rgba(125,162,225,.14);
            position: sticky; top: 0;
            background: linear-gradient(180deg, rgba(17,31,59,.99), rgba(17,31,59,.94));
            cursor: move;
        }
        .sk-popup-close {
            position: absolute; right: 8px; top: 8px;
            width: 24px; height: 24px; border-radius: 999px;
            border: 1px solid rgba(126,154,214,.18);
            background: rgba(6,14,30,.9); color: #a8badf;
            cursor: pointer; z-index: 60;
            font-size: 14px; line-height: 1;
        }
        .sk-popup-eyebrow {
            color: var(--muted); font-size: 10px; font-weight: 700;
            text-transform: uppercase; letter-spacing: .05em;
            padding-right: 28px; margin-bottom: 4px;
        }
        .sk-popup-title {
            color: var(--cyan); font-size: 15px; font-weight: 900;
            line-height: 1.28; padding-right: 24px; word-break: break-word;
        }
        .sk-popup-body { padding: 10px 14px 14px; }
        .sk-row { display: flex; justify-content: space-between; gap: 12px; margin: 3px 0; }
        .sk-k { color: var(--ink-3); font-weight: 600; font-size: 11.5px; }
        .sk-v { color: var(--ink-1); font-weight: 700; font-size: 11.5px; font-variant-numeric: tabular-nums; text-align: right; }
        .sk-v.accent { color: var(--accent-ink); }
        .sk-section {
            margin-top: 10px; padding-top: 10px;
            border-top: 1px solid rgba(124,167,255,.18);
        }
        .sk-section-title {
            color: var(--ink-3); font-size: 10.5px; font-weight: 800;
            letter-spacing: .05em; text-transform: uppercase;
            margin-bottom: 5px;
        }

        /* -----------------------------------------------------------
           v77 items 9 + 10: modal overlays for (i) sql and (?) help.
           Self-contained (no dependency on PROFILE_HTML's help system).
           Click backdrop or X to close. Esc also closes.
           ----------------------------------------------------------- */
        .sk-overlay {
            position: fixed; inset: 0;
            background: rgba(2,8,20,.72);
            display: none; z-index: 10000;
            align-items: center; justify-content: center;
            padding: 20px;
        }
        .sk-overlay.show { display: flex; }
        .sk-modal {
            background: linear-gradient(180deg, rgba(17,31,59,.98), rgba(16,30,55,.985));
            border: 1px solid rgba(120,180,255,0.55);
            border-radius: 14px;
            box-shadow: 0 24px 42px rgba(0,0,0,.5), 0 0 18px rgba(83,163,255,0.22);
            color: var(--text);
            width: min(760px, 100%);
            max-height: calc(100vh - 40px);
            display: flex; flex-direction: column; overflow: hidden;
        }
        .sk-modal-head {
            padding: 14px 18px; display: flex; justify-content: space-between;
            align-items: center; border-bottom: 1px solid rgba(125,162,225,.14);
        }
        .sk-modal-title { color: var(--cyan); font-size: 16px; font-weight: 800; }
        .sk-modal-close {
            width: 28px; height: 28px; border-radius: 999px;
            border: 1px solid rgba(126,154,214,.22);
            background: rgba(6,14,30,.9); color: #a8badf;
            cursor: pointer; font-size: 16px; line-height: 1;
        }
        .sk-modal-body {
            padding: 16px 20px; overflow: auto; font-size: 13px; line-height: 1.55;
            color: var(--ink-2);
        }
        .sk-modal-body h4 {
            margin: 14px 0 6px; color: var(--ink-1);
            font-size: 13px; font-weight: 800;
            letter-spacing: .03em; text-transform: uppercase;
        }
        .sk-modal-body h4:first-child { margin-top: 0; }
        .sk-modal-body p, .sk-modal-body li { color: var(--ink-2); }
        .sk-modal-body ul { padding-left: 20px; margin: 6px 0 10px; }
        .sk-modal-body li { margin: 3px 0; }
        .sk-modal-body pre {
            background: rgba(5,12,25,.6);
            border: 1px solid var(--hairline);
            border-radius: 8px;
            padding: 12px 14px;
            font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
            font-size: 12px;
            line-height: 1.5;
            color: #d4e3ff;
            white-space: pre;
            overflow: auto;
            margin: 4px 0;
        }
        .sk-modal-body .sql-kw  { color: #ffa07a; font-weight: 700; }
        .sk-modal-body .sql-str { color: #b5c7a8; }
        .sk-modal-body .sql-num { color: #8fb4d9; }
        .sk-modal-body code {
            background: rgba(5,12,25,.5); padding: 1px 5px;
            border-radius: 4px; font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
            font-size: 12px; color: #d4e3ff;
        }

        /* Mobile. */
        @media (max-width: 640px) {
            .page { width: calc(100% - 16px); margin: 12px auto 32px; gap: 12px; }
            .hero { grid-template-columns: 1fr; padding: 14px 16px; }
            .hero h1 { font-size: 17px; }
            .meta-row { gap: 6px; }
            .meta-pill { font-size: 11px; padding: 3px 7px; }
            .back-btn, .control-btn {
                justify-self: start; font-size: 12px; padding: 6px 10px;
            }
            .report-head { padding: 16px 18px 12px; }
            .report-title { font-size: 16px; }
            .report-sub { font-size: 12px; }
            .kpi-row { grid-template-columns: 1fr; padding: 10px 18px 2px; gap: 8px; }
            .kpi { padding: 10px 12px; }
            .kpi .v { font-size: 14px; }
            .chart-col-titles { padding: 8px 18px 5px; font-size: 9.5px; }
            .chart-wrap { padding: 4px 2px 16px; }
        }
    </style>
</head>
<body>
    <div class="page">
        <div class="glass hero">
            <div>
                <h1>Skew in Executers Time Between Nodes</h1>
                <div class="meta-row">
                    <span class="meta-label">Transaction</span>
                    <span id="metaTx" class="meta-pill">-</span>
                    <span class="meta-label">Statement</span>
                    <span id="metaStmt" class="meta-pill">-</span>
                </div>
            </div>
            <a class="back-btn" href="/app">Back to app</a>
        </div>

        <div class="report-card">
            <div class="report-head">
                <div class="report-eyebrow">Execution Steps - Ranked by Cross-Node Skew</div>
                <div class="report-title-row">
                    <h2 class="report-title" id="reportTitle">Loading...</h2>
                    <!-- v77 items 9 + 10: chips next to the title. -->
                    <span id="skInfoChip"  class="sk-chip info-chip" title="Show the SQL query used for this page">i</span>
                    <span id="skHelpChip"  class="sk-chip"           title="What does this page show?">?</span>
                </div>
                <p class="report-sub" id="reportSub">Fetching cross-node timing from dc_query_executions.</p>
            </div>

            <div class="kpi-row" id="kpiRow" style="display:none;">
                <div class="kpi accent">
                    <div class="k">Worst Step</div>
                    <div class="v" id="kpiStep">-</div>
                </div>
                <div class="kpi">
                    <div class="k">Max Skew</div>
                    <div class="v" id="kpiSkew">-</div>
                </div>
                <div class="kpi">
                    <div class="k">Slowest Node</div>
                    <div class="v" id="kpiNode">-</div>
                </div>
            </div>

            <!-- v77 item 1: zoom controls -->
            <div class="chart-controls">
                <span class="spacer"></span>
                <span class="hint">Ctrl+wheel on chart to zoom</span>
                <button id="skZoomOut"   class="control-btn icon-btn" type="button" title="Zoom out">&minus;</button>
                <button id="skZoomIn"    class="control-btn icon-btn" type="button" title="Zoom in">+</button>
                <button id="skZoomReset" class="control-btn"          type="button" title="Reset zoom">Reset</button>
            </div>

            <!-- v78 (Maya item 6): Skew / Duration toggle. Clicking the
                 inactive button flips the card 3D to show the other view.
                 Each face has its own chart instance so ECharts animations
                 don't collide during the flip. -->
            <div class="sk-toggle-row">
                <div class="sk-toggle" role="tablist" aria-label="Chart view">
                    <button id="skViewSkewBtn"     class="active" type="button" role="tab" aria-selected="true">Skew</button>
                    <button id="skViewDurationBtn"              type="button" role="tab" aria-selected="false">Duration</button>
                </div>
                <span class="sk-toggle-caption" id="skToggleCaption">Cross-node skew per execution step</span>
            </div>

            <!-- v77 item 7 + v78 item 6: column titles. The middle
                 column label changes with the active view: "Skew (ms)"
                 when skew is on, "Duration (ms)" when duration is on. -->
            <div class="chart-col-titles" aria-hidden="true">
                <div class="c1">Execution Step</div>
                <div class="c2" id="skCol2Title">Skew (ms)</div>
                <div class="c3" id="skCol3Title">Vertica Node</div>
            </div>

            <!-- v78 item 6: flip card with two faces. Front = skew,
                 Back = duration. Inner wrapper gets .flipped to rotate. -->
            <div class="chart-wrap" id="chartWrap">
                <div class="flip-card" id="skFlipCard">
                    <div class="flip-card-inner" id="skFlipInner">
                        <div class="flip-card-face front">
                            <div id="skewChart"     role="img" aria-label="Ranked cross-node skew per execution step"></div>
                        </div>
                        <div class="flip-card-face back">
                            <div id="durationChart" role="img" aria-label="Ranked slowest-node duration per execution step"></div>
                        </div>
                    </div>
                </div>
            </div>
        </div>

        <div class="footer-note" id="footerNote"></div>
    </div>

    <!-- Floating popup (initially hidden). Click a bar to open, drag head to move, drag handles to resize. -->
    <aside id="skPopup" class="sk-popup hidden" aria-hidden="true"></aside>

    <!-- Info overlay (SQL) and help overlay (static + dynamic). -->
    <div class="sk-overlay" id="skInfoOverlay">
        <div class="sk-modal">
            <div class="sk-modal-head">
                <div class="sk-modal-title">Query behind this page</div>
                <button class="sk-modal-close" id="skInfoClose" type="button">&times;</button>
            </div>
            <div class="sk-modal-body" id="skInfoBody"></div>
        </div>
    </div>
    <div class="sk-overlay" id="skHelpOverlay">
        <div class="sk-modal">
            <div class="sk-modal-head">
                <div class="sk-modal-title">About this page</div>
                <button class="sk-modal-close" id="skHelpClose" type="button">&times;</button>
            </div>
            <div class="sk-modal-body" id="skHelpBody"></div>
        </div>
    </div>

    <script src="https://cdn.jsdelivr.net/npm/echarts@5.5.1/dist/echarts.min.js"></script>
    <script>
    (function(){
        'use strict';
        var PROFILE_ID = '__PROFILE_ID__';

        // State that survives redraws.
        var state = {
            data:          null,
            rows:          [],
            byCat:         {},
            // v78: one chart instance per flip-card face + shared zoom
            // state. viewMode: 'skew' | 'duration' tracks which face
            // the toggle buttons have flipped to.
            chartSkew:     null,
            chartDuration: null,
            userScale:     1.0,
            viewMode:      'skew',
            rendered:      false,
        };

        // ----- Formatters ----------------------------------------------------
        function fmtMs(n){
            n = Number(n || 0);
            if (!isFinite(n) || n <= 0) return '0 ms';
            if (n >= 60000) return (n/1000).toFixed(1) + ' s';
            if (n >= 1000) return (n/1000).toFixed(2) + ' s';
            if (n >= 100) return n.toFixed(0) + ' ms';
            return n.toFixed(1) + ' ms';
        }
        function escHtml(s){
            return String(s == null ? '' : s)
                .replace(/&/g,'&amp;').replace(/</g,'&lt;')
                .replace(/>/g,'&gt;').replace(/"/g,'&quot;');
        }
        function truncate(s, max){
            s = String(s == null ? '' : s);
            return s.length > max ? s.slice(0, max - 1) + '\u2026' : s;
        }
        function shortTs(ts){
            var s = String(ts || '');
            if (!s) return '-';
            var m = s.match(/(\d{2}:\d{2}:\d{2}(?:\.\d{1,6})?)/);
            if (!m) return s;
            var hms = m[1];
            var dot = hms.indexOf('.');
            if (dot >= 0 && hms.length - dot > 4) hms = hms.slice(0, dot + 4);
            return hms;
        }

        // ----- v77 item 8: blue-glass bar colors ----------------------------
        // Light-to-dark ramp by rank: bar 0 (longest) = lightest, bar N
        // = darkest. Each returned color is an ECharts LinearGradient with
        // a vertical top-light / bottom-dark stop, giving the glass look.
        function barGradient(rank, count){
            // t: 0 (top bar = lightest) .. 1 (bottom bar = darkest).
            var t = count <= 1 ? 0 : (rank / (count - 1));
            function lerp(a,b,k){ return Math.round(a + (b-a)*k); }
            // Top-rank palette:   R 126 G 200 B 255 (bright sky blue)
            // Bottom-rank palette: R 29  G 78  B 170 (deep navy blue)
            var rA = 126, gA = 200, bA = 255;
            var rB = 29,  gB = 78,  bB = 170;
            var r  = lerp(rA, rB, t);
            var g  = lerp(gA, gB, t);
            var b  = lerp(bA, bB, t);
            // Top-of-bar lighter stop ("glass highlight")
            var top = 'rgba(' +
                Math.min(255, r + 45) + ',' +
                Math.min(255, g + 30) + ',' +
                Math.min(255, b + 15) + ',0.98)';
            var mid = 'rgba(' + r + ',' + g + ',' + b + ',0.94)';
            // Bottom darker stop
            var bot = 'rgba(' +
                Math.max(0, r - 25) + ',' +
                Math.max(0, g - 25) + ',' +
                Math.max(0, b - 25) + ',0.96)';
            return {
                type: 'linear', x: 0, y: 0, x2: 0, y2: 1,
                colorStops: [
                    { offset: 0.0, color: top },
                    { offset: 0.5, color: mid },
                    { offset: 1.0, color: bot }
                ]
            };
        }
        // Rough middle-tone for the glow (shadow matches the bar's hue).
        function barGlow(rank, count){
            var t = count <= 1 ? 0 : (rank / (count - 1));
            function lerp(a,b,k){ return Math.round(a + (b-a)*k); }
            var r = lerp(150, 74, t), g = lerp(210, 140, t), b = lerp(255, 210, t);
            return 'rgba(' + r + ',' + g + ',' + b + ',0.55)';
        }

        // v78 item 6: green-glass ramp for the DURATION view. Same
        // shape as barGradient() but cool-teal/green hues so the user
        // can tell at a glance which view is active after the flip.
        // Top-rank (longest duration): R 134 G 238 B 200 (mint)
        // Bottom-rank:                  R 23  G 120 B 92  (deep teal)
        function durBarGradient(rank, count){
            var t = count <= 1 ? 0 : (rank / (count - 1));
            function lerp(a,b,k){ return Math.round(a + (b-a)*k); }
            var rA = 134, gA = 238, bA = 200;
            var rB = 23,  gB = 120, bB = 92;
            var r = lerp(rA, rB, t), g = lerp(gA, gB, t), b = lerp(bA, bB, t);
            var top = 'rgba(' +
                Math.min(255, r + 40) + ',' +
                Math.min(255, g + 15) + ',' +
                Math.min(255, b + 25) + ',0.98)';
            var mid = 'rgba(' + r + ',' + g + ',' + b + ',0.94)';
            var bot = 'rgba(' +
                Math.max(0, r - 22) + ',' +
                Math.max(0, g - 28) + ',' +
                Math.max(0, b - 22) + ',0.96)';
            return {
                type: 'linear', x: 0, y: 0, x2: 0, y2: 1,
                colorStops: [
                    { offset: 0.0, color: top },
                    { offset: 0.5, color: mid },
                    { offset: 1.0, color: bot }
                ]
            };
        }
        function durBarGlow(rank, count){
            var t = count <= 1 ? 0 : (rank / (count - 1));
            function lerp(a,b,k){ return Math.round(a + (b-a)*k); }
            var r = lerp(150, 60, t), g = lerp(245, 180, t), b = lerp(210, 140, t);
            return 'rgba(' + r + ',' + g + ',' + b + ',0.55)';
        }

        // ----- Data fetch ----------------------------------------------------
        function load(){
            fetch('/api/skew_run?profile_id=' + encodeURIComponent(PROFILE_ID), {
                credentials: 'same-origin'
            })
            .then(function(resp){
                if (resp.status === 401) { window.location.href = '/'; return null; }
                if (!resp.ok) throw new Error('HTTP ' + resp.status);
                return resp.json();
            })
            .then(function(data){
                if (!data) return;
                state.data = data;
                render(data);
            })
            .catch(function(err){
                document.getElementById('reportTitle').textContent = 'Could not load skew data';
                document.getElementById('reportSub').textContent   = String(err);
            });
        }

        // ----- Render --------------------------------------------------------
        function render(data){
            document.getElementById('metaTx').textContent   = data.transaction_id || '-';
            document.getElementById('metaStmt').textContent = data.statement_id   || '-';

            var rows = Array.isArray(data.skew_rows) ? data.skew_rows.slice() : [];
            rows.sort(function(a,b){ return (b.skew_ms||0) - (a.skew_ms||0); });
            state.rows = rows;
            state.byCat = {};
            rows.forEach(function(r){ state.byCat[r.step] = r; });

            var meaningful = !!data.skew_meaningful;
            var top = rows.length ? rows[0] : null;

            if (!rows.length) {
                document.getElementById('reportTitle').textContent = 'No distributed steps recorded';
                document.getElementById('reportSub').textContent   =
                    'dc_query_executions returned no rows where more than one node participated. ' +
                    'Either the query ran entirely on the initiator or no per-step timing was captured.';
                document.getElementById('kpiRow').style.display = 'none';
                document.getElementById('footerNote').textContent =
                    'Source: v_internal.dc_query_executions';
            } else if (!meaningful) {
                document.getElementById('reportTitle').textContent = 'No meaningful skew detected';
                document.getElementById('reportSub').textContent   =
                    'All distributed execution steps completed at similar times across every node. ' +
                    'The chart below ranks all ' + rows.length + ' step' + (rows.length === 1 ? '' : 's') +
                    ' for reference - the healthy outcome is this visual symmetry.';
                document.getElementById('kpiRow').style.display = 'none';
                document.getElementById('footerNote').textContent =
                    'Source: v_internal.dc_query_executions \u00b7 ' + rows.length +
                    ' distributed step' + (rows.length === 1 ? '' : 's');
            } else {
                // v80 (Maya): the subtitle and the Slowest-Node KPI now
                // name the node that FINISHED last, not just the one that
                // started last. This is the node the cluster actually
                // waited on. Start-time skew remains the chart-ranking
                // metric (Max Skew KPI unchanged); completion info is a
                // new read on the same step.
                var topSlowestNode   = top.last_to_finish_node  || top.slowest_node  || '-';
                var topCompletionSkew = (top.completion_skew_ms != null) ? top.completion_skew_ms : top.skew_ms;
                document.getElementById('reportTitle').textContent =
                    'Node skew concentrated in ' + top.step;
                document.getElementById('reportSub').textContent =
                    'The slowest node (' + topSlowestNode + ') finished ' +
                    fmtMs(topCompletionSkew) + ' after the fastest on this step. ' +
                    (rows.length > 1 ? (rows.length - 1) + ' other step' +
                        (rows.length - 1 === 1 ? '' : 's') + ' also show cross-node skew - the full ranking is below.' : '');
                document.getElementById('kpiStep').textContent = top.step;
                document.getElementById('kpiSkew').textContent = fmtMs(top.skew_ms);
                document.getElementById('kpiNode').textContent = topSlowestNode;
                document.getElementById('kpiRow').style.display = '';
                document.getElementById('footerNote').textContent =
                    'Source: v_internal.dc_query_executions \u00b7 ' + rows.length +
                    ' distributed step' + (rows.length === 1 ? '' : 's');
            }

            drawCharts();
            state.rendered = true;
        }

        // ----- ECharts -------------------------------------------------------
        // v78 (Maya items 1, 2, 4, 6): unified chart renderer.
        //   - Renders ONE face at a time: 'skew' or 'duration'.
        //   - Width is set INLINE on the chart <div> from JS state, so
        //     the chart never overflows the chart-wrap at scale 1.0.
        //     At scale > 1.0 the chart grows and the wrap shows a
        //     scrollbar, but scale 1.0 always fits - no more right-edge
        //     overflow hiding the bar label (items 1 + 2).
        //   - Height depends on row count * row-pitch * scale.
        //   - Uses state.userScale (NOT the removed --chart-scale CSS
        //     var), so +/-/Reset and Ctrl+wheel actually work (item 4).
        //   - Node tag on bar-end label has new behavior (item 2): if
        //     the bar + label would overflow the right edge, the label
        //     is positioned INSIDE the bar instead of outside, so every
        //     bar (short AND long) always shows its node-name tag.
        function drawOneChart(mode){
            var isDuration = (mode === 'duration');
            var containerId = isDuration ? 'durationChart' : 'skewChart';
            var container   = document.getElementById(containerId);
            if (!container) return;

            // Get data rows for this mode.
            var rows = state.rows || [];
            if (isDuration) {
                rows = rows.slice().sort(function(a,b){
                    return (b.duration_max_ms||0) - (a.duration_max_ms||0);
                });
            } else {
                // Skew view keeps the server-provided order (desc by skew_ms).
                rows = rows.slice();
            }
            var rowCount = rows.length;

            // Dispose any previous instance on THIS face before re-init.
            var prevChart = isDuration ? state.chartDuration : state.chartSkew;
            if (prevChart) { prevChart.dispose(); }

            var scale = Number(state.userScale) || 1;
            // v79 (Maya item 3): "empty line" between bars fixed by
            // tightening the per-row pitch. Was 48 px, now 30 px: at
            // scale 1.0 this leaves ~8-10 px between adjacent bars
            // instead of 26+ px. Bars still get the full barMaxWidth
            // (~22 px), so the impression of "a row" stays clear but
            // the vertical rhythm is denser - more like a real Roambi
            // bar chart and less like a sparse dot plot.
            var ROW_PITCH = 30 * scale;
            // Height: bars * pitch + padding. Minimum 300.
            var height = Math.max(300, rowCount * ROW_PITCH + 60);
            container.style.height = height + 'px';

            // Width: EXACTLY the chart-wrap content width at scale 1.0
            // so no horizontal scroll is needed by default (Maya item 1).
            // At scale > 1.0 width grows; wrap's overflow:auto reveals
            // a horizontal scrollbar.
            var wrap = document.getElementById('chartWrap');
            var wrapInner = wrap ? (wrap.clientWidth - 24) : 0;   // account for wrap padding
            if (wrapInner < 320) wrapInner = 320;
            var chartWidth = Math.round(wrapInner * scale);
            container.style.width = chartWidth + 'px';

            // Keep the flip-card's inner height in sync with the
            // active face so the flip animation doesn't squash the
            // back face.
            var flipInner = document.getElementById('skFlipInner');
            if (flipInner) flipInner.style.height = height + 'px';

            if (!rowCount) {
                var emptyChart = echarts.init(container, null, { renderer: 'canvas' });
                emptyChart.setOption({
                    grid: { left: 6, right: 28, top: 8, bottom: 6, containLabel: true },
                    xAxis: { type: 'value',
                        axisLine: { show: false }, axisTick: { show: false },
                        axisLabel: { show: false },
                        splitLine: { show: true, lineStyle: { color: 'rgba(124,167,255,0.08)' } }
                    },
                    yAxis: { type: 'category', data: [] },
                    series: [{ type: 'bar', data: [] }]
                });
                if (isDuration) state.chartDuration = emptyChart; else state.chartSkew = emptyChart;
                return;
            }

            var chart = echarts.init(container, null, { renderer: 'canvas' });
            if (isDuration) state.chartDuration = chart; else state.chartSkew = chart;

            // ECharts horizontal bar draws bottom-up, so reverse so top-rank
            // (index 0) sits at the top of the chart.
            var categories = rows.map(function(r){ return r.step; }).reverse();
            var values     = rows.map(function(r){
                return isDuration ? (r.duration_max_ms || 0) : (r.skew_ms || 0);
            }).reverse();

            // Choose gradient/glow by mode.
            var gradFn = isDuration ? durBarGradient : barGradient;
            var glowFn = isDuration ? durBarGlow    : barGlow;
            var emphColor = isDuration ? 'rgba(140,240,200,0.75)' : 'rgba(120,200,255,0.75)';

            // v79 (Maya items 1 + 2): bars NO LONGER carry a static
            // shadowBlur - the default itemStyle is clean. Glow now
            // appears ONLY on hover via the emphasis.itemStyle below.
            // glowFn is still used by the hover color so the hue stays
            // rank-matched to the bar.
            var bars = values.map(function(v, idx){
                var originalRank = rows.length - 1 - idx;
                return {
                    value: v,
                    itemStyle: {
                        color: gradFn(originalRank, rows.length),
                        borderRadius: [6, 6, 6, 6]
                    },
                    // Per-bar emphasis override so each bar's hover glow
                    // is tinted with its own rank hue instead of a flat
                    // cross-chart color. ECharts merges this with the
                    // series-level emphasis below.
                    emphasis: {
                        itemStyle: {
                            shadowBlur:  18,
                            shadowColor: glowFn(originalRank, rows.length),
                            shadowOffsetY: 0
                        }
                    }
                };
            });

            var labelFontSize = Math.max(9, Math.round(11.5 * scale));
            var yAxisFontSize = Math.max(9, Math.round(11.5 * scale));
            var maxVal = values.reduce(function(m,v){ return Math.max(m, v||0); }, 0) || 1;

            var option = {
                animation: true,
                animationDuration: 620,
                animationEasing: 'cubicOut',
                grid: {
                    left: 6,
                    right: 28,
                    top: 8,
                    bottom: 6,
                    containLabel: true
                },
                tooltip: { show: false },
                xAxis: {
                    type: 'value',
                    axisLine:  { show: false },
                    axisTick:  { show: false },
                    axisLabel: { show: false },
                    splitLine: { show: true, lineStyle: { color: 'rgba(124,167,255,0.08)' } }
                },
                yAxis: {
                    type: 'category',
                    data: categories,
                    axisLine: { show: false },
                    axisTick: { show: false },
                    axisLabel: {
                        color: '#bcd1f4',
                        fontSize: yAxisFontSize,
                        fontWeight: 600,
                        margin: 10,
                        formatter: function(val){ return truncate(val, 32); }
                    }
                },
                series: [{
                    type: 'bar',
                    data: bars,
                    barMaxWidth: Math.max(14, Math.round(22 * scale)),
                    barMinHeight: 2,
                    // v79 (Maya item 3): bar fills ~80% of its category
                    // slot, leaving ~20% as gap above/below. With the
                    // tightened ROW_PITCH above this puts bars ~6-8 px
                    // apart at scale 1.0, no more "empty row" feel.
                    barCategoryGap: '30%',
                    label: {
                        show: true,
                        // v78 item 2: for the longest bars, the label
                        // would overflow the chart's right edge and get
                        // clipped. ECharts offers 'insideRight' so the
                        // label sits at the bar's tail end inside the
                        // bar. We pick position per-bar: bars >=85% of
                        // max go inside (with a dark shadow for contrast
                        // against the light blue bar), shorter bars go
                        // outside. This guarantees every bar label is
                        // visible regardless of bar length.
                        position: 'right',
                        distance: 6,
                        fontSize: labelFontSize,
                        fontWeight: 800,
                        formatter: function(p){
                            var step = categories[p.dataIndex];
                            var r = state.byCat[step] || {};
                            // v80 (Option B discipline): the bar's VALUE
                            // determines which node to tag. Skew view
                            // shows start-time skew, so the relevant
                            // node is last-to-start (server field
                            // r.slowest_node - legacy name, kept for
                            // back-compat; the popup labels it
                            // "last to start" to match the metric).
                            // Duration view tags the longest-duration
                            // node. "Slowest to finish" is never a bar
                            // metric - it's surfaced in the popup only.
                            var nodeName = isDuration ? (r.duration_max_node || '') : (r.slowest_node || '');
                            var v = p.value || 0;
                            var nodeTag = (nodeName && v > 0) ? '  \u2022  ' + nodeName : '';
                            // Keep node tag even on narrow screens for
                            // the TOP bars - truncate instead. Maya: the
                            // longer bars had NO node tag in the v77 UI.
                            var w = (chart.getWidth && chart.getWidth()) || 0;
                            if (w && w < 340 && nodeName) {
                                // very narrow: drop the bullet + truncate
                                nodeTag = '  ' + (nodeName.length > 14 ? nodeName.slice(0,13)+'\u2026' : nodeName);
                            }
                            var isInside = (v / maxVal) >= 0.85;
                            var style = isInside ? 'inside' : 'outside';
                            return '{' + style + '|' + fmtMs(v) + nodeTag + '}';
                        },
                        rich: {
                            // Outside labels: light on dark background
                            outside: {
                                color: '#eef4ff',
                                fontSize: labelFontSize,
                                fontWeight: 800
                            },
                            // Inside labels: dark on light bar, for
                            // contrast. textShadowBlur adds a subtle
                            // glow so the text stays readable even on
                            // the lightest top bar.
                            inside: {
                                color: '#071a33',
                                fontSize: labelFontSize,
                                fontWeight: 800,
                                textShadowColor: 'rgba(255,255,255,0.55)',
                                textShadowBlur: 4
                            }
                        }
                    },
                    // Push the inside-labels to the right end of the bar
                    // instead of left. ECharts horizontal bar default
                    // position 'right' aligns to the tail which is
                    // exactly what we want. For insideRight specifically
                    // ECharts has labelLayout but that's chart-wide;
                    // simpler to keep position:'right' and rely on the
                    // rich color split above.
                    labelLayout: function(params){
                        // When the formatter returned {inside|...}, offset
                        // the label LEFT so it sits INSIDE the bar end.
                        // ECharts >=5 supports labelLayout function; if
                        // not available the label just stays at the tail
                        // outside the bar (graceful fallback, still visible).
                        var dataIndex = params.dataIndex;
                        var v = values[dataIndex] || 0;
                        if ((v / maxVal) >= 0.85) {
                            return { dx: -(params.labelRect.width + 14) };
                        }
                        return {};
                    },
                    emphasis: {
                        focus: 'none',
                        itemStyle: {
                            shadowBlur: 22,
                            shadowColor: emphColor
                        }
                    }
                }]
            };

            chart.setOption(option);

            chart.on('click', function(params){
                if (params && params.componentType === 'series') {
                    var step = categories[params.dataIndex];
                    var r = state.byCat[step];
                    if (r) showSkewPopup(r, params.event && params.event.event);
                }
            });
        }

        // Draw both faces. Called from render() and after every scale change.
        function drawCharts(){
            drawOneChart('skew');
            drawOneChart('duration');
        }

        // Back-compat shim: legacy call sites that used drawChart(rows)
        // now just trigger a full redraw of both faces using state.rows.
        function drawChart(rows){
            if (rows) state.rows = rows;
            drawCharts();
        }

        // Debounced window-resize: redraw both charts so width tracks
        // the wrap's new content box.
        if (!window.__skResizeHooked) {
            window.__skResizeHooked = true;
            window.addEventListener('resize', function(){
                clearTimeout(window.__skResizeTimer);
                window.__skResizeTimer = setTimeout(function(){
                    drawCharts();
                }, 90);
            });
        }

        // ----- v77 items 2 + 3: floating popup with drag + resize ------------
        function ensurePopupStructure(popup){
            if (!popup.querySelector('.sk-popup-scroll')){
                var sides = ['top','bottom','left','right','tl','tr','bl','br'];
                sides.forEach(function(side){
                    var h = document.createElement('div');
                    h.className = 'sk-resize-handle sk-rh-' + side;
                    h.dataset.side = side;
                    h.addEventListener('mousedown', function(ev){ startPopupResize(ev, side, popup); });
                    popup.appendChild(h);
                });
                var scroll = document.createElement('div');
                scroll.className = 'sk-popup-scroll';
                popup.appendChild(scroll);
            }
            return popup.querySelector('.sk-popup-scroll');
        }

        function startPopupResize(ev, side, popup){
            ev.preventDefault(); ev.stopPropagation();
            var rect = popup.getBoundingClientRect();
            var startX = ev.clientX, startY = ev.clientY;
            var startLeft = rect.left, startTop = rect.top;
            var startW = rect.width, startH = rect.height;
            var isN = (side === 'top'    || side === 'tl' || side === 'tr');
            var isS = (side === 'bottom' || side === 'bl' || side === 'br');
            var isW = (side === 'left'   || side === 'tl' || side === 'bl');
            var isE = (side === 'right'  || side === 'tr' || side === 'br');
            var MIN_W = 220, MIN_H = 140;
            popup.style.maxHeight = 'none';
            popup.style.maxWidth  = 'none';
            popup.classList.add('resizing');
            function move(e){
                var dx = e.clientX - startX, dy = e.clientY - startY;
                var newLeft = startLeft, newTop = startTop, newW = startW, newH = startH;
                if (isE) newW = Math.max(MIN_W, startW + dx);
                if (isW) {
                    var w = Math.max(MIN_W, startW - dx);
                    newLeft = startLeft + (startW - w);
                    newW = w;
                }
                if (isS) newH = Math.max(MIN_H, startH + dy);
                if (isN) {
                    var h = Math.max(MIN_H, startH - dy);
                    newTop = startTop + (startH - h);
                    newH = h;
                }
                popup.style.left = newLeft + 'px';
                popup.style.top  = newTop  + 'px';
                popup.style.width  = newW + 'px';
                popup.style.height = newH + 'px';
            }
            function up(){
                document.removeEventListener('mousemove', move);
                document.removeEventListener('mouseup', up);
                popup.classList.remove('resizing');
            }
            document.addEventListener('mousemove', move);
            document.addEventListener('mouseup', up);
        }

        function makePopupDraggable(popup, handle){
            handle.addEventListener('mousedown', function(ev){
                // Ignore clicks on the close button / resize handles.
                if (ev.target.closest('.sk-popup-close')) return;
                if (ev.target.classList && ev.target.classList.contains('sk-resize-handle')) return;
                ev.preventDefault();
                var rect = popup.getBoundingClientRect();
                var offX = ev.clientX - rect.left, offY = ev.clientY - rect.top;
                popup.classList.add('dragging');
                function mv(e){
                    popup.style.left = (e.clientX - offX) + 'px';
                    popup.style.top  = (e.clientY - offY) + 'px';
                }
                function up(){
                    document.removeEventListener('mousemove', mv);
                    document.removeEventListener('mouseup', up);
                    popup.classList.remove('dragging');
                }
                document.addEventListener('mousemove', mv);
                document.addEventListener('mouseup', up);
            });
        }

        function renderPopupContent(r){
            // v80 (Maya: "node0003 isn't the slowest"):
            // Option B naming discipline. The word "slowest" is reserved
            // for the node that FINISHED last (start + duration) - the
            // only node the cluster actually waited on. Start-time fields
            // get explicit "last to start" / "first to start" labels so
            // no reader can confuse a dispatch timestamp with a "who held
            // us up" judgement. The chart still ranks by start-time skew
            // (that's what the user asked to keep); completion data is
            // surfaced here, in the popup, where the user has already
            // earned the detail.
            var nodeTimes = Array.isArray(r.node_times) ? r.node_times : [];
            var nodeRows = '';
            if (nodeTimes.length){
                nodeRows += '<div class="sk-section">' +
                    '<div class="sk-section-title">Per-node offset from first to start</div>';
                nodeTimes.forEach(function(nt){
                    // v80: highlight = "last to start", not "slowest".
                    // A node that started last isn't necessarily slow;
                    // it might just have been dispatched late.
                    var isLastStart = (nt.node === r.slowest_node) && r.skew_ms > 0;
                    var attempts = nt.attempt_count || 1;
                    var tail = '';
                    if (attempts > 1 && nt.last_offset_ms !== undefined &&
                        nt.last_offset_ms !== nt.offset_ms) {
                        tail = ' <span style="color:var(--muted);font-weight:500;">' +
                               '(' + attempts + ' attempts, last +' +
                               escHtml(fmtMs(nt.last_offset_ms)) + ')</span>';
                    } else if (attempts > 1) {
                        tail = ' <span style="color:var(--muted);font-weight:500;">' +
                               '(' + attempts + ' attempts)</span>';
                    }
                    nodeRows +=
                        '<div class="sk-row">' +
                            '<span class="sk-k"' + (isLastStart ? ' style="color:var(--accent-ink);font-weight:800;"' : '') + '>' +
                                escHtml(nt.node) + (isLastStart ? ' \u25c0 last to start' : '') +
                            '</span>' +
                            '<span class="sk-v' + (isLastStart ? ' accent' : '') + '">+' +
                                escHtml(fmtMs(nt.offset_ms)) + tail +
                            '</span>' +
                        '</div>';
                });
                nodeRows += '</div>';
            }

            // Per-node duration section.
            var nodeDurations = Array.isArray(r.node_durations) ? r.node_durations : [];
            var durationRows = '';
            if (nodeDurations.length){
                durationRows += '<div class="sk-section">' +
                    '<div class="sk-section-title">Per-node duration (wall-clock in step)</div>';
                nodeDurations.forEach(function(nd){
                    var isMax = (nd.node === r.duration_max_node) && (r.duration_max_ms || 0) > 0;
                    durationRows +=
                        '<div class="sk-row">' +
                            '<span class="sk-k"' + (isMax ? ' style="color:#c5f4d8;font-weight:800;"' : '') + '>' +
                                escHtml(nd.node) + (isMax ? ' \u25c0 longest' : '') +
                            '</span>' +
                            '<span class="sk-v' + (isMax ? ' accent' : '') + '">' +
                                escHtml(fmtMs(nd.duration_ms)) +
                            '</span>' +
                        '</div>';
                });
                durationRows += '</div>';
            }

            // v80: per-node COMPLETION offset section - "when did this
            // node release the cluster from this step". This is the row
            // Maya needed to see in her screenshot: the node that
            // genuinely held the cluster back, not just the node that
            // started last.
            var completionOffsets = Array.isArray(r.completion_offsets) ? r.completion_offsets : [];
            var completionRows = '';
            if (completionOffsets.length){
                completionRows += '<div class="sk-section">' +
                    '<div class="sk-section-title">Per-node completion offset (start + duration)</div>';
                completionOffsets.forEach(function(co){
                    var isSlow  = (co.node === r.last_to_finish_node)  && (r.completion_skew_ms || 0) > 0;
                    var isFirst = (co.node === r.first_to_finish_node) && (r.completion_skew_ms || 0) > 0;
                    var tag = '';
                    var style = '';
                    if (isSlow)  { tag = ' \u25c0 slowest to finish'; style = ' style="color:var(--accent-ink);font-weight:800;"'; }
                    else if (isFirst) { tag = ' \u25c0 first to finish'; style = ' style="color:#c5f4d8;font-weight:700;"'; }
                    completionRows +=
                        '<div class="sk-row">' +
                            '<span class="sk-k"' + style + '>' +
                                escHtml(co.node) + tag +
                            '</span>' +
                            '<span class="sk-v' + (isSlow ? ' accent' : '') + '">+' +
                                escHtml(fmtMs(co.completion_ms)) +
                            '</span>' +
                        '</div>';
                });
                completionRows += '</div>';
            }

            // Headline rows. "Slowest node" now exclusively names the
            // last-to-finish node. "Start skew" and "Completion skew"
            // are shown as separate numbers so the reader can see both
            // the dispatch-lag component and the overall cluster-wait
            // component at a glance.
            var slowestCell = r.last_to_finish_node
                ? (escHtml(r.last_to_finish_node) + '  \u00b7  +' + escHtml(fmtMs(r.last_to_finish_ms || 0)))
                : '-';
            var firstCell = r.first_to_finish_node
                ? (escHtml(r.first_to_finish_node) + '  \u00b7  +' + escHtml(fmtMs(r.first_to_finish_ms || 0)))
                : '-';

            return (
                '<div class="sk-popup-head">' +
                    '<button class="sk-popup-close" type="button" aria-label="Close">&times;</button>' +
                    '<div class="sk-popup-eyebrow">Execution step</div>' +
                    '<div class="sk-popup-title">' + escHtml(r.step) + '</div>' +
                '</div>' +
                '<div class="sk-popup-body">' +
                    '<div class="sk-row"><span class="sk-k">Slowest node</span>' +
                        '<span class="sk-v accent">' + slowestCell + '</span></div>' +
                    '<div class="sk-row"><span class="sk-k">First to finish</span>' +
                        '<span class="sk-v">' + firstCell + '</span></div>' +
                    '<div class="sk-row"><span class="sk-k">Completion skew</span>' +
                        '<span class="sk-v accent">' + escHtml(fmtMs(r.completion_skew_ms || 0)) + '</span></div>' +
                    '<div class="sk-row"><span class="sk-k">Start skew</span>' +
                        '<span class="sk-v">' + escHtml(fmtMs(r.skew_ms || 0)) + '</span></div>' +
                    '<div class="sk-row"><span class="sk-k">Last to start</span>' +
                        '<span class="sk-v">' + escHtml(r.slowest_node || '-') + '</span></div>' +
                    '<div class="sk-row"><span class="sk-k">First to start</span>' +
                        '<span class="sk-v">' + escHtml(r.fastest_node || '-') + '</span></div>' +
                    '<div class="sk-row"><span class="sk-k">Longest duration</span>' +
                        '<span class="sk-v">' + escHtml(fmtMs(r.duration_max_ms || 0)) +
                        (r.duration_max_node ? '  \u00b7  ' + escHtml(r.duration_max_node) : '') +
                        '</span></div>' +
                    '<div class="sk-row"><span class="sk-k">First start time</span>' +
                        '<span class="sk-v">' + escHtml(shortTs(r.first_start)) + '</span></div>' +
                    '<div class="sk-row"><span class="sk-k">Last start time</span>' +
                        '<span class="sk-v">' + escHtml(shortTs(r.last_start)) + '</span></div>' +
                    completionRows +
                    nodeRows +
                    durationRows +
                '</div>'
            );
        }

        function showSkewPopup(r, domEvent){
            var popup = document.getElementById('skPopup');
            var scroll = ensurePopupStructure(popup);
            scroll.innerHTML = renderPopupContent(r);

            // Hook the freshly-rendered close button.
            var closeBtn = scroll.querySelector('.sk-popup-close');
            if (closeBtn) closeBtn.addEventListener('click', hideSkewPopup);

            // Drag via the head. Attach once per render.
            var head = scroll.querySelector('.sk-popup-head');
            if (head) makePopupDraggable(popup, head);

            // Position near the click (or viewport-centered fallback).
            var popupW = 360, popupH = 340;
            var cx = domEvent && domEvent.clientX ? domEvent.clientX : (window.innerWidth / 2);
            var cy = domEvent && domEvent.clientY ? domEvent.clientY : (window.innerHeight / 2);
            // Prefer right of click; fall back to left if it would spill.
            var left = cx + 18;
            if (left + popupW > window.innerWidth - 16) left = Math.max(16, cx - popupW - 18);
            var top  = cy - 20;
            if (top  + popupH > window.innerHeight - 16) top = Math.max(16, window.innerHeight - popupH - 16);
            if (top  < 16) top = 16;
            popup.style.left = left + 'px';
            popup.style.top  = top  + 'px';
            popup.style.width  = popupW + 'px';
            popup.style.height = '';         // let content decide until user resizes
            popup.classList.remove('hidden');
            popup.setAttribute('aria-hidden', 'false');
        }
        function hideSkewPopup(){
            var popup = document.getElementById('skPopup');
            popup.classList.add('hidden');
            popup.setAttribute('aria-hidden', 'true');
        }

        // ----- v77 item 4: drag-to-pan on empty chart-wrap area --------------
        (function setupChartPan(){
            var wrap = document.getElementById('chartWrap');
            if (!wrap) return;
            var panning = false, startX = 0, startY = 0, startL = 0, startT = 0;
            function isPanTarget(el){
                if (!el) return false;
                if (el === wrap) return true;
                if (el.id === 'skewChart') return true;
                // ECharts internal canvas is a direct child of #skewChart.
                if (el.tagName && el.tagName.toLowerCase() === 'canvas') {
                    // BUT only when no bar sits at the click point - we leave
                    // ECharts to handle bar clicks itself. The chart.on('click')
                    // handler above stops propagation via ECharts' own logic;
                    // mousedown on empty canvas areas will bubble here.
                    return true;
                }
                return false;
            }
            wrap.addEventListener('mousedown', function(ev){
                if (ev.button !== 0) return;
                if (!isPanTarget(ev.target)) return;
                // Small delay so ECharts has a chance to register a click.
                // If the user was actually clicking a bar, the chart handler
                // will open the popup and the pan won't engage (because the
                // mouseup will fire before the move threshold).
                panning = true;
                startX = ev.clientX; startY = ev.clientY;
                startL = wrap.scrollLeft; startT = wrap.scrollTop;
                wrap.classList.add('panning');
                ev.preventDefault();
            });
            document.addEventListener('mousemove', function(ev){
                if (!panning) return;
                wrap.scrollLeft = startL - (ev.clientX - startX);
                wrap.scrollTop  = startT - (ev.clientY - startY);
            });
            function stop(){
                if (!panning) return;
                panning = false;
                wrap.classList.remove('panning');
            }
            document.addEventListener('mouseup',   stop);
            document.addEventListener('mouseleave', stop);
        })();

        // ----- v77 items 1 + 5: zoom buttons + Ctrl+wheel --------------------
        // v78 (Maya item 4): zoom now drives state.userScale directly and
        // calls drawCharts() to re-render BOTH flip-card faces. The old
        // --chart-scale CSS variable is gone.
        function applyScale(newScale){
            var clamped = Math.max(0.5, Math.min(2.5, newScale));
            state.userScale = clamped;
            drawCharts();
        }
        function getScale(){
            return Number(state.userScale) || 1;
        }
        document.getElementById('skZoomIn').addEventListener('click', function(){
            applyScale(getScale() + 0.15);
        });
        document.getElementById('skZoomOut').addEventListener('click', function(){
            applyScale(getScale() - 0.15);
        });
        document.getElementById('skZoomReset').addEventListener('click', function(){
            applyScale(1.0);
        });
        // Ctrl+wheel to zoom; plain wheel still scrolls.
        (function(){
            var wrap = document.getElementById('chartWrap');
            if (!wrap) return;
            wrap.addEventListener('wheel', function(ev){
                if (!(ev.ctrlKey || ev.metaKey)) return;
                ev.preventDefault();
                // Small step per click. Trackpad pinch also generates
                // ctrlKey+wheel events in Chrome/Safari, which works nicely.
                var dir = ev.deltaY < 0 ? +0.08 : -0.08;
                applyScale(getScale() + dir);
            }, { passive: false });
        })();

        // ----- v78 item 6: Skew / Duration toggle ---------------------------
        // Clicking the inactive tab flips the card in 3D and swaps the
        // middle-column title. Both chart instances are kept alive so
        // the flip animation doesn't need to re-render the other face.
        function setViewMode(mode){
            if (mode !== 'skew' && mode !== 'duration') return;
            if (state.viewMode === mode) return;
            state.viewMode = mode;

            var skewBtn = document.getElementById('skViewSkewBtn');
            var durBtn  = document.getElementById('skViewDurationBtn');
            var inner   = document.getElementById('skFlipInner');
            var col2    = document.getElementById('skCol2Title');
            var caption = document.getElementById('skToggleCaption');

            if (mode === 'skew') {
                skewBtn.classList.add('active');    skewBtn.setAttribute('aria-selected','true');
                durBtn.classList.remove('active');  durBtn.setAttribute('aria-selected','false');
                if (inner) inner.classList.remove('flipped');
                if (col2)  col2.textContent = 'Skew (ms)';
                if (caption) caption.textContent = 'Cross-node skew per execution step';
            } else {
                durBtn.classList.add('active');     durBtn.setAttribute('aria-selected','true');
                skewBtn.classList.remove('active'); skewBtn.setAttribute('aria-selected','false');
                if (inner) inner.classList.add('flipped');
                if (col2)  col2.textContent = 'Duration (ms)';
                if (caption) caption.textContent = 'Slowest-node duration per execution step';
            }

            // Re-fit the back face height to match the front (rows may
            // rank differently, so the count of distributed steps is the
            // same but the visual height is set inline - drawCharts()
            // already sets flipInner height to match the active face).
            drawCharts();
        }
        document.getElementById('skViewSkewBtn').addEventListener('click', function(){
            setViewMode('skew');
        });
        document.getElementById('skViewDurationBtn').addEventListener('click', function(){
            setViewMode('duration');
        });

        // ----- v77 item 9: (i) info modal ------------------------------------
        function syntaxHighlightSQL(sql){
            var kw = /\b(WITH|SELECT|FROM|WHERE|GROUP BY|ORDER BY|HAVING|AND|OR|ASC|DESC|INNER|JOIN|ON|AS|CASE|WHEN|THEN|ELSE|END|MAX|MIN|COUNT|DISTINCT|TIMESTAMPDIFF|NULL|IS|NOT|IN|LIKE|LIMIT)\b/g;
            var out = escHtml(sql);
            out = out.replace(/('[^']*')/g, '<span class="sql-str">$1</span>');
            out = out.replace(/\b(\d+)\b/g, '<span class="sql-num">$1</span>');
            out = out.replace(kw, '<span class="sql-kw">$1</span>');
            return out;
        }
        function openInfo(){
            // v78 (Maya item 6): show BOTH the skew query and the
            // duration query, labelled, so the (i) chip reflects the
            // two views of the flip-card.
            var body = document.getElementById('skInfoBody');
            var sql1 = (state.data && state.data.sql_text)          || '(SQL text not available)';
            var sql2 = (state.data && state.data.duration_sql_text) || '';
            body.innerHTML =
                '<h4>Queries behind this page</h4>' +
                '<p>The flip card has two views; each is powered by the query shown below. Both read ' +
                '<code>v_internal.dc_query_executions</code> for this transaction and statement.</p>' +
                '<h4>Skew view (default)</h4>' +
                '<p>Aggregates per execution-step across all nodes, ' +
                'then ranks the steps by cross-node skew (max minus min start time).</p>' +
                '<pre>' + syntaxHighlightSQL(sql1) + '</pre>' +
                (sql2 ?
                    ('<h4>Duration view</h4>' +
                     '<p>For each (node, execution-step) pair, the wall-clock time spent in the step ' +
                     '(<code>completion_time - time</code>). Ranks steps by the longest per-step duration.</p>' +
                     '<pre>' + syntaxHighlightSQL(sql2) + '</pre>')
                    : ''
                );
            document.getElementById('skInfoOverlay').classList.add('show');
        }
        function closeInfo(){
            document.getElementById('skInfoOverlay').classList.remove('show');
        }

        // ----- v77 item 10 + v78 item 5 + v80 naming discipline -----
        // v80 (Option B): the help modal now distinguishes three
        // related-but-not-identical concepts. The Maya "node0003 isn't
        // the slowest" observation is what forced this separation:
        //   - Start skew:       MAX(start) - MIN(start) across nodes.
        //                       What the chart ranks by. Measures DISPATCH
        //                       imbalance (catalog contention, network
        //                       lag before a node can start its portion).
        //   - Duration:         MAX(completion_time - time) per node.
        //                       What the Duration-view chart ranks by.
        //                       Measures WORK per node.
        //   - Completion skew:  MAX(start + duration) - MIN(start + duration)
        //                       across nodes. What the popup headlines
        //                       and the subtitle report as "Slowest
        //                       node". The cluster actually waits for
        //                       the last node to finish, so this is
        //                       the answer to "who held us up?".
        // The dynamic paragraph now names last_to_finish_node (the
        // real "slowest") and uses completion_skew_ms, matching the
        // popup's and subtitle's language so nothing reads as a
        // contradiction when a user compares the three.
        function openHelp(){
            var body = document.getElementById('skHelpBody');
            var data = state.data || {};
            var rows = state.rows || [];
            var dynamic = '';
            if (!rows.length) {
                dynamic =
                    '<h4>This specific query</h4>' +
                    '<p>No distributed steps were recorded. The query either ran entirely on the ' +
                    'initiator or <code>dc_query_executions</code> captured no per-step timing for it.</p>';
            } else {
                var top = rows[0];
                var others = rows.length - 1;
                // v80: prefer completion-semantic fields for the dynamic
                // sentence. Fall back to start-time fields on older
                // payloads that don't carry completion data.
                var slowName     = top.last_to_finish_node || top.slowest_node || '';
                var slowSkewMs   = (top.completion_skew_ms != null) ? top.completion_skew_ms : top.skew_ms;
                var sentence;
                if (!data.skew_meaningful) {
                    sentence =
                        'The top start-time skew is <b>' + escHtml(fmtMs(top.skew_ms)) + '</b> on step <code>' +
                        escHtml(top.step) + '</code>, which is below the threshold we consider ' +
                        'meaningful. The chart ranks every distributed step for reference.';
                } else {
                    sentence =
                        'The slowest node (<b>' + escHtml(slowName) + '</b>) finished <b>' +
                        escHtml(fmtMs(slowSkewMs)) + '</b> after the fastest on step <code>' +
                        escHtml(top.step) + '</code>.';
                    if (others > 0) {
                        sentence += ' ' + others + ' other step' + (others === 1 ? '' : 's') +
                                    ' also show cross-node skew - the full ranking is below.';
                    }
                }
                // Duration + start-skew breakdown: what each number on
                // the popup actually measures, in the user's terms.
                var breakdown = '';
                if (top.completion_skew_ms != null) {
                    breakdown =
                        '<p>For this top step the breakdown is:</p>' +
                        '<ul>' +
                            '<li><b>Start skew:</b> ' + escHtml(fmtMs(top.skew_ms)) +
                                ' (node <code>' + escHtml(top.slowest_node || '-') + '</code> started last).</li>' +
                            '<li><b>Longest duration:</b> ' + escHtml(fmtMs(top.duration_max_ms || 0)) +
                                ' on node <code>' + escHtml(top.duration_max_node || '-') + '</code>.</li>' +
                            '<li><b>Completion skew:</b> ' + escHtml(fmtMs(top.completion_skew_ms)) +
                                ' - node <code>' + escHtml(slowName) + '</code> is the slowest to finish at ' +
                                escHtml(fmtMs(top.last_to_finish_ms || 0)) + ' after the step started; the ' +
                                'first to finish was <code>' + escHtml(top.first_to_finish_node || '-') + '</code> at ' +
                                escHtml(fmtMs(top.first_to_finish_ms || 0)) + '.</li>' +
                        '</ul>';
                }
                dynamic =
                    '<h4>This specific query</h4>' +
                    '<p>' + sentence + '</p>' +
                    breakdown;
            }
            body.innerHTML =
                '<h4>What this page shows</h4>' +
                '<p>When Vertica runs a query across multiple nodes, each node executes its portion of the plan in parallel. ' +
                'The query only finishes when the <i>slowest</i> node finishes, so a single lagging node can dominate the total wall-clock time. ' +
                'This page highlights that kind of imbalance per execution step, with two views you can flip between.</p>' +
                // v80: three-concept section. The word "slowest" is
                // precise and reserved for completion semantics so we
                // never have the v79 bug where the popup called the
                // last-to-start node "slowest" even when other nodes
                // had more work and finished at the same time or later.
                '<h4>Three related numbers you will see</h4>' +
                '<ul>' +
                    '<li><b>Start skew</b> = MAX(start) - MIN(start) across nodes. Measures DISPATCH imbalance ' +
                        '(catalog contention, network hop, planning retries). <i>This is what the Skew-view chart ranks by.</i></li>' +
                    '<li><b>Duration</b> = MAX(completion_time - time) for each node. Measures WORK per node. ' +
                        '<i>This is what the Duration-view chart ranks by.</i></li>' +
                    '<li><b>Completion skew</b> = MAX(start + duration) - MIN(start + duration) across nodes. ' +
                        'The answer to "which node did the cluster wait on?". <i>The popup names this node as the ' +
                        'slowest. The subtitle and the Slowest-Node KPI use the same definition.</i></li>' +
                '</ul>' +
                '<p>A node can be "last to start" without being "slowest to finish" - for example if it started late but ' +
                'ran a small portion. Conversely, a node can be "slowest to finish" without being last to start - it ' +
                'started on time but had more work. The popup shows both dimensions so you can see which one dominates ' +
                'for a given step.</p>' +
                '<h4>Skew view</h4>' +
                '<ul>' +
                    '<li>For each execution step, we take the timestamp of every node that ran it.</li>' +
                    '<li><b>Start skew = MAX(time) - MIN(time)</b> across those nodes, in milliseconds.</li>' +
                    '<li>Steps that ran on only one node (BeforePlan, InitPlan, SerializePlan, etc.) are excluded - they cannot have skew.</li>' +
                '</ul>' +
                '<h4>Duration view</h4>' +
                '<ul>' +
                    '<li>For each (node, execution-step) pair: <b>MAX(completion_time - time)</b>, the wall-clock the node spent in that step.</li>' +
                    '<li>The chart ranks steps by the single longest per-node duration (the node that did the most work).</li>' +
                    '<li>This view answers "which step chewed the most time on any one node?" rather than "which step was most imbalanced?"</li>' +
                '</ul>' +
                '<h4>Reading the chart</h4>' +
                '<ul>' +
                    '<li>Each bar is one execution step. Longer = worse (start skew in Skew view, wall-clock in Duration view).</li>' +
                    '<li>Steps are ranked descending - the worst sits at the top.</li>' +
                    '<li>Click any bar to open a popup with the slowest-to-finish node, start times, per-node offsets, per-node durations, and per-node completion offsets.</li>' +
                    '<li>The controls above the chart (- / + / Reset) or <kbd>Ctrl</kbd>+wheel zoom only the bars.</li>' +
                    '<li>Click-and-drag an empty area of the chart to pan.</li>' +
                '</ul>' +
                '<h4>When to worry</h4>' +
                '<p>Skew matters most when it is a large fraction of the total query duration. The Profile tab link to this page is labelled ' +
                '<i>"Meaningful skew found"</i> only when the top start-time skew exceeds a threshold relative to the whole-query wall-clock.</p>' +
                '<h4>Possible causes of node skew</h4>' +
                '<ul>' +
                    '<li><b>Data-distribution skew.</b> The projection\'s segmentation key concentrates rows (or large groups) on one or two nodes, so those nodes do proportionally more I/O and CPU work. Common with <code>HASH(key)</code> on a low-cardinality or heavily-biased column. Shows up mainly as <i>duration</i> imbalance.</li>' +
                    '<li><b>Network / communication imbalance.</b> A GROUP BY, JOIN, or ORDER BY re-segments data mid-plan; the receiving node (or the sender on the slowest link) becomes the bottleneck. Visible as skew on <code>ExecutePlan:EEexecute</code> or <code>ExecutePlan:Finalize</code>.</li>' +
                    '<li><b>Hardware / storage variance.</b> One node has slower disks, a hot disk controller, a failing drive, a stale cache, a noisy neighbour on the same hypervisor, or simply less RAM free than the others. Recurring completion skew that always names the same node is a strong hint.</li>' +
                    '<li><b>Tuple Mover / Mergeout activity.</b> A node running a heavy TM operation competes for CPU and I/O with the query it\'s serving.</li>' +
                    '<li><b>Query compilation retries.</b> Planning/compilation phases (<code>PreparePlan:*</code>, <code>CompilePlan:EEpreexecute</code>) can retry on a node when a resource check fails; this shows as a late "last start" on one node (high <i>start skew</i>). The popup shows attempt counts per node.</li>' +
                    '<li><b>Resource-pool pressure.</b> One node\'s execution pool is full or queued, so the query waits on that node while the others execute. Check <code>resource_pool_status</code> per node.</li>' +
                    '<li><b>Stale statistics on a skewed column.</b> The optimiser under-estimates a join output, picks a suboptimal distribution, and one node ends up doing the remediation work at runtime.</li>' +
                    '<li><b>Cluster topology change.</b> A node was recently restored / rebalanced and has a colder buffer cache than the others.</li>' +
                '</ul>' +
                '<h4>What to do when skew is large</h4>' +
                '<ul>' +
                    '<li><b>Confirm the pattern is repeatable.</b> Re-run the query 3-5 times; transient skew (e.g. from a one-off TM job) is not worth re-designing a projection for.</li>' +
                    '<li><b>Check which dimension dominates.</b> If <i>start skew</i> is most of the completion skew it\'s a dispatch / control-plane issue (catalog contention, stats, planning retries). If <i>duration</i> is most of it it\'s a data-plane issue (segmentation, hardware, resource pool).</li>' +
                    '<li><b>Identify the dominant step.</b> If the skew is concentrated in planning/compilation phases, it\'s usually control-plane; if it\'s on <code>ExecutePlan:EEexecute</code> or <code>:Finalize</code> it\'s usually data-plane.</li>' +
                    '<li><b>Check <code>v_monitor.node_resources</code> and <code>disk_storage</code></b> for the slowest-to-finish node during the query window; look at CPU, memory, and I/O metrics to isolate hardware problems.</li>' +
                    '<li><b>Inspect the projection segmentation.</b> <code>SELECT projection_schema, projection_name, segment_expression FROM v_catalog.projections WHERE anchor_table_name=\'...\';</code>. If the segmentation expression concentrates the hot key, re-segment with a higher-cardinality key or a composite expression.</li>' +
                    '<li><b>Refresh statistics</b> on the tables / columns touched by the slow step: <code>SELECT ANALYZE_STATISTICS(\'schema.table\');</code>.</li>' +
                    '<li><b>Review the resource pool</b> used by this query class. Budgets, memory cap, and planned concurrency on the slowest-to-finish node may differ from the others.</li>' +
                    '<li><b>Run <code>ANALYZE_WORKLOAD()</code></b> for optimiser tuning suggestions against this transaction.</li>' +
                    '<li><b>If one node always lags,</b> open a ticket with Vertica support and provide this page\'s screenshot plus <code>dc_query_executions</code> output for the transaction - the combination of per-step skew, per-node duration, and per-node completion offsets narrows the root cause fast.</li>' +
                '</ul>' +
                dynamic;
            document.getElementById('skHelpOverlay').classList.add('show');
        }
        function closeHelp(){
            document.getElementById('skHelpOverlay').classList.remove('show');
        }

        // Wire chip buttons + overlay close.
        document.getElementById('skInfoChip').addEventListener('click', openInfo);
        document.getElementById('skHelpChip').addEventListener('click', openHelp);
        document.getElementById('skInfoClose').addEventListener('click', closeInfo);
        document.getElementById('skHelpClose').addEventListener('click', closeHelp);
        // Click outside modal (on backdrop) closes.
        document.getElementById('skInfoOverlay').addEventListener('click', function(ev){
            if (ev.target === ev.currentTarget) closeInfo();
        });
        document.getElementById('skHelpOverlay').addEventListener('click', function(ev){
            if (ev.target === ev.currentTarget) closeHelp();
        });
        // Escape closes popup + overlays.
        document.addEventListener('keydown', function(ev){
            if (ev.key === 'Escape') {
                hideSkewPopup(); closeInfo(); closeHelp();
            }
        });

        load();
    })();
    </script>
</body>
</html>
'''

APP_HTML = r'''
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>Vertica Database Navigator</title>
    <link rel="icon" type="image/x-icon" href="/ASSETS/verticalogo.png">
    <style>
        :root {
            --bg: #0b1020;
            --bg-2: #11182d;
            --bg-3: #151f38;
            --panel: #f6f9fc;
            --line: #d5deea;
            --text: #0f172a;
            --muted: #5d6b82;
            --accent: #0f7cff;
            --accent-dark: #0a63cd;
            --tab-active: #1a243d;
        }
        * { box-sizing: border-box; }
        body {
            font-family: Inter, -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Arial, sans-serif;
            margin: 0;
            padding: 0;
            font-size: 12px;
            height: 100vh;
            overflow: hidden;
            color: var(--text);
            background: #eef3f8;
        }
        .main-container {
            display: flex;
            height: 100vh;
            position: relative;
            overflow: hidden;
        }
        .tree-wrapper {
            position: relative;
            flex-shrink: 0;
            display: flex;
            height: 100vh;
        }
        .tree-panel {
            width: 350px;
            min-width: 220px;
            max-width: 800px;
            background-color: white;
            border-right: 1px solid var(--line);
            display: flex;
            flex-direction: column;
            height: 100vh;
        }
        .tree-toolbar {
            display: flex;
            flex-direction: column;
            gap: 8px;
            padding: 10px;
            border-bottom: 1px solid var(--line);
            background: #fbfdff;
        }
        .tree-filter-row {
            display: flex;
            gap: 8px;
            align-items: center;
        }
        .tree-filter-input {
            flex: 1;
            min-width: 0;
            padding: 7px 9px;
            border: 1px solid #c8d4e3;
            border-radius: 8px;
            font-size: 12px;
            box-sizing: border-box;
        }
        .tree-action-button, .query-button, .logout-button {
            padding: 7px 12px;
            background-color: var(--accent);
            color: white;
            border: none;
            border-radius: 8px;
            cursor: pointer;
            font-size: 12px;
            white-space: nowrap;
        }
        .tree-action-button:hover, .query-button:hover, .logout-button:hover {
            background-color: var(--accent-dark);
        }
        .tree-container {
            flex: 1;
            padding: 8px;
            overflow-y: auto;
            overflow-x: hidden;
            min-height: 0;
        }
        .resizer {
            width: 5px;
            background: #e6edf5;
            cursor: col-resize;
            height: 100vh;
            position: absolute;
            right: 0;
            top: 0;
            transition: background-color 0.2s;
            z-index: 1;
        }
        .vertical-resizer {
            width: 100%;
            height: 5px;
            background: #e6edf5;
            cursor: row-resize;
            transition: background-color 0.2s;
            margin: 3px 0;
        }
        .resizer:hover, .resizer.dragging,
        .vertical-resizer:hover, .vertical-resizer.dragging {
            background: var(--accent);
        }
        .tree-node {
            padding: 2px 0;
            cursor: pointer;
            display: block;
            border-radius: 6px;
        }
        .tree-node:hover {
            background-color: #edf4fb;
        }
        .children {
            margin-left: 20px;
            display: none;
            border-left: 1px dotted #ccd6e4;
            padding-left: 8px;
        }
        .expanded > .children { display: block; }
        .node-content {
            display: flex;
            align-items: center;
            padding: 2px 4px;
        }
        .icon {
            width: 16px;
            height: 16px;
            margin-right: 4px;
            display: inline-flex;
            align-items: center;
            justify-content: center;
        }
        .checkbox { margin-right: 4px; cursor: pointer; }
        .name {
            color: #223049;
            white-space: pre-wrap;
            word-break: break-word;
            max-width: 100%;
            overflow-wrap: break-word;
        }
        .category { color: #65758b; font-weight: 600; }
        .root { color: #0a63cd; font-weight: 700; }
        .content-area {
            flex: 1;
            display: flex;
            flex-direction: column;
            background-color: #edf2f8;
            min-width: 200px;
            overflow: hidden;
            padding: 16px;
            gap: 16px;
            box-sizing: border-box;
        }
        .topbar {
            display: flex;
            justify-content: space-between;
            align-items: center;
            gap: 12px;
        }
        .brand-title {
            margin: 0;
            font-size: 20px;
            color: #0f7cff;
        }
        .session-meta {
            display: flex;
            align-items: center;
            gap: 10px;
            color: var(--muted);
        }
        .session-badge {
            background: white;
            border: 1px solid var(--line);
            padding: 7px 10px;
            border-radius: 999px;
        }
        .content-wrapper {
            display: flex;
            flex-direction: column;
            gap: 8px;
            height: calc(100vh - 95px);
            width: 100%;
            overflow: hidden;
        }
        .query-section {
            width: 100%;
            height: 50%;
            min-height: 100px;
            display: flex;
            flex-direction: column;
            gap: 8px;
        }
        .query-editor {
            width: 100%;
            height: 100%;
            font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
            font-size: 12px;
            padding: 12px;
            resize: none;
            border: 0;
            border-radius: 10px;
            background: transparent;
            overflow: auto;
            box-sizing: border-box;
            /* v71 syntax-highlight overlay: text is rendered invisible here
               and the colored version shows through from the <pre> behind.
               Caret stays visible. */
            color: transparent;
            caret-color: #222;
            line-height: 1.5;
            letter-spacing: normal;
            tab-size: 4;
            white-space: pre-wrap;
            word-wrap: break-word;
        }
        /* v71: the wrap container holds both the editable <textarea> and the
           underlying colored <pre>. Same geometry + same padding + same
           font so the colored glyphs render exactly where the user sees
           the (invisible) textarea characters. */
        .code-editor-wrap {
            position: relative;
            width: 100%;
            height: calc(100% - 40px);
            border: 1px solid var(--line);
            border-radius: 10px;
            overflow: hidden;
            background: #ffffff;
        }
        .code-editor-wrap .code-highlight,
        .code-editor-wrap .query-editor {
            position: absolute;
            inset: 0;
            margin: 0;
            padding: 12px;
            border: 0;
            border-radius: 10px;
            box-sizing: border-box;
            font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
            font-size: 12px;
            line-height: 1.5;
            letter-spacing: normal;
            tab-size: 4;
            white-space: pre-wrap;
            word-wrap: break-word;
        }
        .code-editor-wrap .code-highlight {
            pointer-events: none;
            color: #222;
            background: transparent;
            overflow: hidden;
            z-index: 0;
        }
        .code-editor-wrap .query-editor {
            z-index: 1;
        }
        /* v71 SQL token colors, picked to sit legibly on white background
           and echo the "Reading the edge labels" palette (cyan for positions,
           green for good, orange for distribution/warn, muted for meta). */
        .sql-kw  { color: #0047ab; font-weight: 600; }   /* SELECT/FROM/WHERE/JOIN/CASE/... */
        .sql-str { color: #116329; }                     /* 'string literals'              */
        .sql-num { color: #bf5a00; }                     /* 42, 3.14, 1e6                  */
        .sql-op  { color: #0a7490; }                     /* = < > + - * / :: ||            */
        .sql-com { color: #6a737d; font-style: italic; } /* -- line or /* block comments */
        .sql-fn  { color: #6b3aa6; }                     /* function names: foo(x)         */
        .sql-id  { color: inherit; }                     /* identifiers - take default     */
        .button-container { display: flex; gap: 8px; }
        .results-section {
            width: 100%;
            height: 50%;
            min-height: 100px;
            overflow: hidden;
            border: 1px solid var(--line);
            background: white;
            box-sizing: border-box;
            border-radius: 10px;
            display: flex;
            flex-direction: column;
        }
        .results-table {
            width: 100%;
            border-collapse: collapse;
            font-size: 12px;
        }
        .results-table th, .results-table td {
            border: 1px solid #dde5ef;
            padding: 6px 8px;
            text-align: left;
            vertical-align: top;
        }
        .results-table th { background-color: #f5f8fc; font-weight: 600; }
        .tab-container {
            display: flex;
            flex-direction: column;
            height: 100%;
            background: white;
            min-height: 0;
        }
        .tab-header {
            display: flex;
            background: #f5f8fc;
            border-bottom: 1px solid var(--line);
            overflow-x: auto;
            min-height: 36px;
            padding-left: 6px;
            flex-shrink: 0;
        }
        .tab {
            padding: 8px 14px;
            background: white;
            border: 1px solid var(--line);
            border-bottom: none;
            margin: 6px 6px 0 0;
            border-radius: 8px 8px 0 0;
            cursor: pointer;
            display: flex;
            align-items: center;
            gap: 8px;
            font-size: 12px;
        }
        .tab.active {
            background: var(--tab-active);
            color: white;
            border-color: var(--tab-active);
        }
        .tab-close {
            width: 16px;
            height: 16px;
            border-radius: 50%;
            display: flex;
            align-items: center;
            justify-content: center;
            background: rgba(0,0,0,0.08);
            cursor: pointer;
        }
        .tab-content-host {
            flex: 1;
            overflow: auto;
            min-height: 0;
        }
        .tab-content {
            padding: 10px;
            display: none;
        }
        .tab-content.active { display: block; }
        .execution-info {
            font-size: 11px;
            color: #637389;
            margin-bottom: 8px;
        }
        .error-tab { color: #dc3545; background: #fff5f5; }
        .loading-indicator {
            display: inline-block;
            width: 16px;
            height: 16px;
            border: 2px solid #eef2f6;
            border-top: 2px solid var(--accent);
            border-radius: 50%;
            animation: spin 1s linear infinite;
        }
        @keyframes spin {
            0% { transform: rotate(0deg); }
            100% { transform: rotate(360deg); }
        }
        .content-footer {
            padding: 4px 10px 8px;
            font-size: 10px;
            color: #6f7f95;
            line-height: 1.3;
            text-align: center;
            border-top: 1px solid #eef2f6;
            flex-shrink: 0;
        }
        .view { color: #6b4c9a; }
        .view_definition {
            color: #666;
            font-family: monospace;
            font-size: 11px;
            white-space: pre-wrap;
            padding: 4px;
            background: #f8f8f8;
            border: 1px solid #eee;
            margin-top: 4px;
        }
        .system_table_remarks {
            color: #666;
            font-style: italic;
            padding-left: 20px;
            cursor: default;
        }
        .user-select-none {
            user-select: none;
            -webkit-user-select: none;
            -moz-user-select: none;
            -ms-user-select: none;
        }

        /* v79 (Maya general feedback): privilege-error modal. Shown
           when the server returns 403 with
           error='insufficient_privileges' - typically because the
           logged-in account lacks permission to query v_monitor /
           v_internal / v_catalog system tables used by the Profile
           Tab. The modal explains the two common remedies: (a) log
           in as dbadmin, or (b) have dbadmin delegate the role to
           the current user via GRANT + SET ROLE.
           Visual language mirrors the .sk-modal in SKEW_HTML: dark
           glass surface, blue border, cyan title, dark-blue code block
           for the SQL grant example. */
        .priv-overlay {
            position: fixed; inset: 0;
            background: rgba(2, 8, 20, 0.72);
            display: none; z-index: 10000;
            align-items: center; justify-content: center;
            padding: 20px;
        }
        .priv-overlay.show { display: flex; }
        .priv-modal {
            background: linear-gradient(180deg, rgba(17,31,59,.98), rgba(16,30,55,.985));
            border: 1px solid rgba(120,180,255,0.55);
            border-radius: 14px;
            box-shadow: 0 24px 42px rgba(0,0,0,.5), 0 0 18px rgba(83,163,255,0.22);
            color: #e7f0ff;
            width: min(780px, 100%);
            max-height: calc(100vh - 40px);
            display: flex; flex-direction: column; overflow: hidden;
        }
        .priv-head {
            padding: 14px 18px; display: flex; justify-content: space-between;
            align-items: center; border-bottom: 1px solid rgba(125,162,225,.14);
            gap: 10px;
        }
        .priv-title {
            color: #13c7ff; font-size: 16px; font-weight: 800;
            display: inline-flex; align-items: center; gap: 8px;
        }
        .priv-title .priv-badge {
            display: inline-block;
            background: rgba(255, 159, 67, 0.18);
            border: 1px solid rgba(255, 159, 67, 0.35);
            color: #ffbd80;
            font-size: 10.5px; font-weight: 800;
            letter-spacing: .08em; text-transform: uppercase;
            padding: 2px 8px; border-radius: 8px;
        }
        .priv-close {
            width: 28px; height: 28px; border-radius: 999px;
            border: 1px solid rgba(126,154,214,.22);
            background: rgba(6,14,30,.9); color: #a8badf;
            cursor: pointer; font-size: 16px; line-height: 1;
        }
        .priv-body {
            padding: 16px 20px; overflow: auto;
            font-size: 13px; line-height: 1.55;
            color: #bcd1f4;
        }
        .priv-body p { margin: 6px 0 10px; color: #bcd1f4; }
        .priv-body h4 {
            margin: 14px 0 6px; color: #eef4ff;
            font-size: 13px; font-weight: 800;
            letter-spacing: .03em; text-transform: uppercase;
        }
        .priv-body h4:first-child { margin-top: 0; }
        .priv-body code {
            background: rgba(5,12,25,.5); padding: 1px 5px;
            border-radius: 4px;
            font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
            font-size: 12px; color: #d4e3ff;
        }
        .priv-body pre {
            background: rgba(5,12,25,.6);
            border: 1px solid rgba(124,167,255,.16);
            border-radius: 8px;
            padding: 12px 14px;
            font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
            font-size: 12px;
            line-height: 1.55;
            color: #d4e3ff;
            white-space: pre;
            overflow: auto;
            margin: 6px 0 4px;
        }
        .priv-body .sql-kw  { color: #ffa07a; font-weight: 700; }
        .priv-body .sql-comment { color: #84a0c8; font-style: italic; }
        .priv-option {
            border: 1px solid rgba(124,167,255,.18);
            background: rgba(8,16,34,.4);
            border-radius: 10px;
            padding: 12px 14px;
            margin: 10px 0;
        }
        .priv-option .opt-title {
            color: #eef4ff; font-size: 13px; font-weight: 800;
            margin-bottom: 4px;
        }
        .priv-option .opt-body { color: #bcd1f4; font-size: 12.5px; }
        .priv-option .opt-note {
            color: #8fa4cd; font-size: 11.5px; font-style: italic;
            margin-top: 6px;
        }
        .priv-meta-row {
            display: flex; gap: 14px; align-items: center;
            padding: 8px 0 4px;
            font-size: 12px;
            color: #8fa4cd;
            border-bottom: 1px solid rgba(124,167,255,.10);
            margin-bottom: 12px;
        }
        .priv-meta-row b { color: #eef4ff; font-weight: 700; }
        .priv-detail {
            display: block;
            background: rgba(180, 40, 40, 0.12);
            border: 1px solid rgba(230, 100, 100, 0.26);
            color: #ffc1c1;
            padding: 8px 10px;
            border-radius: 8px;
            font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
            font-size: 11.5px;
            margin: 4px 0 10px;
            word-break: break-word;
        }
    </style>
</head>
<body>
    <!-- v79 (Maya general feedback): privilege-error modal. Hidden by
         default. showPrivilegeModal(payload) populates it from the 403
         JSON returned by the server when _is_privilege_error fires. -->
    <div class="priv-overlay" id="privilegeOverlay" aria-hidden="true">
        <div class="priv-modal" role="dialog" aria-labelledby="privModalTitle" aria-modal="true">
            <div class="priv-head">
                <div class="priv-title" id="privModalTitle">
                    <span>Vertica Permission Required</span>
                    <span class="priv-badge">Action needed</span>
                </div>
                <button class="priv-close" id="privilegeClose" type="button" aria-label="Close">&times;</button>
            </div>
            <div class="priv-body" id="privilegeBody">
                <!-- populated by showPrivilegeModal() -->
            </div>
        </div>
    </div>
    <div class="main-container">
        <div class="tree-wrapper">
            <div id="treePanel" class="tree-panel">
                <div class="tree-toolbar">
                    <button class="tree-action-button" onclick="refreshTree()">Refresh</button>
                    <div class="tree-filter-row">
                        <input id="treeFilterInput" class="tree-filter-input" type="text" placeholder="Filter schemas or tables..." onkeydown="handleFilterKey(event)">
                        <button class="tree-action-button" onclick="applyTreeFilter()">Filter</button>
                    </div>
                </div>
                <div id="tree" class="tree-container"></div>
            </div>
            <div class="resizer" id="dragMe"></div>
        </div>
        <div class="content-area">
            <div class="topbar">
                <h1 class="brand-title">Database Navigator</h1>
                <div class="session-meta">
                    <div class="session-badge">Signed in as <strong id="sessionUsername"></strong></div>
                    <button class="logout-button" onclick="logout()">Logout</button>
                </div>
            </div>
            <div class="content-wrapper">
                <div class="query-section">
                    <div class="code-editor-wrap">
                        <pre class="code-highlight" id="queryHighlight" aria-hidden="true"></pre>
                        <textarea id="queryEditor" class="query-editor" placeholder="Write your SQL queries here... Separate multiple queries with semicolons (;)" spellcheck="false"></textarea>
                    </div>
                    <div class="button-container">
                        <button class="query-button" onclick="generateQuery()">Generate Query</button>
                        <button class="query-button" onclick="beautifySQL()">✨ Beautify</button>
                        <button class="query-button" onclick="profileQuery()">Profile</button>
                        <button class="query-button" onclick="executeQueries()">Run Queries</button>
                        <button class="query-button" onclick="clearAll()">Clear All</button>
                    </div>
                </div>
                <div class="vertical-resizer" id="verticalDragMe"></div>
                <div class="results-section">
                    <div class="tab-container">
                        <div id="tabHeader" class="tab-header"></div>
                        <div id="tabContent" class="tab-content-host"></div>
                    </div>
                    <div class="content-footer">This program is provided 'as is' without warranty of any kind. Users assume all risks associated with its use. No rights to the program are granted. A valid Vertica product license is required for Vertica usage. Created by Maya Goldberg.</div>
                </div>
            </div>
        </div>
    </div>
    <script>
        let fullTreeData = null;
        let currentTreeData = null;
        let currentTabIndex = 0;
        let executingQueries = false;

        async function loadSessionInfo() {
            const response = await fetch('/api/session');
            if (!response.ok) {
                window.location.href = '/';
                return;
            }
            const data = await response.json();
            document.getElementById('sessionUsername').textContent = data.username;
        }

        async function logout() {
            await fetch('/api/logout', { method: 'POST' });
            window.location.href = '/';
        }

        async function loadTree() {
            try {
                const response = await fetch('/api/dbtree');
                if (response.status === 401) {
                    window.location.href = '/';
                    return;
                }
                if (!response.ok) throw new Error('Failed to load tree data');
                const data = await response.json();
                fullTreeData = data;
                currentTreeData = data;
                renderTree(data);
            } catch (error) {
                console.error('Error loading tree:', error);
                document.getElementById('tree').innerHTML = '<div style="color: red; padding: 10px;">Error loading database structure</div>';
            }
        }

        function renderTree(data) {
            document.getElementById('tree').innerHTML = renderNode(data);
        }

        async function refreshTree() {
            const filterInput = document.getElementById('treeFilterInput');
            if (filterInput) filterInput.value = '';
            await loadTree();
        }

        function handleFilterKey(event) {
            if (event.key === 'Enter') applyTreeFilter();
        }

        function applyTreeFilter() {
            if (!fullTreeData) return;
            const filterValue = document.getElementById('treeFilterInput').value.trim().toLowerCase();
            if (!filterValue) {
                currentTreeData = fullTreeData;
                renderTree(currentTreeData);
                return;
            }
            const filteredTree = filterTreeData(fullTreeData, filterValue);
            currentTreeData = filteredTree;
            renderTree(filteredTree);
            document.querySelectorAll('.tree-node').forEach(node => {
                if (node.querySelector('.children')) node.classList.add('expanded');
            });
        }

        function filterTreeData(treeData, filterValue) {
            const clonedRoot = JSON.parse(JSON.stringify(treeData));
            const schemasCategory = clonedRoot.children.find(child => child.name === 'Schemas');
            const systemTablesCategory = clonedRoot.children.find(child => child.name === 'System Tables');

            if (schemasCategory) {
                schemasCategory.children = schemasCategory.children
                    .map(schemaNode => {
                        const schemaNameMatches = schemaNode.name.toLowerCase().includes(filterValue);
                        const tablesCategory = schemaNode.children.find(child => child.name === 'Tables');
                        const viewsCategory = schemaNode.children.find(child => child.name === 'Views');

                        if (tablesCategory) {
                            tablesCategory.children = tablesCategory.children.filter(tableNode => schemaNameMatches || tableNode.name.toLowerCase().includes(filterValue));
                        }
                        if (viewsCategory) {
                            viewsCategory.children = viewsCategory.children.filter(viewNode => schemaNameMatches || viewNode.name.toLowerCase().includes(filterValue));
                        }

                        const hasTables = tablesCategory && tablesCategory.children.length > 0;
                        const hasViews = viewsCategory && viewsCategory.children.length > 0;
                        return (schemaNameMatches || hasTables || hasViews) ? schemaNode : null;
                    })
                    .filter(Boolean);
            }

            if (systemTablesCategory) {
                systemTablesCategory.children = systemTablesCategory.children.filter(tableNode => tableNode.name.toLowerCase().includes(filterValue));
            }
            return clonedRoot;
        }

        function getIcon(type) {
            switch(type) {
                case 'root': return '🌐';
                case 'category': return '📁';
                case 'schema': return '📑';
                case 'table': return '📋';
                case 'view': return '👁️';
                case 'column': return '🔹';
                case 'view_definition': return '📝';
                case 'system_table': return '⚙️';
                case 'system_table_remarks': return '';
                default: return '📄';
            }
        }

        function escapeHtml(text) {
            return String(text)
                .replace(/&/g, '&amp;')
                .replace(/</g, '&lt;')
                .replace(/>/g, '&gt;')
                .replace(/"/g, '&quot;')
                .replace(/'/g, '&#39;');
        }

        // v63 items 5, 6a, 8, 12: rich Profile Tab renderer.
        //
        // We still escape EVERY character from profile_text (so user-supplied
        // table/column names cannot inject HTML). Highlighting is done on the
        // already-escaped string using safe regex -> <span> substitutions,
        // looking for specific Vertica plan keywords, event_type values, and
        // the Step-xx headers.
        //
        // Three visual layers:
        //   (1) Top "Query profile main findings" callout block - built from
        //       the server's tree_analysis list (same as graph page's
        //       'tree-overview' help dynamic observations).
        //   (2) Step-xx headers get a small green underline so the eye can
        //       find them quickly while scrolling.
        //   (3) Inside Steps 05, 06: plan keywords (JOIN HASH, BROADCAST,
        //       RESEGMENT, Sort Key, PATH ID, Cost, Projection:...) in bold
        //       blue.
        //   (4) Inside Step 10: event_type column colored by Vertica's
        //       documented severity (Informational = green, Warning = orange,
        //       Critical = red) from the Vertica QUERY_EVENTS KB.
        function renderProfileText(rawText, findings){
            const findingsBlock = renderProfileFindings(findings);
            const escaped = escapeHtml(rawText);
            const highlighted = highlightProfileText(escaped);
            const pre = `<pre class="profile-text-pre" style="white-space: pre-wrap; word-break: break-word; background: #f8fbff; border: 1px solid #d5deea; border-radius: 8px; padding: 12px; margin: 0; font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: 12px; line-height: 1.5; color:#0b1020;">${highlighted}</pre>`;
            return findingsBlock + pre;
        }

        // Build the top "Query profile main findings" call-out block from the
        // list of sentences the server produced. Intentionally compact but
        // visually distinct so users see it before the raw step dump.
        function renderProfileFindings(findings){
            if (!Array.isArray(findings) || findings.length === 0) return '';
            const items = findings.map(s => `<li style="margin-bottom:6px;line-height:1.55;">${escapeHtml(s)}</li>`).join('');
            return (
                '<div class="profile-findings" style="'+
                    'background:linear-gradient(90deg,#eff8ff,#f6fbff);'+
                    'border:1px solid #bddcff;border-left:4px solid #3d8bff;'+
                    'border-radius:8px;padding:12px 16px;margin:0 0 14px;'+
                    'font-family:system-ui,-apple-system,sans-serif;color:#0b1020;">'+
                    '<div style="font-size:13px;font-weight:800;color:#0f56b8;'+
                        'letter-spacing:.04em;margin-bottom:8px;">'+
                        '&#128269; Query profile main findings'+
                    '</div>'+
                    '<ul style="margin:0;padding-left:18px;font-size:12.5px;color:#1a2433;">'+
                        items+
                    '</ul>'+
                '</div>'
            );
        }

        // Regex-based highlighting of already-HTML-escaped text. Every
        // regex below operates on post-escape characters (e.g. '&gt;' for
        // '>') so raw angle brackets never reach the HTML parser.
        function highlightProfileText(escaped){
            // (a) Mark Step-xx headers so they stand out visually.
            escaped = escaped.replace(
                /^(&gt;&gt;&gt; Step \d{2}:[^\n]*)/gm,
                '<span style="color:#056611;font-weight:800;border-bottom:2px solid #8fd78a;display:inline-block;padding-bottom:1px;margin-top:4px;">$1</span>'
            );

            // (b) Plan-keyword highlighting. We bias toward PRECISE matches
            // that are unlikely to collide with table/column names. Each is
            // wrapped in blue-bold. Order matters: longest/most-specific
            // patterns first so they don't get eaten by broader ones.
            //
            // The regex targets only tokens we know appear in
            // dc_explain_plans / query_plan_profiles path_line text. Color
            // is #0c4a9c (bold); consistent across Steps 05 and 06.
            const blueBold = (m) => '<span style="color:#0c4a9c;font-weight:700;">'+m+'</span>';

            // Join operators
            escaped = escaped.replace(
                /\b(JOIN HASH|JOIN MERGE|JOIN PIPELINED|JOIN FILTER|JOIN CROSS|HASH JOIN|MERGE JOIN|CROSS JOIN)\b/g,
                blueBold('$1')
            );
            // Distribution modifiers (parenthesized in Vertica plan text)
            escaped = escaped.replace(
                /\b(BROADCAST|GLOBAL RESEGMENT|LOCAL RESEGMENT|LOCAL ROUND ROBIN|RESEGMENT)\b/g,
                blueBold('$1')
            );
            // Other notable plan operators
            escaped = escaped.replace(
                /\b(STORAGE ACCESS|GROUPBY HASH|GROUPBY PIPELINED|GROUPBY NOTHING|GROUP BY HASH|GROUP BY PIPELINED|ANALYTICAL|UNION ALL|UNION)\b/g,
                blueBold('$1')
            );
            // Path-line annotations (Sort Key, PATH ID, Cost, Projection,
            // Materialize, Filter, Runtime Filter, Execute on, Join Cond,
            // Aggregates) - the whole "keyword:" including colon.
            // Note: use \b\w+: anchors carefully; we target explicit known
            // keywords to avoid recoloring every SQL column.
            escaped = escaped.replace(
                /\b(Sort Key|PATH ID|Cost|Rows|Projection|Materialize|Runtime Filter|Execute on|Join Cond|Aggregates|Filter)(:)/g,
                blueBold('$1$2')
            );
            // "Outer ->" / "Inner ->" markers (post-escape: '-&gt;')
            escaped = escaped.replace(
                /\b(Outer|Inner) -&gt;/g,
                '<span style="color:#0c4a9c;font-weight:700;">$1 -&gt;</span>'
            );

            // (c) Step 10 event-type severity coloring. From the Vertica KB
            // "QUERY_EVENTS" documentation, event_types map to one of:
            //   Informational -> green
            //   Warning       -> orange
            //   Critical      -> red
            // We recolor any bare token match on these event_type names
            // anywhere they appear in the text (they are unique identifiers
            // so false-positive risk is low).
            const EVENT_INFO = [
                'AUTO_PROJECTION_USED',
                'RLE_OVERRIDDEN',
                'INVALID COST',
                'RUNTIME_PREDICATE_EVAL_ORDER',
                'EE_COMPILE_MEMORY_ALLOC',
                'SMALL_MERGE_REPLACED'
            ];
            const EVENT_WARN = [
                'NO HISTOGRAM',
                'NO_HISTOGRAM',
                'PREDICATE OUTSIDE HISTOGRAM',
                'PREDICATE_OUTSIDE_HISTOGRAM',
                'NON-OPTIMIZED CONCAT',
                'NON-OPTIMIZED_CONCAT',
                'PATTERN MISMATCH',
                'PATTERN_MISMATCH',
                'WORKLOAD ANALYZER RECOMMENDATION',
                'WORKLOAD_ANALYZER_RECOMMENDATION',
                'RESEGMENTED MANY ROWS',
                'RESEGMENTED_MANY_ROWS',
                'RECEIVED MANY ROWS',
                'RECEIVED_MANY_ROWS',
                'TOO MANY ROS CONTAINERS',
                'TOO_MANY_ROS_CONTAINERS',
                'PARTITIONS_ELIMINATED',
                'PARTITIONS_NOT_ELIMINATED'
            ];
            const EVENT_CRIT = [
                'MEMORY LIMIT HIT',
                'MEMORY_LIMIT_HIT',
                'GROUP BY SPILLED',
                'GROUP_BY_SPILLED',
                'JOIN SPILLED',
                'JOIN_SPILLED',
                'PLANNING MEMORY LIMIT',
                'PLANNING_MEMORY_LIMIT',
                'WOS SPILL',
                'WOS_SPILL',
                'RESOURCE POOL TIMEOUT',
                'RESOURCE_POOL_TIMEOUT',
                'TOTAL TABLE RANGE PARTITIONS TIMEOUT',
                'TOTAL_TABLE_RANGE_PARTITIONS_TIMEOUT'
            ];
            function eventRegex(list){
                const escapedList = list.map(s => s.replace(/[.*+?^${}()|[\]\\]/g,'\\$&'));
                return new RegExp('\\b(' + escapedList.join('|') + ')\\b', 'g');
            }
            escaped = escaped.replace(eventRegex(EVENT_INFO),
                '<span style="color:#056611;font-weight:700;">$1</span>');
            escaped = escaped.replace(eventRegex(EVENT_WARN),
                '<span style="color:#a65000;font-weight:700;">$1</span>');
            escaped = escaped.replace(eventRegex(EVENT_CRIT),
                '<span style="color:#b91c1c;font-weight:700;">$1</span>');

            return escaped;
        }

        function renderNode(node) {
            let html = `<div class="tree-node" oncontextmenu="handleTreeContextMenu('${escapeHtml(node.type)}', '${escapeHtml(node.name)}', event); return false;">`;
            html += '<div class="node-content">';
            if (node.isCheckable && node.type !== 'system_table_remarks') {
                html += `<input type="checkbox" class="checkbox" onclick="event.stopPropagation();">`;
            }
            if (node.type !== 'system_table_remarks') {
                html += `<span class="icon">${getIcon(node.type)}</span>`;
            }
            html += `<span class="${node.type} name">${escapeHtml(node.name)}</span>`;
            html += '</div>';
            if (node.children && node.children.length > 0) {
                html += `<div class="children">${node.children.map(child => renderNode(child)).join('')}</div>`;
            }
            html += '</div>';
            return html;
        }

        function handleTreeContextMenu(type, name, event) {
            event.preventDefault();
            event.stopPropagation();
            const editor = document.getElementById('queryEditor');
            if (!editor) return;
            const cursorPos = editor.selectionStart;
            let insertText = '';
            if (type === 'schema') insertText = name + '.';
            else if (type === 'table') insertText = name;
            else if (type === 'column') insertText = name.split(' - ')[0];
            editor.value = editor.value.slice(0, cursorPos) + insertText + editor.value.slice(cursorPos);
            editor.focus();
            editor.selectionStart = editor.selectionEnd = cursorPos + insertText.length;
        }

        function getCheckedTableFullName() {
            const checkedBox = document.querySelector('input[type="checkbox"]:checked');
            if (!checkedBox) return null;

            let node = checkedBox.closest('.tree-node');
            const nodeElement = node.querySelector('.name');
            const nodeName = nodeElement.textContent;

            let parentNode = node.parentElement.parentElement;
            while (parentNode) {
                const categoryName = parentNode.querySelector('.name')?.textContent;
                if (categoryName === 'System Tables') return nodeName;
                if (categoryName === 'Schemas') break;
                parentNode = parentNode.parentElement;
            }

            let schemaNode = node.parentElement;
            while (schemaNode && !schemaNode.querySelector('.schema')) {
                schemaNode = schemaNode.parentElement;
            }
            const schemaName = schemaNode ? schemaNode.querySelector('.schema').textContent : '';
            return `${schemaName}.${nodeName}`;
        }

        function generateQuery() {
            const fullTableName = getCheckedTableFullName();
            if (!fullTableName) {
                alert('Please select a table or view first');
                return;
            }
            document.getElementById('queryEditor').value = `SELECT * FROM ${fullTableName} LIMIT 100;`;
            if (typeof syncHighlight === 'function') syncHighlight();
        }

        function parseQueries(queryText) {
            return queryText.split(';').map(q => q.trim()).filter(q => q.length > 0);
        }

        function createTab(label, content, isError = false) {
            const tabId = `tab-${currentTabIndex++}`;
            const tabHeader = document.createElement('div');
            tabHeader.className = `tab${isError ? ' error-tab' : ''}`;
            tabHeader.setAttribute('data-tab', tabId);
            tabHeader.addEventListener('click', (e) => {
                if (!e.target.classList.contains('tab-close')) activateTab(tabId);
            });
            tabHeader.innerHTML = `<span>${escapeHtml(label)}</span><span class="tab-close" onclick="event.stopPropagation(); closeTab('${tabId}')">×</span>`;
            const tabContent = document.createElement('div');
            tabContent.className = 'tab-content';
            tabContent.id = tabId;
            tabContent.innerHTML = content;
            document.getElementById('tabHeader').appendChild(tabHeader);
            document.getElementById('tabContent').appendChild(tabContent);
            activateTab(tabId);
            return tabId;
        }

        function activateTab(tabId) {
            document.querySelectorAll('.tab').forEach(tab => tab.classList.remove('active'));
            document.querySelectorAll('.tab-content').forEach(content => content.classList.remove('active'));
            const selectedTab = document.querySelector(`[data-tab="${tabId}"]`);
            const selectedContent = document.getElementById(tabId);
            if (selectedTab && selectedContent) {
                selectedTab.classList.add('active');
                selectedContent.classList.add('active');
            }
        }

        function closeTab(tabId) {
            const tab = document.querySelector(`[data-tab="${tabId}"]`);
            const content = document.getElementById(tabId);
            if (tab && content) {
                const isActiveTab = tab.classList.contains('active');
                if (isActiveTab) {
                    const nextTab = tab.nextElementSibling || tab.previousElementSibling;
                    tab.remove();
                    content.remove();
                    if (nextTab) activateTab(nextTab.getAttribute('data-tab'));
                } else {
                    tab.remove();
                    content.remove();
                }
            }
        }

        function clearAll() {
            document.querySelectorAll('.checkbox:checked').forEach(checkbox => { checkbox.checked = false; });
            document.getElementById('queryEditor').value = '';
            if (typeof syncHighlight === 'function') syncHighlight();
            document.getElementById('tabHeader').innerHTML = '';
            document.getElementById('tabContent').innerHTML = '';
            currentTabIndex = 0;
        }

        function beautifySQL() {
            const editor = document.getElementById('queryEditor');
            const originalText = editor.value;
            fetch('/api/beautify_sql', {
                method: 'POST',
                headers: {'Content-Type': 'application/json'},
                body: JSON.stringify({ query: originalText })
            })
            .then(response => {
                if (response.status === 401) {
                    window.location.href = '/';
                    throw new Error('Not authenticated');
                }
                if (!response.ok) throw new Error('Failed to beautify SQL');
                return response.json();
            })
            .then(result => {
                editor.value = result.query || originalText;
                // v71: refresh the syntax-highlight overlay so the colored
                // rendering catches the new text. Without this call the
                // overlay would still show the pre-beautify version until
                // the user types.
                if (typeof syncHighlight === 'function') syncHighlight();
            })
            .catch(error => {
                if (error.message !== 'Not authenticated') alert('Failed to beautify SQL');
            });
        }

        // =====================================================================
        // v71 SQL syntax highlighting (overlay pattern).
        //
        // Maya asked that Beautify's output be visually cleaner - "blue
        // keywords and any other format that can make it clearer to Vertica
        // and SQL novice users" - pointing at the "Reading the edge labels"
        // rich-color style as the reference. textarea elements cannot render
        // HTML, so we use the standard overlay trick: an invisible (transparent-
        // text) textarea sits on top of a <pre> that renders the colored
        // version. Caret remains visible via caret-color. Geometry, padding,
        // font, line-height, tab-size and wrap mode MUST match exactly
        // between the two or glyphs drift.
        //
        // Tokenizer mirrors the server-side beautify tokenizer (same keyword
        // set, same comment/string/identifier handling) so colors are
        // consistent with beautification output. Keyword set is a superset
        // chosen for visual density on a typical Vertica query: major
        // clauses, conjunctions, data-shape verbs, type names, window
        // functions, DDL verbs. Extend freely.
        // =====================================================================
        const SQL_KEYWORDS = new Set([
            'SELECT','FROM','WHERE','GROUP','BY','HAVING','ORDER','INNER','LEFT',
            'RIGHT','FULL','CROSS','OUTER','JOIN','NATURAL','LATERAL','UNION',
            'INTERSECT','EXCEPT','ALL','WITH','RECURSIVE','AS','ON','USING',
            'UPDATE','DELETE','INSERT','INTO','VALUES','SET','LIMIT','OFFSET',
            'FETCH','FIRST','NEXT','ROW','ROWS','ONLY','TIES',
            'AND','OR','NOT','DISTINCT','CASE','WHEN','THEN','ELSE','END',
            'IN','IS','NULL','LIKE','ILIKE','BETWEEN','EXISTS','SOME','ANY',
            'CAST','EXTRACT','INTERVAL','AT','TIME','ZONE',
            'PROFILE','EXPLAIN','LOCAL','VERBOSE',
            'PARTITION','OVER','WINDOW','PRECEDING','FOLLOWING','UNBOUNDED','CURRENT',
            'DESC','ASC','NULLS','LAST',
            'TRUE','FALSE','UNKNOWN',
            'CREATE','TABLE','VIEW','PROJECTION','SCHEMA','DATABASE','FUNCTION',
            'IF','REPLACE',
            'PRIMARY','FOREIGN','KEY','REFERENCES','UNIQUE','CONSTRAINT',
            'SEGMENTED','UNSEGMENTED','HASH','NODE',
            'ANALYZE_STATISTICS','ANALYZE_HISTOGRAM'
        ]);

        function highlightSQL(text) {
            const n = text.length;
            let out = '';
            let i = 0;
            const escHtml = (s) => s
                .replace(/&/g, '&amp;').replace(/</g, '&lt;')
                .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
            while (i < n) {
                const ch = text[i];
                const nx = (i + 1 < n) ? text[i + 1] : '';
                // Line comment: -- ... EOL
                if (ch === '-' && nx === '-') {
                    let j = i + 2;
                    while (j < n && text[j] !== '\n' && text[j] !== '\r') j++;
                    out += '<span class="sql-com">' + escHtml(text.slice(i, j)) + '</span>';
                    i = j; continue;
                }
                // Block comment: /* ... */
                if (ch === '/' && nx === '*') {
                    let j = i + 2;
                    while (j < n - 1 && !(text[j] === '*' && text[j + 1] === '/')) j++;
                    j = Math.min(j + 2, n);
                    out += '<span class="sql-com">' + escHtml(text.slice(i, j)) + '</span>';
                    i = j; continue;
                }
                // Single-quoted string (with '' escape)
                if (ch === "'") {
                    let j = i + 1;
                    while (j < n) {
                        if (text[j] === "'") {
                            if (j + 1 < n && text[j + 1] === "'") { j += 2; continue; }
                            j++; break;
                        }
                        j++;
                    }
                    out += '<span class="sql-str">' + escHtml(text.slice(i, j)) + '</span>';
                    i = j; continue;
                }
                // Double-quoted identifier (with "" escape)
                if (ch === '"') {
                    let j = i + 1;
                    while (j < n) {
                        if (text[j] === '"') {
                            if (j + 1 < n && text[j + 1] === '"') { j += 2; continue; }
                            j++; break;
                        }
                        j++;
                    }
                    out += '<span class="sql-id">' + escHtml(text.slice(i, j)) + '</span>';
                    i = j; continue;
                }
                // Number (integer or decimal; no scientific for now)
                if (ch >= '0' && ch <= '9') {
                    let j = i + 1;
                    while (j < n) {
                        const c = text[j];
                        if ((c >= '0' && c <= '9') || c === '.') j++;
                        else break;
                    }
                    out += '<span class="sql-num">' + escHtml(text.slice(i, j)) + '</span>';
                    i = j; continue;
                }
                // Word: letters/underscore/digits/dollar. Could be keyword,
                // function name (if followed by '('), or plain identifier.
                if ((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') ||
                    ch === '_' || ch === '$') {
                    let j = i + 1;
                    while (j < n) {
                        const c = text[j];
                        if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
                            (c >= '0' && c <= '9') || c === '_' || c === '$') j++;
                        else break;
                    }
                    const word = text.slice(i, j);
                    const upper = word.toUpperCase();
                    // Skip inline whitespace to see if the next non-space is '('
                    let k = j;
                    while (k < n && (text[k] === ' ' || text[k] === '\t')) k++;
                    const nextIsParen = text[k] === '(';
                    if (SQL_KEYWORDS.has(upper)) {
                        out += '<span class="sql-kw">' + escHtml(upper) + '</span>';
                    } else if (nextIsParen) {
                        out += '<span class="sql-fn">' + escHtml(word) + '</span>';
                    } else {
                        out += escHtml(word);
                    }
                    i = j; continue;
                }
                // Multi-char operators
                if ('<>=!|:'.indexOf(ch) >= 0) {
                    const pair = ch + nx;
                    let j = i + 1;
                    if (pair === '<=' || pair === '>=' || pair === '<>' ||
                        pair === '!=' || pair === '||' || pair === '::' ||
                        pair === '==') j = i + 2;
                    out += '<span class="sql-op">' + escHtml(text.slice(i, j)) + '</span>';
                    i = j; continue;
                }
                // Single-char operators + punctuation
                if ('+-*/%=.,;(){}[]'.indexOf(ch) >= 0) {
                    // Don't wrap parens/commas/semicolons in op spans so they
                    // stay visually quiet - makes colored keywords pop.
                    if ('+-*/%='.indexOf(ch) >= 0) {
                        out += '<span class="sql-op">' + escHtml(ch) + '</span>';
                    } else {
                        out += escHtml(ch);
                    }
                    i++; continue;
                }
                // Whitespace + anything else: passthrough escaped
                out += escHtml(ch);
                i++;
            }
            return out;
        }

        function syncHighlight() {
            const ed = document.getElementById('queryEditor');
            const hl = document.getElementById('queryHighlight');
            if (!ed || !hl) return;
            // Trailing-newline fix: textarea renders a final \n as a blank
            // line, but a <pre> whose string ends in \n trims that line
            // visually. Append a space so both surfaces are the same height.
            let text = ed.value;
            if (text.endsWith('\n')) text += ' ';
            hl.innerHTML = highlightSQL(text);
            hl.scrollTop = ed.scrollTop;
            hl.scrollLeft = ed.scrollLeft;
        }

        // Wire syncHighlight to editor lifecycle events once the DOM exists.
        // Input fires on every keystroke (typing, paste, cut); scroll fires
        // when the user scrolls the textarea and we must re-pin the overlay.
        document.addEventListener('DOMContentLoaded', function() {
            const ed = document.getElementById('queryEditor');
            if (!ed) return;
            ed.addEventListener('input', syncHighlight);
            ed.addEventListener('scroll', function() {
                const hl = document.getElementById('queryHighlight');
                if (hl) {
                    hl.scrollTop  = ed.scrollTop;
                    hl.scrollLeft = ed.scrollLeft;
                }
            });
            // Initial paint for placeholder-or-preset content.
            syncHighlight();
        });

        async function profileQuery() {
            if (executingQueries) return;
            const { queryText, hasSelection } = getQueryTextToExecute();
            if (!queryText) {
                alert(hasSelection ? 'Please select exactly one query to profile' : 'Please enter exactly one query to profile');
                return;
            }
            const tabId = createTab('Profile', '<div class="loading-indicator"></div>');
            try {
                const response = await fetch('/api/profile_query', {
                    method: 'POST',
                    headers: {'Content-Type': 'application/json'},
                    body: JSON.stringify({ query: queryText })
                });
                if (response.status === 401) {
                    window.location.href = '/';
                    return;
                }
                // v79 (Maya general feedback): 403 w/ error=
                // 'insufficient_privileges' -> show the dedicated
                // privilege-remedy modal and close the Profile tab.
                if (await handlePrivilege403(response)) {
                    closeTab(tabId);
                    return;
                }
                const payloadText = await response.text();
                if (!response.ok) throw new Error(payloadText);
                const result = JSON.parse(payloadText);
                const summary = result.summary_text ? `<div class="execution-info">${escapeHtml(result.summary_text)}</div>` : '';
                // v76: small inline SVG "graph" icon used as a visual cue on
                // both link rows. currentColor so it inherits the anchor's
                // default blue - matches the existing link style without
                // introducing new CSS. aria-hidden because the link text
                // conveys the meaning on its own. role="button" on the span
                // wrapper is deliberately NOT used: the icon is inside the
                // anchor, so the whole thing already acts as one link.
                const GRAPH_ICON_SVG =
                    `<svg aria-hidden="true" width="14" height="14" viewBox="0 0 16 16" `+
                    `style="vertical-align:-2px;margin-right:6px;" fill="none" `+
                    `stroke="currentColor" stroke-width="1.6" stroke-linecap="round" `+
                    `stroke-linejoin="round">`+
                        `<path d="M2 14 L2 2"/>`+
                        `<path d="M2 14 L14 14"/>`+
                        `<path d="M4 11 L7 7 L10 9 L14 4"/>`+
                        `<circle cx="7"  cy="7" r="1" fill="currentColor" stroke="none"/>`+
                        `<circle cx="10" cy="9" r="1" fill="currentColor" stroke="none"/>`+
                        `<circle cx="14" cy="4" r="1" fill="currentColor" stroke="none"/>`+
                    `</svg>`;
                const graphLink = `<div style="margin-bottom:10px;"><a href="/profile/${encodeURIComponent(result.profile_id)}" target="_blank" rel="noopener">${GRAPH_ICON_SVG}Open Graphical Profile</a></div>`;
                // v76 (updated per Maya's follow-up): the skew link is ALWAYS
                // shown, directly below "Open Graphical Profile". A short
                // sentence on the RIGHT of the link states whether the
                // server found meaningful cross-node skew for this query
                // (MEANINGFUL_SKEW_MS_FLOOR + MEANINGFUL_SKEW_FRACTION
                // thresholds; evaluated once on the server, not re-run).
                // This way the user always sees the link exists and learns
                // whether it's worth clicking at a glance. Same anchor
                // style, same font, same background as the link above -
                // only the destination and the trailing status text differ.
                const skewStatusText = result.skew_meaningful
                    ? ' - Meaningful skew found'
                    : ' - No meaningful skew found';
                const skewStatusStyle = result.skew_meaningful
                    ? 'color:#b04a00;font-weight:600;'   // subtle orange tint
                    : 'color:#637389;font-weight:500;';  // muted gray (same as .execution-info)
                const skewLink =
                    `<div style="margin-bottom:10px;">`+
                        `<a href="/skew/${encodeURIComponent(result.profile_id)}" target="_blank" rel="noopener">${GRAPH_ICON_SVG}Open Skew Between Nodes</a>`+
                        `<span style="${skewStatusStyle}font-size:12px;margin-left:6px;">${escapeHtml(skewStatusText)}</span>`+
                    `</div>`;
                // v82 item 5 (Maya request): third link directly below the
                // Skew link. Opens a full ScoreCard page (Roambi-style
                // dashboard) that runs ~30 diagnostic checks against the
                // Vertica system tables for this transaction/statement and
                // grades each HIGH/MEDIUM/LOW/OK/INFO with a remediation
                // hint on the HIGH rows. Unlike the Skew link, the status
                // blurb here is static ("Click to run diagnostics") because
                // the scorecard has not been executed yet when the Profile
                // tab is built - it runs on-demand when the user opens the
                // scorecard page, to avoid adding another Vertica round-trip
                // to every profile response.
                const scorecardLink =
                    `<div style="margin-bottom:10px;">`+
                        `<a href="/scorecard/${encodeURIComponent(result.profile_id)}" target="_blank" rel="noopener">${GRAPH_ICON_SVG}Open ScoreCard</a>`+
                        `<span style="color:#637389;font-weight:500;font-size:12px;margin-left:6px;">${escapeHtml(' - Click to run diagnostic checks')}</span>`+
                    `</div>`;
                const rich = renderProfileText(result.profile_text || '', result.findings || []);
                const content = `${summary}${graphLink}${skewLink}${scorecardLink}${rich}`;
                const tabContent = document.getElementById(tabId);
                if (tabContent) {
                    tabContent.innerHTML = content;
                    activateTab(tabId);
                }
            } catch (error) {
                const tabContent = document.getElementById(tabId);
                if (tabContent) {
                    tabContent.innerHTML = `<div class="execution-info">Profile error:</div><pre style="white-space: pre-wrap; word-break: break-word; color: #dc3545; background: #fff5f5; border: 1px solid #dc3545; border-radius: 6px; padding: 12px; margin: 0; font-family: system-ui, -apple-system, sans-serif; font-size: 13px; line-height: 1.5; max-width: 900px;">${escapeHtml(error.message)}</pre>`;
                    activateTab(tabId);
                }
            }
        }

        function getQueryTextToExecute() {
            const editor = document.getElementById('queryEditor');
            const fullText = editor.value;
            const selectionStart = editor.selectionStart;
            const selectionEnd = editor.selectionEnd;
            const hasSelection = selectionStart !== selectionEnd;
            if (hasSelection) {
                const selectedText = fullText.slice(selectionStart, selectionEnd);
                return { queryText: selectedText.trim(), hasSelection: true };
            }
            return { queryText: fullText.trim(), hasSelection: false };
        }

        async function executeQueries() {
            if (executingQueries) return;
            const { queryText, hasSelection } = getQueryTextToExecute();
            if (!queryText) {
                alert(hasSelection ? 'Please select at least one query to run' : 'Please enter at least one query');
                return;
            }
            const queries = parseQueries(queryText);
            executingQueries = true;
            for (let i = 0; i < queries.length; i++) {
                const query = queries[i];
                const startTime = performance.now();
                const tabLabel = `Query ${i + 1}`;
                const tabId = createTab(tabLabel, '<div class="loading-indicator"></div>');
                try {
                    const response = await fetch('/api/execute_query', {
                        method: 'POST',
                        headers: {'Content-Type': 'application/json'},
                        body: JSON.stringify({ query })
                    });
                    if (response.status === 401) {
                        window.location.href = '/';
                        return;
                    }
                    // v79 (Maya general feedback): 403 privilege popup.
                    if (await handlePrivilege403(response)) {
                        closeTab(tabId);
                        return;
                    }
                    const payloadText = await response.text();
                    if (!response.ok) throw new Error(payloadText);
                    const result = JSON.parse(payloadText);
                    const executionTime = ((performance.now() - startTime) / 1000).toFixed(2);
                    const content = `
                        <div class="execution-info">Execution time: ${executionTime}s</div>
                        <table class="results-table">
                            <thead><tr>${result.columns.map(col => `<th>${escapeHtml(col)}</th>`).join('')}</tr></thead>
                            <tbody>${result.rows.map(row => `<tr>${row.map(cell => `<td>${escapeHtml(cell)}</td>`).join('')}</tr>`).join('')}</tbody>
                        </table>`;
                    const tabContent = document.getElementById(tabId);
                    if (tabContent) {
                        tabContent.innerHTML = content;
                        activateTab(tabId);
                    }
                } catch (error) {
                    console.error('Query execution error:', error);
                    const errorContent = `<div class="execution-info">Error in query:</div><pre style="white-space: pre-wrap; word-break: break-word; color: #dc3545; background: #fff5f5; border: 1px solid #dc3545; border-radius: 6px; padding: 12px; margin: 0; font-family: system-ui, -apple-system, sans-serif; font-size: 13px; line-height: 1.5; max-width: 900px;">${escapeHtml(error.message)}</pre>`;
                    const tabContent = document.getElementById(tabId);
                    if (tabContent) {
                        tabContent.innerHTML = errorContent;
                        activateTab(tabId);
                    }
                }
            }
            executingQueries = false;
        }

        document.addEventListener('click', (e) => {
            const node = e.target.closest('.tree-node');
            if (node && !e.target.classList.contains('checkbox')) node.classList.toggle('expanded');
        });

        const resizer = document.getElementById('dragMe');
        const treeWrapper = document.querySelector('.tree-wrapper');
        const treePanel = document.getElementById('treePanel');
        let isResizing = false;

        resizer.addEventListener('mousedown', () => {
            isResizing = true;
            document.body.classList.add('user-select-none');
            resizer.classList.add('dragging');
        });
        document.addEventListener('mousemove', (e) => {
            if (!isResizing) return;
            const newWidth = e.clientX;
            if (newWidth >= 220 && newWidth <= 800) {
                treePanel.style.width = `${newWidth}px`;
                treeWrapper.style.width = `${newWidth + 5}px`;
            }
        });
        document.addEventListener('mouseup', () => {
            if (isResizing) {
                isResizing = false;
                document.body.classList.remove('user-select-none');
                resizer.classList.remove('dragging');
            }
        });

        const verticalResizer = document.getElementById('verticalDragMe');
        const querySection = document.querySelector('.query-section');
        const resultsSection = document.querySelector('.results-section');
        let isVerticalResizing = false;
        verticalResizer.addEventListener('mousedown', () => {
            isVerticalResizing = true;
            document.body.classList.add('user-select-none');
            verticalResizer.classList.add('dragging');
        });
        document.addEventListener('mousemove', (e) => {
            if (!isVerticalResizing) return;
            const containerRect = document.querySelector('.content-wrapper').getBoundingClientRect();
            const containerHeight = containerRect.height;
            const mouseY = e.clientY - containerRect.top;
            const queryPercentage = (mouseY / containerHeight) * 100;
            const resultsPercentage = 100 - queryPercentage;
            if (queryPercentage >= 20 && queryPercentage <= 80) {
                querySection.style.height = `${queryPercentage}%`;
                resultsSection.style.height = `${resultsPercentage}%`;
            }
        });
        document.addEventListener('mouseup', () => {
            if (isVerticalResizing) {
                isVerticalResizing = false;
                document.body.classList.remove('user-select-none');
                verticalResizer.classList.remove('dragging');
            }
        });

        document.addEventListener('DOMContentLoaded', async () => {
            await loadSessionInfo();
            await loadTree();
            const editor = document.getElementById('queryEditor');
            editor.addEventListener('contextmenu', (e) => e.stopPropagation());
        });

        // v79 (Maya general feedback): privilege-error popup.
        //
        // handlePrivilege403(response) - called from every API fetch
        // that talks to Vertica. Returns true if the 403 was a
        // privilege error (modal already shown) so the caller can
        // short-circuit its own error path. Returns false otherwise,
        // letting the caller handle 403 normally (e.g. CSRF).
        async function handlePrivilege403(response) {
            if (response.status !== 403) return false;
            let data = null;
            try {
                const txt = await response.clone().text();
                data = txt ? JSON.parse(txt) : null;
            } catch (e) { data = null; }
            if (!data || data.error !== 'insufficient_privileges') return false;
            showPrivilegeModal(data);
            return true;
        }

        // Very small SQL syntax highlighter for the grant example.
        // Scoped to this function so it doesn't fight any other
        // highlighter elsewhere in APP_HTML. Keyword list is deliberate
        // - only the ones the grant/role snippet uses.
        function _privHighlightSQL(sql) {
            const esc = (s) => String(s == null ? '' : s)
                .replace(/&/g,'&amp;').replace(/</g,'&lt;')
                .replace(/>/g,'&gt;').replace(/"/g,'&quot;');
            let out = esc(sql);
            // Comments: "-- ... EOL"
            out = out.replace(/(--[^\n]*)/g, '<span class="sql-comment">$1</span>');
            // Keywords
            const kw = /\b(GRANT|TO|SET|ROLE|FROM|AS|WITH|ADMIN|OPTION|DBADMIN|PSEUDOSUPERUSER|DBDUSER)\b/g;
            out = out.replace(kw, '<span class="sql-kw">$1</span>');
            return out;
        }

        function showPrivilegeModal(payload) {
            const body = document.getElementById('privilegeBody');
            const overlay = document.getElementById('privilegeOverlay');
            if (!body || !overlay) return;
            const user    = payload.current_user || '(unknown user)';
            const state   = payload.sqlstate ? (' \u00b7 SQLSTATE ' + escapeHtml(payload.sqlstate)) : '';
            const detail  = payload.detail || 'Permission denied while reading Vertica system tables.';
            const remedy  = payload.remedy || {};
            const summary = remedy.summary ||
                'This request reads Vertica system tables that require elevated privileges. Your account does not have them.';
            const options = Array.isArray(remedy.options) ? remedy.options : [];

            let optionsHtml = '';
            options.forEach((opt, idx) => {
                let block = '<div class="priv-option">' +
                    '<div class="opt-title">' + (idx + 1) + '. ' + escapeHtml(opt.title || 'Option') + '</div>' +
                    '<div class="opt-body">' + escapeHtml(opt.body || '') + '</div>';
                if (opt.code) {
                    block += '<pre>' + _privHighlightSQL(opt.code) + '</pre>';
                }
                if (opt.note) {
                    block += '<div class="opt-note">' + escapeHtml(opt.note) + '</div>';
                }
                block += '</div>';
                optionsHtml += block;
            });

            body.innerHTML =
                '<div class="priv-meta-row">' +
                    '<div>Current user: <b>' + escapeHtml(user) + '</b>' + state + '</div>' +
                '</div>' +
                '<h4>What happened</h4>' +
                '<p>' + escapeHtml(summary) + '</p>' +
                '<span class="priv-detail">' + escapeHtml(detail) + '</span>' +
                '<h4>How to fix it</h4>' +
                optionsHtml;

            overlay.classList.add('show');
            overlay.setAttribute('aria-hidden', 'false');
        }

        function closePrivilegeModal() {
            const overlay = document.getElementById('privilegeOverlay');
            if (!overlay) return;
            overlay.classList.remove('show');
            overlay.setAttribute('aria-hidden', 'true');
        }

        // Wire close interactions (button, backdrop click, Escape).
        (function wirePrivilegeModalClose(){
            const closeBtn = document.getElementById('privilegeClose');
            const overlay  = document.getElementById('privilegeOverlay');
            if (closeBtn) closeBtn.addEventListener('click', closePrivilegeModal);
            if (overlay) overlay.addEventListener('click', (ev) => {
                if (ev.target === overlay) closePrivilegeModal();
            });
            document.addEventListener('keydown', (ev) => {
                if (ev.key === 'Escape') closePrivilegeModal();
            });
        })();
    </script>
</body>
</html>
'''


# v59 (F-STATUS-BAR-01): inject the activity status bar into every template.
# Done once at module load so the runtime cost is zero. Each template gets:
#   - _STATUS_BAR_CSS inserted right before </style>
#   - _STATUS_BAR_HTML inserted right before </body>
#   - _STATUS_BAR_JS inserted right after the first <script> tag so that
#     window.fetch is wrapped before the template's own code can fetch.
# All three templates follow the same structure and contain these anchors
# exactly once, so count=1 replacements are safe.
SCORECARD_HTML = r'''
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>Query ScoreCard</title>
    <style>
        :root {
            --bg-1: #0a1428;
            --bg-2: #0c1730;
            --bg-3: #101d3d;
            --line: rgba(124, 167, 255, 0.16);
            --hairline: rgba(124, 167, 255, 0.12);
            --ink-1: #eef4ff;
            --ink-2: #bcd1f4;
            --ink-3: #8fa4cd;
            --accent: #4aa3ff;
            --accent-soft: rgba(74, 163, 255, 0.18);
            --sev-high:   #ef4444;
            --sev-medium: #f59e0b;
            --sev-low:    #fbbf24;
            --sev-ok:     #22c55e;
            --sev-info:   #3b82f6;
            --shadow: 0 22px 60px rgba(0,0,0,.45);
        }
        * { box-sizing: border-box; }
        html, body { height: 100%; }
        body {
            margin: 0;
            font-family: Inter, system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif;
            color: var(--ink-1);
            background: linear-gradient(180deg, var(--bg-1) 0%, var(--bg-2) 40%, var(--bg-3) 100%);
            -webkit-font-smoothing: antialiased;
            -moz-osx-font-smoothing: grayscale;
        }
        .page {
            max-width: 1600px;
            margin: 0 auto;
            padding: 22px 28px 42px;
        }
        /* ===================== Top bar ===================== */
        .topbar {
            display: grid;
            grid-template-columns: auto 1fr;
            gap: 28px;
            align-items: center;
            margin-bottom: 18px;
        }
        .topbar .left h1 {
            margin: 0;
            font-size: 30px; font-weight: 800; letter-spacing: .005em;
            color: var(--ink-1);
            display: inline-flex; align-items: center; gap: 12px;
        }
        .topbar .left h1 .sc-chip {
            font-size: 12px; font-weight: 700;
            background: rgba(83,163,255,.14); color: #cfe4ff;
            border: 1px solid rgba(124,167,255,.22);
            border-radius: 999px; padding: 3px 9px;
            cursor: pointer; user-select: none;
        }
        .topbar .left h1 .sc-chip:hover { background: rgba(83,163,255,.26); color: #fff; }
        .meta-row {
            display: flex; flex-wrap: wrap; gap: 10px 22px; align-items: center;
            margin-top: 10px;
        }
        .meta-label {
            color: var(--ink-3); font-size: 12.5px; font-weight: 500;
            letter-spacing: .01em;
        }
        .meta-pill {
            font-size: 13px; color: var(--ink-1);
            background: rgba(9,18,40,.85); border: 1px solid var(--hairline);
            border-radius: 8px; padding: 4px 14px;
            font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
            font-weight: 500;
        }
        /* ===================== Filter pills (top-right) ===================== */
        .filter-panel {
            justify-self: end;
            display: inline-flex; align-items: center;
            gap: 10px;
            padding: 8px 14px;
            background: linear-gradient(180deg, rgba(14,26,52,.9), rgba(10,18,40,.9));
            border: 1px solid var(--hairline);
            border-radius: 999px;
        }
        .filter-panel .flabel {
            font-size: 11.5px; color: var(--ink-3); font-weight: 700;
            letter-spacing: .18em; text-transform: uppercase;
            margin-right: 4px;
        }
        .pill {
            cursor: pointer; user-select: none;
            background: transparent;
            border: 1px solid transparent;
            color: var(--ink-2);
            font-size: 13px; font-weight: 600;
            padding: 6px 14px;
            border-radius: 999px;
            transition: all .12s ease;
            display: inline-flex; align-items: center; gap: 8px;
            white-space: nowrap;
        }
        .pill:hover { color: #fff; }
        .pill .count {
            display: inline-flex; align-items: center; justify-content: center;
            min-width: 24px; height: 22px; padding: 0 8px;
            background: rgba(9,18,40,.85);
            border: 1px solid var(--hairline);
            border-radius: 999px;
            font-size: 12px; font-weight: 700;
            color: var(--ink-1);
        }
        .pill.active {
            background: rgba(74,163,255,.1);
            border-color: rgba(74,163,255,.55);
            color: #fff;
        }
        .pill .dot {
            width: 10px; height: 10px; border-radius: 999px;
            display: inline-block;
        }
        .pill[data-sev="HIGH"]   .dot { background: var(--sev-high); }
        .pill[data-sev="MEDIUM"] .dot { background: var(--sev-medium); }
        .pill[data-sev="LOW"]    .dot { background: var(--sev-low); }
        .pill[data-sev="OK"]     .dot { background: var(--sev-ok); }
        .pill[data-sev="INFO"]   .dot { background: var(--sev-info); }
        /* ===================== Findings panel ===================== */
        .findings-panel {
            background: linear-gradient(180deg, rgba(14,26,52,.9), rgba(10,18,40,.9));
            border: 1px solid var(--hairline);
            border-radius: 14px;
            padding: 22px 26px 26px;
            box-shadow: var(--shadow);
        }
        .findings-panel h2 {
            margin: 0 0 6px 0;
            font-size: 24px; font-weight: 800; color: var(--ink-1);
        }
        .findings-panel .subtitle {
            color: var(--ink-3); font-size: 13.5px; margin-bottom: 18px;
        }
        .ftable {
            width: 100%; border-collapse: collapse;
            table-layout: fixed;
        }
        .ftable col.c-sev      { width: 130px; }
        .ftable col.c-type     { width: 130px; }
        .ftable col.c-find     { width: auto; }
        .ftable col.c-action   { width: 36%; }
        .ftable col.c-measured { width: 110px; }
        .ftable thead th {
            text-align: left;
            font-size: 11.5px; font-weight: 700;
            letter-spacing: .14em; text-transform: uppercase;
            color: var(--ink-3);
            padding: 0 14px 14px;
            border-bottom: 1px solid var(--hairline);
        }
        .ftable thead th.col-action   { color: #4ade80; }
        .ftable thead th.col-measured { text-align: right; }
        .ftable tbody td {
            padding: 20px 14px;
            vertical-align: middle;
            border-bottom: 1px solid rgba(124,152,200,.08);
        }
        .ftable tbody tr:last-child td { border-bottom: 0; }

        /* Left accent strip. A continuous vertical colored bar spans a
           severity group. It's drawn on the first cell (sev-cell) of
           every row in the group, rounded only at the top of the first
           row and the bottom of the last row. */
        .ftable td.sev-cell {
            position: relative;
            padding-left: 30px;
        }
        .ftable td.sev-cell::before {
            content: ''; position: absolute;
            left: 10px; top: 0; bottom: 0;
            width: 4px;
            background: transparent;
        }
        .ftable tr.sev-high    td.sev-cell::before { background: var(--sev-high); }
        .ftable tr.sev-medium  td.sev-cell::before { background: var(--sev-medium); }
        .ftable tr.sev-low     td.sev-cell::before { background: var(--sev-low); }
        .ftable tr.sev-ok      td.sev-cell::before { background: var(--sev-ok); }
        .ftable tr.sev-info    td.sev-cell::before { background: var(--sev-info); }
        .ftable tr.group-top    td.sev-cell::before { top: 20px; border-top-left-radius: 4px; border-top-right-radius: 4px; }
        .ftable tr.group-bottom td.sev-cell::before { bottom: 20px; border-bottom-left-radius: 4px; border-bottom-right-radius: 4px; }

        /* Severity badge (only on group-top rows). This is the click target
           that toggles expansion of the whole severity group. */
        .sev-badge {
            display: inline-flex; align-items: center; justify-content: center;
            padding: 8px 18px; border-radius: 10px;
            font-size: 13px; font-weight: 800;
            letter-spacing: .12em;
            color: #fff;
            cursor: pointer;
            user-select: none;
            transition: filter .12s ease, transform .12s ease;
            box-shadow: 0 4px 10px rgba(0,0,0,.28);
            position: relative;  /* anchor for the stack pseudo-elements */
            z-index: 1;
        }
        .sev-badge:hover   { filter: brightness(1.1); transform: translateY(-1px); }
        .sev-badge:active  { transform: translateY(0); }
        .sev-badge.high    { background: var(--sev-high);   }
        .sev-badge.medium  { background: var(--sev-medium); }
        .sev-badge.low     { background: var(--sev-low); color: #3a2a00; }
        .sev-badge.ok      { background: var(--sev-ok);     }
        .sev-badge.info    { background: var(--sev-info);   }

        /* v87: "deck of cards" effect behind the badge. Renders ONLY when
           the badge has the .stacked class (added by the JS only when the
           group is collapsed AND the group has >1 finding). Two copies of
           the badge shape peek out to the lower-right of the front badge,
           each slightly smaller in perceived z-plane via a darker/lighter
           tint. Uses ::before + ::after so the actual badge DOM stays
           simple. When the group is expanded (no .stacked class), the
           badge renders as a plain single button with no deck.

           Coordinates: the two "behind" cards sit offset roughly (4px, 4px)
           and (8px, 8px) to the lower-right. Border-radius matches the
           front badge so the stack looks coherent. */
        .sev-badge.stacked::before,
        .sev-badge.stacked::after {
            content: '';
            position: absolute;
            left: 0; right: 0; top: 0; bottom: 0;
            border-radius: inherit;
            pointer-events: none;
        }
        .sev-badge.stacked::before {
            transform: translate(4px, 4px);
            background: inherit;
            filter: brightness(.82);
            z-index: -1;
            box-shadow: 0 4px 10px rgba(0,0,0,.28);
        }
        .sev-badge.stacked::after {
            transform: translate(8px, 8px);
            background: inherit;
            filter: brightness(.65);
            z-index: -2;
            box-shadow: 0 4px 10px rgba(0,0,0,.28);
        }
        /* The finger indicator is rendered as a separate span next to the
           badge, only on collapsed multi-finding groups. It is NOT a
           click target itself - clicks go through to the containing row.
           The emoji is position-shifted slightly down and to the right so
           it visually "points at" the stacked badge. */
        .sev-finger {
            display: inline-flex; align-items: center; justify-content: center;
            margin-left: 18px;  /* clears the stack offset (8px) + gap */
            font-size: 26px;
            line-height: 1;
            filter: drop-shadow(0 2px 3px rgba(0,0,0,.5));
            pointer-events: none;
            user-select: none;
            transform: translateY(4px);
            animation: finger-nudge 1.8s ease-in-out infinite;
        }
        @keyframes finger-nudge {
            0%, 100% { transform: translate(0, 4px); }
            50%      { transform: translate(-4px, 4px); }
        }
        /* Wrapper that keeps the stacked badge and the finger on one line
           and vertically centered. Needed because .sev-cell has
           padding-left to clear the accent stripe. */
        .sev-badge-wrap {
            display: inline-flex;
            align-items: center;
        }

        /* TYPE pill */
        .type-pill {
            display: inline-flex; align-items: center; justify-content: center;
            padding: 6px 16px; border-radius: 8px;
            background: rgba(12,35,80,.95);
            border: 1px solid rgba(59,130,246,.38);
            color: #dbe8ff;
            font-size: 11.5px; font-weight: 800;
            letter-spacing: .1em; text-transform: uppercase;
        }
        .find-name {
            font-size: 15px; font-weight: 700;
            color: var(--ink-1);
            letter-spacing: .005em;
            line-height: 1.35;
        }
        .ftable tr.sev-high   .find-name { color: #f87171; }
        .ftable tr.sev-medium .find-name { color: #fbbf24; }
        .ftable tr.sev-low    .find-name { color: #fde68a; }
        .ftable tr.sev-ok     .find-name { color: #86efac; }
        .ftable tr.sev-info   .find-name { color: #93c5fd; }
        .find-desc {
            margin-top: 4px;
            font-size: 12.5px; color: var(--ink-2); line-height: 1.5;
        }
        .action-cell {
            font-size: 13px; color: var(--ink-1); line-height: 1.55;
        }
        .measured-cell {
            text-align: right;
            font-size: 24px; font-weight: 800;
            color: #ffffff;   /* v86 item 4: white for all severities */
            font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
        }
        /* v86 item 3: the collapsed group-top row is clickable anywhere on
           it (not just the colored badge), so we show a pointer cursor and
           a subtle hover tint across the entire row. When the group is
           already expanded, the extra click-anywhere behavior is disabled
           so expanded rows don't look "clickable" - the badge alone
           collapses the group. */
        .ftable tr.clickable-row { cursor: pointer; }
        .ftable tr.clickable-row:hover td { background: rgba(74,163,255,.06); }

        /* Empty / loading / error states */
        .loading, .error, .empty {
            padding: 32px; text-align: center; color: var(--ink-2); font-size: 14px;
        }
        .error { color: #ffc7cc; background: rgba(239,68,68,.08); border: 1px solid rgba(239,68,68,.4); border-radius: 10px; }
        .empty { color: var(--ink-3); }
        /* Modal */
        .sc-overlay {
            position: fixed; inset: 0; background: rgba(3,8,22,.68);
            display: none; align-items: center; justify-content: center;
            z-index: 100;
        }
        .sc-overlay.open { display: flex; }
        .sc-modal {
            background: linear-gradient(180deg, rgba(16,28,56,.98), rgba(10,18,40,.98));
            border: 1px solid rgba(125,196,255,.32);
            border-radius: 14px;
            max-width: 720px; width: calc(100vw - 48px);
            max-height: calc(100vh - 80px); overflow: auto;
            color: var(--ink-1);
            padding: 24px 28px;
            box-shadow: 0 30px 80px rgba(0,0,0,.55);
        }
        .sc-modal h2 { margin: 0 0 12px 0; font-size: 20px; font-weight: 800; color: #eaf4ff; }
        .sc-modal p { font-size: 13.5px; line-height: 1.6; color: var(--ink-2); margin: 8px 0; }
        .sc-modal .close {
            float: right; background: transparent; border: 0; color: var(--ink-3);
            font-size: 22px; cursor: pointer; line-height: 1;
        }
        .sc-modal pre {
            background: rgba(4,10,26,.82); border: 1px solid var(--hairline);
            border-radius: 8px; padding: 12px 14px;
            color: #cfe4ff; font-size: 11.5px; line-height: 1.5;
            max-height: 380px; overflow: auto;
            white-space: pre; font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
        }
        @media (max-width: 1100px) {
            .topbar { grid-template-columns: 1fr; }
            .filter-panel { justify-self: start; }
        }
        @media (max-width: 780px) {
            .ftable col.c-action { width: 35%; }
            .ftable col.c-type { width: 100px; }
            .ftable thead { display: none; }
            .ftable, .ftable tbody, .ftable tr, .ftable td { display: block; width: 100%; }
            .ftable tr { border-bottom: 1px solid var(--hairline); padding: 10px 0; }
            .ftable tbody td { padding: 6px 0; border-bottom: 0; }
            .ftable td.sev-cell { padding-left: 16px; }
        }
    </style>
</head>
<body>
<div class="page">

    <!-- Top bar: title + meta on the left, filter pills on the right -->
    <div class="topbar">
        <div class="left">
            <h1>Query Scorecard
                <span class="sc-chip" onclick="openHelp()" title="What does this page measure?">?</span>
                <span class="sc-chip" onclick="openInfo()" title="Show the SQL that powers this scorecard">&#9432;</span>
            </h1>
            <div class="meta-row">
                <span class="meta-label">Transaction</span>
                <span id="metaTxn" class="meta-pill">-</span>
                <span class="meta-label">Statement</span>
                <span id="metaStmt" class="meta-pill">-</span>
                <span class="meta-label">Checks</span>
                <span id="metaChecks" class="meta-pill">-</span>
            </div>
        </div>
        <div class="filter-panel">
            <span class="flabel">Filter</span>
            <span class="pill active" data-sev="ALL"    onclick="setFilter('ALL')">All <span class="count" id="cAll">0</span></span>
            <span class="pill" data-sev="HIGH"   onclick="setFilter('HIGH')"><span class="dot"></span>High <span class="count" id="cHigh">0</span></span>
            <span class="pill" data-sev="MEDIUM" onclick="setFilter('MEDIUM')"><span class="dot"></span>Medium <span class="count" id="cMedium">0</span></span>
            <span class="pill" data-sev="LOW"    onclick="setFilter('LOW')"><span class="dot"></span>Low <span class="count" id="cLow">0</span></span>
            <span class="pill" data-sev="OK"     onclick="setFilter('OK')"><span class="dot"></span>OK <span class="count" id="cOk">0</span></span>
            <span class="pill" data-sev="INFO"   onclick="setFilter('INFO')"><span class="dot"></span>Info <span class="count" id="cInfo">0</span></span>
        </div>
    </div>

    <!-- Priority Findings -->
    <div class="findings-panel">
        <h2>Priority Findings</h2>
        <div class="subtitle">Focus on high-impact issues first to improve query performance.</div>
        <table class="ftable" id="ftable">
            <colgroup>
                <col class="c-sev">
                <col class="c-type">
                <col class="c-find">
                <col class="c-action">
                <col class="c-measured">
            </colgroup>
            <thead>
                <tr>
                    <th>SEVERITY</th>
                    <th>TYPE</th>
                    <th>FINDING</th>
                    <th class="col-action">RECOMMENDED ACTION</th>
                    <th class="col-measured">MEASURED</th>
                </tr>
            </thead>
            <tbody id="findingsBody">
                <tr><td colspan="5" class="loading">Loading scorecard...</td></tr>
            </tbody>
        </table>
    </div>
</div>

<!-- Help + SQL modals -->
<div class="sc-overlay" id="helpOverlay" onclick="if(event.target===this) closeOverlays()">
    <div class="sc-modal">
        <button class="close" onclick="closeOverlays()">&times;</button>
        <h2>What is the Query ScoreCard?</h2>
        <p>The scorecard is a battery of ~30 diagnostic checks run against the Vertica system tables for this specific profiled query. Each check inspects one aspect of the query's runtime behavior - hash joins, broadcasts, spills to disk, skew across nodes, missing statistics, queue waits - and grades it as <b>OK</b>, <b>INFO</b>, <b>LOW</b>, <b>MEDIUM</b>, or <b>HIGH</b>.</p>
        <p><b>HIGH</b> severity means the issue is likely to have a significant impact and has a clear remediation. <b>MEDIUM</b> / <b>LOW</b> are worth reviewing. <b>OK</b> means the check passed. <b>INFO</b> is background context (query duration, nodes participating, etc).</p>
        <p>By default each severity group shows only its first finding, with the colored badge acting as an accordion toggle. Click the badge to expand the group; click the chevron at the end of each row to view that specific finding's details and recommended action.</p>
        <p>The underlying SQL runs in session-private LOCAL TEMPORARY tables, so running the scorecard does not interfere with any other query.</p>
    </div>
</div>
<div class="sc-overlay" id="infoOverlay" onclick="if(event.target===this) closeOverlays()">
    <div class="sc-modal">
        <button class="close" onclick="closeOverlays()">&times;</button>
        <h2>Scorecard SQL</h2>
        <p>Full text of <code>vertica_query_scorecard.sql</code> run for this transaction/statement:</p>
        <pre id="sqlDump">(loading)</pre>
    </div>
</div>

<script>
const PROFILE_ID = '__PROFILE_ID__';
let ALL_ROWS = [];
let CURRENT_FILTER = 'ALL';
let SQL_TEXT = '';
const SEV_ORDER = ['HIGH', 'MEDIUM', 'LOW', 'OK', 'INFO'];

// Per-severity expanded flag. When a severity is collapsed, only the first
// finding of that severity is shown (and the badge is the click-to-expand).
const GROUP_EXPANDED = {HIGH:false, MEDIUM:false, LOW:false, OK:false, INFO:false};

function esc(s){
    return String(s==null?'':s)
        .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')
        .replace(/"/g,'&quot;').replace(/'/g,'&#39;');
}

function openHelp(){ document.getElementById('helpOverlay').classList.add('open'); }
function openInfo(){
    document.getElementById('sqlDump').textContent = SQL_TEXT || '(SQL not loaded)';
    document.getElementById('infoOverlay').classList.add('open');
}
function closeOverlays(){
    document.getElementById('helpOverlay').classList.remove('open');
    document.getElementById('infoOverlay').classList.remove('open');
}
document.addEventListener('keydown', (e) => { if (e.key === 'Escape') closeOverlays(); });

function setFilter(sev){
    CURRENT_FILTER = sev;
    document.querySelectorAll('.filter-panel .pill').forEach(el => {
        el.classList.toggle('active', el.dataset.sev === sev);
    });
    // When the user filters down to a single severity, auto-expand that
    // group so they see all its findings immediately. Other groups don't
    // matter because they'll be filtered out. When switching back to 'ALL',
    // collapse everything so the user sees the one-row-per-severity overview.
    if (sev === 'ALL') {
        for (const k of SEV_ORDER) GROUP_EXPANDED[k] = false;
    } else if (GROUP_EXPANDED.hasOwnProperty(sev)) {
        GROUP_EXPANDED[sev] = true;
    }
    renderFindings();
}

function toggleGroup(sev){
    if (!GROUP_EXPANDED.hasOwnProperty(sev)) return;
    GROUP_EXPANDED[sev] = !GROUP_EXPANDED[sev];
    renderFindings();
}

function groupRowsBySeverity(rows){
    // Returns an ordered list of [severity, [rows]] using SEV_ORDER.
    const by = {};
    for (const r of rows) {
        const sev = String(r.severity||'').toUpperCase();
        if (!by[sev]) by[sev] = [];
        by[sev].push(r);
    }
    return SEV_ORDER.filter(s => by[s] && by[s].length > 0).map(s => [s, by[s]]);
}

function renderFindings(){
    const body = document.getElementById('findingsBody');
    // Apply filter first.
    let rowsFiltered;
    if (CURRENT_FILTER === 'ALL') rowsFiltered = ALL_ROWS.slice();
    else rowsFiltered = ALL_ROWS.filter(r => String(r.severity||'').toUpperCase() === CURRENT_FILTER);

    if (rowsFiltered.length === 0) {
        body.innerHTML = `<tr><td colspan="5" class="empty">No findings match this filter.</td></tr>`;
        return;
    }

    const groups = groupRowsBySeverity(rowsFiltered);
    const html = [];

    for (const [sev, rows] of groups) {
        const sevLower = sev.toLowerCase();
        const expanded = GROUP_EXPANDED[sev];
        const visibleRows = expanded ? rows : rows.slice(0, 1);
        const groupTopIdx = 0;
        const groupBottomIdx = visibleRows.length - 1;
        const canExpand = (rows.length > 1);

        for (let i = 0; i < visibleRows.length; i++) {
            const r = visibleRows[i];
            const isTop = (i === groupTopIdx);
            const isBottom = (i === groupBottomIdx);
            const classes = [`sev-${sevLower}`];
            if (isTop) classes.push('group-top');
            if (isBottom) classes.push('group-bottom');
            // When the group is COLLAPSED and has >1 finding, the first
            // (and only) visible row is clickable anywhere on it to expand
            // the group. When already expanded, the top row keeps its
            // badge-as-collapse-toggle but the rest of the row is not
            // itself a click target - otherwise clicks on the text in an
            // expanded row would re-collapse unexpectedly.
            const rowClickable = isTop && canExpand && !expanded;
            if (rowClickable) classes.push('clickable-row');
            // v87: when a group is COLLAPSED and has multiple findings, the
            // first visible row shows only the SEVERITY badge (with a
            // "deck of cards" stack) and the MEASURED value. The middle
            // columns (TYPE / FINDING / RECOMMENDED ACTION) are intentionally
            // empty until the user clicks to expand. This gives the user a
            // clean overview of which severity buckets contain findings
            // without overwhelming them with the first finding's content.
            //
            // When a group is EXPANDED, or when the group has only 1
            // finding total, all columns render normally with real data.
            const isCollapsedMulti = isTop && canExpand && !expanded;
            // SEVERITY cell. Only group-top rows show the badge. When the
            // row is collapsed AND multi-finding, the badge renders with
            // the .stacked class (the deck-of-cards pseudo-elements kick
            // in) and a finger indicator is rendered next to it.
            const badgeTitle = canExpand
                ? `Click to ${expanded ? 'collapse' : 'expand'} the ${sev} group`
                : `${sev} (single finding)`;
            const badgeOnclick = canExpand ? `onclick="event.stopPropagation(); toggleGroup('${sev}')"` : '';
            const badgeClasses = ['sev-badge', sevLower];
            if (isCollapsedMulti) badgeClasses.push('stacked');
            const fingerHtml = isCollapsedMulti
                ? `<span class="sev-finger" aria-hidden="true" title="Click to expand">&#128073;</span>`
                : '';
            const badgeHtml = isTop
                ? `<span class="sev-badge-wrap">`
                    + `<span class="${badgeClasses.join(' ')}" ${badgeOnclick} title="${badgeTitle}">${esc(sev)}</span>`
                    + fingerHtml
                  + `</span>`
                : '';
            // Middle column content - rendered only when the group is
            // EXPANDED or is a single-finding group (isCollapsedMulti=false).
            const typePillHtml = (!isCollapsedMulti && r.category)
                ? `<span class="type-pill">${esc(r.category)}</span>`
                : '';
            const findNameHtml = isCollapsedMulti
                ? ''
                : `<div class="find-name">${esc(r.check_name||'')}</div>`
                  + `<div class="find-desc">${esc(r.details||'')}</div>`;
            // v86 item 1: show the real suggested_action text in the column
            // (only when not a collapsed-multi row - same rule).
            const actionText = (!isCollapsedMulti && r.suggested_action && String(r.suggested_action).trim())
                ? esc(r.suggested_action)
                : '';
            const rowOnclick = rowClickable ? `onclick="toggleGroup('${sev}')"` : '';
            html.push(`
                <tr class="${classes.join(' ')}" ${rowOnclick}>
                    <td class="sev-cell">${badgeHtml}</td>
                    <td>${typePillHtml}</td>
                    <td>${findNameHtml}</td>
                    <td class="action-cell">${actionText}</td>
                    <td class="measured-cell">${esc(r.score||'')}</td>
                </tr>
            `);
        }
    }
    body.innerHTML = html.join('');
}

async function load(){
    try {
        const resp = await fetch('/api/scorecard_run?profile_id=' + encodeURIComponent(PROFILE_ID));
        if (!resp.ok) {
            const txt = await resp.text();
            throw new Error('Scorecard API returned ' + resp.status + ': ' + txt);
        }
        const data = await resp.json();
        ALL_ROWS = data.rows || [];
        SQL_TEXT = data.sql_text || '';
        document.getElementById('metaTxn').textContent    = data.transaction_id || '-';
        document.getElementById('metaStmt').textContent   = data.statement_id   || '-';
        document.getElementById('metaChecks').textContent = String(ALL_ROWS.length);
        const s = data.summary || {counts:{}, score: 0};
        const c = s.counts || {};
        document.getElementById('cAll').textContent    = String(ALL_ROWS.length);
        document.getElementById('cHigh').textContent   = String(c.HIGH   || 0);
        document.getElementById('cMedium').textContent = String(c.MEDIUM || 0);
        document.getElementById('cLow').textContent    = String(c.LOW    || 0);
        document.getElementById('cOk').textContent     = String(c.OK     || 0);
        document.getElementById('cInfo').textContent   = String(c.INFO   || 0);
        renderFindings();
    } catch (e) {
        const body = document.getElementById('findingsBody');
        body.innerHTML = `<tr><td colspan="5" class="error">${esc(e.message || String(e))}</td></tr>`;
    }
}
load();
</script>
</body>
</html>
'''


def _inject_status_bar(html_template: str) -> str:
    if '</style>' in html_template:
        html_template = html_template.replace('</style>', _STATUS_BAR_CSS + '    </style>', 1)
    if '<script>' in html_template:
        html_template = html_template.replace('<script>', '<script>\n' + _STATUS_BAR_JS + '\n', 1)
    if '</body>' in html_template:
        html_template = html_template.replace('</body>', _STATUS_BAR_HTML + '\n</body>', 1)
    return html_template

LOGIN_HTML   = _inject_status_bar(LOGIN_HTML)
PROFILE_HTML = _inject_status_bar(PROFILE_HTML)
SKEW_HTML    = _inject_status_bar(SKEW_HTML)
SCORECARD_HTML = _inject_status_bar(SCORECARD_HTML)
APP_HTML     = _inject_status_bar(APP_HTML)


# -----------------------------------------------------------------------------
# HTTP handler
# -----------------------------------------------------------------------------
class DBTreeHandler(http.server.SimpleHTTPRequestHandler):
    # v57: suppress access-log lines for well-known web-vulnerability-scanner
    # probes. Scanners like Qualys hit every HTTP endpoint they can find with
    # thousands of canned attack paths (/etc/passwd traversal, phpinfo.php,
    # XSS payloads, Jboss JMX, old struts, etc.). Every one of those lands at
    # 401 or 404 against our server - so nothing is vulnerable - but the sheer
    # volume drowns real access entries. These fingerprints never match any
    # of our real routes ('/', '/app', '/api/*', '/profile/<uuid>', '/ASSETS/*')
    # so dropping them from INFO-level access logs is safe. Case-insensitive
    # substring match against self.path (and self.requestline as a fallback
    # for malformed requests where self.path isn't parsed).
    _SCANNER_FINGERPRINTS = (
        '..', '%2e%2e', '%252e%252e',
        '%c0%ae', '%e0%80', '%f0%80', '%f8%80',
        '<script', '<img ', 'javascript:', 'alert(',
        '.php', '.asp', '.aspx', '.cgi', '.pl', '.exe',
        '.jsp', '.action', '.mdb', '.wsgi', '.user.ini',
        'qualys', 'phpinfo', 'formmail',
        'jmx-console', 'web-console', 'jmxinvoker', 'ejbinvoker',
        'mmhttpdb', '/_mm', 'cgiwrap', 'sdbsearch', 'netpad',
        'webnews', 'dnewsweb', 'guestbook', 'cgiforum',
        'splatt_forum', 'ubbthreads', 'wwwthreads',
        'struts/', 'moin.wsgi', 'release-notes',
        'recipe_search', 'recipe_view', 'htsearch',
        'globals.php', 'modules.php',
    )

    def _looks_like_scanner_probe(self) -> bool:
        haystack = ((getattr(self, 'path', '') or '') + ' ' +
                    (getattr(self, 'requestline', '') or '')).lower()
        return any(m in haystack for m in self._SCANNER_FINGERPRINTS)

    def log_message(self, format, *args):
        if not DEBUG_LOGGING:
            return
        if self._looks_like_scanner_probe():
            return
        logger.info(format % args)

    # ---- client-disconnect detection -----------------------------------------
    # If the client closes the connection mid-response the write() on self.wfile
    # raises BrokenPipeError, or - under HTTPS - ssl.SSLError with code
    # "BAD_LENGTH". In either case the socket is dead, so calling send_error()
    # on it just raises a second exception that buries the real error in a
    # traceback. _is_client_disconnect() lets handlers short-circuit cleanly:
    # just log and return, never try to write a 500 on a torn-down socket.
    CLIENT_DISCONNECT_EXCEPTIONS = (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, ssl.SSLError)

    @staticmethod
    def _is_client_disconnect(exc: BaseException) -> bool:
        return isinstance(exc, DBTreeHandler.CLIENT_DISCONNECT_EXCEPTIONS)

    def _safe_send_error(self, status: int, message: str):
        """Send a 500-style error reply, but only if the socket is still alive.
        Any failure here is swallowed - we've already lost the client."""
        try:
            self.send_error(status, message)
        except self.CLIENT_DISCONNECT_EXCEPTIONS:
            # Client went away mid-error-response. Nothing more we can do.
            pass
        except Exception:
            # Any other failure at this point is also hopeless; avoid
            # amplifying it with yet another traceback in the log.
            pass

    def _send_privilege_error(self, exc: BaseException, current_user: str = ''):
        """v79 (Maya general feedback): emit a structured 403 JSON that
        the client recognises and renders as the "how to fix privileges"
        popup. Payload shape is documented below - keep stable so the
        frontend can branch on `error='insufficient_privileges'`
        reliably across future versions."""
        try:
            payload = {
                'error':         'insufficient_privileges',
                'current_user':  current_user or '',
                'sqlstate':      str(getattr(exc, 'sqlstate', '') or ''),
                # Trim the raw message so it fits a modal but keep
                # enough for the user to see which table / column the
                # driver complained about.
                'detail':        (str(exc) or 'Permission denied')[:600],
                # Structured remediation hints the client will render as
                # numbered steps in the popup.
                'remedy': {
                    'summary': (
                        'This query reads Vertica system tables '
                        '(v_monitor / v_internal / v_catalog) that require '
                        'elevated privileges. Your account does not have '
                        'them. There are two common ways to fix this.'
                    ),
                    'options': [
                        {
                            'title': 'Log in as a Vertica superuser',
                            'body': (
                                'Sign out and sign in again as `dbadmin` '
                                '(or any other account that already has '
                                'the DBADMIN / PSEUDOSUPERUSER role). '
                                'This is the quickest path but the superuser '
                                'password is often shared only with DBAs.'
                            ),
                        },
                        {
                            'title': 'Ask the DBA to delegate the role to your account',
                            'body': (
                                'Your DBA can delegate the required roles to '
                                'your user once, then you log in as yourself '
                                'and activate the role when needed. '
                                'Typical grant (from dbadmin):'
                            ),
                            'code': (
                                '-- As dbadmin, one time:\n'
                                'GRANT dbduser, dbadmin, pseudosuperuser TO your_username;\n\n'
                                '-- As your_username, each session that needs elevated reads:\n'
                                'SET ROLE pseudosuperuser;\n'
                                '-- or, for full superuser-equivalent catalog access:\n'
                                'SET ROLE dbadmin;'
                            ),
                            'note': (
                                'After SET ROLE, the current session inherits the role\'s '
                                'privileges. Open the Profile Tab again to re-run the query.'
                            ),
                        },
                    ],
                },
            }
            self.send_response(403)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps(payload, default=str).encode('utf-8'))
        except self.CLIENT_DISCONNECT_EXCEPTIONS:
            pass
        except Exception:
            # Same defensive posture as _safe_send_error.
            pass

    def _read_json_body(self):
        content_length = int(self.headers.get('Content-Length', '0'))
        post_data = self.rfile.read(content_length) if content_length > 0 else b'{}'
        return json.loads(post_data.decode('utf-8'))

    def _send_json(self, payload, status=200, extra_headers=None):
        self.send_response(status)
        self.send_header('Content-Type', 'application/json')
        if extra_headers:
            for key, value in extra_headers.items():
                self.send_header(key, value)
        self.end_headers()
        self.wfile.write(json.dumps(payload, default=str).encode('utf-8'))

    def _send_html(self, html_text, status=200, extra_headers=None):
        self.send_response(status)
        self.send_header('Content-Type', 'text/html; charset=utf-8')
        if extra_headers:
            for key, value in extra_headers.items():
                self.send_header(key, value)
        self.end_headers()
        self.wfile.write(html_text.encode('utf-8'))

    def _get_cookie_value(self, name: str):
        raw = self.headers.get('Cookie')
        if not raw:
            return None
        jar = cookies.SimpleCookie()
        jar.load(raw)
        morsel = jar.get(name)
        return morsel.value if morsel else None

    def _get_session(self):
        return get_session(self._get_cookie_value(SESSION_COOKIE_NAME))

    def _require_session(self):
        session = self._get_session()
        if not session:
            self._send_json({'error': 'Authentication required'}, status=401)
            return None
        return session

    def _session_cookie_header(self, session_id: str):
        parts = [
            f'{SESSION_COOKIE_NAME}={session_id}',
            'Path=/',
            'HttpOnly',
            f'Max-Age={SESSION_MAX_AGE_SECONDS}',
            'SameSite=Lax',
        ]
        if TLS_COOKIE_SECURE:
            parts.append('Secure')
        return '; '.join(parts)

    def _expired_cookie_header(self):
        return f'{SESSION_COOKIE_NAME}=; Path=/; HttpOnly; Max-Age=0; SameSite=Lax'

    def do_GET(self):
        try:
            cleanup_sessions()
            cleanup_profile_runs()
            parsed = urlparse(self.path)
            path = parsed.path

            if path == '/':
                if self._get_session():
                    self.send_response(302)
                    self.send_header('Location', '/app')
                    self.end_headers()
                    return
                self._send_html(LOGIN_HTML)
                return

            if path == '/app':
                if not self._get_session():
                    self.send_response(302)
                    self.send_header('Location', '/')
                    self.end_headers()
                    return
                self._send_html(APP_HTML)
                return

            if path.startswith('/profile/'):
                session = self._require_session()
                if not session:
                    return
                profile_id = path.split('/profile/', 1)[1].strip()
                profile_run = get_profile_run(profile_id)
                if not profile_run or profile_run.get('session_id') != session.get('session_id'):
                    self.send_error(404, 'Profile not found')
                    return
                self._send_html(PROFILE_HTML.replace('__PROFILE_ID__', html.escape(profile_id)))
                return

            # v76: skew-between-nodes page. Same tenant check as /profile/
            # (session owns the profile_id), same template-substitution
            # pattern. The page itself is SKEW_HTML; it pulls its data
            # from /api/skew_run.
            if path.startswith('/skew/'):
                session = self._require_session()
                if not session:
                    return
                profile_id = path.split('/skew/', 1)[1].strip()
                profile_run = get_profile_run(profile_id)
                if not profile_run or profile_run.get('session_id') != session.get('session_id'):
                    self.send_error(404, 'Profile not found')
                    return
                self._send_html(SKEW_HTML.replace('__PROFILE_ID__', html.escape(profile_id)))
                return

            # v82 item 5: ScoreCard page. Same tenant-check pattern as
            # /skew/<id> (session must own the profile_id). The page itself
            # is SCORECARD_HTML; it pulls its data from /api/scorecard_run.
            if path.startswith('/scorecard/'):
                session = self._require_session()
                if not session:
                    return
                profile_id = path.split('/scorecard/', 1)[1].strip()
                profile_run = get_profile_run(profile_id)
                if not profile_run or profile_run.get('session_id') != session.get('session_id'):
                    self.send_error(404, 'Profile not found')
                    return
                self._send_html(SCORECARD_HTML.replace('__PROFILE_ID__', html.escape(profile_id)))
                return

            if path == '/api/profile_run':
                session = self._require_session()
                if not session:
                    return
                profile_id = (parse_qs(parsed.query).get('profile_id') or [''])[0].strip()
                profile_run = get_profile_run(profile_id)
                if not profile_run or profile_run.get('session_id') != session.get('session_id'):
                    self.send_error(404, 'Profile not found')
                    return
                self._send_json(profile_run['graph_data'])
                return

            # v76: skew data endpoint. Returns the subset of graph_data
            # needed by the /skew/<id> page: just the ranked skew_rows
            # plus enough context (query duration, cluster nodes) for
            # the chart to render its tooltip and "out of total" labels
            # without loading the full graph payload.
            if path == '/api/skew_run':
                session = self._require_session()
                if not session:
                    return
                profile_id = (parse_qs(parsed.query).get('profile_id') or [''])[0].strip()
                profile_run = get_profile_run(profile_id)
                if not profile_run or profile_run.get('session_id') != session.get('session_id'):
                    self.send_error(404, 'Profile not found')
                    return
                gd = profile_run.get('graph_data') or {}
                summary = gd.get('summary') or {}
                step_skew = summary.get('step_skew') or {}
                payload = {
                    'transaction_id':    str(summary.get('transaction_id') or ''),
                    'statement_id':      str(summary.get('statement_id') or ''),
                    'query_duration_us': int(summary.get('query_duration_us') or 0),
                    'cluster_node_count': int(((summary.get('coverage') or {}).get('cluster_nodes')) or 0),
                    'skew_meaningful':   _skew_is_meaningful(
                                             step_skew,
                                             int(summary.get('query_duration_us') or 0),
                                         ),
                    'skew_rows':         list(step_skew.get('skew_rows') or []),
                    'top_step':          str(step_skew.get('step') or ''),
                    'top_skew_ms':       int(step_skew.get('skew_ms') or 0),
                    'top_slowest_node':  str(step_skew.get('slowest_node') or ''),
                    'top_fastest_node':  str(step_skew.get('fastest_node') or ''),
                    # v77 (Maya item #9): exact SQL of the skew query,
                    # so the (i) info-chip on the page can show it.
                    'sql_text':          _SKEW_QUERY_SQL,
                    # v78 (Maya item #6): SQL of the DURATION view too,
                    # so the (i) chip can show both toggles' backing
                    # queries side-by-side.
                    'duration_sql_text': _DURATION_QUERY_SQL,
                }
                self._send_json(payload)
                return

            # v82 item 5: ScoreCard data endpoint. Opens a FRESH Vertica
            # connection (not shared with any other request), executes the
            # full vertica_query_scorecard.sql script - LOCAL TEMP tables
            # are session-private so concurrent users run safely - and
            # returns the ranked findings as JSON.
            #
            # Uses the transaction_id / statement_id already stored with
            # this profile_run (captured when the user first profiled the
            # query), so the page never has to re-profile.
            if path == '/api/scorecard_run':
                session = self._require_session()
                if not session:
                    return
                profile_id = (parse_qs(parsed.query).get('profile_id') or [''])[0].strip()
                profile_run = get_profile_run(profile_id)
                if not profile_run or profile_run.get('session_id') != session.get('session_id'):
                    self.send_error(404, 'Profile not found')
                    return
                transaction_id = int(profile_run.get('transaction_id') or 0)
                statement_id   = int(profile_run.get('statement_id')   or 0)
                if not transaction_id or not statement_id:
                    self.send_error(400, 'Profile is missing transaction/statement id')
                    return
                try:
                    # v81 SEC-001: decrypt only at the connection-open moment.
                    _u, _p = decrypt_credentials(session)
                    conn_info = build_connection_info(_u, _p)
                    del _u, _p
                    with vertica_python.connect(**conn_info) as connection:
                        with connection.cursor() as cursor:
                            rows = _run_scorecard(cursor, transaction_id, statement_id)
                            try:
                                connection.commit()
                            except Exception:
                                pass
                    summary = _scorecard_summary(rows)
                    # HIGH count determines the Profile-tab status blurb
                    # (the third link sitting below "Open Skew Between Nodes"
                    # uses this to say "- N HIGH findings" / "- No HIGH findings").
                    high_count = int((summary.get('counts') or {}).get('HIGH') or 0)
                    payload = {
                        'transaction_id': str(transaction_id),
                        'statement_id':   str(statement_id),
                        'rows':           rows,
                        'summary':        summary,
                        'high_count':     high_count,
                        'sql_text':       _SCORECARD_QUERY_SQL,
                    }
                    self._send_json(payload)
                except Exception as e:
                    if self._is_client_disconnect(e):
                        return
                    _uname = session_username(session)
                    if _is_privilege_error(e):
                        logger.info('Privilege error during scorecard for %s: %s', _uname, e)
                        self._send_privilege_error(e, current_user=_uname)
                        return
                    logger.error(f'Scorecard error for {_uname}: {str(e)}')
                    self._safe_send_error(500, html.escape(str(e)))
                return

            # v83 regression fix: v82's str_replace for the /api/scorecard_run
            # endpoint used an `old_str` that started at the preceding route's
            # closing `return` and ended at `if path == '/api/session':`. The
            # scorecard block was inserted in its place, but the replacement
            # dropped the `if path == '/api/session':` line itself. The body
            # of the handler (session check, send_json, return) survived as
            # dead code after the scorecard's `return`, which meant every
            # `/api/session` request fell through to the 404 fallback. Without
            # this route the browser concluded every page load was unauthed,
            # redirected back to `/` -> `/app` -> `/api/session` -> 404 on
            # loop, which is what Maya saw as the endless "Loading DB tree..."
            # / "checking session" cycle. Restoring the route guard reattaches
            # the existing handler body; no other change needed.
            if path == '/api/session':
                session = self._require_session()
                if not session:
                    return
                # v81 SEC-001: username is stored encrypted; decrypt just the
                # username (not the password) for the display endpoint.
                self._send_json({'username': session_username(session)})
                return

            if path == '/api/dbtree':
                session = self._require_session()
                if not session:
                    return
                self.get_tree(session)
                return

            if path.startswith('/ASSETS/'):
                return http.server.SimpleHTTPRequestHandler.do_GET(self)

            self.send_error(404, 'Not found')
        except Exception as e:
            if self._is_client_disconnect(e):
                # Client closed the connection (navigated away / browser
                # timeout). The socket's gone, no point in trying to reply.
                logger.info(f'Client disconnected during GET {self.path!r}: {type(e).__name__}')
                return
            logger.error(f'Error handling GET request: {str(e)}')
            self._safe_send_error(500, str(e))

    def do_POST(self):
        try:
            cleanup_sessions()
            cleanup_profile_runs()
            parsed = urlparse(self.path)
            path = parsed.path

            if path == '/api/login':
                data = self._read_json_body()
                username = (data.get('username') or '').strip()
                password = data.get('password') or ''
                if not username or not password:
                    self._send_json({'error': 'Username and password are required'}, status=400)
                    return
                try:
                    version = test_login(username, password)
                    session_id = create_session(username, password)
                    self._send_json(
                        {'ok': True, 'version': version, 'username': username},
                        status=200,
                        extra_headers={'Set-Cookie': self._session_cookie_header(session_id)}
                    )
                    log_info(f'Login successful for user {username}')
                except Exception as e:
                    logger.warning(f'Login failed for user {username}: {str(e)}')
                    self._send_json({'error': 'Invalid username or password'}, status=401)
                return

            if path == '/api/logout':
                session_id = self._get_cookie_value(SESSION_COOKIE_NAME)
                if session_id:
                    delete_session(session_id)
                self._send_json({'ok': True}, extra_headers={'Set-Cookie': self._expired_cookie_header()})
                return

            if path == '/api/profile_query':
                session = self._require_session()
                if not session:
                    return
                query_data = self._read_json_body()
                try:
                    statement = ensure_single_statement(query_data.get('query', ''))
                    profile_payload = run_profile_query(session, statement)
                    graph_data = profile_payload['graph_data']
                    # v57: cast ids to str at the JSON boundary. Vertica
                    # transaction_id can exceed JS Number.MAX_SAFE_INTEGER
                    # (2^53-1), so sending the raw int causes JSON.parse
                    # rounding on the browser. See the matching comment in
                    # fetch_profile_graph_data's summary dict.
                    self._send_json({
                        'profile_id': profile_payload['profile_id'],
                        'profile_text': profile_payload['profile_text'],
                        'transaction_id': str(profile_payload['transaction_id']),
                        'statement_id': str(profile_payload['statement_id']),
                        'summary_text': format_profile_summary(graph_data['summary']),
                        # v63 item 12: surface the same dynamic findings
                        # list already used by the graph page's "tree-overview"
                        # help, so the Profile Tab can show them at the top.
                        'findings': list(graph_data.get('summary', {}).get('tree_analysis') or []),
                    })
                except ValueError as e:
                    self._safe_send_error(400, html.escape(str(e)))
                except Exception as e:
                    # v81 SEC-001: decrypt username only for the log/error path.
                    _uname_err = session_username(session)
                    if self._is_client_disconnect(e):
                        logger.info(f'Client disconnected during profile for {_uname_err}')
                        return
                    # v79 (Maya general feedback): privilege errors
                    # deserve a dedicated 403 payload the frontend
                    # renders as a "how to get access" popup.
                    if _is_privilege_error(e):
                        logger.info(
                            'Privilege error during profile for %s: %s',
                            _uname_err, e,
                        )
                        self._send_privilege_error(e, current_user=_uname_err)
                        return
                    logger.error(f'Profile error for {_uname_err}: {str(e)}')
                    self._safe_send_error(500, html.escape(str(e)))
                return

            if path == '/api/execute_query':
                session = self._require_session()
                if not session:
                    return
                query_data = self._read_json_body()
                query = query_data.get('query', '')
                # v81 SEC-001: username for logging goes through the decrypt
                # helper; password never touches the log path.
                _uname_log = session_username(session)
                log_info(f"Executing query for user {_uname_log}: {query}")
                try:
                    _u, _p = decrypt_credentials(session)
                    conn_info = build_connection_info(_u, _p)
                    del _u, _p
                    with vertica_python.connect(**conn_info) as connection:
                        with connection.cursor() as cursor:
                            cursor.execute(query)
                            if cursor.description:
                                columns = [desc[0] for desc in cursor.description]
                                rows = cursor.fetchall()
                                row_count = len(rows)
                            else:
                                columns = ['status', 'message', 'rows_affected']
                                affected_rows = cursor.rowcount if cursor.rowcount is not None and cursor.rowcount >= 0 else 0
                                rows = [['success', 'Statement executed successfully.', affected_rows]]
                                row_count = affected_rows
                            connection.commit()
                            self._send_json({
                                'columns': columns,
                                'rows': rows,
                                'rowCount': row_count,
                                'hasResultSet': bool(cursor.description)
                            })
                except Exception as e:
                    if self._is_client_disconnect(e):
                        logger.info(f'Client disconnected during query for {_uname_log}')
                        return
                    # v79 (Maya general feedback): same 403 popup path
                    # when a user runs a raw SQL against system tables
                    # from the Query Tab and hits a privilege wall.
                    if _is_privilege_error(e):
                        logger.info(
                            'Privilege error during query for %s: %s',
                            _uname_log, e,
                        )
                        self._send_privilege_error(e, current_user=_uname_log)
                        return
                    logger.error(f'Query execution error for {_uname_log}: {str(e)}')
                    self._safe_send_error(500, html.escape(str(e)))
                return

            if path == '/api/beautify_sql':
                session = self._require_session()
                if not session:
                    return
                query_data = self._read_json_body()
                sql_text = query_data.get('query', '')
                self._send_json({'query': beautify_sql_text(sql_text)})
                return

            self.send_error(404, 'Not found')
        except Exception as e:
            if self._is_client_disconnect(e):
                logger.info(f'Client disconnected during POST {self.path!r}: {type(e).__name__}')
                return
            logger.error(f'Error handling POST request: {str(e)}')
            self._safe_send_error(500, str(e))

    def get_tree(self, session):
        start_time = time.time()
        try:
            # v81 SEC-001: decrypt credentials for this one connection; clear
            # locals after we hand them to build_connection_info.
            _u, _p = decrypt_credentials(session)
            conn_info = build_connection_info(_u, _p)
            del _u, _p
            with vertica_python.connect(**conn_info) as connection:
                with connection.cursor() as cursor:
                    cursor.execute('SELECT database_name FROM databases')
                    db_name = cursor.fetchone()[0]

                    cursor.execute("""
                        SELECT table_name, remarks
                        FROM all_tables
                        WHERE table_type = 'SYSTEM TABLE'
                        ORDER BY table_name
                    """)
                    system_tables = cursor.fetchall()

                    cursor.execute("""
                        SELECT schema_name
                        FROM schemata
                        ORDER BY schema_name
                    """)
                    schema_rows = cursor.fetchall()

                    cursor.execute("""
                        SELECT table_namespace, table_schema, table_name, column_name, data_type
                        FROM columns
                        ORDER BY 1,2,3,4,ordinal_position
                    """)
                    table_rows = cursor.fetchall()

                    cursor.execute("""
                        SELECT table_id as view_id_join_key,
                               table_namespace as view_table_namespace,
                               table_schema as view_schema,
                               table_name as view_name,
                               view_definition
                        FROM VIEWS
                    """)
                    view_rows = cursor.fetchall()

                    root = {
                        'name': f'Database {db_name}',
                        'type': 'root',
                        'children': [
                            {'name': 'Schemas', 'type': 'category', 'children': []},
                            {'name': 'System Tables', 'type': 'category', 'children': []}
                        ]
                    }

                    system_tables_node = root['children'][1]
                    for table_name, remarks in system_tables:
                        system_table_node = {
                            'name': table_name,
                            'type': 'system_table',
                            'isCheckable': True,
                            'children': []
                        }
                        if remarks:
                            system_table_node['children'].append({
                                'name': f' - {remarks}',
                                'type': 'system_table_remarks',
                                'children': []
                            })
                        system_tables_node['children'].append(system_table_node)

                    schemas_list = root['children'][0]['children']
                    schema_dict = {}
                    excluded_schemas = {
                        'v_catalog', 'v_func', 'v_internal', 'v_internal_tables',
                        'v_monitor', 'v_secret_managers', 'v_txtindex'
                    }

                    for schema_row in schema_rows:
                        schema_name = schema_row[0]
                        if schema_name in excluded_schemas:
                            continue
                        schema_dict[schema_name] = {
                            'name': schema_name,
                            'type': 'schema',
                            'tables': {},
                            'views': {},
                            'children': [
                                {'name': 'Tables', 'type': 'category', 'children': []},
                                {'name': 'Views', 'type': 'category', 'children': []}
                            ]
                        }

                    for row in table_rows:
                        namespace, schema, table, column, data_type = row
                        if schema not in schema_dict:
                            schema_dict[schema] = {
                                'name': schema,
                                'type': 'schema',
                                'tables': {},
                                'views': {},
                                'children': [
                                    {'name': 'Tables', 'type': 'category', 'children': []},
                                    {'name': 'Views', 'type': 'category', 'children': []}
                                ]
                            }
                        tables_dict = schema_dict[schema]['tables']
                        if table not in tables_dict:
                            tables_dict[table] = {
                                'name': table,
                                'type': 'table',
                                'isCheckable': True,
                                'children': [{'name': 'Columns', 'type': 'category', 'children': []}]
                            }
                        tables_dict[table]['children'][0]['children'].append({
                            'name': f'{column} - {data_type}',
                            'type': 'column'
                        })

                    for row in view_rows:
                        _, namespace, schema, view_name, view_def = row
                        if schema not in schema_dict:
                            continue
                        schema_dict[schema]['views'][view_name] = {
                            'name': view_name,
                            'type': 'view',
                            'isCheckable': True,
                            'children': [{'name': view_def, 'type': 'view_definition'}]
                        }

                    for schema_name in sorted(schema_dict.keys()):
                        schema_data = schema_dict[schema_name]
                        schema_node = {
                            'name': schema_name,
                            'type': 'schema',
                            'children': [
                                {'name': 'Tables', 'type': 'category', 'children': []},
                                {'name': 'Views', 'type': 'category', 'children': []}
                            ]
                        }
                        for table_name in sorted(schema_data['tables'].keys()):
                            schema_node['children'][0]['children'].append(schema_data['tables'][table_name])
                        for view_name in sorted(schema_data['views'].keys()):
                            schema_node['children'][1]['children'].append(schema_data['views'][view_name])
                        schemas_list.append(schema_node)

                    self._send_json(root)
                    # v81 SEC-001: decrypt username only for the log line.
                    log_info(f"Tree generation completed for {session_username(session)} in {time.time() - start_time:.2f} seconds")
        except Exception as e:
            if self._is_client_disconnect(e):
                # Common when the user navigates away while dbtree is being
                # built (3-4 seconds on some clusters). Exactly what was in
                # the v52 log: BrokenPipe wrapped by SSLError.
                logger.info(f'Client disconnected during dbtree generation: {type(e).__name__}')
                return
            logger.error(f'Error getting DB structure: {str(e)}')
            self._safe_send_error(500, html.escape(str(e)))


class ThreadingHTTPServer(ThreadingMixIn, socketserver.TCPServer):
    # Thread-per-request server. Session/profile state is protected by locks and
    # profile payloads are deep-copied on store/read so concurrent users do not
    # mutate each other's in-memory data, including graphical profile payloads.
    allow_reuse_address = True
    daemon_threads = True


class RedirectHandler(http.server.BaseHTTPRequestHandler):
    # v57: same scanner-noise suppression as DBTreeHandler. The plain-HTTP
    # port gets probed by the same tools and all those probes just redirect
    # to HTTPS - no point logging each one.
    def log_message(self, format, *args):
        if not DEBUG_LOGGING:
            return
        haystack = ((getattr(self, 'path', '') or '') + ' ' +
                    (getattr(self, 'requestline', '') or '')).lower()
        if any(m in haystack for m in DBTreeHandler._SCANNER_FINGERPRINTS):
            return
        logger.info(format % args)

    def _redirect(self):
        target_host = get_preferred_host_for_display()
        location = f'https://{target_host}:{HTTPS_PORT}{self.path}'
        self.send_response(301)
        self.send_header('Location', location)
        self.end_headers()

    def do_GET(self):
        self._redirect()

    def do_POST(self):
        self._redirect()

    def do_PUT(self):
        self._redirect()

    def do_DELETE(self):
        self._redirect()

    def do_OPTIONS(self):
        self._redirect()


# -----------------------------------------------------------------------------
# Server
# -----------------------------------------------------------------------------
def run_server():
    global TLS_ACTIVE, TLS_COOKIE_SECURE
    redirect_server = None
    redirect_thread = None

    try:
        display_host = get_preferred_host_for_display()

        if HTTPS_ENABLED:
            tls_ready = ensure_self_signed_certificate(display_host)
            if tls_ready and cert_files_exist():
                context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
                context.load_cert_chain(certfile=HTTPS_CERTFILE, keyfile=HTTPS_KEYFILE)

                TLS_ACTIVE = True
                TLS_COOKIE_SECURE = True

                with ThreadingHTTPServer((SERVER_HOST, HTTPS_PORT), DBTreeHandler) as httpsd:
                    httpsd.socket = context.wrap_socket(httpsd.socket, server_side=True)

                    redirect_url = None
                    if HTTP_REDIRECT_TO_HTTPS:
                        redirect_server = ThreadingHTTPServer((SERVER_HOST, HTTP_PORT), RedirectHandler)
                        redirect_thread = threading.Thread(target=redirect_server.serve_forever, daemon=True)
                        redirect_thread.start()
                        redirect_url = f'http://{display_host}:{HTTP_PORT}'

                    app_url = f'https://{display_host}:{HTTPS_PORT}'
                    print_startup_banner('HTTPS', app_url, redirect_url=redirect_url)
                    log_info(f'Starting HTTPS server on {SERVER_HOST}:{HTTPS_PORT}')
                    httpsd.serve_forever()
                    return

            fallback_note = (
                'HTTPS requested, but automatic certificate generation is unavailable. '
                'Falling back to HTTP mode.'
            )
        else:
            fallback_note = None

        TLS_ACTIVE = False
        TLS_COOKIE_SECURE = False
        with ThreadingHTTPServer((SERVER_HOST, HTTP_PORT), DBTreeHandler) as httpd:
            app_url = f'http://{display_host}:{HTTP_PORT}'
            print_startup_banner('HTTP', app_url, startup_note=fallback_note)
            log_info(f'Starting HTTP server on {SERVER_HOST}:{HTTP_PORT}')
            httpd.serve_forever()
    except KeyboardInterrupt:
        log_info('Server shutdown initiated by user')
        print('\nShutting down server')
    except Exception as e:
        logger.error(f'Server error: {str(e)}')
        raise
    finally:
        if redirect_server is not None:
            redirect_server.shutdown()
            redirect_server.server_close()


if __name__ == '__main__':
    run_server()