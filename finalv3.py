"""
Smart Stealth Scraper – Final (v6.7.1, single-file)
====================================================
Improvements over v6.7.0:
  • StealthBrowser.navigate() now logs when the browser is redirected
    away from the URL you asked for (Cloudflare / canonical-address
    redirect detection).
  • "Scrape ALL Results" now reads the address box. If the address in
    the entry differs from the currently loaded page, the browser is
    navigated to the new address first and the results table is reset,
    then the scrape runs. No more stale results from a previous address.
  • New helper BrowserApp._reset_results_for_new_address() wipes the
    table + bookkeeping when the target address changes.

Run: python smart_scraper.py
"""

from __future__ import annotations

# ══════════════════════════════════════════════════════════════════
# IMPORTS
# ══════════════════════════════════════════════════════════════════
import base64
import json
import os
import random
import re
import select
import socket
import threading
import time
import tkinter as tk
from dataclasses import dataclass
from tkinter import ttk, messagebox

import undetected_chromedriver as uc
from selenium.webdriver.common.by import By
from bs4 import BeautifulSoup

import gspread
from google.oauth2.service_account import Credentials

try:
    import usaddress as _usaddress
    _HAS_USADDRESS = True
except ImportError:
    _usaddress = None
    _HAS_USADDRESS = False

# Prefer lxml; fall back to the stdlib parser if unavailable.
try:
    import lxml  # noqa: F401
    _BS_PARSER = "lxml"
except ImportError:
    _BS_PARSER = "html.parser"


# ══════════════════════════════════════════════════════════════════
# CONFIGURATION
# ══════════════════════════════════════════════════════════════════
SERVICE_ACCOUNT_FILE = "service_account.json"
SPREADSHEET_NAME     = "BackgroundCheck_Data"
WORKSHEET_NAME       = "Sheet1"

RESIDENTIAL_PROXY    = None
HEADLESS             = False
CHROME_MAJOR_VERSION = None

MAX_PAGES                   = 25
PHONE_NEAR_NAME_WINDOW      = 60
ADDRESS_WAIT_TIMEOUT        = 12
ADDRESS_PARSE_RETRIES       = 3
NAV_MAX_RETRIES             = 3
HIGHLIGHT_DURATION_NEW      = 10
HIGHLIGHT_DURATION_UPDATED  = 6

EXPORT_COLUMNS = [
    "Name", "Aliases", "Age",
    "Phone", "Phone 2", "Phone 3",
    "Email", "Address", "City", "State", "ZIP",
    "Previous Addresses", "Relatives",
    "Source URL",
]

ADDRESS_PREFIX = "https://www.cyberbackgroundchecks.com/address/"

ADDRESS_PRIORITY_SELECTORS = [
    "div.col-md-5.text-secondary",
    "div[class*='col-md-5'][class*='text-secondary']",
    "div[class~='col-md-5'][class~='text-secondary']",
    "div.col-md-6.text-secondary",
    "div.col-md-7.text-secondary",
    "div.col-md-4.text-secondary",
    "[class*='text-secondary'][class*='col-md']",
]

ADDRESS_CURRENT_TITLE_PREFIX = "Find other people associated with"
ADDRESS_CURRENT_SELECTORS = [
    "a.address-current",
    "a[class*='address-current']",
    "[class*='address-current']",
]

ADDRESS_JUNK_MARKERS = [
    "remove my record",
    "full background report",
    "background report",
    "current address",
    "view details",
    "view full report",
    "show more",
    "click here",
    "learn more",
]


# ══════════════════════════════════════════════════════════════════
# TIMING PROFILE (immutable, thread-safe)
# ══════════════════════════════════════════════════════════════════
@dataclass(frozen=True)
class Timing:
    min_delay_between_lookups: float
    scroll_pause: float
    detail_drill_delay: float
    address_wait_poll: float
    post_nav_settle: float
    challenge_poll: float
    results_poll: float
    reveal_pre_click: float
    reveal_post_click: float
    reveal_rounds: int
    load_more_post_click: float
    scroll_max_iter: int
    load_more_max_rounds: int

    @classmethod
    def for_mode(cls, fast: bool) -> "Timing":
        if fast:
            return cls(
                min_delay_between_lookups=2.5,
                scroll_pause=0.5,
                detail_drill_delay=0.4,
                address_wait_poll=0.15,
                post_nav_settle=0.3,
                challenge_poll=0.3,
                results_poll=0.15,
                reveal_pre_click=0.1,
                reveal_post_click=0.3,
                reveal_rounds=3,
                load_more_post_click=0.8,
                scroll_max_iter=25,
                load_more_max_rounds=8,
            )
        return cls(
            min_delay_between_lookups=8.0,
            scroll_pause=1.2,
            detail_drill_delay=2.0,
            address_wait_poll=0.4,
            post_nav_settle=1.0,
            challenge_poll=1.0,
            results_poll=0.4,
            reveal_pre_click=0.3,
            reveal_post_click=0.8,
            reveal_rounds=6,
            load_more_post_click=1.8,
            scroll_max_iter=40,
            load_more_max_rounds=15,
        )


class TimingBox:
    """Thread-safe holder around an immutable Timing profile."""

    def __init__(self, fast: bool = True):
        self._lock = threading.Lock()
        self._timing = Timing.for_mode(fast)

    def get(self) -> Timing:
        with self._lock:
            return self._timing

    def set_fast(self, fast: bool) -> Timing:
        with self._lock:
            self._timing = Timing.for_mode(fast)
            return self._timing


# ══════════════════════════════════════════════════════════════════
# PERSISTENT CONFIG
# ══════════════════════════════════════════════════════════════════
CONFIG_FILE = "scraper_config.json"


def load_config() -> dict:
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
            return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def save_config(cfg: dict) -> bool:
    try:
        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            json.dump(cfg, f, indent=2)
        return True
    except Exception as e:
        print(f"[Config] Save failed: {e}")
        return False


# ══════════════════════════════════════════════════════════════════
# TEXT UTILS
# ══════════════════════════════════════════════════════════════════
def normalize_whitespace(s) -> str:
    return re.sub(r"\s+", " ", (s or "")).strip()


def normalize_age(s) -> str:
    if not s:
        return ""
    m = re.search(r"\d{1,3}", str(s))
    return m.group(0) if m else ""


def col_letter(n: int) -> str:
    result = ""
    while n > 0:
        n, rem = divmod(n - 1, 26)
        result = chr(65 + rem) + result
    return result


BLOCKED_NAME_PATTERNS = [
    re.compile(r"^\s*cyber\s+background\s+checks\s*$", re.I),
    re.compile(r"\bcyber\s+background\s+checks\b", re.I),
    re.compile(r"^\s*\$?\d+(?:\.\d+)?\s*/\s*mo\.?\s*$", re.I),
    re.compile(r"^\s*name\s*$", re.I),
    re.compile(r"^\s*search\s+for\s+people", re.I),
]

JUNK_NAME_PATTERNS = [
    re.compile(r"[?:!]", re.I),
    re.compile(r"\b(privacy|notice|terms|cookie|policy|disclaimer)\b", re.I),
    re.compile(r"\b(what\s+is|how\s+to|learn\s+more|click\s+here|read\s+more|show\s+more)\b", re.I),
    re.compile(r"\b(skip\s+trace|background\s+check|built\s+for)\b", re.I),
    re.compile(r"\b(lives?\s+at)\b", re.I),
    re.compile(r"\bsearch\b", re.I),
    re.compile(r"^\s*(current\s+)?address", re.I),
    re.compile(r"^\s*phone\s+number", re.I),
    re.compile(r"^\s*(full\s+)?background\s+report", re.I),
]

_AGE_SUFFIX_RE     = re.compile(r"\s+Age\s*:?\s*\d{1,3}\s*$", re.I)
_REAL_NAME_WORD_RE = re.compile(r"^[A-Z][a-zA-Z'.\-]*\.?$")
_INITIAL_RE        = re.compile(r"^[A-Z]\.?$")


def strip_age_from_name(name: str) -> str:
    if not name:
        return ""
    return _AGE_SUFFIX_RE.sub("", normalize_whitespace(name)).strip()


def is_blocked_name(name: str) -> bool:
    if not name:
        return False
    n = strip_age_from_name(name)
    if not n:
        return True
    return any(p.search(n) for p in BLOCKED_NAME_PATTERNS)


def looks_like_real_name(name: str) -> bool:
    if not name:
        return False
    n = strip_age_from_name(name)
    if not n:
        return False
    for p in JUNK_NAME_PATTERNS:
        if p.search(n):
            return False
    words = n.split()
    if not (2 <= len(words) <= 5):
        return False
    for w in words:
        if not (_REAL_NAME_WORD_RE.match(w) or _INITIAL_RE.match(w)):
            return False
    return True


# ══════════════════════════════════════════════════════════════════
# PROXY
# ══════════════════════════════════════════════════════════════════
def normalize_proxy_url(raw: str) -> str:
    if not raw:
        return ""
    s = raw.strip()
    if "://" in s and "@" in s:
        return s
    if "@" in s and "://" not in s:
        return "http://" + s
    if "://" in s:
        scheme, rest = s.split("://", 1)
        scheme = scheme or "http"
    else:
        scheme, rest = "http", s
    parts = rest.split(":")
    if len(parts) == 2:
        return f"{scheme}://{rest}"
    if len(parts) >= 4:
        host, port, user = parts[0], parts[1], parts[2]
        password = ":".join(parts[3:])
        return f"{scheme}://{user}:{password}@{host}:{port}"
    return f"{scheme}://{rest}"


def redact_proxy(proxy_url: str) -> str:
    if not proxy_url:
        return proxy_url
    try:
        scheme, rest = proxy_url.split("://", 1)
        if "@" in rest:
            creds, host = rest.rsplit("@", 1)
            if ":" in creds:
                user, _ = creds.split(":", 1)
                return f"{scheme}://{user}:***@{host}"
        return proxy_url
    except Exception:
        return proxy_url


class LocalProxyForwarder:
    """In-process HTTP proxy that injects Proxy-Authorization."""

    IDLE_TIMEOUT = 120
    CONNECT_TIMEOUT = 30

    def __init__(self, upstream_url: str):
        self.upstream_url = (upstream_url or "").strip()
        self.upstream_host = ""
        self.upstream_port = 8080
        self.username = ""
        self.password = ""
        self._parse_upstream()
        self.listen_host = "127.0.0.1"
        self.listen_port = 0
        self.local_url = ""
        self._server_socket = None
        self._thread = None
        self._stop_event = threading.Event()

    def _parse_upstream(self):
        s = normalize_proxy_url(self.upstream_url)
        if "://" in s:
            _, s = s.split("://", 1)
        if "@" in s:
            creds, hostport = s.rsplit("@", 1)
            if ":" in creds:
                self.username, self.password = creds.split(":", 1)
            else:
                self.username = creds
        else:
            hostport = s
        if ":" in hostport:
            host_part, port_str = hostport.rsplit(":", 1)
            try:
                self.upstream_port = int(port_str)
            except ValueError:
                self.upstream_port = 8080
            self.upstream_host = host_part
        else:
            self.upstream_host = hostport

    def has_credentials(self) -> bool:
        return bool(self.username and self.password)

    def start(self) -> str:
        self._server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self._server_socket.bind((self.listen_host, 0))
        self.listen_port = self._server_socket.getsockname()[1]
        self._server_socket.listen(100)
        self._server_socket.settimeout(1.0)
        self.local_url = f"http://{self.listen_host}:{self.listen_port}"
        self._thread = threading.Thread(target=self._serve_loop, daemon=True)
        self._thread.start()
        return self.local_url

    def stop(self):
        self._stop_event.set()
        if self._server_socket:
            try:
                self._server_socket.close()
            except Exception:
                pass
            self._server_socket = None
        if self._thread:
            try:
                self._thread.join(timeout=3)
            except Exception:
                pass
            self._thread = None

    def _serve_loop(self):
        while not self._stop_event.is_set():
            try:
                client, _ = self._server_socket.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            except Exception:
                continue
            threading.Thread(target=self._handle_client, args=(client,),
                             daemon=True).start()

    @staticmethod
    def _read_headers(sock, max_bytes=131072):
        data = b""
        while b"\r\n\r\n" not in data:
            try:
                chunk = sock.recv(4096)
            except Exception:
                return None, None
            if not chunk:
                return None, None
            data += chunk
            if len(data) > max_bytes:
                return None, None
        idx = data.index(b"\r\n\r\n") + 4
        return data[:idx], data[idx:]

    def _handle_client(self, client):
        upstream = None
        try:
            client.settimeout(self.CONNECT_TIMEOUT)
            headers_part, remaining = self._read_headers(client)
            if headers_part is None:
                return
            lines = headers_part.split(b"\r\n")
            method = lines[0].split(b" ", 1)[0].upper()
            auth_b64 = base64.b64encode(
                f"{self.username}:{self.password}".encode("utf-8")
            ).decode("ascii")
            new_lines = [lines[0]]
            for line in lines[1:]:
                if not line:
                    continue
                low = line.lower()
                if low.startswith(b"proxy-authorization:"):
                    continue
                if low.startswith(b"proxy-connection:"):
                    continue
                new_lines.append(line)
            rebuilt = b"\r\n".join(new_lines) + b"\r\n"
            rebuilt += f"Proxy-Authorization: Basic {auth_b64}\r\n".encode("ascii")
            rebuilt += b"\r\n"
            upstream = socket.create_connection(
                (self.upstream_host, self.upstream_port),
                timeout=self.CONNECT_TIMEOUT,
            )
            upstream.sendall(rebuilt)
            if remaining:
                upstream.sendall(remaining)
            if method == b"CONNECT":
                resp, extra = self._read_headers(upstream)
                if resp is None:
                    return
                client.sendall(resp)
                if extra:
                    client.sendall(extra)
                if b" 200 " not in resp.split(b"\r\n", 1)[0]:
                    return
            self._tunnel(client, upstream)
        except Exception:
            pass
        finally:
            try:
                client.close()
            except Exception:
                pass
            if upstream is not None:
                try:
                    upstream.close()
                except Exception:
                    pass

    def _tunnel(self, a, b):
        sockets = [a, b]
        while True:
            try:
                r, _, _ = select.select(sockets, [], [], self.IDLE_TIMEOUT)
            except Exception:
                break
            if not r:
                break
            done = False
            for s in r:
                try:
                    data = s.recv(65536)
                except Exception:
                    done = True
                    break
                if not data:
                    done = True
                    break
                other = b if s is a else a
                try:
                    other.sendall(data)
                except Exception:
                    done = True
                    break
            if done:
                break


# ══════════════════════════════════════════════════════════════════
# PHONE EXTRACTION
# ══════════════════════════════════════════════════════════════════
_PHONE_BODY = r"\(?(\d{3})\)?[\s.\-]?(\d{3})[\s.\-]?(\d{4})"
_PHONE_EXT  = r"(?:\s*(?:ext|x|extension|#)\.?\s*(\d{1,6}))?"

PHONE_PATTERNS = [
    re.compile(r"(?:Phone(?:\s*Number)?|Telephone|Tel|Mobile|Cell|Contact)"
               r"\s*[:\-]?\s*" + _PHONE_BODY + _PHONE_EXT, re.I),
    re.compile(r"\(" + _PHONE_BODY + r"\)" + _PHONE_EXT),
    re.compile(r"\+1[\s.\-]?" + _PHONE_BODY + _PHONE_EXT),
    re.compile(r"\b" + _PHONE_BODY + _PHONE_EXT),
    re.compile(r"\b(\d{3})\.(\d{3})\.(\d{4})" + _PHONE_EXT),
    re.compile(r"\b(\d{3})\s+(\d{3})\s+(\d{4})" + _PHONE_EXT),
    re.compile(r"\b([2-9]\d{2})(\d{3})(\d{4})\b"),
]

FALSE_POSITIVE_PATTERNS = [
    re.compile(r"^\d{4}-\d{2}-\d{2}$"),
    re.compile(r"^\d{1,2}/\d{1,2}/\d{2,4}$"),
    re.compile(r"^\d{3}-\d{2}-\d{4}$"),
    re.compile(r"^\d{5}-\d{4}$"),
]


def _format_phone(area, exch, line, ext=None):
    number = f"({area}) {exch}-{line}"
    if ext:
        number += f" ext. {ext}"
    return number


def _is_valid_us_phone(area, exch):
    if not area or not exch:
        return False
    return area[0] not in "01" and exch[0] not in "01"


def _looks_like_real_phone(number):
    if not number:
        return False
    digits = re.sub(r"\D", "", number)
    if len(digits) < 10:
        return False
    for fp in FALSE_POSITIVE_PATTERNS:
        if fp.match(number):
            return False
    if digits in ("1234567890", "0123456789", "1111111111", "0000000000"):
        return False
    return True


def _find_all_phones_in_text(text: str):
    if not text:
        return []
    results = []
    for pat in PHONE_PATTERNS:
        for m in pat.finditer(text):
            nums = [g for g in m.groups() if g and g.isdigit()]
            if len(nums) >= 3:
                area, exch, line = nums[-3], nums[-2], nums[-1]
                ext = nums[-4] if len(nums) >= 4 else None
                if _is_valid_us_phone(area, exch):
                    results.append(_format_phone(area, exch, line, ext))
    seen, out = set(), []
    for r in results:
        if r not in seen and _looks_like_real_phone(r):
            seen.add(r)
            out.append(r)
    return out


class PhoneExtractor:
    PHONE_ATTRS = ["data-phone", "data-tel", "data-telephone", "data-number",
                   "data-value", "value", "content", "aria-label", "title", "alt"]
    PHONE_SELECTORS = [
        "a[href^='tel:']", "a[href^='callto:']", "a[href^='sms:']",
        "a[href^='whatsapp:']",
        "span.phone", "div.phone", "p.phone",
        "span.phone-number", "div.phone-number",
        "span[class*='phone']", "div[class*='phone']",
        "span[class*='tel']", "div[class*='tel']",
        "span[class*='mobile']", "div[class*='mobile']",
        "span[class*='cell']", "div[class*='cell']",
        "span[class*='contact']", "div[class*='contact']",
        "[data-phone]", "[data-tel]", "[data-telephone]",
        "[itemprop='telephone']",
    ]
    LABELS = ["phone", "phone number", "telephone", "tel",
              "mobile", "cell", "cell phone", "mobile phone", "contact number"]

    def extract_from_container(self, container, person_name, full_page_text):
        found = []
        for a in container.find_all("a", href=True):
            low = a["href"].lower()
            for scheme in ("tel:", "callto:", "sms:", "whatsapp:"):
                if low.startswith(scheme):
                    found.extend(_find_all_phones_in_text(a["href"][len(scheme):]))
        for sel in self.PHONE_SELECTORS:
            try:
                els = container.select(sel)
            except Exception:
                continue
            for el in els:
                txt = el.get_text(" ", strip=True)
                if txt:
                    found.extend(_find_all_phones_in_text(txt))
        lines = [l.strip() for l in container.get_text("\n", strip=True).splitlines()
                 if l.strip()]
        for i, line in enumerate(lines):
            low = line.lower()
            for lbl in self.LABELS:
                if re.search(rf"\b{re.escape(lbl)}\b", low):
                    found.extend(_find_all_phones_in_text(line))
                    if i + 1 < len(lines):
                        found.extend(_find_all_phones_in_text(lines[i + 1]))
        for el in container.find_all(True):
            for attr in self.PHONE_ATTRS:
                v = el.get(attr)
                if v and isinstance(v, str):
                    found.extend(_find_all_phones_in_text(v))
        if not found and person_name and full_page_text:
            found.extend(self._near_name_phones(full_page_text, person_name))
        seen, out = set(), []
        for p in found:
            if p and p not in seen and _looks_like_real_phone(p):
                seen.add(p)
                out.append(p)
        return out

    def _near_name_phones(self, page_text, name):
        results = []
        for m in re.finditer(re.escape(name), page_text):
            start = max(0, m.start() - PHONE_NEAR_NAME_WINDOW)
            end = min(len(page_text), m.end() + PHONE_NEAR_NAME_WINDOW)
            results.extend(_find_all_phones_in_text(page_text[start:end]))
        seen, out = set(), []
        for p in results:
            if p not in seen:
                seen.add(p)
                out.append(p)
        return out


# ══════════════════════════════════════════════════════════════════
# ADDRESS
# ══════════════════════════════════════════════════════════════════
_LEADING_JUNK_PHRASE = (
    r"(?:Remove\s+My\s+Record|FULL\s+BACKGROUND\s+REPORT|Background\s+Report|"
    r"Current\s+Address|Current\s+Residence|Current\s+Location|"
    r"Present\s+Address|Current\s+Home)"
)

_LEADING_JUNK_PREFIX_STRICT_RE = re.compile(
    r"^\s*(?:\d{1,6}\s+)?"
    r"Remove\s+My\s+Record\s+"
    r"FULL\s+BACKGROUND\s+REPORT\s+"
    r"Current\s+Address\s+",
    re.I,
)

_LEADING_JUNK_PREFIX_LOOSE_RE = re.compile(
    r"^\s*(?:\d{1,6}\s+)?"
    + _LEADING_JUNK_PHRASE
    + r"(?:\s*[:\-]?\s*" + _LEADING_JUNK_PHRASE + r")*\s*[:\-]?\s*",
    re.I,
)


def strip_leading_address_junk(s):
    if not s:
        return s
    s2 = _LEADING_JUNK_PREFIX_STRICT_RE.sub("", s, count=1)
    if s2 != s and s2.strip():
        return s2.lstrip(" :-,\t")
    s2 = _LEADING_JUNK_PREFIX_LOOSE_RE.sub("", s, count=1)
    if s2 != s and s2.strip():
        return s2.lstrip(" :-,\t")
    return s


US_STATE_ABBREVS = {
    "AL","AK","AZ","AR","CA","CO","CT","DE","FL","GA","HI","ID","IL",
    "IN","IA","KS","KY","LA","ME","MD","MA","MI","MN","MS","MO","MT",
    "NE","NV","NH","NJ","NM","NY","NC","ND","OH","OK","OR","PA","RI",
    "SC","SD","TN","TX","UT","VT","VA","WA","WV","WI","WY","DC",
}

US_STATE_NAMES = {
    "Alabama","Alaska","Arizona","Arkansas","California","Colorado",
    "Connecticut","Delaware","Florida","Georgia","Hawaii","Idaho",
    "Illinois","Indiana","Iowa","Kansas","Kentucky","Louisiana","Maine",
    "Maryland","Massachusetts","Michigan","Minnesota","Mississippi",
    "Missouri","Montana","Nebraska","Nevada","New Hampshire","New Jersey",
    "New Mexico","New York","North Carolina","North Dakota","Ohio",
    "Oklahoma","Oregon","Pennsylvania","Rhode Island","South Carolina",
    "South Dakota","Tennessee","Texas","Utah","Vermont","Virginia",
    "Washington","West Virginia","Wisconsin","Wyoming",
    "District of Columbia",
}

_DIRECTIONAL = (r"(?:N|S|E|W|NE|NW|SE|SW|"
                r"North|South|East|West|"
                r"Northeast|Northwest|Southeast|Southwest)")

_ST_SUFFIXES = (
    r"(?:Ave|Avenue|St|Street|Rd|Road|Blvd|Boulevard|Dr|Drive|Ln|Lane|"
    r"Way|Ct|Court|Ter|Terrace|Pl|Place|Hwy|Highway|Cir|Circle|"
    r"Pkwy|Parkway|Sq|Square|Aly|Alley|Loop|Bnd|Bend|Xing|Crossing|"
    r"Trl|Trail|Pt|Point|Run|Walk|Cv|Cove|Grv|Grove|Holw|Hollow|"
    r"Ldg|Lodge|Mnr|Manor|Mdw|Meadow|Pass|Path|Pike|Row|Spg|Spring|"
    r"Vlg|Village|Vis|Vista|Brg|Bridge|Byp|Bypass|Clb|Club|"
    r"Cor|Corner|Cswy|Causeway|Expy|Expressway|Fwy|Freeway|"
    r"Gdn|Garden|Gtwy|Gateway|Hbr|Harbor|Hvn|Haven|Is|Island|"
    r"Jct|Junction|Ky|Key|Lndg|Landing|Mall|Mtwy|Motorway|Nck|Neck|"
    r"Orch|Orchard|Park|Prt|Port|Radl|Radial|Rst|Rest|Rte|Route|"
    r"Shr|Shore|Skwy|Skyway|Smt|Summit|Trak|Track|Trce|Trace|"
    r"Tunl|Tunnel|Vly|Valley|Via|Vw|View|Wlk|Wells|Wls)"
)

_UNIT = (r"(?:Apt|Apartment|Unit|Ste|Suite|Bldg|Building|Fl|Floor|"
         r"Rm|Room|Lot|Trlr|Trailer|#)")

FULL_ADDR_RE = re.compile(
    r"\b(\d{1,6}(?:[-\s]\d{1,4})?\s+"
    rf"(?:{_DIRECTIONAL}\.?\s+)?"
    r"[A-Za-z0-9'\-.]"
    r"[A-Za-z0-9'\-.\s]*?\s+"
    rf"{_ST_SUFFIXES}\.?"
    rf"(?:\s+{_UNIT}\.?\s*[\w\-]+)?"
    r"(?:\s*,?\s*([A-Z][A-Za-z.\s'\-]{1,40}?))?"
    r"\s*,?\s*([A-Z]{2})\b"
    r"(?:\s*,?\s*(\d{5}(?:-\d{4})?))?"
    r")",
    re.I,
)

STREET_ONLY_RE = re.compile(
    r"\b(\d{1,6}(?:[-\s]\d{1,4})?\s+"
    rf"(?:{_DIRECTIONAL}\.?\s+)?"
    r"[A-Za-z0-9'\-.]"
    r"[A-Za-z0-9'\-.\s]*?\s+"
    rf"{_ST_SUFFIXES}\.?"
    rf"(?:\s+{_UNIT}\.?\s*[\w\-]+)?)",
    re.I,
)

CITY_STATE_ZIP_RE = re.compile(
    r"^\s*([A-Z][A-Za-z.\s'\-]{2,40}?)\s*,\s*([A-Z]{2})\s+(\d{5}(?:-\d{4})?)\s*$"
)
CITY_STATE_RE = re.compile(
    r"^\s*([A-Z][A-Za-z.\s'\-]{2,40}?)\s*,\s*([A-Z]{2})\s*$"
)


def _uppercase_state_in_address(s):
    if not s:
        return s
    s = re.sub(r"\b(\d{5})\s+(\d{4})\b(?=\s*(?:,|$))", r"\1-\2", s)

    def _fix_after_comma(m):
        abbr = m.group(1)
        if abbr.upper() in US_STATE_ABBREVS:
            off = m.start(1) - m.start(0)
            return m.group(0)[:off] + abbr.upper() + m.group(0)[off + len(abbr):]
        return m.group(0)

    def _fix_before_zip(m):
        abbr = m.group(1)
        if abbr.upper() in US_STATE_ABBREVS:
            return abbr.upper() + m.group(2)
        return m.group(0)

    s = re.sub(r",\s*([A-Za-z]{2})(?=\s*\d|\s*$|\s*,)", _fix_after_comma, s)
    s = re.sub(r"\b([A-Za-z]{2})(\s+\d{5}(?:-\d{4})?\b)", _fix_before_zip, s)
    return s


def _split_with_usaddress(addr):
    if not _HAS_USADDRESS or not addr:
        return None
    try:
        parts, _kind = _usaddress.tag(addr)
    except Exception:
        return None

    num = parts.get("AddressNumber", "")
    name = parts.get("StreetName", "")
    stype = parts.get("StreetNamePostType", "")
    if not num or not (name or stype):
        return None

    street_parts = [
        num,
        parts.get("StreetNamePreDirectional", ""),
        parts.get("StreetNamePreType", ""),
        name,
        parts.get("StreetNamePostDirectional", ""),
        stype,
    ]
    street = " ".join(p for p in street_parts if p)

    unit_type = parts.get("OccupancyType", "")
    unit_id = parts.get("OccupancyIdentifier", "")
    if unit_id:
        street = f"{street} {unit_type} {unit_id}".strip()

    city = parts.get("PlaceName", "")
    state = (parts.get("StateName", "") or "").upper()
    zipc = parts.get("ZipCode", "")

    if not (state or zipc or city):
        return None

    return {"street": street.strip(" ,"), "city": city, "state": state, "zip": zipc}


def _split_with_regex(addr):
    m = FULL_ADDR_RE.search(addr)
    if m:
        city  = (m.group(2) or "").strip()
        state = (m.group(3) or "").strip().upper()
        zipc  = (m.group(4) or "").strip()
        whole = m.group(0)
        end = m.start(2) if m.group(2) else m.start(3)
        street = whole[: end - m.start(1)].strip(" ,")
        if not street:
            street = whole.strip(" ,")
        if not zipc:
            tail = addr[m.end():]
            zm = re.search(r"\b(\d{5}(?:-\d{4})?)\b", tail)
            if zm:
                zipc = zm.group(1)
        return {"street": street, "city": city, "state": state, "zip": zipc}

    zipc = ""
    zm = re.search(r"\b(\d{5}(?:-\d{4})?)\b", addr)
    if zm:
        zipc = zm.group(1)

    state = ""
    sm = re.search(r"\b([A-Z]{2})\s+(?=\d{5})", addr)
    if sm and sm.group(1) in US_STATE_ABBREVS:
        state = sm.group(1)
    else:
        sm = re.search(r",\s*([A-Z]{2})\b", addr)
        if sm and sm.group(1) in US_STATE_ABBREVS:
            state = sm.group(1)

    city = ""
    if state:
        m = re.search(
            r",\s*([A-Za-z][A-Za-z.\s'\-]{1,40}?)\s*,?\s*"
            + re.escape(state) + r"\b",
            addr,
        )
        if m:
            city = m.group(1).strip()

    street_m = STREET_ONLY_RE.search(addr)
    street = street_m.group(0).strip(" ,") if street_m else addr.strip()
    return {"street": street, "city": city, "state": state, "zip": zipc}


def split_address(addr):
    empty = {"street": "", "city": "", "state": "", "zip": ""}
    if not addr:
        return empty
    cleaned = strip_leading_address_junk(addr)
    cleaned = _uppercase_state_in_address(cleaned)
    parsed = _split_with_usaddress(cleaned)
    if parsed and parsed["street"]:
        return parsed
    return _split_with_regex(cleaned)


def _count_person_names(el):
    if el is None:
        return 0
    seen, cnt = set(), 0
    for h in el.find_all(["h1", "h2", "h3", "h4", "h5"]):
        txt = strip_age_from_name(normalize_whitespace(h.get_text(" ", strip=True)))
        if looks_like_real_name(txt):
            key = txt.lower()
            if key not in seen:
                seen.add(key)
                cnt += 1
    return cnt


class AddressExtractor:
    PRIORITY_SELECTORS = ADDRESS_PRIORITY_SELECTORS
    JUNK_ADDRESS_MARKERS = ADDRESS_JUNK_MARKERS

    ADDRESS_SELECTORS = [
        "[itemprop='streetAddress']",
        "[itemprop='address']",
        "span.address", "div.address", "p.address",
        "span.street-address", "div.street-address",
        "span[class*='street-address']", "div[class*='street-address']",
        "span[class*='address']", "div[class*='address']",
        "span[class*='location']", "div[class*='location']",
        "[data-address]", "[data-street]", "[data-address-line]",
        ".address-line", ".addr", ".location-line",
    ]

    LABELS = ["address", "current address", "location", "residence",
              "residential address", "home address", "street address",
              "lives at", "located at"]

    PRIORITY_LABELS = [
        "current address", "current residence", "current location",
        "current home", "present address", "current mailing address",
        "current street address",
    ]

    DATA_ATTRS = ["data-address", "data-street", "data-address-line",
                  "data-location", "content", "value", "title"]

    SCORE_PRIORITY_MATCH   = 500
    SCORE_FULL_WITH_ZIP    = 100
    SCORE_CITY_STATE       = 70
    SCORE_WITH_SUFFIX      = 40
    SCORE_WITH_UNIT        = 15
    SCORE_WITH_DIRECTIONAL = 10

    MAX_PARENT_CLIMB = 6
    MAX_PARENT_TAGS  = 1200
    MAX_ADDRS_PER_CONTAINER = 2

    def __init__(self):
        self.last_candidates = []

    @staticmethod
    def _clean_address_current_title(raw):
        if not raw:
            return ""
        s = normalize_whitespace(raw)
        pfx = ADDRESS_CURRENT_TITLE_PREFIX.lower()
        if s.lower().startswith(pfx):
            s = s[len(pfx):].lstrip(" :-,\t")
        s = strip_leading_address_junk(s)
        s = re.sub(r"\b(\d{5})\s+(\d{4})\b", r"\1-\2", s)
        return s.strip(" ,;")

    def _from_address_current_link(self, container):
        if container is None:
            return ""
        for sel in ADDRESS_CURRENT_SELECTORS:
            try:
                els = container.select(sel)
            except Exception:
                continue
            for el in els:
                title = el.get("title") or ""
                addr = self._clean_address_current_title(title)
                if addr and re.match(r"^\s*\d{1,6}", addr):
                    return addr
                try:
                    txt = el.get_text(" ", strip=True)
                except Exception:
                    txt = ""
                addr = self._clean_address_current_title(txt)
                if addr and re.match(r"^\s*\d{1,6}", addr):
                    return addr
        return ""

    def _sanitize(self, text):
        if not text:
            return ""
        s = normalize_whitespace(str(text))
        if not s:
            return ""

        s = strip_leading_address_junk(s)
        if not s:
            return ""

        low = s.lower()
        cut_end = -1
        for lbl in self.PRIORITY_LABELS:
            pos = low.rfind(lbl)
            if pos >= 0:
                cut_end = max(cut_end, pos + len(lbl))
        if cut_end > 0:
            s = s[cut_end:].lstrip(" :-,\t\n")
            if not s:
                return ""

        low = s.lower()
        last_lead_end = 0
        for marker in self.JUNK_ADDRESS_MARKERS:
            idx = low.find(marker)
            if 0 <= idx < 60:
                last_lead_end = max(last_lead_end, idx + len(marker))
        if last_lead_end > 0:
            candidate = s[last_lead_end:].lstrip(" :-,")
            if candidate:
                s = candidate
        if not s:
            return ""

        s = _uppercase_state_in_address(s)

        m = FULL_ADDR_RE.search(s)
        if m:
            return self._normalize(m.group(0))
        m = STREET_ONLY_RE.search(s)
        if m:
            return self._normalize(m.group(0))
        return ""

    def extract(self, container):
        self.last_candidates = []
        best = self._extract_from(container)
        if best:
            return best
        node = container
        for _ in range(self.MAX_PARENT_CLIMB):
            parent = getattr(node, "parent", None)
            if parent is None or parent.name in (None, "[document]", "html", "body"):
                break
            try:
                tag_count = len(parent.find_all(True))
            except Exception:
                tag_count = 99999
            if tag_count > self.MAX_PARENT_TAGS:
                break
            best = self._extract_from(parent)
            if best:
                return best
            for child in parent.find_all(True, recursive=False):
                if child is node:
                    continue
                try:
                    if len(child.find_all(True)) > 400:
                        continue
                except Exception:
                    continue
                best = self._extract_from(child)
                if best:
                    return best
            node = parent
        return ""

    def extract_from_page_text(self, full_page_text, name):
        if not full_page_text or not name:
            return ""
        results = []
        for m in re.finditer(re.escape(name), full_page_text):
            start = max(0, m.start() - 300)
            end = min(len(full_page_text), m.end() + 800)
            window = full_page_text[start:end]
            for am in FULL_ADDR_RE.finditer(window):
                results.append(am.group(0))
            if not results:
                for am in STREET_ONLY_RE.finditer(window):
                    results.append(am.group(0))
        best, best_score = "", 0
        seen = set()
        for r in results:
            n = self._normalize(r)
            if not n or n in seen:
                continue
            seen.add(n)
            s = self._score(n)
            if s > best_score:
                best_score = s
                best = n
        return best

    def _container_has_multiple_cards(self, container):
        if container is None:
            return True
        try:
            total = 0
            for sel in self.PRIORITY_SELECTORS:
                try:
                    total += len(container.select(sel))
                except Exception:
                    pass
            if total > self.MAX_ADDRS_PER_CONTAINER:
                return True
            if _count_person_names(container) > 1:
                return True
        except Exception:
            return True
        return False

    def _extract_from(self, container):
        if container is None:
            return ""
        if self._container_has_multiple_cards(container):
            return ""

        hit = self._from_address_current_link(container)
        if hit:
            cleaned = self._sanitize(hit) or hit
            if cleaned and re.match(r"^\s*\d{1,6}", cleaned):
                self.last_candidates.append(("address-current-link", cleaned))
                return cleaned

        hit = self._from_priority_selectors(container)
        if hit:
            self.last_candidates.append(("priority-selector", hit))
            return hit

        parent = getattr(container, "parent", None)
        if parent is not None and parent.name not in (None, "[document]", "html", "body"):
            if not self._container_has_multiple_cards(parent):
                try:
                    if parent.select_one(",".join(self.PRIORITY_SELECTORS)):
                        hit = self._from_priority_selectors(parent)
                        if hit:
                            self.last_candidates.append(("priority-parent", hit))
                            return hit
                except Exception:
                    pass

        candidates = []
        for c in self._from_priority_label(container):
            candidates.append((c, self.SCORE_PRIORITY_MATCH, "priority-label"))
        for c in self._from_current_address_element(container):
            candidates.append((c, self.SCORE_PRIORITY_MATCH, "current-addr-el"))
        for c in self._from_selectors(container):
            candidates.append((c, 0, "selector"))
        for c in self._from_labels(container):
            candidates.append((c, 25, "label"))
        for c in self._from_microdata(container):
            candidates.append((c, 0, "microdata"))
        for c in self._from_lines(container):
            candidates.append((c, 0, "lines"))
        for c in self._from_combined(container):
            candidates.append((c, 0, "combined"))
        for c in self._from_siblings(container):
            candidates.append((c, 0, "siblings"))

        best, best_score = "", 0
        seen = set()
        for c, bonus, src in candidates:
            n = self._normalize(c)
            if not n or n in seen:
                continue
            seen.add(n)
            s = self._score(n) + bonus
            self.last_candidates.append((src, n, s))
            if s > best_score:
                best_score = s
                best = n

        if best:
            best = self._sanitize(best)
        if best and not re.match(r"^\s*\d{1,6}", best):
            return ""
        return best

    def _from_priority_selectors(self, container):
        best, best_score = "", 0
        seen = set()
        for sel in self.PRIORITY_SELECTORS:
            try:
                els = container.select(sel)
            except Exception:
                continue
            for el in els:
                lines = [l.strip() for l in
                         el.get_text("\n", strip=True).splitlines() if l.strip()]
                if not lines:
                    continue
                clean = self._sanitize(", ".join(lines))
                if not clean:
                    continue
                n = self._normalize(clean)
                if not n or n in seen:
                    continue
                seen.add(n)
                if not re.match(r"^\s*\d{1,6}", n):
                    continue
                if _find_all_phones_in_text(n):
                    continue
                if not STREET_ONLY_RE.search(n) and not FULL_ADDR_RE.search(n):
                    if not re.search(r"\b\d{5}(?:-\d{4})?\b", n):
                        continue
                s = self._score(n)
                if s > best_score:
                    best_score = s
                    best = n
        return best

    def _from_current_address_element(self, container):
        results = []
        for el in container.find_all(string=True):
            raw = (el or "").strip()
            if not raw:
                continue
            low = re.sub(r"\s+", " ", raw.lower()).strip(" :-")
            hit = None
            for kw in self.PRIORITY_LABELS:
                if low == kw or low.startswith(kw + ":") or low == kw + ":":
                    hit = kw
                    break
            if not hit:
                continue
            parent = el.parent
            if parent is None:
                continue
            p_text = parent.get_text(" ", strip=True)
            idx = p_text.lower().find(hit)
            if idx >= 0:
                inline = p_text[idx + len(hit):].strip(" :-")
                if inline and re.match(r"^\d", inline):
                    results.append(inline)
                    continue
            nxt = parent.find_next_sibling()
            if nxt is not None:
                val = nxt.get_text(" ", strip=True)
                if val and re.match(r"^\d", val):
                    results.append(val)
                    continue
            node = parent
            for _ in range(3):
                node = node.find_next_sibling()
                if node is None:
                    break
                val = node.get_text(" ", strip=True)
                if val and re.match(r"^\d", val):
                    results.append(val)
                    break
        return results

    def _from_priority_label(self, container):
        results = []
        lines = [l.strip() for l in container.get_text("\n", strip=True).splitlines()
                 if l.strip()]
        for i, line in enumerate(lines):
            low = re.sub(r"\s+", " ", line.lower()).strip(" :-")
            hit = None
            for kw in self.PRIORITY_LABELS:
                if kw in low:
                    hit = kw
                    break
            if not hit:
                continue
            same_line_value = ""
            m = re.search(rf"{re.escape(hit)}\s*[:\-]\s*(.+)$", line, re.I)
            if m:
                same_line_value = m.group(1).strip(" :-")
            collected = []
            if same_line_value:
                collected.append(same_line_value)
                if re.search(r"\b\d{5}(?:-\d{4})?\b", same_line_value):
                    results.append(same_line_value)
                    break
            for j in range(i + 1, min(i + 6, len(lines))):
                candidate = lines[j].strip()
                if not candidate:
                    continue
                if self._is_section_label(candidate):
                    break
                if self._is_address_part(candidate):
                    collected.append(candidate)
                    if re.search(r"\b\d{5}(?:-\d{4})?\b", candidate):
                        break
                    if len(collected) >= 2:
                        break
                elif collected:
                    break
            if collected:
                if len(collected) == 1:
                    results.append(collected[0])
                elif len(collected) == 2 and self._is_street_line(collected[0]) \
                        and self._is_city_state(collected[1]):
                    results.append(f"{collected[0]}, {collected[1]}")
                else:
                    results.append(", ".join(collected))
                break
        return results

    def _from_selectors(self, container):
        out = []
        for sel in self.ADDRESS_SELECTORS:
            try:
                els = container.select(sel)
            except Exception:
                continue
            for el in els:
                txt = el.get_text(" ", strip=True)
                if txt:
                    out.append(txt)
        return out

    def _from_labels(self, container):
        out = []
        lines = [l.strip() for l in container.get_text("\n", strip=True).splitlines()
                 if l.strip()]
        for i, line in enumerate(lines):
            low = line.lower()
            for lbl in self.LABELS:
                if lbl in self.PRIORITY_LABELS:
                    continue
                m = re.match(rf"^\s*{re.escape(lbl)}\s*[:\-]\s*(.+)$", low)
                if m:
                    value = line.split(":", 1)[-1].strip(" :-")
                    if value:
                        out.append(value)
                        if i + 1 < len(lines) and self._is_city_state(lines[i + 1]):
                            out.append(value + ", " + lines[i + 1])
                elif low.strip(" :-") == lbl and i + 1 < len(lines):
                    out.append(lines[i + 1])
                    if i + 2 < len(lines) and self._is_city_state(lines[i + 2]):
                        out.append(lines[i + 1] + ", " + lines[i + 2])
        return out

    def _from_microdata(self, container):
        out = []
        for el in container.find_all(True):
            for attr in self.DATA_ATTRS:
                v = el.get(attr)
                if v and isinstance(v, str) and len(v) > 4:
                    out.append(v)
        return out

    def _from_lines(self, container):
        out = []
        lines = [l.strip() for l in container.get_text("\n", strip=True).splitlines()
                 if l.strip()]
        for i, line in enumerate(lines):
            if not self._is_street_line(line):
                continue
            if i + 1 < len(lines) and self._is_city_state(lines[i + 1]):
                out.append(f"{line}, {lines[i + 1]}")
                continue
            out.append(line)
        return out

    def _from_combined(self, container):
        out = []
        text = normalize_whitespace(container.get_text(" ", strip=True))
        for m in FULL_ADDR_RE.finditer(text):
            out.append(m.group(0))
        if not out:
            for m in STREET_ONLY_RE.finditer(text):
                out.append(m.group(0))
        return out

    def _from_siblings(self, container):
        out = []
        for el in container.find_all(True):
            txt = el.get_text(" ", strip=True)
            if not txt or not self._is_street_line(txt):
                continue
            nxt = el.find_next_sibling()
            if nxt:
                nxt_txt = nxt.get_text(" ", strip=True)
                if self._is_city_state(nxt_txt):
                    out.append(f"{txt}, {nxt_txt}")
        return out

    @staticmethod
    def _is_street_line(line):
        if not line or not (5 <= len(line) <= 200):
            return False
        if not re.match(r"^\s*\d{1,6}", line):
            return False
        if _find_all_phones_in_text(line):
            return False
        if re.match(r"^\d{4}-\d{2}-\d{2}", line):
            return False
        if re.match(r"^\d{5}-\d{4}$", line) or re.match(r"^\d{3}-\d{2}-\d{4}$", line):
            return False
        return bool(STREET_ONLY_RE.search(line))

    @staticmethod
    def _is_city_state(line):
        if not line or len(line) > 80:
            return False
        line = line.strip()
        m = CITY_STATE_ZIP_RE.match(line) or CITY_STATE_RE.match(line)
        if not m:
            return False
        return m.group(2).upper() in US_STATE_ABBREVS

    @staticmethod
    def _is_section_label(line):
        low = line.lower().strip(" :-")
        for kw in AddressExtractor.PRIORITY_LABELS:
            if kw in low:
                return False
        section_keywords = [
            "previous address", "past address", "phone", "email", "age",
            "date of birth", "dob", "relatives", "family", "associates",
            "aliases", "aka", "name", "names", "education", "employment",
            "criminal", "court", "records", "background", "work",
        ]
        for kw in section_keywords:
            if low == kw or low.startswith(kw + ":") or low.startswith(kw + " "):
                return True
        if len(line) < 40 and (line.endswith(":") or line.isupper()):
            if any(kw in low for kw in ("address", "phone", "email", "age")):
                return True
        return False

    def _is_address_part(self, line):
        if not line or not (3 <= len(line) <= 200):
            return False
        if re.match(r"^\s*\d", line) and STREET_ONLY_RE.search(line):
            return True
        if self._is_city_state(line):
            return True
        if re.match(r"^[A-Z][A-Za-z.\s'\-]{2,40},\s*[A-Z]{2}\s*$", line):
            return True
        if re.search(r"\b\d{5}(?:-\d{4})?\b", line) and re.search(r",\s*[A-Z]{2}\b", line):
            return True
        if re.match(r"^\s*\d{1,6}\s", line) and re.search(rf"\b{_UNIT}\b", line, re.I):
            return True
        return False

    def _normalize(self, raw):
        if not raw:
            return ""
        s = normalize_whitespace(str(raw))
        s = strip_leading_address_junk(s)
        s = s.strip(" ,;.")
        s = re.sub(r"\s*,\s*", ", ", s)
        s = _uppercase_state_in_address(s)
        return s

    def _score(self, addr):
        s = 0
        if re.search(r"\b\d{5}(?:-\d{4})?\b", addr):
            s += self.SCORE_FULL_WITH_ZIP
        has_state = False
        m = re.search(r",\s*([A-Z]{2})\b", addr)
        if m and m.group(1) in US_STATE_ABBREVS:
            has_state = True
        if not has_state:
            for name in US_STATE_NAMES:
                if re.search(rf"\b{name}\b", addr, re.I):
                    has_state = True
                    break
        if has_state:
            s += self.SCORE_CITY_STATE
        if re.search(_ST_SUFFIXES, addr, re.I):
            s += self.SCORE_WITH_SUFFIX
        if re.search(rf"\b{_UNIT}\b", addr, re.I):
            s += self.SCORE_WITH_UNIT
        if re.search(rf"\b{_DIRECTIONAL}\b", addr):
            s += self.SCORE_WITH_DIRECTIONAL
        return s


# ══════════════════════════════════════════════════════════════════
# PERSON / CONTAINER / EXTRACTOR
# ══════════════════════════════════════════════════════════════════
EMAIL_RE = re.compile(r"\b[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}\b")
AGE_RE   = re.compile(r"\bAge[:\s]*(\d{1,3})\b", re.I)

_ROW_CARD_CLASS_RE = re.compile(
    r"(?:^|\s)(?:row|card|person|resident|result|record|listing|entry)(?:\s|$)",
    re.I,
)


def _find_unique_card_ancestor(el, max_levels=8, max_tags=400):
    cur = el
    best = None
    for _ in range(max_levels):
        parent = getattr(cur, "parent", None)
        if parent is None or parent.name in (None, "[document]", "html", "body"):
            break
        try:
            tags = len(parent.find_all(True))
        except Exception:
            break
        if tags > max_tags:
            break
        try:
            addr_count = 0
            for sel in ADDRESS_PRIORITY_SELECTORS:
                addr_count += len(parent.select(sel))
        except Exception:
            break
        if addr_count == 0:
            cur = parent
            continue
        if addr_count > 2:
            return None
        if _count_person_names(parent) <= 1:
            best = parent
        cur = parent
    return best


def find_person_containers(soup):
    known = [
        "div.person-card", "div.person", "div.resident",
        "div.result-item", "div.result", "div.record",
        "li.result", "li.person", "tr.person-row",
        "article.person", "section.person",
        "div.row.result", "div.row.person", "div.row.record",
        "div.row[class*='result']", "div.row[class*='person']",
    ]
    for sel in known:
        found = soup.select(sel)
        if found:
            return found

    generic = soup.find_all(
        lambda tag: tag.name in ("div", "li", "tr", "article", "section")
        and tag.get("class")
        and any(kw in c.lower() for c in tag.get("class")
                for kw in ("person", "resident", "result", "record"))
    )
    if generic:
        ids = {id(t) for t in generic}
        filtered = [t for t in generic
                    if not any(id(p) in ids for p in t.parents)]
        return filtered or generic

    addr_els = []
    for sel in ADDRESS_PRIORITY_SELECTORS:
        try:
            addr_els.extend(soup.select(sel))
        except Exception:
            continue
    if addr_els:
        cards, seen = [], set()
        for el in addr_els:
            card = _find_unique_card_ancestor(el)
            if card is not None and id(card) not in seen:
                seen.add(id(card))
                cards.append(card)
        if cards:
            return cards

    name_headings = []
    for h in soup.find_all(["h1", "h2", "h3", "h4"]):
        txt = strip_age_from_name(normalize_whitespace(h.get_text(" ", strip=True)))
        if looks_like_real_name(txt):
            name_headings.append(h)

    parents, seen_ids = [], set()
    for h in name_headings:
        p = h.parent
        for _ in range(5):
            if p is None:
                break
            if len(p.find_all(True, recursive=True)) >= 4:
                break
            p = p.parent
        if p is not None and id(p) not in seen_ids:
            seen_ids.add(id(p))
            parents.append(p)
    return parents


class SmartExtractor:
    FIELD_SELECTORS = {
        "Name": ["h1.person-name", "h2.person-name", "h3.person-name",
                 "span.name", "div.name", "a.name", "h1", "h2", "h3", "h4"],
        "Aliases": ["span.aliases", "div.aliases", "div[class*='alias']",
                    "span[class*='aka']", "div[class*='aka']"],
        "Age": ["span.age", "div.age", "span[data-age]",
                "span[class*='age']", "div[class*='age']"],
        "Email": ["a[href^='mailto:']", "span.email", "div.email",
                  "span[class*='email']"],
        "Previous Addresses": [
            "div.previous-addresses", "ul.previous-addresses",
            "div.previous-address", "ul.previous-address",
            "li[class*='previous']", "p[class*='previous']",
            "div[class*='previous-address']", "ul[class*='previous-address']",
            "div[class*='previous']", "ul[class*='previous']",
        ],
        "Relatives": ["div.relatives", "ul.relatives", "span.relatives",
                      "div[class*='relative']", "ul[class*='relative']"],
    }
    LABELS = {
        "Age": ["age"],
        "Email": ["email", "e-mail"],
        "Previous Addresses": ["previous address", "previous addresses",
                               "past address", "past addresses"],
        "Relatives": ["relatives", "associated", "family", "related to"],
        "Aliases": ["aka", "aliases", "also known as", "other names"],
    }
    JUNK_HEADERS = {
        "aliases and aka's", "aliases and akas", "aliases", "aka's", "akas",
        "also known as", "other names",
        "previous addresses", "previous address", "past addresses",
        "past address",
        "phone numbers", "phone number", "phone",
        "email addresses", "email address", "email",
        "relatives", "associated", "associated persons",
        "background report", "summary", "current address", "current addresses",
        "location", "locations",
        "work", "employment", "education",
        "criminal records", "court records", "records",
        "name", "names",
        "age", "date of birth", "dob",
    }
    _DERIVED_FIELDS = {"Source URL", "Name", "Address", "City", "State", "ZIP"}

    def __init__(self):
        self.phone_extractor = PhoneExtractor()
        self.address_extractor = AddressExtractor()

    def extract(self, container, source_url, full_page_text="",
                use_page_fallback=False):
        rec = {col: "" for col in EXPORT_COLUMNS}
        rec["Source URL"] = source_url
        rec["Name"] = self._extract_name(container)
        if not rec["Name"] or not looks_like_real_name(rec["Name"]) \
                or is_blocked_name(rec["Name"]):
            return {col: "" for col in EXPORT_COLUMNS}

        rec["Address"] = self.address_extractor.extract(container)
        if not rec["Address"]:
            card = _find_unique_card_ancestor(container)
            if card is not None and card is not container:
                rec["Address"] = self.address_extractor.extract(card)
        if not rec["Address"] and use_page_fallback and full_page_text:
            rec["Address"] = self.address_extractor.extract_from_page_text(
                full_page_text, rec["Name"]
            )
        if rec["Address"]:
            parts = split_address(rec["Address"])
            rec["City"], rec["State"], rec["ZIP"] = (
                parts["city"], parts["state"], parts["zip"]
            )

        for field in EXPORT_COLUMNS:
            if field in self._DERIVED_FIELDS or field.startswith("Phone"):
                continue
            rec[field] = self._extract_field(container, field)

        phones = self.phone_extractor.extract_from_container(
            container, rec["Name"], full_page_text
        )
        if phones:
            rec["Phone"] = phones[0]
        if len(phones) > 1:
            rec["Phone 2"] = phones[1]
        if len(phones) > 2:
            rec["Phone 3"] = phones[2]
        return rec

    def _extract_name(self, container):
        for sel in self.FIELD_SELECTORS["Name"]:
            try:
                el = container.select_one(sel)
            except Exception:
                el = None
            if not el:
                continue
            raw = normalize_whitespace(el.get_text(" ", strip=True))
            txt = strip_age_from_name(raw)
            if not txt or re.match(r"^\d", txt) or "@" in txt:
                continue
            if _find_all_phones_in_text(txt) or STREET_ONLY_RE.search(txt):
                continue
            if is_blocked_name(txt):
                continue
            return txt
        return ""

    def _extract_field(self, container, field):
        text_all = normalize_whitespace(container.get_text(" ", strip=True))
        v = self._by_selector(container, field)
        if v:
            return self._finalize(field, v)
        v = self._by_label(container, field)
        if v:
            return self._finalize(field, v)
        v = self._by_regex(field, text_all)
        if v:
            return self._finalize(field, v)
        return ""

    def _by_selector(self, container, field):
        for sel in self.FIELD_SELECTORS.get(field, []):
            try:
                els = container.select(sel)
            except Exception:
                continue
            for el in els:
                if field == "Previous Addresses":
                    txt = el.get_text("\n", strip=True)
                else:
                    txt = normalize_whitespace(el.get_text(" ", strip=True))
                if not txt:
                    href = el.get("href", "")
                    if field == "Email" and href.startswith("mailto:"):
                        return href[7:]
                    continue
                if field == "Email":
                    m = EMAIL_RE.search(txt)
                    if m:
                        return m.group(0)
                    continue
                return txt
        return ""

    def _by_label(self, container, field):
        labels = self.LABELS.get(field, [])
        if not labels:
            return ""
        lines = [normalize_whitespace(l) for l in
                 container.get_text("\n", strip=True).splitlines() if l.strip()]
        for i, line in enumerate(lines):
            low = line.lower()
            for lbl in labels:
                m = re.match(rf"^\s*{re.escape(lbl)}\s*[:\-]\s*(.+)$", low)
                if m:
                    value = line.split(":", 1)[-1].strip(" :-")
                    if value and value.lower() not in self.JUNK_HEADERS:
                        return value
                if low.strip(" :-") == lbl and i + 1 < len(lines):
                    next_line = lines[i + 1].strip()
                    if next_line.lower() not in self.JUNK_HEADERS:
                        return next_line
        return ""

    def _by_regex(self, field, text):
        if field == "Email":
            m = EMAIL_RE.search(text)
            return m.group(0) if m else ""
        if field == "Age":
            m = AGE_RE.search(text)
            return m.group(1) if m else ""
        return ""

    def _finalize(self, field, value):
        value = normalize_whitespace(value)
        if field == "Age":
            return normalize_age(value)
        if field in ("Aliases", "Relatives", "Previous Addresses"):
            parts = re.split(r"[;,\n•·|]", value)
            seen, clean = set(), []
            for p in parts:
                p = normalize_whitespace(p)
                if not p or p.lower() in self.JUNK_HEADERS:
                    continue
                if field == "Previous Addresses":
                    if not re.search(r"\d", p) or len(p) < 10:
                        continue
                    if not (STREET_ONLY_RE.search(p) or FULL_ADDR_RE.search(p)):
                        if not re.search(r",\s*[A-Z]{2}\b", p):
                            continue
                if p.lower() not in seen:
                    seen.add(p.lower())
                    clean.append(p)
            return "; ".join(clean)
        return value


# ── JSON-LD + validation + merge helpers ──────────────────────────
def extract_json_ld(soup):
    records = []
    for script in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(script.string or "")
        except Exception:
            continue
        items = data if isinstance(data, list) else [data]
        for item in items:
            if not isinstance(item, dict):
                continue
            t = str(item.get("@type", "")).lower()
            if "person" not in t and "profile" not in t:
                continue
            rec = {c: "" for c in EXPORT_COLUMNS}
            rec["Name"] = strip_age_from_name(
                normalize_whitespace(item.get("name", ""))
            )
            if not rec["Name"] or is_blocked_name(rec["Name"]):
                continue
            rec["Age"] = normalize_age(item.get("age", ""))
            rec["Email"] = normalize_whitespace(item.get("email", ""))
            tel = item.get("telephone", "")
            if tel:
                phones = _find_all_phones_in_text(str(tel))
                if phones:
                    rec["Phone"] = phones[0]
            addr = item.get("address")
            if isinstance(addr, dict):
                parts = [addr.get("streetAddress", ""),
                         addr.get("addressLocality", ""),
                         addr.get("addressRegion", ""),
                         addr.get("postalCode", "")]
                rec["Address"] = ", ".join(p for p in parts if p)
                rec["City"]  = normalize_whitespace(addr.get("addressLocality", ""))
                rec["State"] = normalize_whitespace(addr.get("addressRegion", "")).upper()
                rec["ZIP"]   = normalize_whitespace(addr.get("postalCode", ""))
            elif isinstance(addr, str):
                rec["Address"] = addr
                parts = split_address(addr)
                rec["City"], rec["State"], rec["ZIP"] = (
                    parts["city"], parts["state"], parts["zip"]
                )
            aliases = item.get("alternateName") or item.get("additionalName") or []
            if isinstance(aliases, list):
                rec["Aliases"] = "; ".join(str(a) for a in aliases if a)
            elif isinstance(aliases, str):
                rec["Aliases"] = aliases
            records.append(rec)
    return records


def validate_record(rec) -> bool:
    name = rec.get("Name", "")
    if not name or is_blocked_name(name) or not looks_like_real_name(name):
        return False
    fields = ["Phone", "Address", "Age", "Relatives",
              "Previous Addresses", "Email", "Aliases"]
    return any(rec.get(f) for f in fields)


def name_key(rec) -> str:
    return re.sub(r"[^a-z]", "",
                  strip_age_from_name(rec.get("Name", "")).lower())


def addr_key(rec) -> str:
    return re.sub(r"[^a-z0-9]", "",
                  normalize_whitespace(rec.get("Address", "")).lower())


def merge_phone_fields(old, new):
    existing = [old.get("Phone", ""), old.get("Phone 2", ""), old.get("Phone 3", "")]
    existing = [p for p in existing if p]
    for slot in ("Phone", "Phone 2", "Phone 3"):
        p = new.get(slot, "")
        if p and p not in existing:
            existing.append(p)
    for i, slot in enumerate(("Phone", "Phone 2", "Phone 3")):
        old[slot] = existing[i] if i < len(existing) else ""
    return old


# ══════════════════════════════════════════════════════════════════
# GOOGLE SHEETS
# ══════════════════════════════════════════════════════════════════
class SheetsExporter:
    def __init__(self, service_file, spreadsheet_name, worksheet_name):
        self.sheet = None
        self._cached_last_row = None
        try:
            scopes = [
                "https://www.googleapis.com/auth/spreadsheets",
                "https://www.googleapis.com/auth/drive",
            ]
            creds = Credentials.from_service_account_file(service_file, scopes=scopes)
            client = gspread.authorize(creds)
            self.sheet = client.open(spreadsheet_name).worksheet(worksheet_name)
            if not self.sheet.row_values(1):
                self.sheet.append_row(EXPORT_COLUMNS)
            print("[Sheets] Ready.")
        except Exception as e:
            print(f"[Sheets] Auth error: {e}")

    def _last_data_row(self):
        if self._cached_last_row is not None:
            return self._cached_last_row
        try:
            existing = self.sheet.get_all_values()
        except Exception:
            existing = []
        last = 0
        for i, row in enumerate(existing):
            if any(str(cell).strip() for cell in row):
                last = i + 1
        self._cached_last_row = last
        return last

    def invalidate_cache(self):
        self._cached_last_row = None

    def append_records(self, records) -> int:
        if not self.sheet:
            raise RuntimeError("Google Sheets not connected.")
        rows = [[str(r.get(c, "")) for c in EXPORT_COLUMNS] for r in records]
        if not rows:
            return 0
        start_row = self._last_data_row() + 1
        needed = start_row + len(rows) - 1
        try:
            if self.sheet.row_count < needed:
                self.sheet.add_rows(needed - self.sheet.row_count)
        except Exception:
            pass
        last_col = col_letter(len(EXPORT_COLUMNS))
        CHUNK = 500
        written = 0
        for i in range(0, len(rows), CHUNK):
            chunk = rows[i:i + CHUNK]
            end_row = start_row + len(chunk) - 1
            rng = f"A{start_row}:{last_col}{end_row}"
            for attempt in range(4):
                try:
                    self.sheet.update(range_name=rng, values=chunk,
                                      value_input_option="RAW")
                    break
                except Exception:
                    if attempt == 3:
                        raise
                    time.sleep(2 ** attempt)
            written += len(chunk)
            start_row = end_row + 1
        self._cached_last_row = start_row - 1
        return written


# ══════════════════════════════════════════════════════════════════
# STEALTH BROWSER
# ══════════════════════════════════════════════════════════════════
_ADDRESS_POLL_SCRIPT = """
const sels = arguments[0];
let total = 0, empty = 0;
for (const s of sels) {
  let els;
  try { els = document.querySelectorAll(s); } catch (e) { continue; }
  for (const el of els) {
    if (el.offsetParent === null) continue;
    total++;
    if (!el.innerText.trim()) empty++;
  }
}
return [total, empty];
"""


class StealthBrowser:
    def __init__(self, proxy_string=None, headless=False, fast_mode=True):
        self.proxy_string = proxy_string
        self.headless = headless
        self.driver = None
        self.lock = threading.Lock()
        self.last_navigation_time = 0.0
        self.extractor = SmartExtractor()
        self._forwarder = None
        self._timing = TimingBox(fast_mode)

    def set_fast_mode(self, fast: bool):
        self._timing.set_fast(fast)

    @property
    def timing(self):
        return self._timing.get()

    # ── Proxy plumbing ────────────────────────────────────────────
    def set_proxy(self, proxy_string) -> bool:
        new_val = (proxy_string or "").strip() or None
        changed = (new_val != self.proxy_string)
        self.proxy_string = new_val
        if changed:
            self._stop_forwarder()
            if self.driver:
                try:
                    self.driver.quit()
                except Exception:
                    pass
                self.driver = None
        return changed

    def _stop_forwarder(self):
        if self._forwarder is not None:
            try:
                self._forwarder.stop()
            except Exception:
                pass
            self._forwarder = None

    @staticmethod
    def _string_has_credentials(s):
        if not s:
            return False
        rest = s.split("://", 1)[1] if "://" in s else s
        return "@" in rest

    def _ensure_forwarder(self):
        if not self.proxy_string or not self._string_has_credentials(self.proxy_string):
            return None
        if self._forwarder is not None:
            return self._forwarder.local_url
        fwd = LocalProxyForwarder(self.proxy_string)
        if not fwd.has_credentials():
            return None
        try:
            url = fwd.start()
        except Exception as e:
            print(f"[Forwarder] Failed to start: {e}")
            return None
        self._forwarder = fwd
        print(f"[Forwarder] Local proxy {url} → "
              f"{fwd.upstream_host}:{fwd.upstream_port} (user: {fwd.username})")
        return url

    def _proxy_arg_for_chrome(self):
        if not self.proxy_string:
            return None
        fwd_url = self._ensure_forwarder()
        if fwd_url:
            return fwd_url
        if self._string_has_credentials(self.proxy_string):
            return None
        return self.proxy_string

    # ── Options ───────────────────────────────────────────────────
    def _build_options(self):
        opts = uc.ChromeOptions()
        try:
            opts.page_load_strategy = "eager"
        except Exception:
            opts.set_capability("pageLoadStrategy", "eager")

        prefs = {
            "profile.managed_default_content_settings.images": 2,
            "profile.managed_default_content_settings.plugins": 2,
            "profile.managed_default_content_settings.popups": 2,
            "profile.managed_default_content_settings.geolocation": 2,
            "profile.managed_default_content_settings.media_stream": 2,
            "profile.default_content_setting_values.notifications": 2,
            "profile.managed_default_content_settings.background_sync": 2,
            "credentials_enable_service": False,
            "profile.password_manager_enabled": False,
        }
        try:
            opts.add_experimental_option("prefs", prefs)
        except Exception:
            pass

        proxy_arg = self._proxy_arg_for_chrome()
        if proxy_arg:
            opts.add_argument(f"--proxy-server={proxy_arg}")
        if self.headless:
            opts.add_argument("--headless=new")

        for a in (
            "--no-sandbox",
            "--disable-dev-shm-usage",
            "--disable-blink-features=AutomationControlled",
            "--disable-gpu",
            "--window-size=1366,900",
            "--lang=en-US",
            "--disable-background-networking",
            "--disable-background-timer-throttling",
            "--disable-backgrounding-occluded-windows",
            "--disable-renderer-backgrounding",
            "--disable-features=Translate,BackForwardCache,"
            "AcceptCHFrame,MediaRouter,OptimizationHints",
            "--no-first-run",
            "--no-default-browser-check",
            "--disable-sync",
            "--disable-extensions",
            "--disable-component-update",
            "--disable-default-apps",
            "--metrics-recording-only",
            "--mute-audio",
        ):
            opts.add_argument(a)
        return opts

    def start(self):
        if CHROME_MAJOR_VERSION:
            try:
                self.driver = uc.Chrome(
                    options=self._build_options(),
                    version_main=CHROME_MAJOR_VERSION,
                )
                try:
                    self.driver.maximize_window()
                except Exception:
                    pass
                return
            except Exception as e:
                print(f"[Browser] Pinned version {CHROME_MAJOR_VERSION} failed: {e}")
                print("[Browser] Retrying with autodetected version…")
        self.driver = uc.Chrome(options=self._build_options())
        try:
            self.driver.maximize_window()
        except Exception:
            pass

    # ── Navigation with retry + backoff ──────────────────────────
    def _safe_get(self, url, log=None, max_retries=NAV_MAX_RETRIES):
        timing = self.timing
        last_err = None
        for attempt in range(1, max_retries + 1):
            elapsed = time.time() - self.last_navigation_time
            if elapsed < timing.min_delay_between_lookups:
                time.sleep(timing.min_delay_between_lookups - elapsed)
            msg = f"→ {url}" + (f"  (attempt {attempt})" if attempt > 1 else "")
            (log or print)(msg)
            try:
                self.driver.get(url)
                self.last_navigation_time = time.time()
                self._wait_for_challenge()
                return
            except RuntimeError as e:
                last_err = e
                if attempt == max_retries:
                    break
                backoff = (2 ** (attempt - 1)) + random.uniform(0, 1.5)
                (log or print)(f"⚠ Navigation failed: {e} — retrying in "
                               f"{backoff:.1f}s")
                time.sleep(backoff)
            except Exception as e:
                last_err = e
                if attempt == max_retries:
                    break
                backoff = (2 ** (attempt - 1)) + random.uniform(0, 1.5)
                (log or print)(f"⚠ Nav error: {type(e).__name__}: {e} — "
                               f"retrying in {backoff:.1f}s")
                time.sleep(backoff)
        raise last_err if last_err else RuntimeError("Navigation failed")

    def _wait_for_challenge(self, timeout=45):
        timing = self.timing
        deadline = time.time() + timeout
        while time.time() < deadline:
            time.sleep(timing.challenge_poll)
            try:
                html = self.driver.page_source
            except Exception:
                continue
            if "Sorry, you have been blocked" in html:
                raise RuntimeError("Cloudflare blocked your IP.")
            low = html.lower()
            if "just a moment" not in low and "checking your browser" not in low:
                return True
        return False

    def _wait_for_results(self, timeout=15):
        timing = self.timing
        selectors = [
            "div.person-card", "div.person", "div.resident",
            "div.result-item", "div.result", "div.record",
            "li.result", "li.person", "tr.person-row",
            "div[class*='person']", "div[class*='resident']",
            "div[class*='result']",
            "div.row.result", "div.row.person",
        ]
        end = time.time() + timeout
        while time.time() < end:
            for sel in selectors:
                try:
                    if self.driver.find_elements(By.CSS_SELECTOR, sel):
                        return True
                except Exception:
                    continue
            time.sleep(timing.results_poll)
        return False

    # ── Single-RPC address poll ──────────────────────────────────
    def _wait_for_address_population(self, timeout=None, log=None):
        timing = self.timing
        if timeout is None:
            timeout = ADDRESS_WAIT_TIMEOUT
        end = time.time() + timeout
        last_total = -1
        total = empty = 0
        while time.time() < end:
            try:
                total, empty = self.driver.execute_script(
                    _ADDRESS_POLL_SCRIPT, ADDRESS_PRIORITY_SELECTORS
                )
            except Exception:
                time.sleep(timing.address_wait_poll)
                continue
            if total == 0:
                return True
            if empty == 0:
                if log and total != last_total:
                    log(f"Address columns populated ({total} found).")
                return True
            last_total = total
            time.sleep(timing.address_wait_poll)
        if log:
            log(f"⚠ Address population timed out ({empty}/{total} still empty).")
        return False

    def navigate(self, url):
        with self.lock:
            if not self.driver:
                self.start()
            self._safe_get(url)
            self._wait_for_results(timeout=15)
            self._wait_for_address_population()
            time.sleep(self.timing.post_nav_settle)

            # ── PATCH 1: surface where the browser actually ended up ──
            try:
                final_url = (self.driver.current_url or "").rstrip("/")
            except Exception:
                final_url = ""
            if final_url and final_url != url.rstrip("/"):
                print(f"[Nav] Redirected: {url}  →  {final_url}")
                if hasattr(self, "_nav_redirect_log") and self._nav_redirect_log:
                    try:
                        self._nav_redirect_log(
                            f"⚠ Site redirected to: {final_url}"
                        )
                    except Exception:
                        pass

    def set_nav_redirect_logger(self, fn):
        """Optional: hook used by the GUI to route redirect notices."""
        self._nav_redirect_log = fn

    # ── Proxy test ────────────────────────────────────────────────
    def test_proxy_with_browser(self, test_url, timeout=25):
        try:
            if not self.driver:
                self.start()
            self.driver.set_page_load_timeout(timeout)
            self.driver.get(test_url)
            time.sleep(2)
            html = self.driver.page_source or ""
            low = html.lower()
            if "sorry, you have been blocked" in low:
                return False, "Cloudflare blocked this proxy IP (browser test)."
            if "just a moment" in low or "checking your browser" in low:
                return False, "Cloudflare challenge page (browser test)."
            if len(html) < 2000:
                return False, f"Page too small ({len(html)} bytes)."
            return True, f"OK — {len(html):,} bytes loaded in browser."
        except Exception as e:
            return False, f"Browser test error: {type(e).__name__}: {e}"
        finally:
            try:
                self.driver.set_page_load_timeout(300)
            except Exception:
                pass

    # ── Debug dump ────────────────────────────────────────────────
    def debug_dump(self, out_path="debug_page.html", log=None):
        with self.lock:
            if not self.driver:
                raise RuntimeError("Browser not running.")
            html = self.driver.page_source
            with open(out_path, "w", encoding="utf-8") as f:
                f.write(html)
            if log:
                log(f"Saved page HTML to {os.path.abspath(out_path)} "
                    f"({len(html):,} bytes)")

            soup = BeautifulSoup(html, _BS_PARSER)
            containers = find_person_containers(soup)
            if log:
                log(f"Container detector found {len(containers)} containers.")
                log(f"Priority-selector hits: "
                    f"{len(soup.select(','.join(ADDRESS_PRIORITY_SELECTORS)))}")

            for i, c in enumerate(containers[:5]):
                try:
                    preview = normalize_whitespace(c.get_text(" ", strip=True))[:200]
                except Exception:
                    preview = "(unreadable)"
                if log:
                    log(f"--- container #{i+1} preview: {preview}")
                rec = self.extractor.extract(c, "(debug)")
                if log:
                    log(f"    Name='{rec.get('Name','')}'  "
                        f"Addr='{rec.get('Address','')}'  "
                        f"City='{rec.get('City','')}'  "
                        f"State='{rec.get('State','')}'  "
                        f"ZIP='{rec.get('ZIP','')}'")
        return out_path

    # ── In-page interactions ─────────────────────────────────────
    def _click_phone_reveals(self, log=None):
        timing = self.timing
        reveal_xpaths = [
            "//button[contains(translate(.,'SHOW PHONE','show phone'),'show phone')]",
            "//button[contains(translate(.,'REVEAL','reveal'),'reveal')]",
            "//button[contains(translate(.,'VIEW NUMBER','view number'),'view number')]",
            "//button[contains(translate(.,'VIEW PHONE','view phone'),'view phone')]",
            "//button[contains(translate(.,'GET PHONE','get phone'),'get phone')]",
            "//a[contains(translate(.,'SHOW PHONE','show phone'),'show phone')]",
            "//a[contains(translate(.,'REVEAL','reveal'),'reveal')]",
            "//a[contains(translate(.,'VIEW NUMBER','view number'),'view number')]",
            "//a[contains(translate(.,'VIEW PHONE','view phone'),'view phone')]",
            "//span[contains(translate(.,'SHOW PHONE','show phone'),'show phone')]",
            "//*[contains(@class,'show-phone') or contains(@class,'showphone')]",
            "//*[contains(@class,'reveal-phone') or contains(@class,'revealphone')]",
            "//*[contains(@class,'view-phone') or contains(@class,'viewphone')]",
            "//*[contains(@class,'phone-reveal') or contains(@class,'phonereveal')]",
            "//*[contains(@class,'reveal-number')]",
            "//*[contains(@class,'show-number')]",
            "//*[contains(@aria-label,'phone') or contains(@aria-label,'Phone')]",
        ]
        clicked_total = 0
        for round_num in range(timing.reveal_rounds):
            clicked_this_round = 0
            for xp in reveal_xpaths:
                try:
                    btns = self.driver.find_elements(By.XPATH, xp)
                except Exception:
                    continue
                for b in btns:
                    try:
                        if not b.is_displayed() or not b.is_enabled():
                            continue
                        txt = (b.text or "").strip().lower()
                        if txt in ("call now", "contact us", "call us"):
                            continue
                        self.driver.execute_script(
                            "arguments[0].scrollIntoView({block:'center'});", b
                        )
                        time.sleep(timing.reveal_pre_click)
                        self.driver.execute_script("arguments[0].click();", b)
                        clicked_this_round += 1
                        clicked_total += 1
                        time.sleep(timing.reveal_post_click)
                    except Exception:
                        continue
            if clicked_this_round == 0:
                break
            if log:
                log(f"Revealed {clicked_this_round} phone button(s) "
                    f"(round {round_num+1})")
        if log and clicked_total:
            log(f"Total phone reveals clicked: {clicked_total}")
        return clicked_total

    def _auto_scroll_and_load(self, log=None):
        timing = self.timing
        if log:
            log("Scrolling to load lazy content…")
        last_height = 0
        stable = 0
        for _ in range(timing.scroll_max_iter):
            self.driver.execute_script(
                "window.scrollTo(0, document.body.scrollHeight);"
            )
            time.sleep(timing.scroll_pause)
            try:
                new_height = self.driver.execute_script(
                    "return document.body.scrollHeight"
                )
            except Exception:
                break
            if new_height == last_height:
                stable += 1
                if stable >= 2:
                    break
            else:
                stable = 0
            last_height = new_height

        xpaths = [
            "//button[contains(translate(.,'LOAD MORE','load more'),'load more')]",
            "//button[contains(translate(.,'SHOW MORE','show more'),'show more')]",
            "//a[contains(translate(.,'LOAD MORE','load more'),'load more')]",
            "//a[contains(translate(.,'SHOW MORE','show more'),'show more')]",
            "//*[contains(@class,'load-more') or contains(@class,'loadmore')]",
            "//*[contains(@class,'show-more') or contains(@class,'showmore')]",
        ]
        for i in range(timing.load_more_max_rounds):
            clicked = False
            for xp in xpaths:
                try:
                    btns = self.driver.find_elements(By.XPATH, xp)
                except Exception:
                    continue
                for b in btns:
                    try:
                        if not b.is_displayed() or not b.is_enabled():
                            continue
                        self.driver.execute_script(
                            "arguments[0].scrollIntoView({block:'center'});", b
                        )
                        time.sleep(timing.reveal_pre_click)
                        self.driver.execute_script("arguments[0].click();", b)
                        clicked = True
                        time.sleep(timing.load_more_post_click)
                    except Exception:
                        continue
            if not clicked:
                break
            if log:
                log(f"Clicked Load More (round {i+1})")

        self.driver.execute_script(
            "window.scrollTo(0, document.body.scrollHeight);"
        )
        time.sleep(timing.post_nav_settle)
        self._click_phone_reveals(log=log)
        self._wait_for_address_population(log=log)

    def _find_next_page(self):
        xpaths = [
            "//a[contains(@rel,'next')]",
            "//a[contains(@aria-label,'Next')]",
            "//a[contains(@class,'next')]",
            "//li[contains(@class,'next')]/a",
            "//a[contains(translate(.,'NEXT','next'),'next') and not(contains(.,'<'))]",
            "//a[@title='Next' or @title='next']",
        ]
        for xp in xpaths:
            try:
                els = self.driver.find_elements(By.XPATH, xp)
            except Exception:
                continue
            for el in els:
                try:
                    if not el.is_displayed() or not el.is_enabled():
                        continue
                    href = el.get_attribute("href")
                    if href and not href.startswith("javascript:"):
                        return href
                except Exception:
                    continue
        return None

    def _go_to_next_page(self, log=None):
        target = self._find_next_page()
        if not target:
            return False
        try:
            self._safe_get(target, log=log)
            self._wait_for_results(timeout=15)
            self._wait_for_address_population(log=log)
            time.sleep(self.timing.post_nav_settle)
            return True
        except Exception:
            return False

    def _collect_detail_links(self):
        link_xpaths = [
            "//div[contains(@class,'person')]//a[href]",
            "//div[contains(@class,'resident')]//a[href]",
            "//div[contains(@class,'result')]//a[href]",
            "//li[contains(@class,'result')]//a[href]",
            "//a[contains(@href,'/person/')]",
            "//a[contains(@href,'/name/')]",
            "//a[contains(@href,'/profile/')]",
        ]
        hrefs = []
        for xp in link_xpaths:
            try:
                els = self.driver.find_elements(By.XPATH, xp)
            except Exception:
                continue
            for el in els:
                try:
                    href = el.get_attribute("href")
                    if href and href not in hrefs:
                        hrefs.append(href)
                except Exception:
                    continue
        if not hrefs:
            for el in self.driver.find_elements(By.TAG_NAME, "a"):
                try:
                    txt = strip_age_from_name((el.text or "").strip())
                    if re.match(r"^[A-Z][a-zA-Z'\-]+(?:\s+[A-Z][a-zA-Z'\-]+){1,3}$", txt):
                        href = el.get_attribute("href")
                        if href:
                            hrefs.append(href)
                except Exception:
                    continue
        return hrefs

    # ── Parsing ───────────────────────────────────────────────────
    def _parse_detail_page(self, html, url):
        soup = BeautifulSoup(html, _BS_PARSER)
        records = extract_json_ld(soup)
        if records:
            for r in records:
                r["Source URL"] = url
            return [r for r in records if validate_record(r)]
        body = soup.body or soup
        full_text = normalize_whitespace(body.get_text(" ", strip=True))
        rec = self.extractor.extract(body, url, full_page_text=full_text,
                                     use_page_fallback=True)
        return [rec] if validate_record(rec) else []

    def _parse_listing(self, html, url, log=None):
        soup = BeautifulSoup(html, _BS_PARSER)
        full_page_text = normalize_whitespace(soup.get_text(" ", strip=True))

        ld_records = extract_json_ld(soup)
        if ld_records:
            for r in ld_records:
                r["Source URL"] = url
            return [r for r in ld_records if validate_record(r)]

        containers = find_person_containers(soup)
        print(f"[Parser] {len(containers)} person containers detected.")
        if log:
            log(f"Parser: {len(containers)} containers detected.")
        records = []
        empty_addr_count = 0
        for c in containers:
            rec = self.extractor.extract(c, url, full_page_text=full_page_text,
                                         use_page_fallback=False)
            if validate_record(rec):
                records.append(rec)
                if not rec.get("Address"):
                    empty_addr_count += 1
                    if log and empty_addr_count <= 3:
                        preview = normalize_whitespace(c.get_text(" ", strip=True))[:180]
                        log(f"⚠ No address for '{rec.get('Name','?')}' "
                            f"| preview: {preview}")
        if log and empty_addr_count:
            log(f"⚠ {empty_addr_count}/{len(records)} records missing address.")
        return records

    @staticmethod
    def _score_records(records):
        if not records:
            return -1
        with_addr = sum(1 for r in records if r.get("Address"))
        return with_addr * 1000 + len(records)

    def _parse_listing_with_retry(self, url, log=None):
        best_records, best_score = [], -1
        for attempt in range(1, ADDRESS_PARSE_RETRIES + 1):
            html = self.driver.page_source
            records = self._parse_listing(html, url, log=log)
            if not records:
                if log:
                    log(f"Parse attempt {attempt}: 0 records; retrying…")
                time.sleep(1.5)
                continue
            score = self._score_records(records)
            if score > best_score:
                best_score = score
                best_records = records
            missing = sum(1 for r in records if not r.get("Address"))
            if missing == 0:
                return records
            if log:
                log(f"Parse attempt {attempt}: {missing}/{len(records)} "
                    f"missing address – waiting & retrying…")
            self._wait_for_address_population(timeout=4, log=log)
            time.sleep(1.0)
            try:
                has_priority = bool(self.driver.find_elements(
                    By.CSS_SELECTOR, ADDRESS_PRIORITY_SELECTORS[0]
                ))
            except Exception:
                has_priority = False
            if not has_priority:
                break
        return best_records

    # ── Orchestration ─────────────────────────────────────────────
    def scrape_all_results(self, drill_details=False,
                           on_record=None, on_log=None,
                           should_stop=None):
        with self.lock:
            if not self.driver:
                return []
            base_url = self.driver.current_url

        all_records = []

        for page_num in range(1, MAX_PAGES + 1):
            if should_stop and should_stop():
                if on_log:
                    on_log("■ Stop requested – halting scrape.")
                break
            if on_log:
                on_log(f"═══ PAGE {page_num} ═══")

            with self.lock:
                self._auto_scroll_and_load(log=on_log)
            if should_stop and should_stop():
                if on_log:
                    on_log("■ Stop requested – halting scrape.")
                break

            if drill_details:
                with self.lock:
                    hrefs = self._collect_detail_links()
                if on_log:
                    on_log(f"Found {len(hrefs)} detail links.")
                if hrefs:
                    for i, href in enumerate(hrefs):
                        if should_stop and should_stop():
                            if on_log:
                                on_log("■ Stop requested – aborting drill loop.")
                            break
                        try:
                            with self.lock:
                                self._safe_get(href, log=on_log)
                                self._wait_for_address_population(timeout=8)
                                time.sleep(self.timing.detail_drill_delay)
                                self._click_phone_reveals(log=on_log)
                                html = self.driver.page_source
                            for r in self._parse_detail_page(html, href):
                                all_records.append(r)
                                if on_record:
                                    on_record(r, f"page {page_num} · drill {i+1}")
                        except Exception as e:
                            if on_log:
                                on_log(f"Skipped drill: {e}")
                    with self.lock:
                        try:
                            self._safe_get(base_url, log=on_log)
                            self._wait_for_results(timeout=15)
                            self._wait_for_address_population(log=on_log)
                            time.sleep(self.timing.post_nav_settle)
                        except Exception:
                            pass
                    continue

            with self.lock:
                page_records = self._parse_listing_with_retry(base_url, log=on_log)
            for r in page_records:
                all_records.append(r)
                if on_record:
                    on_record(r, f"page {page_num}")

            if should_stop and should_stop():
                if on_log:
                    on_log("■ Stop requested – halting scrape.")
                break

            with self.lock:
                advanced = self._go_to_next_page(log=on_log)
            if not advanced:
                if on_log:
                    on_log("No next page – done.")
                break

        if on_log:
            on_log(f"✔ Finished. {len(all_records)} records total.")
        return all_records

    def close(self):
        self._stop_forwarder()
        if self.driver:
            try:
                self.driver.quit()
            except Exception:
                pass
            self.driver = None


# ══════════════════════════════════════════════════════════════════
# GUI
# ══════════════════════════════════════════════════════════════════
class TreeviewTooltip:
    def __init__(self, tree):
        self.tree = tree
        self.tip = None
        self.last = (None, None)
        tree.bind("<Motion>", self._on_motion, add="+")
        tree.bind("<Leave>", lambda e: self._hide(), add="+")

    def _on_motion(self, event):
        row = self.tree.identify_row(event.y)
        col = self.tree.identify_column(event.x)
        if not row or not col:
            self._hide()
            return
        if (row, col) == self.last:
            return
        self.last = (row, col)
        try:
            idx = int(col.replace("#", "")) - 1
            values = self.tree.item(row, "values")
            if idx < 0 or idx >= len(values):
                self._hide()
                return
            text = str(values[idx])
        except Exception:
            self._hide()
            return
        if not text or text == "(none)" or len(text) < 12:
            self._hide()
            return
        self._show(event.x_root + 18, event.y_root + 18, text)

    def _show(self, x, y, text):
        self._hide()
        self.tip = tk.Toplevel(self.tree)
        self.tip.wm_overrideredirect(True)
        self.tip.wm_geometry(f"+{x}+{y}")
        tk.Label(
            self.tip, text=text, justify=tk.LEFT,
            background="#fffde7", foreground="#000000",
            relief=tk.SOLID, borderwidth=1,
            font=("Segoe UI", 9), wraplength=520,
            padx=6, pady=4,
        ).pack()

    def _hide(self):
        if self.tip is not None:
            try:
                self.tip.destroy()
            except Exception:
                pass
            self.tip = None
        self.last = (None, None)


_KNOWN_PREFIXES = (
    "https://www.cyberbackgroundchecks.com/address/",
    "http://www.cyberbackgroundchecks.com/address/",
    "www.cyberbackgroundchecks.com/address/",
    "/address/",
)


def normalize_address_input(text: str) -> str:
    if not text:
        return ""
    s = text.strip()
    for p in _KNOWN_PREFIXES:
        if s.lower().startswith(p.lower()):
            s = s[len(p):]
            break
    s = s.strip().strip("/")
    if not s:
        return ""
    if " " not in s and "," not in s:
        s = re.sub(r"-+", "-", s)
        s = re.sub(r"/+", "/", s)
        return s.strip("/-")
    s = s.replace(",", "/")
    parts = [re.sub(r"\s+", "-", p.strip()) for p in s.split("/") if p.strip()]
    s = "/".join(parts)
    s = re.sub(r"-+", "-", s)
    s = re.sub(r"/+", "/", s)
    return s.strip("/-")


class BrowserApp:
    _POLL_INTERVAL_MS = 100
    _POLL_BATCH       = 100

    def __init__(self, root):
        self.root = root
        root.title("Smart Stealth Scraper – Final (v6.7.1)")
        root.geometry("1400x900")

        self._cfg = load_config()
        proxy_enabled = self._cfg.get("proxy_enabled",
                                      RESIDENTIAL_PROXY is not None)
        proxy_string = self._cfg.get("proxy_string", RESIDENTIAL_PROXY or "")
        initial_proxy = proxy_string if proxy_enabled and proxy_string else None
        fast_default = self._cfg.get("fast_mode", True)

        self.browser = StealthBrowser(proxy_string=initial_proxy,
                                      headless=HEADLESS,
                                      fast_mode=fast_default)
        # Route redirect notices into the live log.
        try:
            self.browser.set_nav_redirect_logger(
                lambda msg: self._log(msg, "error")
            )
        except Exception:
            pass

        self.exporter = SheetsExporter(
            SERVICE_ACCOUNT_FILE, SPREADSHEET_NAME, WORKSHEET_NAME
        )

        self.collected_records = []
        self.row_index = {}
        self.pending_highlight_clear = {}
        self.new_count_this_run = 0
        self.updated_count_this_run = 0
        self.skipped_count_this_run = 0
        self.stop_event = threading.Event()
        self._worker_thread = None

        self._record_buffer = []
        self._record_buffer_lock = threading.Lock()
        self._log_buffer = []
        self._log_buffer_lock = threading.Lock()

        self._build_ui()
        self.root.after(self._POLL_INTERVAL_MS, self._poll_records)
        self.root.after(self._POLL_INTERVAL_MS, self._poll_logs)

    # ── UI construction ──────────────────────────────────────────
    def _build_ui(self):
        top = ttk.Frame(self.root, padding=6)
        top.pack(fill=tk.X)
        ttk.Label(top, text="Address:").pack(side=tk.LEFT, padx=(0, 5))
        ttk.Label(top, text=ADDRESS_PREFIX,
                  foreground="#666666").pack(side=tk.LEFT)

        self.url_slug_var = tk.StringVar(
            value="6031-ne-6th-ter/fort-lauderdale/fl"
        )
        self.url_entry = ttk.Entry(top, textvariable=self.url_slug_var, width=60)
        self.url_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))
        self.url_entry.bind("<Return>", lambda e: self.on_go())

        self.go_btn = ttk.Button(top, text="Go", command=self.on_go)
        self.go_btn.pack(side=tk.LEFT)

        proxy_row = ttk.Frame(self.root, padding=(6, 0, 6, 6))
        proxy_row.pack(fill=tk.X)

        self.proxy_enabled_var = tk.BooleanVar(
            value=bool(self._cfg.get("proxy_enabled",
                                     RESIDENTIAL_PROXY is not None))
        )
        self.proxy_entry_var = tk.StringVar(
            value=self._cfg.get("proxy_string", RESIDENTIAL_PROXY or "")
        )

        ttk.Checkbutton(
            proxy_row, text="Use Residential Proxy",
            variable=self.proxy_enabled_var, command=self._on_proxy_toggle,
        ).pack(side=tk.LEFT)

        self.proxy_entry = ttk.Entry(
            proxy_row, textvariable=self.proxy_entry_var, width=70
        )
        self.proxy_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(8, 5))

        self.save_proxy_btn = ttk.Button(
            proxy_row, text="Save", command=self.on_save_proxy
        )
        self.save_proxy_btn.pack(side=tk.LEFT)

        self.test_proxy_btn = ttk.Button(
            proxy_row, text="Test", command=self.on_test_proxy
        )
        self.test_proxy_btn.pack(side=tk.LEFT, padx=(4, 0))

        self.fast_mode_var = tk.BooleanVar(value=self._cfg.get("fast_mode", True))
        ttk.Checkbutton(
            proxy_row, text="Fast mode",
            variable=self.fast_mode_var, command=self._on_fast_mode_toggle,
        ).pack(side=tk.LEFT, padx=(12, 0))

        self.proxy_status_var = tk.StringVar(value="")
        ttk.Label(proxy_row, textvariable=self.proxy_status_var,
                  foreground="green").pack(side=tk.LEFT, padx=(10, 0))

        self._on_proxy_toggle()

        ctrl = ttk.Frame(self.root, padding=6)
        ctrl.pack(fill=tk.X)

        self.drill_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(ctrl, text="Drill into detail pages",
                        variable=self.drill_var).pack(side=tk.LEFT, padx=(0, 8))

        self.scrape_btn = ttk.Button(ctrl, text="Scrape ALL Results",
                                     command=self.on_scrape)
        self.scrape_btn.pack(side=tk.LEFT, padx=2)

        self.stop_btn = ttk.Button(ctrl, text="■ Stop", command=self.on_stop)
        self.stop_btn.pack(side=tk.LEFT, padx=2)
        self.stop_btn.config(state=tk.DISABLED)

        self.debug_btn = ttk.Button(ctrl, text="Debug Page", command=self.on_debug)
        self.debug_btn.pack(side=tk.LEFT, padx=2)

        self.export_btn = ttk.Button(ctrl, text="Export to Sheets",
                                     command=self.on_export)
        self.export_btn.pack(side=tk.LEFT, padx=2)

        self.clear_btn = ttk.Button(ctrl, text="Clear Data", command=self.on_clear)
        self.clear_btn.pack(side=tk.LEFT, padx=2)

        self.status_var = tk.StringVar(value="Ready.")
        ttk.Label(ctrl, textvariable=self.status_var,
                  foreground="blue").pack(side=tk.RIGHT)

        nb = ttk.Notebook(self.root)
        nb.pack(fill=tk.BOTH, expand=True, padx=6, pady=(0, 6))

        results_frame = ttk.Frame(nb)
        nb.add(results_frame, text="Results (live)")

        table_container = ttk.Frame(results_frame)
        table_container.pack(fill=tk.BOTH, expand=True)

        hsb = ttk.Scrollbar(table_container, orient="horizontal")
        hsb.pack(side=tk.BOTTOM, fill=tk.X)
        vsb = ttk.Scrollbar(table_container, orient="vertical")
        vsb.pack(side=tk.RIGHT, fill=tk.Y)

        cols = EXPORT_COLUMNS[:-1]
        self.tree = ttk.Treeview(
            table_container, columns=cols, show="headings",
            height=22, xscrollcommand=hsb.set, yscrollcommand=vsb.set,
        )
        for col in cols:
            self.tree.heading(col, text=col)
            width = {
                "Address": 260, "Previous Addresses": 200,
                "Relatives": 200, "Aliases": 200, "Email": 180,
                "Name": 160, "City": 120, "State": 50, "ZIP": 80,
                "Age": 60,
            }.get(col)
            if width is None:
                width = 130 if col.startswith("Phone") else 120
            self.tree.column(col, width=width, anchor=tk.W, stretch=False)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        hsb.config(command=self.tree.xview)
        vsb.config(command=self.tree.yview)

        self.tree.tag_configure("new",     background="#d4f7d4")
        self.tree.tag_configure("updated", background="#fff5b3")
        self.tree.tag_configure("normal",  background="#ffffff")

        self.tooltip = TreeviewTooltip(self.tree)
        self.tree.bind("<ButtonRelease-1>", self._on_tree_click, add="+")

        log_frame = ttk.Frame(nb)
        nb.add(log_frame, text="Live log")

        self.log_text = tk.Text(log_frame, wrap=tk.WORD, height=20,
                                state=tk.DISABLED)
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        log_sb = ttk.Scrollbar(log_frame, orient=tk.VERTICAL,
                               command=self.log_text.yview)
        log_sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_text.configure(yscrollcommand=log_sb.set)
        self.log_text.tag_configure("info",    foreground="#333333")
        self.log_text.tag_configure("new",     foreground="#1a7f1a",
                                    font=("Consolas", 9, "bold"))
        self.log_text.tag_configure("updated", foreground="#a07400",
                                    font=("Consolas", 9, "bold"))
        self.log_text.tag_configure("error",   foreground="#c00000",
                                    font=("Consolas", 9, "bold"))
        self.log_text.tag_configure("phone",   foreground="#0070c0",
                                    font=("Consolas", 9, "bold"))
        self.log_text.tag_configure("address", foreground="#7030a0",
                                    font=("Consolas", 9, "bold"))
        self.log_text.tag_configure("skip",    foreground="#888888",
                                    font=("Consolas", 9, "italic"))
        self.log_text.tag_configure("debug",   foreground="#8a2be2",
                                    font=("Consolas", 9, "bold"))

        bottom = ttk.Frame(self.root, padding=6)
        bottom.pack(fill=tk.X)
        self.count_var = tk.StringVar(
            value="Records: 0  |  New this run: 0  |  Updated: 0  |  Skipped: 0"
        )
        ttk.Label(bottom, textvariable=self.count_var).pack(side=tk.LEFT)

    # ── Proxy / fast mode ────────────────────────────────────────
    def _on_proxy_toggle(self):
        state = tk.NORMAL if self.proxy_enabled_var.get() else tk.DISABLED
        self.proxy_entry.config(state=state)
        self.save_proxy_btn.config(state=state)
        self.test_proxy_btn.config(state=state)

    def _on_fast_mode_toggle(self):
        fast = bool(self.fast_mode_var.get())
        self.browser.set_fast_mode(fast)
        cfg = load_config()
        cfg["fast_mode"] = fast
        save_config(cfg)
        self._log(f"Fast mode {'ON' if fast else 'OFF'}.", "info")

    def on_save_proxy(self):
        enabled = bool(self.proxy_enabled_var.get())
        proxy = self.proxy_entry_var.get().strip()
        if proxy:
            proxy = normalize_proxy_url(proxy)
            self.proxy_entry_var.set(proxy)
        if enabled and not proxy:
            messagebox.showwarning(
                "Proxy", "Enable is checked but no proxy string was provided."
            )
            return
        cfg = load_config()
        cfg["proxy_enabled"] = enabled
        cfg["proxy_string"] = proxy
        if not save_config(cfg):
            messagebox.showerror("Proxy", "Failed to write config file.")
            return
        self.proxy_status_var.set("Saved ✓")
        self.root.after(2500, lambda: self.proxy_status_var.set(""))
        new_proxy = proxy if enabled else None
        changed = self.browser.set_proxy(new_proxy)
        if changed:
            self._log(
                f"Proxy {'enabled' if enabled else 'disabled'} – "
                f"browser will start fresh on next navigation.", "info"
            )
        else:
            self._log(
                f"Proxy config saved "
                f"({'enabled' if enabled else 'disabled'}).", "info"
            )

    def on_test_proxy(self):
        proxy = self.proxy_entry_var.get().strip()
        if not proxy:
            messagebox.showwarning("Proxy", "Please enter a proxy string first.")
            return
        proxy = normalize_proxy_url(proxy)
        self.proxy_entry_var.set(proxy)
        self.browser.set_proxy(proxy)
        self.proxy_status_var.set("Testing…")
        self._log(f"▶ Browser-testing proxy: {redact_proxy(proxy)}")
        threading.Thread(target=self._test_proxy_worker_browser,
                         args=(proxy,), daemon=True).start()

    def _test_proxy_worker_browser(self, proxy):
        ok, msg = self.browser.test_proxy_with_browser(
            ADDRESS_PREFIX + "6031-ne-6th-ter/fort-lauderdale/fl"
        )
        self.root.after(0, lambda: self._test_proxy_done(ok, msg))

    def _test_proxy_done(self, ok, msg):
        if ok:
            self.proxy_status_var.set("✓ " + msg)
            self._log(f"✔ Proxy test passed: {msg}", "new")
        else:
            self.proxy_status_var.set("✗ Test failed")
            self._log(f"✗ Proxy test failed: {msg}", "error")
            messagebox.showerror("Proxy Test Failed", msg)
        self.root.after(8000, lambda: self.proxy_status_var.set(""))

    # ── Tree click-to-copy ───────────────────────────────────────
    def _on_tree_click(self, event):
        row = self.tree.identify_row(event.y)
        col = self.tree.identify_column(event.x)
        if not row or not col:
            return
        try:
            idx = int(col.replace("#", "")) - 1
            values = self.tree.item(row, "values")
            if idx < 0 or idx >= len(values):
                return
            text = str(values[idx])
        except Exception:
            return
        if not text:
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
        except Exception:
            return
        preview = text if len(text) <= 60 else text[:57] + "…"
        self._set_status(f"📋 Copied: {preview}")

    # ── Logging / record queues ──────────────────────────────────
    def _log(self, msg, tag="info"):
        with self._log_buffer_lock:
            self._log_buffer.append((time.strftime("%H:%M:%S"), msg, tag))

    def _poll_logs(self):
        with self._log_buffer_lock:
            batch = self._log_buffer[: self._POLL_BATCH]
            del self._log_buffer[: self._POLL_BATCH]
        if batch:
            self.log_text.configure(state=tk.NORMAL)
            for ts, msg, tag in batch:
                self.log_text.insert(tk.END, f"[{ts}] {msg}\n", tag)
            self.log_text.see(tk.END)
            self.log_text.configure(state=tk.DISABLED)
        self.root.after(self._POLL_INTERVAL_MS, self._poll_logs)

    def _enqueue_record(self, rec, source_label):
        with self._record_buffer_lock:
            self._record_buffer.append((rec, source_label))

    def _poll_records(self):
        with self._record_buffer_lock:
            batch = self._record_buffer[: self._POLL_BATCH]
            del self._record_buffer[: self._POLL_BATCH]
        for rec, label in batch:
            self._apply_single_record(rec, label)
        self.root.after(self._POLL_INTERVAL_MS, self._poll_records)

    def _set_status(self, msg):
        self.root.after(0, lambda: self.status_var.set(msg))

    # ── Merging ──────────────────────────────────────────────────
    def _match_existing(self, rec):
        nk = name_key(rec)
        if not nk:
            return None
        ak = addr_key(rec)
        exact = (nk, ak)
        if ak and exact in self.row_index:
            return exact
        candidates = [k for k in self.row_index if k[0] == nk]
        if not candidates:
            return None
        if ak:
            for k in candidates:
                if not k[1]:
                    return k
            return None
        return candidates[0]

    def _find_idx_by_key(self, key):
        nk, ak = key
        for i, r in enumerate(self.collected_records):
            if name_key(r) == nk and addr_key(r) == ak:
                return i
        for i, r in enumerate(self.collected_records):
            if name_key(r) == nk:
                return i
        return -1

    def _apply_single_record(self, rec, source_label):
        if is_blocked_name(rec.get("Name", "")):
            self.skipped_count_this_run += 1
            self._log(f"⊘ Skipped blocked name: {rec.get('Name','?')}  "
                      f"({source_label})", "skip")
            self._update_counter()
            return

        nk = name_key(rec)
        if not nk:
            return

        existing_key = self._match_existing(rec)
        if existing_key is not None:
            item_id = self.row_index[existing_key]
            current = list(self.tree.item(item_id, "values"))
            idx = self._find_idx_by_key(existing_key)
            if idx >= 0:
                merged = self._merge(self.collected_records[idx], rec)
                self.collected_records[idx] = merged
            else:
                merged = rec
            new_values = [str(merged.get(c, "")) for c in EXPORT_COLUMNS[:-1]]
            if new_values != current:
                self.tree.item(item_id, values=new_values, tags=("updated",))
                new_key = (name_key(merged), addr_key(merged))
                if new_key != existing_key and new_key not in self.row_index:
                    self.row_index.pop(existing_key, None)
                    self.row_index[new_key] = item_id
                self._schedule_highlight_clear(
                    item_id, "updated", HIGHLIGHT_DURATION_UPDATED
                )
                self.updated_count_this_run += 1
                filled = []
                for i, col in enumerate(EXPORT_COLUMNS[:-1]):
                    old_val = str(current[i]).strip() if i < len(current) else ""
                    new_val = str(merged.get(col, "")).strip()
                    if new_val and not old_val:
                        filled.append((col, new_val))
                for col, val in filled:
                    tag = ("phone" if col.startswith("Phone")
                           else ("address" if col == "Address" else "updated"))
                    self._log(f"↑ Filled {col} for {merged.get('Name','?')}: "
                              f"{val}  ({source_label})", tag)
                if not filled:
                    self._log(f"↑ Updated duplicate: {merged.get('Name','?')} "
                              f"({source_label})", "updated")
            else:
                self._log(f"= Duplicate (no new info): {merged.get('Name','?')} "
                          f"({source_label})", "info")
        else:
            new_key = (nk, addr_key(rec))
            item_id = self.tree.insert(
                "", tk.END,
                values=[rec.get(c, "") for c in EXPORT_COLUMNS[:-1]],
                tags=("new",),
            )
            self.row_index[new_key] = item_id
            self.collected_records.append(dict(rec))
            self._schedule_highlight_clear(item_id, "new", HIGHLIGHT_DURATION_NEW)
            self.new_count_this_run += 1
            phone = rec.get("Phone", "")
            addr = rec.get("Address", "")
            tag = "address" if addr else ("phone" if phone else "new")
            self._log(
                f"＋ {rec.get('Name','?')} | "
                f"Addr: {addr or '(none)'} | "
                f"Phone: {phone or '-'} | "
                f"Age: {rec.get('Age') or '-'}  ({source_label})", tag,
            )
        self._update_counter()

    @staticmethod
    def _merge(old, new):
        out = dict(old)
        for k, v in new.items():
            if k.startswith("Phone"):
                continue
            if v and not out.get(k):
                out[k] = v
        return merge_phone_fields(out, new)

    def _schedule_highlight_clear(self, item_id, tag, delay):
        if item_id in self.pending_highlight_clear:
            try:
                self.root.after_cancel(self.pending_highlight_clear[item_id])
            except Exception:
                pass

        def _reset():
            try:
                self.tree.item(item_id, tags=("normal",))
            except Exception:
                pass
            self.pending_highlight_clear.pop(item_id, None)

        self.pending_highlight_clear[item_id] = \
            self.root.after(int(delay * 1000), _reset)

    def _update_counter(self):
        self.count_var.set(
            f"Records: {len(self.collected_records)}  |  "
            f"New this run: {self.new_count_this_run}  |  "
            f"Updated: {self.updated_count_this_run}  |  "
            f"Skipped: {self.skipped_count_this_run}"
        )

    # ── PATCH 3: reset helper ────────────────────────────────────
    def _reset_results_for_new_address(self):
        """Clear the table + bookkeeping when the target address changes."""
        self.collected_records.clear()
        self.row_index.clear()
        for i in self.tree.get_children():
            self.tree.delete(i)
        self.new_count_this_run = 0
        self.updated_count_this_run = 0
        self.skipped_count_this_run = 0
        self._update_counter()

    # ── Actions ──────────────────────────────────────────────────
    def on_go(self):
        raw = self.url_slug_var.get().strip()
        if not raw:
            messagebox.showwarning("No Address", "Please enter an address.")
            return
        slug = normalize_address_input(raw)
        if not slug:
            messagebox.showwarning("Bad Address",
                                   "Could not parse the address you entered.")
            return
        self.url_slug_var.set(slug)
        url = ADDRESS_PREFIX + slug
        self._set_status("Navigating…")
        self._log(f"→ Navigate: {url}")
        self._set_buttons(False)
        self._worker_thread = threading.Thread(
            target=self._go_worker, args=(url,), daemon=True
        )
        self._worker_thread.start()

    def _go_worker(self, url):
        try:
            self.browser.navigate(url)
            self.root.after(0, self._navigate_ok)
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda err=err: self._navigate_err(err))

    def _navigate_ok(self):
        self._set_status("Page loaded. Click 'Scrape ALL Results'.")
        self._log("✔ Page loaded.")
        self._set_buttons(True)

    def _navigate_err(self, e):
        self._set_status(f"Error: {e}")
        self._log(f"Navigation error: {e}", "error")
        self._set_buttons(True)
        messagebox.showerror("Navigation Error", str(e))

    def on_debug(self):
        if not self.browser.lock.acquire(blocking=False):
            messagebox.showwarning("Busy", "A scrape is running.")
            return
        self.browser.lock.release()
        self._log("▶ Debug Page requested…", "debug")
        self._set_status("Dumping page for inspection…")
        threading.Thread(target=self._debug_worker, daemon=True).start()

    def _debug_worker(self):
        try:
            path = self.browser.debug_dump(out_path="debug_page.html", log=self._log)
            self.root.after(0, lambda path=path: self._debug_done(path))
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda err=err: self._debug_err(err))

    def _debug_done(self, path):
        self._set_status(f"Debug dump written to {os.path.basename(path)}")
        self._log(f"✔ Debug complete. Open {os.path.abspath(path)} "
                  f"in a text editor to inspect the raw HTML.", "debug")
        messagebox.showinfo(
            "Debug Complete",
            f"Saved to:\n{os.path.abspath(path)}\n\n"
            "See the Live log tab for a container preview.")

    def _debug_err(self, e):
        self._set_status(f"Debug error: {e}")
        self._log(f"Debug error: {e}", "error")
        messagebox.showerror("Debug Error", str(e))

    # ── PATCH 2: scrape honours the address box ──────────────────
    def on_scrape(self):
        drill = self.drill_var.get()

        # Build the URL we *should* be scraping from the address field
        slug = normalize_address_input(self.url_slug_var.get().strip())
        target_url = (ADDRESS_PREFIX + slug) if slug else None

        # Where is Chrome actually right now?
        current_url = None
        if self.browser.driver:
            try:
                current_url = (self.browser.driver.current_url or "").rstrip("/")
            except Exception:
                current_url = None

        target_norm = target_url.rstrip("/") if target_url else None

        if target_norm and current_url != target_norm:
            # Address field ≠ loaded page → navigate first, then scrape.
            self._log(
                f"⚠ Address field ({slug}) differs from loaded page "
                f"({current_url}). Navigating first…", "info"
            )
            self._reset_results_for_new_address()
            self.stop_event.clear()
            self._set_status("Navigating to new address…")
            self._set_buttons(False)
            self._worker_thread = threading.Thread(
                target=self._navigate_then_scrape,
                args=(target_url, drill),
                daemon=True,
            )
            self._worker_thread.start()
            return

        # Same URL → just scrape.
        self.stop_event.clear()
        self.new_count_this_run = 0
        self.updated_count_this_run = 0
        self.skipped_count_this_run = 0
        self._update_counter()
        self._set_status("Scraping (live)…")
        self._log(f"▶ Starting scrape (drill={drill})…")
        self._set_buttons(False)
        self._worker_thread = threading.Thread(
            target=self._scrape_worker, args=(drill,), daemon=True
        )
        self._worker_thread.start()

    def _navigate_then_scrape(self, url, drill):
        """Navigate to `url`, then kick off the normal scrape worker."""
        try:
            self.browser.navigate(url)
            # Confirm Chrome really landed on the requested URL
            try:
                landed = (self.browser.driver.current_url or "").rstrip("/")
            except Exception:
                landed = ""
            if landed and landed != url.rstrip("/"):
                self._log(f"⚠ Site redirected to: {landed}", "error")
            self.root.after(0, lambda: self._scrape_worker_after_nav(drill))
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda err=err: self._scrape_err(err))

    def _scrape_worker_after_nav(self, drill):
        self._set_status("Scraping (live)…")
        self._log(f"▶ Starting scrape (drill={drill})…")
        self._set_buttons(False)
        self._worker_thread = threading.Thread(
            target=self._scrape_worker, args=(drill,), daemon=True
        )
        self._worker_thread.start()

    def on_stop(self):
        if not self.stop_event.is_set():
            self.stop_event.set()
            self._set_status("Stop requested…")
            self._log("■ Stop requested – finishing current step…", "error")
            self.stop_btn.config(state=tk.DISABLED)

    def _scrape_worker(self, drill):
        def on_record(rec, source_label):
            self._enqueue_record(rec, source_label)

        def on_log(msg):
            self._log(msg)

        try:
            records = self.browser.scrape_all_results(
                drill_details=drill,
                on_record=on_record,
                on_log=on_log,
                should_stop=self.stop_event.is_set,
            )
            self.root.after(0, lambda records=records: self._scrape_done(records))
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda err=err: self._scrape_err(err))

    def _scrape_done(self, records):
        self._set_buttons(True)
        with_phone = sum(1 for r in records if r.get("Phone"))
        with_addr  = sum(1 for r in records if r.get("Address"))
        stopped = self.stop_event.is_set()
        prefix = "■ Stopped." if stopped else "Done."
        self._set_status(
            f"{prefix} {len(records)} records, {with_addr} with address, "
            f"{with_phone} with phone, {self.skipped_count_this_run} skipped.")
        self._log(
            f"{'■' if stopped else '✔'} Complete. {len(records)} records · "
            f"{with_addr} with address · {with_phone} with phone · "
            f"{self.skipped_count_this_run} skipped.", "new")
        self._update_counter()

    def _scrape_err(self, e):
        self._set_buttons(True)
        self._set_status(f"Scrape error: {e}")
        self._log(f"Scrape error: {e}", "error")
        messagebox.showerror("Scrape Error", str(e))

    def on_export(self):
        if not self.collected_records:
            messagebox.showinfo("No Data", "No records to export.")
            return
        try:
            n = self.exporter.append_records(self.collected_records)
            self._log(f"✔ Exported {n} rows to Google Sheets (appended below "
                      f"the last data row).", "new")
            self._set_status(f"Exported {n} rows.")
            messagebox.showinfo(
                "Export Complete",
                f"{n} rows appended below the last data row in Google Sheets.")
        except Exception as e:
            self._log(f"Export error: {e}", "error")
            messagebox.showerror("Export Error", str(e))

    def on_clear(self):
        self._reset_results_for_new_address()
        self._log("Cleared all data.")

    def _set_buttons(self, enabled):
        state = tk.NORMAL if enabled else tk.DISABLED
        for b in (self.go_btn, self.scrape_btn, self.export_btn,
                  self.clear_btn, self.debug_btn):
            b.config(state=state)
        self.stop_btn.config(state=tk.DISABLED if enabled else tk.NORMAL)

    def on_close(self):
        try:
            self.stop_event.set()
        except Exception:
            pass
        if self._worker_thread and self._worker_thread.is_alive():
            self._worker_thread.join(timeout=5)
        try:
            self.browser.close()
        except Exception:
            pass
        self.root.destroy()


# ══════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    root = tk.Tk()
    app = BrowserApp(root)
    root.protocol("WM_DELETE_WINDOW", app.on_close)
    root.mainloop()
