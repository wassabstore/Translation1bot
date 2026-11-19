# -*- coding: utf-8 -*-
"""
📚 بوت ترجمة الكتب — Telegram (aiogram 3)
الصيغ: PDF, EPUB, DOCX, TXT, MD, SRT, VTT, HTML, FB2 (+ MOBI/AZW3/RTF/ODT/DOC عبر calibre إن وُجد)
"""
import asyncio, hashlib, html, logging, os, re, secrets, shutil, sqlite3, subprocess, time
import xml.etree.ElementTree as ET
from collections import defaultdict
from datetime import date, datetime
from pathlib import Path

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

import aiosqlite
from aiohttp import ClientSession, web
import fitz  # PyMuPDF
from bs4 import BeautifulSoup, NavigableString
from deep_translator import GoogleTranslator
from docx import Document
from docx.oxml import OxmlElement
from docx.oxml.ns import qn
from ebooklib import epub, ITEM_DOCUMENT

from aiogram import BaseMiddleware, Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramBadRequest, TelegramForbiddenError, TelegramRetryAfter
from aiogram.filters import BaseFilter, Command, CommandObject, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (BotCommand, CallbackQuery, ErrorEvent, FSInputFile, InlineKeyboardButton,
                           LabeledPrice, Message, PreCheckoutQuery)
from aiogram.utils.keyboard import InlineKeyboardBuilder

# ══════════════════════════ الإعدادات ══════════════════════════
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
ADMINS = {8233150959} | {int(x) for x in re.findall(r"\d+", os.getenv("ADMIN_IDS", ""))}  # المالك + أي مدير من Render
DB_PATH = os.getenv("DB_PATH", "bot.db")
TMP = Path(os.getenv("TMP_DIR", "tmp")); TMP.mkdir(exist_ok=True)
MAX_JOBS = int(os.getenv("MAX_JOBS", "3"))          # كتب تُترجم بالتوازي
WORKERS = int(os.getenv("TRANSLATE_WORKERS", "4"))  # طلبات ترجمة متوازية
DEFAULTS = {
    "daily_limit": "30000",     # حرف مجاني يومياً
    "price_month": "150",       # نجوم تيليجرام
    "price_year": "1200",
    "referral_bonus": "10000",  # حرف لكل صديق يدعوه المستخدم
    "max_file_mb": "20",        # حد تيليجرام للتنزيل 20MB
    "contact": "",              # @username للدعم / شراء الأكواد
}
SET_LABELS = {
    "daily_limit": "الحد اليومي المجاني (حرف)", "price_month": "سعر الشهري (نجمة)",
    "price_year": "سعر السنوي (نجمة)", "referral_bonus": "مكافأة الدعوة (حرف)",
    "max_file_mb": "أقصى حجم ملف (MB)", "contact": "حساب الدعم (@username)",
}
LANGS = {
    "ar": "🇸🇦 العربية", "en": "🇬🇧 English", "fr": "🇫🇷 Français", "es": "🇪🇸 Español",
    "de": "🇩🇪 Deutsch", "it": "🇮🇹 Italiano", "pt": "🇵🇹 Português", "ru": "🇷🇺 Русский",
    "tr": "🇹🇷 Türkçe", "fa": "🇮🇷 فارسی", "ur": "🇵🇰 اردو", "hi": "🇮🇳 हिन्दी",
    "id": "🇮🇩 Indonesia", "zh-CN": "🇨🇳 中文", "ja": "🇯🇵 日本語", "ko": "🇰🇷 한국어",
    "nl": "🇳🇱 Nederlands", "pl": "🇵🇱 Polski", "uk": "🇺🇦 Українська", "iw": "🇮🇱 עברית",
}
RTL = {"ar", "fa", "ur", "iw"}

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("bookbot")

# ══════════════════════════ قاعدة البيانات ══════════════════════════
class DB:
    async def init(self):
        self.c = await aiosqlite.connect(DB_PATH)
        self.c.row_factory = aiosqlite.Row
        await self.c.executescript("""
        PRAGMA journal_mode=WAL;
        CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY, username TEXT, name TEXT, lang TEXT DEFAULT 'ar',
            joined INTEGER, last_seen INTEGER DEFAULT 0, used_today INTEGER DEFAULT 0, used_date TEXT DEFAULT '',
            premium_until INTEGER DEFAULT 0, banned INTEGER DEFAULT 0, active INTEGER DEFAULT 1,
            bonus INTEGER DEFAULT 0, referred_by INTEGER, files INTEGER DEFAULT 0);
        CREATE TABLE IF NOT EXISTS codes(code TEXT PRIMARY KEY, days INTEGER, created INTEGER, used_by INTEGER, used_at INTEGER);
        CREATE TABLE IF NOT EXISTS channels(chat_id INTEGER PRIMARY KEY, title TEXT, link TEXT);
        CREATE TABLE IF NOT EXISTS cache(h TEXT PRIMARY KEY, v TEXT);
        CREATE TABLE IF NOT EXISTS payments(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, stars INTEGER, days INTEGER, ts INTEGER);
        CREATE TABLE IF NOT EXISTS settings(k TEXT PRIMARY KEY, v TEXT);
        """)
        await self.c.commit()

    async def one(self, q, a=()):
        cur = await self.c.execute(q, a); r = await cur.fetchone()
        return dict(r) if r else None

    async def all(self, q, a=()):
        cur = await self.c.execute(q, a)
        return [dict(r) for r in await cur.fetchall()]

    async def run(self, q, a=()):
        cur = await self.c.execute(q, a); await self.c.commit()
        return cur.rowcount

    async def many(self, q, rows):
        await self.c.executemany(q, rows); await self.c.commit()


db = DB()
S: dict = {}  # الإعدادات في الذاكرة
BOT_USERNAME = ""
BOT_ID = 0


def gi(k): return int(S.get(k) or 0)


async def set_setting(k, v):
    S[k] = str(v)
    await db.run("INSERT OR REPLACE INTO settings VALUES(?,?)", (k, S[k]))


async def incr(k, n=1):
    S[k] = str(int(S.get(k, "0")) + n)
    await db.run("INSERT OR REPLACE INTO settings VALUES(?,?)", (k, S[k]))


async def get_user(uid): return await db.one("SELECT * FROM users WHERE id=?", (uid,))


async def ensure_user(tg, ref):
    now = int(time.time())
    rc = await db.run("INSERT OR IGNORE INTO users(id,username,name,joined,referred_by,last_seen) VALUES(?,?,?,?,?,?)",
                      (tg.id, tg.username, (tg.full_name or "")[:64], now, ref, now))
    if rc != 1:
        await db.run("UPDATE users SET username=?,name=?,active=1,last_seen=? WHERE id=?",
                     (tg.username, (tg.full_name or "")[:64], now, tg.id))
    return await get_user(tg.id), rc == 1


def today(): return date.today().isoformat()
def is_premium(u): return u["premium_until"] > time.time()


def remaining(u):
    used = u["used_today"] if u["used_date"] == today() else 0
    return max(0, gi("daily_limit") - used) + u["bonus"]


async def consume(uid, n):
    u = await get_user(uid)
    used = u["used_today"] if u["used_date"] == today() else 0
    daily_left = max(0, gi("daily_limit") - used)
    from_daily = min(n, daily_left)
    from_bonus = n - from_daily
    await db.run("UPDATE users SET used_today=?, used_date=?, bonus=MAX(0,bonus-?), files=files+1 WHERE id=?",
                 (used + from_daily, today(), from_bonus, uid))


async def add_premium(uid, days):
    u = await get_user(uid)
    base = max(int(time.time()), u["premium_until"])
    until = base + days * 86400
    await db.run("UPDATE users SET premium_until=? WHERE id=?", (until, uid))
    return until


def fmt_date(ts): return datetime.fromtimestamp(ts).strftime("%Y-%m-%d")

# ══════════════════════════ محرك الترجمة ══════════════════════════
HAS_LETTER = re.compile(r"[^\W\d_]", re.UNICODE)
CTRL = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f]")
TR_SEM = None


class TranslateError(Exception):
    pass


def _gtx(text, lang):
    import requests
    r = requests.post("https://translate.googleapis.com/translate_a/single",
                      params={"client": "gtx", "sl": "auto", "tl": lang, "dt": "t"},
                      data={"q": text}, timeout=25, headers={"User-Agent": "Mozilla/5.0"})
    r.raise_for_status()
    return "".join(p[0] for p in r.json()[0] if p and p[0])


class Skip(Exception):
    """المحرك لا يدعم هذا الطلب (لغة/طول) — تجاوزه دون تعطيله."""


def _lname(lang): return LANGS.get(lang, lang).split(" ", 1)[-1]


def _deep(text, lang):
    r = GoogleTranslator(source="auto", target=lang).translate(text)
    if not r: raise RuntimeError("empty")
    return r


def _deepl(text, lang):
    import requests
    key = os.getenv("DEEPL_API_KEY", "")
    tl = {"zh-CN": "ZH", "iw": "HE", "pt": "PT-PT", "en": "EN-US"}.get(lang, lang.split("-")[0].upper())
    if lang in ("fa", "ur", "hi"): raise Skip()
    host = "api-free.deepl.com" if key.endswith(":fx") else "api.deepl.com"
    r = requests.post(f"https://{host}/v2/translate", headers={"Authorization": f"DeepL-Auth-Key {key}"},
                      data={"text": text, "target_lang": tl}, timeout=40)
    r.raise_for_status()
    return r.json()["translations"][0]["text"]


def _gcloud(text, lang):
    import requests
    r = requests.post("https://translation.googleapis.com/language/translate/v2",
                      params={"key": os.getenv("GOOGLE_API_KEY", "")},
                      json={"q": text, "target": lang, "format": "text"}, timeout=40)
    r.raise_for_status()
    return html.unescape(r.json()["data"]["translations"][0]["translatedText"])


def _claude(text, lang):
    import requests
    r = requests.post("https://api.anthropic.com/v1/messages", timeout=120,
                      headers={"x-api-key": os.getenv("ANTHROPIC_API_KEY", ""), "anthropic-version": "2023-06-01"},
                      json={"model": os.getenv("CLAUDE_MODEL", "claude-haiku-5-5"), "max_tokens": 8000,
                            "system": f"You are a professional book translator. Translate the user's text into {_lname(lang)} "
                                      f"(language code {lang}). Keep exactly the same number of lines. Do not add notes, quotes or "
                                      f"explanations. Output only the translation.",
                            "messages": [{"role": "user", "content": text}]})
    r.raise_for_status()
    return "".join(b.get("text", "") for b in r.json()["content"])


LINGVA_HOSTS = [h.strip().rstrip("/") for h in os.getenv("LINGVA_HOSTS", "https://lingva.ml,https://lingva.garudalinux.org").split(",") if h.strip()]


def _lingva(text, lang):
    import requests, urllib.parse
    if len(text) > 1200: raise Skip()
    tl = {"zh-CN": "zh"}.get(lang, lang)
    last = None
    for h in LINGVA_HOSTS:
        try:
            r = requests.get(f"{h}/api/v1/auto/{tl}/{urllib.parse.quote(text, safe='')}", timeout=20)
            r.raise_for_status()
            return r.json()["translation"]
        except Exception as e:
            last = e
    raise RuntimeError(f"lingva: {last}")


PROV = {"deepl": _deepl, "gcloud": _gcloud, "claude": _claude, "gtx": _gtx, "deep": _deep, "lingva": _lingva}
PROV_BAD: dict = {}


def _providers():
    names = []
    if os.getenv("DEEPL_API_KEY"): names.append("deepl")
    if os.getenv("GOOGLE_API_KEY"): names.append("gcloud")
    if os.getenv("ANTHROPIC_API_KEY"): names.append("claude")
    return names + ["gtx", "deep", "lingva"]


def _call(text, lang):
    for a in range(3):
        names = _providers()
        active = [n for n in names if PROV_BAD.get(n, 0) <= time.time()] or names
        for n in active:
            try:
                r = PROV[n](text, lang)
                if r: return r
            except Skip:
                continue
            except Exception as e:
                log.warning("provider %s failed: %s", n, str(e)[:200])
                PROV_BAD[n] = time.time() + 60  # راحة دقيقة لهذا المحرك
        time.sleep(1.5 * (a + 1))
    return None


def split_long(t, limit=4000):
    sents = re.split(r"(?<=[.!?؟。])\s+", t)
    parts, cur = [], ""
    for s in sents:
        while len(s) > limit:
            if cur: parts.append(cur); cur = ""
            parts.append(s[:limit]); s = s[limit:]
        if len(cur) + len(s) + 1 > limit and cur:
            parts.append(cur); cur = s
        else:
            cur = (cur + " " + s).strip()
    if cur: parts.append(cur)
    return parts


def translate_group(texts, lang):
    if len(texts) == 1:
        t = texts[0]
        if len(t) <= 4500: return [_call(t, lang)]
        parts = split_long(t)
        res = [_call(p, lang) for p in parts]
        if any(r is None for r in res): return [None]
        return [" ".join(res)]
    r = _call("\n".join(texts), lang)
    if r:
        lines = r.split("\n")
        if len(lines) == len(texts): return lines
    return [_call(t, lang) for t in texts]


async def cache_get(keys):
    out, keys = {}, list(keys)
    for i in range(0, len(keys), 500):
        ch = keys[i:i + 500]
        rows = await db.all(f"SELECT h,v FROM cache WHERE h IN ({','.join('?' * len(ch))})", ch)
        out.update({r["h"]: r["v"] for r in rows})
    return out


async def translate_units(units, lang, idxs, progress=None):
    """يترجم units[i] لكل i في idxs ويعيد dict. بالتوازي + كاش + إعادة محاولة."""
    global TR_SEM
    if TR_SEM is None: TR_SEM = asyncio.Semaphore(WORKERS)
    keys = {i: hashlib.sha1(f"{lang}\0{units[i]}".encode()).hexdigest() for i in idxs}
    cached = await cache_get(set(keys.values()))
    todo = {}
    for i in idxs:
        if keys[i] not in cached: todo[keys[i]] = " ".join(units[i].split())
    groups, cur, size = [], [], 0
    for k, t in todo.items():
        if len(t) > 3800:
            groups.append([(k, t)]); continue
        if cur and (size + len(t) > 3800 or len(cur) >= 40):
            groups.append(cur); cur, size = [], 0
        cur.append((k, t)); size += len(t) + 1
    if cur: groups.append(cur)
    new, done, total = {}, 0, len(groups)

    async def work(g):
        nonlocal done
        async with TR_SEM:
            res = await asyncio.to_thread(translate_group, [t for _, t in g], lang)
        for (k, _), r in zip(g, res):
            if r is not None: new[k] = r
        done += 1
        if progress: await progress(done, total)

    await asyncio.gather(*(work(g) for g in groups))
    if new: await db.many("INSERT OR REPLACE INTO cache VALUES(?,?)", list(new.items()))
    if todo and (len(todo) - len(new)) / len(todo) > 0.3:
        raise TranslateError("translation backend failed")
    merged = {**cached, **new}
    return {i: merged.get(keys[i], units[i]) for i in idxs}

# ══════════════════════════ قراءة وإعادة بناء الكتب ══════════════════════════
def clean(t): return CTRL.sub("", t)


def read_text(path):
    raw = path.read_bytes()
    if raw.startswith((b"\xff\xfe", b"\xfe\xff")): return raw.decode("utf-16")
    for enc in ("utf-8-sig", "cp1256", "cp1252"):
        try: return raw.decode(enc)
        except UnicodeDecodeError: pass
    return raw.decode("utf-8", "ignore")


def load_lines(path, skip=lambda l: False):
    lines = read_text(path).splitlines()
    idx = [i for i, l in enumerate(lines) if l.strip() and not skip(l)]
    units = [lines[i] for i in idx]

    def rebuild(tr, lang, out):
        new = lines[:]
        for i, t in zip(idx, tr): new[i] = t
        out.write_text("\n".join(new), encoding="utf-8")
    return units, rebuild


def load_subs(path):
    return load_lines(path, lambda l: l.strip().isdigit() or "-->" in l or l.startswith("WEBVTT"))


PPR_SUCC = ("adjustRightInd", "snapToGrid", "spacing", "ind", "contextualSpacing", "mirrorIndents",
            "suppressOverlap", "jc", "textDirection", "textAlignment", "textboxTightWrap", "outlineLvl",
            "divId", "cnfStyle", "rPr", "sectPr", "pPrChange")
RPR_SUCC = ("cs", "em", "lang", "eastAsianLayout", "specVanish", "oMath")


def _insert_before(parent, el, succ_names):
    succ = {qn("w:" + s) for s in succ_names}
    for ch in parent:
        if ch.tag in succ: ch.addprevious(el); return
    parent.append(el)


def make_rtl(p):
    pPr = p._p.get_or_add_pPr()
    if pPr.find(qn("w:bidi")) is None: _insert_before(pPr, OxmlElement("w:bidi"), PPR_SUCC)
    for r in p.runs:
        rPr = r._r.get_or_add_rPr()
        if rPr.find(qn("w:rtl")) is None: _insert_before(rPr, OxmlElement("w:rtl"), RPR_SUCC)


def load_docx(path):
    doc, paras, seen = Document(str(path)), [], set()

    def collect(c):
        for p in c.paragraphs:
            if p.text.strip() and id(p._p) not in seen:
                seen.add(id(p._p)); paras.append(p)
        for t in getattr(c, "tables", []):
            for row in t.rows:
                for cell in row.cells: collect(cell)
    collect(doc)
    units = [p.text for p in paras]

    def rebuild(tr, lang, out):
        for p, t in zip(paras, tr):
            t = clean(t)
            if p.runs:
                p.runs[0].text = t
                for r in p.runs[1:]: r.text = ""
            else:
                p.add_run(t)
            if lang in RTL: make_rtl(p)
        doc.save(str(out))
    return units, rebuild


def load_pdf(path):
    d, units, pg = fitz.open(str(path)), [], []
    for n, page in enumerate(d):
        for b in page.get_text("blocks", sort=True):
            if b[6] == 0:
                t = " ".join(b[4].split())
                if t: units.append(t); pg.append(n)
    if not units: raise ValueError("no_text")

    def rebuild(tr, lang, out):
        doc, last = Document(), None
        for t, n in zip(tr, pg):
            if last is not None and n != last: doc.add_page_break()
            last = n
            p = doc.add_paragraph(clean(t))
            if lang in RTL: make_rtl(p)
        doc.save(str(out))
    return units, rebuild


BLOCKS = ["p", "h1", "h2", "h3", "h4", "h5", "h6", "li", "blockquote", "figcaption", "td", "th", "dt", "dd", "caption", "div"]


def html_leafs(soup):
    return [t for t in soup.find_all(BLOCKS) if not t.find(BLOCKS) and t.get_text(strip=True)]


def set_tag_text(tag, t):
    tag.clear(); tag.append(NavigableString(t))


def load_html(path):
    soup = BeautifulSoup(read_text(path), "html.parser")
    tags = html_leafs(soup)

    def rebuild(tr, lang, out):
        for tag, t in zip(tags, tr): set_tag_text(tag, t)
        if lang in RTL:
            root = soup.find("body") or soup
            if hasattr(root, "attrs"): root["dir"] = "rtl"
        out.write_text(str(soup), encoding="utf-8")
    return [t.get_text(" ", strip=True) for t in tags], rebuild


def load_epub(path):
    book = epub.read_epub(str(path))
    items, units, flat = [], [], []
    for it in book.get_items_of_type(ITEM_DOCUMENT):
        soup = BeautifulSoup(it.get_content(), "html.parser")
        tags = html_leafs(soup)
        items.append((it, soup, tags))
        for t in tags: units.append(t.get_text(" ", strip=True)); flat.append(t)
    if not units: raise ValueError("no_text")

    def rebuild(tr, lang, out):
        for tag, t in zip(flat, tr): set_tag_text(tag, t)
        for it, soup, _ in items:
            if lang in RTL:
                root = soup.find("body")
                if root is not None: root["dir"] = "rtl"
            it.set_content(str(soup).encode("utf-8"))
        epub.write_epub(str(out), book)
    return units, rebuild


def load_fb2(path):
    tree = ET.parse(str(path)); root = tree.getroot()
    ns = root.tag.split("}")[0] + "}" if root.tag.startswith("{") else ""
    names = {ns + x for x in ("p", "v", "subtitle", "text-author")}
    els = [e for e in root.iter() if e.tag in names and "".join(e.itertext()).strip()]
    units = ["".join(e.itertext()) for e in els]

    def rebuild(tr, lang, out):
        for e, t in zip(els, tr):
            for c in list(e): e.remove(c)
            e.text = t
        if ns: ET.register_namespace("", ns[1:-1])
        ET.register_namespace("l", "http://www.w3.org/1999/xlink")
        tree.write(str(out), encoding="utf-8", xml_declaration=True)
    return units, rebuild


LOADERS = {".txt": load_lines, ".md": load_lines, ".srt": load_subs, ".vtt": load_subs, ".docx": load_docx,
           ".pdf": load_pdf, ".epub": load_epub, ".html": load_html, ".htm": load_html, ".fb2": load_fb2}
CONVERT = {".mobi": ".epub", ".azw": ".epub", ".azw3": ".epub", ".lit": ".epub",
           ".rtf": ".docx", ".odt": ".docx", ".doc": ".docx"}
SUPPORTED = set(LOADERS) | set(CONVERT)


def convert(path, target):
    exe = shutil.which("ebook-convert")
    if not exe: raise RuntimeError("calibre")
    out = path.with_name(path.stem + "_conv" + target)
    subprocess.run([exe, str(path), str(out)], check=True, capture_output=True, timeout=900)
    return out, target

# ══════════════════════════ أدوات الواجهة ══════════════════════════
def kb(rows):
    b = InlineKeyboardBuilder()
    for row in rows:
        b.row(*[InlineKeyboardButton(text=t, url=d) if d.startswith("http") else
                InlineKeyboardButton(text=t, callback_data=d) for t, d in row])
    return b.as_markup()


def contact_url():
    c = S.get("contact", "").strip()
    if not c: return None
    return c if c.startswith("http") else "https://t.me/" + c.lstrip("@")


def main_kb(uid):
    rows = [[("🌐 لغة الترجمة", "lang"), ("📊 حسابي", "me")],
            [("💎 الاشتراك", "sub"), ("🎟 تفعيل كود", "redeem")],
            [("👥 ادعُ أصدقاءك", "ref"), ("❓ المساعدة", "help")]]
    if uid in ADMINS: rows.append([("🛠 لوحة الإدارة", "adm:home")])
    return kb(rows)


def plans_rows(extra=None):
    rows = [[(f"⭐ شهري — {gi('price_month')} نجمة", "buy:30")],
            [(f"⭐ سنوي — {gi('price_year')} نجمة", "buy:365")],
            [("🎟 لدي كود اشتراك", "redeem")]]
    if contact_url(): rows.append([("💬 شراء كود من الدعم", contact_url())])
    if extra: rows += extra
    return rows


def welcome(u):
    return (f"👋 أهلاً بك في <b>بوت ترجمة الكتب</b>\n\n"
            f"📚 أرسل لي أي كتاب أو ملف أو نص وسأترجمه مع الحفاظ على الصيغة.\n"
            f"🌐 لغة الترجمة الحالية: <b>{LANGS.get(u['lang'], u['lang'])}</b>\n\n"
            f"الصيغ: PDF • EPUB • DOCX • TXT • FB2 • HTML • SRT • MD • MOBI • AZW3 • RTF • ODT")


def bar(pct): return "▰" * (pct // 10) + "▱" * (10 - pct // 10)


class Progress:
    def __init__(self, msg, title): self.msg, self.title, self.last = msg, title, 0

    async def __call__(self, done, total):
        if time.time() - self.last < 2.5 and done < total: return
        self.last = time.time()
        pct = int(done * 100 / max(total, 1))
        try: await self.msg.edit_text(f"{self.title}\n{bar(pct)} {pct}%")
        except (TelegramBadRequest, TelegramRetryAfter): pass


async def edit(cb, text, markup=None):
    try: await cb.message.edit_text(text, reply_markup=markup)
    except TelegramBadRequest: pass

# ══════════════════════════ الاشتراك الإجباري + الحظر (Middleware) ══════════════════════════
SUB_OK: dict = {}


async def check_subs(bot, uid, force=False):
    if not force and time.time() - SUB_OK.get(uid, 0) < 60: return []
    missing = []
    for ch in await db.all("SELECT * FROM channels"):
        try:
            m = await bot.get_chat_member(ch["chat_id"], uid)
            if m.status in ("left", "kicked"): missing.append(ch)
        except Exception as e:
            log.warning("sub check failed for %s: %s", ch["chat_id"], e)
    if not missing: SUB_OK[uid] = time.time()
    return missing


class Gate(BaseMiddleware):
    async def __call__(self, handler, event, data):
        tg = event.from_user
        if tg is None or tg.is_bot: return
        bot = data["bot"]
        ref = None
        if isinstance(event, Message) and event.text:
            m = re.match(r"/start ref_(\d+)", event.text)
            if m: ref = int(m.group(1))
        user, is_new = await ensure_user(tg, ref)
        data["user"] = user
        if is_new and ref and ref != tg.id and await get_user(ref):
            await db.run("UPDATE users SET bonus=bonus+? WHERE id=?", (gi("referral_bonus"), ref))
            try: await bot.send_message(ref, f"🎉 انضم صديق عبر رابطك! حصلت على <b>{gi('referral_bonus'):,}</b> حرف إضافي.")
            except Exception: pass
        if tg.id in ADMINS: return await handler(event, data)
        if user["banned"]:
            if isinstance(event, Message): await event.answer("🚫 تم حظرك من استخدام البوت.")
            else: await event.answer("🚫 تم حظرك من استخدام البوت.", show_alert=True)
            return
        if isinstance(event, Message) and event.successful_payment: return await handler(event, data)
        if isinstance(event, CallbackQuery) and event.data == "chk": return await handler(event, data)
        missing = await check_subs(bot, tg.id)
        if missing:
            rows = [[(f"📢 {c['title']}", c["link"])] for c in missing] + [[("✅ تحققت من الاشتراك", "chk")]]
            text = "📌 للاستخدام يجب الاشتراك أولاً في القنوات التالية ثم الضغط على «تحققت»:"
            if isinstance(event, CallbackQuery): await event.answer()
            await bot.send_message(tg.id, text, reply_markup=kb(rows))
            return
        return await handler(event, data)

# ══════════════════════════ معالجة الكتب ══════════════════════════
JOBS = asyncio.Semaphore(MAX_JOBS)
ULOCK = defaultdict(asyncio.Lock)
PENDING: dict = {}


def safe_name(s): return re.sub(r"[^\w\u0600-\u06FF\- ]", "", s).strip()[:60] or "book"


def offer_text(total, rem):
    return (f"⚠️ حجم النص <b>{total:,}</b> حرف، والمتبقي لك اليوم <b>{rem:,}</b> حرف.\n\n"
            f"💎 اشترك لترجمة بلا حدود، أو اختر أحد الخيارات:")


async def process(bot, uid, orig_name, path, partial=False):
    user = await get_user(uid)
    lang = user["lang"]
    status = await bot.send_message(uid, "⏳ جارٍ تحليل الملف...")
    t0, keep, tmp_files = time.time(), False, [path]
    try:
        async with JOBS:
            ext = Path(orig_name).suffix.lower()
            work = path
            if ext in CONVERT:
                work, ext = await asyncio.to_thread(convert, path, CONVERT[ext]); tmp_files.append(work)
            units, rebuild = await asyncio.to_thread(LOADERS[ext], work)
            idxs = [i for i, u in enumerate(units) if HAS_LETTER.search(u)]
            total = sum(len(units[i]) for i in idxs)
            if not idxs: raise ValueError("no_text")
            prem, rem = is_premium(user), remaining(user)
            if not prem and total > rem:
                if not partial:
                    PENDING[uid] = (path, orig_name); keep = True
                    extra = []
                    if rem >= 500: extra.append([(f"✂️ ترجمة الجزء المجاني فقط ({rem:,} حرف)", "part")])
                    extra.append([("👥 احصل على رصيد بدعوة صديق", "ref")])
                    await status.edit_text(offer_text(total, rem), reply_markup=kb(plans_rows(extra)))
                    return
                acc, sel = 0, []
                for i in idxs:
                    if acc + len(units[i]) > rem: break
                    acc += len(units[i]); sel.append(i)
                if not sel:
                    await status.edit_text("⚠️ لا يوجد رصيد كافٍ اليوم.", reply_markup=kb(plans_rows())); return
                idxs, total = sel, acc
            prog = Progress(status, f"🌐 جارٍ الترجمة إلى {LANGS.get(lang, lang)}")
            res = await translate_units(units, lang, idxs, prog)
            tr = [res.get(i, units[i]) for i in range(len(units))]
            out_ext = ".docx" if ext == ".pdf" else ext
            out = TMP / f"{uid}_{int(t0)}_out{out_ext}"; tmp_files.append(out)
            await status.edit_text("📦 جارٍ بناء الملف النهائي...")
            await asyncio.to_thread(rebuild, tr, lang, out)
            cap = (f"✅ تمت الترجمة إلى <b>{LANGS.get(lang, lang)}</b>\n"
                   f"📝 {total:,} حرف • ⏱ {int(time.time() - t0)} ثانية" + ("\n✂️ ترجمة جزئية (حسب الرصيد المجاني)" if partial and not prem else ""))
            await bot.send_document(uid, FSInputFile(out, filename=f"{safe_name(Path(orig_name).stem)}_{lang}{out_ext}"), caption=cap)
            if not prem: await consume(uid, total)
            else: await db.run("UPDATE users SET files=files+1 WHERE id=?", (uid,))
            await incr("total_chars", total); await incr("total_files")
            try: await status.delete()
            except Exception: pass
    except TranslateError:
        await status.edit_text("❌ خدمة الترجمة لا تستجيب حالياً. لم يُخصم من رصيدك شيء، حاول بعد قليل.")
    except ValueError:
        await status.edit_text("❌ لم أجد نصاً قابلاً للاستخراج (قد يكون الملف صوراً ممسوحة ضوئياً).")
    except RuntimeError:
        await status.edit_text("❌ هذه الصيغة غير مفعّلة على السيرفر حالياً. جرّب EPUB / PDF / DOCX / TXT.")
    except Exception:
        log.exception("process failed")
        await status.edit_text("❌ حدث خطأ أثناء المعالجة. حاول مرة أخرى أو جرّب صيغة أخرى.")
    finally:
        if not keep:
            for f in tmp_files:
                try: f.unlink(missing_ok=True)
                except Exception: pass


async def resume_pending(bot, uid):
    item = PENDING.pop(uid, None)
    if item and item[0].exists():
        async with ULOCK[uid]: await process(bot, uid, item[1], item[0])

# ══════════════════════════ الراوترات ══════════════════════════
router = Router(); router.message.filter(F.chat.type == "private")
adm = Router(); adm.message.filter(F.chat.type == "private")


class IsAdmin(BaseFilter):
    async def __call__(self, ev): return ev.from_user.id in ADMINS


adm.message.filter(IsAdmin()); adm.callback_query.filter(IsAdmin())


class US(StatesGroup): redeem = State()
class AS(StatesGroup): bc = State(); user = State(); channel = State(); setval = State(); delcode = State()


# ─────────── المستخدم ───────────
@router.message(CommandStart())
async def cmd_start(m: Message, user, state: FSMContext):
    await state.clear()
    await m.answer(welcome(user), reply_markup=main_kb(m.from_user.id))


@router.message(Command("cancel"))
async def cmd_cancel(m: Message, state: FSMContext):
    await state.clear(); await m.answer("تم الإلغاء ✅")


@router.callback_query(F.data == "menu")
async def cb_menu(cb: CallbackQuery, user):
    await edit(cb, welcome(user), main_kb(cb.from_user.id)); await cb.answer()


@router.callback_query(F.data == "chk")
async def cb_chk(cb: CallbackQuery, bot: Bot, user):
    if await check_subs(bot, cb.from_user.id, force=True):
        await cb.answer("❌ لم تشترك في كل القنوات بعد", show_alert=True); return
    await cb.answer("✅ تم التحقق")
    try: await cb.message.delete()
    except Exception: pass
    await bot.send_message(cb.from_user.id, welcome(user), reply_markup=main_kb(cb.from_user.id))


@router.message(Command("lang"))
@router.callback_query(F.data == "lang")
async def lang_menu(ev):
    b = InlineKeyboardBuilder()
    for k, v in LANGS.items(): b.button(text=v, callback_data=f"setlang:{k}")
    b.adjust(2); b.row(InlineKeyboardButton(text="🔙 رجوع", callback_data="menu"))
    text = "🌐 اختر لغة الترجمة:"
    if isinstance(ev, CallbackQuery): await edit(ev, text, b.as_markup()); await ev.answer()
    else: await ev.answer(text, reply_markup=b.as_markup())


@router.callback_query(F.data.startswith("setlang:"))
async def set_lang(cb: CallbackQuery):
    lang = cb.data.split(":", 1)[1]
    if lang not in LANGS: return await cb.answer()
    await db.run("UPDATE users SET lang=? WHERE id=?", (lang, cb.from_user.id))
    await cb.answer(f"✅ {LANGS[lang]}")
    await edit(cb, f"✅ لغة الترجمة الآن: <b>{LANGS[lang]}</b>\n\nأرسل كتابك أو نصك 📚", main_kb(cb.from_user.id))


@router.message(Command("me"))
@router.callback_query(F.data == "me")
async def me(ev, user):
    u = await get_user(ev.from_user.id)
    sub = f"💎 نشط حتى <b>{fmt_date(u['premium_until'])}</b> (بلا حدود)" if is_premium(u) else "🆓 مجاني"
    text = (f"👤 <b>حسابك</b>\n🆔 <code>{u['id']}</code>\n🌐 اللغة: {LANGS.get(u['lang'])}\n"
            f"الاشتراك: {sub}\n")
    if not is_premium(u):
        text += f"📊 المتبقي اليوم: <b>{remaining(u):,}</b> حرف (الحد اليومي {gi('daily_limit'):,})\n🎁 رصيد إضافي: {u['bonus']:,}\n"
    text += f"📚 ملفات مترجمة: {u['files']}"
    mk = kb([[("💎 الاشتراك", "sub")], [("🔙 رجوع", "menu")]])
    if isinstance(ev, CallbackQuery): await edit(ev, text, mk); await ev.answer()
    else: await ev.answer(text, reply_markup=mk)


@router.callback_query(F.data == "sub")
async def cb_sub(cb: CallbackQuery):
    text = ("💎 <b>اشتراك بريميوم</b>\n\n• ترجمة كتب بلا حدود يومية\n• أولوية في المعالجة\n• يُجدَّد بالإضافة على المدة الحالية\n\n"
            "الدفع بنجوم تيليجرام ⭐ أو بكود اشتراك:")
    await edit(cb, text, kb(plans_rows([[("🔙 رجوع", "menu")]]))); await cb.answer()


@router.callback_query(F.data.startswith("buy:"))
async def cb_buy(cb: CallbackQuery, bot: Bot):
    days = int(cb.data.split(":")[1])
    stars = gi("price_year") if days == 365 else gi("price_month")
    title = "اشتراك سنوي 💎" if days == 365 else "اشتراك شهري 💎"
    await bot.send_invoice(cb.from_user.id, title=title, description=f"ترجمة كتب بلا حدود لمدة {days} يوماً",
                           payload=f"sub:{days}", provider_token="", currency="XTR",
                           prices=[LabeledPrice(label=title, amount=stars)])
    await cb.answer()


@router.pre_checkout_query()
async def pre_checkout(q: PreCheckoutQuery): await q.answer(ok=True)


@router.message(F.successful_payment)
async def paid(m: Message, bot: Bot):
    sp = m.successful_payment
    days = int(sp.invoice_payload.split(":")[1])
    until = await add_premium(m.from_user.id, days)
    await db.run("INSERT INTO payments(user_id,stars,days,ts) VALUES(?,?,?,?)", (m.from_user.id, sp.total_amount, days, int(time.time())))
    await m.answer(f"🎉 تم تفعيل اشتراكك حتى <b>{fmt_date(until)}</b>. شكراً لك!")
    asyncio.create_task(resume_pending(bot, m.from_user.id))


@router.message(Command("redeem"))
@router.callback_query(F.data == "redeem")
async def ask_code(ev, state: FSMContext):
    await state.set_state(US.redeem)
    text = "🎟 أرسل كود الاشتراك الآن (مثال: <code>BK-AB12-CD34-EF56</code>)\nللإلغاء: /cancel"
    if isinstance(ev, CallbackQuery): await ev.message.answer(text); await ev.answer()
    else: await ev.answer(text)


CODE_RE = re.compile(r"^BK-[A-Z0-9]{4}-[A-Z0-9]{4}-[A-Z0-9]{4}$")


async def redeem_code(m: Message, bot: Bot, code: str):
    code = code.strip().upper()
    row = await db.one("SELECT * FROM codes WHERE code=?", (code,))
    if not row: return await m.answer("❌ الكود غير صحيح.")
    if row["used_by"]: return await m.answer("❌ هذا الكود مستخدم مسبقاً.")
    if await db.run("UPDATE codes SET used_by=?, used_at=? WHERE code=? AND used_by IS NULL", (m.from_user.id, int(time.time()), code)) != 1:
        return await m.answer("❌ هذا الكود مستخدم مسبقاً.")
    until = await add_premium(m.from_user.id, row["days"])
    await m.answer(f"✅ تم التفعيل! اشتراكك ساري حتى <b>{fmt_date(until)}</b> 💎")
    asyncio.create_task(resume_pending(bot, m.from_user.id))


@router.message(US.redeem, F.text)
async def got_code(m: Message, state: FSMContext, bot: Bot):
    if m.text.startswith("/"): return
    await state.clear(); await redeem_code(m, bot, m.text)


@router.callback_query(F.data == "ref")
async def cb_ref(cb: CallbackQuery):
    link = f"https://t.me/{BOT_USERNAME}?start=ref_{cb.from_user.id}"
    await edit(cb, f"👥 <b>ادعُ أصدقاءك</b>\n\nعن كل صديق ينضم عبر رابطك تحصل على <b>{gi('referral_bonus'):,}</b> حرف إضافي!\n\n🔗 رابطك:\n<code>{link}</code>",
               kb([[("🔙 رجوع", "menu")]]))
    await cb.answer()


@router.message(Command("help"))
@router.callback_query(F.data == "help")
async def help_(ev):
    text = ("❓ <b>المساعدة</b>\n\n1️⃣ اختر لغة الترجمة من /lang\n2️⃣ أرسل الكتاب (حتى {mb}MB) أو أي نص\n3️⃣ انتظر الشريط ثم استلم الملف المترجم\n\n"
            "• PDF يُسلَّم بصيغة DOCX لإمكانية التحرير\n• ملف يكبر عن الحد؟ قسّمه إلى أجزاء\n• الملفات الممسوحة ضوئياً (صور) غير مدعومة\n"
            "• /me حسابك • /redeem تفعيل كود").format(mb=gi("max_file_mb"))
    if isinstance(ev, CallbackQuery): await edit(ev, text, kb([[("🔙 رجوع", "menu")]])); await ev.answer()
    else: await ev.answer(text)


@router.callback_query(F.data == "part")
async def cb_part(cb: CallbackQuery, bot: Bot):
    item = PENDING.pop(cb.from_user.id, None)
    if not item or not item[0].exists():
        return await cb.answer("انتهت صلاحية الطلب، أعد إرسال الملف.", show_alert=True)
    await cb.answer()
    try: await cb.message.delete()
    except Exception: pass
    async with ULOCK[cb.from_user.id]:
        await process(bot, cb.from_user.id, item[1], item[0], partial=True)


@router.message(F.document)
async def on_doc(m: Message, bot: Bot, user):
    doc = m.document
    name = doc.file_name or "book"
    ext = Path(name).suffix.lower()
    if ext not in SUPPORTED:
        return await m.answer("❌ صيغة غير مدعومة.\nالمدعوم: PDF • EPUB • DOCX • TXT • FB2 • HTML • SRT • MD • MOBI • AZW3 • RTF • ODT")
    if doc.file_size and doc.file_size > gi("max_file_mb") * 1024 * 1024:
        return await m.answer(f"❌ الملف أكبر من {gi('max_file_mb')}MB. قسّمه إلى أجزاء أصغر.")
    uid = m.from_user.id
    if ULOCK[uid].locked(): await m.answer("🕒 أُضيف ملفك إلى قائمة الانتظار وسيبدأ بعد الملف الحالي.")
    dl = await m.answer("⬇️ جارٍ تنزيل الملف...")
    path = TMP / f"{uid}_{doc.file_unique_id}{ext}"
    try:
        await bot.download(doc, destination=path, timeout=300)
    except Exception:
        return await dl.edit_text("❌ تعذّر تنزيل الملف (قد يكون كبيراً جداً).")
    try: await dl.delete()
    except Exception: pass
    async with ULOCK[uid]:
        await process(bot, uid, name, path)


@router.message(F.text & ~F.text.startswith("/"))
async def on_text(m: Message, bot: Bot, user):
    txt = m.text.strip()
    if CODE_RE.match(txt.upper()): return await redeem_code(m, bot, txt)
    u = await get_user(m.from_user.id)
    lines = txt.splitlines()
    idxs = [i for i, l in enumerate(lines) if HAS_LETTER.search(l)]
    if not idxs: return await m.answer("أرسل نصاً أو ملف كتاب 📚")
    total = sum(len(lines[i]) for i in idxs)
    rem = remaining(u)
    if not is_premium(u) and total > rem:
        return await m.answer(offer_text(total, rem), reply_markup=kb(plans_rows([[("👥 احصل على رصيد بدعوة صديق", "ref")]])))
    await bot.send_chat_action(m.chat.id, "typing")
    try:
        res = await translate_units(lines, u["lang"], idxs)
    except TranslateError:
        return await m.answer("❌ خدمة الترجمة لا تستجيب حالياً. لم يُخصم من رصيدك شيء، حاول بعد قليل.")
    out = "\n".join(res.get(i, l) if i in res else l for i, l in enumerate(lines))
    if not is_premium(u): await consume(u["id"], total)
    await incr("total_chars", total)
    for i in range(0, len(out), 4000): await m.answer(html.escape(out[i:i + 4000]))


@router.message()
async def fallback(m: Message):
    await m.answer("📚 أرسل لي ملف كتاب (PDF / EPUB / DOCX / TXT ...) أو نصاً لأترجمه.")


# ─────────── الإدارة ───────────
def admin_kb():
    return kb([[("📊 الإحصائيات", "adm:stats"), ("📢 إذاعة", "adm:bc")],
               [("👤 إدارة مستخدم", "adm:user"), ("📌 الاشتراك الإجباري", "adm:ch")],
               [("🎟 أكواد الاشتراك", "adm:codes"), ("⚙️ الإعدادات", "adm:set")],
               [("👥 قائمة المستخدمين", "adm:ul:all:0"), ("🗂 نسخة احتياطية", "adm:backup")]])


ADMIN_HOME = "🛠 <b>لوحة الإدارة</b>"
BACK = kb([[("🔙 رجوع", "adm:home")]])


@adm.message(Command("admin"))
async def cmd_admin(m: Message, state: FSMContext):
    await state.clear(); await m.answer(ADMIN_HOME, reply_markup=admin_kb())


@adm.message(Command("diag"))
async def cmd_diag(m: Message):
    """تشخيص الترجمة: يعرض النتيجة أو الخطأ الحقيقي مباشرة في تيليجرام."""
    out = []
    probes = [(n, (lambda n=n: PROV[n]("Hello, how are you today?", "ar"))) for n in _providers()]
    for name, fn in probes:
        try:
            r = await asyncio.to_thread(fn)
            out.append(f"✅ {name}: {html.escape(str(r))}")
        except Exception as e:
            out.append(f"❌ {name}: {html.escape(repr(e)[:300])}")
    u = await get_user(m.from_user.id)
    out.append(f"🌐 لغتك الحالية: {u['lang']}")
    await m.answer("\n".join(out))


@adm.message(F.document, F.caption == "/restore")
async def restore_caption(m: Message, bot: Bot):
    await do_restore(m, m.document, bot)


@adm.message(Command("restore"))
async def restore_reply(m: Message, bot: Bot):
    """الطريقة الأسهل: رد (Reply) بـ /restore على رسالة ملف النسخة الاحتياطية"""
    doc = m.reply_to_message.document if m.reply_to_message else None
    if not doc:
        return await m.answer("↩️ اضغط مطولاً على رسالة ملف النسخة الاحتياطية، اختر <b>رد (Reply)</b>، ثم اكتب <code>/restore</code>.")
    await do_restore(m, doc, bot)


async def do_restore(m: Message, doc, bot: Bot):
    path = TMP / "restore.db"
    try:
        await bot.download(doc, destination=path, timeout=120)
        c = sqlite3.connect(str(path))
        n = c.execute("SELECT COUNT(*) FROM users").fetchone()[0]
        c.execute("SELECT COUNT(*) FROM codes").fetchone(); c.close()
    except Exception:
        return await m.answer("❌ الملف غير صالح. أرسل ملف النسخة الاحتياطية الصحيح.")
    await db.c.close()
    for suf in ("-wal", "-shm"): Path(DB_PATH + suf).unlink(missing_ok=True)
    shutil.copy(path, DB_PATH); path.unlink(missing_ok=True)
    await db.init()
    for k, v in DEFAULTS.items(): S[k] = v
    for r in await db.all("SELECT k,v FROM settings"): S[r["k"]] = r["v"]
    SUB_OK.clear()
    await m.answer(f"✅ تم الاسترجاع بنجاح: {n:,} مستخدم.")


async def unused_view():
    rows = await db.all("SELECT code,days FROM codes WHERE used_by IS NULL ORDER BY created DESC LIMIT 15")
    text = "📋 <b>الأكواد غير المستخدمة</b> (آخر 15)\nاضغط على كود لإلغائه 🗑" if rows else "لا توجد أكواد غير مستخدمة."
    return text, kb([[(f"🗑 {r['code']} • {r['days']}ي", f"adm:cdel:{r['code']}")] for r in rows] + [[("🔙 رجوع", "adm:codes")]])


async def delete_code(code):
    code = code.strip().upper()
    row = await db.one("SELECT * FROM codes WHERE code=?", (code,))
    if not row: return "❌ الكود غير موجود.", None
    if row["used_by"]:
        return (f"⚠️ الكود مستخدم من <code>{row['used_by']}</code> بتاريخ {fmt_date(row['used_at'])}، ولا يمكن حذفه.\n"
                f"يمكنك إلغاء اشتراك صاحبه من بطاقته:"), kb([[("👤 فتح بطاقة المستخدم", f"u:card:{row['used_by']}")]])
    await db.run("DELETE FROM codes WHERE code=?", (code,))
    return f"🗑 تم إلغاء الكود <code>{code}</code> ولن يعمل بعد الآن.", None


@adm.message(Command("cancel"))
async def adm_cancel(m: Message, state: FSMContext):
    await state.clear(); await m.answer("تم الإلغاء ✅")


@adm.message(AS.delcode, F.text)
async def adm_delcode(m: Message, state: FSMContext):
    await state.clear()
    text, mk = await delete_code(m.text)
    await m.answer(text, reply_markup=mk)


@adm.message(Command("delcode"))
async def cmd_delcode(m: Message, command: CommandObject):
    if not command.args: return await m.answer("الاستخدام: /delcode BK-XXXX-XXXX-XXXX")
    text, mk = await delete_code(command.args)
    await m.answer(text, reply_markup=mk)


@adm.message(Command("ban", "unban", "unsub"))
async def cmd_quick(m: Message, command: CommandObject):
    """أوامر سريعة: /ban ID  /unban ID  /unsub ID  (أو @username)"""
    arg = (command.args or "").strip()
    u = None
    if arg.isdigit(): u = await get_user(int(arg))
    elif arg: u = await db.one("SELECT * FROM users WHERE LOWER(username)=?", (arg.lstrip("@").lower(),))
    if not u: return await m.answer(f"الاستخدام: /{command.command} ID أو @username")
    c = command.command
    if c == "ban":
        if u["id"] in ADMINS: return await m.answer("لا يمكن حظر مدير.")
        await db.run("UPDATE users SET banned=1 WHERE id=?", (u["id"],)); msg = "🚫 تم حظر"
    elif c == "unban":
        await db.run("UPDATE users SET banned=0 WHERE id=?", (u["id"],)); msg = "✅ تم فك حظر"
    else:
        await db.run("UPDATE users SET premium_until=0 WHERE id=?", (u["id"],)); msg = "❌ تم إلغاء اشتراك"
    await m.answer(f"{msg} <code>{u['id']}</code>")


async def stats_text():
    now, start = int(time.time()), int(datetime.combine(date.today(), datetime.min.time()).timestamp())
    q = lambda w: db.one(f"SELECT COUNT(*) c FROM users WHERE {w}")
    total, new, act, prem, ban, blocked = [(await q(w))["c"] for w in
        ("1", f"joined>={start}", f"used_date='{today()}'", f"premium_until>{now}", "banned=1", "active=0")]
    stars = (await db.one("SELECT COALESCE(SUM(stars),0) s FROM payments"))["s"]
    codes = await db.one("SELECT COUNT(*) a, SUM(used_by IS NOT NULL) b FROM codes")
    return (f"📊 <b>الإحصائيات</b>\n\n👥 المستخدمون: <b>{total:,}</b>\n🆕 جدد اليوم: {new:,}\n⚡ نشطون اليوم: {act:,}\n"
            f"💎 مشتركون: {prem:,}\n🚫 محظورون: {ban:,}\n🚪 حظروا البوت: {blocked:,}\n\n"
            f"📚 ملفات مترجمة: {int(S.get('total_files', 0)):,}\n📝 حروف مترجمة: {int(S.get('total_chars', 0)):,}\n"
            f"⭐ نجوم مستلمة: {stars:,}\n🎟 أكواد: {codes['a'] or 0} (مستخدم {codes['b'] or 0})")


async def channels_view():
    chs = await db.all("SELECT * FROM channels")
    text = "📌 <b>الاشتراك الإجباري</b>\n\n" + ("\n".join(f"• {html.escape(c['title'])}" for c in chs) if chs else "لا توجد قنوات.") + \
           "\n\n⚠️ يجب أن يكون البوت <b>مشرفاً</b> في القناة."
    rows = [[(f"❌ حذف {c['title'][:25]}", f"adm:chdel:{c['chat_id']}")] for c in chs]
    rows += [[("➕ إضافة قناة", "adm:chadd")], [("🔙 رجوع", "adm:home")]]
    return text, kb(rows)


def gen_code():
    al = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    return "BK-" + "-".join("".join(secrets.choice(al) for _ in range(4)) for _ in range(3))


async def settings_view():
    rows = [[(f"{lbl}: {S.get(k) or '—'}", f"adm:set:{k}")] for k, lbl in SET_LABELS.items()] + [[("🔙 رجوع", "adm:home")]]
    return "⚙️ <b>الإعدادات</b> — اضغط لتعديل قيمة:", kb(rows)


async def users_view(flt, page, per=8):
    now = int(time.time())
    cond = {"all": "1", "prem": f"premium_until>{now}", "ban": "banned=1"}.get(flt, "1")
    total = (await db.one(f"SELECT COUNT(*) c FROM users WHERE {cond}"))["c"]
    pages = max(1, (total + per - 1) // per)
    page = min(max(page, 0), pages - 1)
    rows = await db.all(f"SELECT id,name,banned,premium_until FROM users WHERE {cond} ORDER BY last_seen DESC LIMIT ? OFFSET ?",
                        (per, page * per))
    btns = []
    for r in rows:
        icon = "🚫" if r["banned"] else ("💎" if r["premium_until"] > now else "👤")
        btns.append([(f"{icon} {(r['name'] or '-')[:18]} • {r['id']}", f"u:card:{r['id']}")])
    nav = []
    if page > 0: nav.append(("◀️", f"adm:ul:{flt}:{page - 1}"))
    nav.append((f"{page + 1}/{pages}", "adm:noop"))
    if page < pages - 1: nav.append(("▶️", f"adm:ul:{flt}:{page + 1}"))
    tabs = [(("• " if k == flt else "") + lbl, f"adm:ul:{k}:0") for k, lbl in (("all", "الكل"), ("prem", "💎 المشتركون"), ("ban", "🚫 المحظورون"))]
    text = f"👥 <b>قائمة المستخدمين</b> — {total:,}\n👤 عادي  💎 مشترك  🚫 محظور\nاضغط على مستخدم لإدارته:"
    return text, kb([tabs] + btns + [nav, [("🔙 رجوع", "adm:home")]])


@adm.callback_query(F.data.startswith("adm:"))
async def adm_cb(cb: CallbackQuery, state: FSMContext, bot: Bot):
    p = cb.data.split(":"); a = p[1]
    await state.clear(); await cb.answer()
    if a == "home": await edit(cb, ADMIN_HOME, admin_kb())
    elif a == "stats": await edit(cb, await stats_text(), kb([[("🔄 تحديث", "adm:stats")], [("🔙 رجوع", "adm:home")]]))
    elif a == "bc":
        await state.set_state(AS.bc)
        await edit(cb, "📢 أرسل الآن الرسالة التي تريد إذاعتها (نص / صورة / فيديو / ملف ...)\nللإلغاء: /cancel", BACK)
    elif a == "user":
        await state.set_state(AS.user)
        await edit(cb, "👤 أرسل <b>ID</b> المستخدم أو @username:", BACK)
    elif a == "ch": await edit(cb, *await channels_view())
    elif a == "chadd":
        await state.set_state(AS.channel)
        await edit(cb, "📌 أرسل معرف القناة (@channel) أو أعد توجيه رسالة منها.\nتأكد أن البوت مشرف فيها.", BACK)
    elif a == "chdel":
        await db.run("DELETE FROM channels WHERE chat_id=?", (int(p[2]),)); SUB_OK.clear()
        await edit(cb, *await channels_view())
    elif a == "codes":
        await edit(cb, "🎟 <b>أكواد الاشتراك</b>", kb([[("➕ كود شهري (30 يوم)", "adm:gen:30"), ("➕ كود سنوي (365 يوم)", "adm:gen:365")],
                                                       [("📋 غير المستخدمة", "adm:unused"), ("🗑 إلغاء كود", "adm:delcode")], [("🔙 رجوع", "adm:home")]]))
    elif a == "gen":
        days = int(p[2])
        if len(p) == 3:
            await edit(cb, f"كم كوداً ({days} يوم) تريد إنشاءه؟",
                       kb([[(str(n), f"adm:gen:{days}:{n}") for n in (1, 5, 10, 25)], [("🔙 رجوع", "adm:codes")]]))
        else:
            n = int(p[3]); codes = []
            for _ in range(n):
                c = gen_code(); codes.append(c)
            await db.many("INSERT INTO codes(code,days,created) VALUES(?,?,?)", [(c, days, int(time.time())) for c in codes])
            await edit(cb, f"✅ تم إنشاء {n} كود ({days} يوم):\n\n" + "\n".join(f"<code>{c}</code>" for c in codes),
                       kb([[("🔙 رجوع", "adm:codes")]]))
    elif a == "unused": await edit(cb, *await unused_view())
    elif a == "cdel":
        await db.run("DELETE FROM codes WHERE code=? AND used_by IS NULL", (p[2],))
        await edit(cb, *await unused_view())
    elif a == "delcode":
        await state.set_state(AS.delcode)
        await edit(cb, "🗑 أرسل الكود الذي تريد إلغاءه:\nللإلغاء: /cancel", BACK)
    elif a == "set":
        if len(p) == 2: await edit(cb, *await settings_view())
        else:
            await state.set_state(AS.setval); await state.update_data(key=p[2])
            await edit(cb, f"أرسل القيمة الجديدة لـ <b>{SET_LABELS[p[2]]}</b>\n(القيمة الحالية: {S.get(p[2]) or '—'})\nللحذف أرسل: -", BACK)
    elif a == "ul": await edit(cb, *await users_view(p[2], int(p[3])))
    elif a == "noop": pass
    elif a == "backup":
        await db.c.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        tmp = TMP / "backup.db"; shutil.copy(DB_PATH, tmp)

        def slim():  # نحذف الكاش لتصغير الملف
            c = sqlite3.connect(str(tmp)); c.execute("DELETE FROM cache"); c.commit(); c.execute("VACUUM"); c.close()
        await asyncio.to_thread(slim)
        await bot.send_document(cb.from_user.id, FSInputFile(tmp, filename=f"backup_{today()}.db"),
                                caption="🗂 نسخة احتياطية.\nللاسترجاع: أرسل هذا الملف للبوت وفي التعليق اكتب <code>/restore</code>")


# حظر / إدارة مستخدم
async def user_card(uid):
    u = await get_user(uid)
    if not u: return None, None
    sub = f"حتى {fmt_date(u['premium_until'])}" if is_premium(u) else "لا"
    text = (f"👤 <b>{html.escape(u['name'] or '-')}</b> @{u['user
