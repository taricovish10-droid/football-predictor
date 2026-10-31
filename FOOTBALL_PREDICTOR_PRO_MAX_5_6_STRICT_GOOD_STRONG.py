# -*- coding: utf-8 -*-
"""
محلل وتوقّع مباريات كرة القدم PRO  (الإصدار 3 — External Odds & Predictions)
Windows 10/11 | Python 3.10+
إضافات PRO MAX 5.4: ESPN live/injuries/news, walk-forward backtest, Value Bets, سجل توقعات وتسوية،
مقارنة أسعار كل شركة، تنبيهات تغير النتائج والقيمة، وتوسيع عرض النتائج الدقيقة.
مصدر النتائج التاريخية: football-data.org API | الأودز والتوقعات: API-Football / API-Sports
التثبيت: py -m pip install requests
التشغيل: py football_predictor_pro.py

ما الجديد في هذا الإصدار:
- تلوين الاحتمالات: قوي (أخضر) | جيد (أزرق) | متوسط (أصفر) | ضعيف (أحمر).
- تحليل عميق: هجوم/دفاع (عام + داخل/خارج الأرض) + فورمة + ملف آخر 10 مباريات + مواجهات مباشرة.
- توقع الشوط الأول والثاني والنتيجة النهائية (وإذا توفرت بيانات أشواط فعلية تُستخدم بدل الافتراض).
- مقارنة أسواق: 1 / X / 2 و 1X و X2 و 12 والأهداف وتسجيل الفريقين.
- أفضل اختيار احتمالي، أو "لا اختيار" عندما تكون البيانات أو الأفضلية ضعيفة.
- الاختيار الثاني بأودز أعلى يكون دائماً في نفس اتجاه التحليل (نفس الفريق/نفس اتجاه الأهداف)،
  ولا يعاكس الاختيار الرئيسي أبداً (لا فريق آخر ولا تعادل ولا أهداف معاكسة).

ملف CSV: الأعمدة الأساسية date,home,away,home_goals,away_goals
         أعمدة اختيارية للشوط الأول: ht_home_goals,ht_away_goals

ملاحظات منهجية:
- النموذج: Poisson + تصحيح Dixon-Coles + وزن زمني للمباريات الحديثة + انكماش بايزي للعينات الصغيرة.
- يمكن جلب أودز عدة شركات مراهنات وتوقعات مستقلة عبر API-Football / API-Sports بمفتاح منفصل.
- مقارنة النموذج بالسوق وصفية؛ احتمالات النموذج لا تضمن قيمة رهان أو ربحاً.
- الاحتمالات ليست ضماناً ولا توصية مالية.
"""

from __future__ import annotations

import csv
import json
import math
import os
import sys
import re
import difflib
import hashlib
import uuid
import unicodedata
import threading
import tkinter as tk
from collections import defaultdict, namedtuple
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from tkinter import filedialog, messagebox, ttk, simpledialog
from typing import Optional

try:
    import requests
except ImportError:
    requests = None

APP_TITLE = "محلل كرة القدم PRO MAX 5.6 — فلترة صارمة للتوقعات"
API_BASE = "https://api.football-data.org/v4"
APP_DIR = os.path.dirname(os.path.abspath(sys.executable if getattr(sys, "frozen", False) else __file__))
# تُحفظ الإعدادات والبيانات بجوار ملف البرنامج، ولا تُحمّل إلا المسابقة المختارة.
DATA_DIR = APP_DIR
CACHE_DIR = os.path.join(DATA_DIR, "data_cache")
try:
    os.makedirs(CACHE_DIR, exist_ok=True)
except OSError:
    # إذا كان البرنامج داخل مجلد محمي في Windows، استخدم مجلد المستخدم كحل احتياطي.
    DATA_DIR = os.path.join(os.path.expanduser("~"), "FootballPredictorData")
    CACHE_DIR = os.path.join(DATA_DIR, "data_cache")
    os.makedirs(CACHE_DIR, exist_ok=True)
CONFIG_PATH = os.path.join(DATA_DIR, "football_predictor_config.json")
HISTORY_PATH = os.path.join(DATA_DIR, "prediction_history.json")

LEAGUES = {
    "الدوري الإنجليزي الممتاز": "PL",
    "الدوري الإسباني": "PD",
    "الدوري الألماني": "BL1",
    "الدوري الإيطالي": "SA",
    "الدوري الفرنسي": "FL1",
    "الدوري الهولندي": "DED",
    "الدوري البرتغالي": "PPL",
    "دوري أبطال أوروبا": "CL",
    "دوري البطولة الإنجليزية (Championship)": "ELC",
    "الدوري الإنجليزي الدرجة الأولى": "EL1",
    "الدوري الإنجليزي الدرجة الثانية": "EL2",
    "الدرجة الثانية الإسبانية": "SD",
    "الدرجة الثانية الألمانية": "BL2",
    "الدرجة الثانية الإيطالية": "SB",
    "الدرجة الثانية الفرنسية": "FL2",
    "الدوري البلجيكي": "BJL",
    "الدوري التركي": "TSL",
    "الدوري الاسكتلندي": "SPL",
}

# ------------------------------ بيانات ESPN: إصابات، أخبار، مباشر ------------------------------
def fetch_espn_live(league_code: str, day: Optional[str] = None) -> dict:
    slug = ESPN_LEAGUES.get(league_code)
    if not slug:
        raise RuntimeError("لا يوجد ربط ESPN لهذا الدوري.")
    params = None
    if day and re.fullmatch(r"\d{4}-\d{2}-\d{2}", day):
        params = {"dates": day.replace("-", "")}
    return _espn_get(f"{ESPN_SITE_BASE}/{slug}/scoreboard", params)


def _walk_dicts(node):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from _walk_dicts(value)
    elif isinstance(node, list):
        for value in node:
            yield from _walk_dicts(value)


def _espn_injury_records(payload):
    # بعض ردود ESPN تعيد روابط Core API بدلاً من الكائنات؛ نفكّها عند الحاجة.
    expanded = [payload]
    refs, seen_refs = [], set()
    for obj in _walk_dicts(payload):
        ref = obj.get("$ref")
        if isinstance(ref, str) and ref.startswith("https://") and "espn.com" in ref and ref not in seen_refs:
            refs.append(ref); seen_refs.add(ref)
    for ref in refs[:40]:
        try:
            expanded.append(_espn_get(ref))
        except Exception:
            continue
    # توسيع مراجع اللاعب حتى يمكن استخراج الاسم والمركز.
    athlete_refs = []
    for obj in list(_walk_dicts(expanded)):
        athlete = obj.get("athlete")
        if isinstance(athlete, dict) and isinstance(athlete.get("$ref"), str):
            ref = athlete["$ref"]
            if ref.startswith("https://") and "espn.com" in ref and ref not in seen_refs:
                athlete_refs.append(ref); seen_refs.add(ref)
    for ref in athlete_refs[:40]:
        try:
            expanded.append(_espn_get(ref))
        except Exception:
            continue
    records, seen = [], set()
    for obj in _walk_dicts(expanded):
        athlete = obj.get("athlete") if isinstance(obj.get("athlete"), dict) else {}
        name = (athlete.get("displayName") or athlete.get("fullName") or
                obj.get("displayName") or obj.get("fullName") or "")
        if not name:
            continue
        status_obj = obj.get("status")
        status = (status_obj.get("type") or status_obj.get("name") or status_obj.get("description")
                  if isinstance(status_obj, dict) else status_obj) or obj.get("type") or obj.get("description") or "إصابة مسجلة"
        pos_obj = athlete.get("position") or obj.get("position") or {}
        position = (pos_obj.get("displayName") or pos_obj.get("abbreviation")
                    if isinstance(pos_obj, dict) else str(pos_obj or ""))
        key = (name.casefold(), str(status).casefold())
        if key in seen:
            continue
        seen.add(key)
        records.append({"name": name, "status": str(status), "position": position})
    return records[:40]


def _espn_lineups(summary):
    teams = []
    box = summary.get("boxscore") or {}
    for group in box.get("players", []) or summary.get("rosters", []) or []:
        team = group.get("team") or {}
        team_name = team.get("displayName") or team.get("name") or "فريق"
        starters, substitutes = [], []
        for stat_group in group.get("statistics", []) or []:
            for player in stat_group.get("athletes", []) or []:
                athlete = player.get("athlete") or player
                name = athlete.get("displayName") or athlete.get("fullName")
                if not name:
                    continue
                if player.get("starter") is True or str(player.get("starter", "")).lower() == "true":
                    starters.append(name)
                else:
                    substitutes.append(name)
        if starters or substitutes:
            teams.append({"team": team_name, "starters": list(dict.fromkeys(starters)),
                          "substitutes": list(dict.fromkeys(substitutes))})
    return teams


def fetch_espn_team_context(league_code: str, home: str, away: str, match_date: str = "") -> dict:
    """Fetch match-specific injuries and confirmed lineups from ESPN; cache briefly beside the app."""
    slug = ESPN_LEAGUES.get(league_code)
    if not slug:
        return {"available": False, "message": "لا يوجد ربط ESPN لهذا الدوري."}
    cache_key = re.sub(r"[^A-Za-z0-9_-]+", "_", f"availability_{league_code}_{home}_{away}_{match_date}")
    cache_file = os.path.join(CACHE_DIR, cache_key[:150] + ".json")
    try:
        with open(cache_file, "r", encoding="utf-8") as f:
            cached = json.load(f)
        if datetime.now().timestamp() - float(cached.get("saved_at", 0)) < 300:
            return cached.get("data", {})
    except Exception:
        pass

    found, league_name = _espn_find_event(slug, home, away, match_date)
    _, _, event, competition, home_name, away_name = found
    event_id = str(event.get("id") or "")
    team_records = []
    for competitor in competition.get("competitors", []) or []:
        team = competitor.get("team") or {}
        team_name = team.get("displayName") or team.get("name") or ""
        team_id = team.get("id")
        injuries, injury_error = [], ""
        if team_id:
            try:
                injury_payload = _espn_get(f"{ESPN_SITE_BASE}/{slug}/teams/{team_id}/injuries")
                injuries = _espn_injury_records(injury_payload)
            except Exception as exc:
                injury_error = str(exc)
        team_records.append({"team": team_name, "team_id": str(team_id or ""),
                             "injuries": injuries, "injury_error": injury_error})

    summary, summary_error = {}, ""
    if event_id:
        try:
            summary = _espn_get(f"{ESPN_SITE_BASE}/{slug}/summary", {"event": event_id})
        except Exception as exc:
            summary_error = str(exc)
    lineups = _espn_lineups(summary)
    lineup_confirmed = any(x.get("starters") for x in lineups)
    result = {
        "available": True, "event_id": event_id, "league": league_name,
        "fixture": {"home": home_name, "away": away_name, "date": event.get("date", "")},
        "teams": team_records, "lineups": lineups,
        "lineup_status": "تشكيلة منشورة من ESPN" if lineup_confirmed else "التشكيلة لم تُنشر بعد في ESPN",
        "lineup_confirmed": lineup_confirmed,
        "summary_error": summary_error,
        "note": "الإصابات والتشكيلات لا تتوفر لكل الدوريات أو المباريات. لا تُفسر البيانات غير المتاحة على أنها عدم وجود غيابات."
    }
    try:
        tmp = cache_file + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"saved_at": datetime.now().timestamp(), "data": result}, f, ensure_ascii=False)
        os.replace(tmp, cache_file)
    except Exception:
        pass
    return result


def _availability_factors(context, home, away):
    """Small, capped xG adjustments only for ESPN-listed injuries with identifiable roles."""
    factors = {"home_attack": 1.0, "home_defence": 1.0,
               "away_attack": 1.0, "away_defence": 1.0, "details": []}
    if not isinstance(context, dict) or not context.get("available"):
        return factors
    for team in context.get("teams", []):
        name = team.get("team", "")
        is_home = _team_similarity(name, home) >= _team_similarity(name, away)
        attack_loss = defence_loss = 0.0
        for injury in team.get("injuries", []) or []:
            pos = str(injury.get("position", "")).casefold()
            status = str(injury.get("status", "")).casefold()
            if any(k in status for k in ("available", "fit", "active", "healthy")):
                continue
            severity = 0.55 if any(k in status for k in ("doubt", "question", "day-to-day", "50/50")) else 1.0
            # التشكيلة الرسمية تُستخدم لتحديد إن كان اللاعب المصاب ضمن الأساسيين فعلاً.
            lineup = next((x for x in context.get("lineups", [])
                           if _team_similarity(x.get("team", ""), name) >= 0.78), None)
            if context.get("lineup_confirmed") and lineup:
                starters = {str(x).casefold() for x in lineup.get("starters", [])}
                if str(injury.get("name", "")).casefold() in starters:
                    severity *= 0.20  # اللاعب مشارك رغم وجود تقرير إصابة/شكوى
            is_gk = pos.strip() in ("gk", "g", "goalkeeper") or any(k in pos for k in ("goalkeeper", "keeper", "حارس"))
            is_def = pos.strip() in ("d", "df", "cb", "lb", "rb") or any(k in pos for k in ("defen", "back", "ظهير", "دفاع"))
            is_fwd = pos.strip() in ("f", "fw", "st", "cf", "w") or any(k in pos for k in ("forward", "striker", "wing", "attacker", "مهاجم"))
            is_mid = pos.strip() in ("m", "mf", "cm", "dm", "am") or any(k in pos for k in ("mid", "وسط"))
            if is_gk:
                defence_loss += 0.055 * severity
            elif is_def:
                defence_loss += 0.035 * severity
            elif is_fwd:
                attack_loss += 0.040 * severity
            elif is_mid:
                attack_loss += 0.022 * severity
                defence_loss += 0.012 * severity
            else:
                # Position unknown: record it, but do not invent a tactical effect.
                factors["details"].append(f"{name}: {injury.get('name', 'لاعب')} — مركز غير معروف، لم يُخصم آلياً")
                continue
            factors["details"].append(f"{name}: {injury.get('name', 'لاعب')} ({injury.get('status', 'إصابة')})")
        attack_loss = min(0.16, attack_loss)
        defence_loss = min(0.14, defence_loss)
        prefix = "home" if is_home else "away"
        factors[f"{prefix}_attack"] *= (1.0 - attack_loss)
        factors[f"{prefix}_defence"] *= (1.0 - defence_loss)
    return factors


def parse_espn_live_events(data: dict) -> list[dict]:
    out = []
    for ev in data.get("events", []) or []:
        comp = (ev.get("competitions") or [{}])[0]
        sides = comp.get("competitors", [])
        if len(sides) < 2:
            continue
        h = next((x for x in sides if x.get("homeAway") == "home"), sides[0])
        a = next((x for x in sides if x.get("homeAway") == "away"), sides[1])
        status_obj = comp.get("status", {}) or {}
        st = status_obj.get("type", {}) or {}
        def stat_map(side):
            vals = {}
            for item in side.get("statistics", []) or []:
                if isinstance(item, dict):
                    key = str(item.get("name") or item.get("abbreviation") or "").casefold()
                    value = item.get("displayValue", item.get("value", ""))
                    if key: vals[key] = value
            return vals
        hs_stats, as_stats = stat_map(h), stat_map(a)
        def first_stat(stats, *names):
            for name in names:
                if name in stats and stats[name] not in (None, ""):
                    return stats[name]
            return "—"
        live_stats = (
            f"تسديدات {first_stat(hs_stats, 'totalshots', 'shots')}:{first_stat(as_stats, 'totalshots', 'shots')} | "
            f"على المرمى {first_stat(hs_stats, 'shotsontarget', 'shots_on_target')}:{first_stat(as_stats, 'shotsontarget', 'shots_on_target')} | "
            f"استحواذ {first_stat(hs_stats, 'possession', 'possessionpct')}:{first_stat(as_stats, 'possession', 'possessionpct')}"
        )
        out.append({"home": (h.get("team") or {}).get("displayName", "Home"),
                    "away": (a.get("team") or {}).get("displayName", "Away"),
                    "hs": h.get("score", "-"), "as": a.get("score", "-"),
                    "status": st.get("shortDetail") or st.get("description") or "مجدولة",
                    "clock": status_obj.get("displayClock") or "—",
                    "period": status_obj.get("period", 0), "stats": live_stats,
                    "state": st.get("state", "pre"), "date": ev.get("date", "")})
    return out


# ------------------------------ مستويات الاحتمال والألوان ------------------------------
# يمكنك تعديل الحدود من هنا. الترتيب من الأعلى إلى الأدنى.
Tier = namedtuple("Tier", "min key label fg bg")
TIERS = [
    Tier(0.70, "strong", "قوي", "#0f6b3f", "#d9f2e3"),    # أخضر
    Tier(0.60, "good", "جيد", "#0b5cad", "#dbeafe"),      # أزرق
    Tier(0.50, "medium", "متوسط", "#7a5200", "#fff1bf"),  # أصفر
    Tier(0.00, "weak", "ضعيف", "#a4170f", "#fddcd8"),     # أحمر
]
TIER_BY_KEY = {t.key: t for t in TIERS}

# شروط تقديم اختيار (وإلا يُعرض "لا اختيار").
PICK_MIN_PROB = 0.70      # لا يُعرض اختيار إلا إذا تجاوز الاحتمال المحافظ 70%
PICK_MIN_QUALITY = 70     # جودة بيانات مرتفعة فقط
PICK_MIN_GAMES = 10       # عينة تاريخية أكبر لتقليل التذبذب
UNCERTAINTY_MARGIN = 0.10  # أقصى خصم من الاحتمال عندما تكون الجودة صفراً
HIGH_ODDS_MIN_PROB = 0.20  # أدنى احتمال محافظ لاعتبار سوق «محتملاً» عند البحث عن أعلى أودز
MIN_HT_MATCHES = 40       # أقل عدد مباريات ببيانات شوط أول فعلية لاعتمادها

# اتجاه التحليل: الاختيار بأودز عالية لا يُقبل إلا إذا كان في نفس اتجاه التحليل ولا يعاكسه.
SIDE_LEAN_GAP = 0.05      # فارق (فوز المضيف − فوز الضيف) الذي يُعدّ ميلاً واضحاً لفريق
GOALS_LEAN = 0.55         # احتمال أكثر من 2.5 ≥ هذا الحد ⇒ اتجاه «أهداف أكثر»، ≤ (1−الحد) ⇒ «أهداف أقل»
BTTS_LEAN = 0.55          # احتمال تسجيل الفريقين ≥ هذا الحد ⇒ «نعم»، ≤ (1−الحد) ⇒ «لا»


def tier_of(p: float) -> Tier:
    for t in TIERS:
        if p >= t.min:
            return t
    return TIERS[-1]


# ------------------------------ أدوات رياضية ------------------------------

def poisson_pmf(k: int, lam: float) -> float:
    if lam <= 0:
        return 1.0 if k == 0 else 0.0
    return math.exp(-lam + k * math.log(lam) - math.lgamma(k + 1))


def clamp(x: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, x))


def dc_tau(x: int, y: int, lam_h: float, lam_a: float, rho: float) -> float:
    """Dixon-Coles correction for the four low-score outcomes."""
    if x == 0 and y == 0:
        return 1.0 - lam_h * lam_a * rho
    if x == 0 and y == 1:
        return 1.0 + lam_h * rho
    if x == 1 and y == 0:
        return 1.0 + lam_a * rho
    if x == 1 and y == 1:
        return 1.0 - rho
    return 1.0


def attack_label(v: float):
    """(نص، مفتاح لون) — كلما زادت القيمة كان الهجوم أقوى."""
    if v >= 1.25:
        return "هجوم ممتاز", "strong"
    if v >= 1.05:
        return "هجوم جيد", "good"
    if v >= 0.90:
        return "هجوم متوسط", "medium"
    return "هجوم ضعيف", "weak"


def defence_label(v: float):
    """(نص، مفتاح لون) — كلما قلّت القيمة كان الدفاع أصلب."""
    if v <= 0.80:
        return "دفاع صلب جداً", "strong"
    if v <= 0.95:
        return "دفاع جيد", "good"
    if v <= 1.10:
        return "دفاع متوسط", "medium"
    return "دفاع ضعيف", "weak"


# ------------------------------ البيانات ------------------------------

@dataclass
class Match:
    played: date
    home: str
    away: str
    hg: int
    ag: int
    hht: Optional[int] = None   # أهداف المضيف في الشوط الأول (اختياري)
    aht: Optional[int] = None   # أهداف الضيف في الشوط الأول (اختياري)


def _opt_int(value) -> Optional[int]:
    if value is None:
        return None
    try:
        text = str(value).strip()
        return int(text) if text != "" else None
    except (TypeError, ValueError):
        return None


# # FIX #35/#36: تصفير أشواط غير متسقة بدل تركها فاسدة في المباراة.
def _validate_half_time(m: Match) -> Match:
    if m.hht is not None and (m.hht < 0 or m.hht > m.hg):
        m.hht = None
    if m.aht is not None and (m.aht < 0 or m.aht > m.ag):
        m.aht = None
    if (m.hht is None) != (m.aht is None):
        m.hht = None
        m.aht = None
    return m


def parse_matches(items) -> list[Match]:
    rows = []
    for m in items:
        try:
            score = m.get("score", {})
            ft = score.get("fullTime", {})
            hg, ag = ft.get("home"), ft.get("away")
            if hg is None or ag is None:
                continue
            ht = score.get("halfTime") or {}
            row = Match(
                date.fromisoformat(m["utcDate"][:10]),
                m["homeTeam"].get("shortName") or m["homeTeam"]["name"],
                m["awayTeam"].get("shortName") or m["awayTeam"]["name"],
                int(hg), int(ag),
                _opt_int(ht.get("home")), _opt_int(ht.get("away")),
            )
            rows.append(_validate_half_time(row))
        except (KeyError, TypeError, ValueError):
            continue
    return rows


def load_csv(path: str) -> list[Match]:
    """CSV columns: date,home,away,home_goals,away_goals (YYYY-MM-DD)
    optional: ht_home_goals,ht_away_goals"""
    rows = []
    with open(path, "r", encoding="utf-8-sig", newline="") as f:
        reader = csv.DictReader(f)
        required = {"date", "home", "away", "home_goals", "away_goals"}
        if not required.issubset(set(reader.fieldnames or [])):
            raise ValueError("أعمدة CSV المطلوبة: date,home,away,home_goals,away_goals")
        for row in reader:
            try:
                m = Match(
                    date.fromisoformat(row["date"].strip()[:10]),
                    row["home"].strip(), row["away"].strip(),
                    int(row["home_goals"]), int(row["away_goals"]),
                    _opt_int(row.get("ht_home_goals")), _opt_int(row.get("ht_away_goals")),
                )
                rows.append(_validate_half_time(m))
            except Exception:
                continue
    if not rows:
        raise ValueError("لم أجد مباريات صحيحة في الملف.")
    return rows


def fetch_competition(code: str, api_key: str, seasons_back: int = 2, force_refresh: bool = False):
    os.makedirs(CACHE_DIR, exist_ok=True)
    cache_file = os.path.join(CACHE_DIR, f"competition_{code}_{seasons_back}.json")
    if not force_refresh:
        try:
            with open(cache_file, "r", encoding="utf-8") as cf:
                cached = json.load(cf)
            if datetime.now().timestamp() - float(cached.get("saved_at", 0)) < 86400:
                rows = [_validate_half_time(Match(date.fromisoformat(x[0]), x[1], x[2],
                              int(x[3]), int(x[4]), _opt_int(x[5]), _opt_int(x[6])))
                        for x in cached["matches"]]
                if len(rows) >= 30:
                    return rows, cached.get("name", code) + " (ذاكرة 24 ساعة)", []
        except Exception:
            pass
    if requests is None:
        raise RuntimeError("مكتبة requests غير مثبتة. نفّذ: py -m pip install requests")
    headers = {"X-Auth-Token": api_key}
    session = requests.Session()
    session.headers.update(headers)
    try:
        info = session.get(f"{API_BASE}/competitions/{code}", timeout=25)
        _raise_api(info)
        info_data = info.json()
        current = int(info_data["currentSeason"]["startDate"][:4])
        all_rows = []
        errors = []
        for year in range(current, current - seasons_back - 1, -1):
            try:
                r = session.get(
                    f"{API_BASE}/competitions/{code}/matches",
                    params={"season": year, "status": "FINISHED"},
                    timeout=30
                )
                _raise_api(r)
                all_rows.extend(parse_matches(r.json().get("matches", [])))
            except Exception as exc:
                errors.append(f"{year}: {exc}")
        # إزالة التكرار
        unique = {(x.played, x.home, x.away): x for x in all_rows}
        result = sorted(unique.values(), key=lambda x: x.played)
        if len(result) < 30:
            detail = "\n".join(errors)
            raise RuntimeError(
                f"البيانات المسترجعة قليلة ({len(result)} مباراة). "
                "قد تكون مواسم سابقة غير متاحة في خطتك.\n" + detail
            )
        try:
            tmp = cache_file + ".tmp"
            with open(tmp, "w", encoding="utf-8") as cf:
                json.dump({"saved_at": datetime.now().timestamp(), "name": info_data.get("name", code),
                           "matches": [[x.played.isoformat(), x.home, x.away, x.hg, x.ag, x.hht, x.aht]
                                       for x in result]}, cf, ensure_ascii=False)
            os.replace(tmp, cache_file)
        except Exception:
            pass
        return result, info_data.get("name", code), errors
    finally:
        session.close()


def _raise_api(response):
    if response.status_code == 401:
        raise RuntimeError("مفتاح API غير صحيح (401).")
    if response.status_code == 403:
        raise RuntimeError("الوصول مرفوض (403): قد لا تكون المسابقة متاحة في خطتك.")
    if response.status_code == 429:
        raise RuntimeError("تم تجاوز حد الطلبات (429). انتظر قليلاً ثم أعد المحاولة.")
    response.raise_for_status()


# ------------------------------ مصادر الأودز وتوقعات المواقع ------------------------------
API_SPORTS_BASE = "https://v3.football.api-sports.io"
# معرّفات API-Football (API-Sports) للدوريات التي يدعمها البرنامج.
API_SPORTS_LEAGUES = {
    "PL": 39, "PD": 140, "BL1": 78, "SA": 135,
    "FL1": 61, "DED": 88, "PPL": 94, "CL": 2,
    "ELC": 40, "EL1": 41, "EL2": 42, "SD": 141,
    "BL2": 79, "SB": 136, "FL2": 62,
    "BJL": 144, "TSL": 203, "SPL": 179,
}


def _team_key(value: str) -> str:
    """توحيد أسماء الفرق لتقليل اختلافات التهجئة بين مزودي البيانات."""
    value = unicodedata.normalize("NFKD", str(value or ""))
    value = "".join(ch for ch in value if not unicodedata.combining(ch))
    value = value.casefold().replace("&", " and ")
    value = re.sub(r"[^a-z0-9]+", " ", value)
    ignored = {"fc", "afc", "cf", "sc", "club", "football", "the", "and"}
    tokens = [x for x in value.split() if x not in ignored]
    key = " ".join(tokens)
    aliases = {
        "man city": "manchester city", "man utd": "manchester united",
        "man united": "manchester united", "spurs": "tottenham hotspur",
        "tottenham": "tottenham hotspur", "wolves": "wolverhampton wanderers",
        "brighton": "brighton hove albion", "west ham": "west ham united",
        "ath madrid": "atletico madrid", "atleti": "atletico madrid",
        "psg": "paris saint germain", "bayern": "bayern munich",
        # # FIX #30: توحيد كلا الناديين تحت اسم قانوني واحد لتفادي الخلط بينهما.
        "inter": "inter milan", "inter milan": "inter milan",
        "ac milan": "ac milan", "milan": "ac milan",
    }
    return aliases.get(key, key)


def _team_similarity(a: str, b: str) -> float:
    aa, bb = _team_key(a), _team_key(b)
    if not aa or not bb:
        return 0.0
    if aa == bb:
        return 1.0
    if aa in bb or bb in aa:
        return 0.90
    seq = difflib.SequenceMatcher(None, aa, bb).ratio()
    ta, tb = set(aa.split()), set(bb.split())
    overlap = len(ta & tb) / max(1, len(ta | tb))
    return 0.65 * seq + 0.35 * overlap


def _api_sports_get(endpoint: str, params: dict, api_key: str):
    if requests is None:
        raise RuntimeError("مكتبة requests غير مثبتة. نفّذ: py -m pip install requests")
    try:
        response = requests.get(
            f"{API_SPORTS_BASE}/{endpoint.lstrip('/')}",
            headers={"x-apisports-key": api_key}, params=params, timeout=30
        )
    except requests.RequestException as exc:
        raise RuntimeError(f"تعذر الاتصال بمصدر API-Football: {exc}") from exc
    if response.status_code == 401:
        raise RuntimeError("مفتاح API-Football غير صحيح (401).")
    if response.status_code == 403:
        raise RuntimeError("الوصول مرفوض (403): تحقق من صلاحية خطتك أو تغطية الدوري.")
    if response.status_code == 429:
        raise RuntimeError("تم تجاوز حد طلبات API-Football. انتظر حتى تجدد الحصة.")
    if response.status_code == 204:
        return {"response": [], "errors": {}}
    response.raise_for_status()
    try:
        data = response.json()
    except ValueError as exc:
        raise RuntimeError("ردّ API-Football ليس JSON صالحاً.") from exc
    errors = data.get("errors") if isinstance(data, dict) else None
    if errors:
        if isinstance(errors, dict):
            detail = "; ".join(f"{k}: {v}" for k, v in errors.items() if v)
        else:
            detail = str(errors)
        raise RuntimeError("API-Football أعاد خطأ: " + (detail or "طلب غير صالح"))
    return data


AUTO_DATE_WORDS = {"", "auto", "تلقائي", "تلقائى", "تلقائيا", "تلقائياً"}
AUTO_SEARCH_DAYS = 30


def _is_auto_date(value: str) -> bool:
    return str(value or "").strip().casefold() in AUTO_DATE_WORDS


def _upcoming_events(api_key: str, league_id: int, season: int):
    """يجلب مباريات الدوري القادمة (نافذة زمنية أولاً ثم next كخطة بديلة)."""
    today = date.today()
    base = {"league": league_id, "season": season, "timezone": "Africa/Casablanca"}
    attempts = [
        dict(base, **{"from": today.isoformat(),
                      "to": (today + timedelta(days=AUTO_SEARCH_DAYS)).isoformat()}),
        dict(base, next=40),
    ]
    last_error = None
    for params in attempts:
        try:
            data = _api_sports_get("fixtures", params, api_key)
            events = data.get("response", []) if isinstance(data, dict) else []
            if events:
                return events
        except RuntimeError as exc:
            last_error = exc
    if last_error:
        raise last_error
    return []


def _find_api_fixture(api_key: str, league_code: str, home: str, away: str, match_date: str):
    league_id = API_SPORTS_LEAGUES.get(league_code)
    if not league_id:
        raise RuntimeError("لا يوجد ربط API-Football لهذا الدوري حالياً.")
    auto = _is_auto_date(match_date)
    if auto:
        today = date.today()
        season = today.year if today.month >= 7 else today.year - 1
        events = _upcoming_events(api_key, league_id, season)
        match_date = f"المباريات القادمة خلال {AUTO_SEARCH_DAYS} يوماً"
    else:
        try:
            match_day = datetime.strptime(match_date, "%Y-%m-%d").date()
        except ValueError as exc:
            raise ValueError("تاريخ المباراة يجب أن يكون بالشكل YYYY-MM-DD أو «تلقائي».") from exc
        # الدوريات الأوروبية تبدأ عادةً في النصف الثاني من السنة.
        season = match_day.year if match_day.month >= 7 else match_day.year - 1
        data = _api_sports_get("fixtures", {
            "date": match_date, "league": league_id, "season": season,
            "timezone": "Africa/Casablanca"
        }, api_key)
        events = data.get("response", []) if isinstance(data, dict) else []
    scored = []
    for event in events:
        teams = event.get("teams") or {}
        h_name = (teams.get("home") or {}).get("name", "")
        a_name = (teams.get("away") or {}).get("name", "")
        hs, as_ = _team_similarity(home, h_name), _team_similarity(away, a_name)
        scored.append((min(hs, as_), hs + as_, event, h_name, a_name))
    scored.sort(key=lambda x: (x[0], x[1]), reverse=True)
    if not scored or scored[0][0] < 0.66:
        examples = "، ".join(f"{x[3]} × {x[4]}" for x in scored[:4])
        suffix = f" مباريات قريبة في الاسم: {examples}." if examples else ""
        raise RuntimeError(
            f"لم أجد مباراة مطابقة لـ {home} × {away} ({match_date}) في هذا الدوري. "
            "تحقق من الدوري واسمَي الفريقين (صاحب الأرض أولاً)، أو أدخل التاريخ يدوياً." + suffix
        )
    best = scored[0]
    if len(scored) > 1 and best[0] == scored[1][0] and best[1] == scored[1][1]:
        raise RuntimeError("وجدت أكثر من مباراة متشابهة؛ تعذر تحديد المباراة بشكل موثوق.")
    fixture = best[2].get("fixture") or {}
    fixture_id = fixture.get("id")
    if not fixture_id:
        raise RuntimeError("وجدت المباراة لكن المصدر لم يُرجع رقمها التعريفي.")
    return {
        "id": fixture_id,
        "date": fixture.get("date", "" if auto else match_date),
        "league": (best[2].get("league") or {}).get("name", ""),
        "home": best[3], "away": best[4], "season": season,
    }


def _percent_number(value):
    if value is None or value == "":
        return None
    try:
        number = float(str(value).replace("%", "").strip())
        if number <= 1:
            number *= 100
        return number
    except (TypeError, ValueError):
        return None


def _parse_site_predictions(data: dict) -> dict:
    rows = data.get("response", []) if isinstance(data, dict) else []
    if not rows:
        return {"available": False, "message": "لا توجد توقعات متاحة لهذه المباراة حالياً."}
    item = rows[0] or {}
    pred = item.get("predictions") or {}
    percent = pred.get("percent") or {}
    goals = pred.get("goals") or {}
    win_or_draw = pred.get("win_or_draw")
    if isinstance(win_or_draw, str):
        win_or_draw = win_or_draw.strip().casefold() in ("true", "1", "yes", "نعم")
    return {
        "available": bool(pred),
        "winner": (pred.get("winner") or {}).get("name"),
        "winner_comment": (pred.get("winner") or {}).get("comment"),
        "advice": pred.get("advice"),
        "win_or_draw": win_or_draw,
        "under_over": pred.get("under_over"),
        "goals_home": goals.get("home"), "goals_away": goals.get("away"),
        "percent": {k: _percent_number(percent.get(k)) for k in ("home", "draw", "away")},
        "comparison": item.get("comparison") or {},
        "teams": item.get("teams") or {},
    }


def _market_ar(value: str) -> str:
    raw = str(value or "").strip()
    low = raw.casefold()
    if low in ("match winner", "1x2", "fulltime result"):
        return "نتيجة المباراة 1X2"
    if "goals over/under" in low:
        line = raw.split("|")[-1].strip() if "|" in raw else ""
        return f"الأهداف أكثر/أقل ({line})" if line else "الأهداف أكثر/أقل"
    if "both teams score" in low or low == "btts":
        return "تسجيل الفريقين"
    if "double chance" in low:
        return "الفرصة المزدوجة"
    if "asian handicap" in low:
        return "الهانديكاب الآسيوي"
    return raw


def _outcome_ar(value: str) -> str:
    raw = str(value or "").strip()
    low = raw.casefold()
    fixed = {"home": "فوز المضيف", "draw": "تعادل", "away": "فوز الضيف",
             "yes": "نعم", "no": "لا", "1": "فوز المضيف", "x": "تعادل", "2": "فوز الضيف"}
    if low in fixed:
        return fixed[low]
    match = re.match(r"^(over|under)\s*([0-9]+(?:\.[0-9]+)?)$", raw, re.I)
    if match:
        return f"{'أكثر من' if match.group(1).casefold() == 'over' else 'أقل من'} {match.group(2)} هدف"
    return raw


def _parse_site_odds(data: dict) -> dict:
    """استخراج متوسط وبأفضل سعر متاح واحتمال سوقي بعد إزالة الهامش لكل bookmaker."""
    fixtures = data.get("response", []) if isinstance(data, dict) else []
    if not fixtures:
        return {"available": False, "books": 0, "rows": [],
                "message": "لم يُرجع المزود أودز لهذه المباراة؛ قد لا تكون التغطية متاحة أو لم يبدأ نشر الأسعار."}
    bookmakers = fixtures[0].get("bookmakers", []) or []
    collected = defaultdict(list)
    for bookmaker in bookmakers:
        book_name = bookmaker.get("name") or bookmaker.get("title") or "شركة غير معروفة"
        for bet in bookmaker.get("bets", []) or []:
            bet_name = bet.get("name") or f"سوق {bet.get('id', '')}"
            grouped = defaultdict(list)
            for outcome in bet.get("values", []) or []:
                label = str(outcome.get("value", "")).strip()
                try:
                    odd = float(outcome.get("odd"))
                except (TypeError, ValueError):
                    continue
                if not label or odd <= 1.0 or not math.isfinite(odd):
                    continue
                line_match = re.match(r"^(over|under)\s*([0-9]+(?:\.[0-9]+)?)$", label, re.I)
                bucket = f"{bet_name} | {line_match.group(2)}" if line_match else bet_name
                grouped[bucket].append((label, odd))
            for bucket, outcomes in grouped.items():
                if not outcomes:
                    continue
                raw = [1.0 / odd for _, odd in outcomes]
                total = sum(raw)
                for (label, odd), implied in zip(outcomes, raw):
                    fair_prob = implied / total if total > 0 and len(outcomes) > 1 else None
                    collected[(bucket, label)].append({
                        "odd": odd, "prob": fair_prob, "book": book_name
                    })
    rows = []
    for (market, outcome), entries in collected.items():
        probs = [x["prob"] for x in entries if x["prob"] is not None]
        odds = [x["odd"] for x in entries]
        rows.append({
            "market": market, "market_ar": _market_ar(market),
            "outcome": outcome, "outcome_ar": _outcome_ar(outcome),
            "avg_odd": sum(odds) / len(odds), "best_odd": max(odds),
            "prob": sum(probs) / len(probs) if probs else None,
            "books": len(entries),
            "bookmakers": sorted({x["book"] for x in entries}),
            "book_odds": sorted([{"book": x["book"], "odd": x["odd"]} for x in entries], key=lambda z: z["odd"], reverse=True),
        })
    rows.sort(key=lambda x: (x["market"].casefold(), x["outcome"].casefold()))
    return {"available": bool(rows), "books": len(bookmakers), "rows": rows,
            "message": "" if rows else "وصل ردّ الأودز لكن لم أتعرف على أسواقه."}


def calculate_value_bets(result: dict, odds_data: dict, min_ev: float = 0.03) -> list[dict]:
    """Match supported bookmaker markets to model probabilities; no inferred bookmaker prices."""
    rows = (odds_data or {}).get("rows", []) or []
    out = []
    probs = result.get("1x2", [None, None, None])
    totals = (result.get("ft") or {}).get("tot", {})
    for row in rows:
        market = str(row.get("market", "")).casefold()
        # # FIX #13/#14: توحيد حالة الأحرف لمطابقة "Home"/"Draw"/"Yes" إلخ.
        outcome = str(row.get("outcome", "")).strip().casefold()
        p = None
        if any(k in market for k in ("match winner", "1x2", "fulltime result")):
            home_name = str(result.get("home", "")).strip().casefold()
            away_name = str(result.get("away", "")).strip().casefold()
            key = "home" if outcome in ("home", home_name) else "away" if outcome in ("away", away_name) else outcome
            p = {"home": probs[0], "draw": probs[1], "away": probs[2]}.get(key)
        elif "over" in outcome or "under" in outcome:
            m = re.search(r"(over|under)\s*([0-9]+(?:\.[0-9]+)?)", outcome)
            if m:
                line = float(m.group(2))
                over_p = sum(float(v) for goals, v in totals.items() if float(goals) > line)
                p = over_p if m.group(1) == "over" else 1.0 - over_p
        elif "both teams" in market or "both teams to score" in market or "btts" in market:
            if outcome in ("yes", "true"):
                p = result.get("btts")
            elif outcome in ("no", "false"):
                p = 1.0 - result.get("btts", 0.0)
        try:
            odd = float(row.get("best_odd"))
        except (TypeError, ValueError):
            continue
        if p is None or not (0 < p < 1) or not math.isfinite(odd) or odd <= 1.0:
            continue
        ev = p * odd - 1.0
        if ev >= min_ev:
            out.append({
                "market": row.get("market_ar", row.get("market", "")),
                "outcome": row.get("outcome_ar", row.get("outcome", "")),
                "probability": p, "best_odd": odd, "ev": ev,
                "edge": (p - (1.0 / odd)), "books": row.get("books", 0),
                "bookmakers": row.get("book_odds", []),
            })
    return sorted(out, key=lambda x: (x["ev"], x["books"]), reverse=True)


# ------------------------------ مصدر مجاني بدون مفتاح: ESPN (واجهة عامة غير رسمية) ------------------------------
ESPN_SITE_BASE = "https://site.api.espn.com/apis/site/v2/sports/soccer"
ESPN_CORE_BASE = "https://sports.core.api.espn.com/v2/sports/soccer/leagues"
ESPN_LEAGUES = {
    "PL": "eng.1", "PD": "esp.1", "BL1": "ger.1", "SA": "ita.1",
    "FL1": "fra.1", "DED": "ned.1", "PPL": "por.1", "CL": "uefa.champions",
    "ELC": "eng.2", "EL1": "eng.3", "EL2": "eng.4", "SD": "esp.2",
    "BL2": "ger.2", "SB": "ita.2", "FL2": "fra.2", "BJL": "bel.1",
    "TSL": "tur.1", "SPL": "sco.1",
}

# # FIX #23: Session مشترك لـESPN لتفادي فتح اتصال TCP جديد لكل طلب من 80+ طلباً في فحص الإصابات.
_ESPN_SESSION = None
_ESPN_SESSION_LOCK = threading.Lock()


def _espn_session():
    global _ESPN_SESSION
    if requests is None:
        raise RuntimeError("مكتبة requests غير مثبتة. نفّذ: py -m pip install requests")
    with _ESPN_SESSION_LOCK:
        if _ESPN_SESSION is None:
            s = requests.Session()
            adapter = requests.adapters.HTTPAdapter(pool_connections=8, pool_maxsize=16)
            s.mount("https://", adapter)
            s.mount("http://", adapter)
            _ESPN_SESSION = s
        return _ESPN_SESSION


class EspnNetworkError(RuntimeError):
    """فشل الاتصال بخوادم ESPN نفسها (DNS/جدار ناري/إنترنت) وليس خطأ في البيانات."""


def _espn_network_message(exc) -> str:
    text = str(exc)
    dns = any(k in text for k in ("getaddrinfo", "NameResolution", "Failed to resolve",
                                  "Name or service not known", "11001"))
    test_url = "https://site.api.espn.com/apis/site/v2/sports/soccer/eng.1/scoreboard"
    if dns:
        return ("تعذر الوصول إلى خوادم ESPN: جهازك لا يستطيع تحويل اسم الموقع إلى عنوان (فشل DNS)، "
                "وهذه ليست مشكلة في البرنامج. جرّب بالترتيب: "
                f"1) افتح هذا الرابط في المتصفح: {test_url} "
                "2) إن لم يفتح: غيّر DNS في ويندوز إلى 1.1.1.1 و8.8.8.8 (إعدادات الشبكة ← خصائص الاتصال ← DNS)، "
                "أو شغّل VPN، أو جرّب شبكة أخرى (هاتف كنقطة اتصال). "
                "3) إن فتح في المتصفح ولم يعمل البرنامج: افحص الجدار الناري/مضاد الفيروسات/البروكسي لـ python.")
    return ("تعذر الاتصال بمصدر ESPN المجاني. تحقق من الإنترنت والجدار الناري أو شغّل VPN، "
            f"ثم أعد المحاولة. (التفصيل التقني: {text[:160]})")


def _espn_hosts(url: str) -> list:
    """عنوان site.api ثم نظيره site.web.api كاحتياط إن كان أحدهما محجوباً."""
    if "://site.api.espn.com/" in url:
        return [url, url.replace("://site.api.espn.com/", "://site.web.api.espn.com/")]
    return [url]


def _espn_get(url: str, params: Optional[dict] = None) -> dict:
    if requests is None:
        raise RuntimeError("مكتبة requests غير مثبتة. نفّذ: py -m pip install requests")
    response, last_exc = None, None
    session = _espn_session()  # # FIX #23: استخدام الجلسة المشتركة
    for candidate in _espn_hosts(url):
        try:
            response = session.get(candidate, params=params, timeout=15,
                                   headers={"User-Agent": "Mozilla/5.0", "Accept": "application/json"})
            break
        except requests.RequestException as exc:
            last_exc = exc
    if response is None:
        raise EspnNetworkError(_espn_network_message(last_exc))
    if response.status_code in (204, 404):
        return {}
    if response.status_code in (401, 403):
        raise RuntimeError(f"ESPN رفض الطلب ({response.status_code}). جرّب لاحقاً أو شغّل VPN.")
    response.raise_for_status()
    try:
        data = response.json()
    except ValueError as exc:
        raise RuntimeError("ردّ ESPN ليس JSON صالحاً.") from exc
    return data if isinstance(data, dict) else {}


def _dig(node, *path):
    for key in path:
        if not isinstance(node, dict):
            return None
        node = node.get(key)
    return node


def _to_decimal(value) -> Optional[float]:
    """يحوّل أودز أمريكية (+150 / -120) أو كسرية (5/2) أو عشرية إلى عشرية."""
    if value is None or isinstance(value, bool):
        return None
    text = str(value).strip()
    if not text or text.upper() in ("N/A", "NA", "-", "—", "OFF"):
        return None
    if text.upper() in ("EVEN", "EVENS", "EV"):
        return 2.0
    try:
        if "/" in text:
            a, b = text.split("/", 1)
            return 1.0 + float(a) / float(b)
        number = float(text.replace("+", ""))
    except (ValueError, ZeroDivisionError):
        return None
    if not math.isfinite(number) or number == 0:
        return None
    if text.startswith(("+", "-")) or abs(number) >= 100:      # صيغة أمريكية
        return 1.0 + number / 100.0 if number > 0 else 1.0 + 100.0 / abs(number)
    return number if number > 1.0 else None                  # صيغة عشرية


def _espn_side_price(entry: dict, side: str) -> Optional[float]:
    for phase in ("close", "current", "open"):
        price = _to_decimal(_dig(entry, "moneyline", side, phase, "odds"))
        if price:
            return price
    team_key = {"home": "homeTeamOdds", "away": "awayTeamOdds", "draw": "drawOdds"}[side]
    for candidate in (_dig(entry, team_key, "moneyLine"),
                      _dig(entry, team_key, "current", "moneyLine", "american"),
                      _dig(entry, team_key, "current", "moneyLine", "value"),
                      _dig(entry, team_key, "moneyline")):
        price = _to_decimal(candidate)
        if price:
            return price
    return None


def _espn_total(entry: dict):
    for phase in ("close", "current", "open"):
        over, under = _dig(entry, "total", "over", phase), _dig(entry, "total", "under", phase)
        if isinstance(over, dict) and isinstance(under, dict):
            m = re.search(r"(\d+(?:\.\d+)?)", str(over.get("line") or under.get("line") or ""))
            po, pu = _to_decimal(over.get("odds")), _to_decimal(under.get("odds"))
            if m and po and pu:
                return float(m.group(1)), po, pu
    try:
        line = float(entry.get("overUnder"))
    except (TypeError, ValueError):
        return None
    po, pu = _to_decimal(entry.get("overOdds")), _to_decimal(entry.get("underOdds"))
    return (line, po, pu) if po and pu else None


def _espn_entry_markets(entry: dict) -> dict:
    """سعر 1X2 وخط الأهداف لشركة واحدة بصيغة {سوق: [(اختيار, أودز عشري)]}."""
    markets = {}
    h, d, a = (_espn_side_price(entry, s) for s in ("home", "draw", "away"))
    if h and d and a:
        markets["Match Winner"] = [("Home", h), ("Draw", d), ("Away", a)]
    total = _espn_total(entry)
    if total:
        line, po, pu = total
        markets[f"Goals Over/Under | {line:g}"] = [(f"Over {line:g}", po), (f"Under {line:g}", pu)]
    return markets


def _aggregate_odds(book_markets: list) -> dict:
    """يجمع أسواق عدة شركات (بعد إزالة الهامش) بنفس شكل _parse_site_odds."""
    collected = defaultdict(list)
    for book_name, markets in book_markets:
        for bucket, outcomes in markets.items():
            raw = [1.0 / odd for _, odd in outcomes]
            total = sum(raw)
            for (label, odd), implied in zip(outcomes, raw):
                fair = implied / total if total > 0 and len(outcomes) > 1 else None
                collected[(bucket, label)].append({"odd": odd, "prob": fair, "book": book_name})
    rows = []
    for (market, outcome), entries in collected.items():
        probs = [x["prob"] for x in entries if x["prob"] is not None]
        odds = [x["odd"] for x in entries]
        rows.append({
            "market": market, "market_ar": _market_ar(market),
            "outcome": outcome, "outcome_ar": _outcome_ar(outcome),
            "avg_odd": sum(odds) / len(odds), "best_odd": max(odds),
            "prob": sum(probs) / len(probs) if probs else None,
            "books": len(entries), "bookmakers": sorted({x["book"] for x in entries}),
            "book_odds": sorted([{"book": x["book"], "odd": x["odd"]} for x in entries], key=lambda z: z["odd"], reverse=True),
        })
    rows.sort(key=lambda x: (x["market"].casefold(), x["outcome"].casefold()))
    books = len({name for name, markets in book_markets if markets})
    return {"available": bool(rows), "books": books, "rows": rows,
            "message": "" if rows else
            "لم تتوفر أودز لهذه المباراة في ESPN؛ غالباً تُنشر قبل المباراة بيوم أو يومين، وقد لا تغطي كل الدوريات."}


def _espn_event_for(events: list, home: str, away: str):
    best = None
    for ev in events:
        comp = (ev.get("competitions") or [{}])[0]
        names = {"home": [], "away": []}
        for c in comp.get("competitors") or []:
            side = c.get("homeAway")
            team = c.get("team") or {}
            if side in names:
                names[side] = [n for n in (team.get("displayName"), team.get("name"),
                                           team.get("shortDisplayName")) if n]
        if not names["home"] or not names["away"]:
            continue
        hs = max(_team_similarity(home, n) for n in names["home"])
        as_ = max(_team_similarity(away, n) for n in names["away"])
        cand = (min(hs, as_), hs + as_, ev, comp, names["home"][0], names["away"][0])
        if best is None or cand[:2] > best[:2]:
            best = cand
    return best if best and best[0] >= 0.66 else None


def _espn_find_event(slug: str, home: str, away: str, match_date: str):
    if _is_auto_date(match_date):
        today = date.today()
        end = today + timedelta(days=14)
        attempts = [f"{today:%Y%m%d}-{end:%Y%m%d}", None] + \
                   [f"{today + timedelta(days=i):%Y%m%d}" for i in range(0, 8)]
        label = "المباريات القادمة"
    else:
        try:
            day = datetime.strptime(match_date, "%Y-%m-%d").date()
        except ValueError as exc:
            raise ValueError("تاريخ المباراة يجب أن يكون بالشكل YYYY-MM-DD أو «تلقائي».") from exc
        attempts = [f"{day:%Y%m%d}"]
        label = match_date
    last_error, seen = None, []
    for dates in attempts:
        params = {"limit": 300}
        if dates:
            params["dates"] = dates
        try:
            data = _espn_get(f"{ESPN_SITE_BASE}/{slug}/scoreboard", params)
        except EspnNetworkError:
            raise
        except RuntimeError as exc:
            last_error = exc
            continue
        events = data.get("events") or []
        found = _espn_event_for(events, home, away)
        if found:
            league_name = ((data.get("leagues") or [{}])[0]).get("name", "")
            return found, league_name
        seen.extend(events)
    if last_error and not seen:
        raise last_error
    examples = []
    for ev in seen[:4]:
        examples.append(ev.get("name") or ev.get("shortName") or "")
    suffix = f" مباريات متاحة: {'، '.join(x for x in examples if x)}." if examples else ""
    raise RuntimeError(f"لم أجد مباراة {home} × {away} ({label}) في ESPN. "
                       "تحقق من الدوري واسمَي الفريقين (صاحب الأرض أولاً) أو أدخل التاريخ يدوياً." + suffix)


def _espn_collect_entries(slug: str, event_id: str, comp: dict) -> list:
    """أودز المباراة: من اللوحة أولاً، ثم واجهة core، ثم summary."""
    def books_from(entries):
        out = []
        for entry in entries or []:
            if not isinstance(entry, dict):
                continue
            name = _dig(entry, "provider", "name") or "ESPN"
            markets = _espn_entry_markets(entry)
            if markets:
                out.append((name, markets))
        return out

    books = books_from(comp.get("odds"))
    if books:
        return books
    comp_id = comp.get("id") or event_id
    try:
        core = _espn_get(f"{ESPN_CORE_BASE}/{slug}/events/{event_id}/competitions/{comp_id}/odds")
        books = books_from(core.get("items"))
        if books:
            return books
    except Exception:
        pass
    try:
        summary = _espn_get(f"{ESPN_SITE_BASE}/{slug}/summary", {"event": event_id})
        books = books_from(summary.get("pickcenter") or summary.get("odds"))
    except Exception:
        books = []
    return books


def fetch_espn_match_data(league_code: str, home: str, away: str, match_date: str) -> dict:
    """يجلب أودز المباراة من ESPN مجاناً وبدون مفتاح."""
    slug = ESPN_LEAGUES.get(league_code)
    if not slug:
        raise RuntimeError("لا يوجد ربط ESPN لهذا الدوري حالياً.")
    (_, _, ev, comp, h_name, a_name), league_name = _espn_find_event(slug, home, away, match_date)
    event_id = str(ev.get("id") or comp.get("id") or "")
    books = _espn_collect_entries(slug, event_id, comp)
    odds = _aggregate_odds(books)
    return {
        "fixture": {"id": event_id, "date": ev.get("date", ""), "league": league_name,
                    "home": h_name, "away": a_name, "season": ""},
        "predictions": {"available": False,
                        "message": "المصدر المجاني (ESPN) يوفر الأودز فقط؛ توقعات المواقع تتطلب مفتاح API-Football."},
        "odds": odds,
        "provider": "ESPN (مجاني بدون مفتاح)",
    }


def _fetch_api_sports_match_data(api_key: str, league_code: str, home: str, away: str,
                              match_date: str) -> dict:
    """يجلب المباراة مرة واحدة ثم يطلب توقعات المزود والأودز لنفس fixture ID."""
    fixture = _find_api_fixture(api_key, league_code, home, away, match_date)
    fixture_id = fixture["id"]
    prediction_raw = _api_sports_get("predictions", {"fixture": fixture_id}, api_key)
    odds_raw = _api_sports_get("odds", {"fixture": fixture_id}, api_key)
    return {
        "fixture": fixture,
        "predictions": _parse_site_predictions(prediction_raw),
        "odds": _parse_site_odds(odds_raw),
        "provider": "API-Football / API-Sports",
    }


def fetch_external_match_data(api_key: str, league_code: str, home: str, away: str,
                              match_date: str) -> dict:
    """بدون مفتاح: ESPN المجاني. مع مفتاح: API-Football أولاً ثم ESPN كخطة بديلة."""
    note = ""
    if api_key:
        try:
            return _fetch_api_sports_match_data(api_key, league_code, home, away, match_date)
        except Exception as exc:
            note = f"تعذر API-Football ({exc}) فاستُخدم المصدر المجاني ESPN."
    result = fetch_espn_match_data(league_code, home, away, match_date)
    if note:
        result["fallback_note"] = note
    return result



# ------------------------------ الأسواق واختيار الأفضل ------------------------------

def _market(group: str, name: str, p: float, quality: int, pickable: bool = True,
            meta: Optional[dict] = None) -> dict:
    margin = (100 - quality) / 100.0 * UNCERTAINTY_MARGIN
    return {
        "group": group, "name": name, "p": p,
        "adj": max(0.0, p - margin),       # الاحتمال المحافظ
        "pickable": pickable,
        "tier": tier_of(p),
        # وصف منظَّم للسوق يُستعمل للتحقق من اتجاه التحليل:
        #   res  = مجموعة النتائج التي تحقق السوق (H مضيف، D تعادل، A ضيف)
        #   ou   = ("over"|"under", خط الأهداف)      btts = True/False
        "meta": meta or {},
    }


# ------------------------------ اتجاه التحليل ------------------------------

def model_lean(H: float, D: float, A: float, o25: float, btts: float) -> dict:
    """ميل النموذج نفسه على ثلاثة محاور: الفريق الأقوى، حجم الأهداف، تسجيل الفريقين (None = لا ميل واضح)."""
    side = "H" if H - A >= SIDE_LEAN_GAP else "A" if A - H >= SIDE_LEAN_GAP else None
    goals = "over" if o25 >= GOALS_LEAN else "under" if o25 <= 1 - GOALS_LEAN else None
    both = True if btts >= BTTS_LEAN else False if btts <= 1 - BTTS_LEAN else None
    return {"side": side, "goals": goals, "btts": both}


def analysis_direction(main: Optional[dict], lean: Optional[dict]) -> dict:
    """اتجاه التحليل = ما يحدده الاختيار الرئيسي أولاً، ثم يُكمَّل بميل النموذج في المحاور الأخرى."""
    d = {"side": None, "goals": None, "btts": None}
    if lean:
        d.update({k: lean.get(k) for k in d})
    fixed = None
    meta = (main or {}).get("meta") or {}
    res = meta.get("res")
    if res is not None:
        if res in (frozenset("H"), frozenset("HD")):
            d["side"], fixed = "H", "side"
        elif res in (frozenset("A"), frozenset("AD")):
            d["side"], fixed = "A", "side"
        elif res == frozenset("D"):
            d["side"], fixed = "D", "side"
        # 12 (أحدهما يفوز): لا يحدد فريقاً، فيبقى ميل النموذج هو المرجع.
    if meta.get("ou") and meta.get("scope") == "ft":
        d["goals"], fixed = meta["ou"][0], "goals"
    if "btts" in meta:
        d["btts"], fixed = meta["btts"], "btts"
    # انسجام المحاور: «أهداف أقل» لا تجتمع مع «كلاهما يسجل: نعم» (لا يبقى إلا 1-1).
    if d["goals"] == "under" and d["btts"] is True:
        if fixed == "btts":
            d["goals"] = None
        else:
            d["btts"] = None
    return d


def is_aligned(m: dict, direction: dict, strict: bool) -> bool:
    """هل السوق في اتجاه التحليل؟
    strict=True : يجب أن يدعم السوق اتجاهاً محدداً في محوره (يُستعمل للاختيار بأودز عالية).
    strict=False: يكفي ألا يعاكس الاتجاه (يُستعمل للبدائل)."""
    meta = m.get("meta") or {}
    res = meta.get("res")
    if res is not None:
        side = direction.get("side")
        if side is None:
            if strict:
                return False
        elif side == "D":
            if ("D" not in res) if not strict else (res != frozenset("D")):
                return False
        else:
            opp = "A" if side == "H" else "H"
            if opp in res or (strict and side not in res):
                return False
    if "ou" in meta:
        g = direction.get("goals")
        if g is None:
            if strict:
                return False
        elif meta["ou"][0] != g:
            return False
    if "btts" in meta:
        b = direction.get("btts")
        if b is None:
            if strict:
                return False
        elif meta["btts"] != b:
            return False
    return True


def direction_label(direction: dict, home: str, away: str) -> str:
    parts = []
    side = direction.get("side")
    if side == "H":
        parts.append(f"فوز {home}")
    elif side == "A":
        parts.append(f"فوز {away}")
    elif side == "D":
        parts.append("التعادل")
    if direction.get("goals") == "over":
        parts.append("أهداف أكثر")
    elif direction.get("goals") == "under":
        parts.append("أهداف أقل")
    if direction.get("btts") is True:
        parts.append("تسجيل الفريقين")
    elif direction.get("btts") is False:
        parts.append("عدم تسجيل أحد الفريقين")
    return " + ".join(parts)


def choose_pick(markets: list[dict], quality: int, min_games: int, lean: Optional[dict] = None) -> dict:
    """يعيد {'pick': سوق أو None، 'reason': نص، 'alts': [أسواق بديلة]}."""
    candidates = [m for m in markets if m["pickable"]]
    best_by_group: dict[str, dict] = {}
    for m in candidates:
        cur = best_by_group.get(m["group"])
        if cur is None or m["adj"] > cur["adj"]:
            best_by_group[m["group"]] = m
    ranked = sorted(best_by_group.values(), key=lambda m: m["adj"], reverse=True)
    top = ranked[0] if ranked else None

    if quality < PICK_MIN_QUALITY:
        return {"pick": None, "alts": [], "best_seen": top,
                "reason": f"البيانات ضعيفة (جودة {quality}/100، الحد الأدنى {PICK_MIN_QUALITY}). "
                          "لا يُنصح بأي اختيار."}
    if min_games < PICK_MIN_GAMES:
        return {"pick": None, "alts": [], "best_seen": top,
                "reason": f"عينة أحد الفريقين صغيرة ({min_games} مباريات، الحد الأدنى {PICK_MIN_GAMES})."}
    if top is None or top["adj"] < PICK_MIN_PROB:
        seen = f"{top['adj'] * 100:.1f}%" if top else "—"
        return {"pick": None, "alts": [], "best_seen": top,
                "reason": f"لا يوجد سوق بأفضلية كافية: أعلى احتمال محافظ {seen} "
                          f"أقل من الحد {PICK_MIN_PROB * 100:.0f}%."}
    # البدائل: أفضل سوق من كل مجموعة أخرى بشرط ألا يعاكس اتجاه الاختيار الرئيسي.
    direction = analysis_direction(top, lean)
    alt_by_group: dict[str, dict] = {}
    for m in candidates:
        if m is top or m["group"] == top["group"] or not is_aligned(m, direction, strict=False):
            continue
        cur = alt_by_group.get(m["group"])
        if cur is None or m["adj"] > cur["adj"]:
            alt_by_group[m["group"]] = m
    alts = sorted((m for m in alt_by_group.values() if m["adj"] >= PICK_MIN_PROB),
                  key=lambda m: m["adj"], reverse=True)[:3]
    return {"pick": top, "alts": alts, "best_seen": top, "reason": "", "direction": direction}


def _market_ext_key(m: dict):
    """يربط سوق النموذج بسوق الأودز الخارجي: (اسم السوق, الاختيار) بحروف صغيرة."""
    name, group = m["name"], m["group"]
    if group == "النتيجة 1X2":
        if name.startswith("1 "):
            return ("match winner", "home")
        if name.startswith("X "):
            return ("match winner", "draw")
        if name.startswith("2 "):
            return ("match winner", "away")
    if group == "الفرصة المزدوجة":
        if name.startswith("1X"):
            return ("double chance", "home/draw")
        if name.startswith("X2"):
            return ("double chance", "draw/away")
        if name.startswith("12"):
            return ("double chance", "home/away")
    if group == "الأهداف":
        mt = re.match(r"(أكثر|أقل) من ([0-9.]+) هدف", name)
        if mt:
            side = "over" if mt.group(1) == "أكثر" else "under"
            return (f"goals over/under | {mt.group(2)}", f"{side} {mt.group(2)}")
    if group == "تسجيل الفريقين":
        return ("both teams score", "yes" if name.endswith("نعم") else "no")
    return None


def choose_high_odds(r: dict) -> dict:
    """اختيار ثانٍ بأودز أعلى من الاختيار الرئيسي، وفي نفس اتجاه التحليل دائماً.

    مثال: إذا رجّح التحليل فوز فريق وكان أودز اختياره منخفضاً، يُعرض سوق آخر يدعم فوز الفريق نفسه
    (أو الأهداف/تسجيل الفريقين في نفس اتجاه التحليل) بأودز أعلى، ولا يُعرض أبداً فوز الفريق الآخر أو التعادل
    ولا سوق يعاكس اتجاه الاختيار الرئيسي."""
    if r["quality"] < PICK_MIN_QUALITY:
        return {"market": None, "reason": f"البيانات ضعيفة (جودة {r['quality']}/100)؛ لا يُقترح اختيار بأودز عالية."}
    sample = min(r.get("home_games", 0), r.get("away_games", 0))
    if sample < PICK_MIN_GAMES:
        return {"market": None, "reason": f"عينة أحد الفريقين صغيرة ({sample} مباريات)."}
    main = (r.get("pick") or {}).get("pick")
    direction = analysis_direction(main, r.get("lean"))
    label = direction_label(direction, r.get("home", ""), r.get("away", ""))
    if not label:
        return {"market": None, "direction": direction,
                "reason": "لا يوجد اتجاه واضح في التحليل (الفريقان متقاربان ولا ميل للأهداف)، "
                          "فلا يُقترح سوق بأودز عالية قد يعاكس التحليل."}
    pool = [m for m in r["markets"]
            if m["pickable"] and m["adj"] >= HIGH_ODDS_MIN_PROB and m is not main
            and is_aligned(m, direction, strict=True)]
    if not pool:
        return {"market": None, "direction": direction,
                "reason": f"لا يوجد سوق في اتجاه التحليل ({label}) باحتمال ≥ {HIGH_ODDS_MIN_PROB * 100:.0f}%."}
    main_odds = ((main or {}).get("odds") or {}).get("value")
    if main_odds:
        pool = [m for m in pool if m["odds"]["value"] > main_odds]
        if not pool:
            return {"market": None, "direction": direction,
                    "reason": f"لا يوجد سوق في اتجاه التحليل ({label}) بأودز أعلى من الاختيار الرئيسي."}
    if r.get("has_market_odds"):
        # عند توفر أسعار الشركات نقارن بأسعارها فقط حتى لا نخلط أودز السوق بالأودز النموذجية.
        priced = [m for m in pool if (m.get("odds") or {}).get("kind") == "market"]
        pool = priced or pool
    best = max(pool, key=lambda m: (m["odds"]["value"], m["p"]))
    return {"market": best, "direction": direction, "direction_label": label, "reason": ""}


def enrich_result_with_odds(r: dict) -> dict:
    """يضيف لكل سوق أودزه (سعر السوق إن وُجد وإلا أودز النموذج العادلة 1÷p) ثم يحدد اختيار الأودز العالية."""
    rows = (((r.get("external") or {}).get("odds") or {}).get("rows")) or []
    index = {(str(x["market"]).strip().casefold(), str(x["outcome"]).strip().casefold()): x for x in rows}
    has_market = False
    for m in r["markets"]:
        fair = 1.0 / max(m["p"], 0.01)
        # # FIX #15: تخزين المفتاح مرة واحدة (كان يُستدعى مرتين لكل سوق).
        ext_key = _market_ext_key(m)
        row = index.get(ext_key) if ext_key else None
        if row:
            m["odds"] = {"value": row["best_odd"], "avg": row["avg_odd"], "kind": "market",
                         "books": row.get("books", 1)}
            has_market = True
        else:
            m["odds"] = {"value": fair, "kind": "fair"}
        m["fair_odds"] = fair
    r["has_market_odds"] = has_market
    r["high_pick"] = choose_high_odds(r)
    return r


# ------------------------------ محرك التوقع ------------------------------

class FootballModel:
    def __init__(self, matches: list[Match], half_time_share: float = 0.45,
                 half_life_days: float = 180.0, prior_strength: float = 4.0,
                 form_weight: float = 0.08):
        if len(matches) < 20:
            raise ValueError("يلزم 20 مباراة على الأقل لبناء النموذج.")
        self.matches = sorted(matches, key=lambda m: m.played)
        self.fallback_share = clamp(half_time_share, 0.30, 0.65)
        self.form_weight = clamp(form_weight, 0.0, 0.25)
        self.half_life = max(30.0, half_life_days)
        self.prior = max(0.5, prior_strength)
        self.teams = sorted({m.home for m in matches} | {m.away for m in matches})
        self.team_lookup = {t.casefold(): t for t in self.teams}
        self._fit()

    # ---- التدريب ----
    def _fit(self):
        today = date.today()
        sums = defaultdict(lambda: defaultdict(float))
        league_h = league_a = weight_sum = 0.0
        weighted_rows = []
        for m in self.matches:
            age = max(0, (today - m.played).days)
            w = 0.5 ** (age / self.half_life)
            weighted_rows.append((m, w))
            league_h += w * m.hg
            league_a += w * m.ag
            weight_sum += w
            h, a = sums[m.home], sums[m.away]
            h["home_w"] += w
            h["home_gf"] += w * m.hg
            h["home_ga"] += w * m.ag
            a["away_w"] += w
            a["away_gf"] += w * m.ag
            a["away_ga"] += w * m.hg
            h["w"] += w
            a["w"] += w
            h["pts"] += w * (3 if m.hg > m.ag else 1 if m.hg == m.ag else 0)
            a["pts"] += w * (3 if m.ag > m.hg else 1 if m.hg == m.ag else 0)
            h["games"] += 1
            a["games"] += 1

        if weight_sum <= 0:
            raise ValueError("تعذر حساب متوسطات الدوري.")
        self.avg_home = max(0.2, league_h / weight_sum)
        self.avg_away = max(0.2, league_a / weight_sum)
        self.stats = sums
        self.weighted_rows = weighted_rows
        self.rho = self._estimate_rho()
        self._fit_halves()

    def _fit_halves(self):
        """إذا توفرت بيانات شوط أول كافية تُشتق نسبة الشوط الأول منها فعلياً."""
        rows = [(m, w) for m, w in self.weighted_rows
                if m.hht is not None and m.aht is not None
                and 0 <= m.hht <= m.hg and 0 <= m.aht <= m.ag]
        self.ht_count = len(rows)
        self._ht_real = None
        if len(rows) >= MIN_HT_MATCHES:
            fh_h = sum(w * m.hht for m, w in rows)
            fh_a = sum(w * m.aht for m, w in rows)
            ft_h = sum(w * m.hg for m, w in rows)
            ft_a = sum(w * m.ag for m, w in rows)
            if ft_h > 0 and ft_a > 0:
                self._ht_real = (clamp(fh_h / ft_h, 0.30, 0.65),
                                 clamp(fh_a / ft_a, 0.30, 0.65))

    def half_shares(self):
        """(حصة المضيف، حصة الضيف، المصدر 'actual'|'assumed')."""
        if self._ht_real:
            return self._ht_real[0], self._ht_real[1], "actual"
        return self.fallback_share, self.fallback_share, "assumed"

    def _rate(self, total: float, weight: float, avg: float) -> float:
        # Bayesian shrinkage: الفرق ذات العينة الصغيرة تعود تدريجياً لمتوسط الدوري.
        return (total + self.prior * avg) / (weight + self.prior)

    def _strengths(self, team: str):
        s = self.stats[team]
        h_gf = self._rate(s["home_gf"], s["home_w"], self.avg_home)
        h_ga = self._rate(s["home_ga"], s["home_w"], self.avg_away)
        a_gf = self._rate(s["away_gf"], s["away_w"], self.avg_away)
        a_ga = self._rate(s["away_ga"], s["away_w"], self.avg_home)
        return {
            "home_attack": h_gf / self.avg_home,
            "home_defence": h_ga / self.avg_away,
            "away_attack": a_gf / self.avg_away,
            "away_defence": a_ga / self.avg_home,
            "games": int(s["games"]),
        }

    def _estimate_rho(self):
        # Fit low-score dependence against team-specific expected goals, not league averages.
        # This prevents strong/weak fixtures from being treated as if they had identical lambdas.
        rows = []
        for m, weight in self.weighted_rows:
            hs, aws = self._strengths(m.home), self._strengths(m.away)
            lh = clamp(self.avg_home * hs["home_attack"] * aws["away_defence"], 0.15, 4.5)
            la = clamp(self.avg_away * aws["away_attack"] * hs["home_defence"], 0.15, 4.5)
            base = poisson_pmf(m.hg, lh) * poisson_pmf(m.ag, la)
            if base > 0 and math.isfinite(base):
                rows.append((m.hg, m.ag, lh, la, base, weight))
        if len(rows) < 20:
            return 0.0
        best_rho, best_ll = 0.0, -float("inf")
        candidates = [i / 1000 for i in range(-150, 151, 5)]
        for rho in candidates:
            ll = 0.0
            for hg, ag, lh, la, base, weight in rows:
                prob = base * dc_tau(hg, ag, lh, la, rho)
                if prob <= 0 or not math.isfinite(prob):
                    ll = -float("inf")
                    break
                ll += weight * math.log(prob)
            if ll > best_ll:
                best_ll, best_rho = ll, rho
        # Shrink noisy estimates toward zero for small historical samples.
        return best_rho * min(1.0, len(rows) / 200.0)

    # ---- تحليل الفريق ----
    def _recent(self, team: str, n: int, venue: Optional[str] = None) -> list[dict]:
        """آخر n مباريات للفريق (الأحدث أولاً). venue: 'home' | 'away' | None."""
        out = []
        for m in reversed(self.matches):
            if m.home == team and venue in (None, "home"):
                gf, ga, v, opp = m.hg, m.ag, "home", m.away
            elif m.away == team and venue in (None, "away"):
                gf, ga, v, opp = m.ag, m.hg, "away", m.home
            else:
                continue
            out.append({
                "gf": gf, "ga": ga, "venue": v, "opp": opp, "date": m.played,
                "pts": 3 if gf > ga else 1 if gf == ga else 0,
                "res": "ف" if gf > ga else "ت" if gf == ga else "خ",
            })
            if len(out) >= n:
                break
        return out

    @staticmethod
    def _agg(games: list[dict]) -> Optional[dict]:
        n = len(games)
        if not n:
            return None
        return {
            "n": n,
            "gf": sum(g["gf"] for g in games) / n,
            "ga": sum(g["ga"] for g in games) / n,
            "ppg": sum(g["pts"] for g in games) / n,
            "pts": sum(g["pts"] for g in games),
            "clean": sum(1 for g in games if g["ga"] == 0) / n,
            "failed": sum(1 for g in games if g["gf"] == 0) / n,
            "btts": sum(1 for g in games if g["gf"] > 0 and g["ga"] > 0) / n,
            "over25": sum(1 for g in games if g["gf"] + g["ga"] > 2) / n,
        }

    def team_profile(self, team: str, venue: str) -> dict:
        """ملف تحليلي كامل للفريق. venue = 'home' للمضيف أو 'away' للضيف."""
        s = self.stats[team]
        st = self._strengths(team)
        avg_all = (self.avg_home + self.avg_away) / 2
        tw = s["w"]
        att_all = self._rate(s["home_gf"] + s["away_gf"], tw, avg_all) / avg_all
        def_all = self._rate(s["home_ga"] + s["away_ga"], tw, avg_all) / avg_all
        ppg_all = s["pts"] / tw if tw > 0 else 0.0
        r5 = self._recent(team, 5)
        a5 = self._agg(r5)
        form_index = 0.0
        if a5 and a5["n"] >= 3:
            form_index = clamp((a5["ppg"] - ppg_all) / 3.0, -1.0, 1.0)
        return {
            "team": team, "venue": venue, "games": st["games"],
            "att_home": st["home_attack"], "def_home": st["home_defence"],
            "att_away": st["away_attack"], "def_away": st["away_defence"],
            "att_all": att_all, "def_all": def_all, "ppg_all": ppg_all,
            "last5": r5, "a5": a5,
            "a10": self._agg(self._recent(team, 10)),
            "a_venue": self._agg(self._recent(team, 8, venue)),
            "form_index": form_index,
        }

    def head_to_head(self, home: str, away: str, n: int = 5) -> list[Match]:
        out = []
        for m in reversed(self.matches):
            if {m.home, m.away} == {home, away}:
                out.append(m)
                if len(out) >= n:
                    break
        return out

    # ---- الشبكات الاحتمالية ----
    @staticmethod
    def _grid(lh: float, la: float, n: int, rho: Optional[float] = None):
        g = []
        for i in range(n + 1):
            row = []
            for j in range(n + 1):
                p = poisson_pmf(i, lh) * poisson_pmf(j, la)
                if rho is not None:
                    p *= max(0.01, dc_tau(i, j, lh, la, rho))
                row.append(p)
            g.append(row)
        total = sum(sum(r) for r in g)
        return [[p / total for p in r] for r in g]

    @staticmethod
    def _summarize(grid) -> dict:
        hw = dr = aw = btts = 0.0
        tot = defaultdict(float)
        scores = []
        for i, row in enumerate(grid):
            for j, p in enumerate(row):
                if i > j:
                    hw += p
                elif i == j:
                    dr += p
                else:
                    aw += p
                if i > 0 and j > 0:
                    btts += p
                tot[i + j] += p
                scores.append((p, i, j))
        scores.sort(reverse=True)
        return {"probs": [hw, dr, aw], "btts": btts, "tot": dict(tot), "scores": scores[:10]}

    @staticmethod
    def _over(summary: dict, line: float) -> float:
        return sum(p for t, p in summary["tot"].items() if t > line)

    # ---- التوقع ----
    def predict(self, home: str, away: str, team_context: Optional[dict] = None):
        hkey = self.team_lookup.get(home.casefold())
        akey = self.team_lookup.get(away.casefold())
        if not hkey or not akey:
            missing = home if not hkey else away
            raise ValueError(f"الفريق غير موجود في بيانات هذا الدوري: {missing}")
        if hkey == akey:
            raise ValueError("اختر فريقين مختلفين.")

        hs, aws = self._strengths(hkey), self._strengths(akey)
        ph, pa = self.team_profile(hkey, "home"), self.team_profile(akey, "away")

        base_h = clamp(self.avg_home * hs["home_attack"] * aws["away_defence"], 0.15, 4.5)
        base_a = clamp(self.avg_away * aws["away_attack"] * hs["home_defence"], 0.15, 4.5)

        # تعديل محدود بالفورمة الحديثة (الوزن قابل للضبط ويمكن جعله 0).
        w = self.form_weight
        lam_h = base_h * (1 + w * ph["form_index"]) * (1 - 0.5 * w * pa["form_index"])
        lam_a = base_a * (1 + w * pa["form_index"]) * (1 - 0.5 * w * ph["form_index"])
        lam_h, lam_a = clamp(lam_h, 0.15, 4.5), clamp(lam_a, 0.15, 4.5)

        # تعديلات غيابات ESPN تدخل مباشرة في xG قبل بناء احتمالات المباراة.
        availability = _availability_factors(team_context, hkey, akey)
        lam_h *= availability["home_attack"] * (1.0 + (1.0 - availability["away_defence"]))
        lam_a *= availability["away_attack"] * (1.0 + (1.0 - availability["home_defence"]))
        lam_h, lam_a = clamp(lam_h, 0.15, 4.5), clamp(lam_a, 0.15, 4.5)

        # النتيجة النهائية (Poisson + Dixon-Coles)
        ft = self._summarize(self._grid(lam_h, lam_a, 10, self.rho))

        # الشوطان: نسبة فعلية من البيانات إن وُجدت، وإلا النسبة المفترضة
        sh_h, sh_a, share_src = self.half_shares()
        fh = self._summarize(self._grid(max(0.05, lam_h * sh_h), max(0.05, lam_a * sh_a), 6))
        sh = self._summarize(self._grid(max(0.05, lam_h * (1 - sh_h)),
                                        max(0.05, lam_a * (1 - sh_a)), 6))

        # جودة البيانات (ليست احتمال فوز)
        sample = min(hs["games"], aws["games"])
        recency_days = (date.today() - self.matches[-1].played).days
        quality = 35 + min(30, sample * 1.2) + (15 if recency_days <= 14 else 8 if recency_days <= 45 else 0)
        if len(self.matches) >= 100:
            quality += 10
        quality = int(clamp(quality, 20, 95))
        confidence = ("جودة بيانات مرتفعة" if quality >= 75
                      else "جودة بيانات متوسطة" if quality >= 55 else "بيانات محدودة")

        # الأسواق
        ht_ok = share_src == "actual"
        H, D, A = ft["probs"]
        o15, o25, o35 = (self._over(ft, 1.5), self._over(ft, 2.5), self._over(ft, 3.5))
        mk = lambda g, n, p, pick=True, meta=None: _market(g, n, p, quality, pick, meta)  # noqa: E731
        R = frozenset
        markets = [
            mk("النتيجة 1X2", f"1 — فوز {hkey}", H, meta={"scope": "ft", "res": R("H")}),
            mk("النتيجة 1X2", "X — تعادل", D, meta={"scope": "ft", "res": R("D")}),
            mk("النتيجة 1X2", f"2 — فوز {akey}", A, meta={"scope": "ft", "res": R("A")}),
            mk("الفرصة المزدوجة", f"1X — {hkey} أو تعادل", H + D, meta={"scope": "ft", "res": R("HD")}),
            mk("الفرصة المزدوجة", f"X2 — تعادل أو {akey}", D + A, meta={"scope": "ft", "res": R("DA")}),
            mk("الفرصة المزدوجة", "12 — أحدهما يفوز (بدون تعادل)", H + A, meta={"scope": "ft", "res": R("HA")}),
            mk("الأهداف", "أكثر من 1.5 هدف", o15, meta={"scope": "ft", "ou": ("over", 1.5)}),
            mk("الأهداف", "أقل من 1.5 هدف", 1 - o15, meta={"scope": "ft", "ou": ("under", 1.5)}),
            mk("الأهداف", "أكثر من 2.5 هدف", o25, meta={"scope": "ft", "ou": ("over", 2.5)}),
            mk("الأهداف", "أقل من 2.5 هدف", 1 - o25, meta={"scope": "ft", "ou": ("under", 2.5)}),
            mk("الأهداف", "أكثر من 3.5 هدف", o35, meta={"scope": "ft", "ou": ("over", 3.5)}),
            mk("الأهداف", "أقل من 3.5 هدف", 1 - o35, meta={"scope": "ft", "ou": ("under", 3.5)}),
            mk("تسجيل الفريقين", "كلا الفريقين يسجل — نعم", ft["btts"], meta={"scope": "ft", "btts": True}),
            mk("تسجيل الفريقين", "كلا الفريقين يسجل — لا", 1 - ft["btts"], meta={"scope": "ft", "btts": False}),
        ]
        for label, scope, s in (("الشوط الأول", "h1", fh), ("الشوط الثاني", "h2", sh)):
            hp, dp, ap = s["probs"]
            markets += [
                mk(label, f"{label}: 1 — {hkey}", hp, ht_ok, {"scope": scope, "res": R("H")}),
                mk(label, f"{label}: X — تعادل", dp, ht_ok, {"scope": scope, "res": R("D")}),
                mk(label, f"{label}: 2 — {akey}", ap, ht_ok, {"scope": scope, "res": R("A")}),
                mk(label, f"{label}: أكثر من 0.5 هدف", self._over(s, 0.5), ht_ok,
                   {"scope": scope, "ou": ("over", 0.5)}),
                mk(label, f"{label}: أكثر من 1.5 هدف", self._over(s, 1.5), ht_ok,
                   {"scope": scope, "ou": ("over", 1.5)}),
            ]

        lean = model_lean(H, D, A, o25, ft["btts"])
        pick = choose_pick(markets, quality, sample, lean)

        notes = []
        if share_src == "assumed":
            notes.append("لا توجد بيانات شوط أول كافية؛ نسبة الشوطين مفترضة، لذلك أسواق الشوطين "
                         "لا تدخل في اختيار أفضل رهان.")
        if sample < PICK_MIN_GAMES:
            notes.append("عينة أحد الفريقين صغيرة.")
        if recency_days > 45:
            notes.append(f"آخر مباراة في البيانات قبل {recency_days} يوماً.")
        if team_context and team_context.get("available"):
            notes.append("تم فحص إصابات ESPN؛ الغيابات ذات المركز المعروف دخلت في تعديل الأهداف المتوقعة.")
            if not team_context.get("lineup_confirmed"):
                notes.append("التشكيلة الرسمية غير منشورة في ESPN وقت التحليل؛ لم يتم افتراض أسماء أساسيين.")
            if not availability["details"]:
                notes.append("لم يقدم ESPN إصابات قابلة للتقييم لهذه المباراة؛ لم يُجرَ تعديل إصابات.")
        else:
            notes.append("تعذر تأكيد الإصابات/التشكيلة من ESPN؛ التوقع مبني على الإحصاءات التاريخية فقط.")

        return {
            "home": hkey, "away": akey,
            "lambda_home": lam_h, "lambda_away": lam_a,
            "base_home": base_h, "base_away": base_a,
            "ft": ft, "fh": fh, "sh": sh,
            "1x2": ft["probs"],
            "over15": o15, "over25": o25, "over35": o35, "btts": ft["btts"],
            "scores": ft["scores"],
            "half_shares": (sh_h, sh_a), "share_src": share_src, "ht_count": self.ht_count,
            "markets": markets, "pick": pick, "lean": lean,
            "ph": ph, "pa": pa, "h2h": self.head_to_head(hkey, akey),
            "form_weight": w,
            "home_games": hs["games"], "away_games": aws["games"],
            "rho": self.rho, "quality": quality, "confidence": confidence,
            "notes": notes,
            "availability": team_context or {"available": False},
            "availability_factors": availability,
        }


# ------------------------------ الواجهة ------------------------------

class FlowFrame(tk.Frame):
    """إطار يُعيد ترتيب عناصره في عدة أسطر (من اليمين لليسار) حسب العرض المتاح،
    فلا تُقطع الحقول والأزرار عند تصغير النافذة."""

    def __init__(self, master, bg="#f3f5f8", hgap=6, vgap=6):
        super().__init__(master, bg=bg, height=30, highlightthickness=0, bd=0)
        self._items = []
        self._hgap, self._vgap = hgap, vgap
        self._pending = None
        self.bind("<Configure>", self._schedule)

    def add(self, widget, gap=0):
        self._items.append((widget, gap))
        widget.bind("<Configure>", self._schedule, add="+")
        self._schedule()
        return widget

    def _schedule(self, _event=None):
        if self._pending is None:
            self._pending = self.after_idle(self._relayout)

    def _relayout(self):
        self._pending = None
        width = self.winfo_width()
        if width <= 1 or not self._items:
            return
        x, y, row_h, first = width, 0, 0, True
        for w, gap in self._items:
            ww, wh = w.winfo_reqwidth(), w.winfo_reqheight()
            if not first:
                nx = x - self._hgap - gap
                if nx - ww < 0:               # لا مكان كافٍ: انتقل لسطر جديد
                    y += row_h + self._vgap
                    x, row_h = width, 0
                else:
                    x = nx
            w.place(x=max(0, x - ww), y=y)
            x -= ww
            first = False
            row_h = max(row_h, wh)
        total = y + row_h
        if int(float(str(self.cget("height")))) != total:
            self.configure(height=total)


class PredictorApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.minsize(520, 420)
        self.resizable(True, True)
        self._fullscreen = False
        self._settings_visible = True
        self.configure(bg="#f3f5f8")
        self.model: Optional[FootballModel] = None
        self.matches: list[Match] = []
        self.last_result = None
        self._external_request_id = 0
        self._availability_refresh_attempts = 0
        self.config_data = self._load_config()
        self.prediction_history = self._load_prediction_history()
        self._history_current_id = None
        self._alerted_value_keys = set()
        self._live_previous = {}
        self.alerts_enabled = tk.BooleanVar(value=bool(self.config_data.get("alerts_enabled", True)))
        self._init_window()
        self.api_key = tk.StringVar(value=self.config_data.get("api_key", ""))
        self.api_sports_key = tk.StringVar(value=self.config_data.get("api_sports_key", ""))
        saved_date = str(self.config_data.get("match_date", "")).strip()
        try:
            if datetime.strptime(saved_date, "%Y-%m-%d").date() < date.today():
                saved_date = ""
        except ValueError:
            saved_date = ""
        self.match_date = tk.StringVar(value=saved_date or "تلقائي")
        self.league = tk.StringVar(value=self.config_data.get("league", list(LEAGUES)[0]))
        self.home = tk.StringVar()
        self.away = tk.StringVar()
        self.seasons = tk.IntVar(value=int(self.config_data.get("seasons", 2)))
        self.half_share = tk.DoubleVar(value=float(self.config_data.get("half_share", 0.45)))
        self.form_weight = tk.DoubleVar(value=float(self.config_data.get("form_weight", 0.08)))
        self.status = tk.StringVar(value=f"حمّل الدوري المختار فقط. تُحفظ البيانات بجوار البرنامج: {DATA_DIR}")
        self._style()
        self._build()
        self._enable_clipboard_support()
        self.bind("<F11>", self._toggle_fullscreen)
        self.bind("<Escape>", self._exit_fullscreen)
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(300, self._init_sash)

    # ---- سجل التوقعات وتسوية النتائج ----
    def _load_prediction_history(self):
        try:
            with open(HISTORY_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, list) else []
        except Exception:
            return []

    def _save_prediction_history(self):
        try:
            tmp = HISTORY_PATH + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.prediction_history, f, ensure_ascii=False, indent=2)
            os.replace(tmp, HISTORY_PATH)
        except Exception as exc:
            self.status.set("تعذر حفظ سجل التوقعات: " + str(exc))

    def _record_prediction(self, result, update=False):
        if not update or not self._history_current_id:
            self._history_current_id = uuid.uuid4().hex[:12]
            pick = (result.get("pick") or {}).get("pick")
            odd = None
            if pick:
                od = pick.get("odds") or {}
                if od.get("kind") == "market":
                    odd = od.get("value")
            row = {
                "id": self._history_current_id,
                "created_at": datetime.now().astimezone().isoformat(timespec="seconds"),
                "home": result.get("home", ""), "away": result.get("away", ""),
                "pick": pick.get("name") if pick else "بدون اختيار",
                "probability": pick.get("p") if pick else None,
                "odds": odd, "status": "pending", "stake": 1.0,
                "profit": None, "actual_score": "",
                "predicted_score": "{}-{}".format(*result.get("scores", [(0,0,0)])[0][1:]),
                "value_bets": [],
            }
            self.prediction_history.append(row)
        else:
            row = next((x for x in reversed(self.prediction_history) if x.get("id") == self._history_current_id), None)
            if row is None:
                return self._record_prediction(result, update=False)
        ext = result.get("external") or {}
        row["value_bets"] = calculate_value_bets(result, ext.get("odds") or {}, 0.03)
        if ext.get("fixture"):
            row["fixture_date"] = ext["fixture"].get("date", "")
        self._save_prediction_history()

    def show_history(self):
        win = tk.Toplevel(self)
        win.title("سجل التوقعات والأرباح")
        win.geometry("980x520")
        win.minsize(680, 340)
        top = ttk.Frame(win, padding=8); top.pack(fill="x")
        ttk.Label(top, text="سجل التوقعات — وحدة الرهان = قيمة افتراضية قابلة للتعديل عند التسوية").pack(side="right")
        cols = ("date", "match", "pick", "status", "score", "profit")
        tree = ttk.Treeview(win, columns=cols, show="headings", height=13)
        labels = {"date":"التاريخ", "match":"المباراة", "pick":"الاختيار", "status":"الحالة", "score":"النتيجة الفعلية", "profit":"الربح/الخسارة"}
        widths = {"date":150, "match":220, "pick":260, "status":90, "score":110, "profit":120}
        for c in cols:
            tree.heading(c, text=labels[c]); tree.column(c, width=widths[c], anchor="center")
        tree.pack(fill="both", expand=True, padx=8, pady=6)
        def refresh():
            tree.delete(*tree.get_children())
            for item in reversed(self.prediction_history):
                profit = item.get("profit")
                tree.insert("", "end", iid=item.get("id"), values=(
                    str(item.get("created_at", ""))[:16],
                    f"{item.get('home','')} × {item.get('away','')}", item.get("pick", "—"),
                    {"pending":"معلّق", "won":"فوز", "lost":"خسارة", "void":"ملغى"}.get(item.get("status"), item.get("status")),
                    item.get("actual_score", "—"), "—" if profit is None else f"{profit:+.2f}"))
        refresh()
        actions = ttk.Frame(win, padding=8); actions.pack(fill="x")
        def settle():
            sel = tree.selection()
            if not sel:
                messagebox.showinfo("التسوية", "اختر توقعاً من السجل أولاً.", parent=win); return
            item = next((x for x in self.prediction_history if x.get("id") == sel[0]), None)
            if not item: return
            state = simpledialog.askstring("تسوية التوقع", "أدخل W للفوز أو L للخسارة أو V للإلغاء:", parent=win)
            if not state: return
            state = state.strip().upper()
            if state not in ("W", "L", "V"):
                messagebox.showwarning("قيمة غير صحيحة", "استخدم W أو L أو V.", parent=win); return
            stake = simpledialog.askfloat("قيمة الرهان", "قيمة الرهان بوحدات الحساب:", initialvalue=float(item.get("stake", 1.0)), minvalue=0.01, parent=win)
            if stake is None: return
            odd = item.get("odds")
            if state == "W" and not odd:
                odd = simpledialog.askfloat("الأودز الفعلية", "أدخل الأودز العشرية التي لعبت بها:", minvalue=1.01, parent=win)
                if odd is None: return
            score = simpledialog.askstring("النتيجة الفعلية", "النتيجة (مثال 2-1)، أو اتركها فارغة:", parent=win) or ""
            item.update({"status": {"W":"won", "L":"lost", "V":"void"}[state], "stake": stake, "actual_score": score, "odds": odd})
            item["profit"] = (stake * (float(odd) - 1.0)) if state == "W" else (-stake if state == "L" else 0.0)
            self._save_prediction_history(); refresh()
        ttk.Button(actions, text="تسوية التوقع المحدد", command=settle).pack(side="right")
        ttk.Button(actions, text="تحديث", command=refresh).pack(side="right", padx=6)
        settled = [x for x in self.prediction_history if x.get("profit") is not None]
        net = sum(float(x.get("profit", 0)) for x in settled)
        staked = sum(float(x.get("stake", 0)) for x in settled if x.get("status") in ("won", "lost"))
        ttk.Label(actions, text=f"الصافي: {net:+.2f} وحدة | ROI: {(net/staked*100 if staked else 0):.1f}% | تسويات: {len(settled)}").pack(side="left")

    def _notify_value_bets(self, result):
        if not self.alerts_enabled.get(): return
        ext = result.get("external") or {}
        bets = calculate_value_bets(result, ext.get("odds") or {}, 0.05)
        if not bets: return
        key = (result.get("home"), result.get("away"), bets[0]["market"], bets[0]["outcome"])
        if key in self._alerted_value_keys: return
        self._alerted_value_keys.add(key)
        best = bets[0]
        try: self.bell()
        except tk.TclError: pass
        self.status.set(f"تنبيه Value Bet: {best['market']} — {best['outcome']} | EV {best['ev']:+.1%}")
        messagebox.showinfo("تنبيه قيمة متوقعة",
            f"ظهرت فرصة حسابية تستحق المراجعة:\n{result.get('home')} × {result.get('away')}\n"
            f"{best['market']} — {best['outcome']}\nاحتمال النموذج: {best['probability']:.1%}\n"
            f"أفضل أودز: {best['best_odd']:.2f}\nالعائد المتوقع النظري: {best['ev']:+.1%}\n\n"
            "هذه ليست توصية أو ضمان ربح؛ تعتمد على صحة النموذج والسعر وقت التنفيذ.")

    # ---- الإعدادات ----
    def _load_config(self):
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            # # FIX #31: قد يكون الملف قائمة أو نصاً بسبب تلف؛ أعِد dict فقط.
            return data if isinstance(data, dict) else {}
        except Exception:
            return {}

    def _save_config(self):
        try:
            data = {
                "api_key": self.api_key.get().strip(),
                "api_sports_key": self.api_sports_key.get().strip(),
                "match_date": self.match_date.get().strip(),
                "league": self.league.get(),
                "seasons": self.seasons.get(),
                "half_share": self.half_share.get(),
                "form_weight": self.form_weight.get(),
                "alerts_enabled": self.alerts_enabled.get(),
                "window_size": f"{self.winfo_width()}x{self.winfo_height()}",
            }
            with open(CONFIG_PATH, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _style(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure("TFrame", background="#f3f5f8")
        style.configure("TLabelframe", background="#ffffff", borderwidth=1)
        style.configure("TLabelframe.Label", background="#ffffff", foreground="#182230",
                        font=("Segoe UI", 10, "bold"))
        style.configure("TLabel", background="#f3f5f8", foreground="#182230",
                        font=("Segoe UI", 10))
        style.configure("Header.TLabel", font=("Segoe UI", 16, "bold"),
                        foreground="#17324d", background="#f3f5f8")
        style.configure("TButton", font=("Segoe UI", 10), padding=5)
        style.configure("Accent.TButton", font=("Segoe UI", 10, "bold"),
                        background="#087f5b", foreground="white", padding=(12, 7))
        style.map("Accent.TButton", background=[("active", "#066649"), ("disabled", "#9bb8ad")])
        style.configure("Treeview", background="#ffffff", fieldbackground="#ffffff", rowheight=30)
        style.map("Treeview", background=[("selected", "#d8eee6")], foreground=[("selected", "#123b2e")])
        style.configure("Treeview", font=("Segoe UI", 10), rowheight=27)
        style.configure("Treeview.Heading", font=("Segoe UI", 10, "bold"))
        style.configure("TNotebook.Tab", font=("Segoe UI", 10, "bold"), padding=(10, 5))

    def _build(self):
        BG = "#f3f5f8"
        outer = ttk.Frame(self, padding=(10, 8))
        outer.pack(fill="both", expand=True)

        # الشريط العلوي: العنوان + أزرار التحكم بالنافذة
        head = ttk.Frame(outer)
        head.pack(fill="x")
        ttk.Label(head, text="محلل كرة القدم PRO MAX", style="Header.TLabel").pack(side="right")
        ttk.Button(head, text="⛶ ملء الشاشة (F11)", command=self._toggle_fullscreen).pack(side="left")
        self.toggle_btn = ttk.Button(head, text="▲ إخفاء مصادر البيانات", command=self._toggle_settings)
        self.toggle_btn.pack(side="left", padx=6)
        sub = ttk.Label(outer, text="Poisson • Dixon-Coles • ESPN مباشر/إصابات/أخبار • ذاكرة 24 ساعة • اختبار زمني • دوريات موسعة • أودز ومقارنة الأسواق",
                        foreground="#526579", anchor="e", justify="right")
        sub.pack(fill="x", pady=(2, 6))
        self._autowrap(sub)

        # اختيار المباراة (ظاهر دائماً)
        matchbox = ttk.LabelFrame(outer, text="اختيار المباراة", padding=8)
        matchbox.pack(fill="x", pady=(0, 4))
        mrow = FlowFrame(matchbox, bg=BG)
        mrow.pack(fill="x")

        def make_home(p):
            self.home_combo = ttk.Combobox(p, textvariable=self.home, width=26)
            return self.home_combo

        def make_away(p):
            self.away_combo = ttk.Combobox(p, textvariable=self.away, width=26)
            return self.away_combo

        self._field(mrow, "صاحب الأرض:", make_home)
        self._field(mrow, "الفريق الضيف:", make_away)
        mrow.add(ttk.Button(mrow, text="حلّل المباراة", style="Accent.TButton",
                            command=self.predict), 10)
        self.data_label = ttk.Label(matchbox, text="لم يتم تحميل بيانات بعد.", foreground="#65758b",
                                    anchor="e", justify="right")
        self.data_label.pack(fill="x", pady=(6, 0))
        self._autowrap(self.data_label)

        # الشريط السفلي (يُحجز قبل اللوحات كي لا يختفي أبداً)
        bottom = ttk.Frame(outer)
        bottom.pack(side="bottom", fill="x", pady=(6, 0))
        ttk.Button(bottom, text="تصدير آخر تحليل CSV", command=self.export_result).pack(side="left")
        ttk.Button(bottom, text="سجل التوقعات والأرباح", command=self.show_history).pack(side="left", padx=6)
        ttk.Button(bottom, text="مسح النتائج", command=self.clear_result).pack(side="left", padx=6)
        status_lbl = ttk.Label(bottom, textvariable=self.status, foreground="#526579",
                               anchor="e", justify="right", wraplength=400)
        status_lbl.pack(side="right", fill="x", expand=True)
        bottom.bind("<Configure>", lambda e: status_lbl.config(wraplength=max(150, e.width - 340)))

        # لوحة قابلة لتغيير الحجم: [مصادر البيانات] | [النتائج]
        self.paned = ttk.PanedWindow(outer, orient="vertical")
        self.paned.pack(fill="both", expand=True)

        # ---- اللوحة العلوية (قابلة للتمرير والإخفاء) ----
        self.settings_pane = ttk.Frame(self.paned)
        self._sc = tk.Canvas(self.settings_pane, bg=BG, highlightthickness=0, height=200,
                             yscrollincrement=20)
        vsb = ttk.Scrollbar(self.settings_pane, orient="vertical", command=self._sc.yview)
        self._sc.configure(yscrollcommand=vsb.set)
        vsb.pack(side="left", fill="y")
        self._sc.pack(side="right", fill="both", expand=True)
        top = ttk.Frame(self._sc)
        self.settings_inner = top
        win = self._sc.create_window((0, 0), window=top, anchor="nw")
        top.bind("<Configure>", lambda e: self._sc.configure(scrollregion=self._sc.bbox("all")))
        self._sc.bind("<Configure>", lambda e: self._sc.itemconfigure(win, width=e.width))
        self._bind_wheel()

        # 1) المصدر
        source = ttk.LabelFrame(top, text="1) مصدر البيانات", padding=8)
        source.pack(fill="x", pady=3)
        row1 = FlowFrame(source, bg=BG)
        row1.pack(fill="x")
        self._field(row1, "مفتاح football-data.org:",
                    lambda p: ttk.Entry(p, textvariable=self.api_key, show="*", width=34))
        row1.add(ttk.Button(row1, text="تحميل الدوري", command=self.load_api), 6)
        row1.add(ttk.Button(row1, text="استيراد CSV", command=self.import_csv), 6)
        row1.add(ttk.Button(row1, text="تحديث إجباري", command=lambda: self.load_api(force=True)), 6)
        row1.add(ttk.Button(row1, text="مباريات مباشرة ESPN", command=self.show_live), 6)
        row1.add(ttk.Button(row1, text="فحص الإصابات ESPN", command=self.show_team_context), 6)
        row1.add(ttk.Button(row1, text="اختبار الدقة التاريخية", command=self.backtest), 6)
        row2 = FlowFrame(source, bg=BG)
        row2.pack(fill="x", pady=(6, 0))
        self._field(row2, "الدوري:", lambda p: ttk.Combobox(
            p, textvariable=self.league, values=list(LEAGUES), state="readonly", width=24))
        self._field(row2, "المواسم السابقة:", lambda p: ttk.Spinbox(
            p, from_=0, to=5, textvariable=self.seasons, width=5), 10)
        self._field(row2, "حصة الشوط الأول (احتياطية):", lambda p: ttk.Spinbox(
            p, from_=0.30, to=0.65, increment=0.01, textvariable=self.half_share, width=6), 10)
        self._field(row2, "وزن الفورمة (0 = إيقاف):", lambda p: ttk.Spinbox(
            p, from_=0.0, to=0.25, increment=0.01, textvariable=self.form_weight, width=6), 10)
        self._note(source, "المفتاح اختياري عند استيراد CSV. حصة الشوط الأول تُستخدم فقط إذا لم تتوفر "
                           "بيانات أشواط فعلية. يُحفظ المفتاح محلياً في ملف إعدادات المستخدم.", pady=(6, 0))

        # مصدر ثانٍ: توقعات مزود خارجي وأودز شركات متعددة
        ext_source = ttk.LabelFrame(top, text="الأودز التلقائية (مجانية بدون مفتاح عبر ESPN)", padding=8)
        ext_source.pack(fill="x", pady=3)
        ext_row = FlowFrame(ext_source, bg=BG)
        ext_row.pack(fill="x")
        self._field(ext_row, "مفتاح API-Football (اختياري):",
                    lambda p: ttk.Entry(p, textvariable=self.api_sports_key, show="*", width=30))
        self._field(ext_row, "التاريخ (تلقائي أو YYYY-MM-DD):",
                    lambda p: ttk.Entry(p, textvariable=self.match_date, width=12), 12)
        ttk.Checkbutton(ext_row, text="تنبيهات Value Bets (EV ≥ 5%)", variable=self.alerts_enabled).pack(side="left", padx=8)
        self._note(ext_source, "يُجلب الأودز تلقائياً بعد كل تحليل من ESPN بدون أي مفتاح، ويُحدَّد موعد المباراة القادمة "
                               "بنفسه عند ترك التاريخ «تلقائي». مفتاح API-Football اختياري لإضافة توقعات المواقع؛", pady=(5, 0), fg=None)
        self._note(ext_source, "ESPN واجهة عامة غير رسمية وقد تتغير أو لا تتوفر أودز بعض المباريات. "
                               "بدون المفتاح لا تظهر «توقعات المواقع» بل الأودز فقط.")

        # ---- لوحة النتائج ----
        results = ttk.LabelFrame(self.paned, text="نتائج التحليل", padding=8)
        self.paned.add(self.settings_pane, weight=0)
        self.paned.add(results, weight=1)

        self.banner = tk.Label(results, text="حلّل مباراة لعرض أفضل اختيار.",
                               font=("Segoe UI", 13, "bold"), bg="#e6eaf0", fg="#34445a",
                               anchor="e", justify="right", padx=12, pady=7)
        self.banner.pack(fill="x")
        self.banner_sub = tk.Label(results, text="", font=("Segoe UI", 10), bg="#ffffff",
                                   fg="#34445a", anchor="e", justify="right", padx=12, pady=3)
        self.banner_sub.pack(fill="x")
        self.banner_hi = tk.Label(results, text="", font=("Segoe UI", 11, "bold"), bg="#ffffff",
                                  fg="#8a4b00", anchor="e", justify="right", padx=12, pady=6)
        self.banner_hi.pack(fill="x", pady=(4, 0))
        self.backtest_label = tk.Label(
            results,
            text="دقة النموذج التاريخية: ستُحسب تلقائياً بعد تحليل المباراة.",
            font=("Segoe UI", 10, "bold"), bg="#edf3fb", fg="#24476b",
            anchor="e", justify="right", padx=12, pady=6
        )
        self.backtest_label.pack(fill="x", pady=(4, 2))
        self.backtest_label.bind(
            "<Configure>",
            lambda e: self.backtest_label.config(wraplength=max(200, e.width - 30))
        )
        for lbl in (self.banner, self.banner_sub, self.banner_hi):
            lbl.bind("<Configure>", lambda e, l=lbl: l.config(wraplength=max(200, e.width - 30)))

        legend = FlowFrame(results, bg="#ffffff", hgap=6, vgap=4)
        legend.pack(fill="x", pady=(2, 6))
        for t in TIERS:
            if t.key == "weak":
                txt = f"{t.label}  <{TIERS[-2].min * 100:.0f}%"
            elif t.key == "strong":
                txt = f"{t.label}  ≥{t.min * 100:.0f}%"
            else:
                upper = TIERS[TIERS.index(t) - 1].min * 100
                txt = f"{t.label}  {t.min * 100:.0f}–{upper:.0f}%"
            legend.add(tk.Label(legend, text=txt, bg=t.bg, fg=t.fg, font=("Segoe UI", 9, "bold"),
                                padx=10, pady=3))

        self.nb = ttk.Notebook(results)
        self.nb.pack(fill="both", expand=True)

        # تبويب الأسواق
        tab1 = ttk.Frame(self.nb)
        self.nb.add(tab1, text="الأسواق والمقارنة")
        cols = ("bar", "level", "adj", "prob", "odds", "market", "group")
        self.tree = ttk.Treeview(tab1, columns=cols, show="headings", selectmode="browse", height=6)
        heads = {"bar": ("المؤشر", 170), "level": ("المستوى", 70), "adj": ("المحافظ", 70),
                 "prob": ("الاحتمال", 70), "odds": ("الأودز", 80), "market": ("السوق", 300), "group": ("المجموعة", 120)}
        for c in cols:
            self.tree.heading(c, text=heads[c][0], anchor="e")
            self.tree.column(c, width=heads[c][1], minwidth=50, anchor="e", stretch=(c == "market"))
        for t in TIERS:
            self.tree.tag_configure(t.key, background=t.bg, foreground=t.fg)
        vs = ttk.Scrollbar(tab1, orient="vertical", command=self.tree.yview)
        hs = ttk.Scrollbar(tab1, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vs.set, xscrollcommand=hs.set)
        tab1.rowconfigure(0, weight=1)
        tab1.columnconfigure(1, weight=1)
        vs.grid(row=0, column=0, sticky="ns")
        self.tree.grid(row=0, column=1, sticky="nsew")
        hs.grid(row=1, column=1, sticky="ew")

        # تبويب الأشواط
        tab2 = ttk.Frame(self.nb)
        self.nb.add(tab2, text="الشوطان والنتيجة النهائية")
        self.txt_halves = self._make_text(tab2)

        # تبويب التحليل العميق
        tab3 = ttk.Frame(self.nb)
        self.nb.add(tab3, text="التحليل العميق")
        self.txt_deep = self._make_text(tab3)

        tab4 = ttk.Frame(self.nb)
        self.nb.add(tab4, text="أودز وتوقعات المواقع")
        self.txt_external = self._make_text(tab4)

        # لوحات احترافية إضافية داخل واجهة Tkinter الحالية
        self.tab_stats = ttk.Frame(self.nb)
        self.nb.add(self.tab_stats, text="📊 الإحصاءات")
        self.stats_canvas = tk.Canvas(self.tab_stats, bg="#ffffff", height=210, highlightthickness=0)
        self.stats_canvas.pack(fill="x", padx=8, pady=8)
        self.stats_summary = ttk.Label(self.tab_stats, text="حلّل مباراة لعرض مؤشرات النموذج.", anchor="e")
        self.stats_summary.pack(fill="x", padx=10, pady=4)

        self.tab_value = ttk.Frame(self.nb)
        self.nb.add(self.tab_value, text="💎 Value Bets")
        self.value_tree = ttk.Treeview(self.tab_value, columns=("market","outcome","prob","odd","ev","book"), show="headings")
        for c, label, width in (("market","السوق",210),("outcome","الاختيار",170),("prob","احتمال النموذج",110),("odd","أفضل أودز",90),("ev","القيمة المتوقعة",110),("book","المصدر",170)):
            self.value_tree.heading(c, text=label); self.value_tree.column(c, width=width, anchor="center")
        self.value_tree.pack(fill="both", expand=True, padx=8, pady=8)
        self.value_note = ttk.Label(self.tab_value, text="تُعرض الفرص عند توفر أودز خارجية؛ القيمة النظرية ليست ضمان ربح.", anchor="e")
        self.value_note.pack(fill="x", padx=8, pady=(0,8))

        self.tab_live = ttk.Frame(self.nb)
        self.nb.add(self.tab_live, text="🔴 المباشر")
        livebar = ttk.Frame(self.tab_live); livebar.pack(fill="x", padx=8, pady=6)
        ttk.Button(livebar, text="تحديث المباريات المباشرة", command=lambda: self._refresh_dashboard_live()).pack(side="right")
        self.live_dashboard_tree = ttk.Treeview(self.tab_live, columns=("home","score","away","clock","stats","status"), show="headings")
        for c,label,width in (("home","المضيف",150),("score","النتيجة",80),("away","الضيف",150),("clock","الدقيقة",75),("stats","الإحصاءات",300),("status","الحالة",100)):
            self.live_dashboard_tree.heading(c,text=label); self.live_dashboard_tree.column(c,width=width,anchor="center")
        self.live_dashboard_tree.pack(fill="both",expand=True,padx=8,pady=8)

        self.tab_goals = ttk.Frame(self.nb)
        self.nb.add(self.tab_goals, text="⚽ الأهداف")
        self.goals_summary = ttk.Label(self.tab_goals, text="تحليل Over/Under وBTTS والنتائج الدقيقة يظهر بعد تحليل مباراة.", anchor="e")
        self.goals_summary.pack(fill="x", padx=10, pady=8)
        self.goals_tree = ttk.Treeview(self.tab_goals, columns=("market","prob","confidence"), show="headings")
        for c,label,width in (("market","السوق",260),("prob","احتمال النموذج",140),("confidence","المؤشر",160)):
            self.goals_tree.heading(c,text=label); self.goals_tree.column(c,width=width,anchor="center")
        self.goals_tree.pack(fill="both",expand=True,padx=8,pady=8)
        self.goals_scores = ttk.Label(self.tab_goals, text="", anchor="e")
        self.goals_scores.pack(fill="x", padx=10, pady=6)

    # ---- دعم النسخ واللصق في جميع حقول الإدخال ----
    def _enable_clipboard_support(self):
        """يوحّد اختصارات الحافظة والقائمة المختصرة لحقول الإدخال القابلة للتحرير."""
        editable_classes = {"Entry", "TEntry", "Spinbox", "TSpinbox",
                            "Combobox", "TCombobox", "Text"}

        def visit(parent):
            for widget in parent.winfo_children():
                try:
                    if widget.winfo_class() in editable_classes:
                        state = str(widget.cget("state")) if "state" in widget.keys() else "normal"
                        if state not in ("disabled", "readonly"):
                            widget.bind("<Control-v>", self._paste_to_widget, add="+")
                            widget.bind("<Control-V>", self._paste_to_widget, add="+")
                            widget.bind("<Shift-Insert>", self._paste_to_widget, add="+")
                            widget.bind("<Button-3>", self._show_edit_menu, add="+")
                    visit(widget)
                except (tk.TclError, AttributeError):
                    continue

        visit(self)

    def _paste_to_widget(self, event):
        widget = event.widget
        try:
            state = str(widget.cget("state")) if "state" in widget.keys() else "normal"
            if state in ("disabled", "readonly"):
                return "break"
            value = self.clipboard_get()
            if isinstance(widget, tk.Text):
                try:
                    widget.delete("sel.first", "sel.last")
                except tk.TclError:
                    pass
                widget.insert("insert", value)
            else:
                try:
                    widget.delete("sel.first", "sel.last")
                except tk.TclError:
                    pass
                widget.insert("insert", value)
            return "break"
        except (tk.TclError, AttributeError):
            return "break"

    def _copy_from_widget(self, widget, cut=False):
        try:
            if isinstance(widget, tk.Text):
                value = widget.get("sel.first", "sel.last")
            else:
                value = widget.selection_get()
            self.clipboard_clear()
            self.clipboard_append(value)
            if cut:
                if isinstance(widget, tk.Text):
                    widget.delete("sel.first", "sel.last")
                else:
                    widget.delete("sel.first", "sel.last")
        except tk.TclError:
            pass

    def _show_edit_menu(self, event):
        widget = event.widget
        try:
            state = str(widget.cget("state")) if "state" in widget.keys() else "normal"
            if state in ("disabled", "readonly"):
                return
            menu = tk.Menu(self, tearoff=0)
            menu.add_command(label="لصق", command=lambda w=widget: self._paste_to_widget(
                type("PasteEvent", (), {"widget": w})()))
            menu.add_command(label="نسخ", command=lambda w=widget: self._copy_from_widget(w, False))
            menu.add_command(label="قص", command=lambda w=widget: self._copy_from_widget(w, True))
            menu.tk_popup(event.x_root, event.y_root)
        except tk.TclError:
            pass
        finally:
            try:
                menu.grab_release()
            except (tk.TclError, UnboundLocalError):
                pass
        return "break"

    # ---- أدوات تخطيط النافذة ----
    def _field(self, flow, text, factory, gap=0):
        """تسمية + حقل في وحدة واحدة لا تنفصل عند التفاف الأسطر."""
        box = tk.Frame(flow, bg=flow["bg"])
        ttk.Label(box, text=text).pack(side="right", padx=(4, 3))
        widget = factory(box)
        widget.pack(side="right", padx=3)
        flow.add(box, gap)
        return box

    def _autowrap(self, label):
        label.config(wraplength=600)
        label.bind("<Configure>", lambda e, l=label: l.config(wraplength=max(150, e.width - 8)))

    def _note(self, parent, text, pady=(0, 0), fg="#65758b"):
        lbl = ttk.Label(parent, text=text, anchor="e", justify="right",
                        **({"foreground": fg} if fg else {}))
        lbl.pack(fill="x", pady=pady)
        self._autowrap(lbl)
        return lbl

    def _init_window(self):
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        w = min(1000, int(sw * 0.82))
        h = min(720, int(sh * 0.80))
        try:  # استرجاع آخر حجم محفوظ إن وُجد
            sw_, sh_ = str(self.config_data.get("window_size", "")).split("x")
            w, h = int(sw_), int(sh_)
        except Exception:
            pass
        w = max(520, min(w, sw - 20))
        h = max(420, min(h, sh - 80))
        x = max(0, (sw - w) // 2)
        y = max(0, (sh - h) // 3)
        self.geometry(f"{w}x{h}+{x}+{y}")
        # يبدأ مكبّراً مع بقاء أزرار التصغير والاستعادة وتغيير الحجم متاحة
        try:
            self.state("zoomed")
        except tk.TclError:
            try: self.attributes("-zoomed", True)
            except tk.TclError: pass

    def _init_sash(self):
        """يضبط ارتفاع لوحة المصادر مبدئياً بحيث تبقى النتائج ظاهرة."""
        total = self.paned.winfo_height()
        if total <= 1:
            self.after(150, self._init_sash)
            return
        want = self.settings_inner.winfo_reqheight() + 6
        want = max(90, min(want, int(total * 0.40)))
        try:
            self.paned.sashpos(0, want)
        except tk.TclError:
            pass

    def _ensure_results_space(self):
        """بعد التحليل: يضمن ظهور النتائج بتصغير/إخفاء لوحة المصادر عند الحاجة."""
        if not self._settings_visible:
            return
        try:
            self.update_idletasks()
            total = self.paned.winfo_height()
            pos = self.paned.sashpos(0)
            need = 280
            if total - pos < need:
                if total - need < 90:
                    self._toggle_settings()
                else:
                    self.paned.sashpos(0, total - need)
        except tk.TclError:
            pass

    def _toggle_settings(self):
        if self._settings_visible:
            self.paned.forget(self.settings_pane)
            self.toggle_btn.config(text="▼ إظهار مصادر البيانات")
        else:
            self.paned.insert(0, self.settings_pane, weight=0)
            self.toggle_btn.config(text="▲ إخفاء مصادر البيانات")
            self.after(80, self._init_sash)
        self._settings_visible = not self._settings_visible

    def _toggle_fullscreen(self, _event=None):
        self._fullscreen = not self._fullscreen
        self.attributes("-fullscreen", self._fullscreen)

    def _exit_fullscreen(self, _event=None):
        if self._fullscreen:
            self._fullscreen = False
            self.attributes("-fullscreen", False)

    def _bind_wheel(self):
        self.bind_all("<MouseWheel>", self._on_wheel, add="+")
        self.bind_all("<Button-4>", self._on_wheel, add="+")
        self.bind_all("<Button-5>", self._on_wheel, add="+")
        try:  # منع تغيير قيمة القائمة بالخطأ أثناء تمرير الصفحة
            self.unbind_class("TCombobox", "<MouseWheel>")
        except tk.TclError:
            pass

    def _on_wheel(self, e):
        try:
            w = self.winfo_containing(e.x_root, e.y_root)
        except (KeyError, tk.TclError):
            return
        while w is not None and w is not self._sc:
            w = getattr(w, "master", None)
        if w is None or self._sc.yview() == (0.0, 1.0):
            return
        num = getattr(e, "num", None)
        if num == 4:
            step = -1
        elif num == 5:
            step = 1
        else:
            step = -1 if e.delta > 0 else 1
        self._sc.yview_scroll(step * 2, "units")

    def _on_close(self):
        self._save_config()
        self.destroy()

    def _make_text(self, parent) -> tk.Text:
        t = tk.Text(parent, wrap="word", font=("Segoe UI", 10), bg="#ffffff", fg="#182230",
                    relief="flat", padx=12, pady=8, state="disabled")
        sb = ttk.Scrollbar(parent, orient="vertical", command=t.yview)
        t.configure(yscrollcommand=sb.set)
        sb.pack(side="left", fill="y")
        t.pack(side="right", fill="both", expand=True)
        t.tag_configure("rtl", justify="right")
        t.tag_configure("title", font=("Segoe UI", 12, "bold"), foreground="#17324d", spacing1=8)
        t.tag_configure("sub", font=("Segoe UI", 10, "bold"), foreground="#31506f")
        t.tag_configure("muted", foreground="#65758b")
        t.tag_configure("warn", foreground="#a15c00", font=("Segoe UI", 10, "bold"))
        for tier in TIERS:
            t.tag_configure("t_" + tier.key, foreground=tier.fg, background=tier.bg,
                            font=("Segoe UI", 10, "bold"))
        return t

    # ---- حالة التشغيل ----
    def _busy(self, busy: bool, message: str):
        self.status.set(message)
        state = "disabled" if busy else "normal"
        for child in self.winfo_children():
            self._set_buttons(child, state)

    def _set_buttons(self, widget, state):
        if isinstance(widget, ttk.Button):
            try:
                widget.configure(state=state)
            except tk.TclError:
                pass
        for child in widget.winfo_children():
            self._set_buttons(child, state)

    def load_api(self, force=False):
        key = self.api_key.get().strip()
        if not key:
            messagebox.showwarning("مفتاح API", "أدخل مفتاح football-data.org أولاً.")
            return
        code = LEAGUES.get(self.league.get())
        if not code:
            messagebox.showerror("الدوري", "اختر دورياً صحيحاً.")
            return
        self._save_config()
        self._busy(True, "جارٍ تحميل نتائج المواسم من football-data.org...")
        threading.Thread(target=self._api_worker,
                         args=(code, max(0, min(5, self.seasons.get())), force), daemon=True).start()

    def _api_worker(self, code, seasons, force=False):
        try:
            rows, name, errors = fetch_competition(code, self.api_key.get().strip(), seasons, force_refresh=force)
            self.after(0, self._data_loaded, rows, f"{name} • API")
            if errors:
                # # FIX #37: عرض تفاصيل المواسم المتعذرة بدل عدّها فقط.
                detail = " | ".join(errors[:3])
                more = " …" if len(errors) > 3 else ""
                self.after(0, lambda d=detail + more: self.status.set(
                    f"تم التحميل مع تعذر جلب {len(errors)} موسم: {d}"))
        except Exception as exc:
            self.after(0, self._failed, str(exc))

    def show_live(self):
        code = LEAGUES.get(self.league.get(), "")
        if getattr(self, "_live_window", None) is not None:
            try:
                if self._live_window.winfo_exists():
                    self._live_window.lift(); self._refresh_live(code); return
            except tk.TclError:
                pass
        win = tk.Toplevel(self)
        self._live_window = win
        win.title("المباريات المباشرة — ESPN")
        win.geometry("760x440")
        win.minsize(480, 260)
        top = ttk.Frame(win, padding=8); top.pack(fill="x")
        ttk.Label(top, text=f"لوحة ESPN المباشرة — {self.league.get()}").pack(side="right")
        ttk.Button(top, text="تحديث الآن", command=lambda: self._refresh_live(code)).pack(side="left")
        tree = ttk.Treeview(win, columns=("home", "score", "away", "clock", "stats", "status"), show="headings")
        for col, label, width in (("home", "صاحب الأرض", 170), ("score", "النتيجة", 80),
                                  ("away", "الضيف", 170), ("clock", "الدقيقة", 75),
                                  ("stats", "إحصائيات مباشرة", 330), ("status", "الحالة", 110)):
            tree.heading(col, text=label); tree.column(col, width=width, anchor="center")
        tree.pack(fill="both", expand=True, padx=8, pady=8)
        self._live_tree = tree
        self._live_code = code
        self._refresh_live(code)

    def _refresh_live(self, code):
        if not getattr(self, "_live_window", None) or not self._live_window.winfo_exists(): return
        self.status.set("جارٍ تحديث نتائج ESPN المباشرة...")
        def worker():
            try:
                data = fetch_espn_live(code)
                events = parse_espn_live_events(data)
                self.after(0, self._live_loaded, events)
            except Exception as exc:
                self.after(0, lambda: self.status.set("تعذر تحديث ESPN: " + str(exc)))
        threading.Thread(target=worker, daemon=True).start()

    def _live_loaded(self, events):
        if not getattr(self, "_live_tree", None): return
        try:
            live_alerts = []
            for x in events:
                k = (x.get("home", ""), x.get("away", ""))
                score = f'{x.get("hs", 0)}-{x.get("as", 0)}'
                current_status = x.get("status", "")
                prev = self._live_previous.get(k)
                if prev and self.alerts_enabled.get():
                    if prev.get("score") != score:
                        live_alerts.append(f"تغيرت النتيجة: {x.get('home')} {score} {x.get('away')}")
                    elif prev.get("status") != current_status:
                        live_alerts.append(f"تغيرت حالة: {x.get('home')} × {x.get('away')} — {current_status}")
                self._live_previous[k] = {"score": score, "status": current_status}
            for item in self._live_tree.get_children(): self._live_tree.delete(item)
            for x in events:
                self._live_tree.insert("", "end", values=(x["home"], f'{x["hs"]} - {x["as"]}', x["away"],
                    x.get("clock", "—"), x.get("stats", "—"), x["status"]))
            if live_alerts:
                try: self.bell()
                except tk.TclError: pass
                self.status.set("تنبيه مباشر: " + " | ".join(live_alerts[:2]))
            else:
                self.status.set(f"تم تحديث ESPN — {len(events)} مباراة. التحديث التلقائي كل 60 ثانية.")
            if self._live_window.winfo_exists():
                self._live_window.after(60000, lambda: self._refresh_live(self._live_code))
        except tk.TclError:
            pass

    def show_team_context(self):
        code, home, away = LEAGUES.get(self.league.get(), ""), self.home.get().strip(), self.away.get().strip()
        if not home or not away:
            messagebox.showwarning("الإصابات", "اختر الفريقين أولاً."); return
        self.status.set("جارٍ فحص تقارير الإصابات والأخبار من ESPN...")
        def worker():
            try:
                ctx = fetch_espn_team_context(code, home, away)
                lines = [ctx.get("note", "")]
                for team in ctx.get("teams", []):
                    lines.append("\n" + team["team"])
                    if team.get("error"): lines.append("تعذر جلب الإصابات: " + team["error"])
                    elif team.get("injuries"):
                        for item in team["injuries"][:20]:
                            ath = item.get("athlete", {}) if isinstance(item, dict) else {}
                            lines.append("• " + str(ath.get("displayName") or item.get("displayName") or item.get("description") or "تقرير غياب"))
                    else: lines.append("لم يعرض ESPN قائمة إصابات لهذا الفريق في الاستجابة الحالية.")
                for article in ctx.get("news", [])[:5]:
                    lines.append("خبر: " + str(article.get("headline", "")))
                msg = "\n".join(lines)
                self.after(0, lambda: (messagebox.showinfo("تقارير ESPN", msg), self.status.set("اكتمل فحص ESPN.")))
            except Exception as exc:
                self.after(0, lambda: messagebox.showerror("تقارير ESPN", str(exc)))
        threading.Thread(target=worker, daemon=True).start()

    def _backtest_cache_key(self, half_share, form_weight):
        # Fingerprint the loaded historical dataset and model settings.
        digest = hashlib.sha1()
        for m in self.matches:
            digest.update(
                f"{m.played}|{m.home}|{m.away}|{m.hg}|{m.ag};".encode("utf-8", "ignore")
            )
        return (digest.hexdigest(), round(float(half_share), 4), round(float(form_weight), 4))

    def _calculate_backtest(self, half_share, form_weight):
        """
        Expanding-window walk-forward validation:
        every tested fixture is predicted only from matches dated strictly earlier.
        A bounded, evenly spaced test sample keeps the UI responsive on large seasons.
        """
        ordered = sorted(self.matches, key=lambda m: m.played)
        if len(ordered) < 80:
            return {"ok": False, "reason": "يلزم 80 مباراة تاريخية على الأقل."}

        split = max(40, int(len(ordered) * 0.70))
        test_all = ordered[split:]
        if not test_all:
            return {"ok": False, "reason": "لا توجد مباريات اختبار بعد تقسيم البيانات."}

        # Test up to 60 dates spread across the held-out period; never train on test/future rows.
        if len(test_all) > 60:
            step = (len(test_all) - 1) / 59
            test = [test_all[round(i * step)] for i in range(60)]
        else:
            test = test_all

        # # FIX #7: احسب rho مرة واحدة من النموذج الكامل لتفادي O(61n) لكل مباراة اختبار.
        try:
            full_model = FootballModel(ordered, half_time_share=half_share, form_weight=form_weight)
            fixed_rho = full_model.rho
        except Exception:
            fixed_rho = 0.0
        correct = exact = brier = 0.0
        goal_abs_error = 0.0
        n = 0
        for actual in test:
            past = [m for m in ordered if m.played < actual.played]
            if len(past) < 30:
                continue
            try:
                historical_model = FootballModel(
                    past,
                    half_time_share=half_share,
                    form_weight=form_weight
                )
                # # FIX #7: تجاوز حساب rho المكلف في كل نموذج جزئي.
                historical_model.rho = fixed_rho
                pred = historical_model.predict(actual.home, actual.away)
                probs = list(pred.get("1x2", []))
                if len(probs) != 3 or sum(probs) <= 0:
                    continue
                outcome = 0 if actual.hg > actual.ag else 1 if actual.hg == actual.ag else 2
                correct += int(max(range(3), key=lambda i: probs[i]) == outcome)
                scores = pred.get("scores", [])
                if scores:
                    exact += int(scores[0][1] == actual.hg and scores[0][2] == actual.ag)
                brier += sum((probs[i] - int(i == outcome)) ** 2 for i in range(3))
                goal_abs_error += abs(float(pred.get("lambda_home", 0)) - actual.hg)
                goal_abs_error += abs(float(pred.get("lambda_away", 0)) - actual.ag)
                n += 1
            except Exception:
                continue

        if not n:
            return {"ok": False, "reason": "لم تتوفر عينات تاريخية صالحة للتقييم."}

        return {
            "ok": True,
            "n": n,
            "tested_total": len(test),
            "accuracy": correct / n,
            "exact_score": exact / n,
            "brier": brier / n,
            "mae_goals": goal_abs_error / (2 * n),
            "method": "Walk-forward زمني؛ التدريب يقتصر على المباريات الأقدم من كل مباراة اختبار."
        }

    def _start_backtest_for_analysis(self, home=None, away=None):
        if not hasattr(self, "backtest_label"):
            return
        if len(self.matches) < 80:
            self.backtest_label.config(
                text="الدقة التاريخية غير متاحة: يلزم تحميل 80 مباراة مكتملة على الأقل."
            )
            return

        half_share = clamp(self.half_share.get(), 0.30, 0.65)
        form_weight = clamp(self.form_weight.get(), 0.0, 0.25)
        cache_key = self._backtest_cache_key(half_share, form_weight)
        cached = getattr(self, "_backtest_cache", {}).get(cache_key)
        if cached:
            self._backtest_loaded(cached, home, away)
            return

        request_id = getattr(self, "_backtest_request_id", 0) + 1
        self._backtest_request_id = request_id
        self.backtest_label.config(
            text="جارٍ حساب الدقة التاريخية تلقائياً على مباريات سابقة، دون استخدام نتائج مستقبلية..."
        )

        def worker():
            result = self._calculate_backtest(half_share, form_weight)
            self.after(0, self._backtest_loaded, result, home, away, request_id, cache_key)

        threading.Thread(target=worker, daemon=True).start()

    def _backtest_loaded(self, result, home=None, away=None, request_id=None, cache_key=None):
        if request_id is not None and request_id != getattr(self, "_backtest_request_id", request_id):
            return
        if cache_key:
            if not hasattr(self, "_backtest_cache"):
                self._backtest_cache = {}
            self._backtest_cache[cache_key] = result
        if not hasattr(self, "backtest_label"):
            return
        if not result.get("ok"):
            self.backtest_label.config(text="الدقة التاريخية: " + result.get("reason", "غير متاحة"))
            return

        n = result["n"]
        text = (
            f"تقييم النموذج التاريخي ({n} مباراة اختبار): "
            f"دقة 1X2 {result['accuracy']:.1%}  |  "
            f"النتيجة الدقيقة {result['exact_score']:.1%}  |  "
            f"Brier {result['brier']:.3f}  |  "
            f"متوسط خطأ الأهداف {result['mae_goals']:.2f}"
        )
        self.backtest_label.config(text=text)
        if self.last_result is not None:
            self.last_result["historical_validation"] = result

    def backtest(self):
        # The same evaluation is available manually, but is also run automatically
        # and displayed beside every match analysis.
        if len(self.matches) < 80:
            messagebox.showwarning(
                "الاختبار التاريخي",
                "يلزم 80 مباراة تاريخية مكتملة على الأقل لإجراء تقييم زمني."
            )
            return
        half_share = clamp(self.half_share.get(), 0.30, 0.65)
        form_weight = clamp(self.form_weight.get(), 0.0, 0.25)
        cache_key = self._backtest_cache_key(half_share, form_weight)
        cached = getattr(self, "_backtest_cache", {}).get(cache_key)
        if cached:
            self._backtest_loaded(cached)
            if cached.get("ok"):
                self._show_backtest_details(cached)
            return

        self.backtest_label.config(text="جارٍ تنفيذ الاختبار التاريخي...")
        def worker():
            result = self._calculate_backtest(half_share, form_weight)
            self.after(0, self._backtest_manual_done, result, cache_key)
        threading.Thread(target=worker, daemon=True).start()

    def _backtest_manual_done(self, result, cache_key):
        if not hasattr(self, "_backtest_cache"):
            self._backtest_cache = {}
        self._backtest_cache[cache_key] = result
        self._backtest_loaded(result)
        if result.get("ok"):
            self._show_backtest_details(result)
        else:
            messagebox.showwarning("الاختبار التاريخي", result.get("reason", "تعذر التقييم."))

    def _show_backtest_details(self, result):
        messagebox.showinfo(
            "تقييم دقة النموذج التاريخية",
            f"المباريات المختبرة: {result['n']} من {result['tested_total']} عينة مختارة\n"
            f"دقة 1X2: {result['accuracy']:.1%}\n"
            f"توقع النتيجة الدقيقة: {result['exact_score']:.1%}\n"
            f"Brier Score: {result['brier']:.4f} (الأقل أفضل)\n"
            f"متوسط خطأ الأهداف: {result['mae_goals']:.3f} هدف\n\n"
            f"{result['method']}\n"
            "هذا قياس تاريخي على البيانات المحمّلة، وليس ضماناً لدقة المباراة القادمة."
        )

    def import_csv(self):
        path = filedialog.askopenfilename(
            title="اختر ملف نتائج CSV",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
        )
        if not path:
            return
        try:
            rows = load_csv(path)
            self._data_loaded(rows, os.path.basename(path))
        except Exception as exc:
            messagebox.showerror("تعذر استيراد CSV", str(exc))

    def _data_loaded(self, rows, source):
        self._busy(False, "تم تحميل البيانات.")
        self.matches = rows
        try:
            self.model = FootballModel(rows, half_time_share=self.half_share.get(),
                                       form_weight=self.form_weight.get())
            names = self.model.teams
            self.home_combo["values"] = names
            self.away_combo["values"] = names
            ht = (f"أشواط فعلية ({self.model.ht_count} مباراة)" if self.model._ht_real
                  else f"بدون بيانات أشواط كافية ({self.model.ht_count}/{MIN_HT_MATCHES}) — تقدير افتراضي")
            self.data_label.config(
                text=f"المصدر: {source} | المباريات: {len(rows)} | الفرق: {len(names)} | "
                     f"من {rows[0].played} إلى {rows[-1].played} | {ht}"
            )
            self.status.set("تم تجهيز النموذج. اختر الفريقين.")
            self._save_config()
        except Exception as exc:
            self._failed(str(exc))

    def _failed(self, error):
        self._busy(False, "فشل تنفيذ العملية.")
        messagebox.showerror("خطأ", error)

    def predict(self):
        if not self.model:
            messagebox.showwarning("البيانات غير جاهزة", "حمّل بيانات الدوري أو استورد CSV أولاً.")
            return
        home, away = self.home.get().strip(), self.away.get().strip()
        if not home or not away:
            messagebox.showwarning("المباراة", "أدخل اسم الفريقين.")
            return
        try:
            self.model.fallback_share = clamp(self.half_share.get(), 0.30, 0.65)
            self.model.form_weight = clamp(self.form_weight.get(), 0.0, 0.25)
            result = self.model.predict(home, away)
            self.last_result = result
            self.render_result(result)
            self._record_prediction(result, update=False)
            self._start_backtest_for_analysis(home, away)
            self._save_config()
            # Invalidate any previous background request even when the new analysis has no external key.
            self._external_request_id += 1
            self._availability_refresh_attempts = 0
            request_id = self._external_request_id
            external_key = self.api_sports_key.get().strip()   # اختياري: بدونه يُستخدم ESPN المجاني
            league_code = LEAGUES.get(self.league.get(), "")
            match_date = self.match_date.get().strip()
            self.last_result["external_status"] = "loading"
            self._render_external(self.last_result)
            self.status.set("اكتمل التحليل الأساسي؛ يجري فحص الإصابات والتشكيلة والأودز تلقائياً من ESPN...")
            threading.Thread(
                target=self._external_worker,
                args=(external_key, league_code, home, away, match_date, request_id),
                daemon=True
            ).start()
        except Exception as exc:
            messagebox.showerror("تعذر التحليل", str(exc))

    def _external_worker(self, api_key, league_code, home, away, match_date, request_id):
        external, external_error = None, None
        context, context_error = None, None
        try:
            external = fetch_external_match_data(api_key, league_code, home, away, match_date)
        except Exception as exc:
            external_error = str(exc)
        try:
            # فحص الإصابات والتشكيلة تلقائي لكل مباراة، وليس عبر زر يدوي.
            context = fetch_espn_team_context(league_code, home, away, match_date)
        except Exception as exc:
            context_error = str(exc)
        if external is None:
            external = {"error": external_error or "لم تصل بيانات ESPN."}
        if context is None:
            context = {"available": False, "error": context_error or "تعذر جلب سياق المباراة."}
        self.after(0, self._external_loaded, external, context, request_id)

    def _external_loaded(self, external, context, request_id):
        if not self.last_result or request_id != self._external_request_id:
            return
        # إعادة بناء التوقعات بعد إدخال الإصابات الموثقة، ثم إعادة دمج الأودز.
        try:
            home, away = self.home.get().strip(), self.away.get().strip()
            if self.model and context.get("available"):
                updated = self.model.predict(home, away, team_context=context)
                updated["external"] = external
                updated["external_status"] = "ready"
                self.last_result = updated
                self.render_result(self.last_result)
            else:
                self.last_result["availability"] = context
                self.last_result["external"] = external
                self.last_result["external_status"] = "ready"
        except Exception as exc:
            self.last_result["availability_error"] = str(exc)
            self.last_result["external"] = external
            self.last_result["external_status"] = "ready"
        enrich_result_with_odds(self.last_result)
        self._record_prediction(self.last_result, update=True)
        self._render_banner(self.last_result)
        self._notify_value_bets(self.last_result)
        self._render_markets(self.last_result)
        self._render_external(self.last_result)
        self._render_availability(self.last_result)
        if context.get("available") and not context.get("lineup_confirmed"):
            self._schedule_availability_refresh(request_id, self.home.get().strip(), self.away.get().strip(),
                                                LEAGUES.get(self.league.get(), ""), self.match_date.get().strip())
        if context.get("available"):
            inj_count = sum(len(t.get("injuries", [])) for t in context.get("teams", []))
            self.status.set(f"اكتمل التحليل مع فحص ESPN تلقائياً: {inj_count} تقارير إصابة؛ {context.get('lineup_status', 'حالة التشكيلة غير معروفة')}.")
        else:
            self.status.set("اكتمل التحليل؛ لم تتوفر بيانات إصابات/تشكيلة مؤكدة من ESPN لهذه المباراة.")

    def _schedule_availability_refresh(self, request_id, home, away, league_code, match_date):
        # أعد فحص التشكيلة تلقائياً كل خمس دقائق حتى تُنشر أو تنتهي نافذة المتابعة.
        if self._availability_refresh_attempts >= 36:
            return
        # # FIX #19: جدولة آمنة تتحقق من بقاء النافذة حيّة قبل الاستدعاء.
        try:
            if not self.winfo_exists():
                return
        except tk.TclError:
            return

        def _safe_refresh():
            try:
                if not self.winfo_exists():
                    return
            except tk.TclError:
                return
            self._refresh_availability(request_id, home, away, league_code, match_date)

        self.after(300000, _safe_refresh)

    def _refresh_availability(self, request_id, home, away, league_code, match_date):
        if request_id != self._external_request_id or not self.model:
            return
        if home != self.home.get().strip() or away != self.away.get().strip():
            return
        self._availability_refresh_attempts += 1
        def worker():
            try:
                context = fetch_espn_team_context(league_code, home, away, match_date)
            except Exception as exc:
                context = {"available": False, "error": str(exc)}
            self.after(0, self._availability_refreshed, context, request_id, home, away,
                       league_code, match_date)
        threading.Thread(target=worker, daemon=True).start()

    def _availability_refreshed(self, context, request_id, home, away, league_code, match_date):
        if request_id != self._external_request_id or not self.model:
            return
        if context.get("available"):
            try:
                external = (self.last_result or {}).get("external")
                updated = self.model.predict(home, away, team_context=context)
                updated["external"] = external
                updated["external_status"] = "ready"
                self.last_result = updated
                self.render_result(updated)
                enrich_result_with_odds(updated)
                self._record_prediction(updated, update=True)
                self._render_banner(updated)
                self._render_markets(updated)
                self._render_external(updated)
                self._render_availability(updated)
                self.status.set("تم تحديث التحليل تلقائياً بمعلومات ESPN الأحدث.")
                if context.get("lineup_confirmed"):
                    return
            except Exception as exc:
                self.status.set("تعذر تحديث أثر التشكيلة: " + str(exc))
        self._schedule_availability_refresh(request_id, home, away, league_code, match_date)

    def _external_failed(self, error, request_id):
        if not self.last_result or request_id != self._external_request_id:
            return
        self.last_result["external"] = {"error": error}
        self.last_result["external_status"] = "error"
        self._render_external(self.last_result)
        self.status.set("اكتمل التحليل المحلي، لكن تعذر جلب بيانات المواقع: " + error)

    # ---- أدوات العرض ----
    @staticmethod
    def _pct(x):
        return f"{x * 100:.1f}%"

    def _chip(self, p: float):
        t = tier_of(p)
        return (f" {self._pct(p)} ", "t_" + t.key)

    @staticmethod
    def _put(t: tk.Text, parts="", tag=None):
        if isinstance(parts, str):
            parts = [(parts, tag)]
        start = t.index("end-1c")
        for text, tg in parts:
            t.insert("end", text, tg or ())
        t.insert("end", "\n")
        t.tag_add("rtl", start, "end-1c")

    def _reset_text(self, t: tk.Text):
        t.config(state="normal")
        t.delete("1.0", "end")

    # ---- العرض الرئيسي ----
    def render_result(self, r):
        enrich_result_with_odds(r)
        self._render_banner(r)
        self._render_markets(r)
        self._render_halves(r)
        self._render_deep(r)
        self._render_external(r)
        self._render_professional_dashboards(r)
        self.after(50, self._ensure_results_space)

    @staticmethod
    def _odds_text(m, short=False):
        o = m.get("odds") or {}
        v = o.get("value")
        if not v:
            return "—"
        if o.get("kind") == "market":
            return f"{v:.2f}" if short else f"{v:.2f} (أفضل سعر بين {o.get('books', 1)} شركة)"
        return f"≈{v:.2f}" if short else f"≈{v:.2f} (أودز نموذجية = 1÷الاحتمال، ليست سعر شركة)"

    def _odds_note(self, r):
        if r.get("has_market_odds"):
            return "الأودز المعروضة هي أفضل سعر متاح من المصدر الخارجي، والأسواق بلا سعر تُعرض بأودز نموذجية (≈)."
        return ("الأودز المعروضة نموذجية تقريبية (1÷الاحتمال) وليست أسعار شركات؛ "
                "تظهر أسعار السوق تلقائياً عند نجاح جلب الأودز.")

    def _render_high_pick(self, r):
        hp = r.get("high_pick") or {}
        m = hp.get("market")
        if not m:
            self.banner_hi.config(
                text="اختيار بأودز أعلى (نفس اتجاه التحليل): لا يوجد" + (f" — {hp['reason']}" if hp.get("reason") else ""),
                bg="#eef1f5", fg="#4a5a70")
            return
        o = m["odds"]
        ev = ""
        if o.get("kind") == "market":
            ev = f" • عائد نظري خام {(m['p'] * o['value'] - 1) * 100:+.0f}%"
        tenth = max(1, round(m["p"] * 10))
        self.banner_hi.config(
            text=(f"اختيار بأودز أعلى في نفس اتجاه التحليل ({hp.get('direction_label', '')}): {m['name']}"
                  f"   •   أودز {self._odds_text(m, short=True)}"
                  f"   •   احتمال النموذج {self._pct(m['p'])}{ev}\n"
                  f"يتحقق وفق النموذج نحو {tenth} من كل 10 مرات؛ الأودز الأعلى تعني خسارة أكثر تكراراً "
                  "وليست ضماناً لأي ربح."),
            bg="#fff1e0", fg="#8a4b00")

    def _render_banner(self, r):
        info = r["pick"]
        pick = info["pick"]
        title = f"{r['home']}  ×  {r['away']}"
        if pick:
            t = pick["tier"]
            self.banner.config(
                text=(f"أفضل اختيار احتمالي: {pick['name']}   •   {self._pct(pick['p'])} ({t.label})"
                      f"   •   الأودز {self._odds_text(pick, short=True)}"),
                bg=t.bg, fg=t.fg)
            alts = "  |  ".join(f"{m['name']} ({self._pct(m['p'])})" for m in info["alts"])
            sub = (f"{title}\nالاحتمال المحافظ بعد خصم هامش عدم اليقين: {self._pct(pick['adj'])} "
                   f"• جودة البيانات {r['quality']}/100"
                   + (f"\nبدائل من مجموعات أخرى: {alts}" if alts else "")
                   + f"\nالأودز: {self._odds_text(pick)}"
                   + "\n" + self._odds_note(r))
        else:
            self.banner.config(text="لا يوجد اختيار موصى به لهذه المباراة", bg="#e6eaf0", fg="#34445a")
            sub = f"{title}\n{info['reason']}"
        self.banner_sub.config(text=sub)
        self._render_high_pick(r)

    def _render_markets(self, r):
        self.tree.delete(*self.tree.get_children())
        pick = r["pick"]["pick"]
        # عرض التوقعات الجيدة والقوية فقط؛ إخفاء المتوسط والضعيف بالكامل.
        # لا نغيّر حسابات النموذج أو الاحتمالات الأصلية، بل نفلتر ما يظهر للمستخدم.
        for m in r["markets"]:
            if m["tier"].key not in ("good", "strong"):
                continue
            n_bar = int(round(m["p"] * 20))
            star = "★ " if pick is m else ""
            adj = self._pct(m["adj"]) if m["pickable"] else "—"
            self.tree.insert("", "end", tags=(m["tier"].key,), values=(
                "█" * n_bar + "░" * (20 - n_bar), m["tier"].label, adj,
                self._pct(m["p"]), self._odds_text(m, short=True), star + m["name"], m["group"]))

    def _render_halves(self, r):
        t = self.txt_halves
        self._reset_text(t)
        w = lambda *a, **k: self._put(t, *a, **k)  # noqa: E731
        home, away = r["home"], r["away"]
        sh_h, sh_a = r["half_shares"]
        src = (f"نسبة فعلية من {r['ht_count']} مباراة" if r["share_src"] == "actual"
               else "نسبة مفترضة (لا توجد بيانات أشواط كافية)")
        w("توقع الشوطين والنتيجة النهائية", "title")
        w(f"حصة أهداف الشوط الأول: المضيف {sh_h * 100:.0f}% | الضيف {sh_a * 100:.0f}% — {src}", "muted")
        w()

        def phase(title, s, lh, la):
            w(title, "title")
            w(f"الأهداف المتوقعة: {home} {lh:.2f} — {la:.2f} {away}", "muted")
            p = s["probs"]
            w([(f"فوز {home}: ", None), self._chip(p[0]), ("   تعادل: ", None), self._chip(p[1]),
               (f"   فوز {away}: ", None), self._chip(p[2])])
            w([("أرجح النتائج: ", None)] + sum(
                [[(f"{h}-{a}", "sub"), self._chip(pr), ("   ", None)] for pr, h, a in s["scores"][:3]], []))
            w()

        phase("الشوط الأول" + ("" if r["share_src"] == "actual" else "  (تقدير)"),
              r["fh"], r["lambda_home"] * sh_h, r["lambda_away"] * sh_a)
        phase("الشوط الثاني" + ("" if r["share_src"] == "actual" else "  (تقدير)"),
              r["sh"], r["lambda_home"] * (1 - sh_h), r["lambda_away"] * (1 - sh_a))
        phase("النتيجة النهائية", r["ft"], r["lambda_home"], r["lambda_away"])
        w("أفضل 10 نتائج دقيقة محتملة (النهائي)", "title")
        for rank, (prob, hg, ag) in enumerate(r["ft"]["scores"][:10], 1):
            w(f"{rank}) {hg}-{ag}: {prob:.2%}", "sub" if rank == 1 else "muted")

        fh_s, sh_s, ft_s = r["fh"]["scores"][0], r["sh"]["scores"][0], r["ft"]["scores"][0]
        w("الملخص المتوقع", "title")
        w(f"الأشواط: {fh_s[1]}-{fh_s[2]} ثم {sh_s[1]}-{sh_s[2]}   •   النهائي الأرجح: {ft_s[1]}-{ft_s[2]}")
        w("أرجح نتيجة لكل فترة تُحسب بشكل مستقل، لذلك قد لا يتطابق مجموع الشوطين مع النتيجة النهائية "
          "الأرجح؛ وأي نتيجة دقيقة منفردة احتمالها منخفض عادةً حتى لو كانت الأرجح.", "muted")
        t.config(state="disabled")

    def _render_deep(self, r):
        t = self.txt_deep
        self._reset_text(t)
        w = lambda *a, **k: self._put(t, *a, **k)  # noqa: E731
        home, away = r["home"], r["away"]
        ph, pa = r["ph"], r["pa"]

        w("قراءة المواجهة", "title")
        edge_h = ph["att_home"] * pa["def_away"]
        edge_a = pa["att_away"] * ph["def_home"]

        def edge_text(v, att, dfn):
            if v >= 1.20:
                return f"ميزة هجومية واضحة لـ {att} على دفاع {dfn}", "strong"
            if v >= 1.05:
                return f"أفضلية هجومية طفيفة لـ {att}", "good"
            if v >= 0.90:
                return f"مواجهة متكافئة بين هجوم {att} ودفاع {dfn}", "medium"
            return f"دفاع {dfn} قادر على الحد من هجوم {att}", "weak"

        for v, att, dfn in ((edge_h, home, away), (edge_a, away, home)):
            txt, key = edge_text(v, att, dfn)
            w([(f" {txt} ", "t_" + key), (f"   (مؤشر {v:.2f} مقابل 1.00 = متوسط الدوري)", "muted")])
        w(f"الأهداف المتوقعة: {home} {r['lambda_home']:.2f} — {r['lambda_away']:.2f} {away}"
          f"   (قبل تعديل الفورمة: {r['base_home']:.2f} — {r['base_away']:.2f}، وزن الفورمة {r['form_weight']:.2f})")
        w()

        self._team_block(t, home, ph, "صاحب الأرض", "داخل الأرض")
        self._team_block(t, away, pa, "الضيف", "خارج الأرض")

        w("المواجهات المباشرة (آخر مباريات في البيانات)", "title")
        h2h = r["h2h"]
        if not h2h:
            w("لا توجد مواجهات مباشرة في البيانات المحمّلة.", "muted")
        else:
            wins = sum(1 for m in h2h if (m.home == home and m.hg > m.ag) or (m.away == home and m.ag > m.hg))
            draws = sum(1 for m in h2h if m.hg == m.ag)
            w(f"{home}: {wins} فوز | تعادل: {draws} | {away}: {len(h2h) - wins - draws} فوز")
            for m in h2h:
                w(f"  {m.played}: {m.home} {m.hg}-{m.ag} {m.away}", "muted")
        w()

        w("جودة البيانات وحدود النموذج", "title")
        q = r["quality"]
        key = "strong" if q >= 75 else "medium" if q >= 55 else "weak"
        w([(f" {q}/100 ", "t_" + key), (f"  {r['confidence']}", None)])
        w(f"عينة: {r['home_games']} مباراة للمضيف و{r['away_games']} للضيف | Dixon-Coles rho={r['rho']:.3f}", "muted")
        for n in r["notes"]:
            w("• " + n, "muted")
        w("فحص ESPN التلقائي: الإصابات والتشكيلة", "title")
        ctx = r.get("availability") or {}
        if ctx.get("available"):
            w(ctx.get("lineup_status", "حالة التشكيلة غير معروفة"), "sub")
            for team in ctx.get("teams", []):
                injuries = team.get("injuries", []) or []
                w(f"{team.get('team', 'الفريق')}: {len(injuries)} تقارير إصابة", "muted")
                for injury in injuries[:12]:
                    w(f"• {injury.get('name', 'لاعب')} — {injury.get('status', 'إصابة')} — {injury.get('position') or 'المركز غير معروف'}", "muted")
            if ctx.get("lineup_confirmed"):
                for lineup in ctx.get("lineups", []):
                    w(f"التشكيلة المنشورة — {lineup.get('team')}: {', '.join(lineup.get('starters', [])[:11])}", "muted")
            for detail in (r.get("availability_factors") or {}).get("details", []):
                w("تأثير محسوب: " + detail, "muted")
            w(ctx.get("note", ""), "muted")
        else:
            w("لم تصل معلومات مؤكدة من ESPN. لم يفترض البرنامج أن الفريق مكتمل الصفوف، ولم يخترع تشكيلة.", "warn")
        w("الاحتمالات إحصائية وليست نصيحة مراهنة أو ضماناً. لا تراهن بأموال لا يمكنك تحمل خسارتها.", "warn")
        t.config(state="disabled")

    def _render_availability(self, r):
        # إعادة عرض لوحة التحليل العميق بعد وصول تقارير ESPN.
        try:
            self._render_deep(r)
        except Exception:
            pass

    def _render_external(self, r):
        t = self.txt_external
        self._reset_text(t)
        w = lambda *a, **k: self._put(t, *a, **k)  # noqa: E731
        ext = r.get("external")
        w("الأودز وتوقعات المواقع الخارجية", "title")
        w("المصدر: ESPN مجاناً بدون مفتاح، أو API-Football عند إدخال مفتاح. قد تختلف التغطية حسب الدوري والمباراة.", "muted")
        if r.get("external_status") == "loading":
            w("جارٍ العثور على المباراة المطابقة ثم جلب التوقعات والأودز...", "sub")
            t.config(state="disabled")
            return
        if not ext:
            w("لم تصل بيانات خارجية بعد. اضغط «حلّل المباراة» وسيُجلب الأودز تلقائياً بدون مفتاح.", "muted")
            t.config(state="disabled")
            return
        if ext.get("error"):
            w("تعذر جلب البيانات الخارجية", "sub")
            w(ext["error"], "warn")
            w("تحقق من المفتاح، والدوري المختار، وأن صاحب الأرض والضيف بالترتيب الصحيح، وتغطية خطتك (أو أدخل التاريخ يدوياً). التحليل المحلي يبقى متاحاً.", "muted")
            t.config(state="disabled")
            return

        fixture = ext.get("fixture", {})
        w(f"المباراة المطابقة في المصدر: {fixture.get('home', '')} × {fixture.get('away', '')}", "sub")
        w(f"الدوري: {fixture.get('league', '—')} | الموعد: {fixture.get('date', '—')} | المصدر: {ext.get('provider', '—')}", "muted")
        if ext.get("fallback_note"):
            w(ext["fallback_note"], "warn")
        w("توقعات الموقع المستقلة عن الأودز", "title")
        p = ext.get("predictions", {})
        if not p.get("available"):
            w(p.get("message", "لا توجد توقعات خارجية متاحة."), "muted")
        else:
            pct = p.get("percent", {})
            parts = [("فوز المضيف: ", None), (f"{pct.get('home'):.1f}%" if pct.get('home') is not None else "—", "sub"),
                     ("   تعادل: ", None), (f"{pct.get('draw'):.1f}%" if pct.get('draw') is not None else "—", "sub"),
                     ("   فوز الضيف: ", None), (f"{pct.get('away'):.1f}%" if pct.get('away') is not None else "—", "sub")]
            w(parts)
            if p.get("winner"):
                w(f"الفريق الذي يرجحه المزود: {p['winner']}" + (f" — {p['winner_comment']}" if p.get("winner_comment") else ""))
            if p.get("advice"):
                w(f"نصيحة/خلاصة المزود: {p['advice']}", "sub")
            if p.get("under_over"):
                w(f"توقع خط الأهداف: {p['under_over']}")
            if p.get("goals_home") or p.get("goals_away"):
                w(f"أهداف الفريقين حسب المزود: المضيف {p.get('goals_home', '—')} | الضيف {p.get('goals_away', '—')}")
            if p.get("win_or_draw") is not None:
                w(f"فرصة الفوز أو التعادل للفريق الذي عيّنه المزود: {'نعم' if p['win_or_draw'] else 'لا'}", "muted")
            comparison = p.get("comparison") or {}
            comparison_labels = {
                "form": "الفورمة", "att": "الهجوم", "def": "الدفاع",
                "poisson_distribution": "توزيع بواسون لدى المزود",
                "h2h": "المواجهات المباشرة", "total": "المقارنة الإجمالية",
            }
            shown_comparison = False
            for key, label in comparison_labels.items():
                item = comparison.get(key)
                if isinstance(item, dict) and (item.get("home") is not None or item.get("away") is not None):
                    w(f"{label}: {fixture.get('home', 'المضيف')} {item.get('home', '—')} | "
                      f"{fixture.get('away', 'الضيف')} {item.get('away', '—')}", "muted")
                    shown_comparison = True
            if shown_comparison:
                w("المؤشرات أعلاه من مقارنة المزود الخارجي وليست قيماً محسوبة بواسطة نموذج البرنامج.", "muted")

            market_pct = {"home": pct.get("home"), "draw": pct.get("draw"), "away": pct.get("away")}
            w("مقارنة سريعة مع نموذج البرنامج", "sub")
            model_probs = r.get("1x2", [None, None, None])
            for label, key, mp in (("فوز المضيف", "home", model_probs[0]),
                                   ("التعادل", "draw", model_probs[1]),
                                   ("فوز الضيف", "away", model_probs[2])):
                sp = market_pct.get(key)
                if sp is not None:
                    w(f"{label}: النموذج {mp * 100:.1f}% | مزود الموقع {sp:.1f}% | الفرق {mp * 100 - sp:+.1f} نقطة مئوية", "muted")

        w("أودز شركات المراهنات", "title")
        odds = ext.get("odds", {})
        if not odds.get("available"):
            w(odds.get("message", "لا توجد أودز متاحة."), "muted")
        else:
            w(f"عدد الشركات التي أعادت بيانات: {odds.get('books', 0)}", "sub")
            book_names = sorted({name for item in odds.get("rows", []) for name in item.get("bookmakers", [])})
            if book_names:
                w("الشركات/المواقع: " + "، ".join(book_names), "muted")
            w("السوق | الاختيار | متوسط الأودز | أفضل أودز | احتمال السوق بعد إزالة الهامش | عدد الشركات", "muted")
            for item in odds.get("rows", []):
                probability = (f"{item['prob'] * 100:.1f}%" if item.get("prob") is not None else "—")
                w(f"{item.get('market_ar', item['market'])} | {item.get('outcome_ar', item['outcome'])} | "
                  f"{item['avg_odd']:.2f} | {item['best_odd']:.2f} | {probability} | {item['books']}")
                per_book = item.get("book_odds") or []
                if per_book:
                    w("   أسعار الشركات: " + " | ".join(f"{b['book']}: {b['odd']:.2f}" for b in per_book), "muted")
            value_bets = calculate_value_bets(r, odds, 0.03)
            w("فرص القيمة المتوقعة (Value Bets)", "title")
            if not value_bets:
                w("لا توجد حالياً فرص تتجاوز عتبة EV البالغة 3% في الأسواق التي أمكن مطابقتها.", "muted")
            else:
                for vb in value_bets[:12]:
                    w(f"{vb['market']} — {vb['outcome']} | احتمال النموذج {vb['probability']:.1%} | "
                      f"أفضل أودز {vb['best_odd']:.2f} | EV {vb['ev']:+.1%} | "
                      f"الفارق عن الاحتمال الضمني {vb['edge']:+.1%} | شركات: {vb['books']}", "sub" if vb['ev'] >= 0.05 else "muted")
            h2h_rows = [x for x in odds.get("rows", [])
                        if x["market"].strip().casefold() in ("match winner", "1x2", "fulltime result")]
            if h2h_rows:
                w("مقارنة أودز 1X2 مع احتمال نموذج البرنامج", "sub")
                model_by_outcome = {"home": r["1x2"][0], "draw": r["1x2"][1], "away": r["1x2"][2]}
                outcome_map = {"home": "home", "draw": "draw", "away": "away"}
                for item in h2h_rows:
                    key = outcome_map.get(item["outcome"].strip().casefold())
                    if key:
                        model_p = model_by_outcome[key]
                        market_p = item.get("prob")
                        diff = f" | الفرق عن السوق {model_p * 100 - market_p * 100:+.1f} نقطة" if market_p is not None else ""
                        raw_ev = model_p * item["best_odd"] - 1.0
                        w(f"{item.get('outcome_ar', item['outcome'])}: نموذج {model_p * 100:.1f}% | أفضل سعر {item['best_odd']:.2f}"
                          f"{diff} | العائد النظري الخام وفق النموذج {raw_ev * 100:+.1f}%", "muted")
        w()
        w("طريقة القراءة والقيود", "title")
        w("احتمال السوق يُحسب من أسعار كل شركة بعد إزالة الهامش داخل السوق نفسه، ثم يؤخذ متوسط الشركات المتاحة. أفضل أودز هو أعلى سعر ظهر في الرد، وقد يتغير بسرعة.", "muted")
        w("العائد النظري الخام = احتمال النموذج × أفضل أودز − 1؛ وهو مؤشر حسابي غير مضمون ويتأثر بمعايرة النموذج وجودة البيانات، وليس توصية تلقائية بالمراهنة.", "muted")
        w("توقعات الموقع تأتي من خوارزمية المزود وليست ضماناً. عدم ظهور سوق أو أودز لا يعني أن الاحتمال صفر؛ قد تكون البيانات غير متاحة لهذه المباراة.", "warn")
        w("لا يدمج البرنامج توقعات الموقع تلقائياً داخل احتمالات النموذج؛ يعرضهما جنباً إلى جنب لتجنب إخفاء اختلاف المصدرين.", "muted")
        t.config(state="disabled")

    def _team_block(self, t, name, p, role, venue_ar):
        w = lambda *a, **k: self._put(t, *a, **k)  # noqa: E731
        w(f"{name} — {role}", "title")
        v = "home" if p["venue"] == "home" else "away"
        att_v, def_v = p["att_" + v], p["def_" + v]
        for label, a_all, a_ven in (("الهجوم", p["att_all"], att_v),):
            lt, lk = attack_label(a_ven)
            w([(f"{label}: ", "sub"), (f"عام {a_all:.2f}  |  {venue_ar} {a_ven:.2f}  ", None),
               (f" {lt} ", "t_" + lk)])
        lt, lk = defence_label(def_v)
        w([("الدفاع: ", "sub"), (f"عام {p['def_all']:.2f}  |  {venue_ar} {def_v:.2f}  ", None),
           (f" {lt} ", "t_" + lk), ("   (الأقل أفضل — 1.00 = متوسط الدوري)", "muted")])

        a5 = p["a5"]
        if a5:
            parts = [("الفورمة (آخر 5، الأقدم → الأحدث): ", "sub")]
            for g in reversed(p["last5"]):
                k = "strong" if g["res"] == "ف" else "medium" if g["res"] == "ت" else "weak"
                parts.append((f" {g['res']} ", "t_" + k))
                parts.append((" ", None))
            fi = p["form_index"]
            trend = ("أعلى من مستواه المعتاد" if fi > 0.08 else "أقل من مستواه المعتاد" if fi < -0.08
                     else "قريبة من مستواه المعتاد")
            parts.append((f"  {a5['pts']} نقاط • {a5['ppg']:.2f} ن/م مقابل {p['ppg_all']:.2f} للفترة — {trend}", None))
            w(parts)
            w(f"آخر 5: يسجل {a5['gf']:.2f} ويستقبل {a5['ga']:.2f} هدف/مباراة", "muted")
        a10 = p["a10"]
        if a10:
            w(f"آخر {a10['n']}: يسجل {a10['gf']:.2f} ويستقبل {a10['ga']:.2f} • شباك نظيفة {a10['clean'] * 100:.0f}% • "
              f"لم يسجل {a10['failed'] * 100:.0f}% • كلا الفريقين سجّل {a10['btts'] * 100:.0f}% • "
              f"أكثر من 2.5 هدف {a10['over25'] * 100:.0f}%", "muted")
        av = p["a_venue"]
        if av:
            w(f"آخر {av['n']} مباريات {venue_ar}: {av['ppg']:.2f} ن/م • يسجل {av['gf']:.2f} ويستقبل {av['ga']:.2f}", "muted")
        w()

    # ---- مسح وتصدير ----
    def _render_professional_dashboards(self, r):
        # إحصاءات مختصرة ورسم احتمالات 1X2 باستخدام Canvas المدمج
        c = self.stats_canvas
        c.delete("all")
        probs = r.get("1x2", [0,0,0])
        names = [f"فوز {r['home']}", "تعادل", f"فوز {r['away']}"]
        colors = ["#2878b5", "#e3a326", "#39a078"]
        width = max(c.winfo_width(), 520)
        c.create_text(width-12, 18, text="احتمالات نتيجة المباراة", anchor="e", font=("Segoe UI", 12, "bold"), fill="#26384a")
        for i,(name,p,color) in enumerate(zip(names,probs,colors)):
            y=55+i*48
            c.create_text(width-12,y, text=f"{name}  {p:.1%}", anchor="e", font=("Segoe UI",10), fill="#26384a")
            x0=12; x1=max(20,width-190)
            c.create_rectangle(x0,y+10,x1,y+25,fill="#edf1f5",outline="")
            c.create_rectangle(x0,y+10,x0+(x1-x0)*max(0,min(1,p)),y+25,fill=color,outline="")
        c.configure(height=205)
        self.stats_summary.config(text=f"الأهداف المتوقعة: {r['home']} {r['lambda_home']:.2f} — {r['lambda_away']:.2f} {r['away']}  |  جودة البيانات: {r.get('quality','—')}  |  العينة: {r.get('sample','—')}")
        for item in self.value_tree.get_children(): self.value_tree.delete(item)
        ext=(r.get("external") or {}).get("odds") or {}
        bets=calculate_value_bets(r,ext,0.0)
        for b in bets:
            self.value_tree.insert("", "end", values=(b.get("market","—"),b.get("outcome","—"),f"{b.get('probability',0):.1%}",f"{b.get('best_odd',0):.2f}",f"{b.get('ev',0):+.1%}",b.get("book","—")))
        self.value_note.config(text=f"تم العثور على {len(bets)} فرصة/فرص حسب حد EV الحالي. تحقّق من الأسعار الفعلية قبل اتخاذ أي قرار.")
        for item in self.goals_tree.get_children(): self.goals_tree.delete(item)
        for key,label in (("over15","أكثر من 1.5 هدف"),("over25","أكثر من 2.5 هدف"),("over35","أكثر من 3.5 هدف"),("btts","يسجل الفريقان (BTTS)")):
            p=r.get(key)
            if p is not None: self.goals_tree.insert("", "end", values=(label,f"{p:.1%}","نموذج احتمالي"))
        top=r.get("ft",{}).get("scores",[])[:5]
        self.goals_scores.config(text="أكثر النتائج الدقيقة احتمالاً: "+"   |   ".join(f"{h}-{a} ({p:.1%})" for p,h,a in top))

    def _refresh_dashboard_live(self):
        code=LEAGUES.get(self.league.get(),"")
        self.status.set("جارٍ تحميل المباريات المباشرة للوحة...")
        def worker():
            try:
                events=parse_espn_live_events(fetch_espn_live(code))
                self.after(0,lambda:self._dashboard_live_loaded(events))
            except Exception as exc:
                self.after(0,lambda:self.status.set("تعذر تحديث المباشر: "+str(exc)))
        threading.Thread(target=worker,daemon=True).start()

    def _dashboard_live_loaded(self, events):
        for item in self.live_dashboard_tree.get_children(): self.live_dashboard_tree.delete(item)
        for x in events:
            self.live_dashboard_tree.insert("", "end", values=(x.get("home","—"),f"{x.get('hs',0)} - {x.get('as',0)}",x.get("away","—"),x.get("clock","—"),x.get("stats","—"),x.get("status","—")))
        self.status.set(f"لوحة المباشر: تم تحديث {len(events)} مباراة من ESPN.")

    def clear_result(self):
        self._external_request_id += 1
        self.last_result = None
        self._history_current_id = None
        self.tree.delete(*self.tree.get_children())
        for tx in (self.txt_halves, self.txt_deep, self.txt_external):
            self._reset_text(tx)
            tx.config(state="disabled")
        self.banner.config(text="حلّل مباراة لعرض أفضل اختيار.", bg="#e6eaf0", fg="#34445a")
        self.banner_sub.config(text="")
        self.banner_hi.config(text="", bg="#ffffff")
        for item in self.value_tree.get_children(): self.value_tree.delete(item)
        for item in self.goals_tree.get_children(): self.goals_tree.delete(item)
        self.stats_canvas.delete("all")
        self.stats_summary.config(text="حلّل مباراة لعرض مؤشرات النموذج.")
        self.goals_summary.config(text="تحليل Over/Under وBTTS والنتائج الدقيقة يظهر بعد تحليل مباراة.")
        self.goals_scores.config(text="")
        self.status.set("تم مسح النتائج.")

    def export_result(self):
        if not self.last_result:
            messagebox.showinfo("التصدير", "حلّل مباراة أولاً.")
            return
        path = filedialog.asksaveasfilename(
            title="حفظ التحليل", defaultextension=".csv", filetypes=[("CSV files", "*.csv")])
        if not path:
            return
        r = self.last_result
        info = r["pick"]
        pick = info["pick"]
        sh_h, sh_a = r["half_shares"]
        general = [
            ("الفريق المضيف", r["home"]), ("الفريق الضيف", r["away"]),
            ("أهداف المضيف المتوقعة", f'{r["lambda_home"]:.3f}'),
            ("أهداف الضيف المتوقعة", f'{r["lambda_away"]:.3f}'),
            ("النتيجة النهائية الأرجح", "{}-{}".format(*r["ft"]["scores"][0][1:])),
            ("الشوط الأول الأرجح", "{}-{}".format(*r["fh"]["scores"][0][1:])),
            ("الشوط الثاني الأرجح", "{}-{}".format(*r["sh"]["scores"][0][1:])),
            ("مصدر نسبة الشوطين", "فعلية" if r["share_src"] == "actual" else "مفترضة"),
            ("جودة البيانات", r["quality"]),
            ("فورمة المضيف", " - ".join(g["res"] for g in reversed(r["ph"]["last5"]))),
            ("فورمة الضيف", " - ".join(g["res"] for g in reversed(r["pa"]["last5"]))),
            ("أفضل اختيار", f"{pick['name']} ({self._pct(pick['p'])}) | أودز {self._odds_text(pick, short=True)}"
             if pick else "لا يوجد: " + info["reason"]),
            ("أعلى 10 نتائج دقيقة", " | ".join(f"{h}-{a}: {p:.1%}" for p,h,a in r.get("scores", [])[:10])),
            ("اختيار بأودز أعلى (نفس اتجاه التحليل)", (lambda hm: f"{hm['name']} ({self._pct(hm['p'])}) | أودز {self._odds_text(hm, short=True)}"
                                    if hm else "لا يوجد")((r.get("high_pick") or {}).get("market"))),
        ]
        external = r.get("external") or {}
        if external.get("fixture"):
            general.extend([
                ("مصدر التوقعات والأودز", external.get("provider", "API-Football")),
                ("Fixture ID الخارجي", external["fixture"].get("id", "")),
                ("عدد شركات الأودز", (external.get("odds") or {}).get("books", 0)),
                ("توقع الموقع", (external.get("predictions") or {}).get("advice", "")),
            ])
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as f:
                wr = csv.writer(f)
                wr.writerow(["المؤشر", "القيمة"])
                wr.writerows(general)
                wr.writerow([])
                wr.writerow(["المجموعة", "السوق", "الاحتمال", "المحافظ", "المستوى", "الأودز", "نوع الأودز"])
                for m in r["markets"]:
                    wr.writerow([m["group"], m["name"], self._pct(m["p"]),
                                 self._pct(m["adj"]) if m["pickable"] else "—", m["tier"].label,
                                 self._odds_text(m, short=True),
                                 "سعر السوق" if (m.get("odds") or {}).get("kind") == "market" else "نموذجية"])
                external = r.get("external") or {}
                odds = external.get("odds") or {}
                if odds.get("rows"):
                    wr.writerow([])
                    wr.writerow(["الأودز الخارجية", "السوق", "الاختيار", "متوسط الأودز", "أفضل أودز", "احتمال السوق", "عدد الشركات"])
                    for item in odds["rows"]:
                        wr.writerow(["API-Football", item["market"], item["outcome"],
                                     f"{item['avg_odd']:.3f}", f"{item['best_odd']:.3f}",
                                     self._pct(item["prob"]) if item.get("prob") is not None else "—",
                                     item["books"]])
            self.status.set("تم حفظ ملف CSV.")
        except Exception as exc:
            messagebox.showerror("التصدير", str(exc))


def main():
    app = PredictorApp()
    app.mainloop()


if __name__ == "__main__":
    main()
