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
from collections import defaultdict, namedtuple
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from typing import Optional

try:
    import requests
except ImportError:
    requests = None

APP_TITLE = "محلل كرة القدم PRO MAX 5.6 — فلترة صارمة للتوقعات"
API_BASE = "https://api.football-data.org/v4"
APP_DIR = os.path.dirname(os.path.abspath(sys.executable if getattr(sys, "frozen", False) else __file__))
# تُحفظ الإعدادات والبيانات بجوار ملف البرنامج، ولا تُحمّل إلا المسابقة المختارة.
DATA_DIR = os.environ.get("ANDROID_PRIVATE") or os.environ.get("FP_DATA_DIR") or APP_DIR
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


# ====================== اختبار Walk-forward (من الملف الأصلي) ======================

def calculate_backtest(matches, half_share=0.45, form_weight=0.08):
    """
    Expanding-window walk-forward validation:
    every tested fixture is predicted only from matches dated strictly earlier.
    A bounded, evenly spaced test sample keeps the UI responsive on large seasons.
    """
    ordered = sorted(matches, key=lambda m: m.played)
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


# ====================== تحويل النتيجة إلى أسطر للعرض ======================



def pct(p):
    return f"{p * 100:.1f}%"


def _odds(m):
    o = m.get("odds") or {}
    if not o:
        return ""
    return f"{o['value']:.2f}" + (" سوق" if o.get("kind") == "market" else " نموذج")


def _mline(m):
    return (tier_of(m["p"]).key, f"{m['name']}  {pct(m['p'])}  @{_odds(m)}")


def _team(p, name):
    L = [("head", name)]
    t, k = attack_label(p["att_all"]); L.append((k, f"{t} ({p['att_all']:.2f})"))
    t, k = defence_label(p["def_all"]); L.append((k, f"{t} ({p['def_all']:.2f})"))
    a5, a10 = p.get("a5"), p.get("a10")
    L.append(("txt", "آخر 5: " + (" ".join(g["res"] for g in p["last5"]) or "—")))
    if a5:
        L.append(("mut", f"أهداف له/عليه {a5['gf']:.1f}/{a5['ga']:.1f} | نظيفة {a5['clean'] * 100:.0f}%"))
    if a10:
        L.append(("mut", f"آخر 10: نقاط/مباراة {a10['ppg']:.2f} | كلاهما يسجل {a10['btts'] * 100:.0f}% | +2.5 {a10['over25'] * 100:.0f}%"))
    return L


def result_lines(r):
    H, D, A = r["1x2"]
    L = [("head", f"{r['home']}  ضد  {r['away']}"),
         (tier_of(H).key, f"فوز {r['home']}: {pct(H)}"),
         (tier_of(D).key, f"تعادل: {pct(D)}"),
         (tier_of(A).key, f"فوز {r['away']}: {pct(A)}"),
         ("mut", f"الأهداف المتوقعة {r['lambda_home']:.2f} - {r['lambda_away']:.2f} | {r['confidence']} ({r['quality']}/100)")]
    pk = r.get("pick") or {}
    L.append(("head", "الاختيار الرئيسي"))
    if pk.get("pick"):
        m = pk["pick"]
        L.append((tier_of(m["p"]).key, f"{m['name']}  {pct(m['p'])}  (محافظ {pct(m['adj'])})  @{_odds(m)}"))
        for a in pk.get("alts", []):
            L.append(("txt", "بديل بنفس الاتجاه: " + _mline(a)[1]))
    else:
        L.append(("weak", "لا اختيار"))
        L.append(("mut", pk.get("reason", "")))
    hp = r.get("high_pick")
    if hp is not None:
        L.append(("head", "اختيار بأودز أعلى (نفس الاتجاه)"))
        if hp.get("market"):
            L.append(_mline(hp["market"]))
            L.append(("mut", "الاتجاه: " + hp.get("direction_label", "")))
        else:
            L.append(("mut", hp.get("reason", "")))
    L.append(("head", "النتائج الدقيقة الأرجح"))
    L.append(("txt", " | ".join(f"{i}-{j} ({pct(p)})" for p, i, j in r["scores"][:6])))
    for lab, key in (("الشوط الأول", "fh"), ("الشوط الثاني", "sh")):
        h, d, a = r[key]["probs"]
        L.append(("txt", f"{lab}: 1 {pct(h)} | X {pct(d)} | 2 {pct(a)}"))
    L.append(("mut", "نسبة الشوطين: " + ("من بيانات فعلية" if r["share_src"] == "actual" else "مفترضة")))
    L.append(("head", "كل الأسواق"))
    grp = None
    for m in r["markets"]:
        if m["group"] != grp:
            grp = m["group"]; L.append(("mut", "— " + grp))
        L.append(_mline(m))
    L += _team(r["ph"], r["home"] + " (مضيف)") + _team(r["pa"], r["away"] + " (ضيف)")
    if r.get("h2h"):
        L.append(("head", "المواجهات المباشرة"))
        for m in r["h2h"]:
            L.append(("txt", f"{m.played}  {m.home} {m.hg}-{m.ag} {m.away}"))
    av = r.get("availability") or {}
    if av.get("available"):
        L.append(("head", "الإصابات والتشكيلة (ESPN)"))
        L.append(("mut", av.get("lineup_status", "")))
        for t in av.get("teams", []):
            inj = t.get("injuries", [])
            L.append(("txt", f"{t['team']}: {len(inj)} غياب"))
            for x in inj[:8]:
                L.append(("mut", f"  {x['name']} — {x['status']} {x.get('position', '')}"))
    ext = r.get("external") or {}
    if r.get("external_status") == "loading":
        L.append(("mut", "جارٍ جلب الأودز والإصابات من ESPN..."))
    if ext.get("error"):
        L.append(("weak", "الأودز: " + str(ext["error"])))
    rows = (ext.get("odds") or {}).get("rows") or []
    if rows:
        L.append(("head", f"أفضل أودز الشركات ({ext.get('provider', '')})"))
        for x in rows[:18]:
            L.append(("txt", f"{x.get('market_ar', x['market'])} / {x.get('outcome_ar', x['outcome'])}: {x['best_odd']} (متوسط {x.get('avg_odd', '')}) ×{x.get('books', 1)}"))
    vb = r.get("value_bets") or []
    if vb:
        L.append(("head", "Value Bets"))
        for v in vb[:8]:
            L.append(("strong", f"{v['market']} / {v['outcome']}: احتمال {pct(v['probability'])} أودز {v['best_odd']:.2f} EV {v['ev'] * 100:+.1f}%"))
    if r.get("notes"):
        L.append(("head", "ملاحظات"))
        L += [("mut", n) for n in r["notes"]]
    L.append(("mut", "الاحتمالات ليست ضماناً ولا توصية مالية."))
    return L


def backtest_lines(b):
    if not b.get("ok"):
        return [("weak", b.get("reason", "تعذر الاختبار"))]
    return [("head", "اختبار Walk-forward"),
            ("txt", f"عدد المباريات: {b['n']} من {b['tested_total']}"),
            ("txt", f"دقة 1X2: {pct(b['accuracy'])}"),
            ("txt", f"النتيجة الدقيقة: {pct(b['exact_score'])}"),
            ("txt", f"Brier: {b['brier']:.3f}   متوسط خطأ الأهداف: {b['mae_goals']:.2f}"),
            ("mut", b["method"])]


def live_lines(events):
    if not events:
        return [("mut", "لا توجد مباريات.")]
    return [("good" if e["state"] == "in" else "txt",
             f"{e['home']} {e['hs']}-{e['as']} {e['away']}   [{e['status']}]") for e in events]


# ====================== إعدادات البناء مضمّنة في هذا الملف ======================
# لإنشاء ملفي البناء (buildozer.spec و .github/workflows/build.yml) بجوار هذا الملف:
#     python main.py --setup
BUILDOZER_SPEC = """[app]
title = Football Predictor
package.name = footballpredictor
package.domain = org.fp
source.dir = .
source.include_exts = py,json
version = 5.6
requirements = python3,kivy==2.3.0,requests,urllib3,chardet,idna,certifi,charset-normalizer,arabic-reshaper==3.0.0,python-bidi==0.4.2
orientation = portrait
fullscreen = 0
android.permissions = INTERNET,READ_EXTERNAL_STORAGE,WRITE_EXTERNAL_STORAGE
android.api = 33
android.minapi = 24
android.archs = arm64-v8a
android.accept_sdk_license = True

[buildozer]
log_level = 2
warn_on_root = 1
"""

GITHUB_WORKFLOW = """name: Build APK
on:
  push:
  workflow_dispatch:
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: ArtemSBulgakov/buildozer-action@v1
        id: buildozer
        with:
          command: buildozer android debug
          buildozer_version: stable
      - uses: actions/upload-artifact@v4
        with:
          name: football-predictor-apk
          path: ${{ steps.buildozer.outputs.filename }}
"""

if __name__ == "__main__" and "--setup" in sys.argv:
    _d = os.path.dirname(os.path.abspath(__file__))
    os.makedirs(os.path.join(_d, ".github", "workflows"), exist_ok=True)
    with open(os.path.join(_d, "buildozer.spec"), "w", encoding="utf-8", newline="\n") as _f:
        _f.write(BUILDOZER_SPEC)
    with open(os.path.join(_d, ".github", "workflows", "build.yml"), "w", encoding="utf-8", newline="\n") as _f:
        _f.write(GITHUB_WORKFLOW)
    print("تم إنشاء buildozer.spec و .github/workflows/build.yml")
    sys.exit(0)


# ====================== واجهة Kivy للهاتف ======================
# KIVY-UI-START
import sys
E = R = BT = sys.modules[__name__]
import os, json, uuid, threading, textwrap
from datetime import datetime
from kivy.app import App
from kivy.clock import Clock
from kivy.core.text import LabelBase
from kivy.core.window import Window
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.button import Button
from kivy.uix.filechooser import FileChooserListView
from kivy.uix.label import Label
from kivy.uix.popup import Popup
from kivy.uix.scrollview import ScrollView
from kivy.uix.spinner import Spinner
from kivy.uix.textinput import TextInput
from kivy.utils import platform
import arabic_reshaper
from bidi.algorithm import get_display

HERE = os.path.dirname(os.path.abspath(__file__))
def _find_font():
    for p in ("/system/fonts/NotoNaskhArabic-Regular.ttf", "/system/fonts/NotoSansArabic-Regular.ttf",
              "/system/fonts/NotoNaskhArabicUI-Regular.ttf", "/system/fonts/DroidSansArabic.ttf",
              "/system/fonts/Roboto-Regular.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
              "C:/Windows/Fonts/segoeui.ttf", "C:/Windows/Fonts/arial.ttf"):
        if os.path.exists(p):
            return p
    return None


FONT = _find_font()
if FONT:
    LabelBase.register(name="AR", fn_regular=FONT, fn_bold=FONT)
else:
    LabelBase.register(name="AR", fn_regular="Roboto")


def _setup_dirs():
    app = App.get_running_app()
    d = app.user_data_dir if app else os.path.expanduser("~")
    os.makedirs(d, exist_ok=True)
    os.environ["FP_DATA_DIR"] = d


class FPApp(App):
    title = "محلل كرة القدم PRO"

    def build(self):
        _setup_dirs()
        self.model = self.matches = self.last = None
        self.hist = self._load(E.HISTORY_PATH, [])
        self.cfg = self._load(E.CONFIG_PATH, {})
        Window.clearcolor = (.07, .09, .11, 1)
        self.colors = {"strong": (.35, .87, .55, 1), "good": (.45, .72, 1, 1), "medium": (1, .85, .35, 1),
                       "weak": (1, .5, .45, 1), "head": (.4, .85, .6, 1), "mut": (.62, .67, .72, 1), "txt": (.93, .95, .97, 1)}
        root = BoxLayout(orientation="vertical", padding=6, spacing=4)
        self.status = self.lbl("جاهز. حمّل البيانات أو استورد CSV.", "mut")
        root.add_widget(self.status)
        sv = ScrollView(do_scroll_x=False)
        self.box = BoxLayout(orientation="vertical", size_hint_y=None, spacing=4, padding=4)
        self.box.bind(minimum_height=self.box.setter("height"))
        sv.add_widget(self.box)
        root.add_widget(sv)
        self.league = Spinner(text=self.cfg.get("league", list(E.LEAGUES)[0]), values=list(E.LEAGUES), font_name="AR", size_hint_y=None, height=96)
        self.key = TextInput(text=self.cfg.get("api_key", ""), hint_text="football-data.org key", password=True, multiline=False, size_hint_y=None, height=90)
        self.skey = TextInput(text=self.cfg.get("api_sports_key", ""), hint_text="API-Football key (optional)", password=True, multiline=False, size_hint_y=None, height=90)
        self.date = TextInput(text=self.cfg.get("match_date", ""), hint_text="YYYY-MM-DD (optional)", multiline=False, size_hint_y=None, height=90)
        self.home = Spinner(text="Home", values=[], size_hint_y=None, height=96)
        self.away = Spinner(text="Away", values=[], size_hint_y=None, height=96)
        for w in (self.league, self.key, self.skey, self.date):
            self.box.add_widget(w)
        self.btn_row([("تحميل API", self.load_api), ("استيراد CSV", self.pick_csv)])
        self.box.add_widget(self.home); self.box.add_widget(self.away)
        self.btn_row([("احسب التوقع", self.predict), ("مباشر", self.live)])
        self.btn_row([("Backtest", self.backtest), ("السجل", self.show_history)])
        self.out = BoxLayout(orientation="vertical", size_hint_y=None, spacing=2)
        self.out.bind(minimum_height=self.out.setter("height"))
        self.box.add_widget(self.out)
        if platform == "android":
            try:
                from android.permissions import request_permissions, Permission
                request_permissions([Permission.READ_EXTERNAL_STORAGE, Permission.WRITE_EXTERNAL_STORAGE])
            except Exception:
                pass
        return root

    # ---------- أدوات ----------
    @staticmethod
    def ar(text):
        return get_display(arabic_reshaper.reshape(text))

    def lbl(self, text, key="txt"):
        w = Window.width - 24
        l = Label(text=self.ar(text), font_name="AR", font_size="15sp", color=self.colors.get(key, (1, 1, 1, 1)) if hasattr(self, "colors") else (1, 1, 1, 1),
                  size_hint_y=None, halign="right", valign="middle", text_size=(w, None))
        l.bind(texture_size=lambda i, v: setattr(i, "height", v[1] + 6))
        return l

    def btn_row(self, items):
        r = BoxLayout(size_hint_y=None, height=100, spacing=6)
        for t, f in items:
            b = Button(text=self.ar(t), font_name="AR", on_release=lambda *_a, f=f: f())
            r.add_widget(b)
        self.box.add_widget(r)

    def show(self, lines):
        self.out.clear_widgets()
        for key, text in lines:
            for chunk in textwrap.wrap(str(text), 36) or [""]:
                self.out.add_widget(self.lbl(chunk, key))

    def say(self, t):
        Clock.schedule_once(lambda *_: setattr(self.status, "text", self.ar(t)))

    def ui(self, f, *a):
        Clock.schedule_once(lambda *_: f(*a))

    @staticmethod
    def _load(path, default):
        try:
            with open(path, encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return default

    def save_cfg(self):
        try:
            with open(E.CONFIG_PATH, "w", encoding="utf-8") as f:
                json.dump({"api_key": self.key.text.strip(), "api_sports_key": self.skey.text.strip(),
                           "match_date": self.date.text.strip(), "league": self.league.text}, f, ensure_ascii=False)
        except Exception:
            pass

    # ---------- البيانات ----------
    def load_api(self):
        k = self.key.text.strip()
        if not k:
            return self.say("أدخل مفتاح football-data.org أولاً.")
        self.save_cfg(); self.say("جارٍ تحميل نتائج المواسم...")
        code = E.LEAGUES[self.league.text]

        def w():
            try:
                rows, name, errs = E.fetch_competition(code, k, 2)
                self.ui(self.data_ready, rows, name + " • API")
            except Exception as ex:
                self.say("تعذر التحميل: " + str(ex))
        threading.Thread(target=w, daemon=True).start()

    def pick_csv(self):
        start = "/storage/emulated/0/Download" if platform == "android" else os.path.expanduser("~")
        fc = FileChooserListView(path=start if os.path.isdir(start) else HERE, filters=["*.csv"])
        pop = Popup(title="CSV", content=fc, size_hint=(.95, .85))

        def sel(_i, files):
            if files:
                pop.dismiss()
                try:
                    self.data_ready(E.load_csv(files[0]), os.path.basename(files[0]))
                except Exception as ex:
                    self.say("خطأ CSV: " + str(ex))
        fc.bind(on_submit=sel)
        pop.open()

    def data_ready(self, rows, name):
        try:
            self.model = E.FootballModel(rows)
        except Exception as ex:
            return self.say(str(ex))
        self.matches = rows
        t = self.model.teams
        self.home.values = t; self.away.values = t
        self.home.text = t[0]; self.away.text = t[min(1, len(t) - 1)]
        self.say(f"✔ {name}: {len(rows)} مباراة، {len(t)} فريقاً")

    # ---------- التوقع ----------
    def predict(self):
        if not self.model:
            return self.say("حمّل البيانات أو استورد CSV أولاً.")
        h, a = self.home.text, self.away.text
        try:
            r = self.model.predict(h, a)
            E.enrich_result_with_odds(r)
        except Exception as ex:
            return self.say("تعذر التحليل: " + str(ex))
        self.last = r; r["external_status"] = "loading"
        self.show(R.result_lines(r)); self.save_cfg()
        self.rec_id = uuid.uuid4().hex[:12]
        self.record(r)
        self.say("اكتمل التحليل الأساسي؛ جارٍ فحص ESPN...")
        code, day, key = E.LEAGUES[self.league.text], self.date.text.strip(), self.skey.text.strip()

        def w():
            ext = ctx = None
            try:
                ext = E.fetch_external_match_data(key, code, h, a, day)
            except Exception as ex:
                ext = {"error": str(ex)}
            try:
                ctx = E.fetch_espn_team_context(code, h, a, day)
            except Exception as ex:
                ctx = {"available": False, "error": str(ex)}
            self.ui(self.ext_ready, r, ext, ctx, h, a)
        threading.Thread(target=w, daemon=True).start()

    def ext_ready(self, old, ext, ctx, h, a):
        if self.last is not old:
            return
        try:
            r = self.model.predict(h, a, team_context=ctx) if ctx.get("available") else old
        except Exception:
            r = old
        r["availability"] = ctx; r["external"] = ext; r["external_status"] = "ready"
        E.enrich_result_with_odds(r)
        r["value_bets"] = E.calculate_value_bets(r, (ext or {}).get("odds") or {}, 0.03)
        self.last = r
        self.record(r, update=True)
        self.show(R.result_lines(r))
        self.say(f"اكتمل التحليل. Value Bets: {len(r['value_bets'])}")

    # ---------- السجل ----------
    def record(self, r, update=False):
        try:
            pk = (r.get("pick") or {}).get("pick")
            row = next((x for x in self.hist if x["id"] == self.rec_id), None)
            if row is None:
                row = {"id": self.rec_id, "created_at": datetime.now().astimezone().isoformat(timespec="seconds"),
                       "home": r["home"], "away": r["away"], "pick": pk["name"] if pk else "بدون اختيار",
                       "probability": pk["p"] if pk else None, "status": "pending",
                       "predicted_score": "{}-{}".format(*r["scores"][0][1:])}
                self.hist.append(row)
            row["value_bets"] = r.get("value_bets", [])
            with open(E.HISTORY_PATH, "w", encoding="utf-8") as f:
                json.dump(self.hist, f, ensure_ascii=False, indent=1)
        except Exception:
            pass

    def show_history(self):
        L = [("head", f"سجل التوقعات ({len(self.hist)})")]
        for x in reversed(self.hist[-30:]):
            p = f" {x['probability'] * 100:.0f}%" if x.get("probability") else ""
            L.append(("txt", f"{x['created_at'][:10]}  {x['home']} - {x['away']}  | {x['pick']}{p}  | {x['predicted_score']}"))
        self.show(L)

    # ---------- مباشر / Backtest ----------
    def live(self):
        code, day = E.LEAGUES[self.league.text], self.date.text.strip() or None
        self.say("جارٍ جلب المباريات...")

        def w():
            try:
                ev = E.parse_espn_live_events(E.fetch_espn_live(code, day))
                self.ui(self.show, R.live_lines(ev)); self.say("تم.")
            except Exception as ex:
                self.say("تعذر: " + str(ex))
        threading.Thread(target=w, daemon=True).start()

    def backtest(self):
        if not self.matches:
            return self.say("حمّل البيانات أولاً.")
        self.say("جارٍ الاختبار (قد يستغرق دقيقة)...")

        def w():
            b = BT.calculate_backtest(self.matches, self.model.fallback_share, self.model.form_weight)
            self.ui(self.show, R.backtest_lines(b)); self.say("اكتمل Backtest.")
        threading.Thread(target=w, daemon=True).start()


if __name__ == "__main__":
    FPApp().run()
