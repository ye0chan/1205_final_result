"""
약결: 일반의약품 구매 전 성분 중복·주의사항 확인 보조 앱.

Python 3.11 또는 3.12 권장.

실행:
    pip install -r requirements.txt
    streamlit run app.py

Streamlit Settings > Secrets 또는 환경변수:
    MFDS_SERVICE_KEY = "공공데이터포털 일반인증키"
    GOOGLE_VISION_API_KEY = "선택: Google Cloud Vision API 키"

공공데이터포털에서 다음 API 활용승인이 각각 필요합니다.
- 의약품 제품 허가정보 08
- DUR 품목정보 03
- e약은요

로그인과 영구 데이터베이스를 사용하지 않습니다.
프로필은 접속 세션의 서버 메모리에 보관합니다.

이 앱은 복용 가능 여부, 중단, 용량 변경을 결정하지 않습니다.
자료 없음은 안전하다는 의미가 아닙니다.
교육용 그래프는 실제 개인의 혈중농도를 예측하지 않습니다.

공식 API 명세 및 근거 검토일: 2026-11-13.
실제 승인키를 사용한 통합 검증은 별도로 필요합니다.
"""

import base64
import copy
import csv
import hashlib
import html
import io
import json
import math
import os
import re
import unicodedata
import urllib.parse
import uuid
import xml.etree.ElementTree as ET
from collections import defaultdict
from datetime import datetime, timezone
from itertools import combinations
from pathlib import Path
from zoneinfo import ZoneInfo

import requests
import streamlit as st
from PIL import Image, ImageOps, UnidentifiedImageError


# ============================================================
# 기본 설정
# ============================================================

APP_NAME = "약결"
APP_VERSION = "1.0.0"
REVIEW_DATE = "2026-11-13"

PERMIT_BASE = (
    "https://apis.data.go.kr/1471000/"
    "DrugPrdtPrmsnInfoService08/"
)
DUR_BASE = (
    "https://apis.data.go.kr/1471000/"
    "DURPrdlstInfoService03/"
)
EASY_BASE = (
    "https://apis.data.go.kr/1471000/"
    "DrbEasyDrugInfoService/"
)

MAX_API_BYTES = 12 * 1024 * 1024
API_PAGE_SIZE = 100
API_MAX_PAGES = 30

LEVELS = {
    "contraindication": ("⛔", "공식 병용금기", "#b42318"),
    "duplicate": ("◉", "동일 성분 중복", "#b54708"),
    "caution": ("!", "전문가 확인 필요", "#805500"),
    "unknown": ("?", "미확인 정보", "#475467"),
}

SCOPE_LABELS = {
    "official": "식약처 공식 자료",
    "general": "근거 기반 일반 주의 · 국내 DUR 판정 아님",
    "data": "성분·자료 점검",
}

SOURCES = {
    "mfds": "https://nedrug.mfds.go.kr/",
    "acetaminophen": (
        "https://www.fda.gov/drugs/"
        "safe-use-over-counter-pain-relievers-and-fever-reducers/"
        "acetaminophen"
    ),
    "nsaid": (
        "https://www.nhs.uk/medicines/ibuprofen-for-adults/"
    ),
    "kidney": (
        "https://www.niddk.nih.gov/health-information/"
        "kidney-disease/keeping-kidneys-safe"
    ),
    "hypo": (
        "https://www.niddk.nih.gov/health-information/diabetes/"
        "overview/preventing-problems/low-blood-glucose-hypoglycemia"
    ),
    "beta": (
        "https://www.cdc.gov/diabetes/about/"
        "low-blood-sugar-hypoglycemia.html"
    ),
    "cognition": (
        "https://www.nia.nih.gov/health/"
        "health-care-professionals-information/"
        "caring-older-patients-cognitive-impairment"
    ),
    "pseudo": (
        "https://www.nhs.uk/medicines/pseudoephedrine/"
    ),
    "anticholinergic": (
        "https://www.nhs.uk/medicines/"
        "chlorphenamine-including-piriton/"
        "who-can-and-cannot-take-chlorphenamine/"
    ),
    "asthma": (
        "https://sps.nhs.uk/articles/using-nsaids-in-asthma/"
    ),
    "heart": (
        "https://www.nice.org.uk/guidance/ng106/"
        "chapter/Recommendations"
    ),
    "arthritis": (
        "https://www.nice.org.uk/guidance/ng226/"
        "chapter/Recommendations"
    ),
    "warfarin": (
        "https://www.nhs.uk/medicines/anticoagulants/"
        "considerations/"
    ),
    "grapefruit": (
        "https://www.fda.gov/consumers/consumer-updates/"
        "grapefruit-juice-and-some-drugs-dont-mix"
    ),
    "thyroid": (
        "https://www.dailymed.nlm.nih.gov/dailymed/fda/"
        "fdaDrugXsl.cfm?"
        "setid=758588c3-c63e-491b-0aa2-4f50d80cb174&type=display"
    ),
    "renal_diet": (
        "https://www.niddk.nih.gov/health-information/"
        "kidney-disease/chronic-kidney-disease-ckd/"
        "healthy-eating-adults-chronic-kidney-disease"
    ),
    "insulin": (
        "https://sps.nhs.uk/articles/"
        "managing-the-risk-of-confusion-between-insulin-products/"
    ),
}

CAFFEINE_SOURCES = {
    "식약처 최대 일일섭취권고량": (
        "https://impfood.mfds.go.kr/CFBCC02F02/getCntntsDetail"
        "?cntntsMngId=00005&cntntsSn=278410"
    ),
    "FDA 성인 카페인 안내": (
        "https://www.fda.gov/consumers/consumer-updates/"
        "spilling-beans-how-much-caffeine-too-much"
    ),
    "CDC 반감기 교육자료": (
        "https://www.cdc.gov/niosh/"
        "work-hour-training-for-nurses/longhours/mod6/11.html"
    ),
    "MedlinePlus 테오필린": (
        "https://medlineplus.gov/druginfo/meds/a681006.html"
    ),
    "MedlinePlus 슈도에페드린": (
        "https://medlineplus.gov/druginfo/meds/a682619.html"
    ),
    "MedlinePlus 아미노필린": (
        "https://medlineplus.gov/druginfo/meds/a601015.html"
    ),
    "NCBI 카페인 약리 설명": (
        "https://www.ncbi.nlm.nih.gov/books/NBK223808/"
    ),
}

DISEASES = {
    "당뇨병": {
        "icon": "🩸",
        "short": "혈당·저혈당",
        "advice": (
            "인슐린·일부 혈당강하제는 결식·식사 지연·음주 때 "
            "저혈당 위험이 있습니다. 실제 복용약을 등록하세요. "
            "당뇨병 선택만으로 인슐린 복용을 추정하지 않습니다."
        ),
        "source": SOURCES["hypo"],
    },
    "고혈압": {
        "icon": "💓",
        "short": "혈압·코감기약",
        "advice": (
            "슈도에페드린 등 코막힘 성분과 진통소염제를 구매할 때 "
            "혈압 상태와 복용약을 약사에게 알려주세요."
        ),
        "source": SOURCES["pseudo"],
    },
    "골관절염·관절통": {
        "icon": "🦵",
        "short": "진통제 겹침",
        "advice": (
            "관절약·감기약·두통약의 진통 성분이 겹칠 수 있습니다. "
            "식품이나 보충제를 관절염 치료제 대신 사용하지 마세요."
        ),
        "source": SOURCES["arthritis"],
    },
    "인지저하·치매": {
        "icon": "🧠",
        "short": "졸림·혼동",
        "advice": (
            "일부 감기약·알레르기약·수면보조제의 항콜린성 성분은 "
            "졸림과 혼동을 유발할 수 있습니다. 전체 약 목록을 "
            "약사에게 보여주세요."
        ),
        "source": SOURCES["cognition"],
    },
    "만성콩팥병": {
        "icon": "💧",
        "short": "신장·식단 확인",
        "advice": (
            "진통소염제와 탈수, 건강기능식품에 주의가 필요합니다. "
            "칼륨·단백질·수분 제한은 검사와 병기에 따라 달라집니다."
        ),
        "source": SOURCES["renal_diet"],
    },
    "심부전": {
        "icon": "🫀",
        "short": "부종·체액",
        "advice": (
            "진통소염제는 체액 저류와 심부전 악화에 영향을 줄 수 "
            "있습니다. 새 일반약과 칼륨 함유 대체소금은 "
            "치료팀에 확인하세요."
        ),
        "source": SOURCES["heart"],
    },
    "위궤양·위장출혈 병력": {
        "icon": "🩹",
        "short": "출혈 위험",
        "advice": (
            "진통소염제와 항응고제·항혈소판제 조합은 별도 확인이 "
            "필요합니다. 궤양·출혈 병력을 알려주세요."
        ),
        "source": SOURCES["nsaid"],
    },
    "이상지질혈증": {
        "icon": "🫒",
        "short": "성분별 식품 주의",
        "advice": (
            "자몽 상호작용은 정확한 성분에 따라 다릅니다. "
            "모든 스타틴에 동일한 금기를 적용하지 않습니다."
        ),
        "source": SOURCES["grapefruit"],
    },
    "천식": {
        "icon": "🫁",
        "short": "진통제 반응 병력",
        "advice": (
            "아스피린·진통소염제로 숨참이나 천식 악화를 경험한 "
            "적이 있는지 확인하세요. 천식 전체를 절대금기로 "
            "판정하지 않습니다."
        ),
        "source": SOURCES["asthma"],
    },
    "녹내장·배뇨장애": {
        "icon": "👁️",
        "short": "감기약 성분 확인",
        "advice": (
            "일부 항히스타민·코막힘 성분은 폐쇄각녹내장·"
            "전립선비대 등에서 주의가 필요합니다. "
            "진단 유형과 증상을 알려주세요."
        ),
        "source": SOURCES["anticholinergic"],
    },
}


# ============================================================
# 화면 디자인
# ============================================================

CSS = """
<style>
@import url('https://fonts.googleapis.com/css2?family=Noto+Sans+KR:wght@400;500;600;700;800;900&display=swap');

:root {
    --ink:#102b3b;
    --muted:#5b7080;
    --mint:#0d766e;
    --line:#dce7ec;
}

html,body,.stApp {
    font-family:'Noto Sans KR',sans-serif;
}

.stApp {
    background:linear-gradient(145deg,#f0f7f7 0%,#f8fafc 48%,#f3f5fa 100%);
    color:var(--ink);
}

header[data-testid="stHeader"] {
    background:transparent;
    height:0;
}

[data-testid="stToolbar"] {
    display:none!important;
}

.block-container {
    max-width:990px;
    padding:1.1rem 1.2rem 1rem;
}

[data-testid="stVerticalBlock"] {
    gap:.55rem;
}

[data-testid="stCaptionContainer"] {
    color:#536775;
    font-size:.83rem;
}

.stButton button,
.stDownloadButton button,
.stFormSubmitButton button {
    border-radius:13px;
    min-height:46px;
    font-weight:700;
    border-color:#cddde4;
}

.stButton button[kind="primary"],
.stFormSubmitButton button[kind="primary"] {
    background:#0b746c;
    color:white;
    border-color:#0b746c;
}

.stButton button:hover,
.stDownloadButton button:hover {
    border-color:#0d766e;
    color:#0b665f;
}

.stTextInput input,
.stSelectbox [data-baseweb="select"] {
    font-size:1rem;
}

[data-testid="stMetric"] {
    background:#fff;
    border:1px solid var(--line);
    border-radius:14px;
    padding:10px 15px;
}

[data-testid="stMetricValue"] {
    font-size:1.45rem;
}

.brand {
    display:flex;
    align-items:center;
    gap:11px;
    margin:2px 0 6px;
}

.brand-icon {
    width:44px;
    height:44px;
    border-radius:15px;
    background:linear-gradient(140deg,#0c8178,#065b59);
    display:grid;
    place-items:center;
    box-shadow:0 6px 14px #086c6320;
}

.brand-title {
    font-size:23px;
    letter-spacing:-1.4px;
    font-weight:900;
    line-height:1.25;
}

.brand-sub {
    font-size:11px;
    letter-spacing:.12em;
    color:#50727e;
    font-weight:700;
}

.hero {
    position:relative;
    overflow:hidden;
    background:linear-gradient(125deg,#102f43,#123c4c 56%,#0b6863);
    border-radius:26px;
    padding:36px;
    color:white;
    box-shadow:0 15px 32px #12344518;
    margin:10px 0 18px;
}

.hero:after {
    content:'';
    position:absolute;
    width:260px;
    height:260px;
    border:45px solid #ffffff09;
    border-radius:50%;
    right:-78px;
    top:-40px;
    pointer-events:none;
}

.hero .eyebrow {
    font-size:12px;
    color:#9be7db;
    letter-spacing:.13em;
    font-weight:700;
}

.hero h1 {
    font-size:clamp(28px,4vw,42px);
    letter-spacing:-1.8px;
    line-height:1.35;
    margin:14px 0;
    font-weight:800;
    position:relative;
    z-index:1;
}

.hero p {
    font-size:16px;
    color:#e0efef;
    line-height:1.8;
    max-width:520px;
    margin:0;
    position:relative;
    z-index:1;
}

.hero-tag {
    display:inline-block;
    border:1px solid #95d7cb60;
    background:#ffffff0a;
    border-radius:20px;
    padding:6px 12px;
    font-size:12px;
    color:#d7ffef;
    margin-top:22px;
}

.intro-features {
    display:grid;
    grid-template-columns:repeat(3,1fr);
    gap:10px;
    margin-bottom:18px;
}

.intro-feature {
    background:white;
    border:1px solid var(--line);
    padding:18px 8px;
    border-radius:18px;
    text-align:center;
}

.intro-feature span {
    display:block;
    font-size:26px;
    margin-bottom:7px;
}

.intro-feature b {
    font-size:14px;
}

.intro-feature small {
    display:block;
    color:#546c77;
    font-size:12px;
    margin-top:5px;
}

.context {
    font-size:13px;
    color:#3e5f6b;
    padding:5px 0;
    line-height:1.7;
}

.pill {
    display:inline-block;
    border-radius:7px;
    background:#e6f2f0;
    color:#12625d;
    padding:2px 7px;
    margin:0 4px 3px 0;
    font-size:12px;
    font-weight:600;
}

.medline {
    background:white;
    border:1px solid var(--line);
    border-radius:14px;
    padding:11px 13px;
    margin:4px 0;
}

.medline small {
    color:#526975;
    font-size:12px;
}

.medline b {
    font-size:15px;
}

.empty {
    border:1px dashed #aec6cd;
    border-radius:14px;
    background:#ffffff80;
    padding:15px;
    color:#506d78;
    font-size:14px;
    text-align:center;
}

.resultrow {
    border-radius:13px;
    background:#fff;
    border:1px solid #dce7ec;
    padding:12px;
    margin-bottom:8px;
}

.resultrow .title {
    font-weight:800;
    font-size:15px;
    line-height:1.6;
}

.resultrow .detail {
    font-size:14px;
    color:#3d5460;
    line-height:1.75;
    margin-top:5px;
}

.resultrow .label {
    font-size:11px;
    font-weight:800;
}

.footer-note {
    font-size:12px;
    color:#546a76;
    text-align:center;
    line-height:1.7;
    margin:10px 0 0;
}

[data-testid="stDialog"] [role="dialog"] {
    border-radius:22px;
}

@media(max-width:600px) {
    .block-container {
        padding:.65rem .8rem .6rem;
    }
    [data-testid="stVerticalBlock"] {
        gap:.36rem;
    }
    [data-testid="stHorizontalBlock"] {
        gap:.4rem;
        flex-wrap:nowrap!important;
    }
    [data-testid="stColumn"] {
        min-width:0!important;
    }
    .hero {
        padding:26px 22px;
        border-radius:23px;
        margin:7px 0 12px;
    }
    .hero h1 {
        font-size:30px;
        margin:12px 0;
    }
    .hero p {
        font-size:14px;
        line-height:1.75;
    }
    .hero-tag {
        margin-top:16px;
        font-size:11px;
        padding:5px 9px;
    }
    .intro-features {
        gap:7px;
        margin-bottom:12px;
    }
    .intro-feature {
        padding:13px 4px;
    }
    .intro-feature b {
        font-size:12px;
    }
    .intro-feature small {
        font-size:10px;
    }
    .brand-title {
        font-size:21px;
    }
    .brand-icon {
        width:39px;
        height:39px;
        border-radius:13px;
    }
    .stButton button,
    .stDownloadButton button,
    .stFormSubmitButton button {
        min-height:46px;
        padding:.45rem .35rem;
        font-size:14px;
    }
    [data-testid="stMetric"] {
        padding:8px;
    }
    [data-testid="stMetricLabel"] p {
        font-size:11px;
    }
    [data-testid="stMetricValue"] {
        font-size:1.2rem;
    }
    .medline {
        padding:9px 11px;
    }
    .medline b {
        font-size:14px;
    }
}

@media(max-width:600px) and (max-height:740px) {
    .hero {
        padding:18px 20px;
    }
    .hero h1 {
        font-size:27px;
        margin:10px 0;
    }
    .hero p {
        font-size:13px;
        line-height:1.6;
    }
    .hero-tag {
        margin-top:12px;
    }
    .intro-feature {
        padding:9px 4px;
    }
    .intro-feature span {
        font-size:22px;
        margin-bottom:4px;
    }
    [data-testid="stMain"] [data-testid="stVerticalBlock"] {
        gap:.2rem;
    }
    .main-footer {
        display:none;
    }
}
</style>
"""

CAPSULE = """
<svg width="25" height="25" viewBox="0 0 32 32" aria-hidden="true">
<g transform="rotate(-40 16 16)">
<rect x="8" y="2" width="16" height="28" rx="8" fill="#fff"/>
<path d="M8 16h16v6a8 8 0 0 1-16 0z" fill="#7cddbb"/>
<path d="M8 16h16" stroke="#0d766e" stroke-width="1.4"/>
</g>
</svg>
"""


# ============================================================
# 공통 도구
# ============================================================

def h(value):
    return html.escape(str(value), quote=True)


def plain_text(value, limit=16000):
    value = re.sub(r"<[^>]+>", " ", str(value or ""))
    return value.replace("\x00", "")[:limit].strip()


def now_kst():
    return datetime.now(ZoneInfo("Asia/Seoul")).strftime(
        "%Y-%m-%d %H:%M KST"
    )


def api_now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def text_value(value):
    if value is None:
        return ""
    if isinstance(value, dict):
        return str(value.get("#text", "")).strip()
    return str(value).strip()


def secret(name):
    try:
        return str(
            st.secrets.get(name, "") or os.environ.get(name, "")
        ).strip()
    except (
        FileNotFoundError,
        st.errors.StreamlitSecretNotFoundError,
    ):
        return os.environ.get(name, "").strip()


def api_key():
    return st.session_state.get("mfds_key", "") or secret(
        "MFDS_SERVICE_KEY"
    )


def vision_key():
    return st.session_state.get("vision_key", "") or secret(
        "GOOGLE_VISION_API_KEY"
    )


# ============================================================
# 식약처 공식 API
# ============================================================

class ApiError(Exception):
    """키와 요청 URL을 노출하지 않는 사용자용 오류."""


def xml_value(node):
    if not list(node):
        return node.text or ""

    result = {}

    for child in node:
        key = child.tag.rsplit("}", 1)[-1]
        value = xml_value(child)

        if key in result:
            if not isinstance(result[key], list):
                result[key] = [result[key]]
            result[key].append(value)
        else:
            result[key] = value

    return result


def check_result_code(code):
    if code in {"00", "000", "0"}:
        return

    if code in {
        "20", "30", "31", "21",
        "SERVICE_KEY_IS_NOT_REGISTERED_ERROR",
    }:
        raise ApiError(
            "API 키 또는 해당 서비스의 활용승인 상태를 확인해 주세요."
        )

    if code in {"22", "23"}:
        raise ApiError(
            "공식 API 호출 한도에 도달했습니다. 잠시 후 다시 확인해 주세요."
        )

    if code in {"03", "NODATA_ERROR"}:
        raise ApiError(
            "공식 API가 자료 없음 상태를 반환했습니다. "
            "조회 완료로 간주하지 않습니다."
        )

    raise ApiError(
        "공식 API 조회가 완료되지 않았습니다. "
        "설정과 서비스 상태를 확인해 주세요."
    )


def decode_api_response(raw):
    try:
        data = json.loads(raw.decode("utf-8-sig"))
    except (UnicodeError, ValueError):
        if b"<!DOCTYPE" in raw.upper() or b"<!ENTITY" in raw.upper():
            raise ApiError(
                "공식 API 응답 형식을 확인하지 못했습니다."
            ) from None

        try:
            data = xml_value(ET.fromstring(raw))
        except ET.ParseError:
            raise ApiError(
                "공식 API가 해석할 수 없는 응답을 반환했습니다."
            ) from None

    if not isinstance(data, dict):
        raise ApiError("공식 API 응답 형식을 확인하지 못했습니다.")

    if isinstance(data.get("response"), dict):
        data = data["response"]

    gateway = data.get("cmmMsgHeader")

    if isinstance(gateway, dict):
        check_result_code(text_value(gateway.get("returnReasonCode")))
        raise ApiError(
            "공식 API 게이트웨이에서 요청을 처리하지 못했습니다."
        )

    header = data.get("header")

    if not isinstance(header, dict):
        raise ApiError("공식 API의 결과 상태가 누락되었습니다.")

    check_result_code(text_value(header.get("resultCode")))

    body = data.get("body")

    if not isinstance(body, dict):
        raise ApiError("공식 API의 본문이 누락되었습니다.")

    try:
        total = int(body.get("totalCount"))
        if total < 0:
            raise ValueError
    except (ValueError, TypeError):
        raise ApiError(
            "공식 API의 전체 결과 수를 확인하지 못했습니다."
        ) from None

    items = body.get("items", [])

    if isinstance(items, dict):
        items = items.get("item", [])

    if items in (None, ""):
        items = []

    if isinstance(items, dict):
        items = [items]

    if (
        not isinstance(items, list)
        or any(not isinstance(row, dict) for row in items)
    ):
        raise ApiError("공식 API의 목록 형식이 예상과 다릅니다.")

    if total > 0 and not items:
        raise ApiError("공식 API 응답 목록이 누락되었습니다.")

    if total == 0 and items:
        raise ApiError(
            "공식 API의 전체 결과 수와 목록이 일치하지 않습니다."
        )

    return items, total


def api_get(
    base,
    operation,
    key,
    filters,
    page=1,
    rows=API_PAGE_SIZE,
):
    key = text_value(key)

    if not key:
        raise ApiError("공공데이터포털 API 키를 먼저 설정해 주세요.")

    if "%" in key:
        key = urllib.parse.unquote(key)

    params = {
        "serviceKey": key,
        "type": "json",
        "pageNo": page,
        "numOfRows": rows,
    }
    params.update(filters)

    try:
        with requests.get(
            base + operation,
            params=params,
            timeout=(4, 16),
            stream=True,
            allow_redirects=False,
        ) as response:
            if response.status_code in (401, 403):
                raise ApiError(
                    "API 키와 해당 서비스의 활용승인 여부를 확인해 주세요."
                )

            if response.status_code == 429:
                raise ApiError(
                    "공식 API 호출 한도에 도달했습니다."
                )

            if response.status_code != 200:
                raise ApiError(
                    "공식 API 서버에 연결하지 못했습니다."
                )

            chunks = []
            size = 0

            for chunk in response.iter_content(chunk_size=65536):
                size += len(chunk)

                if size > MAX_API_BYTES:
                    raise ApiError(
                        "공식 API 응답이 처리 한도를 초과했습니다."
                    )

                chunks.append(chunk)

            return decode_api_response(b"".join(chunks))

    except requests.RequestException:
        raise ApiError(
            "공식 API 연결이 지연되거나 실패했습니다. "
            "잠시 후 다시 확인해 주세요."
        ) from None


def api_all(
    base,
    operation,
    key,
    filters,
    max_pages=API_MAX_PAGES,
):
    rows = []
    expected = None
    seen_pages = set()

    for page in range(1, max_pages + 1):
        batch, total = api_get(
            base,
            operation,
            key,
            filters,
            page=page,
        )

        if expected is None:
            expected = total
        elif total != expected:
            raise ApiError(
                "조회 중 공식 자료 수가 변경되었습니다. 다시 점검해 주세요."
            )

        if total == 0:
            return []

        if not batch:
            raise ApiError(
                "공식 API 페이지가 누락되어 전체 조회를 완료하지 않았습니다."
            )

        fingerprint = json.dumps(
            batch,
            sort_keys=True,
            ensure_ascii=False,
        )

        if fingerprint in seen_pages:
            raise ApiError(
                "공식 API가 같은 페이지를 반복했습니다."
            )

        seen_pages.add(fingerprint)
        rows.extend(batch)

        if len(rows) >= total:
            if len(rows) != total:
                raise ApiError(
                    "공식 API 결과 수가 맞지 않습니다."
                )
            return rows

    raise ApiError(
        "공식 API 페이지 수가 처리 한도를 넘어 "
        "전체 조회를 완료하지 않았습니다."
    )


def item_url(item_seq):
    return (
        "https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq="
        + urllib.parse.quote(str(item_seq), safe="")
    )


def api_search(query, key, barcode=False, page=1):
    query = text_value(query)

    try:
        page = int(page)
    except (ValueError, TypeError):
        raise ApiError("검색 페이지 형식이 올바르지 않습니다.") from None

    if not 1 <= page <= 1000:
        raise ApiError("검색 페이지 범위를 확인해 주세요.")

    if barcode:
        query = re.sub(r"\s", "", query)

        if not re.fullmatch(r"\d{13}", query):
            raise ApiError(
                "의약품 포장의 13자리 표준코드를 입력해 주세요."
            )

        field = "bar_code"
    else:
        if not 2 <= len(query) <= 80:
            raise ApiError(
                "약 이름을 2~80자로 입력해 주세요. 예: 타이레놀, 하벤"
            )

        field = "item_name"

    items, total = api_get(
        PERMIT_BASE,
        "getDrugPrdtPrmsnDtlInq08",
        key,
        {field: query},
        page=page,
        rows=10,
    )

    return {
        "items": items,
        "total": total,
        "page": page,
        "fetched_at": api_now(),
    }


def ingredient_name_key(name):
    return re.sub(
        r"\s+",
        "",
        unicodedata.normalize("NFKC", str(name)),
    ).casefold()


def parse_active_names(raw):
    """
    유효성분 필드 MAIN_ITEM_INGR만 사용합니다.
    INGR_NAME은 첨가제 필드이므로 사용하지 않습니다.
    불명확한 직렬화 형식은 완전한 성분 목록으로 확정하지 않습니다.
    """
    raw = html.unescape(text_value(raw)).strip()

    if not raw:
        return [], False

    result = []
    complete = True
    coded = list(re.finditer(r"\[([A-Za-z]\d{4,12})\]", raw))

    if coded:
        if raw[:coded[0].start()].strip(" ;|,/"):
            complete = False

        for index, token in enumerate(coded):
            end = (
                coded[index + 1].start()
                if index + 1 < len(coded)
                else len(raw)
            )
            name = raw[token.end():end].strip(" ;|,/")

            if not name or re.search(r"[|;\n\[\]]", name):
                complete = False
                continue

            result.append({
                "name": name,
                "amount": "",
                "code": token.group(1),
            })
    else:
        if any(mark in raw for mark in (",", "，", "/")):
            return [], False

        for part in re.split(r"[|;\n]+", raw):
            name = part.strip()

            if (
                not name
                or len(name) > 150
                or re.search(r"[<>\[\]]", name)
            ):
                complete = False
                continue

            result.append({
                "name": name,
                "amount": "",
                "code": "",
            })

    dedup = {}

    for item in result:
        if re.search(r"[=:]|성분명|분량\s*:", item["name"]):
            complete = False
            continue

        dedup.setdefault(ingredient_name_key(item["name"]), item)

    return list(dedup.values()), bool(dedup) and complete


def check_item_rows(rows, item_seq):
    for row in rows:
        returned = text_value(
            row.get("ITEM_SEQ", row.get("itemSeq"))
        )
        if returned != item_seq:
            raise ApiError(
                "공식 API의 품목코드가 요청한 제품과 일치하지 않습니다."
            )

    return rows


def api_details(item_seq, key):
    item_seq = text_value(item_seq)

    if not re.fullmatch(r"\d{9}", item_seq):
        raise ApiError("공식 품목기준코드를 확인해 주세요.")

    products, _ = api_get(
        PERMIT_BASE,
        "getDrugPrdtPrmsnDtlInq08",
        key,
        {"item_seq": item_seq},
        rows=10,
    )

    products = check_item_rows(products, item_seq)

    if len(products) != 1:
        raise ApiError(
            "해당 품목의 공식 상세정보를 하나로 확인하지 못했습니다."
        )

    product = products[0]
    warnings = []

    ingredients, complete = parse_active_names(
        product.get("MAIN_ITEM_INGR")
    )

    if not complete:
        warnings.append(
            "공식 유효성분 전체를 자동 확인하지 못했습니다. "
            "포장·공식 원문으로 성분을 확인해 주세요."
        )

    if ingredients:
        try:
            raw_ingredients = api_all(
                PERMIT_BASE,
                "getDrugPrdtMcpnDtlInq08",
                key,
                {"Item_seq": item_seq},
                max_pages=5,
            )

            raw_ingredients = check_item_rows(
                raw_ingredients,
                item_seq,
            )

            for active in ingredients:
                matches = [
                    row
                    for row in raw_ingredients
                    if ingredient_name_key(
                        text_value(row.get("MTRAL_NM"))
                    ) == ingredient_name_key(active["name"])
                ]

                quantities = {
                    (
                        text_value(row.get("QNT")),
                        text_value(row.get("INGD_UNIT_CD")),
                        text_value(row.get("TAMT_SEQ")),
                    )
                    for row in matches
                }

                if len(quantities) == 1:
                    qty, unit, group = next(iter(quantities))

                    if qty:
                        active["amount"] = qty + (
                            " " + unit
                            if unit
                            else " (단위 미확인)"
                        )

                        if group:
                            active["amount"] += " · 총량그룹 " + group

                if not active["code"] and matches:
                    codes = {
                        text_value(row.get("MTRAL_CODE"))
                        for row in matches
                    }
                    if len(codes) == 1:
                        active["code"] = next(iter(codes))

        except ApiError as exc:
            warnings.append("함량 보강 조회 미완료: " + str(exc))

    leaflet = {}

    try:
        leaves, _ = api_get(
            EASY_BASE,
            "getDrbEasyDrugList",
            key,
            {"itemSeq": item_seq},
            rows=10,
        )

        leaves = check_item_rows(leaves, item_seq)

        if len(leaves) == 1:
            leaflet = leaves[0]
        elif len(leaves) > 1:
            warnings.append(
                "e약은요 자료가 여러 건이라 자동 연결하지 않았습니다."
            )
        else:
            warnings.append(
                "이 품목에는 e약은요 자료가 없습니다."
            )

    except ApiError as exc:
        warnings.append("e약은요 조회 미완료: " + str(exc))

    result = {
        "product": product,
        "ingredients": ingredients,
        "ingredient_complete": complete,
        "warnings": warnings,
        "leaflet": leaflet,
        "dur": [],
        "dur_complete": False,
        "elderly": [],
        "elderly_complete": False,
        "fetched_at": api_now(),
    }

    endpoints = [
        (
            "병용금기",
            "getUsjntTabooInfoList03",
            "dur",
            "dur_complete",
        ),
        (
            "노인주의",
            "getOdsnAtentInfoList03",
            "elderly",
            "elderly_complete",
        ),
    ]

    for label, operation, list_key, done_key in endpoints:
        try:
            rows = api_all(
                DUR_BASE,
                operation,
                key,
                {"itemSeq": item_seq},
            )
            result[list_key] = check_item_rows(rows, item_seq)
            result[done_key] = True

        except ApiError as exc:
            warnings.append(label + " 조회 미완료: " + str(exc))

    return result


def official_item_to_med(detail):
    product = detail["product"]
    item_seq = text_value(product.get("ITEM_SEQ"))
    classification = text_value(product.get("ETC_OTC_CODE"))

    if "일반" in classification:
        kind = "일반의약품"
    elif "전문" in classification:
        kind = "처방의약품"
    else:
        kind = "미확인"

    return {
        "id": item_seq,
        "name": text_value(product.get("ITEM_NAME")),
        "kind": kind,
        "form": text_value(product.get("CHART")),
        "manufacturer": text_value(product.get("ENTP_NAME")),
        "ingredients": detail["ingredients"],
        "confirmed": True,
        "origin": "official",
        "source_url": item_url(item_seq),
        "source_date": text_value(product.get("CHANGE_DATE")),
        "dur": detail["dur"],
        "dur_complete": detail["dur_complete"],
        "elderly": detail["elderly"],
        "elderly_complete": detail["elderly_complete"],
        "leaflet": detail["leaflet"],
        "warnings": detail["warnings"],
        "ingredient_complete": detail["ingredient_complete"],
        "fetched_at": detail["fetched_at"],
        "status": text_value(product.get("CANCEL_NAME")),
        "raw_ingredients": text_value(
            product.get("MAIN_ITEM_INGR")
        ),
        "raw_material": text_value(product.get("MATERIAL_NAME")),
        "official_warning_text": (
            text_value(product.get("NB_DOC_DATA"))
            or text_value(product.get("PN_DOC_DATA"))
        ),
        "barcodes": text_value(product.get("BAR_CODE")),
    }


# ============================================================
# 성분 정규화 및 근거 기반 분석
# ============================================================

def alias_key(value):
    value = unicodedata.normalize(
        "NFKC",
        str(value or ""),
    ).strip().casefold()

    return re.sub(r"[\s·_\-]+", "", value)


ALIAS_GROUPS = {
    "아세트아미노펜": [
        "acetaminophen", "paracetamol",
        "아세트아미노펜(KP)", "아세트아미노펜(USP)",
    ],
    "클로르페니라민": [
        "chlorpheniramine", "chlorphenamine",
        "chlorpheniramine maleate", "chlorphenamine maleate",
        "클로르페니라민말레산염", "말레인산클로르페니라민",
    ],
    "디펜히드라민": [
        "diphenhydramine", "diphenhydramine hydrochloride",
        "디펜히드라민염산염", "염산디펜히드라민",
    ],
    "이부프로펜": ["ibuprofen"],
    "덱시부프로펜": ["dexibuprofen"],
    "나프록센": ["naproxen", "naproxen sodium", "나프록센나트륨"],
    "디클로페낙": [
        "diclofenac", "diclofenac sodium", "diclofenac potassium",
        "디클로페낙나트륨", "디클로페낙칼륨",
    ],
    "아세클로페낙": ["aceclofenac"],
    "셀레콕시브": ["celecoxib"],
    "아스피린": ["aspirin", "acetylsalicylic acid", "아세틸살리실산"],
    "슈도에페드린": [
        "pseudoephedrine", "pseudoephedrine hydrochloride",
        "슈도에페드린염산염", "염산슈도에페드린",
    ],
    "메트포르민": [
        "metformin", "metformin hydrochloride",
        "메트포르민염산염", "염산메트포르민",
    ],
    "글리메피리드": ["glimepiride"],
    "글리클라지드": ["gliclazide"],
    "글리벤클라미드": ["glibenclamide", "glyburide"],
    "글리피지드": ["glipizide"],
    "인슐린인체": [
        "human insulin", "insulin human",
        "Human Insulin (Recombinant)",
        "사람인슐린", "휴먼인슐린",
        "휴먼인슐린(유전자재조합)",
        "인슐린(유전자재조합)",
        "인슐린인체(유전자재조합)",
    ],
    "인슐린글라진": [
        "insulin glargine", "인슐린글라진(유전자재조합)",
    ],
    "인슐린아스파트": [
        "insulin aspart", "인슐린아스파트(유전자재조합)",
    ],
    "인슐린리스프로": [
        "insulin lispro", "인슐린리스프로(유전자재조합)",
    ],
    "인슐린데글루덱": [
        "insulin degludec", "인슐린데글루덱(유전자재조합)",
    ],
    "인슐린데테미르": [
        "insulin detemir", "인슐린데테미르(유전자재조합)",
    ],
    "인슐린글루리신": [
        "insulin glulisine", "인슐린글루리신(유전자재조합)",
    ],
    "프로프라놀롤": [
        "propranolol", "propranolol hydrochloride",
        "프로프라놀롤염산염",
    ],
    "아테놀롤": ["atenolol"],
    "비소프롤롤": [
        "bisoprolol", "bisoprolol fumarate",
        "비소프롤롤푸마르산염",
    ],
    "카르베딜롤": ["carvedilol"],
    "메토프롤롤": [
        "metoprolol", "metoprolol tartrate", "metoprolol succinate",
        "메토프롤롤타르타르산염", "메토프롤롤숙신산염",
    ],
    "심바스타틴": ["simvastatin"],
    "레보티록신": [
        "levothyroxine", "levothyroxine sodium",
        "레보티록신나트륨", "레보티록신나트륨수화물",
    ],
    "탄산칼슘": ["calcium carbonate", "침강탄산칼슘"],
    "황산철": [
        "ferrous sulfate", "ferrous sulphate",
        "황산제일철", "건조황산제일철",
    ],
    "와파린": ["warfarin", "warfarin sodium", "와파린나트륨"],
    "아픽사반": ["apixaban"],
    "리바록사반": ["rivaroxaban"],
    "다비가트란에텍실레이트": [
        "dabigatran etexilate", "dabigatran etexilate mesylate",
        "다비가트란에텍실레이트메실산염",
    ],
}

ALIASES = {
    alias_key(alias): canonical
    for canonical, aliases in ALIAS_GROUPS.items()
    for alias in [canonical] + aliases
}

INSULINS = {
    "인슐린인체", "인슐린글라진", "인슐린아스파트",
    "인슐린리스프로", "인슐린데글루덱",
    "인슐린데테미르", "인슐린글루리신",
}

SULFONYL = {
    "글리메피리드", "글리클라지드",
    "글리벤클라미드", "글리피지드",
}

NSAIDS = {
    "이부프로펜", "덱시부프로펜", "나프록센",
    "디클로페낙", "아세클로페낙", "셀레콕시브", "아스피린",
}

BETA_BLOCKERS = {
    "프로프라놀롤", "아테놀롤", "비소프롤롤",
    "카르베딜롤", "메토프롤롤",
}

ANTICOAGULANTS = {
    "와파린", "아픽사반", "리바록사반",
    "다비가트란에텍실레이트",
}

ANTICHOLINERGICS = {
    "디펜히드라민", "클로르페니라민",
}


def normalize_ingredient(value):
    original = " ".join(
        unicodedata.normalize(
            "NFKC",
            str(value or ""),
        ).strip().split()
    )

    return ALIASES.get(alias_key(original), original)


def official_item_seq(med):
    if med.get("origin") != "official" or not med.get("confirmed"):
        return ""

    value = str(
        med.get("item_seq")
        or med.get("ITEM_SEQ")
        or med.get("id")
        or ""
    )

    value = re.sub(r"^(?:mfds|official):", "", value)

    return value if re.fullmatch(r"\d{8,12}", value) else ""


def list_rows(value):
    if isinstance(value, dict):
        return [value]
    if isinstance(value, list):
        return value
    return []


def analyze(meds, candidate, conditions, older, foods=None):
    foods = list(foods or [])
    conditions = set(conditions or [])

    unique = {}

    for index, med in enumerate(meds or []):
        if isinstance(med, dict):
            unique.setdefault(
                str(med.get("id") or f"row-{index}"),
                med,
            )

    products = list(unique.values())
    findings = []
    emitted = set()

    def add(
        level,
        title,
        detail,
        action,
        source,
        scope="general",
        selected=None,
        mechanism="",
    ):
        ids = list(dict.fromkeys(
            str(m.get("id") or m.get("name") or "")
            for m in (selected or [])
        ))

        key = (level, title, tuple(sorted(ids)))

        if key in emitted:
            return

        emitted.add(key)

        finding = {
            "level": level,
            "title": title,
            "detail": detail,
            "action": action,
            "source": source,
            "scope": scope,
            "med_ids": ids,
        }

        if mechanism:
            finding["mechanism"] = mechanism

        findings.append(finding)

    if isinstance(candidate, dict):
        matching = next(
            (
                m for m in products
                if m.get("id")
                and str(m["id"]) == str(candidate.get("id"))
            ),
            None,
        )

        if matching:
            add(
                "duplicate",
                "복용 중인 제품과 같은 구매 예정 품목",
                (
                    f"{candidate.get('name', '제품')}이 복용 목록과 "
                    "구매 예정에 함께 등록되어 있습니다."
                ),
                "실제 추가 복용 계획인지 약사와 확인하세요.",
                SOURCES["mfds"],
                "data",
                [matching, candidate],
            )
        else:
            products.append(candidate)

    if not products:
        return [{
            "level": "unknown",
            "title": "점검할 약을 등록해 주세요",
            "detail": (
                "정확한 제품·제형·함량을 선택하고 "
                "복용 목록과 구매 예정 약을 등록해야 점검할 수 있습니다."
            ),
            "action": "건강기능식품과 필요할 때만 먹는 약도 알려주세요.",
            "source": SOURCES["mfds"],
            "scope": "data",
            "med_ids": [],
        }]

    known = []
    ingredient_owners = defaultdict(list)

    for med in products:
        name = str(med.get("name") or "이름 미등록 제품")

        if not med.get("confirmed"):
            add(
                "unknown",
                f"제품 확인 필요 · {name}",
                (
                    "제품명·제형·함량·성분이 아직 확인되지 않았습니다. "
                    "이 제품은 성분 기반 분석에서 제외했습니다."
                ),
                "포장이나 처방전과 비교해 확인하세요.",
                SOURCES["mfds"],
                "data",
                [med],
            )
            continue

        ingredients = {
            normalize_ingredient(i.get("name", ""))
            for i in med.get("ingredients", [])
            if isinstance(i, dict) and i.get("name")
        }

        known.append((med, ingredients))

        if not med.get("ingredient_complete") or not ingredients:
            add(
                "unknown",
                f"성분 정보 불완전 · {name}",
                (
                    "확인된 일부 성분만 점검했습니다. "
                    "누락된 성분의 중복·상호작용은 평가하지 못했습니다."
                ),
                "공식 성분표 전체와 함량·단위를 확인하세요.",
                SOURCES["mfds"],
                "data",
                [med],
            )

        for ingredient in ingredients:
            ingredient_owners[ingredient].append(med)

    for ingredient, owners in ingredient_owners.items():
        if len(owners) < 2:
            continue

        names = " / ".join(
            str(m.get("name", "제품")) for m in owners
        )

        if ingredient in INSULINS:
            note = (
                " 인슐린은 농도·혼합비·작용시간이 달라 "
                "교환하거나 용량을 환산할 수 없습니다."
            )
            source = SOURCES["insulin"]
        else:
            note = (
                " 제형·함량·투여 경로를 함께 확인해야 하며 "
                "이 결과는 과량 복용 판정이 아닙니다."
            )
            source = (
                SOURCES["acetaminophen"]
                if ingredient == "아세트아미노펜"
                else SOURCES["mfds"]
            )

        add(
            "duplicate",
            f"동일 성분 겹침 · {ingredient}",
            f"{names}에 같은 성분으로 확인된 명칭이 있습니다.{note}",
            (
                "기존 처방약을 임의로 중단하지 말고, "
                "새 약의 추가 복용 여부와 총량을 약사에게 확인하세요."
            ),
            source,
            "data",
            owners,
        )

    # 공식 금기는 정확한 품목 코드 두 개와 금기 원문이 있을 때만 표시.
    for med, other in combinations(products, 2):
        left = official_item_seq(med)
        right = official_item_seq(other)

        if not left or not right:
            continue

        for owner, own_id, target_id in (
            (med, left, right),
            (other, right, left),
        ):
            for row in list_rows(owner.get("dur")):
                if not isinstance(row, dict):
                    continue

                if (
                    str(row.get("ITEM_SEQ", "")).strip() != own_id
                    or str(
                        row.get("MIXTURE_ITEM_SEQ", "")
                    ).strip() != target_id
                ):
                    continue

                reason = str(
                    row.get("PROHBT_CONTENT") or ""
                ).strip()

                if not reason:
                    continue

                add(
                    "contraindication",
                    (
                        f"공식 병용금기 · {med.get('name', '제품')} "
                        f"+ {other.get('name', '제품')}"
                    ),
                    reason,
                    (
                        "추가 병용 전에 약사·처방의에게 공식 금기 사유를 "
                        "보여주세요. 기존 약의 중단·대체·용량 변경은 "
                        "전문가가 결정합니다."
                    ),
                    item_url(own_id),
                    "official",
                    [med, other],
                )

    incomplete_dur = [
        m for m in products
        if not m.get("dur_complete") or not official_item_seq(m)
    ]

    if incomplete_dur:
        add(
            "unknown",
            "공식 병용금기 점검 미완료",
            (
                "다음 제품의 국내 DUR 조회 또는 공식 품목 확인이 "
                "완료되지 않았습니다: "
                + ", ".join(m.get("name", "제품") for m in incomplete_dur)
                + ". 조회 실패·자료 없음은 병용 가능하다는 뜻이 아닙니다."
            ),
            "공식 품목을 확인하고 전체 목록을 약사에게 보여주세요.",
            SOURCES["mfds"],
            "data",
            incomplete_dur,
        )

    if older:
        missing_elderly = []

        for med in products:
            seq = official_item_seq(med)

            if not med.get("elderly_complete") or not seq:
                missing_elderly.append(med)

            for row in list_rows(med.get("elderly")):
                if (
                    not isinstance(row, dict)
                    or not seq
                    or str(row.get("ITEM_SEQ", "")).strip() != seq
                ):
                    continue

                reason = str(
                    row.get("PROHBT_CONTENT") or ""
                ).strip()

                if reason:
                    add(
                        "caution",
                        f"공식 노인주의 · {med.get('name', '제품')}",
                        reason,
                        (
                            "연령·낙상·인지·신장 기능과 함께 "
                            "약사·처방의에게 확인하세요."
                        ),
                        item_url(seq),
                        "official",
                        [med],
                    )

        if missing_elderly:
            add(
                "unknown",
                "공식 노인주의 점검 미완료",
                "일부 제품의 공식 노인주의 자료가 확인되지 않았습니다.",
                "수면보조제와 일반약을 포함해 약사에게 확인하세요.",
                SOURCES["mfds"],
                "data",
                missing_elderly,
            )

    def owners(group):
        return [
            med for med, ingredients in known
            if ingredients & group
        ]

    all_ingredients = (
        set().union(*(ingredients for _, ingredients in known))
        if known else set()
    )

    nsaids = owners(NSAIDS)
    antichol = owners(ANTICHOLINERGICS)
    hypoglycemic = owners(INSULINS | SULFONYL)

    for med1, med2 in combinations(nsaids, 2):
        first = next(
            ingredients for med, ingredients in known if med is med1
        ) & NSAIDS
        second = next(
            ingredients for med, ingredients in known if med is med2
        ) & NSAIDS

        if first != second or len(first | second) > 1:
            add(
                "caution",
                "같은 계열 진통소염제 겹침",
                (
                    "서로 다른 NSAID 성분이 등록되어 있습니다. "
                    "같은 성분 중복과 별개로 위장관 출혈·신장 "
                    "부작용을 검토해야 합니다."
                ),
                (
                    "국소제·먹는 약의 경로를 알려주세요. "
                    "저용량 아스피린 처방은 임의로 중단하지 마세요."
                ),
                SOURCES["nsaid"],
                selected=[med1, med2],
            )

    anticoag = owners(ANTICOAGULANTS)

    if nsaids and anticoag:
        add(
            "caution",
            "항응고제와 진통소염제 · 출혈 위험 확인",
            "항응고제와 NSAID 조합은 출혈 위험에 영향을 줄 수 있습니다.",
            (
                "항응고제를 임의로 중단하지 말고 "
                "새 진통제 구매 전에 상담하세요."
            ),
            SOURCES["warfarin"],
            selected=nsaids + anticoag,
            mechanism=(
                "약력학적 주의: 응고·혈소판 및 위장관 손상과 "
                "관련된 출혈 위험입니다. ADME 기전으로 분류하지 않습니다."
            ),
        )

    if nsaids and conditions & {"당뇨병", "고혈압", "만성콩팥병"}:
        add(
            "caution",
            "진통소염제 · 신장·혈압 상태 확인",
            (
                "당뇨병·고혈압·만성콩팥병과 탈수는 NSAID 사용 시 "
                "신장 위험을 검토해야 하는 요인입니다."
            ),
            "최근 신장 검사와 탈수 여부를 알려 구매 전 상담하세요.",
            SOURCES["kidney"],
            selected=nsaids,
        )

    if nsaids and "심부전" in conditions:
        add(
            "caution",
            "심부전 · 진통소염제 추가 전 확인",
            "NSAID는 체액 저류와 심부전 악화에 영향을 줄 수 있습니다.",
            "새 진통제 사용 전에 심부전 치료팀에 확인하세요.",
            SOURCES["heart"],
            selected=nsaids,
        )

    if nsaids and "위궤양·위장출혈 병력" in conditions:
        add(
            "caution",
            "출혈 병력 · 진통소염제 확인",
            (
                "NSAID의 위장관 출혈 위험은 고령·과거 궤양·"
                "출혈·동반약에 따라 달라집니다."
            ),
            "과거 출혈·궤양과 현재 항혈전제를 알려주세요.",
            SOURCES["nsaid"],
            selected=nsaids,
        )

    if nsaids and "천식" in conditions:
        add(
            "caution",
            "천식 · 진통소염제 반응 병력 확인",
            (
                "일부 환자는 아스피린·NSAID 사용 후 "
                "호흡기 증상이 악화될 수 있습니다. "
                "천식 전체에 대한 절대금기 판정은 아닙니다."
            ),
            "진통소염제로 숨참·천식 악화가 있었는지 알려주세요.",
            SOURCES["asthma"],
            selected=nsaids,
        )

    pseudo = owners({"슈도에페드린"})

    if pseudo and conditions & {
        "당뇨병", "고혈압", "심부전", "녹내장·배뇨장애",
    }:
        add(
            "caution",
            "코막힘 성분 · 기저질환 확인",
            (
                "슈도에페드린은 혈압·심장·당뇨병·녹내장·"
                "배뇨장애 병력에 따라 사용 전 확인이 필요합니다."
            ),
            "질환 조절 상태와 정확한 진단 유형을 알려주세요.",
            SOURCES["pseudo"],
            selected=pseudo,
        )

    if antichol and (older or "인지저하·치매" in conditions):
        add(
            "caution",
            "항콜린성 성분 · 졸림·혼동 확인",
            (
                "일부 1세대 항히스타민은 고령자·인지저하 환자에서 "
                "졸림·혼동 등 부작용을 검토해야 합니다. "
                "치매의 원인이나 악화를 확정하는 결과는 아닙니다."
            ),
            "감기약·알레르기약·수면보조제를 함께 제시하세요.",
            SOURCES["cognition"],
            selected=antichol,
        )

    if antichol and "녹내장·배뇨장애" in conditions:
        add(
            "caution",
            "항히스타민 · 눈·배뇨 상태 확인",
            (
                "항콜린성 성분은 특히 폐쇄각녹내장·전립선비대 "
                "등의 병력에서 주의가 필요합니다."
            ),
            "녹내장 종류와 배뇨장애를 알려 구매 전 상담하세요.",
            SOURCES["anticholinergic"],
            selected=antichol,
        )

    if hypoglycemic:
        add(
            "caution",
            "인슐린·일부 혈당강하제 · 식사와 저혈당",
            (
                "등록된 인슐린 또는 설포닐유레아는 결식·식사 지연·"
                "섭취량 감소·음주와 함께 저혈당 위험을 검토해야 합니다. "
                "메트포르민 단독은 이 규칙에 포함하지 않습니다."
            ),
            (
                "식사·혈당 확인 계획을 따르고 식사량이 달라졌을 때의 "
                "대처를 치료팀에 확인하세요. 용량은 임의 변경하지 마세요."
            ),
            SOURCES["hypo"],
            selected=hypoglycemic,
        )

        beta = owners(BETA_BLOCKERS)

        if beta:
            add(
                "caution",
                "베타차단제 병용 · 저혈당 자각 증상 확인",
                (
                    "일부 베타차단제는 저혈당을 "
                    "알아차리기 어렵게 할 수 있습니다."
                ),
                (
                    "증상만으로 판단하지 말고 혈당 확인 계획을 상담하세요. "
                    "심장약을 임의로 중단하지 마세요."
                ),
                SOURCES["beta"],
                selected=hypoglycemic + beta,
            )

    insulin = owners(INSULINS)

    if len(insulin) > 1:
        add(
            "caution",
            "인슐린 종류·농도 · 처방 구성 확인",
            (
                "기저·식사 인슐린 병용은 처방된 구성일 수 있습니다. "
                "다른 작용시간·농도·혼합비를 같은 제품으로 취급하지 "
                "않으며 중복 처방을 확정하지 않습니다."
            ),
            "제품명·농도·기기·투여 계획을 약사에게 보여주세요.",
            SOURCES["insulin"],
            selected=insulin,
        )

    if (
        "레보티록신" in all_ingredients
        and all_ingredients & {"탄산칼슘", "황산철"}
    ):
        add(
            "caution",
            "갑상선호르몬·칼슘/철 · 흡수 확인",
            (
                "미국 허가문서에는 레보티록신과 탄산칼슘·황산철의 "
                "흡수 영향 및 복용 간격 안내가 있습니다. "
                "한국의 실제 제품 허가사항을 우선 확인하세요."
            ),
            "현재 복용 시각을 약사에게 보여 적절한 간격을 확인하세요.",
            SOURCES["thyroid"],
            selected=owners({"레보티록신", "탄산칼슘", "황산철"}),
            mechanism=(
                "흡수(A): 탄산칼슘의 불용성 결합 또는 황산철과의 "
                "복합체 형성이 레보티록신 흡수를 감소시킬 수 있습니다."
            ),
        )

    food_text = " ".join(
        unicodedata.normalize("NFKC", str(food)) for food in foods
    )

    if "자몽" in food_text and "심바스타틴" in all_ingredients:
        add(
            "caution",
            "심바스타틴·자몽 · 식품 상호작용",
            (
                "자몽은 심바스타틴의 노출과 부작용 위험에 영향을 "
                "줄 수 있습니다. 모든 스타틴으로 확대하지 않습니다."
            ),
            "자몽이 포함된 식품을 알려 제품별 주의를 확인하세요.",
            SOURCES["grapefruit"],
            selected=owners({"심바스타틴"}),
            mechanism=(
                "대사(M): 자몽 성분이 장의 CYP3A4 작용을 억제하여 "
                "일부 약물의 혈중 노출을 증가시킬 수 있습니다."
            ),
        )

    if (
        "와파린" in all_ingredients
        and any(
            food in food_text
            for food in ("시금치", "브로콜리", "케일", "녹색채소")
        )
    ):
        add(
            "caution",
            "와파린·녹색채소 · 섭취량 일정하게",
            (
                "비타민 K가 많은 식품은 와파린 작용에 영향을 줄 수 "
                "있습니다. 녹색채소를 일괄 금지하지 않습니다."
            ),
            "평소와 비슷하게 섭취하고 큰 식단 변화 전 상담하세요.",
            SOURCES["warfarin"],
            selected=owners({"와파린"}),
        )

    if hypoglycemic and any(
        food in food_text
        for food in ("술", "음주", "맥주", "소주", "와인", "알코올")
    ):
        add(
            "caution",
            "혈당강하제·음주 · 저혈당 주의",
            (
                "인슐린·일부 혈당강하제를 사용하는 동안 음주, "
                "특히 음식 섭취가 부족한 상태의 음주는 "
                "저혈당 위험을 높일 수 있습니다."
            ),
            "음주 계획과 식사량을 당뇨 치료팀에 상담하세요.",
            SOURCES["hypo"],
            selected=hypoglycemic,
        )

    if foods and "만성콩팥병" in conditions:
        add(
            "unknown",
            "콩팥병 식단 · 개인 검사 확인 필요",
            (
                "재료만으로 칼륨·인·단백질·수분의 "
                "개인 허용량을 판단할 수 없습니다."
            ),
            "병기와 검사값을 바탕으로 영양사에게 확인하세요.",
            SOURCES["renal_diet"],
            "data",
        )

    if any(m.get("origin") == "demo" for m in products):
        add(
            "unknown",
            "체험용 가상 제품 · 실제 구매 판단에 사용 금지",
            (
                "이 제품명·성분은 기능 확인용 가상 예시이며 "
                "특정 판매 제품의 공식 정보가 아닙니다."
            ),
            "실제 포장에서 정확한 제품·함량을 확인하세요.",
            SOURCES["mfds"],
            "data",
        )

    add(
        "unknown",
        "점검 범위의 한계",
        (
            "등록·확인된 성분의 중복, 조회된 공식 DUR, 제한된 일반 "
            "주의를 표시합니다. 알레르기·용량·신장/간 기능·임신·"
            "전체 식품/보충제 상호작용을 완전히 평가하지 않습니다. "
            "표시되지 않은 위험이 있을 수 있습니다."
        ),
        "전체 약의 포장과 실제 복용 계획을 약사에게 제시하세요.",
        SOURCES["mfds"],
        "data",
        products,
    )

    order = {
        "contraindication": 0,
        "duplicate": 1,
        "caution": 2,
        "unknown": 3,
    }

    return sorted(findings, key=lambda finding: order[finding["level"]])


# ============================================================
# 시뮬레이션 데이터: 실제 판매 제품 아님
# ============================================================

def demo_med(
    identifier,
    name,
    ingredients,
    form="정제",
    kind="처방의약품",
):
    return {
        "id": identifier,
        "name": name,
        "kind": kind,
        "form": form,
        "ingredients": [
            {"name": name, "amount": amount, "code": ""}
            for name, amount in ingredients
        ],
        "confirmed": True,
        "origin": "demo",
        "ingredient_complete": True,
        "dur": [],
        "dur_complete": False,
        "elderly": [],
        "elderly_complete": False,
        "leaflet": {},
        "warnings": [],
    }


SIMULATIONS = [
    {
        "title": "당뇨·감기약 점검",
        "description": (
            "가상 복합감기약의 진통 성분 중복과 "
            "코막힘 성분 주의를 확인합니다."
        ),
        "conditions": ["당뇨병", "고혈압"],
        "older": True,
        "meds": [
            demo_med(
                "demo-insulin",
                "가상 기저 인슐린 예시",
                [("인슐린글라진", "100 단위/mL")],
                "주사제",
            ),
            demo_med(
                "demo-acet",
                "가상 단일 해열진통제 예시",
                [("아세트아미노펜", "500 mg")],
                kind="일반의약품",
            ),
        ],
        "candidate": demo_med(
            "demo-cold",
            "가상 3성분 감기약 예시",
            [
                ("아세트아미노펜", "300 mg"),
                ("슈도에페드린염산염", "15 mg"),
                ("클로르페니라민말레산염", "1.25 mg"),
            ],
            kind="일반의약품",
        ),
    },
    {
        "title": "관절통·신장·출혈 점검",
        "description": (
            "항응고제 복용 중 진통소염제 추가 시 "
            "확인할 사항을 보여주는 가상 예시입니다."
        ),
        "conditions": [
            "골관절염·관절통",
            "만성콩팥병",
            "위궤양·위장출혈 병력",
        ],
        "older": True,
        "meds": [
            demo_med(
                "demo-warfarin",
                "가상 항응고제 예시",
                [("와파린나트륨", "2 mg")],
            ),
        ],
        "candidate": demo_med(
            "demo-ibuprofen",
            "가상 진통소염제 예시",
            [("이부프로펜", "200 mg")],
            kind="일반의약품",
        ),
    },
    {
        "title": "인지저하·수면보조제 점검",
        "description": (
            "1세대 항히스타민 성분의 졸림·혼동과 "
            "배뇨 관련 주의를 확인하는 가상 예시입니다."
        ),
        "conditions": ["인지저하·치매", "녹내장·배뇨장애"],
        "older": True,
        "meds": [],
        "candidate": demo_med(
            "demo-diphenhydramine",
            "가상 수면보조 성분 예시",
            [("디펜히드라민염산염", "25 mg")],
            kind="일반의약품",
        ),
    },
]


# ============================================================
# 세션 상태
# ============================================================

def init_state():
    defaults = {
        "started": False,
        "demo_index": None,
        "candidate": None,
        "profiles": {
            "mine": {
                "name": "내 건강 프로필",
                "conditions": [],
                "older": False,
                "meds": [],
            },
            "diabetes": {
                "name": "당뇨병 프로필",
                "conditions": ["당뇨병"],
                "older": False,
                "meds": [],
            },
            "joints": {
                "name": "관절·혈압 프로필",
                "conditions": ["골관절염·관절통", "고혈압"],
                "older": False,
                "meds": [],
            },
        },
        "active_profile": "mine",
        "report": None,
        "search_results": None,
        "pending_med": None,
    }

    for key, value in defaults.items():
        if key not in st.session_state:
            st.session_state[key] = copy.deepcopy(value)


def context():
    index = st.session_state.demo_index

    if index is not None:
        scenario = SIMULATIONS[index]

        return {
            "name": scenario["title"],
            "conditions": scenario["conditions"],
            "older": scenario["older"],
            "meds": scenario["meds"],
            "foods": st.session_state.get("demo_foods", []),
            "food_exclusions": st.session_state.get(
                "demo_food_exclusions", []
            ),
        }, scenario["candidate"]

    return (
        st.session_state.profiles[st.session_state.active_profile],
        st.session_state.candidate,
    )


def invalidate_report():
    st.session_state.report = None
    st.session_state.pop("pdf_bytes", None)


def make_report():
    profile, candidate = context()
    foods = list(profile.get("foods", []))

    findings = analyze(
        profile["meds"],
        candidate,
        profile["conditions"],
        profile["older"],
        foods,
    )

    st.session_state.report = {
        "findings": findings,
        "created": now_kst(),
        "demo": st.session_state.demo_index is not None,
        "foods": foods,
        "food_exclusions": list(profile.get("food_exclusions", [])),
    }

    st.session_state.pop("pdf_bytes", None)


def launch_demo(index=0):
    st.session_state.demo_index = index
    st.session_state.started = True
    st.session_state.demo_foods = []
    st.session_state.demo_food_exclusions = []
    make_report()


def ingredient_label(med):
    labels = []

    for ingredient in med.get("ingredients", []):
        name = ingredient.get("name", "")
        amount = ingredient.get("amount", "")
        labels.append(name + (" " + amount if amount else ""))

    return " · ".join(labels) or "유효성분 미확인"


def brand():
    st.markdown(
        f"""
        <div class="brand">
            <div class="brand-icon">{CAPSULE}</div>
            <div>
                <div class="brand-title">
                    약결<span style="color:#0e8c7d">.</span>
                </div>
                <div class="brand-sub">MEDICATION COMPANION</div>
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )


def med_card(med, prefix="", compact=False):
    origin = {
        "official": "공식 조회",
        "manual": "직접 입력",
        "demo": "체험용 가상 제품",
    }.get(med.get("origin"), "미확인")

    ingredients = ingredient_label(med)

    if compact:
        ingredients = (
            f'유효성분 {len(med.get("ingredients", []))}개'
            " · 복용 목록에서 함량 확인"
        )

    st.markdown(
        f"""
        <div class="medline">
            <small>
                {h(prefix)} · {h(med.get("kind", "미확인"))}
                · {h(origin)}
            </small><br>
            <b>{h(med["name"])}</b><br>
            <small>{h(ingredients)}</small>
        </div>
        """,
        unsafe_allow_html=True,
    )


def add_medicine(med, target):
    if st.session_state.demo_index is not None:
        st.warning("실제 목록에 추가하려면 체험을 종료해 주세요.")
        return False

    profile = st.session_state.profiles[
        st.session_state.active_profile
    ]

    if target == "구매 예정":
        st.session_state.candidate = copy.deepcopy(med)
    else:
        if len(profile["meds"]) >= 25:
            st.warning("한 프로필은 25개까지 등록할 수 있습니다.")
            return False

        if any(m["id"] == med["id"] for m in profile["meds"]):
            st.warning("이미 등록된 제품입니다.")
            return False

        profile["meds"].append(copy.deepcopy(med))

    invalidate_report()
    return True


# ============================================================
# 설정·프로필·수기 입력
# ============================================================

@st.dialog("⚙️ 연결 설정 · 개인정보", width="large")
def settings_dialog():
    st.markdown("**배포 파일 받기**")

    source_path = Path(__file__)
    requirements_path = source_path.with_name("requirements.txt")

    left, right = st.columns(2)

    if source_path.is_file():
        left.download_button(
            "📥 app.py",
            source_path.read_bytes(),
            file_name="app.py",
            mime="text/x-python",
            use_container_width=True,
        )

    if requirements_path.is_file():
        right.download_button(
            "📥 requirements.txt",
            requirements_path.read_bytes(),
            file_name="requirements.txt",
            mime="text/plain",
            use_container_width=True,
        )

    st.write(
        "**로그인 없이 사용합니다.** 질환과 약 목록은 서버의 "
        "접속 세션 메모리에 보관하며 데이터베이스에 저장하지 않습니다. "
        "같은 기기·열린 세션을 함께 쓰는 사람은 내용을 볼 수 있습니다."
    )

    st.caption(
        "이 버전에는 사용자별 접근 권한과 영구 저장 기능이 없습니다. "
        "사진은 앱 서버 메모리로 업로드됩니다. OCR에 동의한 경우에만 "
        "Google에 추가 전송합니다."
    )

    with st.form("key_settings"):
        st.text_input(
            "공공데이터포털 서비스 키",
            type="password",
            key="mfds_key",
        )
        st.text_input(
            "Google Cloud Vision API 키 · 사진 OCR 선택 기능",
            type="password",
            key="vision_key",
        )

        if st.form_submit_button(
            "설정 적용",
            type="primary",
            use_container_width=True,
        ):
            st.session_state.search_results = None
            st.session_state.pending_med = None
            st.rerun()

    st.markdown("**GitHub → Streamlit Community Cloud 배포**")

    st.code(
        "pip install -r requirements.txt\n"
        "streamlit run app.py",
        language="bash",
    )

    st.caption(
        "Python 3.11~3.12 권장. GitHub 저장소에 두 파일을 올린 뒤 "
        "Streamlit 앱의 메인 파일을 app.py로 지정합니다."
    )

    st.code(
        'MFDS_SERVICE_KEY = "공공데이터포털_일반인증키"\n'
        '# 선택: GOOGLE_VISION_API_KEY = "클라우드_비전_API_키"',
        language="toml",
    )

    st.caption(
        "Streamlit 앱 Settings → Secrets에 입력합니다. "
        "키를 GitHub 저장소에 커밋하지 마세요. "
        "아래 세 API의 활용신청·승인은 각각 필요합니다."
    )

    st.markdown(
        "[의약품 제품 허가정보 08]"
        "(https://www.data.go.kr/data/15095677/openapi.do)"
        " · [DUR 품목정보 03]"
        "(https://www.data.go.kr/data/15059486/openapi.do)"
        " · [e약은요]"
        "(https://www.data.go.kr/data/15075057/openapi.do)"
    )

    st.caption(
        "식약처 조회에는 검색어·품목코드만 전송하며 "
        "프로필 질환은 전송하지 않습니다. "
        "Google OCR에는 동의한 사진이 전송됩니다."
    )

    if st.checkbox(
        "모든 프로필·약 목록·접속 세션 입력을 지우겠습니다",
        key="reset_agree",
    ):
        if st.button("세션 초기화", use_container_width=True):
            for key in list(st.session_state):
                del st.session_state[key]
            st.rerun()


@st.dialog("👤 건강 프로필", width="large")
def profile_dialog():
    if st.session_state.demo_index is not None:
        st.info("체험을 종료한 뒤 실제 프로필을 수정할 수 있습니다.")
        return

    profile, _ = context()

    st.caption(
        "실명·생년월일·연락처를 수집하지 않습니다. "
        "프리셋의 질환과 연령을 실제 상태에 맞게 수정하세요."
    )

    with st.form("profile_form"):
        alias = st.text_input(
            "표시 이름",
            value=profile["name"],
            max_chars=30,
        )

        conditions = st.multiselect(
            "현재 확인된 질환",
            list(DISEASES),
            default=profile["conditions"],
            format_func=lambda disease: (
                f'{DISEASES[disease]["icon"]} {disease}'
            ),
        )

        older = st.checkbox(
            "65세 이상",
            value=profile["older"],
        )

        if st.form_submit_button(
            "프로필 저장",
            type="primary",
            use_container_width=True,
        ):
            profile.update(
                name=alias.strip() or "내 프로필",
                conditions=conditions,
                older=older,
            )
            invalidate_report()
            st.rerun()

    for disease in profile["conditions"]:
        data = DISEASES[disease]
        st.write(
            f'**{data["icon"]} {disease}** — {data["advice"]}'
        )
        st.markdown(f'[근거 원문]({data["source"]})')

    with st.expander("새 가족 프로필 만들기"):
        new_name = st.text_input(
            "새 프로필 표시 이름",
            max_chars=30,
        )

        if st.button(
            "빈 프로필 추가",
            disabled=len(st.session_state.profiles) >= 8,
        ):
            if not new_name.strip():
                st.warning("표시 이름을 입력해 주세요.")
            else:
                identifier = uuid.uuid4().hex[:10]

                st.session_state.profiles[identifier] = {
                    "name": new_name.strip(),
                    "conditions": [],
                    "older": False,
                    "meds": [],
                }

                st.session_state.active_profile = identifier
                st.session_state.pending_profile = identifier
                st.session_state.candidate = None
                invalidate_report()
                st.rerun()


@st.dialog("💊 복용 목록 · 직접 등록", width="large")
def medicine_dialog():
    profile, candidate = context()

    st.caption(
        "처방약·일반약·건강기능식품을 모두 알려주세요. "
        "인슐린은 종류·농도·혼합비·기기명을 그대로 기록합니다."
    )

    for index, med in enumerate(profile["meds"]):
        med_card(med, "현재 복용")

        if st.session_state.demo_index is None:
            if st.button("목록에서 삭제", key=f"remove_{index}"):
                profile["meds"].pop(index)
                invalidate_report()
                st.rerun()

    if candidate:
        med_card(candidate, "구매 예정")

        if st.session_state.demo_index is None:
            if st.button("구매 예정 선택 해제"):
                st.session_state.candidate = None
                invalidate_report()
                st.rerun()

    if st.session_state.demo_index is not None:
        st.info("체험 중에는 가상 예시 목록을 사용합니다.")
        return

    st.divider()
    st.write("**직접 입력 · 처방약/건강기능식품 포함**")

    st.caption(
        "유효성분을 한 줄에 하나씩 입력하세요. "
        "직접 입력 자료는 공식 DUR 조회가 수행되지 않습니다."
    )

    with st.form("manual_medicine"):
        name = st.text_input("정확한 제품명", max_chars=120)

        left, right = st.columns(2)

        kind = left.selectbox(
            "구분",
            ["일반의약품", "처방의약품", "건강기능식품"],
        )

        form = right.text_input(
            "제형·농도·혼합비",
            max_chars=100,
            placeholder="예: 정제 / U-100 주사",
        )

        raw = st.text_area(
            "유효성분 | 1정/1회 단위 함량",
            placeholder=(
                "아세트아미노펜 | 500 mg\n"
                "클로르페니라민말레산염 | 2 mg"
            ),
            height=90,
            max_chars=3000,
        )

        target = st.radio(
            "추가 위치",
            ["현재 복용", "구매 예정"],
            horizontal=True,
        )

        confirmed = st.checkbox(
            "입력한 제품명·성분은 라벨/처방전과 대조했습니다"
        )
        complete = st.checkbox(
            "전체 유효성분을 빠짐없이 입력했습니다"
        )

        submit = st.form_submit_button(
            "직접 등록",
            type="primary",
            use_container_width=True,
        )

    if submit:
        if not name.strip():
            st.warning("제품명을 입력해 주세요.")
            return

        ingredients = []

        for line in raw.splitlines():
            if not line.strip():
                continue

            parts = line.split("|", 1)

            ingredients.append({
                "name": parts[0].strip()[:160],
                "amount": (
                    parts[1].strip()[:100]
                    if len(parts) > 1 else ""
                ),
                "code": "",
            })

        if len(ingredients) > 30:
            st.error("유효성분은 30개 이하로 입력해 주세요.")
            return

        med = {
            "id": "manual:" + uuid.uuid4().hex,
            "name": name.strip(),
            "kind": kind,
            "form": form,
            "ingredients": ingredients,
            "confirmed": bool(confirmed),
            "ingredient_complete": bool(
                ingredients and complete and confirmed
            ),
            "origin": "manual",
            "source_url": "",
            "source_date": "",
            "fetched_at": now_kst(),
            "dur": [],
            "dur_complete": False,
            "elderly": [],
            "elderly_complete": False,
            "leaflet": {},
            "warnings": [
                "사용자 직접 입력. 공식 제품 식별·DUR 조회 미완료."
            ],
        }

        if add_medicine(med, target):
            st.rerun()


# ============================================================
# 제품 검색
# ============================================================

def run_search(query, barcode=False, page=1):
    if not api_key():
        st.warning(
            "공식 검색에는 API 키가 필요합니다. "
            "설정에서 연결하거나 시뮬레이션을 체험해 주세요."
        )
        return

    if st.session_state.demo_index is not None:
        st.warning("실제 제품 검색은 체험 종료 후 사용해 주세요.")
        return

    with st.spinner("식약처 공식 품목 검색 중…"):
        try:
            result = api_search(
                query,
                api_key(),
                barcode=barcode,
                page=page,
            )

            st.session_state.search_results = {
                **result,
                "query": query,
                "barcode": barcode,
            }

            st.session_state.pending_med = None

        except ApiError as exc:
            st.session_state.search_results = None
            st.warning(str(exc))
            return

    st.rerun()


@st.dialog("🔎 정확한 제품 선택", width="large")
def search_dialog():
    result = st.session_state.search_results

    if result is None:
        st.info("검색어를 입력해 주세요.")
        return

    st.caption(
        f'‘{result["query"]}’ · 공식 후보 {result["total"]:,}개'
        " · 같은 이름이어도 제형·함량을 확인하세요."
    )

    items = result["items"]

    if not items:
        st.warning(
            "검색 결과가 없습니다. 이름 일부로 다시 검색하거나 "
            "포장을 확인해 직접 등록하세요. 자료 없음은 안전의 뜻이 아닙니다."
        )
        return

    def label(index):
        row = items[index]
        return (
            f'{row.get("ITEM_NAME", "이름 미확인")} | '
            f'{row.get("ENTP_NAME", "제조사 미확인")} | '
            f'{row.get("ITEM_SEQ", "")}'
        )

    selection = st.selectbox(
        "포장과 같은 제품을 선택",
        range(len(items)),
        format_func=label,
        key=f'pick_{result["query"]}_{result["page"]}',
    )

    row = items[selection]

    st.write(
        "**제형/성상:** "
        + (plain_text(row.get("CHART")) or "미제공")
    )
    st.write(
        "**분류:** "
        + (plain_text(row.get("ETC_OTC_CODE")) or "미확인")
        + " · **상태:** "
        + (plain_text(row.get("CANCEL_NAME")) or "미제공")
    )

    if st.button(
        "성분·공식 주의사항 불러오기",
        type="primary",
        use_container_width=True,
    ):
        with st.spinner("품목 상세·DUR·노인주의 조회 중…"):
            try:
                detail = api_details(
                    str(row.get("ITEM_SEQ", "")),
                    api_key(),
                )

                st.session_state.pending_med = (
                    official_item_to_med(detail)
                )
            except ApiError as exc:
                st.warning(str(exc))

    med = st.session_state.pending_med

    if med and med["id"] == str(row.get("ITEM_SEQ", "")):
        med_card(med, "선택한 공식 제품")

        st.caption(
            "원문 유효성분: "
            + (med.get("raw_ingredients") or "미제공")
        )

        if not med.get("ingredient_complete"):
            st.warning(
                "전체 성분을 완전하게 해석하지 못했습니다. "
                "공식 원문과 대조하거나 미확인 상태로 약사에게 확인하세요."
            )

        for message in med.get("warnings", []):
            st.caption(message)

        st.link_button(
            "의약품안전나라 제품 원문",
            med["source_url"],
            use_container_width=True,
        )

        st.caption(
            f'허가자료 변경일: {med.get("source_date") or "미제공"}'
            f' · 조회: {med.get("fetched_at", "")}'
        )

        with st.form("confirm_official"):
            target = st.radio(
                "추가 위치",
                ["구매 예정", "현재 복용"],
                horizontal=True,
            )

            checked = st.checkbox(
                "포장의 정확한 제품명·제형·함량과 위 제품이 일치합니다"
            )

            add = st.form_submit_button(
                "선택한 제품 등록",
                type="primary",
                use_container_width=True,
            )

        if add:
            status = str(med.get("status", ""))
            bad_status = status and status not in {
                "정상", "유효", "정상허가",
            }

            if not checked:
                st.warning("정확한 제품 일치 여부를 확인해 주세요.")

            elif target == "구매 예정" and bad_status:
                st.error(
                    "취하·취소 등 정상 여부를 확인해야 하는 품목입니다. "
                    "구매 전 약사와 확인해 주세요."
                )

            elif add_medicine(med, target):
                st.session_state.search_results = None
                st.session_state.pending_med = None
                st.rerun()

    total_pages = math.ceil(result["total"] / 10)

    if total_pages > 1:
        left, right = st.columns(2)

        if left.button(
            "이전 후보",
            disabled=result["page"] <= 1,
            use_container_width=True,
        ):
            run_search(
                result["query"],
                result["barcode"],
                result["page"] - 1,
            )

        if right.button(
            "다음 후보",
            disabled=result["page"] >= total_pages,
            use_container_width=True,
        ):
            run_search(
                result["query"],
                result["barcode"],
                result["page"] + 1,
            )

        st.caption(f'{result["page"]}/{total_pages} 페이지')


# ============================================================
# 사진·바코드·OCR
# ============================================================

def prepare_image(upload):
    if upload.size > 8 * 1024 * 1024:
        raise ValueError("사진은 8 MB 이하로 선택해 주세요.")

    try:
        with Image.open(upload) as original:
            if original.width * original.height > 24_000_000:
                raise ValueError(
                    "2,400만 화소 이하 사진을 사용해 주세요."
                )

            image = ImageOps.exif_transpose(original).convert("RGB")
            image.thumbnail((2000, 2000))

            output = io.BytesIO()
            image.save(output, format="JPEG", quality=90)

            return image, output.getvalue()

    except (
        UnidentifiedImageError,
        OSError,
        Image.DecompressionBombError,
    ):
        raise ValueError(
            "사진 파일을 확인하지 못했습니다. JPG/PNG/WebP를 사용하세요."
        ) from None


def ocr_image(payload, key):
    if not key:
        raise ValueError(
            "Google Cloud Vision API 키를 먼저 설정하거나 "
            "약 이름을 직접 입력해 주세요."
        )

    body = {
        "requests": [{
            "image": {
                "content": base64.b64encode(payload).decode("ascii")
            },
            "features": [{"type": "DOCUMENT_TEXT_DETECTION"}],
            "imageContext": {"languageHints": ["ko", "en"]},
        }]
    }

    try:
        response = requests.post(
            "https://vision.googleapis.com/v1/images:annotate",
            headers={"X-Goog-Api-Key": key},
            json=body,
            timeout=(4, 25),
            allow_redirects=False,
        )

        if response.status_code != 200:
            raise ValueError(
                "OCR 요청을 완료하지 못했습니다. "
                "API 활성화·결제·키 제한을 확인해 주세요."
            )

        parsed = response.json()

        if (
            not isinstance(parsed, dict)
            or not isinstance(parsed.get("responses"), list)
            or not parsed["responses"]
            or not isinstance(parsed["responses"][0], dict)
        ):
            raise ValueError("OCR 응답 형식을 확인하지 못했습니다.")

        data = parsed["responses"][0]

        if data.get("error"):
            raise ValueError("OCR 서비스가 사진을 처리하지 못했습니다.")

        annotation = data.get("fullTextAnnotation") or {}

        if not isinstance(annotation, dict):
            raise ValueError("OCR 텍스트를 확인하지 못했습니다.")

        return str(annotation.get("text", ""))[:14000]

    except (
        requests.RequestException,
        json.JSONDecodeError,
        IndexError,
        TypeError,
    ):
        raise ValueError(
            "OCR 연결 또는 응답을 확인하지 못했습니다."
        ) from None


@st.dialog("📷 포장 사진 · 바코드", width="large")
def photo_dialog():
    st.caption(
        "제품명·유효성분·함량이 선명하게 보이도록 촬영하세요. "
        "OCR은 글자 추출을 돕는 기능이며 제품 확인을 대신하지 않습니다."
    )

    upload = st.file_uploader(
        "포장 사진",
        type=["jpg", "jpeg", "png", "webp"],
        key="package_upload",
    )

    with st.expander("카메라로 직접 촬영"):
        shot = st.camera_input("촬영", key="package_camera")

    chosen = shot or upload

    if chosen:
        try:
            image, payload = prepare_image(chosen)
            st.image(image, width=220)

            digest = hashlib.sha256(payload).hexdigest()

            if st.session_state.get("photo_digest") != digest:
                st.session_state.photo_digest = digest
                st.session_state.ocr_text = ""
                st.session_state.barcode_detected = ""

            left, right = st.columns(2)

            if left.button(
                "바코드 읽기",
                use_container_width=True,
            ):
                try:
                    import zxingcpp

                    codes = [
                        result.text
                        for result in zxingcpp.read_barcodes(image)
                        if result.text.isdigit()
                        and len(result.text) == 13
                    ]

                    st.session_state.barcode_detected = (
                        codes[0] if codes else ""
                    )

                    if not codes:
                        st.warning(
                            "13자리 코드를 찾지 못했습니다. "
                            "숫자를 직접 입력할 수 있습니다."
                        )

                except Exception:
                    st.warning(
                        "바코드 엔진을 실행하지 못했습니다. "
                        "코드를 직접 입력해 주세요."
                    )

            consent = st.checkbox(
                "사진을 Google Cloud Vision에 전송하는 데 동의합니다. "
                "이름·처방전 개인정보는 가려 주세요."
            )

            if right.button(
                "제품명·성분·함량 OCR",
                use_container_width=True,
                disabled=not consent,
            ):
                with st.spinner("글자 추출 중…"):
                    try:
                        st.session_state.ocr_text = ocr_image(
                            payload,
                            vision_key(),
                        )
                    except ValueError as exc:
                        st.warning(str(exc))

            st.text_area(
                "OCR 원문 · 오인식은 반드시 수정",
                key="ocr_text",
                height=120,
                max_chars=14000,
            )

            st.caption(
                "사진은 앱 서버 메모리에서 처리합니다. "
                "바코드 읽기에는 별도 외부 API를 사용하지 않습니다. "
                "OCR 텍스트는 자동으로 약 목록에 등록하지 않습니다."
            )

        except ValueError as exc:
            st.warning(str(exc))

    with st.form("photo_search"):
        mode = st.radio(
            "검색 방식",
            ["제품명", "13자리 바코드"],
            horizontal=True,
        )

        query = st.text_input(
            "확인·수정한 검색어",
            value=st.session_state.get("barcode_detected", ""),
            max_chars=80,
        )

        if st.form_submit_button(
            "공식 제품 검색",
            type="primary",
            use_container_width=True,
        ):
            st.session_state.open_search = True
            run_search(
                query,
                barcode=mode == "13자리 바코드",
            )


# ============================================================
# 결과 표시
# ============================================================

def finding_view(finding):
    icon, label, color = LEVELS.get(
        finding["level"],
        LEVELS["unknown"],
    )

    scope = SCOPE_LABELS.get(
        finding.get("scope"),
        "자료 점검",
    )

    mechanism = ""

    if finding.get("mechanism"):
        mechanism = (
            '<div class="detail"><b>기전</b> '
            + h(finding["mechanism"])
            + "</div>"
        )

    st.markdown(
        f"""
        <div class="resultrow" style="border-left:4px solid {color}">
            <div class="label" style="color:{color}">
                {h(icon)} {h(label)} · {h(scope)}
            </div>
            <div class="title">{h(finding["title"])}</div>
            <div class="detail">
                {h(plain_text(finding["detail"]))}
            </div>
            {mechanism}
            <div class="detail">
                <b>확인 방법</b> {h(finding["action"])}
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )

    source = finding.get("source", "")

    if source.startswith("https://"):
        st.markdown(f"[근거 원문 확인]({source})")


def refresh_official():
    profile, candidate = context()

    if st.session_state.demo_index is not None:
        st.info("체험 자료는 실제 API로 갱신하지 않습니다.")
        return

    if not api_key():
        st.warning("공식 API 키를 먼저 설정해 주세요.")
        return

    errors = []

    for med in profile["meds"] + ([candidate] if candidate else []):
        if med.get("origin") != "official":
            continue

        try:
            fresh = official_item_to_med(
                api_details(med["id"], api_key())
            )

            med.clear()
            med.update(fresh)

        except ApiError as exc:
            med["dur_complete"] = False
            med["elderly_complete"] = False
            med["warnings"] = [
                "재조회 미완료. 이전 조회 자료가 남아 있습니다.",
                str(exc),
            ]
            errors.append(med["name"])

    make_report()

    if errors:
        st.warning("일부 재조회 미완료: " + ", ".join(errors))


@st.dialog("🔎 점검 결과 · 공식 원문", width="large")
def results_dialog():
    profile, candidate = context()

    if not st.session_state.report:
        make_report()

    report = st.session_state.report

    st.caption(
        f'점검 시각: {report["created"]} · '
        + (
            "체험용 가상 제품"
            if report["demo"]
            else "현재 입력 목록 기준"
        )
    )

    st.warning(
        "추가 복용·중단·용량 변경을 이 결과만으로 결정하지 마세요. "
        "확인되지 않은 상호작용, 용량·시각·신장/간 기능·알레르기 "
        "위험이 남아 있습니다."
    )

    if candidate is None:
        st.info(
            "현재 복용 목록 내부만 점검했습니다. "
            "구매 예정 제품을 선택하면 함께 비교합니다."
        )

    if not report["demo"]:
        if st.button(
            "공식 자료 다시 조회 · 결과 갱신",
            use_container_width=True,
        ):
            with st.spinner("공식 등록 품목 재조회 중…"):
                refresh_official()
            st.rerun()

    for finding in st.session_state.report["findings"]:
        finding_view(finding)

    st.divider()
    st.write("**제품별 원자료 · 갱신 시점**")

    for med in profile["meds"] + ([candidate] if candidate else []):
        with st.expander(med["name"]):
            st.write("유효성분: " + ingredient_label(med))

            st.caption(
                f'제형/성상: {med.get("form") or "미확인"}'
                f' · 변경일: {med.get("source_date") or "미제공"}'
                f' · 조회: {med.get("fetched_at") or "미제공"}'
            )

            st.caption(
                "함량은 제품 원자료 단위입니다. "
                "하루 복용량이나 교환 가능한 투여량으로 계산하지 않습니다."
            )

            for warning in med.get("warnings", []):
                st.caption(warning)

            leaflet = med.get("leaflet", {})

            fields = [
                ("atpnWarnQesitm", "주의 경고"),
                ("atpnQesitm", "사용상 주의"),
                ("intrcQesitm", "약·음식 상호작용 원문"),
                ("seQesitm", "이상반응"),
            ]

            for key, title in fields:
                if leaflet.get(key):
                    st.write(f"**{title}**")
                    st.write(plain_text(leaflet[key]))

            st.caption(
                "e약은요 갱신일: "
                + str(leaflet.get("updateDe") or "미제공")
            )

            if med.get("official_warning_text"):
                st.write("**허가사항 주의 원문**")
                st.write(plain_text(med["official_warning_text"]))

            if med.get("source_url", "").startswith("https://"):
                st.link_button(
                    "식약처 제품 원문 열기",
                    med["source_url"],
                    use_container_width=True,
                )


# ============================================================
# 재료별 요리 및 약물-식품 주의
# ============================================================

RECIPES = [
    {
        "name": "두부·버섯 채소찜",
        "needs": {"두부", "버섯", "양배추"},
        "steps": [
            "두부와 채소를 먹기 편한 크기로 썹니다.",
            "냄비에 물을 조금 넣고 재료를 충분히 익힙니다.",
            "간은 먹기 전에 소량씩 조절합니다.",
        ],
        "note": (
            "당뇨병에서는 주식과 함께 식사 전체의 탄수화물 양을 "
            "확인하세요. 이 요리만으로 한 끼를 대체하도록 권하지 않습니다."
        ),
    },
    {
        "name": "닭고기·양배추 볶음",
        "needs": {"닭고기", "양배추", "당근"},
        "steps": [
            "생닭과 채소는 도마·집게를 구분해 준비합니다.",
            "닭고기 중심부가 충분히 익도록 조리합니다.",
            "채소를 넣어 익히고 양념은 소량으로 조절합니다.",
        ],
        "note": (
            "관절 증상을 치료하는 식단은 아닙니다. "
            "체중·활동 계획은 의료진과 상의하세요."
        ),
    },
    {
        "name": "달걀·버섯 부드러운 찜",
        "needs": {"달걀", "버섯", "당근"},
        "steps": [
            "달걀을 풀어 물과 잘게 썬 채소를 섞습니다.",
            "중심부까지 완전히 익도록 찝니다.",
            "사레가 잦다면 연하평가에 따른 음식 점도를 확인합니다.",
        ],
        "note": (
            "부드러운 질감의 조리 예시입니다. "
            "알레르기·단백질 처방량에 따라 바꾸세요."
        ),
    },
    {
        "name": "익힌 생선·브로콜리 한 접시",
        "needs": {"생선", "브로콜리", "당근"},
        "steps": [
            "생선의 잔가시를 충분히 제거합니다.",
            "생선과 채소를 각각 완전히 익힙니다.",
            "주식은 평소 처방식에 맞춰 별도로 곁들입니다.",
        ],
        "note": (
            "와파린 복용자는 녹색채소 섭취량을 "
            "갑자기 바꾸지 마세요."
        ),
    },
]

FOOD_CHOICES = [
    "두부", "버섯", "양배추", "당근", "닭고기", "달걀",
    "생선", "브로콜리", "시금치", "현미", "우유", "자몽", "술",
]


@st.dialog("🥗 재료로 찾는 식사 아이디어", width="large")
def food_dialog():
    profile, candidate = context()

    st.caption(
        "식단은 약을 대체하지 않습니다. 선택 재료의 조리 아이디어와 "
        "확인할 내용을 제공합니다."
    )

    profile_key = (
        "demo"
        if st.session_state.demo_index is not None
        else st.session_state.active_profile
    )

    foods = st.multiselect(
        "사용할 재료·함께 먹을 식품",
        FOOD_CHOICES,
        default=profile.get("foods", []),
        key=f"food_choices_{profile_key}",
    )

    exclusions = st.multiselect(
        "제외할 식품 · 알레르기·기호",
        ["콩", "달걀", "생선", "우유"],
        default=profile.get("food_exclusions", []),
        key=f"food_exclude_{profile_key}",
    )

    if st.button(
        "선택한 식품을 점검·상담 카드에 반영",
        use_container_width=True,
        type="primary",
    ):
        if st.session_state.demo_index is not None:
            st.session_state.demo_foods = list(foods)
            st.session_state.demo_food_exclusions = list(exclusions)
        else:
            profile["foods"] = list(foods)
            profile["food_exclusions"] = list(exclusions)

        make_report()
        st.success("점검 결과와 상담 카드에 반영했습니다.")

    st.caption(
        "알레르기 전수 점검 기능은 아닙니다. "
        "실제 원재료·교차오염 표시를 확인하세요."
    )

    findings = analyze(
        profile["meds"],
        candidate,
        profile["conditions"],
        profile["older"],
        foods,
    )

    for finding in findings:
        if (
            finding["level"] != "unknown"
            and any(
                word in finding["title"]
                for word in (
                    "자몽", "음주", "녹색", "비타민",
                    "식사", "칼륨", "식단",
                )
            )
        ):
            finding_view(finding)

    if "만성콩팥병" in profile["conditions"]:
        st.warning(
            "만성콩팥병 프로필: 병기·혈중 칼륨·인·단백질 "
            "처방량이 없어 자동 요리 추천을 보류합니다. "
            "선택 재료를 영양사에게 보여주세요."
        )
        st.markdown(
            f'[NIDDK 콩팥병 식사 안내]({SOURCES["renal_diet"]})'
        )
        return

    if "당뇨병" in profile["conditions"]:
        st.info(
            "탄수화물의 양·식사 시각·약물 계획을 함께 확인하세요. "
            "인슐린·저혈당 위험 약을 복용하면 결식과 급격한 "
            "식사량 변화에 주의합니다."
        )

    if set(profile["conditions"]) & {"고혈압", "심부전"}:
        st.caption(
            "나트륨과 수분의 구체적인 제한량은 "
            "개인 처방에 따라 확인하세요."
        )

    excluded = set(exclusions) & set(FOOD_CHOICES)

    if "콩" in exclusions:
        excluded.add("두부")

    available = set(foods) - excluded

    ranked = sorted(
        RECIPES,
        key=lambda recipe: len(recipe["needs"] & available),
        reverse=True,
    )

    count = 0

    for recipe in ranked:
        if (
            recipe["needs"] & excluded
            or not recipe["needs"] & available
        ):
            continue

        missing = recipe["needs"] - available

        with st.container(border=True):
            st.write(f'**🍽️ {recipe["name"]}**')
            st.caption(
                "재료: " + ", ".join(sorted(recipe["needs"]))
            )

            if missing:
                st.caption(
                    "추가 필요: " + ", ".join(sorted(missing))
                )

            for index, step in enumerate(recipe["steps"], 1):
                st.write(f"{index}. {step}")

            st.caption(
                recipe["note"]
                + " 정량 영양분석·치료식 검증을 거친 레시피는 아닙니다."
            )

        count += 1

        if count == 2:
            break

    if not count:
        st.info("조리 재료를 선택해 주세요.")


# ============================================================
# 카페인 계산 및 교육용 그래프
# ============================================================

def caffeine_total_from_rows(rows, medicine_mg=0.0):
    if not isinstance(rows, list) or len(rows) > 10:
        raise ValueError("입력은 10개 이내여야 합니다.")

    extra = float(medicine_mg)

    if not math.isfinite(extra) or not 0 <= extra <= 5000:
        raise ValueError("의약품·기타 카페인 입력을 확인하세요.")

    total = extra

    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("입력 형식을 확인하세요.")

        amount = float(row.get("1회 카페인(mg)", 0) or 0)
        count = float(row.get("오늘 횟수", 0) or 0)

        if not (
            math.isfinite(amount)
            and 0 <= amount <= 2000
            and math.isfinite(count)
            and 0 <= count <= 20
        ):
            raise ValueError("함량·횟수 범위를 확인하세요.")

        total += amount * count

    return total


def caffeine_decay_series(dose_mg, half_life_hours, hours=24):
    if not (
        math.isfinite(dose_mg)
        and 0 <= dose_mg <= 20000
    ):
        raise ValueError("초기값 범위를 확인하세요.")

    if not (
        math.isfinite(half_life_hours)
        and 0 < half_life_hours <= 100
    ):
        raise ValueError("반감기 범위를 확인하세요.")

    if not isinstance(hours, int) or not 1 <= hours <= 72:
        raise ValueError("표시 시간 범위를 확인하세요.")

    points = [index / 2 for index in range(hours * 2 + 1)]

    return {
        "경과 시간(h)": points,
        "교육 모델상 잔여량(mg)": [
            round(dose_mg * 0.5 ** (time / half_life_hours), 3)
            for time in points
        ],
    }


def caffeine_key(name):
    return re.sub(
        r"[\s_·.\-()]",
        "",
        unicodedata.normalize("NFKC", str(name)),
    ).casefold()


def caffeine_medication_notes(meds):
    rules = {
        "theophylline": ("테오필린", "MedlinePlus 테오필린"),
        "테오필린": ("테오필린", "MedlinePlus 테오필린"),
        "theophyllineanhydrous": (
            "테오필린", "MedlinePlus 테오필린"
        ),
        "무수테오필린": ("테오필린", "MedlinePlus 테오필린"),
        "aminophylline": ("아미노필린", "MedlinePlus 아미노필린"),
        "아미노필린": ("아미노필린", "MedlinePlus 아미노필린"),
        "aminophyllinehydrate": (
            "아미노필린", "MedlinePlus 아미노필린"
        ),
        "아미노필린수화물": (
            "아미노필린", "MedlinePlus 아미노필린"
        ),
        "pseudoephedrine": (
            "슈도에페드린", "MedlinePlus 슈도에페드린"
        ),
        "슈도에페드린": (
            "슈도에페드린", "MedlinePlus 슈도에페드린"
        ),
        "pseudoephedrinehydrochloride": (
            "슈도에페드린", "MedlinePlus 슈도에페드린"
        ),
        "슈도에페드린염산염": (
            "슈도에페드린", "MedlinePlus 슈도에페드린"
        ),
        "염산슈도에페드린": (
            "슈도에페드린", "MedlinePlus 슈도에페드린"
        ),
    }

    caffeine_aliases = {
        "caffeine", "caffeineanhydrous", "anhydrouscaffeine",
        "카페인", "무수카페인", "카페인무수물",
        "카페인수화물", "caffeinehydrate",
    }

    notes = []
    seen = set()

    for med in meds:
        if not med.get("confirmed", False):
            continue

        for ingredient in med.get("ingredients", []):
            name = ingredient.get("name", "")
            key = caffeine_key(name)
            match = rules.get(key)
            medname = med.get("name", "등록 약")

            if match and (medname, match[0]) not in seen:
                seen.add((medname, match[0]))
                drug, source = match

                notes.append({
                    "title": f"{medname} · {drug}",
                    "detail": (
                        "다량의 카페인이 이 약의 부작용을 심하게 할 수 "
                        "있다는 안내가 있습니다. 이 계산기로 병용 가능한 "
                        "양을 정하지 말고 제품 설명서와 약사 안내를 확인하세요."
                    ),
                    "source": CAFFEINE_SOURCES[source],
                })

            if (
                key in caffeine_aliases
                and (medname, "caffeine") not in seen
            ):
                seen.add((medname, "caffeine"))

                notes.append({
                    "title": f"{medname}에 카페인 성분 등록",
                    "detail": (
                        f'등록 함량: {ingredient.get("amount") or "미확인"}. '
                        "실제 복용 횟수를 확인한 뒤 ‘의약품·기타 하루 합계’에 "
                        "직접 반영하세요. 하루 복용량으로 자동 환산하지 않습니다."
                    ),
                    "source": CAFFEINE_SOURCES[
                        "FDA 성인 카페인 안내"
                    ],
                })

    return notes


def body_svg():
    return """
    <svg role="img"
         aria-label="교육용 인체: 뇌, 심장, 간, 소화관, 신장"
         viewBox="0 0 630 275"
         xmlns="http://www.w3.org/2000/svg"
         style="width:100%;max-height:270px">
      <rect width="630" height="275" rx="20" fill="#f0f7f7"/>
      <circle cx="309" cy="41" r="24"
              fill="#dcece9" stroke="#6d9e97"/>
      <path d="M287 70Q270 82 263 115L248 163Q245 179 258 178
               L282 129L280 193L273 253H294L309 204L325 253H346
               L337 191L336 128L358 174Q370 182 372 166
               L355 110Q349 78 332 70Z"
            fill="#dcece9" stroke="#6d9e97"/>
      <ellipse cx="309" cy="40" rx="14" ry="10" fill="#a995d3"/>
      <path d="M310 104Q300 90 294 101Q285 113 310 126
               Q332 110 322 101Q316 95 310 104"
            fill="#e9978e"/>
      <ellipse cx="321" cy="145" rx="18" ry="10" fill="#dfae68"/>
      <path d="M294 166H324Q337 177 300 177Q288 188 329 190"
            fill="none" stroke="#5bafa1" stroke-width="6"/>
      <ellipse cx="288" cy="146" rx="7" ry="11" fill="#a388b4"/>
      <g font-family="sans-serif" font-size="14" fill="#1b414f">
        <text x="27" y="50">뇌 · 졸림·각성·혼동</text>
        <path d="M225 45H290" stroke="#a995d3"/>
        <text x="395" y="111">심장 · 혈압·두근거림</text>
        <path d="M330 110H385" stroke="#e9978e"/>
        <text x="395" y="150">간 · 대사(M)</text>
        <path d="M342 145H385" stroke="#dfae68"/>
        <text x="27" y="143">신장 · 배설(E)</text>
        <path d="M170 140H280" stroke="#a388b4"/>
        <text x="27" y="185">소화관 · 흡수(A)</text>
        <path d="M190 180H288" stroke="#5bafa1"/>
        <text x="395" y="217">혈류 · 분포(D)</text>
        <text x="27" y="255" font-size="11" fill="#526b76">
          위치와 일반 경로를 보여주는 그림이며 손상·위험도를 뜻하지 않습니다.
        </text>
      </g>
    </svg>
    """


@st.dialog("☕ 카페인 · 인체·그래프", width="large")
def caffeine_dialog():
    profile, candidate = context()
    meds = profile["meds"] + ([candidate] if candidate else [])

    st.info(
        "최대 일일섭취권고량은 채워 마셔야 하는 목표나 "
        "약과 함께 섭취해도 되는 개인별 허용량이 아닙니다."
    )

    calc_tab, model_tab, sources_tab = st.tabs([
        "☕ 하루 총량",
        "🧍 인체·그래프",
        "📚 공식 근거",
    ])

    with calc_tab:
        basis = st.selectbox(
            "비교할 국내 기준",
            [
                "성인 일반 기준",
                "임산부 국내 기준",
                "어린이·청소년 국내 기준",
            ],
            key="caf_basis",
        )

        if basis == "어린이·청소년 국내 기준":
            weight = st.number_input(
                "체중(kg) · 이 세션에서만 사용",
                5.0,
                200.0,
                50.0,
                0.5,
                key="caf_weight",
            )

            limit = float(weight) * 2.5
            rule = "식약처: 체중 1kg당 2.5mg/일 이하"

            st.caption(
                "어린이·청소년에게 카페인 섭취를 권장하지 않습니다."
            )

        elif basis == "임산부 국내 기준":
            limit = 300.0
            rule = "식약처: 임산부 300mg/일 이하"

            st.caption(
                "담당 산부인과의 더 엄격한 지침이 있으면 따르세요."
            )

        else:
            limit = 400.0
            rule = "식약처: 성인 400mg/일 이하"

        st.caption(rule + " · 개인별 안전 보장 없음")

        if profile["older"]:
            st.warning(
                "65세 이상 프로필입니다. 일반 성인 기준을 개인 허용량으로 "
                "사용하지 마세요. 수면·두근거림·약물을 상담하세요."
            )

        st.caption(
            "아래 함량은 입력을 돕는 가상 예시입니다. "
            "실제 음료 라벨·제조사 함량으로 수정하세요."
        )

        defaults = [
            {
                "음료·식품": "예시 커피",
                "1회 카페인(mg)": 100.0,
                "오늘 횟수": 1.0,
            },
            {
                "음료·식품": "예시 차",
                "1회 카페인(mg)": 40.0,
                "오늘 횟수": 0.0,
            },
            {
                "음료·식품": "예시 에너지음료",
                "1회 카페인(mg)": 80.0,
                "오늘 횟수": 0.0,
            },
            {
                "음료·식품": "기타 식품",
                "1회 카페인(mg)": 0.0,
                "오늘 횟수": 0.0,
            },
        ]

        rows = st.data_editor(
            defaults,
            hide_index=True,
            num_rows="fixed",
            key="caf_food_rows",
            use_container_width=True,
            column_config={
                "음료·식품": st.column_config.TextColumn(
                    "음료·식품",
                    max_chars=40,
                ),
                "1회 카페인(mg)": st.column_config.NumberColumn(
                    "1회 mg",
                    min_value=0.0,
                    max_value=2000.0,
                    step=1.0,
                    required=True,
                ),
                "오늘 횟수": st.column_config.NumberColumn(
                    "오늘 횟수",
                    min_value=0.0,
                    max_value=20.0,
                    step=0.5,
                    required=True,
                ),
            },
        )

        medicine_mg = st.number_input(
            "의약품·기타에서 섭취한 카페인 하루 합계(mg)",
            min_value=0.0,
            max_value=5000.0,
            value=0.0,
            step=1.0,
            key="caf_other_mg",
        )

        try:
            total = caffeine_total_from_rows(
                rows,
                float(medicine_mg),
            )
        except (TypeError, ValueError, OverflowError):
            st.error("함량·횟수를 유한한 0 이상 숫자로 수정하세요.")
            return

        st.session_state.caffeine_last_total = total

        left, right = st.columns(2)
        left.metric("입력한 하루 합계", f"{total:,.0f} mg")
        right.metric("국내 기준과 비교", f"{total / limit * 100:,.0f}%")
        st.progress(min(total / limit, 1.0))

        if total > limit:
            st.warning(
                "입력한 총량이 선택한 최대 일일섭취권고량을 넘습니다. "
                "약의 복용량은 임의로 변경하지 말고 "
                "카페인 섭취와 증상을 상담하세요."
            )
        else:
            st.caption(
                "기준 이하라는 계산만으로 약과의 병용 가능 여부를 "
                "판단할 수 없습니다. 남은 허용량은 산출하지 않습니다."
            )

        notes = caffeine_medication_notes(meds)

        if notes:
            for note in notes:
                st.warning(note["title"] + "\n\n" + note["detail"])
                st.caption(
                    "해외 공공 의약품 일반 주의 · 국내 DUR 판정 아님"
                )
                st.markdown(
                    f'[해당 근거 확인]({note["source"]})'
                )
        else:
            st.caption(
                "이 도구가 다루는 일부 성분을 찾지 못했습니다. "
                "다른 약의 카페인 상호작용을 배제하지 않습니다."
            )

        if any(
            not med.get("ingredient_complete", False)
            for med in meds
        ):
            st.warning(
                "일부 약의 성분이 불완전합니다. "
                "카페인 포함 여부를 설명서에서 추가 확인하세요."
            )

        st.caption(
            "심한 두근거림·흉통·실신·경련 등 급성 증상이 있으면 "
            "계산을 계속하지 말고 응급의료기관에 도움을 요청하세요."
        )

    with model_tab:
        st.markdown(body_svg(), unsafe_allow_html=True)

        st.caption(
            "카페인은 소화관에서 흡수되어 전신에 분포하며 "
            "주로 간의 CYP1A2가 대사에 관여합니다. "
            "대사산물은 주로 소변으로 배출됩니다. "
            "근거는 공식 근거 탭의 NCBI 자료를 확인하세요."
        )

        initial = st.number_input(
            "모델 초기량(mg) · 실제 섭취량과 별도",
            0.0,
            2000.0,
            100.0,
            10.0,
            key="caf_model_initial",
        )

        half_life = st.slider(
            "교육용 가상 반감기(시간)",
            2.0,
            12.0,
            5.0,
            0.5,
            key="caf_half_life",
        )

        graph = caffeine_decay_series(
            float(initial),
            float(half_life),
        )

        st.line_chart(
            graph,
            x="경과 시간(h)",
            y="교육 모델상 잔여량(mg)",
            color="#138c80",
            height=230,
        )

        st.caption(
            "가정: 0시간에 한 번에 흡수되어 일정한 반감기로 감소. "
            "M(t) = M(0) × ½^(t/반감기)."
        )

        st.warning(
            "실제 혈중농도·체내 잔여량을 예측하지 않습니다. "
            "과거 누적 섭취·흡수 지연·약물 영향·개인 차이를 "
            "반영하지 않습니다. 복용 간격·다음 커피 시간·"
            "운전·수면 가능 여부를 결정하는 데 사용하지 마세요."
        )

        st.caption(
            "CDC 교육자료는 반감기를 약 5~6시간으로 설명합니다. "
            "슬라이더의 2~12시간 범위는 가정 비교용입니다."
        )

    with sources_tab:
        st.write(
            "**국내 최대 일일섭취권고량:** "
            "성인 400mg/일 이하, 임산부 300mg/일 이하, "
            "어린이·청소년 체중 1kg당 2.5mg/일 이하."
        )

        for title, url in CAFFEINE_SOURCES.items():
            st.markdown(f"- [{title}]({url})")

        st.caption(
            f"근거 검토일: {REVIEW_DATE}. "
            "일반 교육자료이며 국내 제품 허가사항을 대체하지 않습니다."
        )


# ============================================================
# 인체·약물 시뮬레이션
# ============================================================

@st.dialog("🧍 인체로 보는 점검 · 체험", width="large")
def simulation_dialog():
    names = [scenario["title"] for scenario in SIMULATIONS]

    choice = st.selectbox(
        "체험 상황",
        range(len(names)),
        format_func=lambda index: names[index],
        index=st.session_state.demo_index or 0,
    )

    st.caption(SIMULATIONS[choice]["description"])

    if st.button(
        "이 상황으로 체험 시작",
        type="primary",
        use_container_width=True,
    ):
        launch_demo(choice)
        st.rerun()

    st.write("**인체·ADME 지도**")
    st.markdown(body_svg(), unsafe_allow_html=True)

    st.caption(
        "일반적인 위치와 과정을 보여주는 교육 그림입니다. "
        "장기 손상·위험 확률·개인의 약물 농도는 계산하지 않습니다."
    )

    if st.session_state.report:
        mechanisms = [
            finding
            for finding in st.session_state.report["findings"]
            if finding.get("mechanism")
        ]

        if mechanisms:
            for finding in mechanisms:
                finding_view(finding)
        else:
            st.info(
                "현재 목록에서 출처로 확인한 개별 ADME 기전은 없습니다. "
                "성분 이름만으로 기전을 생성하지 않습니다."
            )

    st.caption(
        "고령자 항히스타민의 졸림 등은 약력학적 주의입니다. "
        "모든 주의를 CYP 효소 기전으로 설명하지 않습니다."
    )

    if st.button(
        "☕ 카페인 반감기 그래프도 보기",
        use_container_width=True,
    ):
        st.session_state.next_dialog = "caffeine"
        st.rerun()


# ============================================================
# 약사 상담 PDF
# ============================================================

def build_pdf(profile, candidate, report):
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.cidfonts import UnicodeCIDFont
    from reportlab.lib import colors
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.lib.pagesizes import A4
    from reportlab.platypus import SimpleDocTemplate, Paragraph

    font = "HYSMyeongJo-Medium"

    if font not in pdfmetrics.getRegisteredFontNames():
        pdfmetrics.registerFont(UnicodeCIDFont(font))

    output = io.BytesIO()

    document = SimpleDocTemplate(
        output,
        pagesize=A4,
        topMargin=35,
        bottomMargin=35,
        leftMargin=38,
        rightMargin=38,
        title="약결 약사 상담 요약",
        author="약결",
    )

    body_style = ParagraphStyle(
        "body",
        fontName=font,
        fontSize=10,
        leading=16,
        wordWrap="CJK",
        textColor=colors.HexColor("#233c49"),
        spaceAfter=6,
    )

    title_style = ParagraphStyle(
        "title",
        parent=body_style,
        fontSize=17,
        leading=23,
        spaceAfter=12,
    )

    sub_style = ParagraphStyle(
        "sub",
        parent=body_style,
        fontSize=12,
        leading=18,
        textColor=colors.HexColor("#0d766e"),
        spaceBefore=10,
    )

    def paragraph(value, style=body_style):
        escaped = html.escape(str(value)).replace("\n", "<br/>")
        return Paragraph(escaped, style)

    story = [paragraph("약결 | 약사 상담 요약", title_style)]

    if report["demo"]:
        story.append(paragraph(
            "[체험용 가상 제품] 실제 환자·공식 품목 조회 결과가 아닙니다.",
            sub_style,
        ))

    story.append(paragraph(
        f'프로필: {profile["name"]} | 65세 이상: '
        + ("설정됨" if profile["older"] else "미설정")
    ))

    story.append(paragraph(
        "질환 설정: "
        + (", ".join(profile["conditions"]) or "없음/미입력")
    ))

    story.append(paragraph(
        "선택한 식품: "
        + (", ".join(report.get("foods", [])) or "미입력")
    ))

    story.append(paragraph(
        "제외할 식품: "
        + (", ".join(report.get("food_exclusions", [])) or "미입력")
    ))

    story.append(paragraph(
        "점검 시각: " + report["created"]
    ))

    story.append(paragraph(
        "복용 중단·추가·용량 변경은 이 문서만으로 결정하지 않습니다. "
        "약사·처방의가 실제 제품과 전체 복용 정보를 확인해야 합니다."
    ))

    groups = [
        ("현재 복용 목록", profile["meds"]),
        ("구매 예정", [candidate] if candidate else []),
    ]

    for title, meds in groups:
        story.append(paragraph(title, sub_style))

        if not meds:
            story.append(paragraph("미등록"))

        for med in meds:
            story.append(paragraph(
                f'{med["name"]} | {med.get("kind", "미확인")} '
                f'| {med.get("form", "")}'
            ))

            story.append(paragraph(ingredient_label(med)))

            story.append(paragraph(
                f'자료: {med.get("origin", "미확인")} '
                f'| 변경일: {med.get("source_date") or "미제공"} '
                f'| 조회: {med.get("fetched_at") or "미제공"}'
            ))

            if med.get("source_url"):
                story.append(paragraph(med["source_url"]))

    story.append(paragraph(
        "확인된 주의사항과 미확인 범위",
        sub_style,
    ))

    for index, finding in enumerate(report["findings"], 1):
        label = LEVELS.get(
            finding["level"],
            LEVELS["unknown"],
        )[1]

        scope = SCOPE_LABELS.get(
            finding.get("scope"),
            "자료 점검",
        )

        story.append(paragraph(
            f'{index}. [{label}] {finding["title"]}'
        ))

        story.append(paragraph("구분: " + scope))
        story.append(paragraph(plain_text(finding["detail"])))

        if finding.get("mechanism"):
            story.append(paragraph(
                "근거에 있는 기전: " + finding["mechanism"]
            ))

        story.append(paragraph(
            "확인 방법: " + finding["action"]
        ))

        story.append(paragraph(
            "출처: " + finding.get("source", "미제공")
        ))

    story.append(paragraph("상담할 질문", sub_style))

    story.append(paragraph(
        "1) 정확한 제형·함량의 제품인가요? "
        "2) 같은 성분이나 진통소염제 계열이 겹치나요? "
        "3) 식사·저혈당·카페인에서 무엇을 확인해야 하나요? "
        "4) 기존 처방과 복용 시각·용량을 어떻게 맞추나요?"
    ))

    story.append(paragraph(
        "개인별 용량·신장/간 기능·알레르기·복용 시각을 포함한 "
        "전수 평가가 아닙니다. 공식 DUR에 항목이 없어도 "
        "안전하다고 판정하지 않습니다."
    ))

    def footer(canvas, doc):
        canvas.setFont(font, 8)
        canvas.drawString(
            38,
            20,
            "약결 | 건강 정보가 포함된 상담 자료입니다.",
        )
        canvas.drawRightString(
            A4[0] - 38,
            20,
            str(doc.page),
        )

    document.build(
        story,
        onFirstPage=footer,
        onLaterPages=footer,
    )

    return output.getvalue()


@st.dialog("📄 약사 상담 카드", width="large")
def consultation_dialog():
    profile, candidate = context()

    if not st.session_state.report:
        make_report()

    report = st.session_state.report

    st.caption(
        "성분·주의사항·미확인 범위를 함께 전달합니다. "
        "다운로드 파일에 건강 정보가 포함됩니다."
    )

    st.write(f'**{profile["name"]}** · {report["created"]}')

    if report["demo"]:
        st.warning("체험용 가상 제품으로 만든 상담 예시입니다.")

    for med in profile["meds"]:
        med_card(med, "현재 복용")

    if candidate:
        med_card(candidate, "구매 예정")

    for finding in report["findings"]:
        label = LEVELS[finding["level"]][1]
        st.write(f'**[{label}] {finding["title"]}**')

    if st.button(
        "상담 PDF 만들기",
        type="primary",
        use_container_width=True,
    ):
        try:
            st.session_state.pdf_bytes = build_pdf(
                profile,
                candidate,
                report,
            )
        except Exception:
            st.error(
                "PDF를 만들지 못했습니다. "
                "화면의 상담 목록을 약사에게 보여주세요."
            )

    if st.session_state.get("pdf_bytes"):
        st.download_button(
            "📥 상담 요약 PDF 저장",
            st.session_state.pdf_bytes,
            file_name="yakgyeol_consultation.pdf",
            mime="application/pdf",
            use_container_width=True,
        )

        st.caption(
            "표준 한국어 CID 글꼴을 사용합니다. "
            "PDF 뷰어에 따라 글꼴이 대체될 수 있습니다."
        )


# ============================================================
# 성분 중복 탐지 성능 평가
# ============================================================

def evaluate_duplicate_csv(data):
    if len(data) > 1024 * 1024:
        raise ValueError("검증 CSV는 1 MB 이하로 업로드해 주세요.")

    try:
        reader = csv.DictReader(
            io.StringIO(data.decode("utf-8-sig"))
        )
    except UnicodeError:
        raise ValueError("UTF-8 CSV로 저장해 주세요.") from None

    required = {
        "case_id",
        "left_ingredients",
        "right_ingredients",
        "expected_duplicate",
        "source_url",
        "reviewed_on",
    }

    if not required.issubset(set(reader.fieldnames or [])):
        raise ValueError("필수 열이 없습니다. 템플릿을 사용해 주세요.")

    counts = {"TP": 0, "FP": 0, "FN": 0, "TN": 0}
    details = []
    identifiers = set()

    for row in reader:
        if len(details) >= 2000:
            raise ValueError("한 번에 2,000개 사례까지 평가합니다.")

        identifier = row.get("case_id", "").strip()
        left = row.get("left_ingredients", "")
        right = row.get("right_ingredients", "")
        label = row.get("expected_duplicate", "").strip()

        if (
            not identifier
            or identifier in identifiers
            or label not in {"0", "1"}
            or not left.strip()
            or not right.strip()
        ):
            raise ValueError(
                "ID는 유일해야 하며 성분과 0/1 정답이 필요합니다."
            )

        if (
            not row.get("source_url", "").startswith("https://")
            or not re.fullmatch(
                r"\d{4}-\d{2}-\d{2}",
                row.get("reviewed_on", ""),
            )
        ):
            raise ValueError(
                "각 사례에 근거 URL과 검토일(YYYY-MM-DD)이 필요합니다."
            )

        identifiers.add(identifier)

        a = {
            normalize_ingredient(value.strip())
            for value in left.split("|")
            if value.strip()
        }

        b = {
            normalize_ingredient(value.strip())
            for value in right.split("|")
            if value.strip()
        }

        predicted = bool(a & b)
        expected = label == "1"

        if predicted and expected:
            result = "TP"
        elif predicted:
            result = "FP"
        elif expected:
            result = "FN"
        else:
            result = "TN"

        counts[result] += 1

        details.append({
            "case_id": identifier,
            "정답": int(expected),
            "예측": int(predicted),
            "결과": result,
        })

    if not details:
        raise ValueError("평가할 사례가 없습니다.")

    tp = counts["TP"]
    fp = counts["FP"]
    fn = counts["FN"]

    precision = tp / (tp + fp) if tp + fp else None
    recall = tp / (tp + fn) if tp + fn else None

    f1 = (
        2 * tp / (2 * tp + fp + fn)
        if 2 * tp + fp + fn else None
    )

    return {
        **counts,
        "precision": precision,
        "recall": recall,
        "f1": f1,
        "rows": details,
    }


@st.dialog("🔬 근거 · 성분 중복 탐지 평가", width="large")
def evidence_dialog():
    st.write("**공식 제품 성분표와 전문가 정답으로 검증**")

    st.caption(
        f"앱 {APP_VERSION} · 근거·API 명세 검토일: {REVIEW_DATE}. "
        "공식 데이터 갱신일·임상 검증일과는 다릅니다."
    )

    st.write(
        "아래 평가는 입력된 성분 목록의 제품 쌍 단위 중복 탐지만 "
        "측정합니다. 검색 정확도·OCR·DUR 누락·임상 결과의 정확도를 "
        "대신하지 않습니다. 공식 원문을 바탕으로 독립 검토한 "
        "정답 세트가 필요합니다."
    )

    template = (
        "case_id,left_ingredients,right_ingredients,"
        "expected_duplicate,source_url,reviewed_on\n"
    )

    st.download_button(
        "검증 CSV 빈 템플릿",
        template.encode("utf-8-sig"),
        file_name="duplicate_validation_template.csv",
        mime="text/csv",
        use_container_width=True,
    )

    st.caption(
        "성분 구분자는 |, 정답은 중복 1/비중복 0입니다. "
        "정답의 임상적 타당성을 앱이 자동 인증하지 않습니다."
    )

    uploaded = st.file_uploader(
        "독립 검증 CSV",
        type=["csv"],
        key="evaluation_csv",
    )

    if uploaded:
        try:
            result = evaluate_duplicate_csv(uploaded.getvalue())
            columns = st.columns(3)

            for column, key, title in zip(
                columns,
                ["precision", "recall", "f1"],
                ["정밀도", "재현율", "F1"],
            ):
                value = result[key]
                column.metric(
                    title,
                    f"{value:.3f}" if value is not None else "정의 불가",
                )

            st.caption(
                f'TP {result["TP"]} · FP {result["FP"]} · '
                f'FN {result["FN"]} · TN {result["TN"]}'
            )

            st.dataframe(
                result["rows"],
                hide_index=True,
                use_container_width=True,
            )

        except (ValueError, csv.Error) as exc:
            st.error(str(exc))

    st.divider()

    st.write(
        "한국 허가정보 08은 품목·유효성분 식별에, DUR 03은 정확한 "
        "품목 쌍의 공식 금기와 노인주의에 사용합니다. "
        "e약은요는 일부 일반약의 쉬운 원문을 보완합니다."
    )

    st.caption(
        "건강기능식품 성분 DB·모든 질환별 금기·총 복용량·"
        "신장/간 기능별 용량을 전수 점검하지 않습니다. "
        "생성형 AI로 금기·기전을 생성하지 않습니다."
    )

    st.markdown(
        "[식약처 허가정보]"
        "(https://www.data.go.kr/data/15095677/openapi.do)"
        " · [DUR]"
        "(https://www.data.go.kr/data/15059486/openapi.do)"
        " · [e약은요]"
        "(https://www.data.go.kr/data/15075057/openapi.do)"
    )


# ============================================================
# 시작 화면 및 본 화면
# ============================================================

def landing():
    brand()

    st.markdown(
        """
        <div class="hero">
            <div class="eyebrow">MY MEDICATION, CONNECTED</div>
            <h1>구매 전,<br>내 약과 한 번 더 확인.</h1>
            <p>
                약 이름을 조금만 알아도 괜찮아요.<br>
                복용 중인 약과 구매할 약을 함께 살펴보고,<br>
                나의 질환·식사·카페인까지 확인하세요.
            </p>
            <div class="hero-tag">
                로그인 없이 · 큰 버튼으로 · 근거와 함께
            </div>
        </div>
        <div class="intro-features">
            <div class="intro-feature">
                <span>💊</span>
                <b>성분 중복·주의</b>
                <small>제품명 대신 성분으로</small>
            </div>
            <div class="intro-feature">
                <span>🧍</span>
                <b>10개 질환 맞춤</b>
                <small>당뇨·혈압·인지건강</small>
            </div>
            <div class="intro-feature">
                <span>☕</span>
                <b>식사·카페인</b>
                <small>인체·그래프 체험</small>
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )

    if st.button(
        "시작하기  →",
        type="primary",
        use_container_width=True,
    ):
        st.session_state.started = True
        st.rerun()

    if st.button(
        "▶  예시로 먼저 체험하기",
        use_container_width=True,
    ):
        launch_demo(0)
        st.rerun()

    st.markdown(
        """
        <div class="footer-note">
            추가 복용을 결정하기 전 확인을 돕는 도구입니다.<br>
            복용 중단·용량 변경은 약사·의사와 상의하세요.
        </div>
        """,
        unsafe_allow_html=True,
    )


def main():
    st.set_page_config(
        page_title="약결 | 약·질환·카페인 확인",
        page_icon="💊",
        layout="centered",
        initial_sidebar_state="collapsed",
    )

    st.markdown(CSS, unsafe_allow_html=True)
    init_state()

    if not st.session_state.started:
        landing()
        return

    profile, candidate = context()
    demo = st.session_state.demo_index is not None

    header1, header2, header3 = st.columns(
        [6, 1.1, 1.1],
        vertical_alignment="center",
    )

    with header1:
        brand()

    if header2.button("홈", use_container_width=True):
        st.session_state.started = False
        st.rerun()

    if header3.button(
        "⚙",
        help="API 연결·배포 방법·개인정보",
        use_container_width=True,
    ):
        settings_dialog()

    if demo:
        left, right = st.columns(
            [5, 2],
            vertical_alignment="center",
        )

        left.caption("▶ 체험 중 · 가상 제품, 실제 복용 지침 아님")

        if right.button("체험 종료", use_container_width=True):
            st.session_state.demo_index = None
            invalidate_report()
            st.rerun()
    else:
        st.caption("구매 전, 약 이름보다 성분을 먼저 확인해요.")

    left, right = st.columns(
        [4, 1.35],
        vertical_alignment="bottom",
    )

    with left:
        keys = list(st.session_state.profiles)
        names = {
            key: st.session_state.profiles[key]["name"]
            for key in keys
        }

        if "pending_profile" in st.session_state:
            st.session_state.profile_select = (
                st.session_state.pop("pending_profile")
            )

        if demo:
            st.selectbox(
                "체험 프로필",
                ["체험 · " + profile["name"]],
                disabled=True,
                label_visibility="collapsed",
                key="demo_profile_select",
            )
            selection = st.session_state.active_profile

        else:
            selection = st.selectbox(
                "건강 프로필",
                keys,
                index=keys.index(st.session_state.active_profile),
                format_func=names.get,
                label_visibility="collapsed",
                key="profile_select",
            )

        if (
            selection != st.session_state.active_profile
            and not demo
        ):
            st.session_state.active_profile = selection
            st.session_state.candidate = None
            st.session_state.search_results = None
            invalidate_report()
            st.rerun()

    if right.button("👤 설정", use_container_width=True):
        profile_dialog()

    condition_html = " ".join(
        (
            '<span class="pill">'
            f'{h(DISEASES[disease]["icon"])} {h(disease)}'
            "</span>"
        )
        for disease in profile["conditions"][:2]
    )

    if len(profile["conditions"]) > 2:
        condition_html += (
            '<span class="pill">'
            f'외 {len(profile["conditions"]) - 2}개'
            "</span>"
        )

    age_html = (
        '<span class="pill">65세 이상</span>'
        if profile["older"] else ""
    )

    st.markdown(
        '<div class="context">'
        + age_html
        + (
            condition_html
            or "질환이 있으면 프로필에서 선택해 주세요."
        )
        + "</div>",
        unsafe_allow_html=True,
    )

    with st.form("name_search", border=False):
        search1, search2 = st.columns(
            [4, 1.15],
            vertical_alignment="bottom",
        )

        query = search1.text_input(
            "약 이름 일부로 검색",
            placeholder="타이레놀, 하벤…",
            label_visibility="collapsed",
            key="search_input",
            max_chars=80,
        )

        submit = search2.form_submit_button(
            "🔎 검색",
            use_container_width=True,
        )

    if submit:
        st.session_state.open_search = True
        run_search(query)

    if (
        st.session_state.pop("open_search", False)
        and st.session_state.search_results
    ):
        search_dialog()

    action1, action2 = st.columns(2)

    if action1.button(
        f'💊 복용 목록 {len(profile["meds"])}개',
        use_container_width=True,
    ):
        medicine_dialog()

    if action2.button(
        "📷 사진·바코드",
        use_container_width=True,
    ):
        photo_dialog()

    if candidate:
        med_card(candidate, "구매 예정", compact=True)
    else:
        st.markdown(
            '<div class="empty">'
            "＋ 검색 후 <b>구매 예정 약</b>을 선택해 주세요"
            "</div>",
            unsafe_allow_html=True,
        )

    if st.button(
        "내 약과 함께 점검하기",
        type="primary",
        use_container_width=True,
    ):
        make_report()

    report = st.session_state.report

    if report:
        counts = {
            level: sum(
                finding["level"] == level
                for finding in report["findings"]
            )
            for level in LEVELS
        }

        metric1, metric2, metric3 = st.columns(3)

        metric1.metric(
            "⛔ 금기·중복 검출",
            counts["contraindication"] + counts["duplicate"],
        )
        metric2.metric("! 확인 필요", counts["caution"])
        metric3.metric("? 미확인", counts["unknown"])

        if st.button(
            "근거·확인 방법 보기",
            use_container_width=True,
        ):
            results_dialog()

    else:
        status = (
            "키 설정됨 · 실제 연결은 조회 시 확인"
            if api_key()
            else "미연결 · 설정에서 키 입력"
        )

        st.caption(
            f"공식 API {status} | 예시 체험은 연결 없이 이용 가능"
        )

    feature1, feature2, feature3 = st.columns(3)

    if feature1.button("🥗 식단", use_container_width=True):
        food_dialog()

    if feature2.button("☕ 카페인", use_container_width=True):
        caffeine_dialog()

    if feature3.button("📄 상담", use_container_width=True):
        consultation_dialog()

    bottom1, bottom2 = st.columns(2)

    if bottom1.button(
        "🧍 인체·시뮬레이션",
        use_container_width=True,
    ):
        simulation_dialog()

    if bottom2.button(
        "🔬 근거·평가",
        use_container_width=True,
    ):
        evidence_dialog()

    next_dialog = st.session_state.pop("next_dialog", None)

    if next_dialog == "caffeine":
        caffeine_dialog()

    st.markdown(
        '<div class="footer-note main-footer">'
        "자료 없음 ≠ 안전 · 추가 복용 전 약사와 확인하세요."
        "</div>",
        unsafe_allow_html=True,
    )


if __name__ == "__main__":
    main()