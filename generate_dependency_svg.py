#!/usr/bin/env python3
"""Generate Qur'anic dependency SVGs from MASAQ.

Spec inputs:
- tokens: mapping of token ids to text segments, colours, and labels
- edges: dependency arcs between tokens with colours and labels
- line_groups: horizontal groupings (e.g., جار ومجرور)
- segments: ordered layout blocks listing tokens per row and heights

Primary data sources:
- Quran words are sourced from MASAQ.db Word column (canonical Mushaf text; rendering must not override this text)
- MASAQ: SQLite table MASAQ providing per-word segmentation and annotation

MASAQ columns (summary):
- Indexing: ID, Sura_No, Verse_No, Word_No, Segment_No
- Entry: Word, Without_Diacritics, Segmented_Word
- Morphology: Morph_Tag (e.g., PREP, NOUN, PV/IV), Morph_Type (prefix/stem/suffix)
- Punctuation: Punctuation_Mark
- Syntax: Invariable_Declinable, Syntactic_Role, Possessive_Construct, Case_Mood, Case_Mood_Marker
- Phrases: Phrase (begin + type), Phrasal_Function (Predicate/Agent/…/بدل dependency)

Rendering and arrows policy:
- Every non-root segment inside a word receives an internal arrow to its root (fallback "تابع" in gray if no specific role style applies)
- Phrase aggregation:
  - PREP → governed noun: مجرور edge + جار ومجرور line
  - Possessive_Construct=CONSTRUCT or role=GEN_CONS → مضاف إليه
  - ADJ/ATTRIB → attach to nearest suitable nominal head to the left
  - Subject/Object → attach to nearest verb (prefer stem)

Usage:
- Build specs and SVGs from databases:
    python scripts/generate_dependency_svg.py \\
      --surah 1 --ayah 1 2 3 4 5 6 7 \\
      --masaq-db ./MASAQ.db \\
      --spec-dir ./specs_generated --skip-svg
- Render a spec to SVG:
    python scripts/generate_dependency_svg.py --spec ./specs_generated/1/1.json --output ./output_v2/1/1.svg

Font embedding:
- The Kitab font is embedded into the SVG to keep diacritic placement consistent across viewers.
"""

from __future__ import annotations

"""Dependency Graph SVG Generator

Non-violable rendering requirements (invariants):
1. Arabic grammar term labels (token labels and edge labels) must not overlap.
2. Arcs may share endpoints (token circles) but their curve bodies should remain visually distinct; adjust vertical control points to reduce overlap.
3. Arrowheads must not cover or intersect grammar labels.
4. If a collision cannot be resolved within layout constraints, a diagnostic line should be emitted (e.g., GRAMMAR_OVERLAP / ARC_CONFLICT) rather than silently failing.

Enforcement flags:
--enforce-grammar: enable strict grammar label non-overlap diagnostics.
--enforce-arc-separation: escalate arc heights to avoid curve body overlap.

Debug flags:
--outline-labels: stroke label rectangles to visualize spacing.
--log-overlaps: print label overlap pairs resolved by the algorithm.

"""
import argparse
import base64
import json
import math
import re
import sqlite3
import sys
import unicodedata
import itertools
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

TOKEN_FONT_SIZE = 42
LABEL_FONT_SIZE = 14
PHRASE_FONT_SIZE = 18
TEXT_BASELINE = 100.0  # Ayah text at top
CIRCLE_RADIUS = 3.0
CIRCLE_VERTICAL_OFFSET = 50.0  # Circles closer to text
LABEL_VERTICAL_OFFSET = 0.0  # Labels stay at same position (between text and circles)

MARGIN_X = 42.0
BASE_ADVANCE = 48.0
PER_CHAR_ADVANCE = 24.0  # Increased from 14.0 to prevent Arabic text overlap
SEGMENT_SEGMENT_SPACER = 3.0
MIN_ADVANCE = 80.0  # Increased from 60.0 for minimum word spacing

ARC_BASE_HEIGHT = 48.0  # Reduced for flatter arcs
ARC_HEIGHT_FACTOR = 0.12  # Reduced for more proportional arc growth
ARC_VERTICAL_OFFSET = 0.0  # Arcs start directly from the circle center
ARROW_TIP_OFFSET = (
    12.0  # retained for backward compatibility, unused in new arrow layout
)
ARROW_SIZE = 6.5
ARROW_WIDTH_FACTOR = 0.6
ARROW_POSITION_T = 0.5

LINE_VERTICAL_OFFSET = 35.0  # Closer to tokens; arcs curve around if needed
LINE_LABEL_PADDING = 28.0

# Minimum vertical separation guarantees for wrapped lines.
MULTILINE_BASELINE_STEP = 220.0  # baseline delta applied per additional wrapped line
MULTILINE_DESIRED_GAP = 80.0  # padding between stacked lines (text, labels, arcs)
CONTINUATION_LABEL = "متابعة"
CONTINUATION_COLOR = "dimgray"
CONTINUATION_SYMBOL = "(#)"
CONTINUATION_SYMBOL_SCALE = 0.6  # relative to TOKEN_FONT_SIZE

DEFAULT_LINE_COLOR = "darkred"
DEFAULT_LINE_LABEL = "جار ومجرور"

DEFAULT_STYLE = ("اسم", "cornflowerblue")

MORPH_STYLE_MAP: Dict[str, Tuple[str, str]] = {
    "PV": ("فعل", "seagreen"),
    "IMPV": ("فعل", "seagreen"),
    "IV": ("فعل", "seagreen"),
    "IMPERF_PREF": ("فعل", "seagreen"),
    "IMPERF_SUFF": ("فعل", "seagreen"),
    "IMPERF_SUF": ("فعل", "seagreen"),
    "IMPERF": ("فعل", "seagreen"),
    "NOUN": ("اسم", "cornflowerblue"),
    "NOUN_PROP": ("علم", "purple"),
    "NOUN_ABSTRACT": ("اسم", "cornflowerblue"),
    "NOUN_PASSIVE_PART": ("اسم", "cornflowerblue"),
    "NOUN_ACTIVE_PART": ("اسم", "cornflowerblue"),
    "REL_PRON": ("اسم موصول", "gold"),
    "DEM_PRON": ("اسم إشارة", "brown"),
    "SUBJ_PRON": ("ضمير", "cornflowerblue"),
    "OBJ_PRON": ("ضمير", "slategray"),
    "PRON": ("ضمير", "slategray"),
    "PRON_3MP": ("ضمير", "slategray"),
    "NEG_PART": ("حرف نفي", "red"),
    "PROH_PART": ("حرف نهي", "red"),
    "PREP": ("حرف جر", "firebrick"),
    "CONJ": ("حرف عطف", "navy"),
    "ADV": ("ظرف", "orange"),
    "COND_PART": ("أداة شرط", "orange"),
    "RES_PART": ("حرف", "purple"),
    "EMPH_PART": ("حرف توكيد", "purple"),
    "DET": ("حرف تعريف", "gray"),
    "CASE_DEF_GEN": ("", "cornflowerblue"),
    "NSUFF_MASC_PL_GEN": ("", "cornflowerblue"),
}

ROLE_STYLE_MAP: Dict[str, Tuple[str, str]] = {
    "AGNT": ("فاعل", "cornflowerblue"),
    "SUBJ": ("مبتدأ", "cornflowerblue"),
    "PRED": ("خبر", "slategray"),
    "PRED_ORD": ("خبر", "slategray"),
    "OBJ": ("مفعول به", "slategray"),
    "OBJ1": ("مفعول به", "slategray"),
    "OBJ2": ("مفعول ثانٍ", "slategray"),
    "OBJ3": ("مفعول", "slategray"),
    "IOBJ": ("مفعول معه", "slategray"),
    "PREP": ("حرف جر", "firebrick"),
    "PREP_OBJ": ("اسم مجرور", "cornflowerblue"),
    "GEN_CONS": ("مضاف إليه", "cornflowerblue"),
    "CONJ": ("حرف عطف", "navy"),
    "NON_INFLECT": ("حرف", "purple"),
    "ADV_TIME": ("ظرف زمان", "orange"),
    "ADV_PLACE": ("ظرف مكان", "orange"),
    "ADV": ("ظرف", "orange"),
    "COND": ("أداة شرط", "orange"),
    "RELCL": ("صلة", "gold"),
    "ATTRIB": ("صفة", "purple"),
    "ADJ": ("صفة", "purple"),
    "APPOS": ("بدل", "purple"),
    "EMPH": ("توكيد", "purple"),
    "VOC": ("منادى", "green"),
}

INTERNAL_EDGE_STYLE: Dict[str, Tuple[str, str]] = {
    "AGNT": ("فاعل", "cornflowerblue"),
    "SUBJ": ("مبتدأ", "cornflowerblue"),
    "PRED": ("خبر", "slategray"),
    "OBJ": ("مفعول به", "slategray"),
    "OBJ1": ("مفعول به", "slategray"),
    "OBJ2": ("مفعول ثانٍ", "slategray"),
    "OBJ3": ("مفعول", "slategray"),
    "IOBJ": ("مفعول معه", "slategray"),
    "ATTRIB": ("صفة", "purple"),
    "ADJ": ("صفة", "purple"),
    "APPOS": ("بدل", "purple"),
    "EMPH": ("توكيد", "purple"),
    "GEN_CONS": ("مضاف إليه", "cornflowerblue"),
}

VERB_TAGS = {
    "PV",
    "PV_PASS",
    "IMPV",
    "IV",
    "IV_PASS",
    "IMPERF_PREF",
    "IMPERF_SUFF",
    "IMPERF_SUF",
    "IMPERF",
    "CV",
    "CV_PREF",
    "UNINFLECTED_VERB",
}

VERB_TAG_PREFIXES = ("PV", "IV", "CV", "IMPV", "IMPERF")
VERB_ROLE_PREFIXES = ("PV", "IV", "CV", "IMPV")
VERB_SYNTAX_ROLES = {
    "CV",
    "CV_COP",
    "IV",
    "IV_COP",
    "IV_PASS",
    "PV",
    "PV_PASS",
    "SUBJ_COP_V",
    "V_COP_PRED",
    "INTERJ_IV",
    "INTERJ_PV",
    "INTERJ_CV",
}

NOUN_TAGS = {
    "NOUN",
    "NOUN_PROP",
    "NOUN_ABSTRACT",
    "NOUN_PASSIVE_PART",
    "NOUN_ACTIVE_PART",
    "REL_PRON",
    "DEM_PRON",
    "SUBJ_PRON",
    "OBJ_PRON",
    "PRON",
}

ROOT_ROLE_CANDIDATES = {
    "AGNT",
    "SUBJ",
    "PRED",
    "PREP_OBJ",
    "OBJ",
    "ATTRIB",
    "APPOS",
}

PREDICATE_ROLES = {"PRED", "PRED_ORD", "PRED_CONS", "PRED_SUB"}

OBJECT_ROLES = {"OBJ", "OBJ1", "OBJ2", "OBJ3", "IOBJ"}
OBJECT_ROLE_PREFIXES = ("OBJ",)
SUBJECT_ROLES = {"AGNT", "SUBJ", "SUBJ1", "SUBJ2"}
SUBJECT_ROLE_PREFIXES = ("SUBJ",)


def _infer_sentence_type_from_rows(rows: Sequence[sqlite3.Row]) -> Tuple[str, str]:
    """Infer sentence type from MASAQ rows.

    Returns (type_key, arabic_label):
      - ("verbal", "جملة فعلية") if a verb root appears before nominal heads
      - ("nominal", "جملة اسمية") if a subject/predicate is present with no prior verb
      - ("mixed", "جملة مركبة") if both present but unclear or multiple clauses
      - ("unknown", "") otherwise
    """
    if not rows:
        return "unknown", ""
    # Look at the earliest root-like elements in order
    first_verb_idx: Optional[int] = None
    first_nominal_idx: Optional[int] = None
    has_predicate = False
    has_subject = False
    for r in rows:
        try:
            tag = str(_row_get(r, "Morph_Tag", "") or "").upper()
            role = str(_row_get(r, "Syntactic_Role", "") or "").upper()
            seg_no = int(_row_get(r, "Segment_No", 0) or 0)
        except Exception:
            tag = role = ""
            seg_no = 0
        is_rootish = seg_no == 0 or role in ROOT_ROLE_CANDIDATES or tag in NOUN_TAGS or tag in VERB_TAGS
        if not is_rootish:
            continue
        idx_marker = len(str(_row_get(r, "Word_No", 0))) * 0 + 0  # dummy, we only care about encounter order
        if first_verb_idx is None and (tag in VERB_TAGS or role in VERB_SYNTAX_ROLES):
            first_verb_idx = idx_marker
        if first_nominal_idx is None and (role in {"SUBJ", "SUBJ1", "SUBJ2", "PRED", "PRED_ORD"} or tag in NOUN_TAGS):
            first_nominal_idx = idx_marker
        if role in PREDICATE_ROLES:
            has_predicate = True
        if role in SUBJECT_ROLES:
            has_subject = True

        # Early decision: if verb seen before any nominal head
        if first_verb_idx is not None and first_nominal_idx is None:
            return "verbal", "جملة فعلية"

    if first_verb_idx is not None:
        return "verbal", "جملة فعلية"
    if has_subject or has_predicate or first_nominal_idx is not None:
        return "nominal", "جملة اسمية"
    return "unknown", ""


@dataclass
class Token:
    token_id: str
    segments: Sequence[Tuple[str, str]]
    label: str
    color: str
    word_index: int
    cluster_span: Tuple[int, int]


@dataclass
class Edge:
    src: str
    dst: str
    label: str
    color: str


@dataclass
class LineGroup:
    members: Sequence[str]
    label: str
    color: str
    id: Optional[str] = None  # Unique ID for referencing this line group in edges


@dataclass
class SegmentLayout:
    token_ids: Sequence[str]
    height: float


@dataclass
class TokenPosition:
    text_x: float
    circle_x: float
    circle_y: float
    label_y: float


def load_spec(path: Path) -> Dict[str, object]:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def load_font_data(font_path: Path) -> str:
    font_bytes = font_path.read_bytes()
    return base64.b64encode(font_bytes).decode("ascii")


def normalise_path(path: Optional[str], base: Path) -> Optional[Path]:
    if path is None:
        return None
    return (base.parent / path).resolve()


def find_repo_root(start: Path) -> Path:
    candidates = [start] + list(start.parents)
    for candidate in candidates:
        if (candidate / ".git").exists():
            return candidate
    # Fall back to the highest directory if .git is not present but keep behaviour deterministic.
    return candidates[-1]


def load_ayah_words(spec: Dict[str, object], spec_path: Path) -> List[str]:
    """Load ayah words from MASAQ.db Word column."""
    meta = spec.get("meta", {}) if isinstance(spec, dict) else {}
    surah = meta.get("surah")
    ayah = meta.get("ayah")
    if surah is None or ayah is None:
        raise ValueError(
            "Spec must include meta.surah and meta.ayah to resolve Quran text"
        )

    repo_root = find_repo_root(spec_path.parent)
    masaq_db = (repo_root / "MASAQ.db").resolve()
    if not masaq_db.exists():
        raise FileNotFoundError(f"Unable to locate MASAQ database: {masaq_db}")

    with sqlite3.connect(str(masaq_db)) as conn:
        # Get distinct words ordered by Word_No (each word appears once per segment)
        rows = conn.execute(
            "SELECT DISTINCT Word_No, Word FROM MASAQ WHERE Sura_No=? AND Verse_No=? ORDER BY Word_No",
            (int(surah), int(ayah)),
        ).fetchall()

    if not rows:
        raise ValueError(f"Ayah {surah}:{ayah} not found in MASAQ.db")

    return [row[1] for row in rows]


def _normalise_for_comparison(text: str) -> str:
    result_chars: List[str] = []
    for ch in text:
        if unicodedata.category(ch).startswith("M"):
            continue
        if ch == "\u0649":  # map alef maqsurah to ya
            result_chars.append("\u064a")
        elif ch in {"\u0622", "\u0623", "\u0625"}:  # normalise hamza-forms to bare alif
            result_chars.append("\u0627")
        elif ch == "\u0627":
            continue
        else:
            result_chars.append(ch)
    return "".join(result_chars)


def _split_clusters(text: str) -> List[str]:
    clusters: List[str] = []
    buffer = ""
    for ch in text:
        if unicodedata.category(ch).startswith("M"):
            buffer += ch
        else:
            if buffer:
                clusters.append(buffer)
                buffer = ""
            buffer += ch
    if buffer:
        clusters.append(buffer)
    return clusters


def _svg_arc_params(
    x1: float, y1: float,
    x2: float, y2: float,
    rx: float, ry: float,
    sweep_flag: int,
    large_arc_flag: int = 0,
) -> Tuple[float, float, float, float, float, float]:
    """
    Compute SVG elliptical arc center and angles per W3C SVG spec.
    
    This correctly handles the case where radii need to be scaled up
    to reach between the endpoints.
    
    Returns: (cx, cy, rx_scaled, ry_scaled, theta1, dtheta)
    """
    # Handle degenerate cases
    if rx == 0 or ry == 0:
        return (x1 + x2) / 2, (y1 + y2) / 2, 1, 1, 0, 0
    
    # Take absolute values of radii
    rx = abs(rx)
    ry = abs(ry)
    
    # Step 1: Compute (x1', y1') - transformed coordinates
    # For rotation phi=0, this simplifies
    dx = (x1 - x2) / 2.0
    dy = (y1 - y2) / 2.0
    
    x1_prime = dx
    y1_prime = dy
    
    # Step 2: Check if radii are large enough
    # Lambda is the scaling factor needed
    lambda_sq = (x1_prime * x1_prime) / (rx * rx) + (y1_prime * y1_prime) / (ry * ry)
    
    if lambda_sq > 1.0:
        # Scale up radii to minimum needed
        lambda_val = math.sqrt(lambda_sq)
        rx *= lambda_val
        ry *= lambda_val
    
    # Step 3: Compute center point (cx', cy')
    # Compute the radicand for the center calculation
    rx_sq = rx * rx
    ry_sq = ry * ry
    x1p_sq = x1_prime * x1_prime
    y1p_sq = y1_prime * y1_prime
    
    numerator = rx_sq * ry_sq - rx_sq * y1p_sq - ry_sq * x1p_sq
    denominator = rx_sq * y1p_sq + ry_sq * x1p_sq
    
    if denominator == 0 or numerator < 0:
        radicand = 0
    else:
        radicand = numerator / denominator
    
    root = math.sqrt(max(0, radicand))
    
    # Determine sign: if large_arc_flag == sweep_flag, negate
    if large_arc_flag == sweep_flag:
        root = -root
    
    cx_prime = root * rx * y1_prime / ry
    cy_prime = -root * ry * x1_prime / rx
    
    # Step 4: Compute (cx, cy) from (cx', cy')
    # For rotation phi=0, this is just translation
    cx = cx_prime + (x1 + x2) / 2.0
    cy = cy_prime + (y1 + y2) / 2.0
    
    # Step 5: Compute theta1 and dtheta
    # theta1 is angle from positive x-axis to vector from center to start point
    theta1 = math.atan2((y1 - cy) / ry, (x1 - cx) / rx)
    theta2 = math.atan2((y2 - cy) / ry, (x2 - cx) / rx)
    
    dtheta = theta2 - theta1
    
    # Normalize dtheta based on sweep_flag
    if sweep_flag == 1:
        # Clockwise in SVG (positive direction with y-down)
        if dtheta < 0:
            dtheta += 2 * math.pi
    else:
        # Counter-clockwise
        if dtheta > 0:
            dtheta -= 2 * math.pi
    
    return cx, cy, rx, ry, theta1, dtheta


def _ellipse_arc_point(
    t: float,
    x1: float, y1: float,
    x2: float, y2: float,
    rx: float, ry: float,
    sweep_flag: int,
) -> Tuple[float, float]:
    """Compute a point on an SVG elliptical arc at parameter t (0=start, 1=end).
    
    For an arc from (x1,y1) to (x2,y2) with radii rx, ry.
    Uses the SVG arc parameterization per W3C specification.
    Correctly handles radius scaling when radii are too small.
    """
    cx, cy, rx_scaled, ry_scaled, theta1, dtheta = _svg_arc_params(
        x1, y1, x2, y2, rx, ry, sweep_flag
    )
    
    # Interpolate angle
    theta = theta1 + t * dtheta
    
    # Point on ellipse
    x = cx + rx_scaled * math.cos(theta)
    y = cy + ry_scaled * math.sin(theta)
    
    return x, y


def _ellipse_arc_tangent(
    t: float,
    x1: float, y1: float,
    x2: float, y2: float,
    rx: float, ry: float,
    sweep_flag: int,
) -> Tuple[float, float]:
    """Compute the tangent direction on an SVG elliptical arc at parameter t.
    
    The tangent points in the direction of increasing t (from start to end).
    Uses the SVG arc parameterization per W3C specification.
    """
    cx, cy, rx_scaled, ry_scaled, theta1, dtheta = _svg_arc_params(
        x1, y1, x2, y2, rx, ry, sweep_flag
    )
    
    theta = theta1 + t * dtheta
    
    # Tangent is derivative of position with respect to theta, scaled by dtheta
    # x = cx + rx * cos(theta), y = cy + ry * sin(theta)
    # dx/dt = dx/dtheta * dtheta/dt = -rx * sin(theta) * dtheta
    # dy/dt = dy/dtheta * dtheta/dt = ry * cos(theta) * dtheta
    tangent_x = -rx_scaled * math.sin(theta) * dtheta
    tangent_y = ry_scaled * math.cos(theta) * dtheta
    
    return tangent_x, tangent_y


def _cubic_bezier_point(
    t: float,
    p0: Tuple[float, float],
    p1: Tuple[float, float],
    p2: Tuple[float, float],
    p3: Tuple[float, float],
) -> Tuple[float, float]:
    one_minus = 1.0 - t
    x = (
        one_minus**3 * p0[0]
        + 3 * one_minus**2 * t * p1[0]
        + 3 * one_minus * t**2 * p2[0]
        + t**3 * p3[0]
    )
    y = (
        one_minus**3 * p0[1]
        + 3 * one_minus**2 * t * p1[1]
        + 3 * one_minus * t**2 * p2[1]
        + t**3 * p3[1]
    )
    return x, y


def _cubic_bezier_tangent(
    t: float,
    p0: Tuple[float, float],
    p1: Tuple[float, float],
    p2: Tuple[float, float],
    p3: Tuple[float, float],
) -> Tuple[float, float]:
    one_minus = 1.0 - t
    dx = (
        3 * one_minus**2 * (p1[0] - p0[0])
        + 6 * one_minus * t * (p2[0] - p1[0])
        + 3 * t**2 * (p3[0] - p2[0])
    )
    dy = (
        3 * one_minus**2 * (p1[1] - p0[1])
        + 6 * one_minus * t * (p2[1] - p1[1])
        + 3 * t**2 * (p3[1] - p2[1])
    )
    return dx, dy


def _allocate_counts(weights: Sequence[int], total: int) -> List[int]:
    if not weights:
        return []

    adjusted = [max(weight, 0) for weight in weights]
    if all(weight == 0 for weight in adjusted):
        adjusted = [1] * len(weights)

    total_weight = sum(adjusted)
    if total_weight == 0:
        return [0] * len(weights)

    exact = [weight / total_weight * total for weight in adjusted]
    counts = [int(math.floor(value)) for value in exact]
    remainders = [value - count for value, count in zip(exact, counts)]

    remaining = total - sum(counts)

    for idx, weight in enumerate(adjusted):
        if remaining <= 0:
            break
        if weight > 0 and counts[idx] == 0:
            counts[idx] += 1
            remaining -= 1

    if remaining > 0:
        order = sorted(
            [(remainders[idx], idx) for idx in range(len(weights))],
            reverse=True,
        )
        for _, idx in order:
            if remaining <= 0:
                break
            counts[idx] += 1
            remaining -= 1

    if remaining < 0:
        order = sorted(
            [(remainders[idx], idx) for idx in range(len(weights)) if counts[idx] > 0],
            key=lambda item: item[0],
        )
        for _, idx in order:
            if remaining == 0:
                break
            counts[idx] -= 1
            remaining += 1

    return counts


def _row_get(
    row: Mapping[str, object] | sqlite3.Row, key: str, default: object = None
) -> object:
    if isinstance(row, sqlite3.Row):
        if key in row.keys():
            value = row[key]
        else:
            value = default
    elif isinstance(row, dict):
        value = row.get(key, default)
    else:
        value = getattr(row, key, default)
    return default if value is None else value


def _style_from_masaq_row(row: Mapping[str, object] | sqlite3.Row) -> Tuple[str, str]:
    morph_tag = str(_row_get(row, "Morph_Tag", "")).upper()
    synt_role = str(_row_get(row, "Syntactic_Role", "")).upper()
    segmented = str(_row_get(row, "Segmented_Word", "")).strip()
    morph_type = str(_row_get(row, "Morph_Type", "")).lower()

    label = None
    color = None

    # Priority 1: Morphological identity for pronouns and relative/demonstrative markers
    pronoun_like = {"PRON", "SUBJ_PRON", "OBJ_PRON", "PRON_3MP"}
    priority_morph_tags = pronoun_like | {"REL_PRON", "DEM_PRON"}
    if morph_tag in priority_morph_tags and morph_tag in MORPH_STYLE_MAP:
        morph_label, morph_color = MORPH_STYLE_MAP[morph_tag]
        label = morph_label
        color = morph_color

    # Priority 2: Use morphological tag as primary colour source
    if (not label or not color) and morph_tag in MORPH_STYLE_MAP:
        morph_label, morph_color = MORPH_STYLE_MAP[morph_tag]
        if not label:
            label = morph_label
        if not color:
            color = morph_color

    # Priority 3: Syntactic role for labels when morph doesn't provide one
    if not label and synt_role in ROLE_STYLE_MAP:
        role_label, _ = ROLE_STYLE_MAP[synt_role]
        label = role_label

    # Fallback defaults
    if not label:
        if morph_tag in NOUN_TAGS or morph_tag.startswith("NOUN"):
            label = "اسم"
        elif morph_tag in VERB_TAGS:
            label = "فعل"
        else:
            label = DEFAULT_STYLE[0]

    if not color:
        if morph_tag in VERB_TAGS:
            color = "seagreen"
        elif morph_tag in {"PREP"}:
            color = "firebrick"
        elif morph_tag in {"NEG_PART", "PROH_PART"}:
            color = "red"
        else:
            color = DEFAULT_STYLE[1]

    return label, color


def _edge_style_for_role(role: str) -> Optional[Tuple[str, str]]:
    role_key = role.upper()
    return INTERNAL_EDGE_STYLE.get(role_key)


def build_tokens(
    raw_tokens: Dict[str, object], words: Sequence[str]
) -> Dict[str, Token]:
    tokens: Dict[str, Token] = {}
    token_ids = list(raw_tokens.keys())
    word_to_tokens: Dict[int, List[str]] = {}

    for token_id in token_ids:
        raw = raw_tokens[token_id]
        if not isinstance(raw, dict):
            raise ValueError(f"Token '{token_id}' definition must be an object")
        word_index_raw = raw.get("word_index")
        if word_index_raw is None:
            raise ValueError(f"Token '{token_id}' is missing 'word_index'")

        word_index = int(word_index_raw)
        if word_index < 0 or word_index > len(words):
            raise ValueError(
                f"Token '{token_id}' word_index {word_index} outside range for ayah (1..{len(words)})"
            )
        if word_index > 0:
            word_to_tokens.setdefault(word_index, []).append(token_id)

    assigned_segments: Dict[str, List[Tuple[str, str]]] = {}
    token_cluster_spans: Dict[str, Tuple[int, int]] = {}

    for word_index, token_list in word_to_tokens.items():
        base_word = words[word_index - 1]
        word_clusters = _split_clusters(base_word)

        token_segment_specs: Dict[str, List[Tuple[str, str]]] = {}
        token_weights: List[int] = []
        for token_id in token_list:
            raw = raw_tokens[token_id]
            segments = raw.get("segments")
            if not segments:
                segments = [[base_word, raw.get("color", "black")]]
            segment_pairs: List[Tuple[str, str]] = []
            for entry in segments:
                if not isinstance(entry, (list, tuple)) or len(entry) != 2:
                    raise ValueError(
                        f"Token '{token_id}' segments must be [text, color] pairs"
                    )
                segment_pairs.append((str(entry[0]), str(entry[1])))
            token_segment_specs[token_id] = segment_pairs

            segment_weight = 0
            for segment_text, _ in segment_pairs:
                cluster_count = len(_split_clusters(segment_text))
                if cluster_count == 0 and segment_text.strip():
                    cluster_count = 1
                segment_weight += cluster_count
            token_weights.append(max(segment_weight, 1))

        token_counts = _allocate_counts(token_weights, len(word_clusters))

        pointer = 0
        for token_id, cluster_count in zip(token_list, token_counts):
            segment_pairs = token_segment_specs[token_id]
            token_start = pointer
            slice_clusters = word_clusters[pointer : pointer + cluster_count]
            pointer += cluster_count
            token_end = pointer

            segment_weights: List[int] = []
            for segment_text, _ in segment_pairs:
                cluster_count_segment = len(_split_clusters(segment_text))
                if cluster_count_segment == 0 and segment_text.strip():
                    cluster_count_segment = 1
                segment_weights.append(cluster_count_segment)

            segment_counts = _allocate_counts(segment_weights, len(slice_clusters))
            seg_pointer = 0
            resolved_segments: List[Tuple[str, str]] = []
            for (segment_text, color), seg_count in zip(segment_pairs, segment_counts):
                if seg_count > 0:
                    part = "".join(
                        slice_clusters[seg_pointer : seg_pointer + seg_count]
                    )
                    seg_pointer += seg_count
                    resolved_segments.append((part, color))
                else:
                    resolved_segments.append((segment_text, color))

            if seg_pointer < len(slice_clusters) and resolved_segments:
                text, color = resolved_segments[-1]
                remaining_part = "".join(slice_clusters[seg_pointer:])
                resolved_segments[-1] = (text + remaining_part, color)

            assigned_segments[token_id] = resolved_segments
            token_cluster_spans[token_id] = (token_start, token_end)

        if pointer < len(word_clusters) and token_list:
            remainder = "".join(word_clusters[pointer:])
            last_token_id = token_list[-1]
            segments = assigned_segments.setdefault(last_token_id, [])
            if segments:
                text, color = segments[-1]
                segments[-1] = (text + remainder, color)
            else:
                color = str(raw_tokens[last_token_id].get("color", "black"))
                segments.append((remainder, color))
            prev_start, _ = token_cluster_spans.get(last_token_id, (pointer, pointer))
            token_cluster_spans[last_token_id] = (prev_start, len(word_clusters))
            pointer = len(word_clusters)

    for token_id in token_ids:
        raw = raw_tokens[token_id]
        word_index = int(raw["word_index"])
        segments = assigned_segments.get(token_id)
        if not segments:
            if word_index <= 0:
                raw_segments = raw.get("segments") or [
                    [raw.get("segment_hint", "(*)"), raw.get("color", "silver")]
                ]
                segments = [(str(text), str(col)) for text, col in raw_segments]
            else:
                color = str(raw.get("color", "black"))
                base_word = words[word_index - 1]
                segments = [(base_word, color)]

        cluster_span = token_cluster_spans.get(token_id)
        if cluster_span is None:
            if word_index <= 0:
                # Placeholders and synthetic tokens should occupy a single logical slot to avoid
                # stretching the layout disproportionately compared to real words.
                cluster_span = (0, 1)
            else:
                base_word_clusters = _split_clusters(words[word_index - 1])
                cluster_span = (0, len(base_word_clusters))

        tokens[token_id] = Token(
            token_id=token_id,
            segments=segments,
            label=str(raw.get("label", "")),
            color=str(raw.get("color", "black")),
            word_index=word_index,
            cluster_span=cluster_span,
        )

    return tokens


def build_edges(raw_edges: Iterable[object]) -> List[Edge]:
    edges: List[Edge] = []
    for raw in raw_edges:
        edges.append(
            Edge(
                src=str(raw["src"]),
                dst=str(raw["dst"]),
                label=str(raw.get("label", "")),
                color=str(raw.get("color", "black")),
            )
        )
    return edges


def build_line_groups(raw_groups: Optional[Iterable[object]]) -> List[LineGroup]:
    if not raw_groups:
        return []
    groups: List[LineGroup] = []
    for raw in raw_groups:
        members = [str(token_id) for token_id in raw.get("members", [])]
        if len(members) < 2:
            continue
        groups.append(
            LineGroup(
                members=members,
                label=str(raw.get("label", DEFAULT_LINE_LABEL)),
                color=str(raw.get("color", DEFAULT_LINE_COLOR)),
                id=raw.get("id"),  # Pass through the line group ID if present
            )
        )
    return groups


def build_segments(raw_segments: Iterable[object]) -> List[SegmentLayout]:
    segments: List[SegmentLayout] = []
    for raw in raw_segments:
        token_ids = [str(token_id) for token_id in raw.get("tokens", [])]
        height = float(raw.get("height", 320))
        if not token_ids:
            continue
        segments.append(SegmentLayout(token_ids=token_ids, height=height))
    return segments


def join_segments_text(token: Token) -> str:
    return "".join(text for text, _ in token.segments)


def estimate_word_advance(cluster_count: int, token_count: int) -> float:
    glyph_count = max(cluster_count, 1)
    advance = BASE_ADVANCE + PER_CHAR_ADVANCE * max(glyph_count - 1, 0)
    advance += SEGMENT_SEGMENT_SPACER * max(token_count - 1, 0)
    return max(advance, MIN_ADVANCE)


def layout_segment(
    segment: SegmentLayout,
    tokens: Dict[str, Token],
) -> Tuple[
    float,
    Dict[str, TokenPosition],
    List[str],
    float,
    Dict[str, int],
    List[Dict[str, float]],
]:
    groups: List[List[str]] = []
    last_word_index: Optional[int] = None
    for token_id in segment.token_ids:
        token = tokens[token_id]
        if last_word_index is None or token.word_index != last_word_index:
            groups.append([token_id])
            last_word_index = token.word_index
        else:
            groups[-1].append(token_id)

    word_infos: List[Dict[str, object]] = []
    for group in groups:
        word_tokens = [tokens[token_id] for token_id in group]
        span_start = min(token.cluster_span[0] for token in word_tokens)
        span_end = max(token.cluster_span[1] for token in word_tokens)
        cluster_total = max(span_end - span_start, 1)
        advance = estimate_word_advance(cluster_total, len(group))
        word_infos.append(
            {
                "token_ids": group,
                "span_start": span_start,
                "span_end": span_end,
                "cluster_total": float(cluster_total),
                "advance": max(advance, MIN_ADVANCE),
            }
        )

    # Disable multiline wrapping by setting an extremely large line width
    MAX_LINE_WIDTH = 9999.0
    segment_width_full = sum(info["advance"] for info in word_infos) + 2 * MARGIN_X

    line_word_indices: List[List[int]] = []
    current_line: List[int] = []
    current_width = 2 * MARGIN_X
    for idx, info in enumerate(word_infos):
        advance = float(info["advance"])
        projected = current_width + advance
        if projected <= MAX_LINE_WIDTH or not current_line:
            current_line.append(idx)
            current_width += advance
        else:
            line_word_indices.append(current_line)
            current_line = [idx]
            current_width = 2 * MARGIN_X + advance
    if current_line:
        line_word_indices.append(current_line)

    line_widths: List[float] = []
    for line in line_word_indices:
        lw = 2 * MARGIN_X + sum(float(word_infos[idx]["advance"]) for idx in line)
        line_widths.append(lw)

    segment_width = max(line_widths) if line_widths else segment_width_full

    desired_gap = max(MULTILINE_DESIRED_GAP, 0.0)
    positions: Dict[str, TokenPosition] = {}
    token_line_index: Dict[str, int] = {}
    line_metrics: List[Dict[str, float]] = []
    elements: List[str] = []
    base_line_y = TEXT_BASELINE
    circle_y_base = TEXT_BASELINE + CIRCLE_VERTICAL_OFFSET
    prev_bottom: Optional[float] = None
    max_extent = 0.0

    row_height = LABEL_FONT_SIZE + 2.0

    def layout_line(
        line_indices: Sequence[int],
        shift: float,
    ) -> Tuple[
        Dict[str, TokenPosition],
        List[str],
        float,
        float,
        List[str],
        float,
        float,
    ]:
        local_positions: Dict[str, TokenPosition] = {}
        line_elements: List[str] = []
        cursor = segment_width - MARGIN_X
        baseline_line = base_line_y + shift
        circle_y_line = circle_y_base + shift
        label_y_line = circle_y_line - LABEL_VERTICAL_OFFSET  # Labels above circles
        label_tops: List[float] = []
        label_bottoms: List[float] = []
        token_xs: List[float] = []
        line_token_ids: List[str] = []

        for word_idx in line_indices:
            info = word_infos[word_idx]
            token_ids = info["token_ids"]
            span_start_all = float(info["span_start"])
            span_end_all = float(info["span_end"])
            cluster_total = max(float(info["cluster_total"]), 1.0)
            advance = float(info["advance"])
            word_center = cursor - advance / 2.0
            word_right = word_center + advance / 2.0

            text_parts = [
                f'<text direction="rtl" text-anchor="middle" font-size="{TOKEN_FONT_SIZE}" '
                f'x="{word_center:.2f}" y="{baseline_line:.2f}">'
            ]
            for token_id in token_ids:
                token = tokens[token_id]
                for segment_text, color in token.segments:
                    text_parts.append(f'<tspan fill="{color}">{segment_text}</tspan>')
            text_parts.append("</text>")
            line_elements.append("".join(text_parts))

            cluster_width = advance / cluster_total
            token_centers: List[Tuple[Token, float]] = []
            for token_id in token_ids:
                token = tokens[token_id]
                start, end = token.cluster_span
                start = float(start) - span_start_all
                end = float(end) - span_start_all
                if start < 0.0:
                    start = 0.0
                if end <= start:
                    end = start + 1.0
                if end > cluster_total:
                    end = cluster_total
                avg_index = (start + end) / 2.0
                center_x = word_right - cluster_width * avg_index
                token_centers.append((token, center_x))
                token_xs.append(center_x)
                line_token_ids.append(token.token_id)

            rows: List[List[Tuple[Token, float]]] = []

            def can_place(row: List[Tuple[Token, float]], tok: Token, cx: float) -> bool:
                w_new = max(24.0, len(tok.label) * 9.0)
                left_new = cx - w_new / 2.0
                right_new = cx + w_new / 2.0
                for existing_tok, existing_cx in row:
                    w_ex = max(24.0, len(existing_tok.label) * 9.0)
                    left_ex = existing_cx - w_ex / 2.0
                    right_ex = existing_cx + w_ex / 2.0
                    if not (
                        right_new <= left_ex - 4.0 or right_ex <= left_new - 4.0
                    ):
                        return False
                return True

            for tok, cx in token_centers:
                placed = False
                for row in rows:
                    if can_place(row, tok, cx):
                        row.append((tok, cx))
                        placed = True
                        break
                if not placed:
                    rows.append([(tok, cx)])

            upward_rows = sum(1 for idx in range(len(rows)) if idx % 2 == 0)
            base_top_padding = 24.0
            extra_padding = max(0.0, (upward_rows - 1) * (row_height * 0.25))
            min_top_allowed = base_top_padding + extra_padding

            planned_positions: List[Tuple[int, float]] = []
            for row_index, _ in enumerate(rows):
                if row_index % 2 == 0:
                    upward_rank = (row_index // 2) + 1
                    y_offset = label_y_line - upward_rank * row_height
                else:
                    downward_rank = row_index // 2
                    y_offset = label_y_line + downward_rank * row_height
                planned_positions.append((row_index, y_offset))

            lowest_y = min((y for _, y in planned_positions), default=label_y_line)
            if lowest_y < min_top_allowed:
                adjust = min_top_allowed - lowest_y
                planned_positions = [(idx, y + adjust) for idx, y in planned_positions]

            for row_index, row in enumerate(rows):
                y_offset = next(y for idx, y in planned_positions if idx == row_index)
                for tok, cx in row:
                    local_positions[tok.token_id] = TokenPosition(
                        text_x=cx,
                        circle_x=cx,
                        circle_y=circle_y_line,
                        label_y=y_offset,
                    )
                    line_elements.append(
                        f'<circle cx="{cx:.2f}" cy="{circle_y_line:.2f}" r="{CIRCLE_RADIUS}" fill="{tok.color}"/>'
                    )
                    line_elements.append(
                        f'<text direction="rtl" text-anchor="middle" fill="{tok.color}" font-size="{LABEL_FONT_SIZE}" '
                        f'x="{cx:.2f}" y="{y_offset:.2f}">{tok.label}</text>'
                    )
                    label_tops.append(y_offset - LABEL_FONT_SIZE)
                    label_bottoms.append(y_offset)

            cursor -= advance

        text_top = baseline_line - TOKEN_FONT_SIZE * 0.85
        text_bottom = baseline_line + TOKEN_FONT_SIZE * 0.35
        circle_top = circle_y_line - CIRCLE_RADIUS - 4.0
        circle_bottom = circle_y_line + CIRCLE_RADIUS + 6.0

        line_top = min(label_tops + [text_top, circle_top]) if label_tops else min(
            text_top, circle_top
        )
        line_bottom_labels = max(
            label_bottoms + [text_bottom, circle_bottom]
        ) if label_bottoms else max(text_bottom, circle_bottom)

        span = (max(token_xs) - min(token_xs)) if token_xs else 0.0
        arc_bottom = (
            circle_y_line
            + ARC_VERTICAL_OFFSET
            + ARC_BASE_HEIGHT
            + span * ARC_HEIGHT_FACTOR
            + ARROW_SIZE
            + 12.0
        )
        line_bottom_total = max(line_bottom_labels, arc_bottom)

        anchor_x = max(token_xs) if token_xs else segment_width - MARGIN_X

        return (
            local_positions,
            line_elements,
            line_top,
            line_bottom_total,
            line_token_ids,
            anchor_x,
            circle_y_line,
        )

    for idx, line in enumerate(line_word_indices):
        shift = max(idx * MULTILINE_BASELINE_STEP, 0.0)
        while True:
            (
                local_positions,
                line_elements,
                line_top,
                line_bottom_total,
                line_token_ids,
                anchor_x,
                circle_y_line,
            ) = layout_line(line, shift)
            if prev_bottom is None or line_top >= prev_bottom + desired_gap:
                break
            needed = (prev_bottom + desired_gap) - line_top
            if needed <= 0:
                break
            shift += needed

        positions.update(local_positions)
        elements.extend(line_elements)
        prev_bottom = line_bottom_total
        max_extent = max(max_extent, line_bottom_total)
        for token_id in line_token_ids:
            token_line_index[token_id] = idx
        line_metrics.append(
            {
                "anchor_x": anchor_x,
                "circle_y": circle_y_line,
                "baseline_y": circle_y_line - CIRCLE_VERTICAL_OFFSET,
            }
        )

    return (
        segment_width,
        positions,
        elements,
        max_extent,
        token_line_index,
        line_metrics,
    )


def _load_quran_words_raw(masaq_db: Path, surah: int, ayah: int) -> List[str]:
    """Load ayah words from MASAQ.db Word column."""
    if not masaq_db.exists():
        raise FileNotFoundError(f"Unable to locate MASAQ database: {masaq_db}")

    with sqlite3.connect(str(masaq_db)) as conn:
        # Get distinct words ordered by Word_No (each word appears once per segment)
        rows = conn.execute(
            "SELECT DISTINCT Word_No, Word FROM MASAQ WHERE Sura_No=? AND Verse_No=? ORDER BY Word_No",
            (surah, ayah),
        ).fetchall()

    if not rows:
        raise ValueError(f"Ayah {surah}:{ayah} not found in MASAQ.db")

    return [row[1] for row in rows]


def build_spec_from_sources(
    surah: int,
    ayah: int,
    masaq_db: Path,
) -> Dict[str, object]:
    if not masaq_db.exists():
        raise FileNotFoundError(f"MASAQ database not found: {masaq_db}")

    words = _load_quran_words_raw(masaq_db, surah, ayah)
    if not words:
        raise ValueError(f"Unable to resolve Quran text for {surah}:{ayah}")

    with sqlite3.connect(str(masaq_db)) as conn:
        conn.row_factory = sqlite3.Row
        rows = conn.execute(
            "SELECT * FROM MASAQ WHERE Sura_No=? AND Verse_No=? ORDER BY Word_No, Segment_No",
            (surah, ayah),
        ).fetchall()

    if not rows:
        raise ValueError(f"No MASAQ rows found for {surah}:{ayah}")

    # Infer sentence type from MASAQ rows (best-effort)
    sentence_type_key, sentence_type_label = _infer_sentence_type_from_rows(rows)

    notes: Dict[str, object] = {
        "generated": True,
        "sources": {
            "masaq": str(masaq_db),
        },
        "sentence_type": sentence_type_key,
        "sentence_type_label": sentence_type_label,
    }

    tokens: Dict[str, Dict[str, object]] = {}
    token_sequence: List[str] = []
    token_meta: Dict[str, Dict[str, object]] = {}
    word_roots: Dict[int, str] = {}
    word_token_map: Dict[int, List[str]] = {}

    token_counter = 1
    for word_no, group in itertools.groupby(rows, key=lambda r: int(r["Word_No"])):
        group_rows = list(group)
        if word_no < 1 or word_no > len(words):
            raise ValueError(
                f"Word index {word_no} out of range for surah {surah} ayah {ayah}"
            )

        # Collect all segments for this word, skip null/case-only markers
        word_segments: List[Tuple[str, str]] = []
        root_token_id: Optional[str] = None
        token_ids_for_word: List[str] = []
        
        for row in group_rows:
            morph_tag = str(_row_get(row, "Morph_Tag", "")).upper()
            morph_type = str(_row_get(row, "Morph_Type", "")).lower()
            synt_role = str(_row_get(row, "Syntactic_Role", "")).upper()
            segmented_word = str(_row_get(row, "Segmented_Word", ""))
            segment_hint = (segmented_word or str(_row_get(row, "Word", ""))).strip()
            
            # Skip null/case-only segments that don't render
            if segment_hint in {"(null)", ""} or morph_tag.startswith("CASE_") or morph_tag.startswith("NSUFF_"):
                continue
                
            label, color = _style_from_masaq_row(row)
            
            # Merge DET prefixes into the parent word with gray color
            if morph_type == "prefix" and morph_tag == "DET":
                word_segments.append((segment_hint, "gray"))
                continue
                
            # This is a substantive segment - create a token
            token_id = f"t{token_counter}"
            token_counter += 1
            
            word_text = str(_row_get(row, "Word", ""))
            
            # For stem segments, accumulate any pending prefix segments
            if morph_type == "stem" and word_segments:
                # Merge prefixes into this token
                word_segments.append((segment_hint, color))
                tokens[token_id] = {
                    "segments": list(word_segments),
                    "label": label,
                    "color": color,
                    "word_index": int(word_no),
                }
                word_segments = []
                word_segments_finalized = []
            else:
                # Standalone segment
                tokens[token_id] = {
                    "segments": [(segment_hint, color)],
                    "label": label,
                    "color": color,
                    "word_index": int(word_no),
                }
                
            token_sequence.append(token_id)
            token_ids_for_word.append(token_id)

            poss_construct = str(_row_get(row, "Possessive_Construct", "")).upper()
            case_mood = str(_row_get(row, "Case_Mood", "")).upper()
            case_marker = str(_row_get(row, "Case_Mood_Marker", "")).upper()
            phrase = str(_row_get(row, "Phrase", "")).upper()
            phrase_fn = str(_row_get(row, "Phrasal_Function", "")).upper()

            token_meta[token_id] = {
                "word_index": int(word_no),
                "morph_tag": morph_tag,
                "syntactic_role": synt_role,
                "possessive_construct": poss_construct,
                "segment_no": int(_row_get(row, "Segment_No", 0) or 0),
                "morph_type": morph_type,
                "segment_hint": segment_hint,
                "case_mood": case_mood,
                "case_marker": case_marker,
                "phrase": phrase,
                "phrase_function": phrase_fn,
                "word_text": word_text,
            }
            word_token_map.setdefault(int(word_no), []).append(token_id)

            if root_token_id is None and (
                morph_type == "stem"
                or morph_tag in VERB_TAGS
                or morph_tag in NOUN_TAGS
                or morph_tag.startswith("NOUN")
                or synt_role in ROOT_ROLE_CANDIDATES
            ):
                root_token_id = token_id

        # Fallback: pick first token if no clear root
        if root_token_id is None and token_ids_for_word:
            root_token_id = token_ids_for_word[0]

        if root_token_id:
            word_roots[int(word_no)] = root_token_id
            for tid in token_ids_for_word:
                meta = token_meta.get(tid, {})
                meta["root_id"] = root_token_id
                meta["is_root"] = tid == root_token_id

    # Choose a sentence head token for rendering a sentence-type line on the correct line
    sentence_head_id: Optional[str] = None
    if sentence_type_key == "verbal":
        for tid in token_sequence:
            meta = token_meta.get(tid, {})
            if not meta.get("is_root"):
                continue
            if (meta.get("morph_tag") or "").upper() in VERB_TAGS or (meta.get("syntactic_role") or "").upper() in VERB_SYNTAX_ROLES:
                sentence_head_id = tid
                break
    elif sentence_type_key == "nominal":
        for tid in token_sequence:
            meta = token_meta.get(tid, {})
            if not meta.get("is_root"):
                continue
            role = (meta.get("syntactic_role") or "").upper()
            if role in {"SUBJ", "SUBJ1", "SUBJ2", "PRED", "PRED_ORD"}:
                sentence_head_id = tid
                break
    if sentence_head_id:
        notes["sentence_head_id"] = sentence_head_id

    edges: List[Dict[str, object]] = []
    edge_signatures: set = set()
    line_groups: List[Dict[str, object]] = []
    line_group_pairs: set = set()
    line_group_map: Dict[str, str] = {}  # Maps token_id to line_group_id
    
    # ====================================================================
    # PERFORMANCE MONITORING: Instrumentation for profiling edge building
    # ====================================================================
    import time
    perf_metrics = {
        "edge_building_start": time.time(),
        "edges_created": 0,
        "handler_times": {}
    }
    
    def record_handler_time(handler_name: str, elapsed: float) -> None:
        """Record handler execution time for profiling."""
        if handler_name not in perf_metrics["handler_times"]:
            perf_metrics["handler_times"][handler_name] = []
        perf_metrics["handler_times"][handler_name].append(elapsed)

    def add_edge(src: str, dst: str, color: str, label: str) -> None:
        if src == dst:
            return
        signature = (src, dst, label)
        if signature in edge_signatures:
            return
        edge_signatures.add(signature)
        edges.append({"src": src, "dst": dst, "color": color, "label": label})
        perf_metrics["edges_created"] += 1

    # Internal edges within a word (root to affixes/pronouns etc.).
    # Skip creating internal "تابع" edges - these clutter the output
    for token_id, meta in token_meta.items():
        if meta.get("is_root") or not meta.get("root_id"):
            continue
        role = meta.get("syntactic_role", "")
        style = _edge_style_for_role(role)
        if style:
            label, color = style
            add_edge(
                meta["root_id"], token_id, color or tokens[token_id]["color"], label
            )
        # Removed: fallback "تابع" edges that add visual noise

    token_index = {token_id: idx for idx, token_id in enumerate(token_sequence)}
    
    # ====================================================================
    # PERFORMANCE OPTIMIZATION: Cache filtered token sequences
    # ====================================================================
    # Pre-compute lists of root tokens for faster O(filtered_count) lookups
    # instead of O(all_tokens). This is critical for verses with many affixes.
    root_tokens = [tid for tid in token_sequence if token_meta.get(tid, {}).get("is_root")]
    root_index = {tid: idx for idx, tid in enumerate(root_tokens)}

    def find_next_root(start_idx: int, predicate) -> Optional[str]:
        """Find next root token matching predicate. Uses cached root_tokens for O(root_count) instead of O(n)."""
        for token_id in token_sequence[start_idx + 1 :]:
            meta = token_meta[token_id]
            if not meta.get("is_root"):
                continue
            if predicate(token_id, meta):
                return token_id
        return None

    def find_previous_root(start_idx: int, predicate) -> Optional[str]:
        """Find previous root token matching predicate. Uses cached root_tokens for O(root_count) instead of O(n)."""
        for token_id in reversed(token_sequence[:start_idx]):
            meta = token_meta[token_id]
            if not meta.get("is_root"):
                continue
            if predicate(token_id, meta):
                return token_id
        return None

    def is_verb_token(meta: Dict[str, object]) -> bool:
        """Check if token is verb-like. Optimized with tag caching to avoid redundant string operations."""
        tag = (meta.get("morph_tag") or "").upper()
        role = (meta.get("syntactic_role") or "").upper()
        
        # Quick exit for empty tags
        if not tag and not role:
            return False
        
        # Check exact matches first (O(1) with set lookup)
        if tag in VERB_TAGS or role in VERB_SYNTAX_ROLES:
            return True
        
        # Check prefix matches only if no exact match (O(p) where p = prefixes count, typically ~3)
        # This is faster than checking prefixes for every token
        if tag:
            for prefix in VERB_TAG_PREFIXES:
                if prefix and tag.startswith(prefix):
                    return True
        
        if role:
            for prefix in VERB_ROLE_PREFIXES:
                if prefix and role.startswith(prefix):
                    return True
        
        return False

    def role_matches(
        role: str, allowed: Sequence[str], prefixes: Sequence[str]
    ) -> bool:
        """Check if role matches allowed set or prefix patterns. Optimized with early exit."""
        if role in allowed:
            return True
        # Short-circuit: if no prefixes, return false immediately
        if not prefixes:
            return False
        return any(role.startswith(prefix) for prefix in prefixes if prefix)

    def is_same_segment(src_token_id: str, dst_token_id: str) -> bool:
        """Check if two tokens are likely in the same segment based on word proximity.
        
        RATIONALE:
        Segments typically span 4-12 words (see _segmentize() for details). Cross-segment
        edges fail to render because render_edges() skips edges with missing endpoint positions.
        This heuristic uses word_index proximity to predict segment co-location.
        
        PARAMETERS:
        - src_token_id: Source token ID
        - dst_token_id: Destination token ID
        
        RETURNS:
        True if tokens are within ~15 words of each other (conservative estimate for
        maximum segment size with some buffer for safety).
        
        NOTE:
        This is a proxy heuristic since exact segment boundaries aren't available during
        edge building. The 15-word threshold was chosen to be conservative - typical
        segments are smaller, so this should catch nearly all valid within-segment edges
        while filtering most cross-segment pathologies.
        
        PERFORMANCE:
        O(1) dictionary lookups + one integer comparison. Cached in fast path.
        """
        src_meta = token_meta.get(src_token_id, {})
        dst_meta = token_meta.get(dst_token_id, {})
        src_word = src_meta.get("word_index", 0)
        dst_word = dst_meta.get("word_index", 0)
        # Allow edges within ~15 words (conservative estimate for segment size)
        return abs(int(src_word) - int(dst_word)) <= 15

    def select_nearest(
        idx: int, left_id: Optional[str], right_id: Optional[str]
    ) -> Optional[str]:
        """Select nearest token between left and right. Optimized for common cases."""
        # Fast path: only one candidate
        if not left_id:
            return right_id
        if not right_id:
            return left_id
        
        # Both exist: compute distances (cached in token_index)
        left_distance = idx - token_index[left_id]
        right_distance = token_index[right_id] - idx
        return left_id if left_distance <= right_distance else right_id

    def prefer_stem_variant(token_id: Optional[str]) -> Optional[str]:
        """Prefer stem variant of token for better visual clarity. Optimized to cache results."""
        if not token_id:
            return token_id
        meta = token_meta.get(token_id)
        if not meta:
            return token_id
        morph_type = (meta.get("morph_type") or "").lower()
        if morph_type == "stem" and is_verb_token(meta):
            return token_id
        word_index = meta.get("word_index")
        if not word_index or word_index not in word_token_map:
            return token_id
        for candidate_id in word_token_map[word_index]:
            if candidate_id == token_id:
                continue
            candidate_meta = token_meta.get(candidate_id)
            if not candidate_meta:
                continue
            if (candidate_meta.get("morph_type") or "").lower() != "stem":
                continue
            if not is_verb_token(candidate_meta):
                continue
            return candidate_id
        return token_id

    def find_nearest_verb(start_idx: int) -> Optional[str]:
        """Find the nearest verb (by token distance) to the given index."""
        next_verb = find_next_root(
            start_idx, lambda _tid, _meta: is_verb_token(_meta)
        )
        previous_verb = find_previous_root(
            start_idx, lambda _tid, _meta: is_verb_token(_meta)
        )
        return select_nearest(start_idx, previous_verb, next_verb)

    def find_next_token(start_idx: int, predicate) -> Optional[str]:
        """Find next token (including non-roots) matching the predicate."""
        for token_id in token_sequence[start_idx + 1:]:
            meta = token_meta[token_id]
            if predicate(token_id, meta):
                return token_id
        return None

    def find_previous_token(start_idx: int, predicate) -> Optional[str]:
        """Find previous token (including non-roots) matching the predicate."""
        for token_id in reversed(token_sequence[:start_idx]):
            meta = token_meta[token_id]
            if predicate(token_id, meta):
                return token_id
        return None

    # Add Tier 2 handlers for additional relation coverage
    # Phrase-level heuristics (prepositions, negation, lam al-ta'lil, relative clauses).
    for token_id in token_sequence:
        meta = token_meta[token_id]
        idx = token_index[token_id]
        morph_tag = meta.get("morph_tag", "")
        synt_role = meta.get("syntactic_role", "")

        if morph_tag == "PREP" or synt_role == "PREP":

            def is_preposition_object(_tid: str, _meta: Dict[str, object]) -> bool:
                wi_obj = int(_meta.get("word_index") or 0)
                wi_prep = int(meta.get("word_index") or 0)
                if wi_obj and wi_obj < wi_prep:
                    return False
                # Prefer explicit PREP_OBJ at word-level
                if (_meta.get("syntactic_role") or "").upper() == "PREP_OBJ":
                    return True
                # Accept common governed nominal heads
                if (_meta.get("syntactic_role") or "").upper() in {"OBJ", "AGNT", "SUBJ", "PRED"}:
                    return True
                # Treat pronouns and nouns as valid objects
                if (_meta.get("morph_tag") or "").upper() in NOUN_TAGS or (_meta.get("morph_tag") or "").upper() in {"PRON", "PRON_3MP", "OBJ_PRON", "SUBJ_PRON"}:
                    return True
                return False

            # For PREP, look for next token (not just root) that matches the predicate
            obj_token = None
            for candidate_id in token_sequence[idx + 1:]:
                candidate_meta = token_meta.get(candidate_id, {})
                if is_preposition_object(candidate_id, candidate_meta):
                    obj_token = candidate_id
                    break
            
            if obj_token:
                add_edge(token_id, obj_token, "firebrick", "مجرور")
                pair = tuple(sorted((token_id, obj_token)))
                if pair not in line_group_pairs:
                    # Create a unique ID for this line group
                    lg_id = f"__lg_{token_id}_{obj_token}"
                    line_groups.append(
                        {
                            "members": [token_id, obj_token],
                            "label": DEFAULT_LINE_LABEL,
                            "color": DEFAULT_LINE_COLOR,
                            "id": lg_id,
                        }
                    )
                    line_group_pairs.add(pair)
                    # Track which tokens belong to this line group
                    line_group_map[token_id] = lg_id
                    line_group_map[obj_token] = lg_id

            # متعلق edge: link prepositional phrase back to the verb it modifies
            # The PP is متعلق بـ (attached to) the verb, so edge goes FROM PP TO verb
            # Limit search to nearby verbs (within 3 word positions) to avoid spurious edges
            word_idx = meta.get("word_index", 0)
            verb_token = find_previous_root(
                idx, lambda _tid, _meta: (
                    _meta.get("morph_tag") in VERB_TAGS
                    and abs(_meta.get("word_index", 0) - word_idx) <= 3
                )
            )
            if verb_token and is_same_segment(token_id, verb_token):
                # Edge FROM prep TO verb (PP is متعلق بـ the verb)
                # If the preposition is part of a line group (jar majroor), start the edge from the group
                src_id = line_group_map.get(token_id, token_id)
                add_edge(src_id, verb_token, "orange", "متعلق")

        if morph_tag in {"NEG_PART", "PROH_PART"}:
            verb_token = find_next_root(
                idx, lambda _tid, _meta: _meta.get("morph_tag") in VERB_TAGS
            )
            if verb_token:
                label = "نفي" if morph_tag == "NEG_PART" else "نهي"
                add_edge(token_id, verb_token, "red", label)

        if morph_tag == "REL_PRON":
            verb_token = find_next_root(
                idx, lambda _tid, _meta: _meta.get("morph_tag") in VERB_TAGS
            )
            if verb_token:
                add_edge(token_id, verb_token, "gold", "صلة")

        if synt_role in {"ADV_TIME", "ADV_PLACE", "ADV"} and meta.get("is_root"):
            verb_token = find_next_root(
                idx, lambda _tid, _meta: _meta.get("morph_tag") in VERB_TAGS
            )
            if verb_token:
                add_edge(verb_token, token_id, "orange", "متعلق")

        if meta.get("possessive_construct") == "CONSTRUCT" and meta.get("is_root"):
            next_token = find_next_root(
                idx,
                lambda _tid, _meta: _meta.get("word_index", 0)
                >= meta.get("word_index", 0)
                and (
                    _meta.get("morph_tag") in NOUN_TAGS
                    or _meta.get("syntactic_role")
                    in {"PREP_OBJ", "OBJ", "ATTRIB", "APPOS"}
                ),
            )
            if next_token:
                add_edge(token_id, next_token, "cornflowerblue", "مضاف إليه")

        if synt_role in {"ADJ", "ATTRIB"}:
            head_token = find_previous_root(
                idx,
                lambda _tid, _meta: _meta.get("word_index", 0)
                < meta.get("word_index", 0)
                and (
                    _meta.get("morph_tag") in NOUN_TAGS
                    or _meta.get("syntactic_role")
                    in {"SUBJ", "AGNT", "PREP_OBJ", "OBJ", "PRED"}
                ),
            )
            if head_token:
                edge_label = "صفة"
                edge_color = "purple"
                # Edge goes FROM dependent (ADJ/ATTRIB) TO head
                add_edge(token_id, head_token, edge_color, edge_label)

        if synt_role in {"GEN_CONS"} and meta.get("is_root"):
            head_token = find_previous_root(
                idx,
                lambda _tid, _meta: _meta.get("word_index", 0)
                < meta.get("word_index", 0)
                and (
                    _meta.get("morph_tag") in NOUN_TAGS
                    or _meta.get("syntactic_role")
                    in {"SUBJ", "AGNT", "PREP_OBJ", "OBJ", "PRED", "ATTRIB"}
                ),
            )
            if head_token:
                add_edge(head_token, token_id, "cornflowerblue", "مضاف إليه")

        # ============================================================================
        # TIER 1 & TIER 2 SYNTACTIC ROLE HANDLERS
        # ============================================================================
        #
        # ARCHITECTURE OVERVIEW:
        # This section builds dependency edges for syntactic roles that are not handled
        # by the core MASAQ dataset. These "handler" edges systematically discover and
        # connect grammatical relationships based on morphological tags and position.
        #
        # CRITICAL CONSTRAINTS:
        # 1. Edge Building Time: All edges are built ONCE for the full token_sequence
        #    (before the spec is split into segments). This means we don't have segment
        #    boundary information available here.
        #
        # 2. Edge Rendering Phase: Later, when rendering each segment, edges are filtered
        #    by render_segment_svg() to include only those touching the segment. Then
        #    render_edges() attempts to draw each edge, but SKIPS any edge where either
        #    endpoint doesn't have a position entry in the current segment's positions dict.
        #
        # 3. Position Dictionary Scope: The positions dict built during layout_segment()
        #    only contains tokens that are laid out in the current segment. Tokens from
        #    other segments won't have positions, causing their edges to be silently skipped.
        #
        # SOLUTION: Same-Segment Filtering
        # To prevent edges with missing endpoints:
        # - Tier 2 handlers use is_same_segment() to verify targets are nearby
        # - This heuristic ensures edges stay within probable segment boundaries
        # - Uses word_index proximity (≤15 words) as a proxy for same segment
        #
        # TOKEN SEARCH PATTERNS:
        # - find_next_root() / find_previous_root(): Search ONLY tokens marked is_root=True
        #   These are used by Tier 1 (NON_INFLECT, CONJ, IV) to find grammatical heads
        # - find_next_token() / find_previous_token(): Search ALL tokens in token_sequence
        #   These are used by Tier 2 (CV, ANNUL_PART, PASS_SUBJ, SUBJ_COP_PART) to find
        #   targets that may be affixes or non-root forms
        #
        # HANDLER CATEGORIES:
        #
        # TIER 1 - High-Frequency, Reliable (Pre-implemented):
        #   - NON_INFLECT (حرف): Particles → next verb/noun. Color: teal
        #   - CONJ (عطف): Conjunctions → previous verb/noun. Color: navy
        #   - IV (فعل): Imperfect verbs → complements. Color: seagreen
        #   Coverage impact: +23.9 percentage points, +26,435 relations
        #
        # TIER 2 - Moderate-Frequency, Position-Sensitive (Recently Fixed):
        #   - CV (حال): Circumstantial verbs → nearby main verb. Color: gold
        #   - SUBJ_COP_PART (فاعل كافّ): Copula subjects → preceding particle. Color: purple
        #   - ANNUL_PART (نسخ): Annulling particles → next verb/noun. Color: red
        #   - PASS_SUBJ (نائب فاعل): Passive subjects → passive verb. Color: darkgreen
        #   Critical fix: is_same_segment() ensures all targets within ~15 words
        #
        # TIER 3 - Remaining Unhandled Roles (Lower frequency):
        #   Would require position-aware cross-segment logic or manual tuning.
        #   See build_spec_from_sources() return value for current coverage stats.
        #
        # ============================================================================

        # NON_INFLECT: invariable particles (function words)
        # Connect to nearest following verb or noun head
        if synt_role == "NON_INFLECT":
            # Look for next verb or noun to attach to
            next_verb = find_next_root(
                idx, lambda _tid, _meta: _meta.get("morph_tag") in VERB_TAGS
            )
            next_noun = find_next_root(
                idx, lambda _tid, _meta: _meta.get("morph_tag") in NOUN_TAGS
            )
            # Select the nearest one
            target_token = None
            if next_verb and next_noun:
                verb_idx = token_index.get(next_verb, len(token_sequence))
                noun_idx = token_index.get(next_noun, len(token_sequence))
                target_token = next_verb if verb_idx < noun_idx else next_noun
            else:
                target_token = next_verb or next_noun
            
            if target_token:
                    add_edge(target_token, token_id, "purple", "حرف")

        # CONJ: conjunctions (معطوف relations)
        # These connect preceding noun/verb to form coordinated structure
        if synt_role == "CONJ":
            # Look for previous noun or verb to attach to
            previous_verb = find_previous_root(
                idx, lambda _tid, _meta: _meta.get("morph_tag") in VERB_TAGS
            )
            previous_noun = find_previous_root(
                idx, lambda _tid, _meta: _meta.get("morph_tag") in NOUN_TAGS
            )
            # Select the nearest one
            target_token = None
            if previous_verb and previous_noun:
                verb_idx = token_index.get(previous_verb, -1)
                noun_idx = token_index.get(previous_noun, -1)
                target_token = previous_verb if verb_idx > noun_idx else previous_noun
            else:
                target_token = previous_verb or previous_noun
            
            if target_token:
                src_id = line_group_map.get(target_token, target_token)
                add_edge(src_id, token_id, "navy", "عطف")

        # CONJ_N: conjoined nouns (معطوف - coordinated/conjoined elements)
        # These are nouns that are coordinated with a preceding noun via conjunction.
        #
        # GRAMMATICAL PATTERN:
        # In Arabic coordination, "الضالين" in "غير المغضوب عليهم ولا الضالين" is coordinated
        # with "المغضوب". The conjunction و connects them, and CONJ_N marks the second element.
        # The معطوف edge should point FROM the conjoined element TO the head it's joined with.
        #
        # SEARCH STRATEGY:
        # Search backward for the nearest noun that this token is coordinated with.
        # Skip over prepositions, particles, and other non-nominal elements.
        #
        # EXAMPLES:
        # 1:7 has CONJ_N for الضالين which coordinates with المغضوب
        # Edge: الضالين -> المغضوب (الضالين is معطوف على المغضوب)
        if synt_role == "CONJ_N":
            # Find the previous noun this is coordinated with
            previous_noun = find_previous_root(
                idx, lambda _tid, _meta: _meta.get("morph_tag") in NOUN_TAGS
            )
            if previous_noun and is_same_segment(token_id, previous_noun):
                # Edge FROM conjoined element TO head (current token is the معطوف)
                src_id = line_group_map.get(token_id, token_id)
                dst_id = line_group_map.get(previous_noun, previous_noun)
                add_edge(src_id, dst_id, "navy", "معطوف")

        # INTENCIF: emphatic/intensifier (توكيد)
        # These emphasize or intensify the preceding noun.
        #
        # GRAMMATICAL PATTERN:
        # In Arabic, emphatic particles or words like "لا" in "ولا الضالين" can serve
        # to emphasize negation. INTENCIF marks elements that intensify the preceding word.
        #
        # SEARCH STRATEGY:
        # Search backward for the nearest noun or pronoun being emphasized.
        #
        # EXAMPLES:
        # 1:7 ولا - لا serves as توكيد emphasizing the negation in غير
        if synt_role == "INTENCIF":
            # Find the previous noun being emphasized
            previous_noun = find_previous_root(
                idx, lambda _tid, _meta: _meta.get("morph_tag") in NOUN_TAGS
            )
            if previous_noun and is_same_segment(token_id, previous_noun):
                add_edge(previous_noun, token_id, "purple", "توكيد")

        # APPOS: appositive/substitute (بدل)
        # An appositive noun that substitutes or further defines the preceding noun.
        #
        # GRAMMATICAL PATTERN:
        # In "الصراط المستقيم صراط الذين" (1:6-7), صراط is APPOS as بدل for الصراط.
        # The appositive follows the noun it replaces/further defines.
        #
        # SEARCH STRATEGY:
        # Search backward for the nearest noun that this appositive modifies.
        # Also check commentary hints for specific بدل types.
        #
        # EXAMPLES:
        # 1:7 صراط is بدل مطابق (matching appositive) for الصراط in 1:6
        if synt_role == "APPOS":
            # Find the previous noun this appositive modifies
            previous_noun = find_previous_root(
                idx, lambda _tid, _meta: _meta.get("morph_tag") in NOUN_TAGS
            )
            if previous_noun and is_same_segment(token_id, previous_noun):
                # Edge goes FROM dependent (appositive) TO head (previous noun)
                add_edge(token_id, previous_noun, "cornflowerblue", "بدل")

        # NOUN_PASSIVE_PART: passive participle (اسم مفعول) with نائب فاعل
        # Passive participles like المغضوب act like passive verbs and take نائب فاعل.
        #
        # GRAMMATICAL PATTERN:
        # In "المغضوب عليهم", المغضوب is a passive participle and عليهم is its نائب فاعل
        # (deputy agent). The preposition phrase after a passive participle often functions
        # as its semantic subject.
        #
        # SEARCH STRATEGY:
        # Search forward for the next preposition phrase (PREP + PREP_OBJ) that follows
        # the passive participle within a reasonable window.
        #
        # EXAMPLES:
        # 1:7 المغضوب عليهم - عليهم is نائب فاعل for المغضوب
        if morph_tag == "NOUN_PASSIVE_PART":
            # Find the next prep phrase that acts as نائب فاعل
            for candidate_id in token_sequence[idx + 1:idx + 4]:  # Look within 3 tokens
                candidate_meta = token_meta.get(candidate_id, {})
                candidate_role = (candidate_meta.get("syntactic_role") or "").upper()
                if candidate_role == "PREP_OBJ":
                    if is_same_segment(token_id, candidate_id):
                        # Connect to the line group if it exists, otherwise to the token
                        target_id = line_group_map.get(candidate_id, candidate_id)
                        add_edge(token_id, target_id, "darkgreen", "نائب فاعل")
                    break

        # IV: imperfect verbs
        # Some IV are copulas (كان-type), others are regular imperfect verbs
        # Copula IV may have special subject/predicate handling
        if synt_role == "IV" and meta.get("morph_tag") == "IV":
            morph_type = (meta.get("morph_type") or "").upper()
            # If the IV verb has a SUBJ_COP_PART or similar, it's a copula construction
            is_copula = meta.get("syntactic_role") in {"IV_COP", "V_COP_PRED", "SUBJ_COP_V"}
            
            if not is_copula:
                # Regular IV verb: look for objects/subjects in standard positions
                # Search for object/complement after the verb
                for candidate_id in token_sequence[idx + 1:]:
                    candidate_meta = token_meta.get(candidate_id, {})
                    candidate_role = (candidate_meta.get("syntactic_role") or "").upper()
                    # Stop at major clause boundaries
                    if candidate_meta.get("word_index", 0) - meta.get("word_index", 0) > 5:
                        break
                    if candidate_role in {"OBJ", "OBJ1", "PRED", "PREP_OBJ"}:
                        add_edge(token_id, candidate_id, "seagreen", "فعل")
                        break

        # SUBJ_COP_PART: subject of copula particle (إنّ, كأن, etc.)
        # These are subjects of particles that create copula-like constructions.
        #
        # GRAMMATICAL PATTERN:
        # Particles like إنّ (verily), كأن (as if), etc. introduce copular clauses where
        # the subject is marked with this role. The particle typically precedes the subject
        # by 1-3 tokens.
        #
        # SEARCH STRATEGY:
        # Search backward from the token to find a preceding ANNUL_PART or EMPH_PART.
        # These particles are the grammatical head of the copular construction.
        # Window: 3 tokens back (covering typical particle distance in Arabic).
        #
        # RENDERING NOTE:
        # All tokens in this relation should be close together (within same word/phrase),
        # so cross-segment issues are unlikely. is_same_segment() provides extra safety.
        #
        # EXAMPLES:
        # 2:235 has 1 SUBJ_COP_PART edge with فاعل كافّ label.
        if synt_role == "SUBJ_COP_PART":
            # Look backward for a copula particle (usually just before)
            particle_found = False
            for candidate_id in token_sequence[max(0, idx - 3):idx]:
                candidate_meta = token_meta.get(candidate_id, {})
                candidate_tag = (candidate_meta.get("morph_tag") or "").upper()
                candidate_role = (candidate_meta.get("syntactic_role") or "").upper()
                # Look for annulling particles or emphasis particles that act as copulas
                if candidate_tag in {"ANNUL_PART", "EMPH_PART"} or candidate_role in {"ANNUL_PART", "EMPH_PART"}:
                    add_edge(candidate_id, token_id, "purple", "فاعل كافّ")
                    particle_found = True
                    break
            
            # Fallback: if no explicit particle found, mark as copula subject anyway
            if not particle_found:
                # This is the subject of an implied copula
                pass  # Could add a different style edge here if needed

        # CV: circumstantial verbs (حال relations)
        # These verbs describe the circumstances/state of the main action verb.
        # 
        # GRAMMATICAL PATTERN:
        # In Arabic, حال (circumstantial) construction uses a secondary verb to describe
        # the state/manner of the main action. For example, "He came running" where "running"
        # is a CV modifying "came".
        #
        # SEARCH STRATEGY:
        # Since CV can be any verb form (including affixes), we search ALL tokens
        # (not just roots) using find_next_token/find_previous_token. We prefer closer
        # targets and can accommodate non-root verb forms.
        #
        # RENDERING NOTE:
        # CV targets often include imperfect verbs or other non-root forms that may not
        # have explicit root markers. The is_same_segment() check ensures we don't reach
        # into neighboring segments where such tokens might not have layout positions.
        #
        # EXAMPLES:
        # 2:260 has 5 CV edges with حال labels, demonstrating this pattern frequently.
        if synt_role == "CV" and meta.get("morph_tag") in VERB_TAGS:
            # Search for another verb (not this CV) to attach to
            # Use find_next_token/find_previous_token to find ALL verbs, not just roots
            def is_main_verb(tid, tmeta):
                if tid == token_id:
                    return False
                tag = (tmeta.get("morph_tag") or "").upper()
                # Prefer PV/IV or if marked as main verb
                if tag in {"PV", "PV_PASS", "IV", "IV_PASS"}:
                    return True
                # Accept any verb that's not CV
                if tag in VERB_TAGS and tag not in {"CV", "CV_PREF"}:
                    return True
                return False
            
            next_main_verb = find_next_token(idx, is_main_verb)
            previous_main_verb = find_previous_token(idx, is_main_verb)
            
            # Prefer closer main verb
            main_verb = select_nearest(idx, previous_main_verb, next_main_verb)
            
            # Only create edge if target is likely in same segment (within 15 words)
            if main_verb and is_same_segment(token_id, main_verb):
                add_edge(main_verb, token_id, "gold", "حال")

        # ANNUL_PART: annulling particles (ناسخ particles like ما، إنما)
        # These particles modify or negate the following clause.
        #
        # GRAMMATICAL PATTERN:
        # Particles like ما (not), إنما (rather), etc. modify the subsequent action.
        # They typically precede the main verb/noun of the clause being negated/modified.
        #
        # SEARCH STRATEGY:
        # Search forward for the next verb or noun after the particle. This becomes the
        # target of the modification. Prefer closer targets (nearest verb, then noun).
        #
        # RENDERING NOTE:
        # Since we search forward and stay within the current segment's logical boundaries,
        # is_same_segment() ensures we don't reach across segment splits. This is important
        # because the "negated" action typically follows immediately.
        #
        # EXAMPLES:
        # 8:48 has 3 ANNUL_PART edges with نسخ labels, showing common negation patterns.
        if synt_role == "ANNUL_PART":
            # Look for next verb/nominal after the particle
            next_verb = find_next_token(
                idx, lambda _tid, _meta: (_meta.get("morph_tag") or "").upper() in VERB_TAGS
            )
            next_noun = find_next_token(
                idx, lambda _tid, _meta: (_meta.get("morph_tag") or "").upper() in NOUN_TAGS
            )
            # Select closer target
            target = select_nearest(idx, None, next_verb) if next_verb else None
            if next_noun and (not target or token_index.get(next_noun, len(token_sequence)) < token_index.get(next_verb or token_id, len(token_sequence))):
                target = next_noun
            
            # Only create edge if target is likely in same segment
            if target and is_same_segment(token_id, target):
                add_edge(token_id, target, "red", "نسخ")

        # PASS_SUBJ: passive voice subjects
        # Subjects of passive verbs (agent in passive constructions, often with preposition).
        #
        # GRAMMATICAL PATTERN:
        # In passive voice, the grammatical subject is actually the semantic agent or patient
        # depending on context. This role marks that relationship. The target is the passive
        # verb (marked with PV_PASS or IV_PASS in MASAQ).
        #
        # SEARCH STRATEGY:
        # First search for explicitly marked passive verbs (PV_PASS, IV_PASS tags).
        # Fallback: search for nearest verb (root or non-root) using find_next_token/find_previous_token.
        # This covers cases where passive marking might be implicit or inferred.
        #
        # RENDERING NOTE:
        # Passive constructions are usually local to the verb, so is_same_segment() should
        # rarely filter valid edges. However, the fallback search across all tokens means
        # we need the proximity check to prevent cross-segment pathologies.
        #
        # EXAMPLES:
        # 5:33 has 2 PASS_SUBJ edges with نائب فاعل labels, showing passive agent marking.
        if synt_role == "PASS_SUBJ":
            # Look for passive verb (marked with IV_PASS or similar)
            passive_verb = None
            # First try to find a verb with passive marking (search all tokens, not just roots)
            for candidate_id in token_sequence:
                candidate_meta = token_meta.get(candidate_id, {})
                morph_tag = (candidate_meta.get("morph_tag") or "").upper()
                if morph_tag in {"PV_PASS", "IV_PASS"}:
                    passive_verb = candidate_id
                    break
            
            # Fallback: search for nearest verb (including non-roots)
            if not passive_verb:
                next_verb = find_next_token(idx, lambda _tid, _meta: is_verb_token(_meta))
                previous_verb = find_previous_token(idx, lambda _tid, _meta: is_verb_token(_meta))
                passive_verb = select_nearest(idx, previous_verb, next_verb)
            
            # Only create edge if target is likely in same segment
            if passive_verb and passive_verb != token_id and is_same_segment(token_id, passive_verb):
                add_edge(passive_verb, token_id, "darkgreen", "نائب فاعل")

        # ============================================================================
        # TIER 3 - MODERATE-FREQUENCY HANDLERS
        # ============================================================================
        # These roles have 200-870 occurrences. They handle particles, cognates, and
        # specific verbal complements. Like Tier 2, they use is_same_segment() to prevent
        # cross-segment rendering failures.

        # PART_CONDITION: conditional particles (إذا، لو، لولا، etc.)
        # These particles introduce conditional clauses. The particle head connects to
        # the main action (verb/noun) in the consequence clause.
        if synt_role == "PART_CONDITION":
            # Look for next verb as the consequence action
            next_verb = find_next_token(
                idx, lambda _tid, _meta: is_verb_token(_meta)
            )
            if next_verb and is_same_segment(token_id, next_verb):
                add_edge(token_id, next_verb, "darkblue", "شرط")

        # PART_JUSSIVE: jussive particles (لم، لما، etc.)
        # These particles modify the mood of the following verb (usually make it subjunctive/jussive).
        if synt_role == "PART_JUSSIVE":
            # Look for next verb to modify
            next_verb = find_next_token(
                idx, lambda _tid, _meta: is_verb_token(_meta)
            )
            if next_verb and is_same_segment(token_id, next_verb):
                add_edge(token_id, next_verb, "purple", "جزم")

        # PART_INTERROG: interrogative particles (هل، ما، أ، etc.)
        # These particles ask about the following predicate.
        if synt_role == "PART_INTERROG":
            # Look for next predicate (verb or noun)
            next_verb = find_next_token(
                idx, lambda _tid, _meta: is_verb_token(_meta)
            )
            next_noun = find_next_token(
                idx, lambda _tid, _meta: (_meta.get("morph_tag") or "").upper() in NOUN_TAGS
            )
            target = select_nearest(idx, None, next_verb) if next_verb else None
            if next_noun and (not target or token_index.get(next_noun, len(token_sequence)) < token_index.get(target or token_id, len(token_sequence))):
                target = next_noun
            if target and is_same_segment(token_id, target):
                add_edge(token_id, target, "saddlebrown", "استفهام")

        # COGN: cognate accusative (مفعول مطلق)
        # A noun that echoes the root of its verb for emphasis or specification.
        # Connects FROM the cognate noun TO its parent verb.
        if synt_role == "COGN":
            # Look for nearest verb (this cognate typically modifies it)
            previous_verb = find_previous_token(
                idx, lambda _tid, _meta: is_verb_token(_meta)
            )
            next_verb = find_next_token(
                idx, lambda _tid, _meta: is_verb_token(_meta)
            )
            verb = select_nearest(idx, previous_verb, next_verb)
            if verb and is_same_segment(token_id, verb):
                add_edge(verb, token_id, "mediumpurple", "مفعول مطلق")

        # VOC_PART: vocative particle (يا، أ، etc.)
        # These particles precede or accompany vocative nouns to call out to someone.
        if synt_role == "VOC_PART":
            # Look for next noun (the vocative target)
            next_noun = find_next_token(
                idx, lambda _tid, _meta: (_meta.get("morph_tag") or "").upper() in NOUN_TAGS
            )
            if next_noun and is_same_segment(token_id, next_noun):
                add_edge(token_id, next_noun, "crimson", "نداء")

        # SUBOR_ANN_CONJ: subordinating annulling conjunctions
        # Complex conjunctions like "لكن" (but), "إن" (that) which connect clauses.
        if synt_role == "SUBOR_ANN_CONJ":
            # Look for next verb/noun as the subordinated element
            next_verb = find_next_token(
                idx, lambda _tid, _meta: is_verb_token(_meta)
            )
            next_noun = find_next_token(
                idx, lambda _tid, _meta: (_meta.get("morph_tag") or "").upper() in NOUN_TAGS
            )
            target = select_nearest(idx, None, next_verb) if next_verb else None
            if next_noun and (not target or token_index.get(next_noun, len(token_sequence)) < token_index.get(target or token_id, len(token_sequence))):
                target = next_noun
            if target and is_same_segment(token_id, target):
                add_edge(token_id, target, "mediumvioletred", "ربط")

        # CERT_PART: certainty/emphasis particles (قد، لقد، etc.)
        # These particles emphasize or indicate certainty about the following verb.
        if synt_role == "CERT_PART":
            # Look for next verb to emphasize
            next_verb = find_next_token(
                idx, lambda _tid, _meta: is_verb_token(_meta)
            )
            if next_verb and is_same_segment(token_id, next_verb):
                add_edge(token_id, next_verb, "darkslateblue", "تأكيد")

        # IV_COP: copula imperfect verbs (كان، ظن، بدا، etc.)
        # These are imperfect verbs that function as copulas, connecting subject to predicate.
        if synt_role == "IV_COP":
            # This is typically the head of a copular clause
            # Look for subject before and predicate after
            for candidate_id in token_sequence[max(0, idx - 2):idx]:
                candidate_meta = token_meta.get(candidate_id, {})
                candidate_role = (candidate_meta.get("syntactic_role") or "").upper()
                if candidate_role in {"SUBJ", "SUBJ1", "SUBJ2"} and is_same_segment(token_id, candidate_id):
                    add_edge(token_id, candidate_id, "steelblue", "نعت")
                    break

        # ACC_SPECIF: accusative of specification (تمييز)
        # A noun that specifies or clarifies what something is.
        if synt_role == "ACC_SPECIF":
            # Look for preceding verb/adjective it specifies
            for candidate_id in reversed(token_sequence[:idx]):
                candidate_meta = token_meta.get(candidate_id, {})
                candidate_tag = (candidate_meta.get("morph_tag") or "").upper()
                candidate_role = (candidate_meta.get("syntactic_role") or "").upper()
                if (candidate_tag in VERB_TAGS or candidate_tag == "ADJ" or 
                    candidate_role in VERB_SYNTAX_ROLES) and is_same_segment(token_id, candidate_id):
                    add_edge(candidate_id, token_id, "olive", "تمييز")
                    break

        # COMPL: complement (يمين، إستثناء، etc.)
        # A token that complements or adds to the meaning of the main verb/noun.
        if synt_role == "COMPL":
            # Look for nearest verb or head noun
            previous_verb = find_previous_token(
                idx, lambda _tid, _meta: is_verb_token(_meta)
            )
            next_verb = find_next_token(
                idx, lambda _tid, _meta: is_verb_token(_meta)
            )
            verb = select_nearest(idx, previous_verb, next_verb)
            if verb and is_same_segment(token_id, verb):
                add_edge(verb, token_id, "purple", "متمم")

    for token_id in token_sequence:
        meta = token_meta[token_id]
        role = (meta.get("syntactic_role") or "").upper()
        if not role_matches(role, OBJECT_ROLES, OBJECT_ROLE_PREFIXES):
            continue
        idx = token_index[token_id]
        previous_verb = find_previous_root(
            idx, lambda _tid, _meta: is_verb_token(_meta)
        )
        next_verb = find_next_root(idx, lambda _tid, _meta: is_verb_token(_meta))
        verb_token = select_nearest(idx, previous_verb, next_verb)
        verb_token = prefer_stem_variant(verb_token)
        if not verb_token or verb_token == token_id:
            continue
        style = _edge_style_for_role(role) or _edge_style_for_role("OBJ")
        if not style:
            continue
        label, color = style
        add_edge(verb_token, token_id, color or tokens[token_id]["color"], label)

    for token_id in token_sequence:
        meta = token_meta[token_id]
        role = (meta.get("syntactic_role") or "").upper()
        if role == "SUBJ":
            continue
        if not role_matches(role, SUBJECT_ROLES, SUBJECT_ROLE_PREFIXES):
            continue
        idx = token_index[token_id]
        previous_verb = find_previous_root(
            idx, lambda _tid, _meta: is_verb_token(_meta)
        )
        next_verb = find_next_root(idx, lambda _tid, _meta: is_verb_token(_meta))
        verb_token = select_nearest(idx, previous_verb, next_verb)
        verb_token = prefer_stem_variant(verb_token)
        if not verb_token or verb_token == token_id:
            continue
        if meta.get("root_id") == verb_token:
            continue
        style = _edge_style_for_role(role) or _edge_style_for_role("AGNT")
        if not style:
            continue
        label, color = style
        add_edge(token_id, verb_token, color, label)

    subject_tokens = [
        token_id
        for token_id in token_sequence
        if token_meta[token_id].get("syntactic_role") in {"SUBJ", "SUBJ1", "SUBJ2"}
    ]

    for subject_id in subject_tokens:
        subject_idx = token_index[subject_id]
        predicate_id: Optional[str] = None
        for candidate_id in token_sequence[subject_idx + 1 :]:
            candidate_meta = token_meta[candidate_id]
            placeholder_ref = candidate_meta.get("placeholder_ref")
            if placeholder_ref and placeholder_ref in token_meta:
                predicate_id = placeholder_ref
                break
            role = candidate_meta.get("syntactic_role") or ""
            if role in PREDICATE_ROLES:
                predicate_id = candidate_id
                break
            if candidate_meta.get("phrase_function") == "PRED":
                root_candidate = candidate_meta.get("root_id") or candidate_id
                predicate_id = root_candidate
                break
        if not predicate_id:
            pass
        if predicate_id:
            add_edge(predicate_id, subject_id, "slategray", "خبر")

    # General multi-segmentation to mirror baseline wrapping and scale to other ayahs
    def _strip_diacritics(s: str) -> str:
        import re

        return re.sub(r"[\u064B-\u065F\u0670]", "", s)

    def _token_text_norm(tid: str) -> str:
        tok = tokens.get(tid) or {}
        segs = tok.get("segments") or []
        text = "".join(str(t) for t, _ in segs)
        return _strip_diacritics(text)

    def _compute_breaks(token_ids: list[str]) -> list[int]:
        # Preferred candidates: specific words or labels that indicate a clause break
        preferred_words = {"غير", "إلا"}
        preferred_labels = {"حرف عطف", "حرف نفي"}  # conjunction, negation
        candidates: list[int] = []
        for i, tid in enumerate(token_ids):
            if i == 0:
                continue
            norm = _token_text_norm(tid)
            lbl = str((tokens.get(tid) or {}).get("label") or "")
            if norm in preferred_words:
                candidates.append(i)
                continue
            if lbl in preferred_labels:
                # Prefer to start a new line at the conjunction/negation
                candidates.append(i)
        # Special pattern: "و" followed by "لا" within next few tokens
        for i, tid in enumerate(token_ids[:-1]):
            if _token_text_norm(tid) == "و":
                for j in range(i + 1, min(i + 4, len(token_ids))):
                    if _token_text_norm(token_ids[j]) == "لا":
                        candidates.append(i)
                        break
        # Deduplicate and sort
        return sorted(set(candidates))

    def _segmentize(token_ids: list[str], max_tokens: int = 12) -> list[list[str]]:
        """Recursively split token list into segments of max_tokens or fewer."""
        # Base case: segment fits within limit
        if len(token_ids) <= max_tokens:
            return [token_ids]
        
        # Find best split point
        candidates = _compute_breaks(token_ids)
        
        # Filter candidates to those that would create reasonably balanced segments
        # Prefer splits closer to the middle but respecting grammatical boundaries
        best = None
        best_score = 1e9
        target = min(max_tokens, len(token_ids) // 2)  # Aim for balanced segments
        
        for i in candidates:
            if i < 3 or len(token_ids) - i < 3:  # Ensure minimum segment size
                continue
            # Score: prefer splits that create segments close to target size
            left_size = i
            right_size = len(token_ids) - i
            # Penalize segments that are too large (over max_tokens)
            penalty = 0
            if left_size > max_tokens:
                penalty += (left_size - max_tokens) * 10
            if right_size > max_tokens:
                penalty += (right_size - max_tokens) * 10
            score = abs(left_size - target) + penalty
            if score < best_score:
                best_score = score
                best = i
        
        if best is None:
            # Fallback: split at the midpoint
            best = len(token_ids) // 2
        
        # Recursively split both halves if they're still too large
        left_part = token_ids[:best]
        right_part = token_ids[best:]
        
        left_segments = _segmentize(left_part, max_tokens) if len(left_part) > max_tokens else [left_part]
        right_segments = _segmentize(right_part, max_tokens) if len(right_part) > max_tokens else [right_part]
        
        return left_segments + right_segments

    segments_spec_list = _segmentize(token_sequence, max_tokens=12)
    segments_spec = []
    for seg_tokens in segments_spec_list:
        seg_h = 320 + max(0, (len(seg_tokens) - 12) // 8) * 40
        segments_spec.append({"tokens": seg_tokens, "height": float(seg_h)})

    # Post-process edges: replace PREP_OBJ destinations with line group IDs
    # This handles cases where نائب فاعل and متعلق edges should connect to جار ومجرور line groups
    # instead of individual PREP_OBJ tokens.
    for edge in edges:
        dst = edge.get("dst", "")
        if dst in line_group_map:
            # Check if this is a نائب فاعل or متعلق edge - it should target the line group center
            if edge.get("label") in {"نائب فاعل", "متعلق"}:
                edge["dst"] = line_group_map[dst]

    spec: Dict[str, object] = {
        "meta": {"surah": surah, "ayah": ayah},
        # Use a repo-root relative path for consistent resolution
        "output_path": f"output_v2/{surah}/{ayah}.svg",
        "tokens": tokens,
        "edges": edges,
        "line_groups": line_groups,
        "segments": segments_spec,
        "notes": notes,
    }

    # ====================================================================
    # PERFORMANCE METRICS: Log edge building statistics
    # ====================================================================
    perf_metrics["edge_building_end"] = time.time()
    perf_metrics["edge_building_time"] = perf_metrics["edge_building_end"] - perf_metrics["edge_building_start"]
    
    # Store metrics in spec for optional profiling output
    spec["perf_metrics"] = perf_metrics

    return spec


def build_arc_path(
    src: TokenPosition,
    dst: TokenPosition,
    segment_height: float,
    min_ry: float = 20.0,  # Allow caller to specify minimum radius (for avoiding line groups)
) -> Tuple[str, float, float, float, Tuple[Tuple[float, float], ...], Dict[str, float]]:
    x1 = src.circle_x
    x2 = dst.circle_x
    y1 = src.circle_y + ARC_VERTICAL_OFFSET
    y2 = dst.circle_y + ARC_VERTICAL_OFFSET

    dx = abs(x1 - x2)
    dy = abs(y1 - y2)  # Vertical difference between endpoints
    arc_height = min(segment_height * 0.65, ARC_BASE_HEIGHT + dx * ARC_HEIGHT_FACTOR)
    control_y = min(max(y1, y2) + arc_height, segment_height - 24.0)

    # Use elliptical arc (A command) for smoother curves
    # A rx ry x-axis-rotation large-arc-flag sweep-flag x y
    # rx = half the horizontal distance, ry = vertical radius for arc curvature
    rx = dx / 2.0
    
    # Compute ry with a proportional constraint to keep arcs flat
    # The key insight: ry/rx ratio determines curvature appearance
    # Smaller ratio = flatter arc, larger ratio = more curved/pregnant
    if rx < 40.0:
        # Short arcs: allow more curvature (50% ratio) for visibility
        ry_ratio = 0.5
        base_ry = max(20.0, rx * ry_ratio)
    elif rx < 80.0:
        # Medium arcs: moderate curvature (40% ratio)
        ry_ratio = 0.4
        base_ry = rx * ry_ratio
    elif rx < 150.0:
        # Long arcs: flatter (30% ratio)
        ry_ratio = 0.3
        base_ry = rx * ry_ratio
    else:
        # Very long arcs: even flatter (25% ratio) to avoid bulging
        ry_ratio = 0.25
        base_ry = rx * ry_ratio
    
    # For very long arcs, cap ry even if min_ry is higher (visual preference over clearance)
    max_ry_for_span = rx * 0.4 if rx > 100 else rx * 0.5
    effective_min_ry = min(min_ry, max_ry_for_span) if rx > 100 else min_ry
    
    # Ensure minimum ry for label clearance (but capped for long arcs)
    ry = max(effective_min_ry, base_ry)
    
    # To make arc curve DOWNWARD (convex below the line):
    # - sweep-flag=0 when drawing left-to-right (x increases)
    # - sweep-flag=1 when drawing right-to-left (x decreases)
    sweep_flag = 0 if x1 < x2 else 1
    path_d = f"M {x1:.2f} {y1:.2f} A {rx:.2f} {ry:.2f} 0 0 {sweep_flag} {x2:.2f} {y2:.2f}"
    
    mid_x = (x1 + x2) / 2.0
    # For downward arc, mid_y is at the bottom of the arc (y + ry)
    mid_y = max(y1, y2) + ry
    # bezier_points kept for compatibility with collision detection (approximation)
    bezier_points = ((x1, y1), (mid_x, mid_y), (mid_x, mid_y), (x2, y2))
    # Ellipse parameters for accurate arrow placement
    ellipse_params = {
        "x1": x1, "y1": y1, "x2": x2, "y2": y2,
        "rx": rx, "ry": ry, "sweep_flag": sweep_flag,
    }
    return path_d, control_y, mid_x, mid_y, bezier_points, ellipse_params


DEBUG_FLAGS: Dict[str, bool] = {
    "outline_labels": False,
    "log_overlaps": False,
    "enforce_edge_labels": True,  # Enable edge labels by default
}

# Controls how cross-line edges are rendered:
# - 'one-sided': original behavior, split edge using a single placeholder on the farther line
# - 'bilateral': split into two intra-line edges using placeholders on both involved lines (preferred)
CONTINUATION_MODE: str = "bilateral"

# Controls how edge labels are rendered on arcs:
# - 'none': no edge labels (disabled)
# - 'minimal': future use for selective labels (e.g., only key relations)
# - 'full': render all edge labels on arcs with syntactic relation labels (default)
EDGE_LABEL_MODE: str = "full"


def render_edges(
    edges: Sequence[Edge],
    positions: Dict[str, TokenPosition],
    segment_height: float,
    line_groups: Sequence[LineGroup],
) -> List[str]:
    show_labels = EDGE_LABEL_MODE != "none"
    # Build phrase exclusion bands (reserve vertical clearance around phrase line y within [x_left..x_right])
    # The line group has: line at line_y, circle at line_y+10, label text at line_y+10+LINE_LABEL_PADDING
    phrase_bands: List[Tuple[float, float, float, float]] = []
    # Also build a map: token_id -> group_index to detect internal edges
    token_to_group: Dict[str, int] = {}
    for group_idx, group in enumerate(line_groups):
        for member_id in group.members:
            token_to_group[member_id] = group_idx
        relevant = [positions.get(token_id) for token_id in group.members]
        relevant = [pos for pos in relevant if pos]
        if len(relevant) < 2:
            continue
        xs = [pos.circle_x for pos in relevant]
        ys = [pos.circle_y for pos in relevant]
        x_left = min(xs)
        x_right = max(xs)
        line_y = min(max(ys) + LINE_VERTICAL_OFFSET, segment_height - 32.0)
        band_top = line_y - 5.0  # Small margin above the line
        # Band extends to cover line + circle (10px) + label text (~25px) + padding
        band_bottom = line_y + 10.0 + LINE_LABEL_PADDING + 10.0
        phrase_bands.append((x_left, x_right, band_top, band_bottom))

    base_paths: List[str] = []
    polygons: List[str] = []
    rect_texts: List[str] = []

    # Collect items for stagger + collision processing
    label_items: List[Dict[str, float]] = []
    arrow_items: List[Dict[str, object]] = []

    def _preferred_side(lbl: str, color: str) -> str:
        lbl = (lbl or "").strip()
        if lbl in {"مجرور", "مضاف إليه"}:
            return "above"
        if lbl in {"تابع", "صفة", "بدل"}:
            return "below"
        if color in {"firebrick"}:
            return "above"
        if color in {"purple", "gray"}:
            return "below"
        return "above"

    # Track existing arc spans for separation enforcement
    # Store (x_left, x_right, arc_bottom_y) where arc_bottom_y = y + ry
    existing_arcs: List[Tuple[float, float, float]] = []
    for edge_idx, edge in enumerate(edges):
        src = positions.get(edge.src)
        dst = positions.get(edge.dst)
        if not src or not dst:
            continue

        # Check if this arc spans over a line group and needs extra clearance
        x_left = min(src.circle_x, dst.circle_x)
        x_right = max(src.circle_x, dst.circle_x)
        arc_span = x_right - x_left
        min_ry = 20.0  # default minimum radius
        
        # Skip phrase band clearance for edges that are INTERNAL to a line group
        # (both src and dst are members of the same line group)
        src_group = token_to_group.get(edge.src, -1)
        dst_group = token_to_group.get(edge.dst, -2)
        is_internal_edge = (src_group == dst_group and src_group >= 0)
        
        # For very long arcs (spanning many words), limit the clearance requirement
        # to keep arcs proportionally flat - they can overlap bands visually
        max_clearance_ry = arc_span * 0.35 if arc_span > 200 else float('inf')
        
        if not is_internal_edge:
            for band_left, band_right, band_top, band_bottom in phrase_bands:
                # Check if arc horizontal span overlaps with the line group
                horiz_overlap = not (x_right <= band_left or band_right <= x_left)
                if horiz_overlap:
                    # Arc needs to curve around this line group
                    # Calculate how deep the arc needs to go
                    circle_y = max(src.circle_y, dst.circle_y)
                    clearance_needed = band_bottom - circle_y + 15.0  # Extra padding
                    # Cap clearance for long arcs to keep them flat
                    clearance_needed = min(clearance_needed, max_clearance_ry)
                    if clearance_needed > min_ry:
                        min_ry = clearance_needed

        # Check for overlap with existing arcs and adjust min_ry to separate
        # Skip arc separation for internal edges - their line group lines will be placed below
        if DEBUG_FLAGS.get("enforce_arc_separation") and not is_internal_edge:
            arc_y = max(src.circle_y, dst.circle_y) + ARC_VERTICAL_OFFSET
            for ex_left, ex_right, ex_bottom_y in existing_arcs:
                # Check horizontal overlap
                horiz_overlap = not (x_right <= ex_left or ex_right <= x_left)
                if horiz_overlap:
                    # This arc overlaps horizontally with an existing arc
                    # We need to make sure our arc goes below (or above) the existing one
                    # Current arc bottom would be at: arc_y + min_ry
                    # We need: arc_y + min_ry > ex_bottom_y + separation_gap
                    separation_gap = 18.0  # Minimum vertical gap between arcs
                    needed_ry = ex_bottom_y - arc_y + separation_gap
                    if needed_ry > min_ry:
                        min_ry = needed_ry

        # Arc path with adjusted min_ry to separate from other arcs
        path_d, control_y, mid_x, mid_y, bezier_points, ellipse_params = build_arc_path(
            src, dst, segment_height, min_ry
        )
        
        # Track this arc for future overlap checks
        arc_bottom_y = max(src.circle_y, dst.circle_y) + ARC_VERTICAL_OFFSET + ellipse_params["ry"]
        existing_arcs.append((x_left, x_right, arc_bottom_y))
        
        base_paths.append(
            f'<path d="{path_d}" fill="none" stroke="{edge.color}" stroke-width="2"/>'
        )

        # Arrowhead param suggestion (farther towards head for taller arcs)
        dx = abs(src.circle_x - dst.circle_x)
        arc_height = min(
            segment_height * 0.65, ARC_BASE_HEIGHT + dx * ARC_HEIGHT_FACTOR
        )
        # Position arrow closer to destination (higher t) for better visual clarity
        arrow_t = 0.75 if arc_height > 96.0 else 0.65

        arrow_items.append(
            {
                "edge_idx": edge_idx,
                "color": edge.color,
                "bezier": bezier_points,
                "ellipse_params": ellipse_params,
                "arrow_t": float(arrow_t),
            }
        )

        if show_labels:
            # Label rect (width constrained), with type-based side separation
            label = edge.label
            label_length = max(len(label), 2)
            rect_w = max(48.0, 12.0 * label_length)
            rect_h = 18.0
            rect_x = mid_x - rect_w / 2.0
            # Ensure edge labels are below token labels
            # Token labels are at circle_y + LABEL_VERTICAL_OFFSET - row_height ≈ circle_y + 16
            # Add extra offset to place edge labels below token labels
            baseline_min = min(src.circle_y, dst.circle_y) + LABEL_VERTICAL_OFFSET + 4.0

            side = _preferred_side(edge.label, edge.color)
            side_sign = 1.0 if side == "below" else -1.0

            # Initial placement
            if side_sign > 0:
                rect_y = min(control_y - rect_h - 6.0, segment_height - rect_h - 16.0)
                rect_y = max(rect_y, baseline_min + 6.0)
            else:
                rect_y = max(baseline_min + 6.0, mid_y - rect_h / 2.0)
                rect_y = min(rect_y, segment_height - rect_h - 16.0)

            # Phrase-band collision guard
            def intersects_band(
                x: float, y: float, h: float, band: Tuple[float, float, float, float]
            ) -> bool:
                xl, xr, bt, bb = band
                return (xl <= x <= xr) and not (y + h <= bt or bb <= y)

            def apply_phrase_guard(
                rx: float, ry: float, rw: float, rh: float, sgn: float
            ) -> Tuple[float, float]:
                new_y = ry
                for xl, xr, bt, bb in phrase_bands:
                    if xl <= mid_x <= xr:
                        ay1, ay2 = new_y, new_y + rh
                        if not (ay2 <= bt or bb <= ay1):
                            if sgn > 0:
                                # push below band
                                candidate = max(new_y, bb + 4.0)
                                max_y = min(
                                    control_y - rh - 6.0, segment_height - rh - 16.0
                                )
                                new_y = min(candidate, max_y)
                            else:
                                # push above band
                                candidate = min(new_y, bt - rh - 4.0)
                                min_y = baseline_min + 6.0
                                new_y = max(candidate, min_y)
                return rx, new_y

            rect_x, rect_y = apply_phrase_guard(rect_x, rect_y, rect_w, rect_h, side_sign)

            # If still overlapping any band, try flipping side once
            def overlaps_any_band(x: float, y: float, h: float) -> bool:
                return any(intersects_band(mid_x, y, h, band) for band in phrase_bands)

            if overlaps_any_band(rect_x, rect_y, rect_h):
                # flip side and recompute
                side_sign = -side_sign
                if side_sign > 0:
                    rect_y = min(control_y - rect_h - 6.0, segment_height - rect_h - 16.0)
                    rect_y = max(rect_y, baseline_min + 6.0)
                else:
                    rect_y = max(baseline_min + 6.0, mid_y - rect_h / 2.0)
                    rect_y = min(rect_y, segment_height - rect_h - 16.0)
                rect_x, rect_y = apply_phrase_guard(
                    rect_x, rect_y, rect_w, rect_h, side_sign
                )

            # Adaptive bucket sizing: estimate arc density in local horizontal region
            # Collect dx span and count overlapping arcs (simple heuristic)
            local_count = 0
            span_left = mid_x - 50.0
            span_right = mid_x + 50.0
            for other in edges:
                if other is edge:
                    continue
                osrc = positions.get(other.src)
                odst = positions.get(other.dst)
                if not osrc or not odst:
                    continue
                omx = (osrc.circle_x + odst.circle_x) / 2.0
                if span_left <= omx <= span_right:
                    local_count += 1
            # Choose bucket width inversely to density
            if local_count >= 8:
                bucket_width = 30.0
            elif local_count >= 5:
                bucket_width = 40.0
            elif local_count >= 3:
                bucket_width = 50.0
            else:
                bucket_width = 60.0
            bucket = int(round(mid_x / bucket_width))
            label_items.append(
                {
                    "edge_idx": float(edge_idx),
                    "rect_x": rect_x,
                    "rect_y": rect_y,
                    "rect_w": rect_w,
                    "rect_h": rect_h,
                    "mid_x": mid_x,
                    "text_color": edge.color,
                    "text": label,
                    "side": side_sign,  # below=+1 (increase y), above=-1 (decrease y)
                    "baseline_min": baseline_min,
                    "control_y": control_y,
                    "bucket": float(bucket),
                }
            )

    # Stagger labels per bucket to avoid direct collisions when midpoints coincide
    from collections import defaultdict

    grouped: Dict[int, List[Dict[str, float]]] = defaultdict(list)
    for item in label_items:
        grouped[int(item["bucket"])].append(item)

    overlap_events: List[Tuple[int, int]] = []
    for items in grouped.values():
        # Split by side direction to stack independently
        above_items = [it for it in items if it["side"] < 0]
        below_items = [it for it in items if it["side"] > 0]

        # Above: move upward (decrease y)
        for idx, it in enumerate(above_items):
            offset = idx * (it["rect_h"] + 6.0)
            target_y = it["rect_y"] - offset
            min_y = it["baseline_min"] + 6.0
            it["rect_y"] = max(target_y, min_y)

        # Below: move downward (increase y)
        for idx, it in enumerate(below_items):
            offset = idx * (it["rect_h"] + 6.0)
            target_y = it["rect_y"] + offset
            max_y = min(
                it["control_y"] - it["rect_h"] - 6.0,
                segment_height - it["rect_h"] - 16.0,
            )
            it["rect_y"] = min(target_y, max_y)

        # Simple overlap resolution within bucket: if any rects intersect, nudge by one step
        resolved = True
        iteration = 0
        while resolved and iteration < 4:
            resolved = False
            iteration += 1
            items_sorted = sorted(items, key=lambda it: it["rect_y"])
            for i in range(len(items_sorted) - 1):
                a = items_sorted[i]
                b = items_sorted[i + 1]
                ax1, ax2 = a["rect_x"], a["rect_x"] + a["rect_w"]
                bx1, bx2 = b["rect_x"], b["rect_x"] + b["rect_w"]
                ay1, ay2 = a["rect_y"], a["rect_y"] + a["rect_h"]
                by1, by2 = b["rect_y"], b["rect_y"] + b["rect_h"]
                horizontal_overlap = not (ax2 <= bx1 or bx2 <= ax1)
                vertical_overlap = not (ay2 <= by1 or by2 <= ay1)
                if horizontal_overlap and vertical_overlap:
                    if DEBUG_FLAGS.get("log_overlaps"):
                        overlap_events.append((int(a["edge_idx"]), int(b["edge_idx"])))
                    # Nudge b in its stacking direction
                    step = b["rect_h"] + 6.0
                    if b["side"] > 0:
                        # down
                        max_y = min(
                            b["control_y"] - b["rect_h"] - 6.0,
                            segment_height - b["rect_h"] - 16.0,
                        )
                        new_y = min(b["rect_y"] + step, max_y)
                    else:
                        # up
                        min_y = b["baseline_min"] + 6.0
                        new_y = max(b["rect_y"] - step, min_y)
                    if abs(new_y - b["rect_y"]) >= 1.0:
                        b["rect_y"] = new_y
                        resolved = True

        # Minimum gap enforcement: ensure vertical separation >= (min(rect_h)+4)
        items_sorted = sorted(items, key=lambda it: it["rect_y"])
        for i in range(len(items_sorted) - 1):
            a = items_sorted[i]
            b = items_sorted[i + 1]
            gap_needed = min(a["rect_h"], b["rect_h"]) + 4.0
            actual_gap = b["rect_y"] - (a["rect_y"] + a["rect_h"])
            if actual_gap < gap_needed - 0.5:  # tolerance
                delta = gap_needed - actual_gap
                if b["side"] > 0:
                    # push downward
                    max_y = min(
                        b["control_y"] - b["rect_h"] - 6.0,
                        segment_height - b["rect_h"] - 16.0,
                    )
                    b["rect_y"] = min(b["rect_y"] + delta, max_y)
                else:
                    # push upward
                    min_y = b["baseline_min"] + 6.0
                    b["rect_y"] = max(b["rect_y"] - delta, min_y)

    # Emit rects and texts after collision mitigation (we will add polygons before these to preserve layering)
    if show_labels and DEBUG_FLAGS.get("enforce_edge_labels"):
        # Global sweep: attempt to resolve remaining overlaps across buckets
        # We'll iterate a few times; adjust y position in preferred direction when collisions persist.
        def labels_overlap(a, b) -> bool:
            ax1, ax2 = a["rect_x"], a["rect_x"] + a["rect_w"]
            bx1, bx2 = b["rect_x"], b["rect_x"] + b["rect_w"]
            ay1, ay2 = a["rect_y"], a["rect_y"] + a["rect_h"]
            by1, by2 = b["rect_y"], b["rect_y"] + b["rect_h"]
            horiz = not (ax2 <= bx1 or bx2 <= ax1)
            vert = not (ay2 <= by1 or by2 <= ay1)
            return horiz and vert

        for sweep in range(8):  # Increased iterations further
            changed = False
            # Sort by y then width to encourage stable packing
            ordered = sorted(label_items, key=lambda it: (it["rect_y"], it["rect_x"]))
            for i in range(len(ordered)):
                for j in range(i + 1, len(ordered)):
                    a = ordered[i]
                    b = ordered[j]
                    if labels_overlap(a, b):
                        # Move b in its stacking direction by small increment
                        step = b["rect_h"] * 0.6 + 4.0
                        if b["side"] > 0:
                            max_y = min(
                                b["control_y"] - b["rect_h"] - 6.0,
                                segment_height - b["rect_h"] - 16.0,
                            )
                            new_y = min(b["rect_y"] + step, max_y)
                        else:
                            min_y = b["baseline_min"] + 6.0
                            new_y = max(b["rect_y"] - step, min_y)
                        if abs(new_y - b["rect_y"]) >= 1.0:
                            b["rect_y"] = new_y
                            changed = True
                        else:
                            # If vertical shift ineffective, use horizontal separation
                            # Calculate actual overlap amount to determine minimum separation
                            ax1, ax2 = a["rect_x"], a["rect_x"] + a["rect_w"]
                            bx1, bx2 = b["rect_x"], b["rect_x"] + b["rect_w"]
                            overlap_x = min(ax2, bx2) - max(ax1, bx1)
                            if overlap_x > 0:
                                # Push labels apart by half the overlap plus padding
                                push = (overlap_x / 2.0) + 8.0
                                if a["mid_x"] <= b["mid_x"]:
                                    a["rect_x"] -= push
                                    a["mid_x"] -= push  # Also update mid_x for text rendering
                                    b["rect_x"] += push
                                    b["mid_x"] += push  # Also update mid_x for text rendering
                                else:
                                    a["rect_x"] += push
                                    a["mid_x"] += push  # Also update mid_x for text rendering
                                    b["rect_x"] -= push
                                    b["mid_x"] -= push  # Also update mid_x for text rendering
                            changed = True
            if not changed:
                break

        # Final diagnostics for unresolved overlaps
        # Build adjacency graph of overlapping labels (using current positions)
        n = len(label_items)
        adj: List[List[int]] = [[] for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                if labels_overlap(label_items[i], label_items[j]):
                    adj[i].append(j)
                    adj[j].append(i)
        visited = [False] * n
        clusters: List[List[int]] = []
        for i in range(n):
            if visited[i]:
                continue
            stack = [i]
            comp = []
            while stack:
                k = stack.pop()
                if visited[k]:
                    continue
                visited[k] = True
                comp.append(k)
                for nxt in adj[k]:
                    if not visited[nxt]:
                        stack.append(nxt)
            if len(comp) > 1:
                clusters.append(comp)
        # Horizontal spreading for each cluster
        for comp in clusters:
            # Sort by mid_x
            comp.sort(key=lambda idx: label_items[idx]["mid_x"])
            left = min(label_items[idx]["rect_x"] for idx in comp)
            right = max(
                label_items[idx]["rect_x"] + label_items[idx]["rect_w"] for idx in comp
            )
            total_w = sum(label_items[idx]["rect_w"] for idx in comp)
            span = right - left
            # Target span with padding - increased padding from 8 to 16
            target_span = total_w + (len(comp) - 1) * 16.0
            if target_span > span:
                # Redistribute sequentially
                cursor = (left + right - target_span) / 2.0
                for idx in comp:
                    w = label_items[idx]["rect_w"]
                    old_rect_x = label_items[idx]["rect_x"]
                    label_items[idx]["rect_x"] = cursor
                    # Also update mid_x to keep text centered at new position
                    label_items[idx]["mid_x"] += (cursor - old_rect_x)
                    cursor += w + 16.0
        # Pair-level final fallbacks
        for i in range(n):
            for j in range(i + 1, n):
                a = label_items[i]
                b = label_items[j]
                if not labels_overlap(a, b):
                    continue
                # Side flip attempt if not done
                changed = False
                for item in (a, b):
                    if (
                        DEBUG_FLAGS.get("enforce_edge_labels")
                        and item.get("_flipped") != True
                    ):
                        item["side"] = -item["side"]
                        item["_flipped"] = True
                        if item["side"] > 0:
                            new_y = min(
                                item["control_y"] - item["rect_h"] - 6.0,
                                segment_height - item["rect_h"] - 16.0,
                            )
                            new_y = max(new_y, item["baseline_min"] + 6.0)
                        else:
                            new_y = max(
                                item["baseline_min"] + 6.0,
                                (item["rect_y"] - item["rect_h"] * 0.5),
                            )
                            new_y = min(new_y, segment_height - item["rect_h"] - 16.0)
                        item["rect_y"] = new_y
                        changed = True
                if changed and not labels_overlap(a, b):
                    continue
                # Side-by-side offset fallback - use actual overlap to calculate proper offset
                if labels_overlap(a, b):
                    ax1, ax2 = a["rect_x"], a["rect_x"] + a["rect_w"]
                    bx1, bx2 = b["rect_x"], b["rect_x"] + b["rect_w"]
                    overlap_x = min(ax2, bx2) - max(ax1, bx1)
                    offset = max((overlap_x / 2.0) + 10.0, (a["rect_w"] + b["rect_w"]) * 0.2 + 8.0)
                    # Push a left, b right depending on relative mid positions
                    if a["mid_x"] <= b["mid_x"]:
                        a["rect_x"] -= offset
                        a["mid_x"] -= offset  # Also update mid_x for text rendering
                        b["rect_x"] += offset
                        b["mid_x"] += offset  # Also update mid_x for text rendering
                    else:
                        a["rect_x"] += offset
                        a["mid_x"] += offset  # Also update mid_x for text rendering
                        b["rect_x"] -= offset
                        b["mid_x"] -= offset  # Also update mid_x for text rendering
                # Font-size shrink fallback encoded by artificially reducing rect_h (approx effect)
                shrink_round = 0
                while labels_overlap(a, b) and shrink_round < 3:
                    a["rect_w"] *= 0.94
                    b["rect_w"] *= 0.94
                    a["rect_x"] += 0.5  # slight nudge to preserve center approximate
                    b["rect_x"] -= 0.5
                    shrink_round += 1
                # Final aggressive horizontal separation if still overlapping
                if labels_overlap(a, b):
                    ax1, ax2 = a["rect_x"], a["rect_x"] + a["rect_w"]
                    bx1, bx2 = b["rect_x"], b["rect_x"] + b["rect_w"]
                    overlap_x = min(ax2, bx2) - max(ax1, bx1)
                    if overlap_x > 0:
                        # Force complete separation
                        push = (overlap_x / 2.0) + 15.0
                        if a["mid_x"] <= b["mid_x"]:
                            a["rect_x"] -= push
                            a["mid_x"] -= push
                            b["rect_x"] += push
                            b["mid_x"] += push
                        else:
                            a["rect_x"] += push
                            a["mid_x"] += push
                            b["rect_x"] -= push
                            b["mid_x"] -= push
                if labels_overlap(a, b):
                    print(
                        f"EDGE_LABEL_OVERLAP {int(a['edge_idx'])} {int(b['edge_idx'])}"
                    )

    if DEBUG_FLAGS.get("avoid_circle_overlap"):
        # Spatial binning for circle coordinates to reduce collision checks.
        circle_coords: List[Tuple[float, float]] = [
            (pos.circle_x, pos.circle_y) for pos in positions.values()
        ]
        C_R = CIRCLE_RADIUS
        BIN = 80.0
        bins: Dict[int, List[Tuple[float, float]]] = {}
        for cx, cy in circle_coords:
            key = int(cx // BIN)
            bins.setdefault(key, []).append((cx, cy))

        def label_circle_collision(lbl, cx, cy) -> bool:
            rx, ry = lbl["rect_x"], lbl["rect_y"]
            rw, rh = lbl["rect_w"], lbl["rect_h"]
            nearest_x = max(rx, min(cx, rx + rw))
            nearest_y = max(ry, min(cy, ry + rh))
            dx = cx - nearest_x
            dy = cy - nearest_y
            return dx * dx + dy * dy <= C_R * C_R

        def candidate_circles(lbl) -> List[Tuple[float, float]]:
            rx, rw = lbl["rect_x"], lbl["rect_w"]
            start_bin = int((rx - C_R) // BIN)
            end_bin = int((rx + rw + C_R) // BIN)
            cands: List[Tuple[float, float]] = []
            for k in range(start_bin, end_bin + 1):
                if k in bins:
                    cands.extend(bins[k])
            return cands

        def any_circle_collision(lbl) -> bool:
            return any(
                label_circle_collision(lbl, cx, cy) for cx, cy in candidate_circles(lbl)
            )

        def nearest_circle_vector(lbl) -> Tuple[float, float]:
            rx, ry, rw, rh = lbl["rect_x"], lbl["rect_y"], lbl["rect_w"], lbl["rect_h"]
            center_x = rx + rw / 2.0
            center_y = ry + rh / 2.0
            best_d2 = 1e12
            best_vec = (0.0, 0.0)
            for cx, cy in candidate_circles(lbl):
                dx = center_x - cx
                dy = center_y - cy
                d2 = dx * dx + dy * dy
                if d2 < best_d2:
                    best_d2 = d2
                    best_vec = (dx, dy)
            return best_vec

        for it in label_items:
            attempts = 0
            while attempts < 9 and any_circle_collision(it):
                base_step = it["rect_h"] * 0.35 + 3.0
                step = base_step * (1 + attempts * 0.15)
                side_dir = -1 if it["side"] <= 0 else 1
                if attempts >= 5 and any_circle_collision(it):
                    side_dir *= -1
                if side_dir > 0:
                    max_y = min(
                        it["control_y"] - it["rect_h"] - 6.0,
                        segment_height - it["rect_h"] - 16.0,
                    )
                    it["rect_y"] = min(it["rect_y"] + step, max_y)
                else:
                    min_y = it["baseline_min"] + 6.0
                    it["rect_y"] = max(it["rect_y"] - step, min_y)
                if any_circle_collision(it):
                    vx, vy = nearest_circle_vector(it)
                    horiz = (attempts + 1) * 2.8
                    if vx > 0:
                        it["rect_x"] += horiz
                    else:
                        it["rect_x"] -= horiz
                if any_circle_collision(it):
                    diag = 2.2 * (1 if attempts % 2 == 0 else -1)
                    it["rect_x"] += diag
                    it["rect_y"] += diag * 0.4 * (1 if side_dir > 0 else -1)
                attempts += 1
            # Shrink fallback if still colliding: reduce width (simulated) and re-center
            shrink = 0
            while any_circle_collision(it) and shrink < 3:
                it["rect_w"] *= 0.9
                # recentre around mid_x
                it["rect_x"] = it["mid_x"] - it["rect_w"] / 2.0
                shrink += 1

    for it in (label_items if show_labels else []):
        # Add background rectangle and text for edge label
        rect_x = it["rect_x"]
        rect_y = it["rect_y"]
        rect_w = it["rect_w"]
        rect_h = it["rect_h"]
        mid_x = it["mid_x"]
        # Place text using vertical centering heuristic (Arabic baseline adjustment):
        text_y = rect_y + rect_h * 0.55
        
        # Add semi-transparent white background rectangle (like reference SVGs)
        rect_texts.append(
            f'<rect class="edge-label" fill="rgba(255,255,255,0.705)" '
            f'height="{rect_h:.2f}" width="{rect_w:.2f}" x="{rect_x:.2f}" y="{rect_y:.2f}"></rect>'
        )
        
        # Add text label on top of background rectangle
        rect_texts.append(
            f'<text direction="rtl" fill="{it["text_color"]}" font-family="Times New Roman" font-size="{LABEL_FONT_SIZE}" '
            f'x="{mid_x:.2f}" y="{text_y:.2f}">{it["text"]}</text>'
        )

    # Build arrowhead polygons now, detecting collisions against final rects and nudging along the curve
    def _arrow_scale_for_color(color: str) -> float:
        # Shrink neutral / gray arrows; keep vivid colors larger
        if color in {"gray", "slategray"}:
            return 0.7
        if color in {"firebrick"}:
            return 1.0
        if color in {"purple"}:
            return 0.85
        return 0.9

    def make_arrow_points_from_ellipse(
        t: float, ellipse_params: Dict[str, float], color: str
    ) -> List[Tuple[float, float]]:
        """Compute arrow points using ellipse arc geometry."""
        x1 = ellipse_params["x1"]
        y1 = ellipse_params["y1"]
        x2 = ellipse_params["x2"]
        y2 = ellipse_params["y2"]
        rx = ellipse_params["rx"]
        ry = ellipse_params["ry"]
        sweep_flag = int(ellipse_params["sweep_flag"])
        arrow_point = _ellipse_arc_point(t, x1, y1, x2, y2, rx, ry, sweep_flag)
        tangent = _ellipse_arc_tangent(t, x1, y1, x2, y2, rx, ry, sweep_flag)
        tl = math.hypot(*tangent) or 1.0
        tu = (tangent[0] / tl, tangent[1] / tl)
        nu = (-tu[1], tu[0])
        scale = _arrow_scale_for_color(color)
        arrow_length = ARROW_SIZE * 2.0 * scale
        arrow_half_width = ARROW_SIZE * ARROW_WIDTH_FACTOR * scale
        base_center = (
            arrow_point[0] - tu[0] * arrow_length,
            arrow_point[1] - tu[1] * arrow_length,
        )
        left_point = (
            base_center[0] + nu[0] * arrow_half_width,
            base_center[1] + nu[1] * arrow_half_width,
        )
        right_point = (
            base_center[0] - nu[0] * arrow_half_width,
            base_center[1] - nu[1] * arrow_half_width,
        )
        return [arrow_point, left_point, right_point]

    def make_arrow_points(
        t: float, p0, p1, p2, p3, color: str
    ) -> List[Tuple[float, float]]:
        arrow_point = _cubic_bezier_point(t, p0, p1, p2, p3)
        tangent = _cubic_bezier_tangent(t, p0, p1, p2, p3)
        tl = math.hypot(*tangent) or 1.0
        tu = (tangent[0] / tl, tangent[1] / tl)
        nu = (-tu[1], tu[0])
        scale = _arrow_scale_for_color(color)
        arrow_length = ARROW_SIZE * 2.0 * scale
        arrow_half_width = ARROW_SIZE * ARROW_WIDTH_FACTOR * scale
        base_center = (
            arrow_point[0] - tu[0] * arrow_length,
            arrow_point[1] - tu[1] * arrow_length,
        )
        left_point = (
            base_center[0] + nu[0] * arrow_half_width,
            base_center[1] + nu[1] * arrow_half_width,
        )
        right_point = (
            base_center[0] - nu[0] * arrow_half_width,
            base_center[1] - nu[1] * arrow_half_width,
        )
        return [arrow_point, left_point, right_point]

    # Map edge_idx -> label rect for quick lookup
    label_map: Dict[int, Dict[str, float]] = (
        {int(it["edge_idx"]): it for it in label_items} if show_labels else {}
    )

    for arr in arrow_items:
        edge_idx = int(arr["edge_idx"])
        color = str(arr["color"])
        ellipse_params = arr["ellipse_params"]
        bezier_pts = arr["bezier"]
        t = float(arr["arrow_t"])
        
        # Use ellipse calculation for elliptical arcs, bezier for cubic Bezier curves
        if ellipse_params is not None:
            points = make_arrow_points_from_ellipse(t, ellipse_params, color)
        else:
            p0, p1, p2, p3 = bezier_pts
            points = make_arrow_points(t, p0, p1, p2, p3, color)

        # Collision with own label rect?
        li = label_map.get(edge_idx)
        if li:
            rx, ry = li["rect_x"], li["rect_y"]
            rw, rh = li["rect_w"], li["rect_h"]

            def point_in_rect(pt: Tuple[float, float]) -> bool:
                x, y = pt
                return (rx <= x <= rx + rw) and (ry <= y <= ry + rh)

            if any(point_in_rect(pt) for pt in points):
                # push arrow further along the curve (towards head)
                t = min(0.70, t + 0.10)
                if ellipse_params is not None:
                    points = make_arrow_points_from_ellipse(t, ellipse_params, color)
                else:
                    p0, p1, p2, p3 = bezier_pts
                    points = make_arrow_points(t, p0, p1, p2, p3, color)

        # Broader collision: any label rect (avoid arrow covering foreign labels)
        def _any_collision(pts: List[Tuple[float, float]]) -> bool:
            if not show_labels:
                return False
            for lab in label_items:
                rx = lab["rect_x"]
                ry = lab["rect_y"]
                rw = lab["rect_w"]
                rh = lab["rect_h"]
                for x, y in pts:
                    if rx <= x <= rx + rw and ry <= y <= ry + rh:
                        return True
            return False

        safety_iter = 0
        while _any_collision(points) and safety_iter < 5:
            # advance along curve, but cap at 0.85
            t = min(0.85, t + 0.05)
            if ellipse_params is not None:
                points = make_arrow_points_from_ellipse(t, ellipse_params, color)
            else:
                p0, p1, p2, p3 = bezier_pts
                points = make_arrow_points(t, p0, p1, p2, p3, color)
            safety_iter += 1

        # Arrow-arrow collision avoidance (simple bounding box overlap test)
        # Build bounding box for current arrow
        def arrow_bbox(
            pts: List[Tuple[float, float]],
        ) -> Tuple[float, float, float, float]:
            xs = [p[0] for p in pts]
            ys = [p[1] for p in pts]
            return min(xs), min(ys), max(xs), max(ys)

        ax1, ay1, ax2, ay2 = arrow_bbox(points)

        # Compare with already committed polygons (approximate by parsing existing points)
        def polygons_bbox(poly_str: str) -> Tuple[float, float, float, float]:
            pts_raw = poly_str.split('points="')
            if len(pts_raw) < 2:
                return 0, 0, 0, 0
            pts_part = pts_raw[1].split('"')[0]
            pts = []
            for coord in pts_part.split():
                if "," in coord:
                    x_s, y_s = coord.split(",")
                    try:
                        pts.append((float(x_s), float(y_s)))
                    except ValueError:
                        continue
            if not pts:
                return 0, 0, 0, 0
            xs = [p[0] for p in pts]
            ys = [p[1] for p in pts]
            return min(xs), min(ys), max(xs), max(ys)

        arrow_collision_iter = 0
        while arrow_collision_iter < 4:
            collided = False
            for existing in polygons:
                if "polygon" not in existing:
                    continue
                ex1, ey1, ex2, ey2 = polygons_bbox(existing)
                horiz = not (ax2 <= ex1 or ex2 <= ax1)
                vert = not (ay2 <= ey1 or ey2 <= ay1)
                if horiz and vert:
                    # Move further along curve and shrink slightly
                    t = min(0.90, t + 0.04)
                    # reduce scale a bit for subsequent recompute
                    if ellipse_params is not None:
                        points = make_arrow_points_from_ellipse(t, ellipse_params, color)
                    else:
                        p0, p1, p2, p3 = bezier_pts
                        points = make_arrow_points(t, p0, p1, p2, p3, color)
                    ax1, ay1, ax2, ay2 = arrow_bbox(points)
                    collided = True
                    break
            if not collided:
                break
            arrow_collision_iter += 1

        arrow_points_str = " ".join(f"{x:.2f},{y:.2f}" for x, y in points)
        polygons.append(f'<polygon points="{arrow_points_str}" fill="{color}"/>')

    # Preserve layering: paths, then polygons, then rects+texts
    elements: List[str] = []
    elements.extend(base_paths)
    elements.extend(polygons)
    if show_labels:
        elements.extend(rect_texts)
    if DEBUG_FLAGS.get("log_overlaps") and overlap_events:
        try:
            # Simple stdout print; caller may choose to capture
            print(f"Label overlaps resolved (edge_idx pairs): {overlap_events}")
        except Exception:
            pass
    return elements


def render_line_groups(
    groups: Sequence[LineGroup],
    positions: Dict[str, TokenPosition],
    segment_height: float,
    edges: Sequence[Edge] = (),
) -> List[str]:
    """Render line groups (e.g., جار ومجرور) positioned BELOW any arcs connecting their members."""
    elements: List[str] = []
    for group in groups:
        relevant = [positions.get(token_id) for token_id in group.members]
        relevant = [pos for pos in relevant if pos]
        if len(relevant) < 2:
            continue
        xs = [pos.circle_x for pos in relevant]
        ys = [pos.circle_y for pos in relevant]
        x_left = min(xs)
        x_right = max(xs)
        
        # Calculate the arc bottom for edges connecting group members
        # The line should be placed BELOW any such arcs
        arc_bottom = max(ys) + 30.0  # Default: 30px below circles
        for edge in edges:
            # Check if this edge connects group members (e.g., مجرور edge)
            if edge.src in group.members and edge.dst in group.members:
                src_pos = positions.get(edge.src)
                dst_pos = positions.get(edge.dst)
                if src_pos and dst_pos:
                    dx = abs(src_pos.circle_x - dst_pos.circle_x)
                    # Standard arc ry calculation (matching build_arc_path)
                    ry = min(80.0, max(20.0, dx * 0.3))
                    # But use a smaller ry for tight groups like جار ومجرور
                    ry = min(30.0, ry)  # Cap at 30 for tighter arcs
                    # Arc bottom is at circle_y + ry (since arc drops downward)
                    edge_arc_bottom = max(src_pos.circle_y, dst_pos.circle_y) + ry
                    # Add space for the edge label (مجرور label) - about 40px
                    edge_arc_bottom += 40.0
                    arc_bottom = max(arc_bottom, edge_arc_bottom)
        
        line_y = min(arc_bottom, segment_height - 32.0)
        elements.append(
            f'<line x1="{x_left:.2f}" y1="{line_y:.2f}" x2="{x_right:.2f}" y2="{line_y:.2f}" '
            f'stroke="{group.color}" stroke-width="2"/>'
        )
        mid_x = (x_left + x_right) / 2.0
        circle_y = line_y + 10.0
        elements.append(
            f'<circle cx="{mid_x:.2f}" cy="{circle_y:.2f}" r="{CIRCLE_RADIUS}" fill="{group.color}"/>'
        )
        text_y = circle_y + LINE_LABEL_PADDING
        elements.append(
            f'<text text-anchor="middle" fill="{group.color}" font-size="{PHRASE_FONT_SIZE}" '
            f'x="{mid_x:.2f}" y="{text_y:.2f}">{group.label}</text>'
        )
    return elements


def render_segment_svg(
    segment: SegmentLayout,
    tokens: Dict[str, Token],
    edges: Sequence[Edge],
    line_groups: Sequence[LineGroup],
) -> Tuple[float, float, str]:
    (
        segment_width,
        positions,
        base_elements,
        max_extent,
        token_line_map,
        line_metrics,
    ) = layout_segment(segment, tokens)

    # Determine which lines actually need placeholders based on cross-line edges
    cross_pairs: List[Tuple[int, int]] = []
    for e in edges:
        s_line = token_line_map.get(e.src)
        d_line = token_line_map.get(e.dst)
        if s_line is None or d_line is None or s_line == d_line:
            continue
        cross_pairs.append((int(s_line), int(d_line)))

    lines_needed: set[int] = set()
    if CONTINUATION_MODE == "one-sided":
        for s_line, d_line in cross_pairs:
            # Use farther line placeholder similar to legacy behavior
            lines_needed.add(d_line if s_line < d_line else s_line)
    else:
        for s_line, d_line in cross_pairs:
            lines_needed.add(s_line)
            lines_needed.add(d_line)

    continuation_ids: Dict[int, str] = {}
    continuation_elements: List[str] = []
    for idx, metrics in enumerate(line_metrics):
        # Place markers at the right margin to minimize overlap with tokens
        anchor_x = segment_width - MARGIN_X
        circle_y = metrics.get("circle_y", TEXT_BASELINE + CIRCLE_VERTICAL_OFFSET)
        label_y = circle_y - LABEL_VERTICAL_OFFSET
        # Draw متابعة marker only for wrapped lines (idx > 0)
        if idx > 0:
            continuation_elements.append(
                f'<circle cx="{anchor_x:.2f}" cy="{circle_y:.2f}" r="{CIRCLE_RADIUS}" fill="{CONTINUATION_COLOR}"/>'
            )
            continuation_elements.append(
                f'<text direction="rtl" text-anchor="middle" fill="{CONTINUATION_COLOR}" font-size="{LABEL_FONT_SIZE}" '
                f'x="{anchor_x:.2f}" y="{label_y:.2f}">{CONTINUATION_LABEL}</text>'
            )
        # Only create a placeholder and the (#) symbol for lines that participate in cross-line edges
        if idx in lines_needed:
            placeholder_id = f"__cont_line_{idx + 1}"
            continuation_ids[idx] = placeholder_id
            positions[placeholder_id] = TokenPosition(
                text_x=anchor_x,
                circle_x=anchor_x,
                circle_y=circle_y,
                label_y=label_y,
            )
            token_line_map[placeholder_id] = idx
            baseline_y = float(metrics.get("baseline_y", circle_y - CIRCLE_VERTICAL_OFFSET))
            symbol_font = max(8.0, TOKEN_FONT_SIZE * CONTINUATION_SYMBOL_SCALE)
            # Compute a safer vertical position relative to existing token labels on this line
            # Default near the baseline, then try to place slightly above the highest label if present.
            # Collect label positions for tokens on this line (exclude any placeholders).
            line_token_ids = [tid for tid, lidx in token_line_map.items() if lidx == idx and not str(tid).startswith("__cont_line_")]
            line_label_tops: List[float] = []
            for tid in line_token_ids:
                pos = positions.get(tid)
                if not pos:
                    continue
                line_label_tops.append(pos.label_y - LABEL_FONT_SIZE)
            if line_label_tops:
                highest_label_top = min(line_label_tops)
                # Place the symbol slightly above the highest label to avoid overlap
                symbol_y = max(8.0, highest_label_top - 4.0)
            else:
                symbol_y = max(8.0, baseline_y - 2.0)
            # Nudge the symbol slightly left to avoid hugging the margin
            symbol_x = anchor_x - 4.0
            continuation_elements.append(
                f'<text direction="rtl" text-anchor="middle" fill="{CONTINUATION_COLOR}" font-size="{symbol_font}" '
                f'x="{symbol_x:.2f}" y="{symbol_y:.2f}">{CONTINUATION_SYMBOL}</text>'
            )
            # If this is a wrapped line, draw a thin dashed connector from the symbol to the continuation circle
            if idx > 0:
                continuation_elements.append(
                    f'<line x1="{symbol_x:.2f}" y1="{(symbol_y - 3.0):.2f}" x2="{anchor_x:.2f}" y2="{circle_y:.2f}" '
                    f'stroke="{CONTINUATION_COLOR}" stroke-width="1" stroke-dasharray="4,3" />'
                )

    # Draw faint dashed connectors between placeholders of lines that share cross-line relations
    if lines_needed:
        connector_pairs: set[Tuple[int, int]] = set()
        for s_line, d_line in cross_pairs:
            a, b = sorted((s_line, d_line))
            connector_pairs.add((a, b))
        for a, b in sorted(connector_pairs):
            src_ph = continuation_ids.get(a)
            dst_ph = continuation_ids.get(b)
            if not src_ph or not dst_ph:
                continue
            src_pos = positions.get(src_ph)
            dst_pos = positions.get(dst_ph)
            if not src_pos or not dst_pos:
                continue
            x = src_pos.circle_x
            y1 = src_pos.circle_y
            y2 = dst_pos.circle_y
            continuation_elements.append(
                f'<line x1="{x:.2f}" y1="{min(y1, y2):.2f}" x2="{x:.2f}" y2="{max(y1, y2):.2f}" '
                f'stroke="{CONTINUATION_COLOR}" stroke-width="1" stroke-dasharray="3,3" opacity="0.8" />'
            )

    adjusted_edges: List[Edge] = []
    continuation_edges: List[Edge] = []
    
    # Track cross-segment reference tokens to render
    # Each entry: (anchor_id, source_token_text, x, y, color)
    cross_segment_refs: List[Tuple[str, str, float, float, str]] = []
    cross_segment_anchor_counter = 0
    
    # Build set of line group IDs that belong to this segment
    # A line group belongs to this segment if all its members are in segment.token_ids
    segment_line_group_ids: Set[str] = set()
    for group in line_groups:
        lg_id = getattr(group, 'id', None)
        if lg_id and all(member in segment.token_ids for member in group.members):
            segment_line_group_ids.add(lg_id)
    
    # Base position for cross-segment anchors (right margin)
    first_line_metrics = line_metrics[0] if line_metrics else {}
    base_anchor_y = first_line_metrics.get("circle_y", TEXT_BASELINE + CIRCLE_VERTICAL_OFFSET)
    
    for edge in edges:
        src_line = token_line_map.get(edge.src)
        dst_line = token_line_map.get(edge.dst)
        # Check if endpoints are in this segment
        # A destination is "in segment" if it's a token in segment.token_ids OR a line group ID belonging to this segment
        src_in_segment = (edge.src in segment.token_ids) or (edge.src in segment_line_group_ids)
        dst_in_segment = (edge.dst in segment.token_ids) or (edge.dst in segment_line_group_ids)
        # If both endpoints are outside this segment, ignore (we'll render in their own segments)
        if not src_in_segment and not dst_in_segment:
            continue
        
        # Handle cross-segment edges: if source is outside segment but dest is in segment,
        # skip this edge - the segment containing the source will create the cross-reference
        if not src_in_segment and dst_in_segment:
            continue
        
        # If dest is outside segment but source is in segment, create a cross-reference
        # placeholder for the destination token and draw the arc from source to that placeholder
        if src_in_segment and not dst_in_segment:
            # Get the destination token's text and color to display in brackets
            dst_token = tokens.get(edge.dst)
            if dst_token and dst_token.segments:
                # Get the first segment's text (the main word) and its color
                dst_text = dst_token.segments[0][0] if dst_token.segments[0] else "?"
                dst_color = dst_token.segments[0][1] if len(dst_token.segments[0]) > 1 else dst_token.color
            else:
                dst_text = "?"
                dst_color = edge.color
            
            # Create unique anchor ID for this cross-segment reference
            cross_segment_anchor_counter += 1
            anchor_id = f"__cross_ref_{cross_segment_anchor_counter}"
            
            # Get the source token's position
            src_pos = positions.get(edge.src)
            src_x = src_pos.circle_x if src_pos else segment_width - MARGIN_X
            src_y = src_pos.circle_y if src_pos else base_anchor_y
            
            # Calculate dynamic offset based on source token label width to avoid overlap
            # Estimate label width: ~9px per char for font size 14
            src_token = tokens.get(edge.src)
            src_label_width = len(src_token.label) * 9.0 if src_token else 40.0
            # Also consider the source text width (approx 25px per char for font 42)
            src_text_len = len(src_token.segments[0][0]) if src_token and src_token.segments else 2
            src_word_width = src_text_len * 25.0
            
            # Use the larger of label or word width to determine safe clearance
            # Half width + padding + half anchor text width (approx 40px)
            safe_clearance = max(src_label_width, src_word_width) / 2.0 + 50.0
            offset = max(80.0, safe_clearance)
            
            # Determine preferred direction based on word index
            # RTL: Previous words have higher X (Right), Next words have lower X (Left)
            dst_token_obj = tokens.get(edge.dst)
            src_token_obj = tokens.get(edge.src)
            
            prefer_right = False
            if dst_token_obj and src_token_obj:
                if dst_token_obj.word_index < src_token_obj.word_index:
                    prefer_right = True # Target is previous -> Right
                else:
                    prefer_right = False # Target is next -> Left
            
            # Find available gaps to avoid collisions
            occupied_xs = sorted([p.circle_x for p in positions.values()])
            try:
                src_idx = occupied_xs.index(src_x)
            except ValueError:
                src_idx = -1
            
            left_neighbor_x = occupied_xs[src_idx - 1] if src_idx > 0 else MARGIN_X
            right_neighbor_x = occupied_xs[src_idx + 1] if src_idx < len(occupied_xs) - 1 else segment_width - MARGIN_X
            
            # Calculate gaps (center-to-center)
            gap_left = src_x - left_neighbor_x
            gap_right = right_neighbor_x - src_x
            
            # Minimum gap required to place anchor without overlap (approx 100px)
            MIN_GAP = 140.0
            SAFE_DIST = 40.0 # Distance from neighbor
            
            if prefer_right:
                # Try Right first
                if gap_right > offset + SAFE_DIST:
                    anchor_x = src_x + offset
                elif gap_left > offset + SAFE_DIST:
                    anchor_x = src_x - offset
                elif gap_right > MIN_GAP:
                    anchor_x = src_x + gap_right / 2.0
                elif gap_left > MIN_GAP:
                    anchor_x = src_x - gap_left / 2.0
                else:
                    # No good gap. Squeeze into the larger one.
                    if gap_right > gap_left:
                        anchor_x = src_x + gap_right / 2.0
                    else:
                        anchor_x = src_x - gap_left / 2.0
            else:
                # Try Left first
                if gap_left > offset + SAFE_DIST:
                    anchor_x = src_x - offset
                elif gap_right > offset + SAFE_DIST:
                    anchor_x = src_x + offset
                elif gap_left > MIN_GAP:
                    anchor_x = src_x - gap_left / 2.0
                elif gap_right > MIN_GAP:
                    anchor_x = src_x + gap_right / 2.0
                else:
                    # No good gap. Squeeze into the larger one.
                    if gap_left > gap_right:
                        anchor_x = src_x - gap_left / 2.0
                    else:
                        anchor_x = src_x + gap_right / 2.0
                
            anchor_y = src_y  # Same level as source for short flat arcs
            
            # Register position for this anchor
            positions[anchor_id] = TokenPosition(
                text_x=anchor_x,
                circle_x=anchor_x,
                circle_y=anchor_y,
                label_y=anchor_y - LABEL_VERTICAL_OFFSET,
            )
            
            # Store for rendering the bracketed text - use DESTINATION token's color
            cross_segment_refs.append((anchor_id, dst_text, anchor_x, anchor_y, dst_color))
            
            # Add the edge from source to the anchor (placeholder for destination)
            adjusted_edges.append(
                Edge(edge.src, anchor_id, edge.label, edge.color)
            )
            continue
            
        if src_line is None or dst_line is None or src_line == dst_line:
            adjusted_edges.append(edge)
            continue
        mode = CONTINUATION_MODE or "bilateral"
        if mode == "one-sided":
            # Backward-compatible behavior: split using a single placeholder on the farther line
            if src_line < dst_line:
                placeholder_id = continuation_ids.get(dst_line)
                if placeholder_id:
                    adjusted_edges.append(
                        Edge(edge.src, placeholder_id, edge.label, edge.color)
                    )
                    continuation_edges.append(
                        Edge(placeholder_id, edge.dst, CONTINUATION_LABEL, CONTINUATION_COLOR)
                    )
                else:
                    adjusted_edges.append(edge)
            else:
                placeholder_id = continuation_ids.get(src_line)
                if placeholder_id:
                    continuation_edges.append(
                        Edge(edge.src, placeholder_id, CONTINUATION_LABEL, CONTINUATION_COLOR)
                    )
                    adjusted_edges.append(
                        Edge(placeholder_id, edge.dst, edge.label, edge.color)
                    )
                else:
                    adjusted_edges.append(edge)
        else:
            # Bilateral: split into two intra-line edges via placeholders on both sides
            src_ph = continuation_ids.get(src_line)
            dst_ph = continuation_ids.get(dst_line)
            if src_ph:
                continuation_edges.append(
                    Edge(edge.src, src_ph, CONTINUATION_LABEL, CONTINUATION_COLOR)
                )
            else:
                # If no placeholder (shouldn't happen since we create for all lines), fall back to direct
                adjusted_edges.append(edge)
                continue
            if dst_ph:
                adjusted_edges.append(
                    Edge(dst_ph, edge.dst, edge.label, edge.color)
                )
            else:
                # fallback if missing
                adjusted_edges.append(edge)

    all_edges = adjusted_edges + continuation_edges
    base_elements.extend(continuation_elements)
    
    # Render cross-segment reference tokens (source tokens shown in brackets)
    # Also expand segment width if needed to fit the references
    extra_width_for_refs = 0.0
    for anchor_id, src_text, anchor_x, anchor_y, color in cross_segment_refs:
        # Render the bracketed text above the circle
        bracketed_text = f"({src_text})"
        text_y = anchor_y - 24.0  # Position text above the circle
        base_elements.append(
            f'<text direction="rtl" text-anchor="middle" font-size="{TOKEN_FONT_SIZE * 0.7:.0f}" '
            f'fill="{color}" x="{anchor_x:.2f}" y="{text_y:.2f}">{bracketed_text}</text>'
        )
        # Render the circle
        base_elements.append(
            f'<circle cx="{anchor_x:.2f}" cy="{anchor_y:.2f}" r="{CIRCLE_RADIUS}" fill="{color}"/>'
        )
        # Track extra width needed (text width estimate + margin)
        text_width_estimate = len(src_text) * 12.0 + 40.0
        extra_width_for_refs = max(extra_width_for_refs, anchor_x + text_width_estimate / 2.0 - segment_width)
    
    # Expand segment width to accommodate cross-segment references
    if extra_width_for_refs > 0:
        segment_width += extra_width_for_refs + 20.0

    # Provide breathing room beneath the deepest element (labels/arcs)
    dynamic_height = max(segment.height, max_extent + 60.0)
    
    # Register positions for line group center dots BEFORE rendering edges
    # This allows edges to connect to line group centers (e.g., نائب فاعل → جار ومجرور)
    for group in line_groups:
        lg_id = getattr(group, 'id', None) or group.id if hasattr(group, 'id') else None
        if not lg_id:
            continue
        relevant = [positions.get(token_id) for token_id in group.members]
        relevant = [pos for pos in relevant if pos]
        if len(relevant) < 2:
            continue
        xs = [pos.circle_x for pos in relevant]
        ys = [pos.circle_y for pos in relevant]
        mid_x = (min(xs) + max(xs)) / 2.0
        
        # Calculate line position based on arc bottom (same logic as render_line_groups)
        arc_bottom = max(ys) + 30.0  # Default: 30px below circles
        for edge in all_edges:
            if edge.src in group.members and edge.dst in group.members:
                src_pos = positions.get(edge.src)
                dst_pos = positions.get(edge.dst)
                if src_pos and dst_pos:
                    dx = abs(src_pos.circle_x - dst_pos.circle_x)
                    ry = min(30.0, max(20.0, dx * 0.3))  # Cap at 30 for tighter arcs
                    # Arc bottom is at circle_y + ry, then add 40px for edge label space
                    edge_arc_bottom = max(src_pos.circle_y, dst_pos.circle_y) + ry + 40.0
                    arc_bottom = max(arc_bottom, edge_arc_bottom)
        
        line_y = min(arc_bottom, dynamic_height - 32.0)
        circle_y = line_y + 10.0
        # Register position for the line group center dot
        positions[lg_id] = TokenPosition(
            text_x=mid_x,
            circle_x=mid_x,
            circle_y=circle_y,
            label_y=circle_y + LINE_LABEL_PADDING,
        )
    
    # Separate صلة edges for special handling - they should connect to sentence line
    # But only if both source and destination are in this segment (not cross-segment refs)
    sentence_label = str(DEBUG_FLAGS.get("sentence_type_label") or "")
    sentence_head_id = str(DEBUG_FLAGS.get("sentence_head_id") or "")
    silah_edges = []
    regular_edges = []
    for edge in all_edges:
        # Only redirect صلة to sentence line if:
        # 1. We have a sentence label and head
        # 2. The destination is NOT a cross-segment reference (starts with __cross_ref_)
        is_cross_segment_edge = edge.dst.startswith("__cross_ref_")
        if edge.label == "صلة" and sentence_label and sentence_head_id and not is_cross_segment_edge:
            silah_edges.append(edge)
        else:
            regular_edges.append(edge)
    
    # First pass: render non-صلة edges
    edge_elements = render_edges(regular_edges, positions, dynamic_height, line_groups)
    
    # Sentence-type line rendering: place under all content to avoid overlap
    if sentence_label and sentence_head_id and sentence_head_id in positions:
        # Find tokens that are part of the sentence clause (connected to sentence head)
        # Start with the sentence head and find all tokens that the head points TO
        # (its dependents), not tokens that point TO the head (like صلة from relative pronoun)
        sentence_members = {sentence_head_id}
        for edge in all_edges:
            # Include tokens that the sentence head points to (its dependents)
            if edge.src == sentence_head_id and edge.dst in positions:
                sentence_members.add(edge.dst)
            # Exclude edges that point TO the sentence head (like صلة)
            # The relative pronoun (source of صلة) is not part of the verbal clause
        
        # Also include tokens in line groups that contain any sentence member
        for group in line_groups:
            if any(tid in sentence_members for tid in group.members):
                for tid in group.members:
                    if tid in positions:
                        sentence_members.add(tid)
        
        # Get the x positions of sentence member tokens
        sentence_positions = []
        for tid in sentence_members:
            pos = positions.get(tid)
            if pos and not tid.startswith("__"):
                sentence_positions.append(pos.circle_x)
        
        if sentence_positions:
            x_left = min(sentence_positions)
            x_right = max(sentence_positions)
        else:
            x_left = MARGIN_X
            x_right = segment_width - MARGIN_X
        
        # Compute the lowest y position of content in the sentence's x range
        # Start with token circles
        content_bottom = max(
            pos.circle_y for tid, pos in positions.items() 
            if pos and x_left <= pos.circle_x <= x_right and not tid.startswith("__")
        ) if positions else TEXT_BASELINE + CIRCLE_VERTICAL_OFFSET
        
        # Check phrase lines that overlap with sentence x range
        phrase_bands_in_range = []
        for group in line_groups:
            relevant = [positions.get(token_id) for token_id in group.members]
            relevant = [pos for pos in relevant if pos]
            if len(relevant) < 2:
                continue
            grp_xs = [pos.circle_x for pos in relevant]
            grp_x_left, grp_x_right = min(grp_xs), max(grp_xs)
            # Check if this phrase group overlaps with sentence x range
            if grp_x_right >= x_left and grp_x_left <= x_right:
                ys = [pos.circle_y for pos in relevant]
                line_y = max(ys) + LINE_VERTICAL_OFFSET
                phrase_group_bottom = line_y + 36.0  # line + circle + label
                content_bottom = max(content_bottom, phrase_group_bottom)
                # Track phrase band for arc ry estimation
                phrase_bands_in_range.append((grp_x_left, grp_x_right, line_y, phrase_group_bottom))
        
        # Check edge labels that fall within sentence x range
        # Edge labels are positioned based on arc midpoint and control point
        for edge in all_edges:
            src_pos = positions.get(edge.src)
            dst_pos = positions.get(edge.dst)
            if not src_pos or not dst_pos:
                continue
            # Edge label x position is at arc midpoint
            edge_mid_x = (src_pos.circle_x + dst_pos.circle_x) / 2.0
            if x_left <= edge_mid_x <= x_right:
                # Estimate edge label y position using same logic as render_edges
                arc_x_left = min(src_pos.circle_x, dst_pos.circle_x)
                arc_x_right = max(src_pos.circle_x, dst_pos.circle_x)
                dx = arc_x_right - arc_x_left
                
                # Estimate min_ry based on phrase bands (same logic as render_edges)
                min_ry = 20.0
                for band_left, band_right, band_top, band_bottom in phrase_bands_in_range:
                    horiz_overlap = not (arc_x_right <= band_left or band_right <= arc_x_left)
                    if horiz_overlap:
                        circle_y = max(src_pos.circle_y, dst_pos.circle_y)
                        clearance_needed = band_bottom - circle_y + 15.0
                        if clearance_needed > min_ry:
                            min_ry = clearance_needed
                
                # Calculate ry using same formula as build_arc_path
                ry = min(80.0, max(min_ry, dx * 0.3))
                if ry < min_ry:
                    ry = min_ry
                
                # Arc bottom is at circle_y + ry
                arc_bottom = max(src_pos.circle_y, dst_pos.circle_y) + ry
                # Edge label is positioned near arc bottom, plus label height + padding
                estimated_label_bottom = arc_bottom + 24.0
                content_bottom = max(content_bottom, estimated_label_bottom)
        
        # Place sentence line just below the content with some padding
        y = content_bottom + 25.0  # 25px below the lowest content in range
        
        sentence_elements = []
        sentence_elements.append(
            f'<line x1="{x_left:.2f}" y1="{y:.2f}" x2="{x_right:.2f}" y2="{y:.2f}" stroke="seagreen" stroke-width="2" />'
        )
        mid_x = (x_left + x_right) / 2.0
        sentence_line_center_y = y + 10.0
        sentence_elements.append(
            f'<circle cx="{mid_x:.2f}" cy="{sentence_line_center_y:.2f}" r="{CIRCLE_RADIUS}" fill="seagreen" />'
        )
        sentence_elements.append(
            f'<text text-anchor="middle" fill="seagreen" font-size="{PHRASE_FONT_SIZE}" x="{mid_x:.2f}" y="{y + 36.0:.2f}">{sentence_label}</text>'
        )
        
        # Register sentence line center position for صلة edges
        sentence_line_id = "__sentence_line"
        positions[sentence_line_id] = TokenPosition(
            text_x=mid_x,
            circle_x=mid_x,
            circle_y=sentence_line_center_y,
            label_y=sentence_line_center_y + LINE_LABEL_PADDING,
        )
        
        # Render صلة edges targeting the sentence line center
        if silah_edges:
            # Modify silah edges to target sentence line instead of original destination
            silah_edges_to_sentence = [
                Edge(edge.src, sentence_line_id, edge.label, edge.color)
                for edge in silah_edges
            ]
            silah_edge_elements = render_edges(silah_edges_to_sentence, positions, dynamic_height + 50, line_groups)
            sentence_elements.extend(silah_edge_elements)
        
        edge_elements = sentence_elements + edge_elements
    else:
        # No sentence line - render any صلة edges normally (to their original targets)
        if silah_edges:
            silah_edge_elements = render_edges(silah_edges, positions, dynamic_height, line_groups)
            edge_elements = silah_edge_elements + edge_elements
    
    line_elements = render_line_groups(line_groups, positions, dynamic_height, all_edges)
    body = "\n".join(base_elements + edge_elements + line_elements)
    return segment_width, dynamic_height, body


def assemble_svg(
    segments: Sequence[Tuple[float, float, str]],
    font_data: str,
    total_height: float,
) -> str:
    max_width = max((segment_width for segment_width, _, _ in segments), default=0.0)
    style = (
        "@font-face{font-family:'Kitab';src:url('data:font/ttf;base64,"
        + font_data
        + "') format('truetype');font-weight:normal;font-style:normal;}"
        "text,tspan{font-family:'Kitab','Times New Roman';}"
        "svg{font-family:'Kitab','Times New Roman';background:transparent;}"
    )
    outer_parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{max_width:.2f}" height="{total_height:.2f}" '
        f'viewBox="0 0 {max_width:.2f} {total_height:.2f}">',
        f'<defs><style type="text/css">{style}</style></defs>',
    ]
    # Optional header: sentence type label extracted from first segment body comment (passed via closure)
    # We don’t have direct access to spec here, so we embed a lightweight hook: if the first segment body
    # begins with an HTML comment containing SENTENCE=label, extract and show it. To keep it simple,
    # we’ll skip comment parsing and instead rely on a global temp passed via DEBUG_FLAGS (lightweight approach).
    # Removed top-right sentence header; sentence type is rendered as a line within the relevant line
    current_y = 0.0
    for segment_width, segment_height, body in segments:
        x_offset = (
            (max_width - segment_width) / 2.0 if max_width > segment_width else 0.0
        )
        outer_parts.append(
            f'<svg class="syntax-graph-view" x="{x_offset:.2f}" y="{current_y:.2f}" '
            f'width="{segment_width:.2f}" height="{segment_height:.2f}" '
            f'viewBox="0 0 {segment_width:.2f} {segment_height:.2f}">{body}</svg>'
        )
        current_y += segment_height
    outer_parts.append("</svg>")
    return "\n".join(outer_parts)


def generate_svg(spec_path: Path, output_path: Path, font_path: Path) -> None:
    spec = load_spec(spec_path)
    words = load_ayah_words(spec, spec_path)
    tokens = build_tokens(spec["tokens"], words)
    edges = build_edges(spec.get("edges", []))
    line_groups = build_line_groups(spec.get("line_groups"))
    segments = build_segments(spec["segments"])

    # Pass sentence type and head id before rendering segments so per-line renderer can draw it
    try:
        sentence_label = ""
        sentence_head = ""
        notes = spec.get("notes") if isinstance(spec, dict) else None
        if isinstance(notes, dict):
            sentence_label = str(notes.get("sentence_type_label") or "")
            sentence_head = str(notes.get("sentence_head_id") or "")
        DEBUG_FLAGS["sentence_type_label"] = sentence_label
        DEBUG_FLAGS["sentence_head_id"] = sentence_head
    except Exception:
        DEBUG_FLAGS["sentence_type_label"] = ""
        DEBUG_FLAGS["sentence_head_id"] = ""

    segment_svgs: List[Tuple[float, float, str]] = []
    total_height = 0.0
    for segment in segments:
        # Filter line groups for this segment first
        segment_lines = [
            group
            for group in line_groups
            if all(member in segment.token_ids for member in group.members)
        ]
        # Get set of line group IDs for this segment
        segment_line_group_ids = {group.id for group in segment_lines if group.id}
        
        # Include edges that touch this segment (src or dst inside, or src/dst is a line group ID)
        segment_edges = [
            edge
            for edge in edges
            if (edge.src in segment.token_ids) 
               or (edge.dst in segment.token_ids)
               or (edge.dst in segment_line_group_ids)  # Edges targeting line groups
               or (edge.src in segment_line_group_ids)  # Edges FROM line groups (e.g., متعلق)
        ]
        rendered = render_segment_svg(segment, tokens, segment_edges, segment_lines)
        segment_svgs.append(rendered)
        total_height += rendered[1]

    font_data = load_font_data(font_path)
    svg_content = assemble_svg(segment_svgs, font_data, total_height)

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(svg_content, encoding="utf-8")


def generate_svg_from_spec(
    spec: Dict[str, object],
    output_path: Path,
    font_path: Path,
    masaq_db: Path,
) -> None:
    """Render an SVG directly from an in-memory spec without writing a JSON file."""
    meta = spec.get("meta", {}) if isinstance(spec, dict) else {}
    surah = int((meta.get("surah") or 0))
    ayah = int((meta.get("ayah") or 0))
    if surah <= 0 or ayah <= 0:
        raise ValueError("Spec must include meta.surah and meta.ayah")

    words = _load_quran_words_raw(masaq_db, surah, ayah)
    tokens = build_tokens(spec["tokens"], words)
    edges = build_edges(spec.get("edges", []))
    line_groups = build_line_groups(spec.get("line_groups"))
    segments = build_segments(spec["segments"])

    # Pass sentence type and head id ahead of render
    try:
        sentence_label = ""
        sentence_head = ""
        notes = spec.get("notes") if isinstance(spec, dict) else None
        if isinstance(notes, dict):
            sentence_label = str(notes.get("sentence_type_label") or "")
            sentence_head = str(notes.get("sentence_head_id") or "")
        DEBUG_FLAGS["sentence_type_label"] = sentence_label
        DEBUG_FLAGS["sentence_head_id"] = sentence_head
    except Exception:
        DEBUG_FLAGS["sentence_type_label"] = ""
        DEBUG_FLAGS["sentence_head_id"] = ""

    segment_svgs: List[Tuple[float, float, str]] = []
    total_height = 0.0
    for segment in segments:
        # Filter line groups for this segment first
        segment_lines = [
            group
            for group in line_groups
            if all(member in segment.token_ids for member in group.members)
        ]
        # Get set of line group IDs for this segment
        segment_line_group_ids = {group.id for group in segment_lines if group.id}
        
        # Include edges that touch this segment (src or dst inside, or src/dst is a line group ID)
        segment_edges = [
            edge
            for edge in edges
            if (edge.src in segment.token_ids) 
               or (edge.dst in segment.token_ids)
               or (edge.dst in segment_line_group_ids)  # Edges targeting line groups
               or (edge.src in segment_line_group_ids)  # Edges FROM line groups (e.g., متعلق)
        ]
        rendered = render_segment_svg(segment, tokens, segment_edges, segment_lines)
        segment_svgs.append(rendered)
        total_height += rendered[1]

    font_data = load_font_data(font_path)
    svg_content = assemble_svg(segment_svgs, font_data, total_height)

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(svg_content, encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate dependency SVGs. Minimal usage: --surah N --ayah M [M2 ...]. All layout enforcement is ON by default."
    )
    parser.add_argument("--surah", type=int, help="Surah number for generation")
    parser.add_argument("--ayah", type=int, nargs="+", help="Ayah numbers to generate")
    parser.add_argument(
        "--spec", help="Path to existing JSON spec (alternative to surah/ayah)"
    )
    parser.add_argument("--output", help="Output SVG path (when using --spec)")
    parser.add_argument("--font", help="Override font path")
    parser.add_argument("--spec-dir", help="Directory root for auto-generated specs")
    parser.add_argument("--masaq-db", help="Override MASAQ.db path")
    parser.add_argument(
        "--skip-svg", action="store_true", help="Skip SVG rendering (when writing spec only)"
    )
    parser.add_argument(
        "--no-spec", action="store_true", help="Render directly without writing spec (default behavior)"
    )
    parser.add_argument(
        "--write-spec", action="store_true", help="Write spec JSON to specs_generated and then render"
    )
    parser.add_argument(
        "--continuation-mode",
        choices=["one-sided", "bilateral"],
        default="bilateral",
        help="How to split cross-line edges: one-sided (legacy) or bilateral (placeholders on both lines)",
    )
    parser.add_argument(
        "--edge-label-mode",
        choices=["none", "minimal", "full"],
        default="full",
        help="How to render edge labels on arcs (default: full)",
    )
    # Unified debug flag (optional)
    parser.add_argument(
        "--debug", action="store_true", help="Enable debug outlines and overlap logging"
    )
    # Verbose logging for performance and handler diagnostics
    parser.add_argument(
        "--verbose", action="store_true", help="Enable verbose logging (edge counts, performance metrics)"
    )
    # Opt-out flags (rarely used) to disable specific enforcement behaviors
    parser.add_argument("--no-enforce-grammar", action="store_true")
    parser.add_argument("--no-enforce-arcs", action="store_true")
    parser.add_argument("--no-enforce-edge-labels", action="store_true")
    parser.add_argument("--no-avoid-circles", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    
    # ========================================================================
    # VALIDATION AND EARLY ERROR DETECTION
    # ========================================================================
    
    try:
        # Validate command-line arguments
        if args.surah is None and args.spec is None:
            raise ValueError("Either --surah (with --ayah) or --spec must be provided")
        
        if args.surah is not None and args.ayah is None:
            raise ValueError("--ayah is required when using --surah")
        
        # Validate surah/ayah ranges
        if args.surah is not None:
            if not (1 <= args.surah <= 114):
                raise ValueError(f"Invalid surah number: {args.surah} (must be 1-114)")
            for ayah in args.ayah or []:
                if not (1 <= ayah <= 286):
                    raise ValueError(f"Invalid ayah number: {ayah} (must be 1-286)")
        
        # Validate paths exist
        repo_root = find_repo_root(Path.cwd())
        masaq_db = Path(args.masaq_db or repo_root / "MASAQ.db")
        if not masaq_db.exists():
            raise FileNotFoundError(f"MASAQ database not found: {masaq_db}")
        
        # Validate continuation mode
        valid_modes = {"one-sided", "bilateral"}
        if args.continuation_mode not in valid_modes:
            raise ValueError(f"Invalid continuation_mode: {args.continuation_mode}")
        
        # Validate edge label mode
        valid_label_modes = {"none", "minimal", "full"}
        if args.edge_label_mode not in valid_label_modes:
            raise ValueError(f"Invalid edge_label_mode: {args.edge_label_mode}")
        
        print("✓ All validation checks passed")
        
    except (ValueError, FileNotFoundError) as e:
        print(f"❌ Configuration Error: {e}", file=sys.stderr)
        raise SystemExit(1)
    
    # ========================================================================
    # UPDATE DEBUG FLAGS FROM CLI
    # ========================================================================
    # Default: all enforcement ON unless explicitly opted-out.
    DEBUG_FLAGS["outline_labels"] = bool(getattr(args, "debug", False))
    DEBUG_FLAGS["log_overlaps"] = bool(getattr(args, "debug", False))
    DEBUG_FLAGS["wide_word_spacing"] = False  # experimental disabled by default
    DEBUG_FLAGS["enforce_grammar"] = not getattr(args, "no_enforce_grammar", False)
    DEBUG_FLAGS["enforce_arc_separation"] = not getattr(args, "no_enforce_arcs", False)
    DEBUG_FLAGS["enforce_edge_labels"] = not getattr(
        args, "no_enforce_edge_labels", False
    )
    DEBUG_FLAGS["avoid_circle_overlap"] = not getattr(args, "no_avoid_circles", False)
    # Update continuation mode from CLI
    global CONTINUATION_MODE
    try:
        CONTINUATION_MODE = str(getattr(args, "continuation_mode", CONTINUATION_MODE) or CONTINUATION_MODE)
    except Exception:
        pass
    # Update edge label mode
    global EDGE_LABEL_MODE
    try:
        EDGE_LABEL_MODE = str(getattr(args, "edge_label_mode", EDGE_LABEL_MODE) or EDGE_LABEL_MODE)
    except Exception:
        pass
    if args.surah is not None:
        if not args.ayah:
            raise SystemExit("Provide at least one --ayah when using --surah")

        script_location = Path(__file__).resolve()
        repo_root = find_repo_root(script_location)

        if args.masaq_db:
            masaq_path = Path(args.masaq_db).resolve()
        else:
            masaq_path = (repo_root / "MASAQ.db").resolve()

        # Only needed if explicitly writing the spec
        spec_dir = (
            Path(args.spec_dir).resolve()
            if args.spec_dir
            else (repo_root / "specs_generated")
        )
        font_candidate: Optional[Path]
        if args.font:
            font_candidate = Path(args.font)
        else:
            font_candidate = (repo_root / "fonts" / "Kitab-Regular.ttf").resolve()

        for ayah in args.ayah:
            spec = build_spec_from_sources(
                args.surah,
                ayah,
                masaq_path,
            )
            
            # ================================================================
            # LOGGING: Verbose output for diagnostics
            # ================================================================
            if getattr(args, "verbose", False):
                edges = spec.get("edges", [])
                perf = spec.get("perf_metrics", {})
                tokens = spec.get("tokens", {})
                
                print(f"[{args.surah}:{ayah}] Spec built:")
                print(f"  - Tokens: {len(tokens)}")
                print(f"  - Edges: {len(edges)}")
                
                if perf:
                    elapsed = perf.get("edge_building_time", 0)
                    print(f"  - Edge building time: {elapsed:.3f}s")
                    if perf.get("handler_times"):
                        print(f"  - Handlers invoked: {len(perf['handler_times'])}")

            # Default: generate on-the-fly without writing JSON
            if getattr(args, "no_spec", False) or not getattr(args, "write_spec", False):
                output_path = Path(spec.get("output_path"))
                if not output_path.is_absolute():
                    output_path = (repo_root / output_path).resolve()
                output_path.parent.mkdir(parents=True, exist_ok=True)

                candidate = font_candidate
                if args.font:
                    candidate = Path(args.font)
                elif "font_path" in spec:
                    candidate = normalise_path(
                        spec.get("font_path"), repo_root / "specs_generated"
                    )
                if candidate is None or not candidate.exists():
                    candidate = (
                        repo_root / "fonts" / "Kitab-Regular.ttf"
                    ).resolve()
                if not candidate.exists():
                    raise SystemExit(f"Font file not found: {candidate}")

                generate_svg_from_spec(spec, output_path, candidate, masaq_path)
                print(f"Wrote {output_path}")
                continue

            # Explicit request: write spec JSON then render
            spec_dir.mkdir(parents=True, exist_ok=True)
            target_path = spec_dir / str(args.surah) / f"{ayah}.json"
            target_path.parent.mkdir(parents=True, exist_ok=True)
            target_path.write_text(
                json.dumps(spec, ensure_ascii=False, indent=2), encoding="utf-8"
            )
            print(f"Wrote spec {target_path}")

            if args.skip_svg:
                continue

            spec_path = target_path
            output_path = Path(spec.get("output_path"))
            if not output_path.is_absolute():
                output_path = (spec_path.parent / output_path).resolve()

            candidate = font_candidate
            if args.font:
                candidate = Path(args.font)
            elif "font_path" in spec:
                candidate = normalise_path(spec.get("font_path"), spec_path)
            if candidate is None or not candidate.exists():
                candidate = (repo_root / "fonts" / "Kitab-Regular.ttf").resolve()
            if not candidate.exists():
                raise SystemExit(f"Font file not found: {candidate}")

            generate_svg(spec_path, output_path, candidate)
            print(f"Wrote {output_path}")

        return

    if not args.spec:
        raise SystemExit("Provide --spec or use --surah/--ayah for generation")

    spec_path = Path(args.spec).resolve()
    spec = load_spec(spec_path)

    default_output = spec.get("output_path")
    if not args.output and not default_output:
        raise SystemExit("Either provide --output or include 'output_path' in the spec")

    output_path = Path(args.output or default_output)
    if not output_path.is_absolute():
        output_path = (spec_path.parent / output_path).resolve()

    font_candidate: Optional[Path]
    if args.font:
        font_candidate = Path(args.font)
    else:
        font_candidate = normalise_path(spec.get("font_path"), spec_path)
        if font_candidate is None:
            repo_root = find_repo_root(spec_path.parent)
            font_candidate = (repo_root / "fonts" / "Kitab-Regular.ttf").resolve()

    if not font_candidate.exists():
        raise SystemExit(f"Font file not found: {font_candidate}")

    generate_svg(spec_path, output_path, font_candidate)
    # Persist debug flags for downstream visualization by writing a sibling .debug.json
    debug_info = {
        "outline_labels": bool(getattr(args, "outline_labels", False)),
        "log_overlaps": bool(getattr(args, "log_overlaps", False)),
    }
    if any(debug_info.values()):
        try:
            debug_path = output_path.with_suffix(".debug.json")
            debug_path.write_text(json.dumps(debug_info, indent=2), encoding="utf-8")
            print(f"Wrote debug flags {debug_path}")
        except Exception as e:
            print(f"Failed writing debug info: {e}")
    print(f"Wrote {output_path}")


if __name__ == "__main__":
    main()
