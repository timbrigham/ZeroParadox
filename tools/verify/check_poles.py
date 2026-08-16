#!/usr/bin/env python3
"""DC-16 - pole equalities written with `=`.

THE CLASS. Writing `0 = ∞`, `∞ = ⊥` or `0 = ∞ = ⊥` as a plain equality asserts that two poles are
ONE POINT. That is the quotient which identifies them - which is the MEADOW, the structure this
project explicitly rejected and disproved: `inf_ne_bot` proves ∞ ≠ ⊥ in the wheel of fractions,
choice-free, and `wheelFrac_fork_open` proves 0 ≠ ∞. So the notation is not loose phrasing; it
asserts the refuted alternative.

THE DISCRIMINATOR, and it is the whole design. An equality chain is suspect only when ∞ appears in
it. `⊥ = 0` alone is fine and usually true - the bottom of a lattice genuinely IS the number zero in
ℤ₂, in ℚ₂, in `[0, ∞)`. Both proved distinctness results involve ∞ (∞ ≠ ⊥, 0 ≠ ∞), and all 12
hand-verified OK sites that carry `0 = ⊥` carry no ∞ in the equation. The pole identity needs ∞.

WHAT IS LEGITIMATE, so the allowlist is principled rather than fitted:
  * the OPERATION form - `∞ = /0`, `⊥ = 0·/0`. The right side is a construction, not a pole, so the
    `=` is between an element and an expression. This is the recommended phrasing.
  * an APPLICATION - `rInv 0 = ∞`. The left side is a function applied to a pole. Note the contrast
    with `0 = ∞ under rInv`, which is bare and IS the defect: a map that SWAPS two points is
    evidence they are DIFFERENT, so citing it for an identity inverts its content.
  * describing the REJECTED case - a line naming the meadow/field collapse on purpose.
  * a NEGATED claim - `∞ ≠ ⊥`.

SCOPE covers .lean, .md AND .py. The 2026-08-01 sweep that removed two false universal negatives
grepped `.lean` only and missed a Python build script, so the claim survived into a rendered PDF.
Build scripts are a public surface.

CONTROLS: `--selftest` runs must-fire and must-suppress cases. `--score` grades against the frozen
labelled set in deepseek/pole_groundtruth.json. Verify the detector before believing its output -
in either direction.

  python check_poles.py            # warn, exit 0
  python check_poles.py --block    # exit 1 on any new hit
  python check_poles.py --selftest # controls
  python check_poles.py --score    # grade against ground truth
"""
import io, os, re, sys, json

# Roots come from `common` — ONE derivation for the whole bundle (`DEFECTS.md` MIG-3). SELF is
# derived from `__file__`, never written down: a hardcoded invocation path is a copy of the path and
# drifts exactly like a mirrored file does.
#
# ⚠ COERCED TO `str`, not re-derived. This module speaks `os.path`; `common` speaks `pathlib`. A
# line of type conversion is not a second definition — change the layout and there is still exactly
# one place to edit.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402

# The corpus is full of ⊥ ∞ ℤ₂; Windows stdout defaults to cp1252 and raises on them.
# ⚠ This file's own copy of the guard OMITTED `line_buffering=True` — one of the two that did, out
# of eight. `report.py:34` records what the missing flag costs: Python block-buffers while children
# write straight to the terminal fd, so output arrives out of order and section headers land under
# the wrong section. Shared now, so there is no second copy to get half right.
common.utf8_stdout()

HERE = str(common.HERE)
REPO = str(common.REPO)
PRIV = str(common.PRIV)   # private state; ABSENT in a public clone
SELF = common.self_rel(__file__)
SCAN_EXT = (".lean", ".md", ".py")
SKIP_DIRS = {".lake", ".git", "__pycache__", ".claude-local", "node_modules"}
# ⚠ ANCHORED, and deliberately not a bare directory name. This bundle IS the detector, and its own
# source is full of pole equalities used as PATTERNS, so scanning itself would report its regexes as
# findings. But adding "verify" to SKIP_DIRS above would exempt a directory of that name at ANY
# depth — the exact unanchored hole `vendored.py` records being reached twice (content marker, then
# nested `Vendored/`). Anchored at the repo root, one path, no wildcard.
SKIP_RELDIRS = {"tools/verify"}

POLE = r"(?:0|∞|⊥)"
# A chain of >=2 poles joined by '=' . Captures the whole run so `0 = ∞ = ⊥` is one hit.
CHAIN = re.compile(r"(%s)(?:\s*=\s*(%s))+" % (POLE, POLE))
# An APPLICATION is a NAMED MAP applied to the pole (`rInv 0 = ∞`), not merely any preceding word.
# ⚠ First version accepted `[A-Za-z_]\w*\s+$`, which read "the single point 0 = ∞ = ⊥" as *point*
# applied to 0 and suppressed it. An explicit map list is narrow, auditable, and cannot swallow
# English prose; add names here as the corpus grows rather than loosening the pattern.
MAPS = ("rInv", "rInvHomeo", "winv", "wmul", "swap", "cornerId", "poleToSphere",
        "cnfToZp2", "snapNucleus", "shiftEnd", "localCx", "endVal", "cx", "val", "v_2", "v₂")
#         …plus a bare single-letter name, which in Lean is a function or variable and is almost
#         never an English word sitting before a pole (`g 0 = ∞` in a proof).
APPLIED = re.compile(r"(?:(?:%s)|(?<![A-Za-z])[a-z])\s+$"
                     % "|".join(re.escape(m) for m in MAPS))
# An ARITHMETIC OPERATOR immediately before the chain means the left side is an expression whose
# VALUE is being stated, not a pole being identified with another: `0 · ∞ = ⊥` is the wheel bottom's
# defining equation, `∞ + ∞ = ⊥` an addition-table entry, `/∞ = 0` the reciprocal. All three are
# theorems here. Found by reading the first full-corpus scan - the operation allowlist only knew
# about `/0` and missed every other operator.
EXPR_BEFORE = re.compile(r"[+\-·*/^]\s*$")
# An operation on either side means the `=` is not between two bare poles.
# ⚠ `rInv` and `1/` were listed here at first. Both are WRONG: a map that SWAPS two points is
# evidence they are DIFFERENT, so its presence beside a bare `0 = ∞` INDICTS the line rather than
# excusing it - which is precisely the misuse this class exists to catch. Application is handled
# above, by position; mere mention of an inversion legitimates nothing.
OPERATION = re.compile(r"[/·*]\s*0|0\s*[·*]\s*/|winv|wmul|wheelBot|wheelInf")
REJECTED = re.compile(r"meadow|collapse|field is a wheel|degenerate", re.I)
NEGATED = re.compile(r"≠|!=|\\ne\b|not equal")

GRACE = 24   # chars either side of the chain that count as "beside it"

def classify(line, m):
    """Return None if legitimate, else a one-line reason.

    ⚠ OPERATION is scoped to the chain's NEIGHBOURHOOD, not the whole line. Line-scoping let a
    legitimate `∞ = /0` earlier in a sentence excuse a bare `⊥ = ∞` later in the same sentence -
    the proximity-contamination failure (DC-9) committed inside a checker written to avoid it.
    NEGATED and REJECTED stay line-scoped on purpose: both describe what the SENTENCE is doing."""
    chain = m.group(0)
    poles = re.findall(POLE, chain)
    if "∞" not in poles:
        return None                      # `⊥ = 0` is a within-carrier statement, not a pole identity
    before = line[:m.start()]
    if APPLIED.search(before):
        return None                      # `rInv 0 = ∞` - an application, not an identity
    if EXPR_BEFORE.search(before):
        return None                      # `0 · ∞ = ⊥`, `∞ + ∞ = ⊥`, `/∞ = 0` - an expression's VALUE
    near = line[max(0, m.start() - GRACE): m.end() + GRACE]
    if OPERATION.search(near):
        return None                      # `∞ = /0`, `⊥ = 0·/0` - the operation form, beside the chain
    if NEGATED.search(line):
        return None                      # the line is asserting distinctness
    if REJECTED.search(line):
        return None                      # naming the meadow collapse on purpose
    return "pole chain `%s` written as a plain equality" % chain.strip()

# `Idiom:` - the THIRD label, beside `Statement:` and `Reading:`. It marks text that NAMES the
# phenomenon ("the 0=∞ inversion", "the 0=∞ antipodality") rather than ASSERTING the equation.
# Neither existing label fits: it is not what a theorem proves, and it is not an interpretation of
# one - it is a handle. The test for applying it: does the sentence USE the equation, or does it
# NAME something? "the 0 = ∞ pole" names; "0 = ∞ under rInv" asserts, and stays a defect.
#
# ⚠ This is a SUPPRESSION MECHANISM and can be rubber-stamped. It is deliberately visible in the
# source rather than hidden in a baseline file, and the run reports how many sites carry it, so
# growth shows up instead of going quiet. Same line or the line immediately above, matching the
# gloss convention `check_prose.py` already uses.
IDIOM = re.compile(r"\bIdiom:", re.I)

def scan_text(text, path="<str>"):
    out, idioms = [], []
    lines = text.splitlines()
    for i, line in enumerate(lines, 1):
        for m in CHAIN.finditer(line):
            why = classify(line, m)
            if not why:
                continue
            above = lines[i - 2] if i >= 2 else ""
            if IDIOM.search(line) or IDIOM.search(above):
                idioms.append((path, i))
                continue
            out.append((path, i, why, line.strip()[:160]))
    scan_text.last_idioms = idioms
    return out

def scan_repo():
    hits, idioms = [], []
    for root, dirs, files in os.walk(REPO):
        relroot = os.path.relpath(root, REPO).replace("\\", "/")
        dirs[:] = [
            d for d in dirs
            if d not in SKIP_DIRS
            and (relroot + "/" + d).lstrip("./") not in SKIP_RELDIRS
        ]
        for fn in files:
            if not fn.endswith(SCAN_EXT):
                continue
            p = os.path.join(root, fn)
            try:
                t = io.open(p, encoding="utf-8").read()
            except Exception:
                continue
            hits += scan_text(t, os.path.relpath(p, REPO).replace("\\", "/"))
            idioms += scan_text.last_idioms
    scan_repo.last_idioms = idioms
    return hits

# --------------------------------------------------------------------------- controls
MUST_FIRE = [
    ("bare two-pole", "concurrent is the pole `0 = ∞` where ascent and descent meet"),
    ("three-pole chain", "the pole is the single point 0 = ∞ = ⊥ at which all three coincide"),
    ("swap cited as identity", "Within-frame identities stand (0 = ∞ under rInvHomeo in Q2)"),
    ("inf equals bot", "the two ends are one, so ∞ = ⊥ and the distinction dissolves"),
]
MUST_SUPPRESS = [
    ("Idiom-labelled", "Idiom: the 0 = ∞ inversion - a NAME for the phenomenon, not an assertion"),
    ("within-carrier", "the 2-adic norm converges to 0 = ⊥, the floor of this carrier"),
    ("operation form", "the two derived elements ∞ = /0 and ⊥ = 0·/0"),
    ("application", "Under the inversion the poles are exchanged: rInvHomeo 0 = ∞"),
    ("negated", "Wheel vs meadow diagram (∞ ≠ ⊥), division by zero made total"),
    ("rejected case named", "In a meadow the two collapse: ∞ = ⊥. The wheel refuses this."),
    ("example lattice", "Take the lattice [0, ∞) with ⊥ = 0 and join = max"),
]

def selftest():
    bad = 0
    print("MUST FIRE")
    for name, line in MUST_FIRE:
        got = bool(scan_text(line))
        print("  %-24s %s" % (name, "ok" if got else "*** DID NOT FIRE ***"))
        bad += 0 if got else 1
    print("MUST SUPPRESS")
    for name, line in MUST_SUPPRESS:
        got = bool(scan_text(line))
        print("  %-24s %s" % (name, "ok" if not got else "*** FALSE POSITIVE ***"))
        bad += 1 if got else 0
    print("\nselftest: %s" % ("PASS" if not bad else "FAIL (%d)" % bad))
    return 1 if bad else 0

def score():
    # The labelled set lives in the PRIVATE folder (it quotes un-triaged corpus sites), so scoring
    # is unavailable in a public clone. Say so instead of raising a bare FileNotFoundError.
    gt_path = os.path.join(PRIV, "deepseek", "pole_groundtruth.json")
    if not os.path.exists(gt_path):
        print("--score needs the labelled set at %s, which is private and not present here."
              % os.path.relpath(gt_path, REPO).replace("\\", "/"))
        print("The detector itself, its --selftest controls and the scan all run without it.")
        return 2
    gt = json.load(io.open(gt_path, encoding="utf-8"))
    hits = {(h[0], h[1]) for h in scan_repo()}
    rows, miss, fp = [], 0, 0
    for s in gt["sites"]:
        key, want = (s["file"], s["line"]), s["label"]
        flagged = key in hits
        if want in ("DEFECT", "BORDERLINE"):
            mark = "HIT" if flagged else "*** MISS ***"
            miss += 0 if flagged else 1
        else:
            mark = "*** FALSE POSITIVE ***" if flagged else "ok"
            fp += 1 if flagged else 0
        rows.append((("%s:%d" % key), want, "flag" if flagged else "-", mark))
    w = max(len(r[0]) for r in rows)
    for r in rows:
        print("%-*s  %-10s %-5s %s" % (w, r[0], r[1], r[2], r[3]))
    print("\nmisses %d   false positives %d   of %d labelled sites" % (miss, fp, len(rows)))
    return 1 if (miss or fp) else 0

if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    if "--score" in sys.argv:
        sys.exit(score())
    hits = scan_repo()
    idioms = scan_repo.last_idioms
    if "--idioms" in sys.argv:
        for p, n in idioms:
            print("%s:%d" % (p, n))
        print("\n%d site(s) carry `Idiom:`" % len(idioms))
        sys.exit(0)
    for p, n, why, txt in hits:
        print("%s:%d  %s\n    %s" % (p, n, why, txt))
    # Report the suppressed count ALWAYS. A suppression mechanism that goes quiet is how a
    # baseline turns into a place defects hide; growth here should be visible, not discovered.
    print("\n%d pole-equality site(s)   [%d suppressed by `Idiom:` - list with --idioms]"
          % (len(hits), len(idioms)))
    sys.exit(1 if (hits and "--block" in sys.argv) else 0)
