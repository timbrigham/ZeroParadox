"""Undated universal negatives — DC-3 and DC-8, deliberately one checker.

*"None exists"* and *"not in Mathlib"* are the same defect in two vocabularies: a claim that
something is ABSENT, asserted without a date or a record of the search that would justify it. The
honest form is always *"none located as of <date>, searched as follows"*, because a universal
negative is falsified by any single future commit and **nothing mechanical notices.**

WHY THIS CLASS FIRST AMONG THE UNCOVERED ONES. It has the highest measured cost in this project's
history. Two false universal negatives sat in `Category/ChoiceCannotBe.lean` — a `CannotBe` index,
the file type whose stated premise is that it cannot overclaim — asserting *"No essential case has
been found anywhere in the framework"* while two taboo reductions existed and were `#check`ed
nowhere. One reached a **published PDF** with a Zenodo DOI, which cannot be withdrawn.

⚠ **AND IT MUST SCAN `.py` AND `.md`, NOT ONLY `.lean`.** The 2026-08-01 sweep that removed those
two negatives grepped Lean sources and **missed a Python build script**, so the claim survived in
rendered public prose for two more days. A checker scoped to the corpus would repeat that exactly.

WHAT IT DELIBERATELY DOES NOT DO
It cannot tell a live claim from a retraction quoting one — retraction text repeats the error
verbatim. A hit is a PROMPT TO READ, never a verdict. Read hits; do not count them.

Usage (the exact invocation path is printed in this tool's own output):
  check_negatives.py            # WARN (advisory, exit 0)
  check_negatives.py --block    # exit 1 on any NEW unbaselined site
  check_negatives.py --baseline # rewrite the baseline from current state
  check_negatives.py --selftest # must-fire AND must-suppress controls
"""
import hashlib
import io
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common                              # noqa: E402
# ⚠ IMPORTED, NOT RE-IMPLEMENTED. `normalize_separators` handles wrapped claims — a phrase split
# across a Lean `--` comment continuation or a Python adjacent-string join is invisible to a flat
# pattern, and it needed THREE fixes to get right (literal spaces, then the separators, then line
# numbers counted against the original). A second copy here would be the mirror defect this project
# spent 2026-08-15 removing. One definition.
#
# ⚠ AND IT COMES FROM `common` NOW, NOT FROM `check_modal`. Until 2026-08-16 this line read
# `from check_modal import ...`, which made a CHECKER into a LIBRARY: two peers depended on a third
# peer's internals, invisibly from either end (`DEFECTS.md` MIG-3). Shared machinery belongs in a
# module that checks nothing.
from common import HERE, REPO, normalize_separators, strip_module_docstring  # noqa: E402
from vendored import is_vendored          # noqa: E402
import report                              # noqa: F401,E402  (utf-8 stdout, side effect)

SELF = common.self_rel(__file__)
BASELINE = HERE / 'negatives_baseline.txt'

# ── the claim ────────────────────────────────────────────────────────────────────────────────
# Every space is `\s+`: a claim wrapped across two lines must still match.
# ⚠ THE ADJECTIVE SLOT IS LOAD-BEARING, AND ITS ABSENCE WAS THIS CHECKER'S FIRST BUG. The first
# version required the literal `no case has been found`. The REAL defect — the one that reached a
# published PDF — reads **"No essential case has been found anywhere in the framework"**, and the
# single word `essential` defeated the pattern outright. A checker written for a known defect that
# cannot match that defect is worse than none: it reports a confident zero.
#
# Caught by writing the must-fire control from the ACTUAL historical text rather than from a
# paraphrase of it. `(?:\w+[\s-]+){0,3}` allows up to three qualifiers in the noun phrase.
_QUAL = r"(?:\w+[\s-]+){0,3}"

# ⚠⚠ SURVEY NEGATIVES ONLY. A PROVED NON-EXISTENCE IS NOT THIS DEFECT AND MUST NOT FIRE.
#
# The first pattern set included a bare `no <thing> exists`, and the first real run returned **75
# hits, the large majority of them correct mathematics**: "No fixed point exists; the reflexive
# object is impossible" (Lawvere), "no terminal object exists; AX-G2 holds", "no greatest natural
# number exists" (AX-G1), "no finite tree exists" (an empty W-type). Those are THEOREMS. They are
# proved, they are load-bearing, and flagging them would have trained everyone to ignore this gate
# — the cry-wolf shape this project says to narrow rather than tolerate.
#
# **The discriminator is SEARCH vocabulary, not negation.** DC-3 is a claim about what someone
# LOOKED FOR and did not find — "has been found", "located", "anywhere in the framework", "not in
# Mathlib". Mathematics proves; a survey reports. A theorem never says *found*.
#
# Deliberately NOT matched, and each was a real hit that is correct as written:
#   "no fixed point exists"            - Lawvere / Cantor, proved
#   "no terminal object exists"        - AX-G2, proved
#   "no cross-setting map exists"      - a type boundary, proved
#   "does not exist in <structure>"    - ordinary mathematical scope
_N = [
    # "no <qual> has/have (ever) been found/located/observed"  <- the published defect's shape
    r"\bno\s+" + _QUAL + r"ha(?:s|ve)\s+(?:ever\s+)?been\s+(?:found|located|observed)",
    r"\bnone\s+(?:ha(?:s|ve)\s+(?:ever\s+)?been\s+)?(?:found|located|observed)\b",
    r"\bnever\s+been\s+(?:found|located|observed)\b",
    r"\bhas\s+never\s+been\s+(?:found|located|observed)\b",
    # explicitly scoped to a searched body
    r"\bnowhere\s+in\s+the\s+(?:framework|corpus|repo\w*|codebase)",
    r"\bno\s+" + _QUAL + r"anywhere\s+in\s+the\s+(?:framework|corpus|repo\w*|codebase)",
    r"\bnot\s+in\s+Mathlib\b",
    r"\bthere\s+is\s+no\s+" + _QUAL + r"in\s+(?:Mathlib|the\s+corpus|the\s+framework)",
    r"\bthe\s+corpus\s+does\s+not\s+have\b",
    r"\bno\s+such\s+" + _QUAL + r"in\s+(?:Mathlib|the\s+corpus|the\s+framework)",
]
CLAIM = re.compile("|".join("(?:%s)" % p for p in _N), re.I)

# ── the evidence that makes it honest ────────────────────────────────────────────────────────
# A DATE, or an explicit record of the search. Anything else is an unbacked universal.
#
# ⚠ "searched" ALONE IS NOT ENOUGH and that is deliberate. The failure mode this class exhibits is
# a claim whose author DID search and wrote down only the conclusion; a year anchors it to a tree
# state a reader can check out, and a bare "we searched" does not.
EVIDENCE = re.compile(
    r"as\s+of\s+\d{4}|"                     # "as of 2026-08-15"
    r"\b20\d\d-\d\d-\d\d\b|"                # any ISO date on the line
    r"located\s+as\s+of|"
    r"searched\s+as\s+follows|"
    r"searched\s+\d|"
    # ⚠ "SEARCHED, NONE FOUND" IS EVIDENCE, and omitting it made this gate fight the manual.
    # It is the phrasing CLAUDE.md's prior-art section MANDATES for a completed search that found
    # nothing, and the spec for this checker says a negative passes when accompanied by "a date OR
    # an explicit search record". All six hits of the first narrowed run were this exact form -
    # every one an honest record of work done. A gate that fires on its own project's ratified
    # wording gets muted, and then it is not a gate.
    # A DATE is still stronger and still preferred; this checker cannot enforce that preference
    # without punishing compliance, so it does not try.
    r"searched[,;]?\s+(?:and\s+)?none\s+found|"
    r"prior[- ]art\s+search|"
    r"not\s+located\b|"                     # the ratified honest phrasing
    r"retract|"                             # a retraction quoting the error
    r"used\s+to\s+(?:say|read)|"            # prior-state prose quoting it
    r"corrected\b|"
    r"WAS\s+FALSE|"
    r"this\s+line\s+said",
    re.I)

# The shared skips (`CLAUDE.md`, `register.md`, `RELEASES.md`) live in `common.SKIP_NAMES`. What is
# genuinely THIS checker's stays here: its own source, its own baseline, and the defect register —
# which is an INDEX OF DEFECT KINDS, so it states universal negatives as the thing being catalogued
# rather than as claims of its own. (It is gitignored, so this skip is intent rather than filter:
# `tracked_md()` is tracked-only and cannot yield it.)
SKIP_NAMES = {'check_negatives.py', 'negatives_baseline.txt', 'DEFECT_CLASSES.md'}


def targets():
    """`.lean` + `.md` + `.py`. The `.py` half is the whole point — see the header."""
    return common.targets(skip_names=SKIP_NAMES, is_vendored=is_vendored)


def sentence_around(text, pos):
    """The sentence containing `pos`. Evidence must be IN it — proximity is not aboutness."""
    start = max(text.rfind('.', 0, pos), text.rfind('\n\n', 0, pos)) + 1
    end = text.find('.', pos)
    end = len(text) if end < 0 else end + 1
    return text[start:end]


def scan_text(t):
    """(line, matched, sentence) for every unbacked universal negative."""
    body = strip_module_docstring(t, '')
    norm = normalize_separators(body)
    out = []
    for m in CLAIM.finditer(norm):
        sent = sentence_around(norm, m.start())
        if EVIDENCE.search(sent):
            continue
        # Line number against the ORIGINAL text, never the normalized copy.
        line = body.count('\n', 0, m.start()) + 1
        out.append((line, m.group(0).strip(), ' '.join(sent.split())[:150]))
    return out


def scan():
    hits = []
    for p, rel in targets():
        try:
            t = io.open(p, encoding='utf-8').read()
        except (OSError, UnicodeDecodeError):
            continue
        for line, matched, sent in scan_text(t):
            hits.append((rel, line, matched, sent))
    return hits


def key(h):
    return '%s::%s' % (h[0], hashlib.sha256(h[3].encode('utf-8')).hexdigest()[:12])


def load_baseline():
    return common.load_baseline(BASELINE)


# --------------------------------------------------------------------------- controls
# ⚠ MODULE-LEVEL, not local to `selftest`. `check_checkers.py` audits that every checker SHIPS
# must-fire and must-suppress controls, and it can only see them if they are named at module level.
MUST_FIRE = [
        # ⚠ THE FIRST TWO ARE THE ACTUAL PUBLISHED DEFECT, VERBATIM from ChoiceCannotBe.lean.
        # Written from the real text rather than a paraphrase, which is what exposed the missing
        # adjective slot: the first version of this checker could not match either of them.
        ('the real one: "No essential case…"',
         'No essential case has been found anywhere in the framework.'),
        ('its sibling: "…has ever been found"',
         'No essential case has ever been found.'),
        ('"nowhere in the framework"', 'This has been found nowhere in the framework.'),
        ('"not in Mathlib"', 'The covering relation is not in Mathlib.'),
        ('"never been found"', 'Such a witness has never been found.'),
        ('"no X anywhere in the corpus"', 'There is no such instance anywhere in the corpus.'),
        # ⚠ THE WRAPPED SHAPE. A flat pattern misses this, and it is how a real one hid.
        ('wrapped across a Lean comment', '-- the corpus\n--     does not have\n-- any such case'),
]
MUST_SUPPRESS = [
        ('dated: "as of 2026-08-15"', 'None located as of 2026-08-15, searched as follows.'),
        ('an ISO date in the sentence', 'No instance exists in the tree at 2026-08-01.'),
        ('the ratified "not located"', 'Not located in Mathlib; searched three vocabularies.'),
        ('a retraction quoting it', 'An earlier draft said none exists; that was FALSE and is retracted.'),
        ('ordinary prose', 'The bottom is the diagonal fixed point.'),
        ('a bounded, non-universal claim', 'This file contains no `sorry`.'),
        # ⚠ THE REGRESSION CONTROLS. Every one of these is a real hit from the first run, and every
        # one is correct mathematics. If someone widens the pattern back to bare negation, these
        # fail rather than the report filling with 75 findings nobody will read.
        ('PROVED: Lawvere non-existence', 'No fixed point exists; the reflexive object is impossible.'),
        ('PROVED: AX-G2', 'Zero is initial; no terminal object exists; AX-G2 holds.'),
        ('PROVED: AX-G1', 'AX-G1: no greatest natural number exists.'),
        ('PROVED: an empty W-type', 'no base case, so no finite tree exists - the strict regime.'),
        ('PROVED: a type boundary', 'the QPF instance relates distinct types, and no cross-setting map exists.'),
]


def selftest():
    """MUST-FIRE and MUST-SUPPRESS, including the two shapes that defeated earlier checkers."""
    # The scope control: the .py half is the reason this checker exists at all.
    #
    # ⚠ THIS IS NOW ALSO THE SHARED-ENUMERATOR CONTROL. `targets()` is `common.targets()` for three
    # checkers, so a scope collapse there is a false zero in all three at once rather than in one.
    # Asserting the three extensions are present is what makes that visible from inside this file.
    exts = {os.path.splitext(rel)[1] for _p, rel in targets()}
    bad = common.run_controls([
        ('  MUST FIRE', MUST_FIRE, scan_text, True, 'MISSED'),
        # The 6th element renders WHICH pattern matched when a suppression control fails — the one
        # piece of output the shared harness would otherwise have dropped.
        ('  MUST SUPPRESS', MUST_SUPPRESS, scan_text, False, 'FALSE POSITIVE',
         lambda text: '  -> ' + scan_text(text)[0][1]),
        ('  SCOPE', [('scans .lean AND .md AND .py %s' % sorted(exts), None)],
         lambda _t: {'.py', '.md', '.lean'} <= exts, True, 'SCOPE TOO NARROW'),
    ], width=44)
    # ⚠ THE VOCABULARY PIN (PAT-1). The controls above prove the patterns they exercise;
    # this proves the rest are still there. Measured before it was written: 30 of 34
    # list-shaped patterns could be deleted with every control green, and ~39 compiled
    # regexes carrying the rest of the vocabulary were pinned by nothing at all.
    print('  PATTERNS')
    bad += common.check_vocabulary('check_negatives', globals())
    if bad:
        print('\nselftest: FAIL (%d)' % bad)
    return 1 if bad else 0


def main(argv):
    if '--selftest' in argv:
        print('=' * 44)
        print('  universal-negative check - CONTROLS')
        print('=' * 44)
        return selftest()

    hits = scan()
    if '--baseline' in argv:
        common.refuse_baseline_write('negatives_baseline.txt')
        io.open(BASELINE, 'w', encoding='utf-8', newline='\n').write(
            '# Universal-negative sites present when this baseline was taken.\n'
            '# Each is a PROMPT TO READ, not a verdict: a retraction quoting an error looks\n'
            '# identical to the error. SHRINK this list as files are touched; never grow it.\n'
            '# Refresh with:  python %s --baseline\n' % SELF
            + ''.join('%s\n' % key(h) for h in sorted(hits, key=key)))
        print('baseline written: %d site(s)' % len(hits))
        return 0

    base = load_baseline()
    new = [h for h in hits if key(h) not in base]
    print('=' * 44)
    print('  universal-negative check')
    print('  sites found              : %d' % len(hits))
    print('  grandfathered (baseline) : %d' % len(base))
    print('  NEW undated negatives    : %d' % len(new))
    print('=' * 44)
    for rel, line, matched, sent in new:
        print('  %s:%d  [%s]' % (rel, line, matched))
        print('      %s' % sent)
    if '--record' in argv:
        rc = _record(new, argv)
        if rc:
            return rc

    if new:
        print('\nA universal negative with no date and no search record.')
        print('The honest form is "none located as of <date>, searched as follows".')
        print('Fix the finding, or ledger it in .claude-local/DEFECTS.md.')
        return 1 if '--block' in argv else 0
    print('OK: no new undated universal negatives.')
    return 0


def _record(new, argv):
    """The universe is THIS checker's own scope — never a shared roster."""
    return common.record_if_asked('check_negatives', [rel for _p, rel in targets()],
                                  {h[0] for h in new}, 'undated universal negative', argv,
                                  switches=['tools/verify/negatives_baseline.txt'])


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
