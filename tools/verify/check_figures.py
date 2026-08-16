"""Recorded figures — DC-6. A count copied into prose from something that can change.

THE RULE IT ENFORCES, which this project states in three separate places for three separate
figures: **do not write down a count of an artifact set; measure it on demand.** A number in prose
is a claim that cannot check itself, and the artifact moves without telling it.

MEASURED COST, all three from this repo's own history:
  * the `papers/` count — recorded as "55 files, of which 43 are PDFs", went stale by 15 in a day;
  * the choice-footprint count — wrong three times, once quoted rather than measured, once stale
    within a single session;
  * the `LEAN_CUSTOM_REGISTRY` tally — 18 days stale, discovered AT a release threshold.

THE LEGITIMATE FORM IS A DATED SURVEY. "70 files as of 2026-08-02" is a measurement with a
timestamp; a reader knows exactly how much to trust it. "70 files" is a claim about now, forever.

WHAT IT DELIBERATELY DOES NOT FLAG
  * mathematics — `Fin 3`, "two poles", "the five KINDS", arities, ordinals. These are not artifact
    counts and never go stale.
  * anything already carrying a date, or explicitly deferred to a measurement.
  * numbers in CODE. A `len(x) == 5` is not a recorded figure; only PROSE is scanned — comments,
    docstrings and markdown.

Usage (the exact invocation path is printed in this tool's own output):
  check_figures.py            # WARN (advisory, exit 0)
  check_figures.py --block    # exit 1 on any NEW unbaselined site
  check_figures.py --baseline # rewrite the baseline from current state
  check_figures.py --selftest # must-fire AND must-suppress controls
"""
import hashlib
import io
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SELF = Path(__file__).resolve().relative_to(ROOT).as_posix()
BASELINE = HERE / 'figures_baseline.txt'

sys.path.insert(0, str(HERE))
from vendored import is_vendored          # noqa: E402
import report                              # noqa: F401,E402  (utf-8 stdout, side effect)

# ── the countable artifacts ──────────────────────────────────────────────────────────────────
# Deliberately NARROW. Every noun here names a set that GROWS OR SHRINKS as work happens, which is
# the entire defect: the prose is right on the day it is written and wrong afterwards.
#
# ⚠ NOT included, on purpose: `theorems`, `lemmas`, `axioms`, `points`, `states`, `kinds`, `faces`,
# `poles`, `roots`. Those are either mathematics or a FIXED conceptual enumeration ("the five
# KINDS", "two poles") that does not drift with the tree. Adding them would flag the framework's
# own vocabulary and get this gate muted.
_ARTIFACT = (r"files?|declarations?|decls?|sites?|papers?|entries|entry|rows?|checkers?|"
             r"occurrences?|hits?|violations?|instances?|modules?|scripts?|commits?|"
             r"baselines?|notes?|defects?")

# "55 files", "2494 declarations", "17 sites", "of which 43 are PDFs"
FIGURE = re.compile(r"\b(\d{2,})\s+(?:%s)\b" % _ARTIFACT, re.I)

# ── what makes a figure honest ───────────────────────────────────────────────────────────────
# A DATE, or an explicit deferral to measurement. Nothing else: the whole point is that a bare
# number is unverifiable from where it is written.
EVIDENCE = re.compile(
    r"\bas\s+of\b|"
    r"\b20\d\d-\d\d-\d\d\b|"
    r"\bmeasured\b|"
    r"\bmeasure\s+(?:it|on\s+demand)\b|"
    r"\bnever\s+record\b|"
    r"\bdo\s+not\s+record\b|"
    r"\bre-?measure\b|"
    r"\bcomputed\s+now\b|"
    r"\bat\s+the\s+time\b|"
    r"\bwas\s+stale\b|\bwent\s+stale\b|\bstale\s+by\b|"   # prose ABOUT the defect
    r"\bcorrected\b|\bretract",
    re.I)

SKIP_NAMES = {'CLAUDE.md', 'check_figures.py', 'figures_baseline.txt',
              'register.md', 'RELEASES.md'}
SKIP_DIRS = ('.lake', '.git', 'notes', 'papers', 'archive', 'feedback', 'outreach',
             'autobiography', '__pycache__', 'deepseek', 'fonts')


def prose_lines(text, suffix):
    """(line_no, text) for PROSE only. A number in code is not a recorded figure.

    ⚠ This filter is why the checker is usable. Scanning whole `.py`/`.lean` files would match
    every `Fin 12`, every array index and every line-number citation, and a gate that fires on
    code gets muted within a day."""
    out = []
    if suffix == '.md':
        return list(enumerate(text.split('\n'), 1))
    in_doc = False
    for i, line in enumerate(text.split('\n'), 1):
        s = line.strip()
        if suffix == '.lean':
            if s.startswith('/-') or s.startswith('-/'):
                in_doc = not s.endswith('-/') if s.startswith('/-') else False
                out.append((i, line))
                continue
            if in_doc or s.startswith('--'):
                out.append((i, line))
        else:                                    # .py
            if s.startswith('"""') or s.endswith('"""'):
                in_doc = not in_doc
                out.append((i, line))
                continue
            if in_doc or s.startswith('#'):
                out.append((i, line))
    return out


def targets():
    for pat in ('ZeroParadox/**/*.lean', '*.md', 'scripts/*.py', 'tools/**/*.py'):
        for p in ROOT.glob(pat):
            rel = p.relative_to(ROOT).as_posix()
            if p.name in SKIP_NAMES or any(('/' + d + '/') in ('/' + rel) for d in SKIP_DIRS):
                continue
            if is_vendored(p, rel):
                continue
            yield p, rel


def scan_text(text, suffix='.md'):
    """(line, matched, context) for every undated artifact count in PROSE."""
    out = []
    for lineno, line in prose_lines(text, suffix):
        for m in FIGURE.finditer(line):
            if EVIDENCE.search(line):
                continue
            out.append((lineno, m.group(0).strip(), ' '.join(line.split())[:150]))
    return out


def scan():
    hits = []
    for p, rel in targets():
        try:
            t = io.open(p, encoding='utf-8').read()
        except (OSError, UnicodeDecodeError):
            continue
        for line, matched, ctx in scan_text(t, p.suffix):
            hits.append((rel, line, matched, ctx))
    return hits


def key(h):
    return '%s::%s' % (h[0], hashlib.sha256(h[3].encode('utf-8')).hexdigest()[:12])


def load_baseline():
    if not BASELINE.exists():
        return set()
    return {l.strip() for l in io.open(BASELINE, encoding='utf-8-sig').read().splitlines()
            if l.strip() and not l.startswith('#')}


def selftest():
    bad = 0
    fire = [
        # ⚠ THE THREE REAL ONES, from this project's own recorded history.
        ('the papers count (stale by 15)', '-- The library holds 55 files, of which 43 are PDFs.'),
        ('a corpus declaration count', '-- Snapshot.lean runs over 2494 declarations every build.'),
        ('a site count', '-- The wording survey found 25 sites citing this docstring.'),
        ('an entry tally', '# The registry carries 18 entries for custom declarations.'),
    ]
    suppress = [
        ('dated: "as of"', '-- 70 files as of 2026-08-02, measured not quoted.'),
        ('an ISO date present', '-- 862 sites remain (2026-08-15).'),
        ('explicitly measured', '-- measured 2026-08-15: 17 sites in 8 files.'),
        ('the do-not-record rule itself', '-- NO COUNT: never record 55 files; measure on demand.'),
        ('prose ABOUT the staleness', '-- this line said 55 files and went stale by 15.'),
        # ⚠ MATHEMATICS AND FIXED ENUMERATIONS. Flagging these would fire on the framework's own
        # vocabulary; they do not drift with the tree.
        ('an arity', '-- the fan-out needs 3 pairwise-incomparable successors.'),
        ('a fixed conceptual list', '-- the five KINDS: coincidence, inversion, drift, carrier, invariant.'),
        ('an ordinal', '-- omega-tower iteration reaches 2 levels above the base.'),
        ('a version string', '-- corrected in ZP-P v1.21 after the gate round.'),
        # ⚠ CODE IS NOT PROSE. This is the control that keeps the checker usable at all.
        ('a code line, not a comment', 'assert len(rows) == 25 and len(cols) == 40'),
        ('a Lean term', 'def probe : Fin 12 := ⟨7, by decide⟩'),
    ]

    print('  MUST FIRE')
    for label, text in fire:
        got = scan_text(text, '.lean' if text.strip().startswith('--') else '.py')
        ok = bool(got)
        bad += 0 if ok else 1
        print('    %-34s %s' % (label, 'ok' if ok else '*** MISSED ***'))
    print('  MUST SUPPRESS')
    for label, text in suppress:
        suffix = '.lean' if text.strip().startswith(('--', 'def')) else '.py'
        got = scan_text(text, suffix)
        ok = not got
        bad += 0 if ok else 1
        print('    %-34s %s%s' % (label, 'ok' if ok else '*** FALSE POSITIVE ***',
                                  '' if ok else '  -> ' + got[0][1]))
    print('\n  selftest: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return 1 if bad else 0


def main(argv):
    if '--selftest' in argv:
        print('=' * 44)
        print('  recorded-figure check - CONTROLS')
        print('=' * 44)
        return selftest()

    hits = scan()
    if '--baseline' in argv:
        io.open(BASELINE, 'w', encoding='utf-8', newline='\n').write(
            '# Undated artifact counts present when this baseline was taken.\n'
            '# The honest form is a DATED survey: "70 files as of 2026-08-02".\n'
            '# SHRINK this list as files are touched; never grow it.\n'
            '# Refresh with:  python %s --baseline\n' % SELF
            + ''.join('%s\n' % key(h) for h in sorted(hits, key=key)))
        print('baseline written: %d site(s)' % len(hits))
        return 0

    base = load_baseline()
    new = [h for h in hits if key(h) not in base]
    print('=' * 44)
    print('  recorded-figure check')
    print('  sites found              : %d' % len(hits))
    print('  grandfathered (baseline) : %d' % len(base))
    print('  NEW undated figures      : %d' % len(new))
    print('=' * 44)
    for rel, line, matched, ctx in new:
        print('  %s:%d  [%s]' % (rel, line, matched))
        print('      %s' % ctx)
    if new:
        print('\nAn artifact count recorded in prose, with no date.')
        print('Prefer measuring on demand; if it must be written, date it.')
        return 1 if '--block' in argv else 0
    print('OK: no new undated artifact counts.')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
