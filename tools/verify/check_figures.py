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
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common                              # noqa: E402
# ⚠ ONE DEFINITION. The markdown glob had three copies and a fix reached two of them; see
# `common.tracked_md`. Until 2026-08-16 this line imported it FROM `check_modal`, which made a peer
# checker into a library (`DEFECTS.md` MIG-3) — the cheap move, not the right one. Shared machinery
# belongs in a module that checks nothing.
from common import HERE, REPO              # noqa: E402
from vendored import is_vendored           # noqa: E402
import report                              # noqa: F401,E402  (utf-8 stdout, side effect)

SELF = common.self_rel(__file__)
BASELINE = HERE / 'figures_baseline.txt'

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

# The shared skips live in `common.SKIP_NAMES`; only this checker's own source and baseline are
# genuinely its own. `common.SKIP_DIRS` carries the union of what the three copies of this constant
# used to hold — measured inert before merging, since the globs cannot yield a `.pyc` or a `.ttf`.
SKIP_NAMES = {'check_figures.py', 'figures_baseline.txt'}


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
            # ⚠ A ONE-LINE DOCSTRING MUST NOT TOGGLE THE STATE. `"""text."""` both starts and ends
            # with the delimiter, so `startswith or endswith` flips `in_doc` ON and never back —
            # and every subsequent line of CODE then counts as prose.
            #
            # Measured 2026-08-15: adding a single one-line docstring to `batch.py` made this
            # checker "discover" a pre-existing figure 200 lines further down and block a push.
            # That is the worst shape of false positive, because the site it reports is nowhere
            # near the cause, and the obvious reading is that the reported line is new.
            triple = s.count('"""')
            if triple >= 2:                      # opens and closes on the same line
                out.append((i, line))
                continue
            if triple == 1:
                in_doc = not in_doc
                out.append((i, line))
                continue
            if in_doc or s.startswith('#'):
                out.append((i, line))
    return out


def targets():
    return common.targets(skip_names=SKIP_NAMES, is_vendored=is_vendored)


# How far from a figure its date may sit, in lines, within one CONTIGUOUS prose run.
#
# ⚠ NOT ZERO, AND NOT UNBOUNDED - both errors are recorded in this project's history.
# ZERO (the original) blocked a push on TWO FALSE POSITIVES in `check_hashes.py`, whose figures were
# dated two lines below in the same comment: prose WRAPS, and a one-line evidence window cannot see a
# wrapped sentence. That is `check_modal`'s literal-space bug arriving from the other side - there the
# CLAIM wrapped out of range, here the EVIDENCE does.
# UNBOUNDED is the opposite failure, also measured: `check_modal` once passed a live claim because the
# word "measured" sat six lines away describing a DIFFERENT measurement. **Proximity is not aboutness.**
# Three lines is enough for a wrapped sentence and too few to borrow an unrelated date.
EVIDENCE_WINDOW = 3


def scan_text(text, suffix='.md'):
    """(line, matched, context) for every undated artifact count in PROSE."""
    prose = prose_lines(text, suffix)
    by_line = dict(prose)
    out = []
    for lineno, line in prose:
        for m in FIGURE.finditer(line):
            # The window walks only CONTIGUOUS prose: a gap means a different block, and a date on
            # the far side of code is not this figure's date.
            window = [line]
            for step in (-1, 1):
                for d in range(1, EVIDENCE_WINDOW + 1):
                    nxt = by_line.get(lineno + step * d)
                    if nxt is None:
                        break
                    window.append(nxt)
            if EVIDENCE.search(' '.join(window)):
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
    return common.load_baseline(BASELINE)


# --------------------------------------------------------------------------- controls
# ⚠ MODULE-LEVEL, so `check_checkers.py` can audit that this checker ships controls at all.
MUST_FIRE = [
        # ⚠ THE THREE REAL ONES, from this project's own recorded history.
        ('the papers count (stale by 15)', '-- The library holds 55 files, of which 43 are PDFs.'),
        ('a corpus declaration count', '-- Snapshot.lean runs over 2494 declarations every build.'),
        ('a site count', '-- The wording survey found 25 sites citing this docstring.'),
        ('an entry tally', '# The registry carries 18 entries for custom declarations.'),
        # ⚠ THE BOUND, in the direction that matters: a date FAR away must NOT discharge a figure.
        # Without this control, widening the window to fix the wrapped case would have been
        # unfalsifiable - and "proximity is not aboutness" is the failure check_modal already paid for.
        ('a figure whose only nearby date is 5 lines off',
         '# The survey found 25 sites citing this docstring.\n#\n#\n#\n#\n# (measured 2026-08-18).'),
]
MUST_SUPPRESS = [
        # ⚠ THE WRAPPED CASE, which the one-line window could not see and which blocked a push
        # (/rely round 5). The figure and its date are in one sentence split across two lines.
        ('a WRAPPED figure whose date is on the next line',
         '# 13 of 43 scripts use it - so they were silently exempt\n# (/rely, 2026-08-18).'),
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
        # ⚠ THE STATE-MACHINE CONTROL. A one-line docstring must not leave `in_doc` stuck
        # ON. When it did, every line of CODE after it counted as prose and this checker
        # reported a pre-existing figure 200 lines away as NEW, blocking a push.
        ('code after a 1-line docstring', 'def f():\n    """One line."""\n    return tally(1847, sites)'),
        ('a Lean term', 'def probe : Fin 12 := ⟨7, by decide⟩'),
]


def _fire_probe(text):
    return scan_text(text, '.lean' if text.strip().startswith('--') else '.py')


def _suppress_probe(text):
    # ⚠ The suffix rule differs between the two groups and always has: a suppression control may be
    # a bare `def` line with no comment marker, which must still be read as Lean. Kept as two named
    # probes rather than one clever expression, because the difference is the point.
    return scan_text(text, '.lean' if text.strip().startswith(('--', 'def')) else '.py')


def selftest():
    bad = common.run_controls([
        ('  MUST FIRE', MUST_FIRE, _fire_probe, True, 'MISSED'),
        ('  MUST SUPPRESS', MUST_SUPPRESS, _suppress_probe, False, 'FALSE POSITIVE',
         lambda text: '  -> ' + _suppress_probe(text)[0][1]),
    ])
    # ⚠ THE VOCABULARY PIN (PAT-1). The controls above prove the patterns they exercise;
    # this proves the rest are still there. Measured before it was written: 30 of 34
    # list-shaped patterns could be deleted with every control green, and ~39 compiled
    # regexes carrying the rest of the vocabulary were pinned by nothing at all.
    print('  PATTERNS')
    bad += common.check_vocabulary('check_figures', globals())
    if bad:
        print('\nselftest: FAIL (%d)' % bad)
    return 1 if bad else 0


def main(argv):
    if '--selftest' in argv:
        print('=' * 44)
        print('  recorded-figure check - CONTROLS')
        print('=' * 44)
        return selftest()

    hits = scan()
    if '--baseline' in argv:
        common.refuse_baseline_write('figures_baseline.txt')
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
    if '--record' in argv:
        rc = _record(new, argv)
        if rc:
            return rc

    if new:
        print('\nAn artifact count recorded in prose, with no date.')
        print('Prefer measuring on demand; if it must be written, date it.')
        return 1 if '--block' in argv else 0
    print('OK: no new undated artifact counts.')
    return 0


def _record(new, argv):
    """The universe is THIS checker's own scope — never a shared roster."""
    return common.record_if_asked('check_figures', [rel for _p, rel in targets()],
                                  {h[0] for h in new}, 'undated artifact count', argv,
                                  switches=['tools/verify/figures_baseline.txt'])


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
