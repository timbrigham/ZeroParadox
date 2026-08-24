#!/usr/bin/env python3
"""Enforce the CLAUDE.md shape contract.

Body: tools/process/claude-md-maintenance.md (the skill that defines the contract).

Legs are split by KIND, per the downgrade rule: a leg guarding a FAIL-OPEN surface blocks;
an ENUMERATION leg warns. Legs that CANNOT yet be enforced are declared PENDING and are
never silently counted as passing -- a gate reporting `pass` for a property it does not
check is the RLY25-1 defect this file exists to avoid.
"""
import io, os, re, sys, argparse

sys.stdout.reconfigure(encoding='utf-8', errors='replace')

SELF = os.path.relpath(os.path.abspath(__file__), os.getcwd()).replace(os.sep, '/')
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TARGET = os.path.join(ROOT, 'CLAUDE.md')
LINE_CAP = 12

# --- leg registry. `mode` is DATA, never a literal at the call site, so a control can read it.
LEGS = [
    ('paths',    'BLOCK',   'every ROOTED repo-relative path resolves on disk (CM-9/CM-10)'),
    ('checkers', 'BLOCK',   'every checker named in CLAUDE.md exists'),
    ('unrooted', 'WARN',    'bare-basename / partial file citations (as-touched rollout debt)'),
    ('cap',      'WARN',    'entries over the %d-line cap (CM-1 proxy)' % LINE_CAP),
    ('history',  'WARN',    'prior-state prose (CM-2)'),
    ('enum',     'WARN',    'duplicated enumeration / completeness claims (CM-3)'),
    ('trigger',  'PENDING', 'every entry has a TRIGGER line -- needs the four-part form; arms after Phase 1'),
    ('budget',   'PENDING', 'net lines added while over cap -- the cap is set BY MEASUREMENT after Phase 1'),
    ('cites',    'PENDING', 'per-ID citation counts (CM-5) -- needs stable entry IDs; arms after Phase 1'),
]
BLOCKING = [n for n, m, _ in LEGS if m == 'BLOCK']
PENDING = [n for n, m, _ in LEGS if m == 'PENDING']

PLACEHOLDER = re.compile(r'[<>*?]|YYYY|MM-DD|<name>')

# Transient DESTINATIONS: paths a tool WRITES rather than paths this file tells you to READ.
# They are legitimately absent between runs, so a resolve-check on them measures when the
# checker ran, not whether the pointer is good. Explicit, each with a reason, and the count
# is PRINTED on every run -- a silent exclusion list is how suppression stops being noticed.
TRANSIENT = {
    '.claude-local/er_cleared.txt': 'editorial-review signal, written per-push by the gate',
    '.claude-local/ar_cleared.txt': 'adversary-review signal, written per-push by the gate',
    '.claude-local/pa_cleared.txt': 'prior-art signal, written per-push by the gate',
}
PATHISH = re.compile(r'^[\w.\-/]+\.(md|py|lean|json|txt|sh|yml|yaml|ps1)$')
BACKTICKED = re.compile(r'`([^`\n]+)`')
CHECKER_NAMED = re.compile(r'`(check_\w+\.py|guards\.py|batch\.py|hooks\.py|report\.py)`')
HISTORY_IDIOMS = re.compile(
    r'this line said|used to read|used to say|previously read|was FALSE|'
    r'until 2026-|an earlier draft|is retracted|corrected 2026-', re.I)
ENUM_IDIOMS = re.compile(
    r'\bthe (two|three|four|five|six|seven|eight|nine|ten|\d+) '
    r'(conditions|fields|clauses|members|entries|files|rows)\b', re.I)


def sections(lines):
    idx = [i for i, l in enumerate(lines) if l.startswith('## ')]
    out = []
    for n, i in enumerate(idx):
        end = idx[n + 1] if n + 1 < len(idx) else len(lines)
        out.append((i + 1, lines[i][3:].strip(), end - i))
    return out


def cited_paths(text):
    """Split by kind: a ROOTED repo-relative path is decidable and blocks; a bare basename
    or a partial path is citation-convention debt (as-touched rollout) and only warns.
    Blocking on the second would fire on legitimate flowing prose, and on `Foo.md`
    hypotheticals the file uses to state a rule."""
    roots = set(os.listdir(ROOT))
    rooted, loose = {}, {}
    for m in BACKTICKED.finditer(text):
        tok = m.group(1).strip()
        if PLACEHOLDER.search(tok) or tok.startswith(('http', 'C:', 'origin/')):
            continue
        if not PATHISH.match(tok):
            continue
        ln = text[:m.start()].count('\n') + 1
        if '/' in tok and tok.split('/')[0] in roots:
            rooted.setdefault(tok, ln)
        else:
            loose.setdefault(tok, ln)
    return rooted, loose


def manifest(lines, secs):
    print('=' * 78)
    print('  CLAUDE.md SHAPE CONTRACT')
    print('=' * 78)
    print('  entry      python %s' % SELF)
    print('  target     CLAUDE.md (%d lines, %d sections)' % (len(lines), len(secs)))
    print('  body       tools/process/claude-md-maintenance.md')
    print('  plan       %d leg(s): %d BLOCK, %d WARN, %d PENDING'
          % (len(LEGS), len(BLOCKING),
             sum(1 for _, m, _ in LEGS if m == 'WARN'), len(PENDING)))
    for n, m, d in LEGS:
        print('      %-9s %-8s %s' % (n, m, d))
    print('  ' + '-' * 74)
    print('  PENDING legs are NOT checked and NOT passing. A clear run below is not')
    print('  evidence about them. Arming them is the point of the Phase 1 sweep.')
    print('=' * 78)


def blocking_failures(text):
    """The two BLOCK legs, evaluated against `text`. Returns a list of failure strings.

    Factored out so --selftest exercises THE SAME CODE the push gate runs. A control that
    re-implements the logic it is testing proves nothing about the logic that ships.
    """
    fails = []
    rooted, _ = cited_paths(text)
    missing = [p for p in rooted
               if not os.path.exists(os.path.join(ROOT, p)) and p not in TRANSIENT]
    if missing:
        fails.append('paths:' + ','.join(sorted(missing)))
    absent = [c for c in sorted(set(CHECKER_NAMED.findall(text)))
              if not os.path.exists(os.path.join(ROOT, 'tools', 'verify', c))]
    if absent:
        fails.append('checkers:' + ','.join(absent))
    return fails


def selftest():
    """Both halves, per check_checkers rule 3. A must-fire half alone is half-tested."""
    cases = [
        # (name, text, must_fire)
        ('clean-rooted-path',   'see `tools/verify/check_claude_md.py` for the contract.', False),
        ('clean-named-checker', 'run `check_encoding.py` before every commit.',            False),
        ('transient-excluded',  'the gate writes `.claude-local/er_cleared.txt` on pass.',  False),
        ('placeholder-skipped', 'name it `.claude-local/notes/scan_YYYY-MM-DD.md`.',        False),
        ('broken-rooted-path',  'open `tools/process/definitely_not_here.md` first.',       True),
        ('missing-checker',     'run `check_definitely_absent.py` before committing.',      True),
    ]
    bad = 0
    for name, text, must_fire in cases:
        fired = bool(blocking_failures(text))
        ok = (fired == must_fire)
        if not ok:
            bad += 1
        print('  %-22s %-14s expected %-6s got %-6s %s'
              % (name, 'MUST FIRE' if must_fire else 'MUST SUPPRESS',
                 must_fire, fired, 'ok' if ok else 'FAIL'))
    print('\nselftest: %s (%d/%d) - FIRES on %d planted defect(s), SUPPRESSES on %d clean case(s)'
          % ('PASS' if not bad else 'FAIL', len(cases) - bad, len(cases),
             sum(1 for c in cases if c[2]), sum(1 for c in cases if not c[2])))
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--measure', action='store_true',
                    help='Phase 0: print the section manifest and stop')
    ap.add_argument('--selftest', action='store_true',
                    help='run the controls for this checker (both halves)')
    args = ap.parse_args()

    if args.selftest:
        print('check_claude_md.py --selftest: controls for the two BLOCK legs\n')
        return selftest()

    text = io.open(TARGET, encoding='utf-8').read()
    lines = text.split('\n')
    secs = sections(lines)
    manifest(lines, secs)

    if args.measure:
        print('\nPhase 0 -- section manifest (line counts include the heading):\n')
        for ln, title, count in sorted(secs, key=lambda s: -s[2]):
            flag = '  OVER' if count > LINE_CAP else ''
            print('  %5d  :%-5d  %s%s' % (count, ln, title[:70], flag))
        over = [s for s in secs if s[2] > LINE_CAP]
        med = sorted(s[2] for s in secs)[len(secs) // 2]
        print('\n  sections %d | over cap %d | median %d | in-section lines %d'
              % (len(secs), len(over), med, sum(s[2] for s in secs)))
        print('  Record this in the pass note, never in CLAUDE.md.')
        return 0

    bad = 0

    # --- BLOCK: rooted paths resolve -----------------------------------------
    rooted, loose = cited_paths(text)
    missing = {p: ln for p, ln in rooted.items()
               if not os.path.exists(os.path.join(ROOT, p)) and p not in TRANSIENT}
    skipped = sum(1 for p in rooted if p in TRANSIENT)
    if missing:
        bad += 1
        print('\n  paths            FAIL  %d rooted path(s) do not resolve' % len(missing))
        for p, ln in sorted(missing.items()):
            print('      CLAUDE.md:%d  %s' % (ln, p))
    else:
        print('\n  paths            ok    all %d rooted paths resolve' % len(rooted))
    print('                         (%d transient destination(s) excluded by name, see TRANSIENT)'
          % skipped)

    # --- BLOCK: named checkers exist -----------------------------------------
    named = sorted(set(CHECKER_NAMED.findall(text)))
    absent = [c for c in named
              if not os.path.exists(os.path.join(ROOT, 'tools', 'verify', c))]
    if absent:
        bad += 1
        print('  checkers         FAIL  %d named checker(s) missing: %s'
              % (len(absent), ', '.join(absent)))
    else:
        print('  checkers         ok    all %d named checkers exist' % len(named))

    # --- WARN legs. Counts printed on EVERY run, blocked or clear. -----------
    print('  unrooted         WARN  %d bare/partial file citation(s) '
          '(as-touched debt, not a broken pointer)' % len(loose))

    over = [s for s in secs if s[2] > LINE_CAP]
    print('  cap              WARN  %d/%d entries over the %d-line cap (worst: %d)'
          % (len(over), len(secs), LINE_CAP, max([s[2] for s in over] or [0])))

    hist = [(i + 1, l) for i, l in enumerate(lines) if HISTORY_IDIOMS.search(l)]
    print('  history          WARN  %d prior-state-prose hit(s) (CM-2)' % len(hist))
    for ln, l in hist[:5]:
        print('      CLAUDE.md:%d  %s' % (ln, l.strip()[:64]))
    if len(hist) > 5:
        print('      ... and %d more' % (len(hist) - 5))

    enum = [(i + 1, l) for i, l in enumerate(lines) if ENUM_IDIOMS.search(l)]
    print('  enum             WARN  %d completeness-claim hit(s) (CM-3)' % len(enum))
    for ln, l in enum[:3]:
        print('      CLAUDE.md:%d  %s' % (ln, l.strip()[:64]))

    print('\n' + '=' * 78)
    if bad:
        print('BLOCKED: %d blocking leg(s) failed. %d leg(s) still PENDING.'
              % (bad, len(PENDING)))
        return 1
    print('OK: %d blocking leg(s) clear. WARN counts above are a READING LIST, '
          'not a pass. %d leg(s) PENDING.' % (len(BLOCKING), len(PENDING)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
