#!/usr/bin/env python3
"""Enforce the CLAUDE.md shape contract.

Body: tools/process/claude-md-maintenance.md (the skill that defines the contract).

Legs are split by KIND, per the downgrade rule: a leg guarding a FAIL-OPEN surface blocks;
an ENUMERATION leg warns. Legs that CANNOT yet be enforced are declared PENDING and are
never silently counted as passing -- a gate reporting `pass` for a property it does not
check is the RLY25-1 defect this file exists to avoid.
"""
import io, os, re, sys, argparse

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402  (path set above so this runs from any cwd, as the other checkers do)

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
# ⚠ EMPTY, AND THAT IS THE CURRENT STATE, not an unfinished edit. Its three members were
# `er/ar/pa_cleared.txt`, and the `*_cleared.txt` scheme was RETIRED 2026-08-24 — review coverage
# is a verdictLedger RECORD now, so nothing writes those paths and CLAUDE.md no longer names them.
# Suppressing them TODAY would be backwards: a CLAUDE.md that named one again would be citing a
# path nothing writes, which is precisely the dead pointer this leg exists to catch. Removed
# 2026-09-01, and the printed count is how it was found — the run said "0 transient destination(s)
# excluded by name" while three sat in the list. The mechanism stays; only its members went.
TRANSIENT = {}
# Roots that belong to a DIFFERENT repository. Neither their presence nor their absence here is
# evidence about the pointer, so they are classified by PREFIX rather than by what is on disk —
# the classification must not change when the directory does. See the note in `offer`.
EXTERNAL_ROOTS = ('.claude-local/',)
PATHISH = re.compile(r'^[\w.\-/]+\.(md|py|lean|json|txt|sh|yml|yaml|ps1)$')
BACKTICKED = re.compile(r'`([^`\n]+)`')
# ⚠ `READ <path>` — 37 uses in CLAUDE.md, and the paths leg could not see one of them
# until 2026-08-27 (RLY37-1). It is this file's dominant pointer idiom.
READ_LINE = re.compile(r'^READ\s+(\S+)', re.M)
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
    rooted, loose, external = {}, {}, {}

    def offer(tok, ln):
        if tok.startswith(('http', 'C:', 'origin/')) or not PATHISH.match(tok):
            return
        # ⚠⚠ THIS BRANCH IS WHY THE LEG'S SEVERITY USED TO DEPEND ON THE MACHINE. `roots` is
        # `os.listdir(ROOT)`, and `.claude-local/` is GITIGNORED — present here, absent in a fresh
        # clone and on CI. So the same CLAUDE.md put every `.claude-local/...` citation in the
        # BLOCK bucket on Tim's box and the WARN bucket everywhere else, and the run printed the
        # identical "ok all N rooted paths resolve" either way, N quietly smaller. A shrunken claim
        # rendered exactly like the full one. Measured 2026-09-01 by listing ROOT without it.
        # These paths are not checkable from here in EITHER direction: `.claude-local` is its own
        # repository (R-CONTEXT), so its absence is not evidence of a dead pointer and its presence
        # is not evidence of a live one. Third bucket, COUNTED and PRINTED — same idiom as
        # TRANSIENT, because an exclusion nobody counts is how coverage silently shrinks.
        if tok.startswith(EXTERNAL_ROOTS):
            external.setdefault(tok, ln)
        elif '/' in tok and tok.split('/')[0] in roots:
            rooted.setdefault(tok, ln)
        else:
            loose.setdefault(tok, ln)

    for m in BACKTICKED.finditer(text):
        ln = text[:m.start()].count('\n') + 1
        # ⚠ SPLIT, don't DISCARD. A backticked COMMAND carries a real path beside a
        # placeholder argument — `python tools/verify/check_release_ready.py <tag>` is the
        # R-RELEASE idiom, and dropping the whole token on `[<>*?]` threw the path away with
        # the placeholder. Strip the placeholder ARGUMENTS; keep the parts that are paths.
        for part in m.group(1).strip().split():
            if PLACEHOLDER.search(part):
                continue
            offer(part, ln)

    # ⚠ `READ <path>` IS THIS FILE'S DOMINANT POINTER IDIOM AND WAS INVISIBLE HERE.
    # RLY37-1, 2026-08-27: the leg advertised "every ROOTED repo-relative path resolves" while
    # walking backticked tokens ONLY. Measured on the live file: 37 `READ` lines, ZERO of them
    # in this set. `guards.py` states CLAUDE.md is "routed NOWHERE by design", so this leg is
    # one of the file's only two mechanical covers — and `DC-34` (a stale routing destination)
    # is exactly a dead READ line, filed the same day this hole was found.
    for m in READ_LINE.finditer(text):
        offer(m.group(1).strip(), text[:m.start()].count('\n') + 1)

    return rooted, loose, external


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
    rooted, _, _ = cited_paths(text)
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
        # ⚠ THIS ROW USED TO BE `transient-excluded`, must_fire=False, and it was green for a
        # reason that had nothing to do with what it claimed to test. It asserted `er_cleared.txt`
        # was suppressed BY TRANSIENT; measured 2026-09-01, TRANSIENT excluded nothing (the run
        # printed "0 transient destination(s)") and the row passed anyway, because the retired
        # file is still sitting on disk from the day the scheme was retired, so the path resolves.
        # Three independent reasons to pass, one asserted, none checked. It is now a `.claude-local`
        # row: those never block, whether or not the file is there — which is the property that
        # actually holds. The TRANSIENT mechanism gets its own both-halves control below.
        ('external-repo-path',  'the gate writes `.claude-local/er_cleared.txt` on pass.',  False),
        ('external-repo-absent', 'see `.claude-local/notes/definitely_not_here.md` first.', False),
        ('placeholder-skipped', 'name it `.claude-local/notes/scan_YYYY-MM-DD.md`.',        False),
        ('broken-rooted-path',  'open `tools/process/definitely_not_here.md` first.',       True),
        ('missing-checker',     'run `check_definitely_absent.py` before committing.',      True),
        # RLY37-1 (2026-08-27). The leg walked BACKTICKED tokens only, so `READ <path>` --
        # this file's dominant pointer idiom, 37 uses -- was invisible, and a dead READ line
        # is exactly what DC-34 (stale routing destination) looks like. Both halves, because
        # a must-fire alone would also pass if the new harvester matched everything.
        ('read-line-live',      'READ     tools/process/pipeline.md',                      False),
        ('read-line-dead',      'READ     tools/process/definitely_not_here.md',            True),
        # And the placeholder filter DISCARDED whole commands rather than the placeholder
        # argument, dropping the R-RELEASE idiom's real path with it.
        ('cmd-placeholder-live', 'run `python tools/verify/check_hashes.py <tag>` first.',  False),
        ('cmd-placeholder-dead', 'run `python tools/verify/check_absent.py <tag>` first.',  True),
    ]
    bad = 0

    # The TRANSIENT mechanism itself, exercised on a member that exists only for these two lines.
    # Both halves, against the SAME dict `blocking_failures` reads: absent -> must fire, present ->
    # must suppress. Without this the exclusion path would be untested code the moment the list
    # emptied, and a suppression route nobody has seen work is not a mechanism, it is a hope.
    SYN = 'tools/verify/_synthetic_transient_destination.json'
    syn_text = 'the batch writes `%s` between runs.' % SYN
    if not blocking_failures(syn_text):
        print('  %-22s %-14s expected %-6s got %-6s FAIL'
              % ('transient-mechanism', 'MUST FIRE', True, False))
        bad += 1
    TRANSIENT[SYN] = 'synthetic, installed by --selftest only'
    try:
        fired = bool(blocking_failures(syn_text))
    finally:
        del TRANSIENT[SYN]
    print('  %-22s %-14s expected %-6s got %-6s %s'
          % ('transient-mechanism', 'BOTH HALVES', False, fired, 'ok' if not fired else 'FAIL'))
    if fired:
        bad += 1

    # ⚠⚠ THE CONTROL THIS CHECKER DID NOT HAVE, and its absence is what hid the defect above.
    # Every case here runs on a machine where `.claude-local/` EXISTS. The leg classified by
    # `os.listdir(ROOT)`, so on a fresh clone or CI the same text took a different branch and the
    # BLOCK bucket silently shrank. Re-running the whole case list against a ROOT with the
    # gitignored directory hidden is the state nobody tested; the verdicts must be identical in
    # both, and that INVARIANCE is the property, not either verdict on its own.
    real_listdir = os.listdir
    os.listdir = lambda p: [x for x in real_listdir(p) if x != '.claude-local']
    try:
        no_local = {n: bool(blocking_failures(t)) for n, t, _ in cases}
    finally:
        os.listdir = real_listdir

    drift = [n for n, t, _ in cases if no_local[n] != bool(blocking_failures(t))]
    print('  %-22s %-14s expected %-6s got %-6s %s'
          % ('listdir-invariance', 'BOTH ROOTS', 0, len(drift),
             'ok' if not drift else 'FAIL ' + ','.join(drift)))
    bad += 1 if drift else 0

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
    # ⚠ DECLARED, not merely read. `record_if_asked` gates on `--record` in `sys.argv`, but
    # argparse rejects an undeclared flag BEFORE the checker body runs — measured 2026-08-26,
    # `--record` exited 2 with "unrecognized arguments" and recorded nothing, which reads
    # identically to a ledger refusal at the call site in `hooks.py`.
    ap.add_argument('--record', action='store_true',
                    help='record the two BLOCKING legs to the verdictLedger (V9 needs ZPLEDGER_RUN)')
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
    rooted, loose, external = cited_paths(text)
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
    # Printed whether or not the directory is present, and the SAME number either way — that
    # invariance is the whole point of the bucket, so a reader on CI and a reader here see one
    # count and can tell it did not move.
    print('                         (%d path(s) in a separate repository, not checkable here: %s)'
          % (len(external), ', '.join(EXTERNAL_ROOTS)))

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
    # ⚠ RECORDING, added 2026-08-26. Before this the checker RAN and could never leave a KEY:
    # unregistered, so V8 refused every append, and `inventory` never listed it — which is how
    # `R-NOTINLIB` reached 36 lines against a 12-line cap, the largest entry in the file, with
    # "16 of 18 admission keys" reading as near-complete while this sat outside the denominator.
    # Identical to the `check_fields` defect (`/rely` RLY35-3) closed the same day: a checker that
    # runs, costs time, and can never be missed from the inventory is the "silence is never a
    # pass" defect one layer over.
    #
    # ⚠ SUBJECT IS `CLAUDE.md` ITSELF, and the registry pairs this with `when: "CLAUDE.md"` so the
    # key is NOT_APPLICABLE on every commit that does not touch the file — Tim, 2026-08-26:
    # a full re-analysis on every commit "is nuts". When the file IS in the change the key starts
    # MISSING and fails CLOSED, so nothing has to be remembered.
    #
    # ⚠ WHY PUSH-TIME IS SUFFICIENT, and it is a fact about who READS this file rather than a
    # concession. The agent editing `CLAUDE.md` already holds the desired state in context; the
    # file's only real consumer is the NEXT session, and a push is exactly when it becomes
    # available to one. An edit-time trigger would warn the reader who least needs it, at the cost
    # of one more remembered rule — and R-EDITLEAN records that remembered rules "fail here by
    # construction", seven leaks running.
    #
    # ⚠ THE VERDICT IS THE BLOCKING LEGS ONLY. The WARN counts are a reading list and the three
    # PENDING legs are NOT checked and NOT passing, so a recorded PASS here claims exactly two
    # properties — rooted paths resolve, named checkers exist — and never the shape contract whole.
    _rc = common.record_if_asked(
        'check_claude_md', ['CLAUDE.md'], ([] if not bad else ['CLAUDE.md']),
        'CLAUDE.md names a rooted path or a checker that does not exist',
        module='tools/verify/check_claude_md.py')
    if _rc:
        return _rc
    if bad:
        print('BLOCKED: %d blocking leg(s) failed. %d leg(s) still PENDING.'
              % (bad, len(PENDING)))
        return 1
    print('OK: %d blocking leg(s) clear. WARN counts above are a READING LIST, '
          'not a pass. %d leg(s) PENDING.' % (len(BLOCKING), len(PENDING)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
