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
    ('checkers', 'BLOCK',   'every checker name RESOLVES to a file or is REGISTERED withdrawn'),
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

# The truncation floor. Live figures on 2026-09-16 were 46 rooted paths and 4 checker names, so
# this sits at roughly a fifth of the former and the bare minimum of the latter: reachable only by
# a file that has lost most of itself, never by ordinary editing. Raise it only with a measurement.
MIN_ROOTED = 10

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

# ⭐⭐ A REGISTRY CAN ONLY SPEAK ABOUT WHAT REGISTERED WITH IT (Tim, 2026-09-16: *"the premise of
# a ledger saying these are the only things doing XYZ — that doesn't make sense. The only thing
# you can say is these are the things that have properly registered with me"*). So this leg
# stopped reporting "N named checker(s) MISSING", which asserts a fact about the world it never
# measured, and reports which of four states each name is in — every count printed every run.
# The same inversion `R-TRUNC` already demands of the truncation hook: enumerate the positives,
# do not chase the negatives.
#
#   RESOLVED    a file of that name is under `tools/verify`
#   REGISTERED  the name is declared BELOW as a historical referent, not a dependency
#   REVIVED     declared below AND present on disk — the registration is stale. BLOCKS.
#   UNRESOLVED  neither. BLOCKS — and the message says the LOOKUP failed, never that the tool
#               does not exist, because this leg cannot see anything outside `tools/verify`.
#
# ⚠ REGISTERING A NAME IS A TYPED ACT WITH A REASON, exactly like TRANSIENT above, and it is
# NOT the same as suppressing it: a registered name still appears in the printed counts, and a
# registration that goes stale BLOCKS rather than rotting quietly.
WITHDRAWN = {
    'check_attribution.py':
        'The withdrawn attribution-checker attempt. CLAUDE.md names it to say what the "PULLED" '
        'note was ABOUT: mistaking it for the live `check_paths --claim` is DC-53\'s founding '
        'instance, which cost 28 days and shipped a misattribution into two DOIs. Strip the name '
        'and the entry stops explaining anything.',
}
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


def classify_checkers(text):
    """Every checker name in `text`, partitioned into the four states above.

    Returns `(resolved, registered, revived, unresolved)`. The partition is total and the
    buckets are disjoint, so `len` of the four always sums to the number of names found —
    which is the property that makes the printed counts auditable rather than decorative.
    """
    resolved, registered, revived, unresolved = [], [], [], []
    for c in sorted(set(CHECKER_NAMED.findall(text))):
        on_disk = os.path.exists(os.path.join(ROOT, 'tools', 'verify', c))
        if c in WITHDRAWN and on_disk:
            revived.append(c)
        elif on_disk:
            resolved.append(c)
        elif c in WITHDRAWN:
            registered.append(c)
        else:
            unresolved.append(c)
    return resolved, registered, revived, unresolved


def blocking_failures(text, whole_file=False):
    """The BLOCK legs, evaluated against `text`. Returns a list of failure strings.

    Factored out so --selftest exercises THE SAME CODE the push gate runs. A control that
    re-implements the logic it is testing proves nothing about the logic that ships.

    ⚠ `whole_file` GATES THE FLOOR, and the reason is honest rather than convenient: the floor is a
    property of a COMPLETE `CLAUDE.md`, and the fragment cases below feed one-line snippets that
    are all legitimately below it. Passing a fragment is not a claim that the file is intact, so
    the floor must not judge one. `main()` passes True; the end-to-end fixtures reach it THROUGH
    `main()`, so the shipping path is still what the controls drive.
    """
    fails = []

    # ⛔⛔ THE FLOOR — AN ABSENT FILE IS NOT A CLEAN ONE. `/rely` round 5, ruled BEDROCK by Tim
    # 2026-09-16: every other leg here is a search for BAD pointers, so a `CLAUDE.md` emptied or
    # truncated has none and the gate returned exit 0, printed `OK: 2 blocking leg(s) clear`, and
    # handed `record_if_asked` an empty failing list — PUBLISHING a pass over absent evidence.
    # Measured end to end at 3 bytes: this checker, `check_paths`, `check_prose` and
    # `check_encoding` all exited 0, and `required.v2.json` scope-excludes `CLAUDE.md` from
    # `editorial` and `adversary`, so this is the only gate it has.
    # ⚠ SCOPE, STATED: a floor catches GROSS truncation, never a surgical edit that keeps the
    # pointer density. It is a tripwire on the file's SIZE, not a judgement on its content, and
    # the counts are far below the live figures (46 rooted paths, 4 named checkers) so ordinary
    # editing cannot reach it. R-ZERONULL: the empty branch must return a different VALUE.
    rooted_all, _loose_all, _ext_all = cited_paths(text)
    named_all = set(CHECKER_NAMED.findall(text))
    if whole_file and (len(rooted_all) < MIN_ROOTED or not named_all):
        fails.append('floor:%d rooted path(s) and %d checker name(s) — below the floor of %d/1, '
                     'so this file is truncated or empty rather than clean'
                     % (len(rooted_all), len(named_all), MIN_ROOTED))

    rooted, _, _ = cited_paths(text)
    missing = [p for p in rooted
               if not os.path.exists(os.path.join(ROOT, p)) and p not in TRANSIENT]
    if missing:
        fails.append('paths:' + ','.join(sorted(missing)))
    _res, _reg, revived, unresolved = classify_checkers(text)
    if unresolved:
        fails.append('checkers:' + ','.join(unresolved))
    if revived:
        # A stale WITHDRAWN entry is the registry disagreeing with the tree, which is the exact
        # class this mechanism exists to stop CLAUDE.md committing. It fails on the way back too.
        fails.append('checkers-revived:' + ','.join(revived))
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
        # A REGISTERED withdrawn name must not block, and it must not be silent either -- the
        # run prints it with its reason. This row asserts only the first half; the mechanism's
        # both-halves control is below, on a synthetic member, so it cannot go green by accident
        # the way `transient-excluded` did for three independent wrong reasons.
        ('withdrawn-registered', 'the note was about `check_attribution.py`, a DIFFERENT tool.',
                                                                                          False),
    ]
    bad = 0

    # The TRANSIENT mechanism itself, exercised on a member that exists only for these two lines.
    # Both halves, against the SAME dict `blocking_failures` reads: absent -> must fire, present ->
    # must suppress. Without this the exclusion path would be untested code the moment the list
    # emptied, and a suppression route nobody has seen work is not a mechanism, it is a hope.
    # ⚠ `mech` COUNTS THE MECHANISM CONTROLS so the summary can state a total the reader can
    # re-derive from the rows above it (`/rely` R2-O3, 2026-09-16: the run printed 13 rows and
    # claimed `PASS (11/11)`, counting `cases` only). And the two MUST-FIRE halves below now
    # print on PASS as well as on FAIL — a control that is silent when it succeeds cannot be
    # counted, and an uncountable control is indistinguishable from one that never ran.
    mech = 0

    SYN = 'tools/verify/_synthetic_transient_destination.json'
    syn_text = 'the batch writes `%s` between runs.' % SYN
    t_fired = bool(blocking_failures(syn_text))
    print('  %-22s %-14s expected %-6s got %-6s %s'
          % ('transient-mechanism', 'MUST FIRE', True, t_fired, 'ok' if t_fired else 'FAIL'))
    mech += 1
    bad += (not t_fired)
    TRANSIENT[SYN] = 'synthetic, installed by --selftest only'
    try:
        fired = bool(blocking_failures(syn_text))
    finally:
        del TRANSIENT[SYN]
    print('  %-22s %-14s expected %-6s got %-6s %s'
          % ('transient-mechanism', 'BOTH HALVES', False, fired, 'ok' if not fired else 'FAIL'))
    mech += 1
    if fired:
        bad += 1

    # The WITHDRAWN mechanism, same shape, on a synthetic member -- and a THIRD half the
    # TRANSIENT control does not have: the REVIVED state, where the registration is stale
    # because the file came back. That direction is the one a suppression list normally rots
    # in, so it is the one worth a control.
    WSYN = 'check_synthetic_withdrawn.py'
    wsyn_text = 'the `%s` attempt was pulled; do not confuse it with the live sweep.' % WSYN
    w_fired = bool(blocking_failures(wsyn_text))
    print('  %-22s %-14s expected %-6s got %-6s %s'
          % ('withdrawn-mechanism', 'MUST FIRE', True, w_fired, 'ok' if w_fired else 'FAIL'))
    mech += 1
    bad += (not w_fired)
    WITHDRAWN[WSYN] = 'synthetic, installed by --selftest only'
    try:
        wfired = bool(blocking_failures(wsyn_text))
        # REVIVED: registered AND on disk. Build the file, so the state is CONSTRUCTED and run
        # rather than argued -- the same discipline the `unreadable state` rule asks for.
        wpath = os.path.join(ROOT, 'tools', 'verify', WSYN)
        open(wpath, 'w').close()
        try:
            revived_fired = any(f.startswith('checkers-revived:')
                                for f in blocking_failures(wsyn_text))
        finally:
            os.remove(wpath)
    finally:
        del WITHDRAWN[WSYN]
    print('  %-22s %-14s expected %-6s got %-6s %s'
          % ('withdrawn-mechanism', 'BOTH HALVES', False, wfired, 'ok' if not wfired else 'FAIL'))
    mech += 1
    bad += bool(wfired)
    print('  %-22s %-14s expected %-6s got %-6s %s'
          % ('withdrawn-revived', 'MUST FIRE', True, revived_fired,
             'ok' if revived_fired else 'FAIL'))
    mech += 1
    bad += (not revived_fired)

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
    mech += 1
    bad += 1 if drift else 0

    for name, text, must_fire in cases:
        fired = bool(blocking_failures(text))
        ok = (fired == must_fire)
        if not ok:
            bad += 1
        print('  %-22s %-14s expected %-6s got %-6s %s'
              % (name, 'MUST FIRE' if must_fire else 'MUST SUPPRESS',
                 must_fire, fired, 'ok' if ok else 'FAIL'))
    # ⚠⚠ END-TO-END ON `main()` ITSELF — the function `hooks.py` invokes and the one that calls
    # `record_if_asked`. `/rely` round 4, BEDROCK: the round-3 control asserted the STRING
    # 'blocking_failures(' appeared in `main`'s source, which is a PROXY for the property (DC-27).
    # Measured: keeping the call, discarding its value and re-deriving the verdict from the legs
    # gave `exit 0` on a planted defect while this suite printed `PASS (19/19)`. A control must
    # drive the thing that PRODUCES THE VERDICT; nothing short of running the gate does that.
    import contextlib
    import tempfile
    global TARGET
    _real_target = TARGET
    _real_argv = sys.argv
    _live = io.open(_real_target, encoding='utf-8').read()
    # ⚠⚠ ONE DEFECT PER FIXTURE, AND THAT IS THE WHOLE POINT. A first version planted a dead path
    # AND an unresolved checker in one file; measured against the round-4 mutation (checkers leg
    # neutered, paths leg intact) it stayed GREEN, because the surviving leg still blocked. A
    # control bound to a fixture carrying two defects cannot fail in the shape a single-leg
    # regression takes — DC-49's "bound to its subject by position" wearing a fixture.
    _bad_path = _live + ('\n## R-PROBE  --selftest fixture, never committed\n'
                         'READ     tools/process/definitely_not_here.md\n')
    _bad_check = _live + ('\n## R-PROBE  --selftest fixture, never committed\n'
                          'RULE     run `check_definitely_absent.py` before committing.\n')
    _tmp = os.path.join(tempfile.gettempdir(), '_ccm_selftest_fixture.md')
    # ⛔ THE FIXTURES BELOW ARE SMALLER THAN LIVE, AND THAT IS THE POINT (`/rely` round 5). Every
    # earlier fixture was `_live + <appended defect>`, so the CONSTRUCTION could never produce a
    # target shorter than the real file nor a defect outside the tail — the gate's blindness to an
    # emptied or truncated `CLAUDE.md` was unreachable by its own controls.
    _empty = ''
    _truncated = '\n'.join(_live.split('\n')[:40])
    for _label, _content, _want_block in (('gate-blocks-bad-path', _bad_path, True),
                                          ('gate-blocks-bad-checker', _bad_check, True),
                                          ('gate-blocks-empty', _empty, True),
                                          ('gate-blocks-truncated', _truncated, True),
                                          ('gate-clears-live', _live, False)):
        try:
            io.open(_tmp, 'w', encoding='utf-8').write(_content)
            TARGET = _tmp
            sys.argv = ['check_claude_md.py']          # no --selftest: main() must not recurse
            _buf = io.StringIO()
            with contextlib.redirect_stdout(_buf):
                _rc = main()
        finally:
            TARGET, sys.argv = _real_target, _real_argv
            if os.path.exists(_tmp):
                os.remove(_tmp)
        _blocked = bool(_rc)
        _ok = _blocked == _want_block
        print('  %-22s %-14s expected %-6s got %-6s %s'
              % (_label, 'MUST FIRE' if _want_block else 'MUST SUPPRESS',
                 _want_block, _blocked, 'ok' if _ok else 'FAIL'))
        mech += 1
        bad += (not _ok)

    # ⚠ THE TOTAL COUNTS EVERY ROW PRINTED ABOVE — `cases` plus the `mech` mechanism controls.
    # It used to count `cases` alone, so the printed total was smaller than the printed rows and
    # no reader could re-derive it (`/rely` R2-O3). The `mech` controls are named in the same
    # column as the cases precisely so the two are addable.
    total = len(cases) + mech
    print('\nselftest: %s (%d/%d) - %d case(s) + %d mechanism control(s); '
          'FIRES on %d planted defect(s), SUPPRESSES on %d clean case(s)'
          % ('PASS' if not bad else 'FAIL', total - bad, total, len(cases), mech,
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
    resolved, registered, revived, unresolved = classify_checkers(text)
    named = resolved + registered + revived + unresolved
    if unresolved or revived:
        if unresolved:
            # ⚠ THE WORDING IS THE FINDING. "missing" claims the tool does not exist; all this
            # leg did was fail to find a file in ONE directory and fail to find a registration.
            print('  checkers         FAIL  %d name(s) resolved to no file under tools/verify '
                  'and are not registered: %s' % (len(unresolved), ', '.join(unresolved)))
        if revived:
            print('  checkers         FAIL  %d name(s) registered as WITHDRAWN but present on '
                  'disk — drop the registration: %s' % (len(revived), ', '.join(revived)))
    else:
        print('  checkers         ok    %d of %d name(s) resolved to a file under tools/verify'
              % (len(resolved), len(named)))
    # Printed on EVERY run, clear or blocked, and the reason is the same one TRANSIENT carries:
    # an exclusion nobody counts is how coverage silently shrinks.
    print('                         (%d name(s) registered as WITHDRAWN, see WITHDRAWN)'
          % len(registered))
    for c in registered:
        print('                             %s — %s' % (c, WITHDRAWN[c]))

    # --- THE VERDICT IS `blocking_failures`. The legs above PRINT; they do not decide. ------
    # ⚠⚠ `/rely` ROUND 3, BEDROCK, 2026-09-16. `main()` used to accumulate its own `bad` and
    # called `blocking_failures()` ZERO times, while that function's docstring said *"Factored
    # out so --selftest exercises THE SAME CODE the push gate runs."* Measured both halves:
    # neutering `main()`'s two `bad += 1` lines took the gate from exit 1 to exit 0 on a planted
    # defect, and `--selftest` still printed `PASS (18/18)`. `hooks.py` runs `main()`, so `main()`
    # IS the push gate — and it also calls `record_if_asked`, so the divergence would have
    # PUBLISHED a passing verdict for a `CLAUDE.md` the controls never judged.
    fails = blocking_failures(text, whole_file=True)
    bad = len(fails)

    # And they must not drift apart again. Both sides are computed from the SAME `text`, so a
    # disagreement is a defect in THIS file rather than in `CLAUDE.md` — and it blocks, because a
    # gate that cannot agree with its own controls has no verdict to give.
    # ⚠ COUNT THE SAME OBJECT ON BOTH SIDES (`/rely` round 4, O2). This compared LEGS (max 2)
    # against FAILURE STRINGS (max 3, since the checkers leg can emit both `checkers:` and
    # `checkers-revived:`), so a revived pin plus an unresolved name raised a false DIVERGED.
    # It failed closed, and an alarm that is wrong is still a defect in the alarm.
    printed = set()
    if missing:
        printed.add('paths')
    if unresolved:
        printed.add('checkers')
    if revived:
        printed.add('checkers-revived')
    if printed != {f.split(':', 1)[0] for f in fails}:
        print('\n  ** INTERNAL: legs printed %s, blocking_failures() reports %s.'
              % (sorted(printed) or ['none'], sorted(fails) or ['none']))
        print('     The gate and the code its controls exercise have DIVERGED. Blocking. **')
        bad = max(bad, len(printed), 1)

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
