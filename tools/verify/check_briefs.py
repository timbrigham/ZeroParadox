#!/usr/bin/env python3
"""Enforce that a gate brief instructs a command that actually works.

The briefs under `.claude/commands/` are the ONLY instructions a spawned review agent
receives, and nothing checked them. `check_claude_md.py` does this for `CLAUDE.md`; the
briefs had no equivalent, so a brief could name a flag `record.py` does not have, or a
`--step` the ledger has never heard of, and the defect would surface as a confused agent
mid-round rather than as a red line at push.

⚠⚠ THE STEP LEG IS THE ONE NOTHING ELSE CAN DO. It is a CROSS-SURFACE check: it asks the
LEDGER whether a name written in a MARKDOWN FILE is registered. `batch.py check_signals`
already says what an unregistered name is worth -- "this step name buys no coverage. Fix
the name or register the type; do not read it as a pass" -- but it can only say that at
push time, about a step someone already tried to use. This says it about the instruction.

Legs are split by KIND per the downgrade rule (`R-NOCONV`): a leg guarding a FAIL-OPEN
surface BLOCKS; an enumeration of accumulated debt WARNS and prints its count on every run.

⚠ EXIT 2 IS NOT EXIT 1, AND FOLDING THEM WOULD BE THIS FILE'S OWN DEFECT. The `steps` leg
asks the ledger. If the ledger cannot be reached the question was not answered -- that is
NOT "the briefs are fine" and NOT "the briefs are broken". `DC-45`: absent and clean are
different states, and only one of them is a finding about the subject.
"""
import io, os, re, sys, glob, argparse, subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402

sys.stdout.reconfigure(encoding='utf-8', errors='replace')

SELF = os.path.relpath(os.path.abspath(__file__), os.getcwd()).replace(os.sep, '/')
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
GLOB = '.claude/commands/*.md'

# --- leg registry. `mode` is DATA so a control can READ the enforcement decision. A literal
# at the call site cannot be tested; `guards.py` learned that on `batch.py` the hard way.
LEGS = [
    ('flags',  'BLOCK', 'every --flag in a record.py command line exists in record.py'),
    ('steps',  'BLOCK', 'every --step named is REGISTERED in the ledger'),
    ('paths',  'BLOCK', 'every rooted repo path cited in backticks resolves on disk'),
    ('marker', 'WARN',  'HARD CONSTRAINTS sits BELOW the spawn marker (queue ticket, 6 of 14)'),
    ('names',  'WARN',  'a brief that says "record your verdict" names the --step to use'),
]
BLOCKING = [n for n, m, _ in LEGS if m == 'BLOCK']

# ⚠ LINE-INITIAL, NOT A SUBSTRING. `ship.md` QUOTES this phrase to tell the caller where to
# paste from — `pass the prompt verbatim from after the "Spawn the Agent with this prompt"
# marker` — and a substring match read that as ship spawning an agent with no constraints
# block. It spawns nothing itself; it points at other briefs' markers. Found by opening the
# file rather than by trusting the count, which is the only way this class is ever found.
SPAWN_RE = re.compile(r'^Spawn the Agent with this prompt', re.M)
# The literal the regex anchors on. Used ONLY to build selftest fixtures, so a control never
# hardcodes a phrase the checker no longer looks for.
SPAWN = 'Spawn the Agent with this prompt'
HARD = 'HARD CONSTRAINTS'
RECORD_CMD = re.compile(r'record\.py[^\n`]*(?:\\\n[^\n`]*)*')
FLAG = re.compile(r'(--[a-z][a-z0-9-]+)')
STEP = re.compile(r'--step\s+([a-z_]+)')
CITED = re.compile(r'`(tools/[\w./*-]+|\.claude/[\w./*-]+|scripts/[\w./*-]+)`')
# "record your verdict" in any of the ways the briefs actually phrase it
SAYS_RECORD = re.compile(r'record (?:your|its own|the) verdict', re.I)


def real_flags():
    """What `record.py` ACTUALLY accepts, read from the program, never from a list here.

    ⚠ A hardcoded copy would be the mirror defect: two statements of one interface, and the
    checker would go green on a flag that had been renamed. Asking `--help` costs one
    subprocess and cannot drift from the parser that answers it."""
    p = subprocess.run([sys.executable, os.path.join(ROOT, 'tools', 'verify', 'record.py'),
                        '--help'], capture_output=True, text=True,
                       encoding='utf-8', errors='replace')
    if p.returncode != 0:
        return None
    return set(FLAG.findall(p.stdout))


def registered_steps():
    """Step types the LEDGER knows. None -- never an empty set -- when it cannot be asked.

    ⚠ Returning `set()` on an unreachable ledger would make every brief's step look
    unregistered and turn an outage into 14 findings about the corpus. `record.owing_paths`
    already sets this precedent: "I could not ask" must never render as data."""
    try:
        import record
        out = record._call('requirements', {})
    except Exception:
        return None
    if not out or not isinstance(out.get('types'), dict):
        return None
    return set(out['types'].keys())


def classify_record_failure(rc, ledger_answers):
    """Turn `record_if_asked`'s single failure code into the two facts it is hiding.

    `rc` is what `common.record_if_asked` returned; `ledger_answers` is `record.reachable()`.
    Returns 2 when the ledger could not be ASKED, and **3 when it was asked and REFUSED**.

    ⚠⚠ THIS IS THE `DC-45` SHAPE ONE LAYER UP, AND IT WAS FOUND INSIDE THE CHECKER BUILT TO
    CATCH IT. `record.emit` returns `None` for a refusal and for an outage alike, `emit_verdict`
    maps both to 2, and `hooks.py` printed "ledger or record.py unreachable" for both. On
    2026-09-06 this step was not registered, the ledger ANSWERED with the rule naming exactly
    that, and the push reported the ledger was down -- **a decision rendered as an absence**,
    which is the one distinction the exit-2 design exists to keep.

    ⚠ A DIFFERENT VALUE, NOT A DIFFERENT MESSAGE (`R-ZERONULL`). Both states already had their
    own prose string and nothing branched on either, because consumers branch on the CODE. So
    the code is what had to move: **2 could-not-ask · 3 asked-and-refused**. The remedies are
    genuinely different -- one is "fix the reachability", the other is "read the rule the
    server named" -- and a caller handed one code cannot choose between them.

    ⚠ PURE ON PURPOSE, so both halves are testable with no network at all. The single call that
    must touch the wire is `record.reachable()`, and it is passed IN rather than made here.
    """
    if rc == 2 and ledger_answers:
        return 3
    return rc


def audit(text, flags, steps):
    """Every leg, over one brief. Returns {leg: [finding, ...]}.

    ⚠ ONE function for the gate AND `--selftest`, so the control exercises the code that
    ships. A control that re-implements its subject proves nothing about the subject."""
    f = {n: [] for n, _, _ in LEGS}

    used = set()
    for blk in RECORD_CMD.findall(text):
        used |= set(FLAG.findall(blk))
    if flags is not None:
        f['flags'] = sorted(used - flags)

    declared = sorted(set(STEP.findall(text)))
    if steps is not None:
        f['steps'] = [d for d in declared if d not in steps]

    for q in sorted(set(CITED.findall(text))):
        if '*' not in q and not os.path.exists(os.path.join(ROOT, q)):
            f['paths'].append(q)

    _sm = SPAWN_RE.search(text)
    m, h = (_sm.start() if _sm else -1), text.find(HARD)
    if m >= 0 and h < 0:
        f['marker'].append('spawns an agent and has no HARD CONSTRAINTS block at all')
    elif m >= 0 and h < m:
        f['marker'].append('HARD CONSTRAINTS at char %d is ABOVE the spawn marker at %d '
                           '- a literal reading never delivers it' % (h, m))

    if SAYS_RECORD.search(text) and not declared:
        f['names'].append('says to record a verdict but names no --step')
    return f


def selftest():
    """Both halves, per `check_checkers` rule 3: each leg must FIRE on a planted defect and
    SUPPRESS on a clean case. A must-fire half alone is half-tested."""
    FLAGS = {'--step', '--verdict', '--files', '--failing-file'}
    STEPS = {'rely', 'editorial'}
    OK_PATH = 'tools/verify/check_briefs.py'
    cases = [
        ('flags  fires   unknown flag',
         'run `record.py --step rely --verdict fail --nonesuch x`', 'flags', True),
        ('flags  clean   known flags only',
         'run `record.py --step rely --verdict fail --failing-file f`', 'flags', False),
        ('steps  fires   unregistered step',
         'record.py --step copy_editor --verdict fail', 'steps', True),
        ('steps  clean   registered step',
         'record.py --step rely --verdict fail', 'steps', False),
        ('paths  fires   dead pointer',
         'see `tools/verify/no_such_file_here.py`', 'paths', True),
        ('paths  clean   live pointer',
         'see `%s`' % OK_PATH, 'paths', False),
        ('marker fires   constraints ABOVE marker',
         '## %s\nx\n%s:' % (HARD, SPAWN), 'marker', True),
        ('marker fires   spawns with no block',
         '%s:\nnothing else' % SPAWN, 'marker', True),
        ('marker clean   constraints BELOW marker',
         '%s:\n## %s' % (SPAWN, HARD), 'marker', False),
        ('marker clean   never spawns an agent',
         'this brief spawns nothing at all', 'marker', False),
        ('marker clean   QUOTES the marker, does not spawn',
         'paste verbatim from after the "Spawn the Agent with this prompt" marker', 'marker', False),
        ('names  fires   records with no step',
         'Record your verdict via record.py when done.', 'names', True),
        ('names  clean   records and names the step',
         'Record your verdict: `record.py --step rely --verdict fail`', 'names', False),
    ]
    # ⚠ COUNTED, NOT COMPUTED. This line read `len(cases) + 1` and went WRONG the same hour the
    # classifier controls were added below -- it reported 14/14 while 18 controls ran. A summary
    # whose denominator is arithmetic over ONE of its control lists silently stops covering the
    # others, which is the reach-versus-report defect this whole checker exists to name.
    bad = ran = 0
    fired = clean = 0
    for label, text, leg, must_fire in cases:
        got = bool(audit(text, FLAGS, STEPS)[leg])
        ok = (got == must_fire)
        bad += 0 if ok else 1
        ran += 1
        fired += 1 if must_fire else 0
        clean += 0 if must_fire else 1
        print('  %-4s %-42s %s' % ('ok' if ok else 'FAIL', label,
                                   'fired' if got else 'silent'))
    # ⚠ THE UNREACHABLE-LEDGER CASE IS A CONTROL, NOT AN EDGE CASE. It is the whole reason
    # this file has three exits, so it is tested rather than trusted.
    none_case = audit('record.py --step never_registered --verdict fail', None, None)
    ok = not none_case['steps'] and not none_case['flags']
    bad += 0 if ok else 1
    ran += 1
    print('  %-4s %-42s %s' % ('ok' if ok else 'FAIL',
                               'unasked  ledger/flags unavailable -> no finding',
                               'silent' if ok else 'FIRED - would blame the corpus'))
    # ⚠ THE REFUSAL/UNREACHABLE SPLIT IS A CONTROL TOO, AND IT IS THE ONE `B4` COST US. Both
    # halves, pure: the classifier is HANDED the reachability answer rather than measuring it, so
    # this control cannot pass merely because the ledger happened to be up when it ran.
    for rc_in, answers, want, label in (
            (2, True,  3, 'refusal   ledger answered -> 3, a decision'),
            (2, False, 2, 'outage    ledger silent   -> 2, could not ask'),
            (1, True,  1, 'finding   a real finding is never reclassified'),
            (0, False, 0, 'clean     a clean record stays clean')):
        got = classify_record_failure(rc_in, answers)
        ok = (got == want)
        bad += 0 if ok else 1
        ran += 1
        print('  %-4s %-42s %s' % ('ok' if ok else 'FAIL', label, 'exit %d' % got))
    print('\nselftest: %s (%d/%d) - FIRES on %d planted defect(s), SUPPRESSES on %d clean case(s)'
          % ('PASS' if not bad else 'FAIL', ran - bad, ran, fired, clean))
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--selftest', action='store_true', help='run the leg controls and exit')
    ap.add_argument('--record', action='store_true',
                    help='record the verdict in the ledger (declared so argparse accepts it)')
    args = ap.parse_args()
    if args.selftest:
        print('check_briefs.py --selftest: both halves for every leg\n')
        return selftest()

    print('=' * 78)
    print('  GATE BRIEF CONTRACT')
    print('=' * 78)
    print('  entry      python tools/verify/check_briefs.py')
    print('  target     %s' % GLOB)
    print('  plan       %d leg(s): %d BLOCK, %d WARN'
          % (len(LEGS), len(BLOCKING), sum(1 for _, m, _ in LEGS if m == 'WARN')))
    for n, m, d in LEGS:
        print('      %-8s %-6s %s' % (n, m, d))

    flags, steps = real_flags(), registered_steps()
    if flags is None:
        print('\nCANNOT ASK: record.py --help did not exit 0, so the `flags` leg has no')
        print('ground truth. This is a read failure, not a finding about the briefs.')
        return 2
    if steps is None:
        print('\nCANNOT ASK: the ledger could not be reached, so the `steps` leg cannot be')
        print('answered. NOT a pass and NOT a failure -- exit 2, per DC-45.')
        return 2
    print('  ground     %d record.py flag(s), %d registered step type(s)' % (len(flags), len(steps)))
    print('=' * 78)

    briefs = sorted(glob.glob(os.path.join(ROOT, GLOB.replace('/', os.sep))))
    if not briefs:
        # ⚠ AN EMPTY SCAN IS NOT A CLEAN SCAN. `scan_pdfs` shipped that defect; not here.
        print('\nCANNOT ASK: %s matched no files. An empty scope cannot pass.' % GLOB)
        return 2

    totals = {n: 0 for n, _, _ in LEGS}
    hits = {n: [] for n, _, _ in LEGS}
    for p in briefs:
        rel = os.path.relpath(p, ROOT).replace(os.sep, '/')
        f = audit(io.open(p, encoding='utf-8', errors='replace').read(), flags, steps)
        for leg, items in f.items():
            for it in items:
                totals[leg] += 1
                hits[leg].append((rel, it))

    print()
    bad = 0
    for n, m, _ in LEGS:
        c = totals[n]
        if m == 'BLOCK' and c:
            bad += c
        state = 'FAIL' if (m == 'BLOCK' and c) else ('WARN' if c else 'ok')
        print('  %-8s %-5s %d finding(s) over %d brief(s)' % (n, state, c, len(briefs)))
        # ⚠ EVERY WARN PRINTS ITS COUNT AND ITS SITES ON EVERY RUN, clean or not. A downgraded
        # leg must get LOUDER, not quieter (`RLY25-1`) -- the instance that reached a commit did
        # so by being unnoticed, never by being waved through.
        for rel, it in hits[n][:6]:
            print('      %-28s %s' % (os.path.basename(rel), it))
        if c > 6:
            print('      ... and %d more' % (c - 6))

    _rc = common.record_if_asked(
        'check_briefs', [os.path.relpath(p, ROOT).replace(os.sep, '/') for p in briefs],
        sorted({r for n in BLOCKING for r, _ in hits[n]}),
        'a gate brief names a flag, step or path that does not exist',
        module='tools/verify/check_briefs.py')
    if _rc:
        # ⚠ ASKED ONLY ON THE FAILING PATH. A reachability probe on every clean run would be a
        # round trip that buys nothing; here the record has already failed and the only open
        # question is WHICH of the two failures it was.
        import record as _record
        _rc = classify_record_failure(_rc, _record.reachable())
        if _rc == 3:
            print('\nREFUSED: the ledger was REACHED and REJECTED this record. That is a')
            print('         decision, not an outage -- the rule it named is printed above.')
        return _rc
    if bad:
        print('\nBLOCKED: %d blocking finding(s). A brief instructing a command that does not '
              'work is\n         discovered by a confused agent mid-round, which is the most '
              'expensive place to find it.' % bad)
        return 1
    print('\nOK: %d blocking leg(s) clear over %d brief(s). WARN counts above are a READING '
          'LIST, not a pass.' % (len(BLOCKING), len(briefs)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
