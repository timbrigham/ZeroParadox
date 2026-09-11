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

EXIT CODES THIS EMITS: 0 clean · 1 a finding about the briefs · 2 COULD NOT ASK, the ledger
was never reached, RETRYABLE · 4 ASKED AND REFUSED, the ledger decided and said no, TERMINAL
-- never retry it, read the rule it named. ⚠ NOT 3: that is UNDETERMINED in the fleet
vocabulary and is also `ci_report.SKIPPED_RC`, which renders **skipped**, a non-failure.
The authority is the server, not this docstring: `vocabulary(name='exit_code')`.
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
    ('unexamined', 'WARN', 'path-shaped citations the BLOCK leg did NOT judge (its silence, counted)'),
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
# The continuation character, named so the extractor never carries a bare escape.
BACKSLASH = chr(92)

# ⚠⚠ THE WHOLE TOKEN, INCLUDING THE CHARACTERS THAT MAKE IT INVALID. `(--[a-z][a-z0-9-]+)`
# stopped at the first character it did not accept, so `--files_bogus` captured `--files` and
# `--reason-fileX` captured `--reason-file` -- both KNOWN flags, both reported clean, neither
# ever written in the brief. `--Nonesuch` matched nothing at all and was likewise silent.
# ⚠ THIS IS `B2`'s DEFECT IN THE SIBLING REGEX, SEVEN LINES DOWN, unfixed for a day while the
# diagnosis sat in the file: a pattern that silently truncates its capture does not fail to
# match, it matches something else and answers about THAT. `RLY51-2`, the SECOND occurrence,
# which is why `DC-46` now carries the class and its detector.
FLAG = re.compile(r'(--[A-Za-z][\w-]*)')
# ⚠⚠ `[=\s]` AND A FULL TOKEN, BECAUSE BOTH NARROWER FORMS WALKED THROUGH THE BLOCK LEG.
# This required whitespace, so `--step=totally_unregistered` was never seen at all; and it
# captured `[a-z_]+`, so `--step rely2` stopped at the digit, returned the REGISTERED prefix
# `rely`, and reported clean. Verified both, 2026-09-06 (`B2`) -- on the leg this file's own
# docstring calls THE ONE NOTHING ELSE CAN DO. A pattern that silently truncates its capture
# does not fail to match; it matches something else and answers about that.
STEP = re.compile(r'--step[=\s]+([A-Za-z0-9_-]+)')
CITED = re.compile(r'`(tools/[\w./*-]+|\.claude/[\w./*-]+|scripts/[\w./*-]+|ZeroParadox/[\w./*-]+)(?::\d+)?`')
# ⚠ THE `:LINE` SUFFIX IS STRIPPED, NOT REJECTED. `control.md` cites
# `tools/verify/check_paths.py:1501` and the leg never looked at it: the group had to be
# followed by a closing backtick, the colon sat in between, and the citation simply fell
# outside the pattern. A rooted path with a line number is the MOST checkable kind there is.

# ⚠⚠ EVERY BACKTICKED TOKEN THAT LOOKS LIKE A PATH, FOR THE `unexamined` WARN LEG. `CITED`
# above is deliberately narrow because it BLOCKS; this one is deliberately loose because it
# only COUNTS. The gap between them is the thing the queue ticket named -- 21 citations
# judged out of 193 path-shaped tokens, and a leg reporting `0 findings` over the first
# number reads exactly like a statement about the second.
LOOSE_CITED = re.compile(r'`([^`\n]+)`')
PATHISH = ('.py', '.md', '.json', '.lean', '.txt', '.ps1', '.toml')
# "record your verdict" in any of the ways the briefs actually phrase it
SAYS_RECORD = re.compile(r'record (?:your|its own|the) verdict', re.I)


def record_commands(text):
    """Every `record.py` invocation in `text`, with backslash CONTINUATIONS joined.

    ⚠⚠ THIS REPLACES A REGEX THAT SILENTLY READ ONLY THE FIRST LINE, AND THE SILENCE IS THE
    WHOLE FINDING. The old pattern was `record\\.py[^\\n`]*(?:\\\\\\n[^\\n`]*)*` -- a first
    segment plus an optional run of continuations. The greedy class does not exclude the
    BACKSLASH, so it swallowed the line's trailing one; the continuation group then had nothing
    to anchor on and matched ZERO times -- **which still yields a successful overall match, so
    the engine never backtracks.** A `*` that is happy with nothing cannot force the retry that
    would have saved it.

    ⚠ MEASURED ON THE REAL BRIEFS, AND IT DOES NOT REPRODUCE ON A CASUAL FIXTURE. 2026-09-06:
    `rely.md`, `claim-review.md` and `prior-art-review.md` each hide SIX flags this way
    (`--evidence --files --how --reason-file --run --who`), and the leg reported 0 findings over
    14 briefs. The house style is backslash-continued; every brief's real command is multi-line.

    ⚠ INLINE CODE STILL ENDS AT THE CLOSING BACKTICK, deliberately -- that behaviour was correct
    and is kept. A prose line quoting a command must not drag the rest of the sentence in as
    flags. Only a line with NO backtick after `record.py` is eligible to continue.
    """
    out, src = [], text.split(chr(10))
    i = 0
    while i < len(src):
        k = src[i].find('record.py')
        if k < 0:
            i += 1
            continue
        seg = src[i][k:]
        tick = seg.find('`')
        if tick >= 0:
            out.append(seg[:tick])
            i += 1
            continue
        buf = [seg]
        while buf[-1].rstrip().endswith(BACKSLASH) and i + 1 < len(src):
            i += 1
            nxt = src[i]
            t = nxt.find('`')
            buf.append(nxt if t < 0 else nxt[:t])
        out.append(' '.join(b.strip().rstrip(BACKSLASH).strip() for b in buf))
        i += 1
    return out


def flag_fragments(text):
    """Fenced blocks that CONTINUE a command without repeating `record.py`.

    ⚠⚠ `RLY51-1` — THE `flags` LEG COULD NOT SEE THESE AT ALL. `record_commands` scans only
    lines containing the literal `record.py`, and `rely.md` documents `--failing-file` in a
    fenced block four lines below the command it belongs to, with no such line. Measured on
    shipped bytes: a typo planted in the ORPHAN block exited 0 with `flags ok, 0 findings`,
    while the identical typo inside the `record.py` block exited 1. Two blocks, four lines
    apart, one of them invisible.

    ⚠ THE FRAGMENT TEST IS THE FIRST NON-BLANK LINE, AND IT IS WHAT PRICES THE WIDENING. A
    block belongs to a command only when it OPENS with a flag; anything else is a different
    program. Without that test every `lake build --verbose` in every brief becomes a finding
    against `record.py`'s flag list, which is the over-fire direction -- and a leg that cries
    wolf on ordinary shell examples gets downgraded, which is how the fail-open comes back.
    That case ships as the SUPPRESS half of this control rather than as a comment.
    """
    out, cur, inside = [], [], False
    for line in text.split(chr(10)):
        if line.lstrip().startswith('```'):
            if inside:
                body = [b for b in cur if b.strip()]
                if body and body[0].lstrip().startswith('--'):
                    out.append(' '.join(cur))
                cur, inside = [], False
            else:
                inside = True
            continue
        if inside:
            cur.append(line)
    return out


def flags_from_help(text):
    """Every flag-SHAPED token anywhere in help output. **The old ground truth, kept as a control.**

    ⚠⚠ THIS IS THE DEFECT, PRESERVED SO IT CAN BE TESTED. Help output is prose with options in it,
    so this returns the options AND anything a DESCRIPTION happens to mention -- a flag named only
    inside a help string becomes ground truth, and every brief may then cite a flag the parser does
    not accept. `B3`. Latent on 2026-09-06: the two sets agreed exactly, 18 and 18, so nothing was
    visibly wrong; one prose edit arms it. **A checker whose ground truth is English is asserting
    that nobody will ever write a flag-shaped word in a sentence.**"""
    return set(FLAG.findall(text))


def flags_from_list(text):
    """Every option string from `record.py --list-flags`. One per line, no prose to misread."""
    return {l.strip() for l in text.split(chr(10)) if l.strip().startswith('--')}


def real_flags():
    """What `record.py` ACTUALLY accepts, asked of its PARSER rather than of its help text.

    ⚠ A hardcoded copy would be the mirror defect: two statements of one interface, and the
    checker would go green on a flag that had been renamed. Asking the program costs one
    subprocess and cannot drift from the parser that answers it.

    ⚠⚠ AND WHICH QUESTION YOU ASK IT MATTERS. This used to scrape `--help`, which is the same
    mistake one level down -- reading an interface out of English. `--list-flags` prints the
    parser's own option strings, so a flag mentioned in a DESCRIPTION is no longer ground truth.
    Both readers are kept above and controlled against each other in `--selftest`.

    ⚠ `None`, NEVER AN EMPTY SET, on failure. An empty set would make every flag in every brief
    look unknown and turn an outage into fourteen findings about the corpus."""
    p = subprocess.run([sys.executable, os.path.join(ROOT, 'tools', 'verify', 'record.py'),
                        '--list-flags'], capture_output=True, text=True,
                       encoding='utf-8', errors='replace')
    if p.returncode != 0:
        return None
    out = flags_from_list(p.stdout)
    # ⚠ AN EMPTY ANSWER IS NOT AN ANSWER. `--list-flags` on a program that has it prints at least
    # `--help`; zero lines means the flag was silently ignored by an older copy, and treating that
    # as "record.py accepts nothing" would indict every brief at once.
    return out or None


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
    Returns 2 when the ledger could not be ASKED, and **4 when it was asked and REFUSED**.

    ⚠⚠ THIS IS THE `DC-45` SHAPE ONE LAYER UP, AND IT WAS FOUND INSIDE THE CHECKER BUILT TO
    CATCH IT. `record.emit` returns `None` for a refusal and for an outage alike, `emit_verdict`
    maps both to 2, and `hooks.py` printed "ledger or record.py unreachable" for both. On
    2026-09-06 this step was not registered, the ledger ANSWERED with the rule naming exactly
    that, and the push reported the ledger was down -- **a decision rendered as an absence**,
    which is the one distinction the exit-2 design exists to keep.

    ⚠ A DIFFERENT VALUE, NOT A DIFFERENT MESSAGE (`R-ZERONULL`). Both states already had their
    own prose string and nothing branched on either, because consumers branch on the CODE. So
    the code is what had to move: **2 could-not-ask · 4 asked-and-refused**. The remedies are
    genuinely different -- one is "fix the reachability", the other is "read the rule the
    server named" -- and a caller handed one code cannot choose between them.

    ⚠ 4 RATHER THAN 3, AND THE REASON IS A COLLISION. 3 already means UNDETERMINED in the fleet
    vocabulary -- a verdict about the CONTENT that could not resolve -- and `ci_report.SKIPPED_RC`
    is also 3, rendered **skipped** and scored a NON-FAILURE. A 3 minted for a terminal ledger
    refusal therefore sits one promotion away from reading as "this gate did not run". Latent
    today only because `check_briefs.py` is in `ci_report.SELFTESTS`, which scores on `rc != 0`,
    and not in `CHECKS`, where the skip treatment applies.

    ⚠ PURE ON PURPOSE, so both halves are testable with no network at all. The single call that
    must touch the wire is `record.reachable()`, and it is passed IN rather than made here.
    """
    if rc == 2 and ledger_answers:
        return 4
    return rc


def audit(text, flags, steps):
    """Every leg, over one brief. Returns {leg: [finding, ...]}.

    ⚠ ONE function for the gate AND `--selftest`, so the control exercises the code that
    ships. A control that re-implements its subject proves nothing about the subject."""
    f = {n: [] for n, _, _ in LEGS}

    used = set()
    for blk in record_commands(text) + flag_fragments(text):
        used |= set(FLAG.findall(blk))
    if flags is not None:
        f['flags'] = sorted(used - flags)

    declared = sorted(set(STEP.findall(text)))
    if steps is not None:
        f['steps'] = [d for d in declared if d not in steps]

    judged = sorted(set(CITED.findall(text)))
    for q in judged:
        if '*' not in q and not os.path.exists(os.path.join(ROOT, q)):
            f['paths'].append(q)

    # ⚠⚠ THE COUNT OF WHAT THIS FILE DID **NOT** JUDGE, PRINTED EVERY RUN. `DC-45`: a leg
    # reporting zero cannot distinguish examined-and-clean from never-looked, and this
    # checker shipped exactly that -- `0 findings over 14 briefs` while 14 dead pointers
    # sat outside its view. It CANNOT be widened into the BLOCK leg: seven of the briefs
    # cite `.claude-local/*_cleared.txt` inside a sentence that says DO NOT WRITE IT, so
    # the correct state for those paths is ABSENT. Judging them would manufacture the
    # `ship.md` false positive seven more times.
    # ⚠ SO IT WARNS AND IS LOUD, per `R-NOCONV`: the enumeration leg is a READING LIST,
    # never a verdict, and the number is what stops the silence reading as coverage.
    for q in sorted(set(LOOSE_CITED.findall(text))):
        q = q.strip()
        if not q or ' ' in q or q in judged:
            continue
        if q.startswith('.') and '/' not in q:
            continue          # a bare extension, `.lean`, is not a citation
        if q.startswith('/'):
            continue          # a slash COMMAND, `/rely`, is not a path
        if '/' in q or q.endswith(PATHISH):
            f['unexamined'].append(q)

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
        # ⚠⚠ `RLY51-2` — A TYPO THAT TRUNCATES ONTO A VALID PREFIX. This is `B2`'s defect in the
        # SIBLING regex, seven lines from the comment describing it, unfixed for a day. The
        # capture class stopped at the first character it did not accept and returned the KNOWN
        # prefix, so the audit compared a flag the brief never wrote against the real list and
        # found it present. A pattern that truncates does not fail to match -- it answers about
        # a different string, which is why `flags ok` was the reported result.
        ('flags  fires   typo truncates onto a valid prefix',
         'run `record.py --step rely --files_bogus x`', 'flags', True),
        ('flags  fires   an uppercase flag was invisible',
         'run `record.py --step rely --Nonesuch x`', 'flags', True),
        # ⚠⚠ `RLY51-1` — THE LEG COULD NOT SEE A FENCED BLOCK WITH NO `record.py` LINE, and
        # `rely.md` documents `--failing-file` in exactly one. Measured on shipped bytes: a typo
        # in the orphan block exited 0 while the identical typo four lines up exited 1.
        ('flags  fires   orphan continuation block',
         '```' + chr(10) + '    --nonesuch <value>' + chr(10) + '```', 'flags', True),
        # ⚠ THE SUPPRESS HALF OF THE SAME WIDENING, AND IT IS THE ONE THAT PRICES IT. A fenced
        # block is a fragment only when its first non-blank line STARTS a flag; otherwise every
        # `lake build --verbose` in every brief becomes a finding against record.py's flag list.
        ('flags  clean   a fenced block that is not a fragment',
         '```' + chr(10) + '    lake build --verbose' + chr(10) + '```', 'flags', False),
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
        # ⚠ B1 — THE REAL HOUSE STYLE IS BACKSLASH-CONTINUED AND THE LEG READ ONLY LINE ONE.
        # Measured on the real briefs 2026-09-06, never on a fixture: `rely`, `claim-review` and
        # `prior-art-review` each hid SIX flags this way and reported 0 findings.
        ('flags  fires   unknown flag on a CONTINUATION line',
         'record.py --step rely --verdict fail \\' + '\n    --nonesuch x', 'flags', True),
        ('flags  clean   continuation lines all known',
         'record.py --step rely --verdict fail \\' + '\n    --failing-file f', 'flags', False),
        # ⚠ B2 — `--step=name` and a registered PREFIX both walked through the one leg the
        # docstring calls THE ONE NOTHING ELSE CAN DO.
        ('steps  fires   --step=name, no whitespace',
         'record.py --step=totally_unregistered --verdict fail', 'steps', True),
        ('steps  fires   name EXTENDS a registered one',
         'record.py --step rely2 --verdict fail', 'steps', True),
        ('steps  clean   --step=name, registered',
         'record.py --step=rely --verdict fail', 'steps', False),
        # ⚠ THE `paths` LEG NOW STRIPS A `:LINE` SUFFIX, so both halves are tested WITH one.
        ('paths  fires   dead pointer with a line number',
         'see `tools/verify/no_such_file_here.py:1501`', 'paths', True),
        ('paths  clean   live pointer with a line number',
         'see `%s:1`' % OK_PATH, 'paths', False),
        # ⚠ THE `unexamined` LEG IS THE SILENCE, COUNTED. It must fire on a path-shaped citation
        # the BLOCK leg does not judge, and stay silent on the three shapes that are not paths.
        ('unexam fires   citation outside the BLOCK leg',
         'write `.claude-local/notes/whatever.md` when done', 'unexamined', True),
        ('unexam clean   the BLOCK leg already judged it',
         'see `%s`' % OK_PATH, 'unexamined', False),
        ('unexam clean   a bare extension is not a citation',
         'every `.lean` file in the corpus', 'unexamined', False),
        ('unexam clean   a slash command is not a path',
         'run `/rely` in a fresh agent', 'unexamined', False),
        ('names  fires   records with no step',
         'Record your verdict via record.py when done.', 'names', True),
        ('names  clean   records and names the step',
         'Record your verdict: `record.py --step rely --verdict fail`', 'names', False),
    ]
    # ⚠ COUNTED, NOT COMPUTED. This line read `len(cases) + 1` and went WRONG the same hour the
    # classifier controls were added below -- it reported 14/14 while 18 controls ran. A summary
    # whose denominator is arithmetic over ONE of its control lists silently stops covering the
    # others, which is the reach-versus-report defect this whole checker exists to name.
    # ⚠⚠ `RLY51-5` — AND THIS IS THE SECOND TIME THIS SUMMARY WAS WRONG IN ONE FILE. `ran` was
    # fixed on 2026-09-06 (it read `len(cases) + 1`); `fired` and `clean` were left incrementing
    # only inside the `cases` loop, so the line printed `PASS (32/32) - FIRES on 11 ... on 13`
    # and 11 + 13 = 24. Two numbers that look like a partition of a third, and are not.
    # ⚠ SO THE PARTITION IS NOW ASSERTED RATHER THAN IMPLIED: `other` counts the controls that
    # are neither a planted defect nor a clean case, and a row below FAILS if the three do not
    # sum to `ran`. A summary that can drift silently is the reach-versus-report defect this
    # checker exists to name, committed by the checker itself, twice.
    bad = ran = 0
    fired = clean = other = 0
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
    other += 1
    print('  %-4s %-42s %s' % ('ok' if ok else 'FAIL',
                               'unasked  ledger/flags unavailable -> no finding',
                               'silent' if ok else 'FIRED - would blame the corpus'))
    # ⚠⚠ `B3` — GROUND TRUTH FROM THE PARSER, NOT FROM ITS HELP PROSE. Both readers are kept so
    # the difference is demonstrated rather than asserted: the help scrape returns a flag that
    # exists only inside a DESCRIPTION, and the list reader cannot. Latent on the real file the
    # day this was written (18 and 18, identical) -- so nothing but a control could show it.
    HELP_FIXTURE = ('  --real REAL    the real one; if it fails, pass --fake-flag instead' + chr(10)
                    + '  --other OTHER  another real one')
    LIST_FIXTURE = '--real' + chr(10) + '--other' + chr(10)
    scraped, listed = flags_from_help(HELP_FIXTURE), flags_from_list(LIST_FIXTURE)
    for got, want, label in (
            ('--fake-flag' in scraped, True,
             'ground  help scrape ADOPTS a flag named only in prose'),
            ('--fake-flag' in listed, False,
             'ground  parser list is immune to the same prose'),
            (listed == {'--real', '--other'}, True,
             'ground  parser list returns exactly the options')):
        ok = (got == want)
        bad += 0 if ok else 1
        ran += 1
        other += 1
        print('  %-4s %-42s %s' % ('ok' if ok else 'FAIL', label, got))
    # ⚠ THE REFUSAL/UNREACHABLE SPLIT IS A CONTROL TOO, AND IT IS THE ONE `B4` COST US. Both
    # halves, pure: the classifier is HANDED the reachability answer rather than measuring it, so
    # this control cannot pass merely because the ledger happened to be up when it ran.
    for rc_in, answers, want, label in (
            (2, True,  4, 'refusal   ledger answered -> 4, a decision'),
            (2, False, 2, 'outage    ledger silent   -> 2, could not ask'),
            (1, True,  1, 'finding   a real finding is never reclassified'),
            (0, False, 0, 'clean     a clean record stays clean')):
        got = classify_record_failure(rc_in, answers)
        ok = (got == want)
        bad += 0 if ok else 1
        ran += 1
        other += 1
        print('  %-4s %-42s %s' % ('ok' if ok else 'FAIL', label, 'exit %d' % got))
    # ⚠⚠ THE PARTITION IS A CONTROL, NOT A COMMENT. If these three stop summing to
    # `ran`, a control list has been added that the summary does not describe -- which is
    # exactly how this line went wrong twice. It fails LOUD rather than quietly printing a
    # smaller denominator, because a miscount nobody sees reads as coverage.
    _part_ok = (fired + clean + other == ran)
    bad += 0 if _part_ok else 1
    ran += 1
    other += 1
    print('  %-4s %-42s %s' % ('ok' if _part_ok else 'FAIL',
                               'summary  fired+clean+other == ran',
                               '%d+%d+%d vs %d' % (fired, clean, other, ran)))
    print('\nselftest: %s (%d/%d) - FIRES on %d planted defect(s), SUPPRESSES on %d'
          ' clean case(s), and %d further control(s) that are neither'
          % ('PASS' if not bad else 'FAIL', ran - bad, ran, fired, clean, other))
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
        # ⚠ `RLY51-6` — THIS NAMED THE WRONG PROBE AND THE WRONG EXIT. `real_flags()` was
        # rewired to `record.py --list-flags` on 2026-09-06 and this message still said
        # `--help`; two of the four measured degradations exited 0, so "did not exit 0" was
        # false about them as well. The degradations all fail CLOSED, which is correct and is
        # exactly why the wording mattered: the only thing a reader gets is this sentence, and
        # it sent them to a flag the program no longer runs.
        print('\nCANNOT ASK: `record.py --list-flags` did not yield a usable flag list, so the')
        print('`flags` leg has no ground truth. A read failure, not a finding about the briefs.')
        return 2
    if steps is None:
        print('\nCANNOT ASK: the ledger could not be reached, so the `steps` leg cannot be')
        print('answered. NOT a pass and NOT a failure -- exit 2, per DC-45.')
        return 2
    print('  ground     %d record.py flag(s), %d registered step type(s)' % (len(flags), len(steps)))
    # ⚠⚠ `B3` GOES FROM LATENT TO VISIBLE HERE. The two ground-truth routes agreed exactly on
    # the day this was written -- 18 flags and 18 -- so nothing distinguished the parser from
    # its help prose, and one edit to a help string would have armed it silently. Printing the
    # DELTA means the day a flag-shaped word appears in a description, the run says so.
    # ⚠ It is a REPORT, not a leg: the parser wins, always. This never changes the verdict.
    _hp = subprocess.run([sys.executable, os.path.join(ROOT, 'tools', 'verify', 'record.py'),
                          '--help'], capture_output=True, text=True,
                         encoding='utf-8', errors='replace')
    _only = (flags_from_help(_hp.stdout) - flags) if _hp.returncode == 0 else None
    print('  prose      %s named in --help that the parser does NOT accept%s'
          % ('could not ask -' if _only is None else len(_only),
             '' if not _only else ': ' + ', '.join(sorted(_only))))
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
        if _rc == 4:
            print('\nREFUSED: the ledger was REACHED and REJECTED this record. That is a')
            print('         decision, not an outage -- the rule it named is printed above.')
            print('         TERMINAL: do not retry it. The same call will be refused again.')
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
