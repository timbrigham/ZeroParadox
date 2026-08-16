"""Durable gate-round counter — the tripwire for the severity-tiered review cap.

Why this exists: on 2026-07-19 the review loop ran THREE rounds against a 2-round cap. The rule was
available (memory index) and did not fire, because a rule about a loop does not fire from inside the
loop — each round is locally justified ("a gate found real defects; fix them"), and nobody was counting.
Tracking the count in a file, and PASSING IT TO THE REVIEWER, moves the stopping decision to the one
party standing outside the loop.

Usage:
    python gate_round.py show                  # current round + cap guidance
    python gate_round.py bump                  # increment before spawning a round
    python gate_round.py bump --target NAME     # ... and record WHAT is being re-fixed
    python gate_round.py reset                 # new arc / after a clean push

⚠ THE COUNTER DOES NOT AUTO-RESET, and this docstring claimed for months that it did (REL-4). The
claim was false in code AND wrong as a design: HEAD moves *during* an arc — the stub-first protocol
commits deliberately incomplete work as rollback points — so resetting whenever `HEAD != arc_base`
would wipe the count mid-arc. Measured 2026-08-10: the arc had advanced six commits and the counter
correctly stayed at 3.

What was actually broken was that the staleness was INVISIBLE, and the unsafe direction is
over-counting: a fresh arc inheriting an old count is told to stop on its round 1. So `show` now
WARNS when the recorded base is no longer HEAD, and you `reset` explicitly. A visible question beats
a silent wrong number.

SECOND TRIPWIRE (added 2026-08-03, Tim) — CLAIM REVALIDATION.
The cap above bounds how many times we ITERATE. It does not ask whether iterating is the right move
at all. Measured 2026-08-03: one sentence in ZP-P's remark box was wrong in SIX consecutive versions
(v1.9 a universal, v1.10 a doubling, v1.11 the universal restored, v1.13/v1.14 a false universal,
v1.15 a false uniqueness). Every gate round verified the WORDING against its sources and passed;
the sources were always fine. The defect was one level down: the claim the sentence existed to
support -- that Mathlib's `Classical.choice` in `cofix_nonempty` is "an artifact, not a necessity" --
had never been measured. One probe settled it: `QPF.Cofix` carries `Classical.choice` IN THE TYPE, so
no proof of any statement mentioning it can be choice-free, and "removable in principle" was
unprovable as stated. Six rounds of prose editing could never have found that, because the gates
check citations and the citations were correct.

So: prose that resists correction across rounds is a SYMPTOM. Past a threshold, stop editing it and
go measure the claim underneath. `--target` makes the tripwire fire on the real signal (the same
thing re-fixed) rather than on round count alone.
"""
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common  # noqa: E402
from common import REPO  # noqa: E402

# The Windows console defaults to cp1252, which cannot encode the warning glyphs used below — and a
# UnicodeEncodeError here is not cosmetic: it crashes the process, so `show` returns 1 instead of the
# 2 that means "past the bedrock cap", and every caller reads the crash as an ordinary failure.
# Measured 2026-08-10, immediately after adding that exit code.
#
# ⚠ This used to be a hand-rolled `try: sys.stdout.reconfigure(...)`, with the note that the file
# "stays standalone because everything calls it". Two of the eight copies of that guard had already
# dropped `line_buffering=True`, which is the divergence `common.utf8_stdout` exists to end. The
# standalone argument was about STDOUT and is satisfied by a layer-0 module that imports nothing.
common.utf8_stdout()

# Round state is per-arc PRIVATE state, not part of the published bundle: it records what THIS
# working session is mid-way through reviewing. It stays in `.claude-local/` while the tool itself
# is tracked, which is the split the 2026-08-15 move exists to make.
STATE = common.PRIV / 'gate_round.json'
SELF = common.self_rel(__file__)

BEDROCK_CAP = 5
ORDINARY_CAP = 2

# Rounds after which the claim underneath must be revalidated, regardless of severity.
REVALIDATE_ROUND = 3
# Times the SAME target may be re-fixed before revalidation is mandatory. This is the
# sharper trigger: three attempts at one sentence is a claim problem, not a wording problem.
REVALIDATE_TARGET_HITS = 3

REVALIDATION_PROTOCOL = """
  ================== MANDATORY CLAIM REVALIDATION ==================
  STOP EDITING THE PROSE. The instability IS the finding.

  Prose that will not stay correct across rounds is a symptom of a claim that was never
  measured. The gates verify wording against sources and will keep passing while the
  claim one level down is unsupported -- that is exactly how one ZP-P sentence stayed
  wrong through six versions with every round green on citations.

  Do this BEFORE writing another draft:

  1. NAME THE CLAIM the sentence exists to support, in one line, without the framing.
  2. ASK WHAT WOULD SETTLE IT -- and whether anyone ever did that. Not "is it cited?"
     but "is it PROVED, and by what?"
  3. WATCH FOR MODAL CLAIMS. "not a necessity" / "an artifact" / "in principle" /
     "could be removed" / "is eliminable" are claims about what CANNOT be proved,
     and a footprint measurement can never establish one:
       - ACCIDENTAL is proved only by EXHIBITING the clean proof.
       - ESSENTIAL is proved only by a REDUCTION to a taboo.
       - `#print axioms` follows the STATEMENT, not the proof -- a TYPE can carry an
         axiom, which makes "removable" false for every possible proof. Measure it.
  4. MEASURE IT. A probe in the scratchpad beats another draft. `lake env lean` on a
     standalone file works without touching the repo.
  5. THEN pick one:
       (a) the measurement supports it -> restate to what was measured, and cite it;
       (b) it does not -> restate as an explicit conjecture, or DELETE the sentence.
           Deleting is legitimate and often right: if an accurate statement already
           lives in a checkable file, published prose does not need to relitigate it.

  Record what the measurement showed -- not just that you re-worded something.
  ==================================================================="""


def head():
    return subprocess.run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True,
                          cwd=STATE.parent.parent).stdout.strip()


def load():
    """Read the counter. NEVER silently restart at 0 — that is a route around the cap.

    Measured 2026-08-10 by `guards.py` on its first run: an unparseable state file fell through to
    `{'round': 0}`, so corrupting one byte took the counter from "past the bedrock cap, refuse" to
    "round 1, proceed" with nothing said. That is the fourth route to a property whose first three
    routes (--target slug, --target with no value, no --target) had already been closed by hand —
    the exact recurrence the registry exists to catch.

    Missing and unparseable are DIFFERENT and get different answers. Missing is the normal state of
    a fresh clone, so round 0 is right — but it is announced, because deleting the file is otherwise
    an unlogged `reset`. Unparseable means the count is UNKNOWN, and an unknown count next to a cap
    must fail closed.
    """
    if STATE.exists():
        try:
            d = json.loads(STATE.read_text(encoding='utf-8'))
        except (OSError, ValueError) as e:
            return {'corrupt': str(e)}
        # ⚠ A well-formed file MISSING `round` is not round 0 — it is an unknown count wearing a
        # valid-JSON disguise, and `.get('round', 0)` restarted the counter with nothing said.
        # Found by /rely pass 6 as the SEVENTH route to this one property, after the six above.
        # ⚠ `isinstance(True, int)` is True in Python, so `{"round": true}` passed the type check and
        # then compared `True > 5` as `1 > 5` — exit 0 where `{"round": 6}` exits 2. And a NEGATIVE
        # round passed everything. Routes eight and nine to this one property (/rely pass 7).
        r = d.get('round') if isinstance(d, dict) else None
        if not isinstance(d, dict) or isinstance(r, bool) or not isinstance(r, int) or r < 0:
            return {'corrupt': 'no non-negative integer `round` key (got %r)' % (
                r if isinstance(d, dict) else type(d).__name__)}
        return d
    return {'round': 0, 'arc_base': head(), 'fresh': True}


def save(d):
    # ⚠ Via the shared writer, which creates `.claude-local/` if it is absent. It IS absent in every
    # clone that is not the author's, and `bump` used to die there with a raw FileNotFoundError —
    # on the one command CLAUDE.md requires the CALLER to run before spawning any review round.
    common.write_text_lf(STATE, json.dumps(d, indent=2) + '\n')


def guidance(n, targets=None, arc_base=None):
    targets = targets or {}
    lines = [f'  Gate round: {n}',
             f'  Caps: BEDROCK {BEDROCK_CAP} iterations / ORDINARY {ORDINARY_CAP} iterations']

    # The counter does not auto-reset (see the module docstring). Make the staleness VISIBLE, since
    # the unsafe direction is a fresh arc inheriting an old count and being told to stop on round 1.
    if arc_base and n > 0:
        cur = head()
        if cur and cur != arc_base:
            lines += ['',
                      f'  ⚠ base recorded {arc_base[:7]}, HEAD is now {cur[:7]}.',
                      '    Committing during an arc is normal (stub-first), so this is NOT'
                      ' automatically wrong —',
                      '    but if this is NEW work rather than a continuation, run'
                      ' `gate_round.py reset` first.',
                      '    An inherited count stops a fresh arc early.']

    repeat = sorted((t for t, c in targets.items() if c >= REVALIDATE_TARGET_HITS),
                    key=lambda t: -targets[t])
    if repeat:
        lines += ['', '  ** REPEAT TARGETS (re-fixed %d+ times in this arc): **' % REVALIDATE_TARGET_HITS]
        lines += ['       %s  x%d' % (t, targets[t]) for t in repeat]

    if n >= REVALIDATE_ROUND or repeat:
        why = ('the same target has been re-fixed %d+ times' % REVALIDATE_TARGET_HITS) if repeat \
            else ('this is round %d' % n)
        lines += ['', '  TRIGGERED: %s.' % why, REVALIDATION_PROTOCOL]

    if n > ORDINARY_CAP:
        lines += [
            '',
            f'  ** PAST THE ORDINARY CAP ({ORDINARY_CAP}). **',
            '  This round may ONLY continue the loop if it finds something BEDROCK-tier:',
            '    a violated core invariant (epsilon-zero != 0, epsilon-zero != bottom, min/max',
            '    flattened, snap-arc returning to the SAME bottom, a cross-type equality), a',
            '    FABRICATED claim about an external source, or a false premise carrying a conclusion.',
            '  Anything else -> verdict is STOP-ORDINARY: push despite the findings. Do not iterate.',
        ]
    if n > BEDROCK_CAP:
        lines += ['', f'  ** PAST THE BEDROCK CAP ({BEDROCK_CAP}) TOO. Stop regardless. Escalate to Tim. **']
    return '\n'.join(lines)


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'show'
    d = load()

    # An UNKNOWN count next to a cap fails closed. `reset` is the sanctioned way out, and it is a
    # deliberate typed act that leaves a well-formed file behind.
    if d.get('corrupt') and cmd != 'reset':
        print('  ** gate_round.json is UNREADABLE (%s). **\n'
              '  The round count is UNKNOWN, so the cap cannot be enforced and this refuses.\n'
              '  If this is genuinely a new arc, run: python gate_round.py reset'
              % d['corrupt'])
        return 2

    if cmd == 'reset':
        # ⚠ RECORD WHAT WAS RESET FROM. `reset` is the sanctioned way out of a cap, and it was also
        # a SILENT one: round 6 (exit 2) became round 0 (exit 0) with no later output mentioning it.
        # A permitted route must still be visible — the same requirement the vendored allowlist
        # carries. `show` now announces a reset that walked a cap.
        was = d.get('round', 0) if not d.get('corrupt') else None
        d = {'round': 0, 'arc_base': head(), 'targets': {}, 'reset_from': was}
        save(d)
        print('gate round reset to 0 (targets cleared; was round %s)' % was)
        return 0

    if cmd == 'bump':
        d['round'] = d.get('round', 0) + 1
        targets = d.setdefault('targets', {})
        if '--target' in sys.argv:
            i = sys.argv.index('--target')
            if i + 1 < len(sys.argv):
                name = sys.argv[i + 1].strip()
                targets[name] = targets.get(name, 0) + 1
        save(d)

    n = d.get('round', 0)
    rf = d.get('reset_from')
    if isinstance(rf, int) and rf > ORDINARY_CAP:
        print('  ** counter was RESET from round %d — a cap was walked by resetting it. **\n'
              '  Legitimate for genuinely new work; if this is the same arc, the count is lost.'
              % rf)
    if d.get('fresh'):
        # Deleting the file is otherwise an unlogged `reset`. Say so, so a restart is never quiet.
        print('  (no state file — treating this as a FRESH ARC at round 0)')
    print(guidance(n, d.get('targets', {}), d.get('arc_base')))
    # ⚠ EXIT NON-ZERO PAST THE BEDROCK CAP so a caller can actually act on it. Until 2026-08-10 this
    # printed "Stop regardless. Escalate to Tim." and exited 0, so every consumer sailed past the one
    # boundary the cap exists to defend. The cap's ORDINARY tier stays advisory by design — the
    # REVIEWER decides STOP-ORDINARY vs FAIL-BEDROCK, standing outside the loop — but the BEDROCK
    # tier is the backstop on that judgement, and a backstop that returns success is not one.
    return 2 if n > BEDROCK_CAP else 0


if __name__ == '__main__':
    sys.exit(main())
