"""Point-of-view vocabulary check — every POV claim must declare its KIND and its STATUS.

WHY THIS EXISTS (2026-07-30). "Point of view" / "chart" / "frame" was doing FIVE different jobs with
one word, and the cost was measured: a full day of gate rounds, two bedrock findings, and a
correction that itself over-corrected into DENYING the framework's own thesis. The sequence was:
  1. `snap_is_frameflip` was cited as proving the snap IS a change of frame. Its statement contains
     no snap. That is the witness-vs-statement defect.
  2. The fix wrote "the POLE EXCHANGE (NOT of the snap)" into a dozen sites — which denies a reading
     that is well-motivated and is the layer's stated conjecture. Over-correction.
  3. Neither error is possible if every POV claim must say WHICH KIND it is and WHETHER IT IS PROVED.

This is the FOURTH attempt at a convention of this shape (see `vocabulary_reference.md`: the bare
"bottom" rule, "iterative bottoms", and standard-math-term-first). The previous three are all
discipline-level and all still leak, for the reason `feedback_jargon_blindspot` records: Claude is
embedded in the project's language and structurally cannot self-detect vocabulary drift. So this one
is MECHANICAL — detection, not memory.

  WARN at commit, BLOCK at push.

THE VOCABULARY — every POV claim declares a KIND and a STATUS.

  KIND (what sort of point-of-view phenomenon):
    COINCIDENCE   both readings hold of ONE object simultaneously
                  (⊥ yields nothing AND never halts; ε₀ is min AND max; seam initial AND terminal)
    INVERSION     a map EXCHANGES the two readings; always an involution
                  (`rInv_swaps`, `swap_involutive`, `flipPoles_involutive`)
    DRIFT         two measures run OPPOSITE along one sequence
                  (`pole_inversion` — element descends while complexity ascends)
    CARRIER       the claim's TRUTH VALUE depends which carrier you are in
                  (snap available in Q_2, impossible in R; both completions of Q — Ostrowski)
    INVARIANT     the quantity DOES NOT transform; flipping the chart gains nothing
                  (measure-zero-ness, cardinality)

  STATUS — folded into the EXISTING `Statement:` / `Reading:` gloss convention, deliberately.
  This adds no fifth label to remember:
    `Statement:` + KIND   the theorem proves it. Name the witness.
    `Reading:`   + KIND   the framework reads X as an instance of that kind. Conjectural.
                          NOT a denial — there is no slot for denying a reading, by design.

⚠⚠ WHAT THIS DOES NOT DO — READ BEFORE RELYING ON A ZERO.

**This enforces that a convention was FOLLOWED. It never checks that a claim is TRUE.**
`check_classes.py:25` has said so about this file since it was written; this file did not say it
about itself, and a reader who only opened this one could not have known. Measured 2026-08-17 by a
`/rely` trial that planted defects and ran the gate, so each item below is a reproduction, not a
worry:

  * **A tag LAUNDERS ITS NEIGHBOURS.** KIND and LABEL are searched in an **8-line WINDOW**
    (`lines[i-6:i+2]` — five lines above, the line, two below), not on the line. So an honest
    `Reading:` CARRIER two lines up certifies a false claim below it. The trial replaced
    `SnapDichotomy.lean`'s own fence with its exact negation — the retracted "totally disconnected
    TO the snap" arrow, verbatim — and got `--block` exit 0, `hooks.py pre-commit` exit 0, with the
    inverted claim COUNTED in `tagged POV claims` (44 -> 46). The number a reader takes for good
    news went up.
    ⚠ And the 2026-08-17 remediation ADDED tags at the four sites where this class recurs, so the
    laundering window is now centred exactly on the recurrence sites. The fix made this worse.
  * **WORSE: no real tag is needed.** KIND and LABEL are searched INDEPENDENTLY, so the bare word
    `CARRIER` in ordinary prose plus a bare `Statement:` on a different, unrelated line satisfies
    the test. Neither has to be a gloss, and neither has to be about the claim.
  * **The gate can be WALKED PAST by typing.** `Statement:` CARRIER on the line, or on a
    neighbouring unrelated line, satisfies it with the claim left flatly false. Tagging is the
    whole test.
  * **`ALLOW` is matched against the LINE**, so any line containing `CORRECTED`, `check_pov.py`,
    `vocabulary_reference` or a `v1.N:` token is exempt whatever else it says — and per the note at
    `DENIAL` below, that mutes the DENIAL check too.
  * **Scope holes, all reproduced silent.** ACROSS lines: a claim wrapped over two (there is no
    separator normalisation here, unlike `check_modal.py`). WITHIN a line, and this is the one a
    markdown ledger actually hits: `totally **disconnected**`, `totally *disconnected*`,
    `totally-disconnected`, `totally <b>disconnected</b>`, a double space and a non-breaking space
    are ALL silent where the plain form fires — measured, in `CLAIMS.md`, which is published and is
    the file this defect occurred in. By FILE: `ZeroParadox/MANIFEST.md`, `RELEASES.md` and most
    tracked `.md` are absent from `TARGETS`. And any claim with no backticked declaration name
    within the window is skipped, which is how the build scripts that render this vocabulary into
    PUBLISHED PDFs stay out of remit.

**So a zero here means "nobody skipped the label", never "the corpus says nothing false."** The
truth question belongs to `/reconstruct`, `/rely` and the adversary gate, which read the elaborated
statement. Do not cite this gate as evidence that a carrier claim is correct.

⚠⚠ **AND THE HONEST FRAME, WHICH THE LIST ABOVE SHOULD NOT BE READ AS CONTRADICTING: this is a
DISCIPLINE AID AGAINST FORGETTING, NOT A CONTROL AGAINST AN ADVERSARY.** A tag-presence test cannot
be made adversary-proof — every route closed leaves another, because the property it would need to
decide ("is this carrier claim true?") is not mechanically decidable. Chasing evasion routes one at
a time is the whack-a-mole this project records as its most repeated defect. **Treat the list above
as an enumeration of what it does not cover, not as a to-do list to be driven to zero**, and put the
weight on the gates that read the elaborated statement.

Usage:  check_pov.py [--block]     (the exact invocation path is printed in this tool's output)
Exit 0 = clean (or warn-only mode).  Exit 1 = untagged POV prose found AND --block was passed.
"""
import hashlib
import re
import sys
from pathlib import Path

# Roots come from `common` — one derivation for the whole bundle. SELF is derived from `__file__`,
# never written down: a hardcoded invocation path is a copy of the path, and copies drift.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import common  # noqa: E402
from common import HERE, REPO, SRC  # noqa: E402
from vendored import is_vendored  # noqa: E402

SELF = common.self_rel(__file__)

# ⚠ THIS CHECKER'S SCOPE IS ITS OWN, DELIBERATELY, AND IT IS NOT `common.targets()`. Four named
# reader-facing markdown files and `build_*.py` only — a narrow, hand-picked list, where the
# `targets()` family scans every tracked `.md` and every `.py` under `tools/` and `scripts/`.
# Folding this into the shared enumerator would silently WIDEN a gate that is baselined at ~78
# grandfathered sites, which is a different change wearing a refactor's clothes.
#
# Vendored backports are EXEMPT STRUCTURALLY (see vendored.py) — nothing here fires on them today,
# so that closes a latent hole rather than a live one, and it stops a future vendored drop from
# being reported as our prose.
TARGETS = (
    [p for p in sorted(SRC.rglob('*.lean'))
     if not is_vendored(p, p.relative_to(REPO))]
    + sorted((REPO / 'scripts').glob('build_*.py'))
    + [REPO / p for p in ('README.md', 'CLAIMS.md', 'SNAP.md', 'BOTTOMELEMENT.md')]
)

# The predefined term list: vocabulary that SIGNALS a point-of-view claim.
#
# ⚠ THE CARRIER VOCABULARY WAS MISSING FOR THIRTEEN MONTHS, AND CARRIER IS THIS CHECKER'S OWN
# WORKED EXAMPLE. The docstring above illustrates the CARRIER kind with *"snap available in Q_2,
# impossible in R; both completions of Q — Ostrowski"* — and none of `totally disconnected`,
# `total disconnectedness` or `domain of validity` was in this pattern, so the gate could not see
# the one claim it names. Measured 2026-08-17: adding them reported the *"Q_p totally disconnected =
# snap"* row in the PUBLIC claims ledger `CLAIMS.md`, and the *"totally disconnected -> snap"*
# bullets in `SnapDichotomy.lean`'s module docstring. (Named by FILE and CONTENT, never by line
# number — a line number is a copy of a location and drifts exactly like any other copy. The
# pointer here said `:23,25` for one day and the lines had already moved.)
#
# ⚠ WHAT THE ZERO ELSEWHERE DOES *NOT* MEAN, because an earlier version of this comment said it did.
# `Padic.lean` reports zero under this vocabulary, and that was offered here as evidence of
# precision — *"it leaves the file that states the honest form reporting ZERO"*. **The zero is
# real and the inference was false.** Measured by an editorial gate the same day: planting a flatly
# dishonest carrier claim at four of `Padic.lean`'s own sites, each in its own window, stays SILENT
# at all four; the same text with a backticked declaration name on the line FIRES. So the file is
# out of remit via `CITES_DECL`, not cleared by it, and the gate would stay silent there if the file
# asserted the opposite. That is a must-suppress passing for an unrelated reason — it looks like
# confirmation and is not — sitting in the justification block for a gate change.
#
# ⚠ `CITES_DECL` IS WHAT BOUNDS THE BLAST RADIUS, so anyone widening the window should know what it
# holds back. A claim is skipped entirely unless a backticked declaration name sits within six
# lines. The skipped set includes `Padic.lean` — the canonical home of this argument — and the
# `scripts/build_*.py` strings that render this vocabulary into PUBLISHED PDFs. So this closes the
# class wherever a declaration name happens to sit nearby, which is a proxy for "is a claim" rather
# than the property itself. It also does NOT match the upstream phrasing this whole family started
# from, *"removes the topological obstruction"*.
#
# ⚠ NO COUNTS ARE RECORDED HERE, DELIBERATELY. This comment carried "59 lines … 47 skipped" for one
# day; regenerated, it was 58 and 46, matching neither the commit that recorded it nor its parent —
# the fixes in that same commit deleted a matching line, so the figure went stale INSIDE the commit
# that wrote it. Measure on demand instead: run this checker and read the hits.
#
# The class had recurred at least four times: `Padic.lean`'s *"the snap is forced"* (retracted
# 2026-07-31), the two live sites above, and twice in `SnapCannotBe.lean` § V on 2026-08-16, the
# first of which was a FAIL-BEDROCK. Per the escalation ladder, a 4th occurrence is the rung where
# discipline stops working and a mechanical check is the response. This is that check, and it is a
# VOCABULARY ADDITION rather than a new checker: a carrier-property-versus-snap claim IS a
# CARRIER-kind point-of-view claim, so it was always in this gate's remit and never in its pattern.
POV_TERMS = re.compile(
    r'(point of view|change of frame|frame[- ]change|frame[- ]flip|frameflip'
    r'|pole exchange|both poles|two chart|chart[- ]reading|reads as both'
    r'|swaps? the poles|min\s*≡\s*max|both min and max'
    r'|both extremal|initial AND terminal|least AND greatest'
    r'|totally disconnected|total disconnectedness|domain of validity'
    r'|totally separated|total separatedness|zero[- ]dimensional'
    r'|range of applicability'
    r'|ultrametric.{0,30}(suffic|forc|yield|give|suppl)|carrier requirement)',
    re.IGNORECASE,
)

KINDS = re.compile(r'\b(COINCIDENCE|INVERSION|DRIFT|CARRIER|INVARIANT)\b')
LABEL = re.compile(r'\b(Statement:|Reading:)')

# DENIALS — the convention's other half, and the half a tag-check cannot see.
# `CLAUDE.md`'s POV section says there is deliberately NO slot for denying a reading: if a theorem
# does not establish an identification, write `Reading:` and mark it conjectural. Writing "NOT the
# snap" instead denies a claim the framework actually holds — that was the SECOND bedrock failure of
# 2026-07-30, and the editorial gate had to catch four surviving sites by eye at round 5 because this
# checker only looked for MISSING tags. A denial is always wrong regardless of tagging, so it is
# NOT baselined — no grandfather list can mute it.
#
# ⚠ BUT IT IS NOT "CHECKED UNCONDITIONALLY", WHICH THIS COMMENT CLAIMED UNTIL 2026-08-17.
# `verdict()` computes `DENIAL.search(line) and not ALLOW.search(line)`, so **`ALLOW` mutes a
# denial exactly as it mutes a tag check.** Measured: prefixing a planted denial with `CORRECTED`,
# `v1.4:`, `vocabulary_reference` or `check_pov.py` takes it from reported to silent.
#
# That coupling is DELIBERATE and the corpus needs it — a recorded correction QUOTES the wording it
# retracts, and flagging the retraction as if it were making the claim is the cry-wolf shape. The one
# corpus line this currently mutes is a build-script docstring changelog recording a past adversary
# round; making the check unconditional would fire on an honest historical record, so do not simply
# invert the boolean.
# **The cost is real and is the thing to know: an author can mute a genuine denial by typing one
# allowlisted token on the line.** Narrowing `ALLOW` (it exempts hundreds of lines in scope, many by
# the ordinary English word "corrected") is the fix, and it is tracked in the defect ledger rather
# than done here, because narrowing it changes what the TAG check sees as well.
DENIAL = re.compile(
    r'(NOT the snap|NOT of the snap|NOT that the snap|is not the snap'
    r'|never the same map|were never the same map)',
    re.IGNORECASE,
)

# Intentional collisions — `project_notation_notes`: the bottom / epsilon-nought / P-zero overloads
# are deliberate and must NEVER be flagged. A checker that cries wolf gets muted, and a muted gate
# is worse than no gate.
ALLOW = re.compile(
    r'check_pov\.py'                       # this file's own documentation
    r'|vocabulary_reference'               # the vocabulary guide itself
    r'|^\s*--\s*\[ZP-CUSTOM\]'             # registry tags
    r'|CORRECTED|corrected 20|an earlier revision'   # recorded corrections quote the old wording
    r'|v1\.\d+:|v2\.\d+:',                 # docstring changelogs are history, not claims
    re.IGNORECASE,
)

# A POV term only needs a tag when it sits in a CLAIM — i.e. near a declaration citation.
CITES_DECL = re.compile(r'`[a-z][A-Za-z0-9_]*_[A-Za-z0-9_]+`|`[A-Z][A-Za-z]+\.[a-z]')


def read(p):
    try:
        return p.read_text(encoding='utf-8', errors='replace')
    except FileNotFoundError:
        return ''


def verdict(line, window):
    """The per-line decision, EXTRACTED so `--selftest` exercises the real path.

    `scan()` walks a file tree, so a control could only test a hand-copied replica of this logic —
    and a replica drifts from the thing it certifies, which is the mirror problem this project keeps
    paying for. `scan()` now calls this, so the controls test what actually runs.

    Returns (is_denial, status) where status is 'skip' | 'tagged' | 'untagged'."""
    is_denial = bool(DENIAL.search(line) and not ALLOW.search(line))
    if not POV_TERMS.search(line) or ALLOW.search(line):
        return is_denial, 'skip'
    if not CITES_DECL.search(window):
        return is_denial, 'skip'      # prose with no witness citation is not making a POV CLAIM
    if KINDS.search(window) and LABEL.search(window):
        return is_denial, 'tagged'
    return is_denial, 'untagged'


# --------------------------------------------------------------------------- controls
_W = '`some_thm_name` '            # a witness citation, required before a line counts as a claim

# ⚠ Phrases below are taken FROM `POV_TERMS`, not invented. A first draft guessed the vocabulary
# ("change of chart", "the two readings") and all three must-fire controls returned 'skip' — the
# controls were wrong, not the checker. Read the pattern; do not paraphrase it.
MUST_FIRE = [                       # must be reported UNTAGGED
    ('POV term, no KIND, no label',
     _W + 'the bottom reads as both the zero pole and the infinity pole.'),
    ('KIND present but no label',
     _W + 'this is the pole exchange, a COINCIDENCE at one object.'),
    ('label present but no KIND',
     _W + '`Statement:` the seam is initial AND terminal.'),
    # ⚠ The CARRIER controls. Taken from the two sites this vocabulary was added for, so a future
    # narrowing of the pattern takes them from FIRE to MISSED rather than passing silently.
    ('carrier property identified WITH the snap',
     _W + 'completions of Q: Q_p totally disconnected = snap, R connected = no snap.'),
    ('carrier property claimed to YIELD the snap',
     _W + 'Q_p (the non-Archimedean completions): totally disconnected -> snap.'),
    ('the scope claim, which is the same error in prose form',
     _W + "the Binary Snap's domain of validity is exactly the non-Archimedean completions."),
]
MUST_SUPPRESS = [                   # must NOT be reported
    ('fully tagged',
     _W + '`Statement:` COINCIDENCE — the seam is initial AND terminal.'),
    ('Reading + KIND',
     _W + '`Reading:` INVERSION, conjectural — the map swaps the poles.'),
    ('no witness citation', 'the bottom reads as both poles here.'),
    ('no POV vocabulary at all', _W + 'the floor has complexity ⊤.'),
    ('allowlisted — a recorded correction',
     _W + 'CORRECTED 2026-07-30: it reads as both, which an earlier revision denied.'),
    # ⚠ The CARRIER must-suppress: the HONEST form of the same claim, tagged, must stay silent.
    # Without this, narrowing the fix to "ban the vocabulary" would look correct and would make the
    # gate un-satisfiable — there would be no way to state the true claim at all.
    ('carrier claim, fully tagged',
     _W + '`Statement:` CARRIER — Q_p is totally disconnected and R is not.'),
]
MUST_DENY = [                       # must be reported as a DENIAL — never baselined
    ('explicit denial of a reading',
     _W + 'the pole exchange (NOT of the snap) is what the theorem shows.'),
]


def selftest():
    # Three groups, not two — the denial group is this checker's own, and the shared harness takes
    # a list of groups precisely so a third does not force a hand-written loop back into the file.
    bad = common.run_controls([
        ('MUST FIRE (untagged POV claim)', MUST_FIRE,
         lambda line: verdict(line, line)[1] == 'untagged', True, 'MISSED',
         lambda line: ' (%s)' % verdict(line, line)[1]),
        ('MUST SUPPRESS', MUST_SUPPRESS,
         lambda line: verdict(line, line)[1] == 'untagged', False, 'FALSE POSITIVE'),
        ('MUST DENY (never baselined)', MUST_DENY,
         lambda line: verdict(line, line)[0], True, 'DENIAL NOT DETECTED'),
    ], width=32)
    # ⚠ THE SCOPE PIN (SCOPE-3). This checker enumerates its own `TARGETS` deliberately — folding it
    # into `common.targets()` would WIDEN a gate baselined at ~78 grandfathered sites. But a private
    # enumerator still needs pinning: narrowing this list took a planted violation from detected to
    # undetected with the whole suite green, because `common.py`'s pin only covers the SHARED
    # enumerator and correctly reported it intact. Independent scope, independent pin.
    # ⚠ THE VOCABULARY PIN (PAT-1). The controls above prove the patterns they exercise;
    # this proves the rest are still there. Measured before it was written: 30 of 34
    # list-shaped patterns could be deleted with every control green, and the compiled
    # regexes carrying the rest of the vocabulary were pinned by nothing at all.
    print('PATTERNS')
    bad += common.check_vocabulary('check_pov', globals())
    print('SCOPE')
    bad += common.check_scope(
        'check_pov', [str(p.relative_to(REPO)).replace('\\', '/') for p in TARGETS if p.is_file()])
    if bad:
        print('\nselftest: FAIL (%d)' % bad)
    return 1 if bad else 0


def scan():
    """Return (untagged, tagged, denials). Denials are never baselined — always wrong."""
    untagged, tagged, denials = [], [], []
    for f in TARGETS:
        text = read(f)
        if not text:
            continue
        lines = text.split('\n')
        for i, line in enumerate(lines, 1):
            # Context window: the tag may sit a few lines above, in the same gloss block.
            lo = max(0, i - 6)
            window = '\n'.join(lines[lo:i + 2])
            is_denial, status = verdict(line, window)
            rel = str(f.relative_to(REPO)).replace(chr(92), '/')
            if is_denial:
                denials.append((f'{rel}:{i}', line.strip()[:110]))
            if status == 'skip':
                continue
            if status == 'tagged':
                tagged.append(f'{rel}:{i}')
            else:
                # KEY ON CONTENT, NOT LINE NUMBER. A line-keyed baseline is invalidated by any edit
                # that shifts lines — measured 2026-07-30: one unrelated edit turned 7 grandfathered
                # sites into false "new" hits, i.e. the cry-wolf failure this gate must not have.
                # Content-keying also means EDITING a grandfathered line correctly un-grandfathers it.
                key = f'{rel}::{hashlib.sha256(line.strip().encode("utf-8")).hexdigest()[:12]}'
                untagged.append((key, f'{rel}:{i}', line.strip()[:110]))
    return untagged, tagged, denials


BASELINE = HERE / 'pov_baseline.txt'


def load_baseline():
    """Pre-existing untagged sites, grandfathered. The gate blocks on NEW ones only.

    Measured 2026-07-30: the corpus already carries ~90 untagged POV claims. Demanding a tag on all
    of them is a migration, not a gate, and a gate that blocks everything on day one gets bypassed
    and then ignored. So this follows the project's standing as-touched rollout (same as the
    file-path and CC-2 conventions): NEW prose must be tagged; existing sites convert when their
    file is next opened, and each conversion shrinks the baseline.

    `field0=True`: this baseline is tab-delimited, key first, with the site's location and text
    after it. The shared reader takes the key.
    """
    return common.load_baseline(BASELINE, field0=True)


def ascii_safe(s):
    return s.encode('ascii', 'replace').decode('ascii')


def main():
    block = '--block' in sys.argv
    untagged, tagged, denials = scan()
    if '--update-baseline' in sys.argv:
        # ⚠ LF, via the shared writer. A bare `write_text` emits CRLF on Windows and this file is
        # TRACKED, so regenerating used to leave the tree failing `check_invariants`.
        common.write_text_lf(
            BASELINE,
            '# Grandfathered untagged point-of-view claims. See check_pov.py.\n'
            '# Shrink this file as sites are tagged; never grow it deliberately.\n'
            + '\n'.join(f'{k}\t{loc}\t{ascii_safe(sn)}' for k, loc, sn in sorted(untagged)) + '\n')
        print(f'baseline written: {len(untagged)} grandfathered site(s)')
        return 0
    base = load_baseline()
    new = [(k, loc, sn) for k, loc, sn in untagged if k not in base]
    print('')
    print('=== Point-of-view vocabulary check ===')
    print(f'  tagged POV claims:        {len(tagged)}')
    print(f'  grandfathered (baseline): {len(untagged) - len(new)}')
    print(f'  NEW untagged POV claims:  {len(new)}')
    print(f'  DENIALS (never allowed):  {len(denials)}')
    if denials:
        print('')
        print('  The convention has NO slot for denying a reading. If a theorem does not establish')
        print('  an identification, write `Reading:` + KIND and mark it conjectural.')
        print('')
        for loc, snippet in denials:
            print(f'    {loc}')
            print('        ' + ascii_safe(snippet))
    if new:
        print('')
        print('  These use point-of-view vocabulary beside a declaration citation without')
        print('  declaring a KIND (COINCIDENCE / INVERSION / DRIFT / CARRIER / INVARIANT)')
        print('  under a `Statement:` or `Reading:` label. See this script\'s docstring.')
        print('')
        for _k, loc, snippet in new:
            print(f'    {loc}')
            print('        ' + ascii_safe(snippet))
    print('======================================')
    if (new or denials) and block:
        print('')
        print('Push blocked: NEW untagged point-of-view claim(s) and/or DENIAL(s).')
        print('Fix the finding, or record it in .claude-local/DEFECTS.md and fix the')
        print('site it points at. CI re-runs this checker on pushes and PRs to `main`')
        print('(.github/workflows/verify.yml), but REPORT-ONLY - it publishes the finding')
        print('and does not fail the run. So this is still the last check that STOPS a')
        print('change reaching the remote. Bypassing it ships the change unchecked.')
        return 1
    if new or denials:
        print('')
        print('WARNING ONLY (no --block). Tag these before pushing.')
    return 0


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(selftest())
    sys.exit(main())
