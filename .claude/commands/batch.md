# /batch — the pre-configured verification workflow

Run one debaselining batch end to end. **`$ARGUMENTS` is the bucket name** (`class`, `modal`,
`pov`, `prose-unlabelled`, `prose-bare`, `prose-doc`, `prose-block`).

**This file is POLICY. `tools/verify/batch.py` is ENFORCEMENT.** A command file alone is
bypassable by construction — on 2026-08-09 a stage was skipped by an instance that knew the rule.
The script refuses to advance, so every step described here has a matching precondition there.
Where a step cannot be checked mechanically the script still demands a `--note`, which turns
*forgetting* into *lying* — a much rarer failure.

**If a stage BLOCKS, fix the cause. Never work around it.** Do not delete `batch_state.json`, do not
`--no-verify`, do not push a subset to dodge a signal. A block is the control working; the two
recorded bypasses in this project (a SIGPIPE pipe and a `|| --no-verify` fallback) both happened
because someone treated a block as an obstacle.

---

## Stage 0 — orient (before `start`)

Read, in this order:
1. `.claude-local/DEFECT_CLASSES.md` — the classes and their **detectors**. Pick the detector by id.
2. `.claude-local/DEFECTS.md` — open instances. **The bucket's sites may already be recorded there.**
3. `.claude-local/VERIFICATION_BUILDOUT.md` — the phase this batch belongs to and its exit criterion.

Then `python tools/verify/batch.py start --bucket $ARGUMENTS`. This snapshots the checker hashes,
so any mid-batch change to a filter becomes visible rather than silently moving the target.

## Stage 1 — `ledger`

**Consult `DEFECTS.md` and `CLAUDE.md` for EVERY site before probing anything.**

This is a stage because skipping it is this project's most expensive recurring error. On 2026-08-09,
three "findings" duplicated rows already in the ledger, and two classes already had complete answers
recorded. Grep the **claim**, not the name. Read hits; never count them.

`batch.py stage ledger --note "<what was already recorded, and what genuinely is not>"`

## Stage 2 — `screen`

Bulk-classify the worklist with the cheap tier (`.claude-local/deepseek/`), **wide, not nested** —
over the full bucket, not over what the mechanical filter flagged. DC-17 measured the detectors as
**complementary**: the regex caught two defects the LLM missed in 4/4 runs, and the LLM caught two
the regex structurally cannot see. Feeding one the other's output inherits every false negative.

Take sites flagged in **≥2 of 3 runs** — single-run positives are unstable (1/4/4/3 false positives
on identical negatives).

**Skipping is permitted when the bucket's question needs an ARTIFACT** (class degeneracy is settled
by building a witness; DC-17 puts the screen at 0/8 there). Record the reason in the note.
**Nothing the screen says ever auto-clears a site** — a label asserts that a person verified it.

## Stage 3 — `probe`

**Run something.** Every BEDROCK finding across ~20 agent runs came from executing; every ORDINARY
one from reading. Build the trivial witness, write the `example` that fails when the gloss is wrong,
measure the footprint. Probes go in the **session scratchpad**, never in the repo.

A failed probe is a finding, not a dead end.

## Stage 4 — `judge`

Two terminal states per site, and **neither is "grandfathered": FIX it, or LABEL it in-source.**
⚠ **Fix before label, always** — labelling first grandfathers defects under a new name.

Prefer **deletion**: measured across one arc, deletions ran a zero error rate while authored prose
ran roughly one wrong in seven. A label must **name the class it is about** (`check_classes.py`
requires it, and two notes failed that check on first write).

## Stage 5 — `precommit`, then commit

`batch.py precommit` verifies: filters unmoved since start · build green · a `#print axioms` entry
for every added declaration · every added declaration in `ssot.json` · all checkers at 0 new.

Then commit with `git add` **named paths** — never `-A`.

## Stage 6 — `prepush`, then the gates

`batch.py prepush` reports which reviews are **required**, validating each signal by hash and
coverage rather than existence. Run the required gates from `.claude/commands/*.md` **verbatim, as
separate agents**. Bump `gate_round.py` once per round with a stable `--target`; reviewers may only
`show`.

**Routing beyond the three prose gates:**

| condition | routes to | why |
|---|---|---|
| a **checker or hook** changed | **`/rely`** | its only run produced CHK-2 and CHK-3, both checker bugs. The three prose gates never ask whether a check checks what it says |
| a **CI workflow** changed | `/rely` | a fail-open here publishes a false verification claim |
| ≥50 net `.lean` lines, or a new file | `/prior-art-review` | trigger 5 |

Record each with `batch.py review /rely`. Push only on fresh signals; never pipe `git push` through
`head`/`grep -q`.

## Stage 7 — `close`

Prune the baseline — **remove entries, never regenerate.** Regeneration grandfathers sites nobody
read, which falsifies the baseline's own premise. Assert the result is a strict subset. Record
findings in `DEFECTS.md`, then `batch.py close`.

---

## Standing cautions

- **A new tool's first run goes against data whose answer you already know.** Every proxy check
  found on 2026-08-09 was caught that way and by nothing else (DC-18).
- **Verify a detector before believing a zero — and before believing a non-zero.** A false positive
  manufactures urgent-looking work; a survey once reported six mismatches and all six were the
  detector's.
- **Fixing a finding creates new unreviewed prose** and restarts the obligation for what changed.
  Under a STOP-ORDINARY, push what was certified rather than editing further.
- **Filter changed mid-batch?** The batch was worked against a moving target. Re-run the worklist or
  start a new batch — do not paper over the drift warning.
