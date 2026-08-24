# Narrating the mathematics, the pipeline, and the defect register

**Body for `CLAUDE.md` §§ `R-NARRATE`, `R-PRECOMMIT` and `R-DEFECTCLASS`.** The rules are
there; Tim's original instruction, the pipeline manifest argument and the defect-register
triggers with their measured counts are here.

---

## NARRATE THE MATH — in an engineer's register, every report. (Tim, 2026-08-12.)

> *"for future iterations I want you to narrate the math for me. and do it in terms fitting to an
> engineer that's not a mathematician by trade."*

**Every report touching mathematical content carries a plain-language pass on the MATHEMATICS, beside
the process summary — not instead of it, and not only when asked.** Long verification arcs drift into
reporting gate verdicts, defect ids, signal freshness and exit codes. That is scaffolding. *"The
prior-art gate verified AMM Thm 7.2 p. 27"* says a check passed; it does not say what the theorem
**states** or why its direction was load-bearing.

**Tim is this project's mathematician of record by decision, not by training. He cannot review what is
never explained, and his review is the control that has repeatedly caught what the gates did not.**

- **Use systems and programming analogies** — recursion and termination, type signatures,
  preconditions, interface vs implementation, invariants, null vs empty, cycles in a graph. Name the
  object before using its symbol.
- **Spell glyphs out in words at least once per paragraph** (bottom, epsilon-zero, infinity) — the
  standing mobile-readability rule.
- **Standard mathematical term first, ZP shorthand after.** Narration is never licence to lead with
  framework vocabulary; the § on language ordering still governs.
- **State which direction an implication runs, and why that matters.** The 2026-08-12 arc turned
  entirely on sufficiency versus necessity in a cited theorem, and *"the biconditional overstates the
  source"* is precisely the phrasing that hides the point from anyone not already holding it.
- **Do not soften the claim.** Precision is the deliverable; only the register changes. If a
  distinction is load-bearing, explain it rather than dropping it.

⚠ **This governs REPORTS TO Tim, not the corpus.** It is not licence to add prose to `.lean` files —
the prose cap, the `Statement:`/`Reading:` labels and *"anything convertible to Lean MUST be
converted"* are untouched. If narration reveals that a claim is only expressible in prose, that is a
finding about the claim, not a reason to write an essay into the source.

## ⭐⭐ `batch.py precommit` BEFORE EVERY COMMIT. `/batch` for any multi-site work. Not optional.

**The orchestrator is the default entry point, not a special mode.** `tools/verify/batch.py` owns
sequencing and mechanical preconditions; an agent owns judgement. It decides nothing — it refuses to
let a commit or push happen while a decidable obligation is unmet.

```
python tools/verify/batch.py precommit    # BEFORE EVERY COMMIT. Works with or without a batch.
python tools/verify/batch.py prepush      # before any push: which reviews are required, and are
                                           # the signals FRESH (hash + coverage, not existence)
```

**`precommit` runs the UNIVERSAL obligations on every commit** — build green, a `#print axioms` entry
for every added declaration, an `ssot.json` row for every added declaration, all checkers at zero new.
Those are the four things this project forgets most; each was forgotten again on 2026-08-09 with all
four rules known and written down.

**⭐⭐ DO NOT LOOK UP WHAT BLOCKS WHERE — THE PIPELINE ANNOUNCES ITSELF AT EVERY ENTRY POINT.** Before
any check runs, all four entry points print a manifest: what is about to run, in what order, which
checks BLOCK and which only warn, what scope, what is exempt, and what is deliberately NOT run.
`prepush` additionally prints **the recorded verdict line from each review signal**, so *"cleared"*
is never read as *"clean"*. **Run it; never maintain a prose copy of its answer** — one formatter
(`report.py`), so the four cannot drift.

⚠ **The purity/SSOT check is driven by an ON-DISK BASELINE (`tools/verify/decl_baseline.txt`), never
by git.** Computed against `HEAD` it is meaningful only *before* the commit, and run afterwards both
checks passed **vacuously**. A **stale baseline is safe** — it can only make more declarations look
new, so the check gets stricter, never blind. Re-seed:
`python tools/verify/batch.py decls --baseline`. Vendored backports are exempt structurally.

**⚠ ALL pipeline logic is `tools/verify/hooks.py`; the hooks are three-line shims. Edit `hooks.py`,
and the shim must never grow.** Two partial implementations measurably disagreed three ways while
checking disjoint things — that is what this replaced.

**Use `/batch <bucket>` for anything MULTI-SITE** — a debaselining bucket, a defect-class sweep, a
file-sized burn-down. It adds stage ordering (`ledger` → `screen` → `probe` → `judge`), a frozen
filter snapshot, and a recorded note per stage. **A single targeted fix with a named defect id does
not need a batch**; `precommit` alone covers it.

⚠ **Filters are frozen at `batch start`.** Editing a checker mid-batch means the work was done
against a moving target; the batch is invalid and must restart. Route filter defects to `DEFECTS.md`
and fix them in their own batch. (Violated by the author of the rule on the day it was written —
`PRC-1`.)

⚠ **If a stage BLOCKS, fix the cause.** Do not delete `batch_state.json`, do not `--no-verify`, do
not push a subset to dodge a signal. **This project has two recorded bypass incidents and both began
by treating a block as an obstacle.**

📖 **WHY THE PIPELINE IS SHAPED THIS WAY — `tools/process/pipeline.md`.** Which obligation gates at
commit versus push and why `lake build` deliberately gates neither; the three defects that stayed
invisible for a month because a gate did not declare its own enforcement mode; and the `REL-1`
ordering lesson, where delegating before fixing would have replaced a correct computation with a
vacuous one. **Read it before changing `hooks.py`, `batch.py` or `report.py`, or before arguing a
gate is in the wrong place.**

## ⭐ The defect register — `.claude-local/DEFECT_CLASSES.md`. Consult it by DEFAULT.

**One row per defect CLASS, each with its DETECTOR.** `DEFECTS.md` is open instances; the register is
kinds, and the detector column is the part that transfers to a question nobody has asked yet.

**Three triggers, and they are obligations, not suggestions:**
1. **Writing a gate brief or spawning any reviewing agent** — name the **LAYER** attacked, the
   **STATE** tested, and the **DETECTOR by id**. *"Check the glosses"* is not a detector; *"DC-1: read
   the elaborated `#check`"* is. A gate that does not name its layer re-attacks the one the last gate
   already cleared.
2. **Something looks wrong and you are choosing how to check it** — find the class first. The register
   is indexed by what you have in hand (a suspicious sentence), not by what you are asking.
3. **A defect recurs** — add or amend a row, in the same change. A one-off is an instance and belongs
   in `DEFECTS.md`; the *second* occurrence is a class.

**The one-line summary of everything measured so far: PREFER A DETECTOR WHOSE VERB IS *RUN* OVER ONE
WHOSE VERB IS *READ*.** Across ~20 agent runs, every BEDROCK finding came from an agent **executing**
something and every ORDINARY finding from an agent **reading** something, with no exceptions.

⚠ **Six of seventeen rows have a mechanical checker; eleven do not.** Those eleven rely on someone
remembering, which this file elsewhere records as failing by construction. That is visible debt, not a
solved problem — and this register is the **seventh** convention of this shape, the previous six having
all leaked.
