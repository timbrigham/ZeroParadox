# ComputationCannotBe — ride-along documentation

Moved from `ZeroParadox/Computability/ComputationCannotBe.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## Formal Overview (AI-assisted)

The fourth `#check`-only index, beside `BottomCannotBe.lean`, `Order/SnapCannotBe.lean` and
`Ordinal/Epsilon0CannotBe.lean`. Those pin the three core *objects*; this one pins the
**computational face** — and in particular the proved-versus-committed line, which is where
this face has historically drifted.

Like the others it states no new results and reproduces no logic: every line `#check`s an
already-proven theorem in its home file, so the `import`s recompile those files and the index
cannot point at a dead or renamed result.

## The honest status of a `#check`-only index (corrected 2026-07-26)

The `#check` **lines** cannot overclaim — they create no declarations. The `--` **glosses
beside them absolutely can**, and in two sibling indexes they did, surviving four adversary
rounds. So this file is built under the standing convention from the outset:

* **`Statement:`** — an accurate restatement of what the declaration proves.
* **`Reading:`** — the framework's interpretation, explicitly NOT a claim about the theorem.

No gloss is anything else. Where a `Reading:` is load-bearing, the commitment carrying it is
named.
