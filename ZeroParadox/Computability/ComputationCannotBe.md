# ComputationCannotBe — ride-along documentation

Moved from `ZeroParadox/Computability/ComputationCannotBe.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## Formal Overview (AI-assisted)

One of five `*CannotBe.lean` indexes, beside `ZeroParadox/BottomCannotBe.lean`,
`ZeroParadox/Order/SnapCannotBe.lean`, `ZeroParadox/Ordinal/Epsilon0CannotBe.lean` and
`ZeroParadox/Category/ChoiceCannotBe.lean`. Those pin the bottom, the snap, ε₀ and the framework's
relationship to `Classical.choice`; this one pins the **computational face** — and in particular the
proved-versus-committed line, which is where this face has historically drifted.

Its `#check` lines state no new results: each names an already-proven declaration in its home file,
so the `import`s recompile those files and the index cannot point at a dead or renamed result. Its
anonymous `example`s are CONTROLS, each the falsifier of one `Reading:`; they create no declarations.

## The honest status of a `#check`-only line

The `#check` **lines** cannot overclaim — they create no declarations. The `--` **glosses
beside them can.** So this file is built under the standing convention:

* **`Statement:`** — an accurate restatement of what the declaration proves.
* **`Reading:`** — the framework's interpretation, explicitly NOT a claim about the theorem.

No gloss is anything else, and each gloss sits ABOVE the `#check` it describes. Where a `Reading:` is
load-bearing, the commitment carrying it is named.

## The commitments the glosses name

* **`KleeneStructure`** — that the class's `botCode` is the computational face of `bot`. The field
  `botCode_is_quine` supplies only a periodicity condition, which constant codes meet.
* **The occurrence commitment** — that the snap occurs, which DA-1 consumes as its precondition.
  T-SNAP holds with nothing moving (`tsnap_holds_but_nothing_moves`), and in the computational face
  occurrence is the halting question (`occurs_iff_halts`).
* **AX-B1** — the binary split that removes an unstarted state (`forcing_needs_the_binary_split`).
