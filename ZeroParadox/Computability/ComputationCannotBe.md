# ComputationCannotBe — ride-along documentation

Ride-along for `ZeroParadox/Computability/ComputationCannotBe.lean`.

## Formal Overview (AI-assisted)

One of five `*CannotBe.lean` indexes, beside `ZeroParadox/BottomCannotBe.lean`,
`ZeroParadox/Order/SnapCannotBe.lean`, `ZeroParadox/Ordinal/Epsilon0CannotBe.lean` and
`ZeroParadox/Category/ChoiceCannotBe.lean`. Those pin the bottom, the snap, ε₀ and the framework's
relationship to `Classical.choice`; this one pins the **computational face**, and in particular the
line between what is proved and what is committed.

Its `#check` lines state no new results: each names an already-proven declaration in its home file,
so the `import`s recompile those files and the index cannot point at a dead or renamed result. Its
three anonymous `example`s are controls and create no declarations. The first two each falsify one
reading: that meeting `IsComputationalQuine` pins self-reference (every constant code meets it), and
that being a Quine atom makes something move (c₀ is one while a state sequence at c₀ never steps).
The third supports a CARRIER scope: `MachinePhase`, a finite carrier, admits no `SelfCopyRef` map.

## The honest status of a `#check`-only line

The `#check` **lines** cannot overclaim — they create no declarations. The `--` **glosses
beside them can.** So this file is built under the standing convention:

* **`Statement:`** — an accurate restatement of what the declaration proves.
* **`Reading:`** — the framework's interpretation, explicitly NOT a claim about the theorem.

No gloss is anything else, and each gloss sits ABOVE the `#check` it describes. Where a `Reading:` is
load-bearing, the commitment carrying it is named.

## The commitments the glosses name

* **`KleeneStructure`** — that the class's `botCode` is the computational face of `bot`, the bottom of
  the `ZPSemilattice L`. The field `botCode_is_quine` supplies only a periodicity condition, which
  constant codes meet.
* **The occurrence commitment** (instantiation occurs) — as stated in `ZeroParadox/Order/Snap.lean`'s Formal Overview, from
  which, together with DA-1, the snap occurs. T-SNAP holds with nothing moving
  (`tsnap_holds_but_nothing_moves`). In the computational face the framework reads occurrence as
  halting (`occurs_iff_halts`); that identification is a modelling choice, not a theorem.
* **AX-B1** — the framework takes the binary split that removes an unstarted state
  (`forcing_needs_the_binary_split`) to be a third encoding of AX-B1, beside `ax_b1_distinct` and
  `HasFirstStep`. Per-encoding membership is checkable; identity across the encodings is neither
  claimed nor well-formed.
