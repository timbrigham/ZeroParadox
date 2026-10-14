# The relativized Lawvere witness: level sets, topology and prior art

Argument and attribution for `ZeroParadox/Category/DiagonalWitness.lean`, moved from its module
docstring. The Lean file holds the declarations, the Engineer's Take and the per-declaration glosses.

`ZeroParadox/DiagonalFixedPoint.lean` *collects* the faces of self-reference; the Lean file asks what they **minimally
have in common**, one level beneath the μ/ν fork. The engine is the diagonal argument of **Lawvere
(1969)**, restated by **Yanofsky (2003)**; that whether the witness exists is *category-relative* is the
recognized effective-topos / Turing-category observation (**Hyland 1982; Cockett–Hofstra 2008; van
Oosten**). The Lean file only *packages* those — `HasWitnessRel` is a formalization lever, not a new
theorem, and its level sets are the per-face verdicts already proven in `ZeroParadox/Category/Lawvere.lean` §V–VI.
There the bare `HasLawvereWitness β` (a point-surjection `α → (α → β)`) is FALSE for every nontrivial
type in **Set** (Cantor), so the lattice and 2-adic faces are *posited* fixed points, while the
computability (Kleene) face is *genuine* — in the **effective** category.

## The underlying level: the witness relative to an admissible endomap class

`HasWitnessRel β M` relativizes the diagonal hypothesis to a class `M` of admissible endomaps: a
self-application `e : α → (α → β)` whose range contains the diagonal `fun x => g (e x x)` for every
`g ∈ M`. This is the minimal requirement — the witness only has to dodge the diagonals of the maps `M`
that "count" in the ambient category. The face table becomes level sets of ONE predicate:
- **M coarse (all endomaps), β nontrivial** — a fixed-point-free swap is admissible ⇒ no witness. Set
  floor faces are *posited*, wall faces *refuted*.
- **M fine (computable endomaps)** — with `HasWitnessRel`'s literal equality the obstruction stays:
  `fun c => Code.pair c c` is computable and fixes no code (the `example` after
  `no_witnessRel_of_admissible_fpf` in the Lean file). It is removed only up to `eval` (the Lean
  file's § Axis 2, `no_computable_evalFixedPointFree`), and even there its absence does not by itself
  supply the witness: `fixedPoint_of_witnessRel` runs from a witness to fixed points, one way, and **the Lean file constructs no witness for the computable
  class, up to `eval` or otherwise.** The genuine diagonal fixed point on this side is **Rogers' fixed-point theorem**, cited
  rather than derived there (`Nat.Partrec.Code.fixed_point`, aliased as `computability_face_fixedPoint`
  in `ZeroParadox/Category/Lawvere.lean`; Mathlib reserves *Kleene's second recursion theorem* for
  `fixed_point₂`).

## The topology (why "underlying level" makes it obvious)

`HasWitnessRel β ·` is **antitone** in `M`: shrinking the admissible class can only help the witness. So
`{M | HasWitnessRel β M}` is downward-closed in `⊆` — a lower set on the lattice of admissible-map-classes,
i.e. a **closed set in the Alexandrov topology** on that lattice. The wall/floor/posited trichotomy is the
level structure of one monotone predicate over that space; the floor can "switch on" only once `M` drops
below every admissible fixed-point-free map (`no_witnessRel_of_admissible_fpf`). That lattice-of-map-classes, with the witness as an Alexandrov-closed
set, is the topology the collection carries.
