import ZeroParadox.Settheory.Wall
import ZeroParadox.Settheory.Tarski
import ZeroParadox.Settheory.Curry
import ZeroParadox.Settheory.Loeb
import ZeroParadox.Settheory.SetTheoryAFA
import ZeroParadox.Computability.Rice
import ZeroParadox.Computability.Kleene
import ZeroParadox.Order.LeastFixedPoint
import ZeroParadox.Category.DiagonalWitness

/-!
# Machine-checked characterization index of self-reference — the diagonal fixed point

The keystone index. ⊥ (the bottom), the snap, and ε₀ each have a `#check`-only object
(`BottomCannotBe.lean`, `Order/SnapCannotBe.lean`, `Ordinal/Epsilon0CannotBe.lean`). Those are the three
core *objects*; this file is the front door to the *phenomenon* they share a shape with — **self-reference**,
the diagonal fixed point on which the whole framework rests. Until now self-reference had no single
canonical reference: it lived one-face-per-domain with no direct route in. This is that route.

Like the three object indexes, this file states no new results and reproduces no logic: every line
`#check`s an already-proven theorem in its home file, so the `import`s recompile those files and the
index cannot point at a dead or renamed result. A `#check`-only index creates no declarations and so
*structurally cannot overclaim*.

## The split (the μ/ν fork — the same structure the framework uses throughout)

Self-reference runs off one **engine** — Lawvere's fixed-point construction — and forks in two:
- **§ II. Wall faces (μ) — self-reference CANNOT close.** No fixed point exists; the reflexive object is
  impossible. The classical negative diagonal arguments: Cantor, Russell, Turing, Tarski, Curry.
- **§ III. Floor faces (ν) — self-reference CLOSES, and the fixed point lands at ⊥.** The fixed point is
  genuinely produced and it is the bottom: the Quine atom, the Kleene quine, Löb / Gödel's second, Rice.

This mirrors the ZP-R Diagonal Family Addendum exactly. As with the bottom family (MC-1), the roster is a
matrix of domain cells; the cells below are the ones currently formalized, and other domains' cells remain
to be filled in over time — the same open-cell structure the framework carries elsewhere.

## The fence (built in, load-bearing)

Each face is a proven theorem; this index only *routes* them. That the faces are **one** self-reference
is **Lawvere (1969) / Yanofsky (2003)** — cited prior art, a recognized connection, NOT a Zero Paradox
theorem. The cross-face identity across domains stays a **type boundary**, never a Lean `=`. So this is a
machine-checked *view* over the existing diagonal family, not a new synthesis claim.

## Engineer's Take

We see diagonal fixed points come up time and time again. Collect here to formalize the set, and define
exactly what minimum set of requirements they take.
-/

section DiagonalFixedPointIndex

/-! ### § I. The engine — Lawvere's fixed-point construction and its no-fixed-point dual -/
#check @ZeroParadox.lawvere_fixedpoint       -- a point-surjection forces a fixed point of every endomap (the diagonal engine)
#check @ZeroParadox.negation_no_fixedpoint   -- the dual: negation has no fixed point (¬(p ↔ ¬p)) — the wall's seed

/-! ### § II. Wall faces (μ) — self-reference CANNOT close (no fixed point / no reflexive object)

**Scope note (2026-07-29) — `wf_no_selfloop` sits here but is NOT a μ engine face, and conflating the two
was a live contradiction in this corpus.** The faces below it are engine faces: the map is fixed-point-free
(negation), so *no object forms anywhere*. `wf_no_selfloop` says something different — it is a **verdict a
HOST renders on the engine's ν output**: a well-founded host refuses the self-loop (`no_quine_atom`), while a
host that carries it is thereby not well-founded (`quineHost_not_wellFounded`, `floor_not_wellFounded`, both
in § III's family). Same theorem, two hosts. It is kept in this section because the *signature* is a refusal,
but do not read it as "no fixed point exists" — the object exists and is refused, which is § III's object
seen from a well-founded host. Standard framing: Aczel 1988 p. 6 (Foundation vs Anti-Foundation);
Adámek-Milius-Moss 2020 Thm 7.6 ("the only well-founded fixed point is the initial algebra"). See
`Settheory/Wall.lean`'s one-root-or-two reframe. -/
#check @ZeroParadox.wf_no_selfloop           -- the host verdict, NOT an engine face: a well-founded relation has no self-loop (no x with r x x). Weakest rung — Mathlib's `WellFounded.asymmetric` is stronger
#check @ZeroParadox.cantor_via_engine        -- Cantor: no surjection A → (A → Prop)
#check @ZeroParadox.russell_via_engine       -- Russell: no surjection A → (A → Prop) via membership `mem : A → A → Prop`
#check @ZeroParadox.no_self_decider          -- Turing: no surjection A → (A → Bool) (the halting diagonal)
#check @ZeroParadox.tarski_no_internal_truth -- Tarski: no internal truth predicate (undefinability)
#check @ZeroParadox.tarski_no_truth_bottom   -- Tarski's bottom: truth is the wall dual — no floor
#check @ZeroParadox.curry_no_bottom          -- Curry: no naming surjection; pretending otherwise explodes

/-! ### § III. Floor faces (ν) — self-reference CLOSES, and the fixed point lands at ⊥ -/
#check @ZeroParadox.t_exec                   -- the Quine atom: any self-containing element = ⊥ (self-reference closes at the bottom). "⊥ self-executes" is the framework's reading, not this statement
#check @ZeroParadox.da1_closed_concrete      -- concrete Quine atom: `IsQuineAtom (bot : MachinePhase)`
#check @ZeroParadox.kleene_quine_is_bot      -- any Quine atom = ⊥, under `[KleeneStructure]`. NB the statement has no Kleene clause; "the Kleene quine IS ⊥" is ZP-K's commitment, and is not a Lean `=` (Code vs L)
#check @ZeroParadox.t_comp                   -- T-COMP: proves the Quine-atom / order-bottom / join-identity faces equivalent (three). The Kleene face is a `KleeneStructure` class field, not a clause
#check @ZeroParadox.selfApp_isLeastFixedPointFrom  -- ⊥ is the least fixed point of self-application (the order floor)
#check @ZeroParadox.ProvabilityLogic.loeb_sentence_is_fixedpoint  -- Löb: the provability diagonal closes (the Löb sentence is a fixed point)
#check @ZeroParadox.ProvabilityLogic.godel_two     -- Gödel's second: consistency unprovable — the provability floor
#check @ZeroParadox.rice_face_has_bottom     -- Rice: the floor exists (the pivot face)
#check @ZeroParadox.quine_exists_yet_rice    -- Rice pivot: the fixed point is present yet membership at it is undecidable

/-! ### § IV. The minimum-requirements level (`Category/DiagonalWitness.lean`) — the underlying level beneath the fork

The faces above are collected; this is what they minimally have in common, one level down: a **diagonal
witness relative to an admissible endomap class M** (`HasWitnessRel`). The wall/floor fork is one monotone
predicate over the lattice of map-classes, and the witness-carrying classes form an Alexandrov-closed set —
the topology the collection sits on. The genuine *nontrivial* floor (the Kleene quine) lives one axis
further out, in the effective category (eval-equality); located here, fenced there. -/
#check @ZeroParadox.HasWitnessRel                  -- the minimum requirement: a witness relative to admissible maps M
#check @ZeroParadox.fixedPoint_of_witnessRel       -- the engine: a relative witness forces a fixed point for admissible g
#check @ZeroParadox.no_witnessRel_of_admissible_fpf -- the wall: an admissible fixed-point-free map kills the witness
#check @ZeroParadox.witnessRel_antitone            -- antitone in M — the spine of the topology
#check @ZeroParadox.witnessSet_isLowerSet          -- THE TOPOLOGY: the witness set is Alexandrov-closed (a lower set)
#check @ZeroParadox.hasWitnessRel_of_subsingleton  -- the fine end is inhabited (non-degeneracy)
#check @ZeroParadox.no_witnessRel_top_of_nontrivial -- the coarse end: nontrivial ⇒ no witness (Cantor; posited faces)
#check @ZeroParadox.effective_floor_fixedPoint       -- axis 2: the genuine nontrivial floor (Kleene recursion, effective category)
#check @ZeroParadox.no_computable_evalFixedPointFree -- axis 2 mechanism: no computable fixed-point-free map, so the wall lifts

end DiagonalFixedPointIndex
