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

## Engineer's Take

We see diagonal fixed points come up time and time again. Collect here to formalize the set, and define
exactly what minimum set of requirements they take.

---

## Formal Overview
One engine (Lawvere) forking into wall faces (μ, no fixed point) and floor faces (ν, landing at ⊥).
`#check`-only, so it states no new result — that the faces are ONE self-reference is Lawvere/Yanofsky,
cited prior art and **not** a ZP theorem. Split and fences: `ZeroParadox/DiagonalFixedPoint.md`.
-/

section DiagonalFixedPointIndex

/-! ### § I. The engine — Lawvere's fixed-point construction and its no-fixed-point dual -/
#check @ZeroParadox.lawvere_fixedpoint       -- a point-surjection forces a fixed point of every endomap (the diagonal engine)
#check @ZeroParadox.negation_no_fixedpoint   -- the dual: negation has no fixed point (¬(p ↔ ¬p)) — the wall's seed

/-! ### § II. Wall faces (μ) — self-reference CANNOT close (no fixed point / no reflexive object)

⚠ **`wf_no_selfloop` sits here but is NOT an engine face.** The engine faces have a fixed-point-free
map, so no object forms; `wf_no_selfloop` is a **verdict a HOST renders on the engine's ν output** — the
object exists and is refused. Standard framing and the full scope note: `ZeroParadox/DiagonalFixedPoint.md`. -/
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
