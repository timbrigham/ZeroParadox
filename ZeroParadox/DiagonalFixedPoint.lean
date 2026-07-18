import ZeroParadox.Settheory.Wall
import ZeroParadox.Settheory.Tarski
import ZeroParadox.Settheory.Curry
import ZeroParadox.Settheory.Loeb
import ZeroParadox.Settheory.SetTheoryAFA
import ZeroParadox.Computability.Rice
import ZeroParadox.Computability.Kleene
import ZeroParadox.Order.LeastFixedPoint

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

/-! ### § II. Wall faces (μ) — self-reference CANNOT close (no fixed point / no reflexive object) -/
#check @ZeroParadox.wf_no_selfloop           -- the general wall: a well-founded relation has no self-loop (no x with r x x)
#check @ZeroParadox.cantor_via_engine        -- Cantor: no surjection A → (A → Prop)
#check @ZeroParadox.russell_via_engine       -- Russell: no surjection A → (A → A → Prop) (self-membership)
#check @ZeroParadox.no_self_decider          -- Turing: no surjection A → (A → Bool) (the halting diagonal)
#check @ZeroParadox.tarski_no_internal_truth -- Tarski: no internal truth predicate (undefinability)
#check @ZeroParadox.tarski_no_truth_bottom   -- Tarski's bottom: truth is the wall dual — no floor
#check @ZeroParadox.curry_no_bottom          -- Curry: no naming surjection; pretending otherwise explodes

/-! ### § III. Floor faces (ν) — self-reference CLOSES, and the fixed point lands at ⊥ -/
#check @ZeroParadox.t_exec                   -- the Quine atom: ⊥ self-executes (self-reference closes at the bottom)
#check @ZeroParadox.da1_closed_concrete      -- concrete Quine atom: `IsQuineAtom (bot : MachinePhase)`
#check @ZeroParadox.kleene_quine_is_bot      -- the Kleene quine IS ⊥ (the computability floor)
#check @ZeroParadox.t_comp                   -- T-COMP: the Quine-atom / Kleene-quine / selfApp floor faces are one
#check @ZeroParadox.selfApp_isLeastFixedPointFrom  -- ⊥ is the least fixed point of self-application (the order floor)
#check @ZeroParadox.ProvabilityLogic.loeb_sentence_is_fixedpoint  -- Löb: the provability diagonal closes (the Löb sentence is a fixed point)
#check @ZeroParadox.ProvabilityLogic.godel_two     -- Gödel's second: consistency unprovable — the provability floor
#check @ZeroParadox.rice_face_has_bottom     -- Rice: the floor exists (the pivot face)
#check @ZeroParadox.quine_exists_yet_rice    -- Rice pivot: the fixed point is present yet membership at it is undecidable

end DiagonalFixedPointIndex
