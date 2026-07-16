-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the Lawvere bridge CROSSED in the computability face — the universal machine `eval` is the reflexive object Set refutes, and Roger/Kleene's recursion theorem is Lawvere firing there. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Settheory.LawvereBridge
import Mathlib.Computability.PartrecCode
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The Lawvere bridge, crossed in the computability face (probe)

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

`LawvereBridge.lean` § VI *located* the hard bridge: to source ⊥ as a genuine Lawvere fixed point you
need a reflexive object — a point-surjection onto a function space — and Set refutes it
(`reflexive_object_refuted`), because Set has fixed-point-free maps (negation). The escape is any regime
with *no* fixed-point-free endomap. The monotone/domain regime is one (Knaster-Tarski). This file records
the OTHER, which the framework already contains: the **computable** regime.

The universal machine `eval : Code → (ℕ →. ℕ)` is point-surjective onto the computable functions
(`Nat.Partrec.Code.exists_code`) — the reflexive object. And the computable world has **no
fixed-point-free total computable endomap**: Roger's fixed-point theorem
(`Nat.Partrec.Code.fixed_point`) gives every total computable `f : Code → Code` a fixed point up to
`eval`. That is exactly the obstruction, absent — the dual of `reflexive_object_refuted`. So Lawvere
fires in the computable category, and the self-referential fixed point *exists* there: Kleene's second
recursion theorem (`fixed_point₂`), which is the framework's own Kleene fixed point
(`kleene_fixed_point_exists`, ZP-K).

**The crossing, stated honestly.** The framework's Kleene fixed point IS the Lawvere fixed point in the
reflexive computable structure `eval` — the ν-side existence that Set (`reflexive_object_refuted`)
forbids, realized where the obstruction is absent. This does not claim ⊥-*at-bottom* or uniqueness (those
are the framework's separate identifications, T-EXEC and the fork collapse); it crosses the specific
inch I had wrongly called a `D∞`-only expedition. The framework expedites the crossing by already
carrying the computable reflexive object.

## Structure
- § I  The obstruction is absent in the computable world (Roger — the dual of the wall)
- § II The reflexive object exists: `eval` is point-surjective onto the computable functions
- § III The self-referential fixed point exists there (Kleene's recursion theorem)
-/

namespace ZeroParadox

open Nat.Partrec Nat.Partrec.Code

/-! ## § I. The obstruction is absent in the computable world -/

/-- **No fixed-point-free total computable endomap.** Roger's fixed-point theorem: every total computable
`f : Code → Code` has a fixed point up to `eval`. This is the exact dual of `reflexive_object_refuted` —
the fixed-point-free map that refutes the reflexive object in Set simply does not exist among the total
computable endomaps. So the computable reflexive object is *not* refuted. -/
theorem computable_no_fixedpointfree {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  Nat.Partrec.Code.fixed_point hf

/-! ## § II. The reflexive object exists — `eval` is point-surjective onto the computable functions -/

/-- **The universal machine is the reflexive object.** Every computable partial function is `eval c` for
some code `c` (`exists_code`): `eval` is point-surjective onto the computable functions. This is the
reflexive structure Set lacks (Cantor) but the computable category has — the point-surjection Lawvere
needs. -/
theorem eval_point_surjective {f : ℕ →. ℕ} (hf : Nat.Partrec f) : ∃ c : Code, eval c = f :=
  Nat.Partrec.Code.exists_code.mp hf

/-! ## § III. The self-referential fixed point exists there -/

/-- **The crossing.** Kleene's second recursion theorem: every partially computable `f : Code → (ℕ →. ℕ)`
has a code `c` with `eval c = f c` — a self-referential fixed point. This is the framework's Kleene fixed
point (`kleene_fixed_point_exists`, ZP-K), and here it is exhibited as Lawvere firing in the reflexive
computable structure: the ν-side existence that `reflexive_object_refuted` forbids in Set, realized where
the obstruction is absent. The hard bridge is crossed in the computability face. -/
theorem selfref_fixedpoint_exists_computable {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c :=
  Nat.Partrec.Code.fixed_point₂ hf

end ZeroParadox

/-! ## Axiom Purity Check

These inherit the classical footprint of Mathlib's computability infrastructure ([propext,
Classical.choice, Quot.sound]) — Kleene's/Roger's theorems themselves use choice. This is the same
footprint ZP-K already carries; the crossing is not choice-free, and that is honest for the
computability face. -/
section PurityCheck
open ZeroParadox

#print axioms computable_no_fixedpointfree
#print axioms eval_point_surjective
#print axioms selfref_fixedpoint_exists_computable

end PurityCheck
