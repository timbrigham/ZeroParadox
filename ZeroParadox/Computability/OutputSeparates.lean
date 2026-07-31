-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): what a functor must carry before its
-- non-terminating behaviours are distinguishable at all — the computational-face counterpart of the
-- branching requirement already proved on the valuation face. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Computability.GroundZero
import ZeroParadox.Category.RootCutBinary
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The infinite pole is a POINT unless the functor emits: output separates, arity does not

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer.

## Engineer's Take

TODO (Tim): <your take, in your own voice.>

---

## Formal Overview (AI-assisted)

`GroundZero.notEL_unique` proves that in the `1 + X` regime **every** non-terminating behaviour is the
*same* point, `natInfinity`. That is a single chain's single end, and it is why the computational
face's INFINITE pole reads as degenerate: the functor cannot hold more than one divergent behaviour.

This file asks what has to change, and answers it with a **negative** and a **positive** result:

* **Arity does not separate.** `binPF = ⟨Unit, fun _ => Bool⟩` has **two** recursive positions, yet
  `Cofix binPF.Obj` is a **subsingleton** (`binCofix_subsingleton`). Two children per node buy nothing,
  because the head type is `Unit`: every node looks alike, so there is exactly one infinite tree.
  `RootCutBinary`'s `arity_collapse` already showed arity does not change the *seam* question; this
  shows it does not change the *separation* question either.
* **Output separates.** `streamPF = ⟨Bool, fun _ => PUnit⟩` has **one** recursive position — a chain,
  the same arity as `idPF` — but its head carries a `Bool`. Two of its behaviours are then provably
  distinct (`output_separates`), distinguished by one observation of the head.

So the discriminator is **what a step emits**, not how many successors it has. `Reading:` this is the
computational-face reading of `Valuation/BranchingRequirement.lean`, where branching supplies "the
*infinity* in one instance out of infinity" — on the 2-adic tree a branch choice **is** a digit, so
branching and emission coincide there and come apart here. Conjectural as an identification: the two
live in different carriers and no map between them is claimed.

**Prior art, cited not reproved.** The ladder is Adámek–Milius–Moss 2020 (arXiv:1910.09401v2)
Example 7.7 p. 31: for `F X = A × X + 1` the terminal coalgebra is `A^∞ ∪ A*` and the initial algebra
is `A*` — the `A ×` is exactly the emission that makes `A^∞` large. Rutten, *Universal coalgebra*, TCS
249 (2000) p. 16 is the `A = 1` degenerate case: in `N̄` the point `∞` "only takes a step to itself and
hence never terminates", and it is the *only* such point. Nothing here is new mathematics; what is new
is stating it about this framework's own functors.

**Fences.** This proves *at least two* distinct behaviours, not the continuum — `A^∞` uncountable is
AMM's, not proved here. Nothing about whether any framework bottom *is* a `streamPF` behaviour: no
carrier is identified, and `binCofix_subsingleton` is about `binPF`, not about ⊥.

## Structure
- § I   Arity does not separate: `Cofix binPF.Obj` is a subsingleton
- § II  Output does: `streamPF`, its constant behaviours, and their distinctness
- § III The contrast, bundled
-/

namespace ZeroParadox

open QPF

/-! ## § I — Arity does not separate -/

/-- **Two recursive positions, one behaviour.** `binPF`'s head type is `Unit`, so every node of the
    tree looks alike and there is nothing to tell two infinite trees apart. Proved by bisimulation on
    the total relation: the heads agree because `Unit` is a subsingleton, and the children are related
    for free. This is the NEGATIVE half — doubling the arity leaves the infinite pole a point. -/
theorem binCofix_subsingleton (x y : Cofix binPF.Obj) : x = y := by
  refine Cofix.bisim (fun _ _ => True) ?_ x y trivial
  intro a b _
  rw [liftr_iff]
  exact ⟨(), (Cofix.dest a).2, (Cofix.dest b).2, rfl, rfl, fun _ => trivial⟩

/-! ## § II — Output separates -/

/-- The **labelled chain** functor: one recursive position, like `idPF`, but each node emits a `Bool`.
    `Cofix streamPF.Obj` is the type of `Bool`-streams. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: the minimal polynomial functor that separates divergent behaviours - one recursive position (so arity is held fixed against binPF) with a Bool-labelled head, isolating emission as the discriminating ingredient.
def streamPF : PFunctor.{0, 0} := ⟨Bool, fun _ => PUnit⟩

/-- The constant behaviour emitting `b` forever. -/
def constStream (b : Bool) : Cofix streamPF.Obj :=
  Cofix.corec (fun _ : PUnit => (⟨b, fun _ => PUnit.unit⟩ : streamPF.Obj PUnit)) PUnit.unit

/-- One step of the constant behaviour: it emits `b` and continues as itself. -/
theorem constStream_dest (b : Bool) :
    Cofix.dest (constStream b) = ⟨b, fun _ => constStream b⟩ := by
  unfold constStream
  rw [Cofix.dest_corec]
  rfl

/-- **OUTPUT SEPARATES.** Two behaviours of the same arity as `idPF` — one recursive position each,
    both non-terminating — are nevertheless **distinct**, told apart by a single observation of the
    head. Contrast `notEL_unique`, where all non-terminating behaviours collapse to one point. -/
theorem output_separates : constStream false ≠ constStream true := by
  intro h
  have hd : Cofix.dest (constStream false) = Cofix.dest (constStream true) := congrArg _ h
  rw [constStream_dest, constStream_dest] at hd
  exact Bool.false_ne_true (congrArg Sigma.fst hd)

/-! ## § III — The contrast -/

/-- **The discriminator is emission, not arity.** Bundling the two halves: doubling the recursive
    positions (`binPF`, two children, no label) leaves the final coalgebra a subsingleton, while
    labelling a single-successor node (`streamPF`, one child, a `Bool` head) already yields two
    distinct behaviours. -/
theorem emission_not_arity_separates :
    (∀ x y : Cofix binPF.Obj, x = y) ∧ constStream false ≠ constStream true :=
  ⟨binCofix_subsingleton, output_separates⟩

end ZeroParadox

/-! ## Axiom Purity Check

**Measured 2026-07-30, all four: `[propext, Classical.choice, Quot.sound]`.** The choice is inherited
from Mathlib's `QPF.Cofix`, which is `Quot (@Mcongr F q)` over the M-type construction — every
statement here mentions `Cofix`, and `#print axioms` follows the STATEMENT, not the proof. This
matches the ν-side footprint `Category/CoalgebraForkPlace.lean` already records (μ side choice-free,
ν side not). None of it is a new commitment: the proofs themselves are one `Cofix.bisim`, one
`Cofix.dest_corec`, and one `congrArg` on a `Sigma.fst`.
-/
section PurityCheck
open ZeroParadox

#print axioms binCofix_subsingleton
#print axioms constStream_dest
#print axioms output_separates
#print axioms emission_not_arity_separates

end PurityCheck
