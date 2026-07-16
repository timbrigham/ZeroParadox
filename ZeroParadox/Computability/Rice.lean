import ZeroParadox.Category.Lawvere
import Mathlib.Computability.Halting
import Mathlib.Tactic

/-!
# Rice's theorem — the computability face's UNDECIDABILITY, from the recursion theorem (probe)

## Engineer's Take

Back to basics. We're filling in everything that's left where the relationship between one over
infinity and a bottom element still wasn't fully defined, using the same structure that we have for
everything else in the family.

---

## Overview (AI-assisted)

Rice (1953): every *non-trivial extensional* (semantic) property of partial computable functions is
undecidable. Rice's theorem is **already in Mathlib** (`ComputablePred.rice`, `ComputablePred.rice₂`,
`Mathlib/Computability/Halting.lean`), and its proof runs through `fixed_point₂` — Kleene's second
recursion theorem. This file does not re-prove it; it **cites** Mathlib and connects Rice to the
framework's computability face.

The connection (the genuine content): the framework's computability face is the one place the diagonal
fixed point is *genuinely produced*, not walled — `computability_face_fixedPoint` (`Category/Lawvere.lean`)
is Kleene's recursion theorem, giving the Kleene quine (ν-existence). Rice is the **same** recursion-theorem
fixed point read on the **decidability** axis: the quine *exists*, yet *which* programs have any non-trivial
semantic property is *undecidable*. That pairing — ∃ but ¬decidable — is exactly the "exists-but-undecidable"
signature that `Wall.lean`'s failure-mode taxonomy singles out as the computability row (the pivot face).

So on the wall map: the total faces (lattice, 2-adic) *posit* the fixed point and it is *refuted* as a
Lawvere instance in Set (Cantor); the computability face *has* the fixed point (recursion theorem) but pays
for it with undecidability (Rice). Rice is the price of the ν-existence.

Honest delta: Rice itself is Mathlib's (Rice 1953; the diagonal-family framing is Lawvere/Yanofsky, cited in
`Wall.lean`). New here: the framework restatement, a concrete face (the halting problem), and the
`quine_exists_yet_rice` pairing that states the ν-existence and the undecidability as two faces of one
recursion-theorem setting.

## Structure
- § I.   Rice, framework restatement (a non-trivial extensional property is undecidable) — via `rice₂`.
- § II.  The halting problem as a concrete Rice face — via Mathlib.
- § III. The pairing: the quine exists (ν) yet Rice undecidability holds — two faces, one fixed point.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-! ## § I. Rice, framework restatement -/

/-- **Rice (framework restatement).** A non-trivial extensional semantic property of programs is
    undecidable: if `C : Set Code` is extensional (`Hext`: depends only on `eval`) and non-trivial
    (`C ≠ ∅` and `C ≠ univ`), then membership in `C` is not a `ComputablePred`. Cites Mathlib's
    `ComputablePred.rice₂` (whose proof is Kleene's recursion theorem, `fixed_point₂`). -/
theorem rice_face (C : Set Code)
    (Hext : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C))
    (hne : C ≠ ∅) (huniv : C ≠ Set.univ) :
    ¬ ComputablePred (fun c => c ∈ C) := by
  intro h
  rcases (ComputablePred.rice₂ C Hext).mp h with h1 | h2
  · exact hne h1
  · exact huniv h2

/-! ## § II. The halting problem as a concrete Rice face -/

/-- **A concrete Rice face — the halting problem.** Whether a program halts on input `n` is a
    non-trivial extensional property, hence undecidable. Cites Mathlib's `ComputablePred.halting_problem`
    (itself a `rice` instance). This is the canonical member of the computability-face undecidability. -/
theorem halting_undecidable (n : ℕ) : ¬ ComputablePred (fun c => (eval c n).Dom) :=
  ComputablePred.halting_problem n

/-! ## § III. The pairing — ν-existence and Rice undecidability, one fixed point -/

/-- **The exists-but-undecidable signature.** In the computability setting the recursion theorem gives
    *both*: every computable self-map on codes has a fixed point (the Kleene quine exists — ν, via
    `computability_face_fixedPoint`), *and* every non-trivial extensional property is undecidable (Rice).
    The quine's existence and its undecidability are two faces of one recursion-theorem fixed point — the
    computability floor stated as a single conjunction. -/
theorem quine_exists_yet_rice (C : Set Code)
    (Hext : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C))
    (hne : C ≠ ∅) (huniv : C ≠ Set.univ)
    {f : Code → Code} (hf : Computable f) :
    (∃ c, eval (f c) = eval c) ∧ ¬ ComputablePred (fun c => c ∈ C) :=
  ⟨computability_face_fixedPoint hf, rice_face C Hext hne huniv⟩

/-! ## § IV. The bottom-element relationship — the floor (ν): the bottom exists -/

/-- **Rice on the family's μ/ν fork: the computability face HAS a bottom element.** Unlike the truth /
    comprehension walls (Tarski, Curry — μ, no floor), computation reaches a floor: every computable
    self-map on codes has a fixed point (`computability_face_fixedPoint` — Kleene's recursion theorem),
    the Kleene quine, a program computing its own code (verb = noun). So on the one-over-infinity-to-bottom
    map, the computability face is the ν side, where self-reference DOES close on a bottom — and Rice
    (above) is the price paid for it: the floor exists, but membership at it is undecidable. -/
theorem rice_face_has_bottom {f : Code → Code} (hf : Computable f) :
    ∃ c, eval (f c) = eval c :=
  computability_face_fixedPoint hf

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms rice_face
#print axioms halting_undecidable
#print axioms quine_exists_yet_rice
#print axioms rice_face_has_bottom
end PurityCheck
