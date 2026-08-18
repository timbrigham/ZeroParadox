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

## Formal Overview
Rice is **Mathlib's** (`ComputablePred.rice₂`) and is cited, not re-proved. The content here is the
pairing: one recursion-theorem fixed point gives the quine (ν-existence) and Rice undecidability at
once. Why that is the price of ν-existence: `ZeroParadox/Computability/Rice.md`.
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
    self-map on codes has a fixed point (`computability_face_fixedPoint` — Rogers' fixed-point theorem;
    while `rice_face`, via `ComputablePred.rice₂`, is the one that genuinely routes through
    Kleene's second recursion theorem, `fixed_point₂`),
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
