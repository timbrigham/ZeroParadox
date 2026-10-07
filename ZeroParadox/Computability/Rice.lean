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
Rice (1953) states his theorem for classes of r.e. sets; cited, not re-proved, is Mathlib's program-code
form `ComputablePred.rice₂` (sets of codes closed under equal `eval`). The content here is the pairing:
the quine (ν-existence) and Rice undecidability as two conjuncts, each from its own use of the recursion theorem. Placement: `ZeroParadox/Computability/Rice.md`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-! ## § I. Rice, framework restatement -/

/-- **Rice (framework restatement).** A non-trivial extensional semantic property of programs is
    undecidable: if `C : Set Code` is extensional (`Hext`: depends only on `eval`) and non-trivial
    (`C ≠ ∅` and `C ≠ univ`), then membership in `C` is not a `ComputablePred`. Cites Mathlib's
    `ComputablePred.rice₂` (proved from `ComputablePred.rice`, which uses `fixed_point₂`). -/
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

/-! ## § III. The pairing — ν-existence and Rice undecidability, two conjuncts -/

/-- **The exists-but-undecidable signature.** In the computability setting the recursion theorem, used
    twice, gives *both*: every computable self-map on codes has a fixed point **up to `eval`** (the Kleene quine
    exists — ν, via `computability_face_fixedPoint`; NOT a literal fixed point — `fun c => Code.pair c c`
    has none), *and* every non-trivial extensional property is undecidable (Rice).
    The second conjunct does not mention `f`: the undecidability is of `C` over all codes, and nothing
    is stated about membership at `f`'s fixed point (gloss: `ZeroParadox/Computability/ComputationCannotBe.lean` § V). -/
theorem quine_exists_yet_rice (C : Set Code)
    (Hext : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C))
    (hne : C ≠ ∅) (huniv : C ≠ Set.univ)
    {f : Code → Code} (hf : Computable f) :
    (∃ c, eval (f c) = eval c) ∧ ¬ ComputablePred (fun c => c ∈ C) :=
  ⟨computability_face_fixedPoint hf, rice_face C Hext hne huniv⟩

/-! ## § IV. The bottom-element relationship — the floor (ν): a fixed point up to `eval` exists -/

/-- **Rice on the family's μ/ν fork: the computability face has a fixed point (Rogers); reading it as the face's bottom is the family's criterion, not this theorem.** Despite the
    declaration's name, the statement is a fixed point up to `eval` and names no bottom.
    Unlike the truth / comprehension walls (Tarski, Curry — μ, no floor), computation reaches a floor in
    the family's sense: every computable
    self-map on codes has a fixed point **up to `eval`** (`computability_face_fixedPoint` — Rogers',
    Mathlib's `fixed_point`; `rice_face` also rests on it, through `ComputablePred.rice₂`,
    `ComputablePred.rice` and Kleene's second recursion theorem `fixed_point₂`, which Mathlib derives
    from `fixed_point`),
    read as the Kleene quine (a program printing its own code needs one further s-m-n step). So on the
    one-over-infinity-to-bottom map, the computability face is the ν side, where self-reference
    closes on a Kleene code filling the self-application fixed-point role — and Rice (above) sits beside it: a non-trivial extensional `C` is undecidable
    over all codes, a conjunct that does not mention `f` (`quine_exists_yet_rice`). -/
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
