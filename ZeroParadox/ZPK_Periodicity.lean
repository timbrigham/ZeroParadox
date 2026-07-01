import ZeroParadox.ZPK

/-!
# ZP-K metric: the selfApply periodicity invariant (P5)

The computational quines of ZP-K (`IsComputationalQuine`, the Kleene fixed points of `selfApply`)
already satisfy a raw periodicity equation (`ZPK.quine_period_is_goedel`) and form an unbounded
family (`ZPK.infinite_quine_family`). This file packages those parked facts as the two named
invariants the metric calls for, in standard Mathlib vocabulary:

* `quine_isPeriodic` — `eval c` is `Function.Periodic` with period the code's own Gödel number
  `Encodable.encode c`: the index IS the period.
* `quine_set_infinite` — the set of computational quines is `Set.Infinite` (the DA-2 non-uniqueness
  stated as an explicit infinitude of the fixed-point family).

No new mathematics: these restate existing ZP-K content (`quine_period_is_goedel`, the const-quine
injection used in `infinite_quine_family`) so the periodicity/infinitude can be cited directly.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPK

open Nat.Partrec Nat.Partrec.Code

/-- **The selfApply periodicity invariant (P5).** For a computational quine `c`, the partial
    function `eval c` is periodic with period `Encodable.encode c` — the code's own Gödel number IS
    the period. The named (`Function.Periodic`) form of `quine_period_is_goedel`. -/
theorem quine_isPeriodic (c : Code) (hc : IsComputationalQuine c) :
    Function.Periodic (eval c) (Encodable.encode c) := by
  intro x
  rw [Nat.add_comm x (Encodable.encode c)]
  exact (quine_period_is_goedel c hc x).symm

/-- **The computational-quine family is infinite (P5).** The set of computational quines is
    `Set.Infinite`: every `Code.const k` is a quine and `Code.const` is injective. The explicit
    `Set.Infinite` form behind `infinite_quine_family` — DA-2 instantiation succession is unbounded. -/
theorem quine_set_infinite : {c : Code | IsComputationalQuine c}.Infinite := by
  have hconst_quine : ∀ k : ℕ, IsComputationalQuine (Code.const k) := fun k => by
    show eval (Code.const k) = selfApply (Code.const k)
    funext m
    simp [selfApply, eval_const]
  have hinj : Function.Injective (fun k : ℕ => Code.const k) := fun a b h => const_inj h
  exact Set.infinite_of_injective_forall_mem hinj hconst_quine

end ZeroParadox.ZPK

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPK Nat.Partrec Nat.Partrec.Code
#print axioms quine_isPeriodic
#print axioms quine_set_infinite
end PurityCheck
