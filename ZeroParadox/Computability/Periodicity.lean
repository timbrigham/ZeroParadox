import ZeroParadox.Computability.Kleene

/-!
# ZP-K metric: the selfApply periodicity invariant (P5)

The computational quines of ZP-K (`IsComputationalQuine`, the Kleene fixed points of `selfApply`)
already satisfy a raw periodicity equation (`quine_period_is_goedel`) and form an unbounded
family (`infinite_quine_family`). This file packages those parked facts as the two named
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

namespace ZeroParadox

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

/-- **A quine of least period its own index.** Statement: for every `N` there is a computational
    quine `c` with `N < encode c`, `eval c n = n % encode c` for all `n`, and no positive period
    smaller than `encode c`. Kleene's second recursion theorem applied to `F c n := n % encode c`
    (`fixed_point₂_unbounded`). -/
theorem quine_mod_exists (N : ℕ) :
    ∃ c : Code, IsComputationalQuine c ∧ N < Encodable.encode c ∧
      (∀ n, eval c n = Part.some (n % Encodable.encode c)) ∧
      ∀ q, 0 < q → q < Encodable.encode c → ¬ Function.Periodic (eval c) q := by
  have hF : Partrec₂ (fun (c : Code) (n : ℕ) => (Part.some (n % Encodable.encode c) : Part ℕ)) :=
    (Primrec.nat_mod.comp Primrec.snd (Primrec.encode.comp Primrec.fst)).to_comp.partrec
  obtain ⟨c, hc, hN⟩ := fixed_point₂_unbounded hF N
  have hev : ∀ n, eval c n = Part.some (n % Encodable.encode c) := fun n => congrFun hc n
  refine ⟨c, ?_, hN, hev, fun q hq hqk hper => ?_⟩
  · show eval c = selfApply c
    funext n
    show eval c n = eval c (Encodable.encode c + n)
    rw [hev, hev, Nat.add_mod_left]
  · have h := hper 0
    rw [hev, hev, Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 0 + q < Encodable.encode c)] at h
    simp at h
    omega

-- Statement: CONTROL. A constant code is a computational quine (`quine_set_infinite`) and has
-- period 1, so the periodicity predicate alone does not force the least period to be the index.
example (k : ℕ) : Function.Periodic (eval (Code.const k)) 1 := by
  intro x; simp [eval_const]

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox Nat.Partrec Nat.Partrec.Code
#print axioms quine_isPeriodic
#print axioms quine_set_infinite
#print axioms quine_mod_exists
end PurityCheck
