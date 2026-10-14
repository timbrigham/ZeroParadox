-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the "1-or-∞, no finite middle" dichotomy as an orbit argument — a sufficient condition for that shape; the shape itself is not universal (§ fpp below). The framework's scale map runs the same argument (`valBridge_forces_infinite`). Curated results indexed in ZeroParadox/MANIFEST.md.

import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The orbit dichotomy — "one or infinitely many", no finite middle (probe)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

An orbit argument (`orbit_dichotomy`): elementary, no new mathematics, and a sufficient condition for
the "one or infinitely many" shape only; for the λ-calculus see § fpp.
-/

/-! ## § fpp — the λ-calculus name for the shape, where it holds and where it fails
Reading: there the shape is the **fixed point property (fpp)**: Manzonetto, Polonsky, Saurin & Simonsen,
*The fixed point property and a technique to harness double fixed point combinators*, J. Logic and
Computation (2019), doi:10.1093/logcom/exz013, Def. 2.15 (numbering as in the preprint; the journal
version was not checked). Their Problem 2 restates TLCA #25: "Does λβ satisfy the fixed point property?".
Holds: λβ satisfies the open fpp (their Thm 3.6); the closed question remains open (their abstract).
Fails: no sensible λ-theory satisfies the fpp (their Thm 5.4), and in each one, for every k > 0, some
closed term has exactly k fixed points modulo that theory (their Prop. 5.6). -/

namespace ZeroParadox

/-- **The orbit dichotomy.** Let `s` be injective with `p` its only periodic point
(`s p = p`, and no `x ≠ p` returns to itself under iteration). Then any `s`-invariant set `S` is a
subsingleton or infinite — never a finite set of size ≥ 2. The finite middle is excluded because a
witness `x ≠ p` in `S` drags its whole (infinite) forward orbit into `S`.

**The framework's scale case is checked** at
`valBridge_forces_infinite` (`ZeroParadox/Valuation/ScaleBridge.lean`) runs the same argument for
the framework's scale map and concludes that a `ValBridge` carrier holding any point besides `bot` is
infinite. ⚠ It is **not** an instance of this theorem, and the reason is the `hs` hypothesis here:
`ValBridge` does not supply `Function.Injective s`, and cannot be made to — `L = {bot} ⊎ (ℕ × Bool)`
with `val (n, b) = n` and `scale (n, b) = (n+1, false)` satisfies all four of its axioms while
collapsing `(0, true)` with `(0, false)`. There the valuation supplies injectivity **along an orbit**
directly, which is all the argument consumes. Same argument, weaker hypothesis on that axis. -/
theorem orbit_dichotomy {X : Type*} (s : X → X) (hs : Function.Injective s) (p : X) (_hp : s p = p)
    (hper : ∀ (x : X) (n : ℕ), 0 < n → s^[n] x = x → x = p)
    {S : Set X} (hSinv : ∀ x ∈ S, s x ∈ S) :
    S.Subsingleton ∨ S.Infinite := by
  by_cases h : S.Subsingleton
  · exact Or.inl h
  · right
    rw [Set.not_subsingleton_iff] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    obtain ⟨x, hxS, hxp⟩ : ∃ x ∈ S, x ≠ p := by
      by_cases hap : a = p
      · exact ⟨b, hb, fun hbp => hab (hap.trans hbp.symm)⟩
      · exact ⟨a, ha, hap⟩
    have horb : ∀ n : ℕ, s^[n] x ∈ S := by
      intro n
      induction n with
      | zero => simpa using hxS
      | succ k ih => rw [Function.iterate_succ_apply']; exact hSinv _ ih
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => s^[n] x) _ horb
    intro n m hnm
    rcases le_total n m with hle | hle
    · obtain ⟨k, rfl⟩ := Nat.le.dest hle
      have h2 : s^[n] x = s^[n] (s^[k] x) := hnm.trans (Function.iterate_add_apply s n k x)
      have hx : x = s^[k] x := hs.iterate n h2
      rcases Nat.eq_zero_or_pos k with hk | hk
      · omega
      · exact absurd (hper x k hk hx.symm) hxp
    · obtain ⟨k, rfl⟩ := Nat.le.dest hle
      have h2 : s^[m] (s^[k] x) = s^[m] x := (Function.iterate_add_apply s m k x).symm.trans hnm
      have hx : s^[k] x = x := hs.iterate m h2
      rcases Nat.eq_zero_or_pos k with hk | hk
      · omega
      · exact absurd (hper x k hk hx) hxp

/-- Iterating scalar multiplication: `(c • ·)^[n] x = c^n • x`. -/
theorem iterate_smul {k V : Type*} [Monoid k] [MulAction k V] (c : k) (n : ℕ) (x : V) :
    (fun v => c • v)^[n] x = c ^ n • x := by
  induction n with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', ih, ← mul_smul, ← pow_succ']

/-- **The linear/scaling case.** The fixed points of a linear self-map over an ordered field are a
subsingleton or infinite — the "1 or ∞" dichotomy, no finite middle. Instance of `orbit_dichotomy` via
the scaling action `v ↦ 2 • v`: its only periodic point is `0` (`2^n ≠ 1`), and `Fix f` is
scaling-invariant because `f` is linear (`f (2•v) = 2•(f v)`). Stated over an ordered field for a clean
`2^n ≠ 1`; the framework's scale map `x ↦ 2x` on ℚ₂ (not ordered) obeys the same `orbit_dichotomy` argument
with `2^n ≠ 1` supplied by the 2-adic valuation (`v₂(2^n x) = n + v₂ x ≠ v₂ x` for `n ≥ 1`, `x ≠ 0`;
cf. `q2_unique_fp`, the "1" pole). Here the orbit hypothesis is *checkable*; for the λ-calculus see § fpp. -/
theorem linear_fix_dichotomy {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] {V : Type*}
    [AddCommGroup V] [Module k V] (f : V →ₗ[k] V) :
    {v : V | f v = v}.Subsingleton ∨ {v : V | f v = v}.Infinite := by
  apply orbit_dichotomy (fun v => (2 : k) • v) (smul_right_injective V two_ne_zero) 0 (by simp)
  · intro x n hn hx
    rw [iterate_smul] at hx
    have hne1 : (2 : k) ^ n ≠ 1 := ne_of_gt (one_lt_pow₀ one_lt_two (by omega))
    have h2 : ((2 : k) ^ n - 1) • x = 0 := by rw [sub_smul, hx, one_smul, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne1)
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smul, hx]

/-- **No finite middle, explicit.** If a linear self-map (over an ordered field) has *finitely many*
fixed points, it has at most one — the count can never be a finite number `≥ 2`. This is the sharp form
of the "1 or ∞" dichotomy that the recurring self-reference pattern rhymes with. -/
theorem linear_fix_finite_subsingleton {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    {V : Type*} [AddCommGroup V] [Module k V] (f : V →ₗ[k] V)
    (hfin : {v : V | f v = v}.Finite) : {v : V | f v = v}.Subsingleton :=
  (linear_fix_dichotomy f).resolve_right (Set.not_infinite.mpr hfin)

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms orbit_dichotomy
#print axioms linear_fix_dichotomy
#print axioms linear_fix_finite_subsingleton
end PurityCheck
