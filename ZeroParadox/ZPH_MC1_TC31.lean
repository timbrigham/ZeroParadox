-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_PerronFrobenius
import ZeroParadox.ZPH_MeanErgodic
import ZeroParadox.ZPH_MC1_TC23
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H / TC31: irreducibility forces a unique stationary distribution for node #2

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This is the **constructive complement** to TC23's NO-GO. TC23 proved that a *doubly-stochastic*
kernel can fail uniqueness of the stationary distribution: its `blockKernel` had two absorbing
classes (`pure 0`, `pure 1`), so the stationary predicate `IsStationaryPMF` was **not** a
subsingleton, and node #2 (the Markov-dynamical attractor) had no unique stationary distribution under
doubly-stochasticity (no unique fixed point — what one would *read* as the terminal / final-coalgebra
(ν) universal property, though no such categorical object is built anywhere in this campaign).
TC23 flagged that **irreducibility** (a single
communicating class) *would* give uniqueness, but irreducibility was not a registered hypothesis of
the campaign's ergodic machinery.

**This file builds the positive witness.** It registers a concrete **irreducible** doubly-stochastic
kernel — the cyclic-shift kernel `cycKernel j := pure (j + 1)` on `Fin (n+1)` — and proves, *by hand*
and *against the pin* (no primitivity / Perron–Frobenius uniqueness machinery, which is absent), that
its stationary set is a **subsingleton**:

* `cyc_bind_apply` : the transfer at `k` is `μ (k - 1)` (the cyclic shift moves mass one step).
* `cyc_stationary_iff_shift_inv` : `μ` is stationary ⟺ `μ` is invariant under `+1`.
* `cyc_stationary_const` : a stationary `μ` is **constant** (the single communicating class forces
  all values equal — this is exactly irreducibility doing the work).
* `cyc_stationary_subsingleton` : **the load-bearing theorem.** Any two stationary distributions are
  equal — the stationary PMF of this one irreducible cyclic kernel is **unique**.

**Interpretation note (NOT proved in Lean).** A unique fixed point of an endomorphism is, *read
categorically*, a terminal / final-coalgebra (ν) universal object. That categorical reading is an
**interpretation**: this file constructs no category, no terminal object, and no coalgebra. The Lean
content is exactly *uniqueness of the stationary PMF* for the concrete cyclic kernel — a property of a
single distribution, not a universal property of an object in a category.

The capstone `markov_node_irreducible_rescue` packages both halves of the boundary:

1. the same kernel is doubly-stochastic and **not** the identity (it moves mass), yet
2. its stationary predicate **is** a subsingleton.

Paired with TC23's `doublyStochastic_stationary_not_subsingleton`, this draws the boundary exactly:
the antichain / non-uniqueness obstruction on #2 is an **irreducibility phenomenon**, not absolute.
Reducible ⇒ non-unique (TC23); irreducible (cyclic) ⇒ unique (here).

**Honest scope.** The Lean proves uniqueness *for this one concrete irreducible kernel*, by an
elementary argument special to the cyclic shift (stationarity forces invariance under a generator of
the cyclic group, hence constancy). It does **not** prove the general theorem "every irreducible
finite chain has a unique stationary distribution" — that is the Perron–Frobenius statement the pin
does not supply. So the result is: a *witnessed* example where irreducibility delivers the unique
stationary distribution TC23's reducible witness denied. Verdict: **GO** — the rescue is buildable;
node #2's stationary fixed point becomes unique once the class is made irreducible. (The categorical
reading — calling a unique fixed point a terminal / final-coalgebra (ν) universal object — is an
interpretation only; no category, terminal object, or coalgebra is constructed in this file.)
-/

namespace ZeroParadox.ZPH_MC1_TC31

open scoped BigOperators ENNReal
open ZeroParadox.MeanErgodic
open ZeroParadox.ZPH_MC1_TC23 (IsStationaryPMF)

variable {n : ℕ}

/-- The **cyclic-shift kernel** on `Fin (n+1)`: `j ↦ pure (j + 1)`. This is a single-cycle
    permutation kernel — every state communicates with every other state by repeated `+1`, so the
    chain is **irreducible** (one communicating class), in contrast to TC23's reducible `blockKernel`. -/
noncomputable def cycKernel : Fin (n + 1) → PMF (Fin (n + 1)) := fun j => PMF.pure (j + 1)

/-- The cyclic kernel **moves mass**: it sends `0` to `pure 1 ≠ pure 0` (for `n ≥ 1`). Like TC23's
    `blockKernel`, this is not the do-nothing identity. -/
theorem cycKernel_ne_id {n : ℕ} : (cycKernel (n := n + 1)) 0 ≠ PMF.pure 0 := by
  intro h
  have e : (PMF.pure ((0 : Fin (n + 2)) + 1)) 0 = (PMF.pure (0 : Fin (n + 2))) 0 := by
    rw [show PMF.pure ((0 : Fin (n + 2)) + 1) = (cycKernel (n := n + 1)) 0 from rfl, h]
  have hne : (0 : Fin (n + 2)) ≠ ((0 : Fin (n + 2)) + 1) := by
    rw [zero_add]; exact (zero_ne_one (α := Fin (n + 2)))
  rw [PMF.pure_apply_of_ne _ 0 hne, PMF.pure_apply_self 0] at e
  exact zero_ne_one e

/-- The cyclic kernel is **doubly stochastic**: column `k` of its transfer matrix is the indicator of
    `j + 1 = k`, with the unique hit at `j = k - 1`. -/
theorem cycKernel_doublyStochastic : DoublyStochastic (cycKernel (n := n)) := by
  intro k
  rw [Finset.sum_eq_single (k - 1)]
  · -- (k-1) + 1 = k, so the term is (pure k) k = 1
    show ((PMF.pure ((k - 1) + 1)) k).toReal = 1
    rw [sub_add_cancel, PMF.pure_apply_self, ENNReal.toReal_one]
  · intro j _ hj
    -- j ≠ k - 1 ⇒ j + 1 ≠ k ⇒ (pure (j+1)) k = 0
    show ((PMF.pure (j + 1)) k).toReal = 0
    rw [PMF.pure_apply_of_ne _ k ?_, ENNReal.toReal_zero]
    intro hk
    -- hk : k = j + 1 ⇒ k - 1 = j, contradicting hj
    exact hj (by rw [hk, add_sub_cancel_right])
  · intro h; exact absurd (Finset.mem_univ (k - 1)) h

/-! ## The transfer computation -/

/-- **Transfer formula.** The cyclic transfer of `μ` at `k` is `μ (k - 1)`: all mass at `k - 1` is
    pushed to `k`. -/
theorem cyc_bind_apply (μ : PMF (Fin (n + 1))) (k : Fin (n + 1)) :
    (μ.bind (cycKernel (n := n))) k = μ (k - 1) := by
  rw [PMF.bind_apply]
  rw [tsum_eq_single (k - 1)]
  · -- the surviving term: μ (k-1) * (pure ((k-1)+1)) k = μ (k-1) * 1
    show μ (k - 1) * (PMF.pure ((k - 1) + 1)) k = μ (k - 1)
    rw [sub_add_cancel, PMF.pure_apply_self, mul_one]
  · intro j hj
    -- j ≠ k - 1 ⇒ j + 1 ≠ k ⇒ pure term is 0
    show μ j * (PMF.pure (j + 1)) k = 0
    rw [PMF.pure_apply_of_ne _ k ?_, mul_zero]
    intro hk
    exact hj (by rw [hk, add_sub_cancel_right])

/-! ## Stationary ⟺ shift-invariant -/

/-- A stationary `μ` is **invariant under `+1`**: `μ j = μ (j + 1)` for all `j`. (This is the cyclic
    chain having a single communicating class doing its work.) -/
theorem cyc_stationary_shift_inv {μ : PMF (Fin (n + 1))}
    (hμ : IsStationaryPMF (cycKernel (n := n)) μ) (j : Fin (n + 1)) :
    μ j = μ (j + 1) := by
  -- stationarity at k = j + 1 gives μ ((j+1) - 1) = μ (j+1), i.e. μ j = μ (j+1)
  have h : (μ.bind (cycKernel (n := n))) (j + 1) = μ (j + 1) := by
    rw [hμ]
  rw [cyc_bind_apply] at h
  rwa [add_sub_cancel_right] at h

/-- A stationary `μ` is **constant**: invariance under the generator `+1` of the cyclic group forces
    all coordinates equal. This is the heart of the irreducibility rescue.

    We iterate the shift `s = (· + 1)`: `μ a = μ (sᵐ a)` for every `m`, and `s^[(b - a).val] a = b`
    because applying `+ 1` exactly `(b - a).val` times to `a` adds `b - a` (whose `val` is `< n + 1`),
    landing on `b`. -/
theorem cyc_stationary_const {μ : PMF (Fin (n + 1))}
    (hμ : IsStationaryPMF (cycKernel (n := n)) μ) (a b : Fin (n + 1)) :
    μ a = μ b := by
  -- the shift map
  set s : Fin (n + 1) → Fin (n + 1) := fun x => x + 1 with hs
  -- μ is invariant under every iterate of s
  have iter_inv : ∀ (m : ℕ) (x : Fin (n + 1)), μ x = μ (s^[m] x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [ih x, Function.iterate_succ_apply' s m x]
        exact cyc_stationary_shift_inv hμ (s^[m] x)
  -- applying s exactly (b-a).val times to a lands on b
  have iter_hit : s^[(b - a).val] a = b := by
    -- value of the iterate: (s^[m] a).val = (a.val + m) % (n+1)
    have key : ∀ (m : ℕ), (s^[m] a).val = (a.val + m) % (n + 1) := by
      intro m
      induction m with
      | zero => simp [Nat.mod_eq_of_lt a.isLt]
      | succ m ih =>
          rw [Function.iterate_succ_apply' s m a, hs]
          show ((s^[m] a) + 1).val = (a.val + (m + 1)) % (n + 1)
          rw [Fin.val_add, ih]
          have hone : ((1 : Fin (n + 1)) : ℕ) = 1 % (n + 1) := Fin.val_one' (n + 1)
          rw [hone, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
    apply Fin.ext
    rw [key]
    -- a.val + (b - a).val ≡ b.val  (mod n+1)
    have hmod : (a.val + (b - a).val) % (n + 1) = b.val := by
      have hsub : ((b - a) : Fin (n + 1)).val = ((n + 1 - a.val) + b.val) % (n + 1) := by
        rw [Fin.sub_def]
      rw [hsub]
      have ha : a.val < n + 1 := a.isLt
      have hb : b.val < n + 1 := b.isLt
      -- a.val + (((n+1 - a.val) + b.val) % (n+1)) ≡ b.val mod (n+1)
      rw [Nat.add_mod_mod]
      have heq : a.val + ((n + 1 - a.val) + b.val) = b.val + (n + 1) := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
    rw [hmod]
  rw [iter_inv (b - a).val a, iter_hit]

/-! ## The load-bearing theorem: subsingleton (unique fixed point) -/

/-- **GO — the load-bearing theorem.** The stationary set of the *irreducible* cyclic-shift kernel is
    a **subsingleton**: any two stationary distributions are equal. In plain terms: *this one
    irreducible cyclic kernel has a unique stationary distribution*, in contrast to TC23's *reducible*
    `blockKernel`, which has more than one.

    Interpretation note (NOT proved here): a unique fixed point can be *read* as a terminal /
    final-coalgebra (ν) universal object, but no category, terminal object, or coalgebra is built in
    this file — the proved content is uniqueness of a stationary PMF, not a categorical universal
    property.

    Proof: both `μ` and `ν` are constant (`cyc_stationary_const`); a constant PMF on a finite type is
    pinned by the mass constraint `(card) • value = 1`, so the two constants coincide. -/
theorem cyc_stationary_subsingleton
    (μ ν : PMF (Fin (n + 1)))
    (hμ : IsStationaryPMF (cycKernel (n := n)) μ)
    (hν : IsStationaryPMF (cycKernel (n := n)) ν) :
    μ = ν := by
  -- both constant
  have cμ : ∀ a b, μ a = μ b := cyc_stationary_const hμ
  have cν : ∀ a b, ν a = ν b := cyc_stationary_const hν
  ext k
  -- card • (μ 0) = ∑ x, μ x = 1, and likewise for ν, so μ 0 = ν 0; then μ k = μ 0 = ν 0 = ν k
  have card : Fintype.card (Fin (n + 1)) = n + 1 := Fintype.card_fin _
  -- sum of a constant
  have sumμ : ∑ x : Fin (n + 1), μ x = (n + 1 : ℕ) • μ 0 := by
    rw [Finset.sum_congr rfl (fun x _ => cμ x 0)]
    rw [Finset.sum_const, Finset.card_univ, card]
  have sumν : ∑ x : Fin (n + 1), ν x = (n + 1 : ℕ) • ν 0 := by
    rw [Finset.sum_congr rfl (fun x _ => cν x 0)]
    rw [Finset.sum_const, Finset.card_univ, card]
  -- the sums are both 1 (PMF over a Fintype)
  have totμ : ∑ x : Fin (n + 1), μ x = 1 := by
    rw [← PMF.tsum_coe μ, tsum_eq_sum (s := Finset.univ)
      (fun x hx => absurd (Finset.mem_univ x) hx)]
  have totν : ∑ x : Fin (n + 1), ν x = 1 := by
    rw [← PMF.tsum_coe ν, tsum_eq_sum (s := Finset.univ)
      (fun x hx => absurd (Finset.mem_univ x) hx)]
  -- so (n+1) • μ 0 = 1 = (n+1) • ν 0, with (n+1) ≠ 0 in ENNReal ⇒ μ 0 = ν 0
  have eμ : ((n + 1 : ℕ) : ℝ≥0∞) * μ 0 = 1 := by
    rw [← totμ, sumμ, nsmul_eq_mul]
  have eν : ((n + 1 : ℕ) : ℝ≥0∞) * ν 0 = 1 := by
    rw [← totν, sumν, nsmul_eq_mul]
  have h0 : μ 0 = ν 0 := by
    have hc0 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
      simp
    have hcinf : ((n + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := by
      simp
    rw [← ENNReal.mul_right_inj hc0 hcinf, eμ, eν]
  rw [cμ k 0, cν k 0, h0]

/-! ## Capstone: the boundary of where the obstruction bites -/

/-- **Capstone — the irreducibility rescue.** There is a kernel on `Fin (n+1)` that is

    1. **doubly-stochastic** and **not** the identity (it moves mass — same status as TC23's
       reducible witness), yet
    2. its stationary predicate **is** a subsingleton (a genuine **unique** fixed point).

    Together with TC23's `doublyStochastic_stationary_not_subsingleton` (a reducible doubly-stochastic
    kernel whose stationary predicate is *not* a subsingleton), this pins the boundary: the failure of
    *stationary-distribution uniqueness* for node #2 is an **irreducibility phenomenon**, not absolute.
    Reducible ⇒ non-unique; irreducible (cyclic) ⇒ unique.

    Interpretation note (NOT proved here): uniqueness of the fixed point is what one would *read* as
    the ν / final-coalgebra universal property, but this file constructs no category or coalgebra; the
    Lean statement is exactly the implication "two stationary PMFs of `f` are equal". -/
theorem markov_node_irreducible_rescue {n : ℕ} :
    ∃ f : Fin (n + 2) → PMF (Fin (n + 2)),
      DoublyStochastic f ∧ f 0 ≠ PMF.pure 0 ∧
      (∀ μ ν : PMF (Fin (n + 2)), IsStationaryPMF f μ → IsStationaryPMF f ν → μ = ν) :=
  ⟨cycKernel (n := n + 1), cycKernel_doublyStochastic, cycKernel_ne_id,
    cyc_stationary_subsingleton⟩

end ZeroParadox.ZPH_MC1_TC31

/-! ## Axiom Purity Check

`Classical.choice` enters via the Mathlib PMF / `tsum` / ENNReal libraries — a library dependency, not
a new commitment. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC31

#print axioms cycKernel_doublyStochastic
#print axioms cyc_bind_apply
#print axioms cyc_stationary_shift_inv
#print axioms cyc_stationary_const
#print axioms cyc_stationary_subsingleton
#print axioms markov_node_irreducible_rescue

end PurityCheck
