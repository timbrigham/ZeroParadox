-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.ENat
import ZeroParadox.Valuation.ContractionRate
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The floor's infinite complexity AS an infinitude of zeros (research spike)

## Engineer's Take

I have always thought that bottom itself was infinitely complex, and that this was true even when it
produces nothing. The honest way to say it is that it returns to the infinitude of zeroes, and that means it
meets both criteria at once, a single point and an infinite field. If bottom literally is infinity, then it
can be represented as an arbitrarily long set of functions linked together. To get the types to match I did
one instance out of the set meeting a specific set of requirements, which is the move we always end up
making. A re-description of the pole is exactly what you should get here, and that is the win, not a letdown.
It is literally changing your perspective to look back at the same object.

This was early, when I was chasing whether bottom being infinity could be an arbitrarily long chain of
functions linked together. Sometimes it helps to work through this from the ground up. Much of what is here
re-derives results the framework already has, and that is fine. The movement of the thought process itself was
what I needed.

---

## Formal Overview (AI-assisted)

A well-typed form of the claim **"the bottom's infinite complexity IS its being an infinitude of zeros."**
Rather than equate two objects across a type boundary (the MC-1 wall), we use the framework's
instance-meets-requirements move: a REQUIREMENTS typeclass `InfinitudeFloor` with a `floor` carrying a
complexity `cx : α → ℕ∞`, an infinitude of distinct `member`s below it whose complexities climb strictly,
and the identity field `cx_floor_eq_iSup : cx floor = ⨆ n, cx (member n)` — the floor's complexity IS the
supremum of the infinitude's.

Its consequence, `infinitude_forces_infinite_complexity` (`cx floor = ⊤`), says the infinitude of
(distinct, complexity-climbing) zeros is what MAKES the floor infinitely complex — recovering the
framework's `addVal_bot` (v₂(0) = ⊤, `Valuation/FloorWitness.lean`) as a fact ABOUT the infinitude, not a
separate assertion. "Same" is realized as "both are consequences of one requirements-structure, met by one
witness," not as a cross-type `=`.

Substance is in the WITNESS: the intended instance is ℤ₂ (floor = 0, cx = the 2-adic valuation,
member n = 2ⁿ⁺¹ so cx(member n) = n+1, climbing to ⊤ = v₂(0)). Status: **STUB (sorry)** — the abstract
requirements + payoff theorem + a toy witness (inhabitability) here; the ℤ₂ witness to follow.

## Structure
- § I   The requirements typeclass `InfinitudeFloor`.
- § II  The identity (well-typed) and its consequence (the infinitude forces infinite complexity).
- § III A toy witness (inhabitability); the ℤ₂ witness deferred to the fill.
-/

namespace ZeroParadox

/-! ### § I. The requirements -/

/-- **Requirements typeclass.** A `floor` whose complexity `cx` is the supremum of an infinitude of
distinct `member`s whose complexities climb strictly. The type-match device: we never equate the
complexity-object and the null-family; we require a witness meeting both, of which any instance is one. -/
class InfinitudeFloor (α : Type*) where
  /-- the bottom / floor. -/
  floor : α
  /-- complexity (a valuation / surprisal), ℕ∞-valued. -/
  cx : α → ℕ∞
  /-- the infinitude of zeros: distinct nulls indexed by ℕ. -/
  member : ℕ → α
  /-- each member is distinct from the floor (a "new" null, never the floor itself). -/
  member_ne_floor : ∀ n, member n ≠ floor
  /-- the members' complexities climb strictly (so they are pairwise distinct and unbounded in ℕ∞). -/
  cx_member_strictMono : StrictMono (fun n => cx (member n))
  /-- **the identity**: the floor's complexity is the supremum of the infinitude's. -/
  cx_floor_eq_iSup : cx floor = ⨆ n, cx (member n)

/-! ### § II. Two supпорt lemmas about `ℕ∞` -/

/-- The supremum of all naturals in `ℕ∞` is `⊤` (the value group is Archimedean-unbounded). -/
private theorem iSup_coe_top : ⨆ k : ℕ, (k : ℕ∞) = ⊤ := by
  rw [iSup_eq_top]
  intro b hb
  lift b to ℕ using hb.ne
  exact ⟨b + 1, by exact_mod_cast Nat.lt_succ_self b⟩

/-- A strictly monotone `ℕ → ℕ∞` dominates the coercion: `↑k ≤ g k`. -/
private theorem coe_le_of_strictMono {g : ℕ → ℕ∞} (hg : StrictMono g) (k : ℕ) : (k : ℕ∞) ≤ g k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hlt : (k : ℕ∞) < g (k + 1) := lt_of_le_of_lt ih (hg (Nat.lt_succ_self k))
      have hstep : (k : ℕ∞) + 1 ≤ g (k + 1) := (ENat.add_one_le_iff (by simp)).mpr hlt
      calc ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; ring
        _ ≤ g (k + 1) := hstep

/-- A strictly monotone `ℕ → ℕ∞` has supremum `⊤`. This is the engine: a strictly climbing infinitude is
unbounded in `ℕ∞`. -/
private theorem iSup_strictMono_top {g : ℕ → ℕ∞} (hg : StrictMono g) : ⨆ n, g n = ⊤ := by
  rw [← top_le_iff, ← iSup_coe_top]
  exact iSup_mono fun k => coe_le_of_strictMono hg k

/-! ### § III. The identity and its consequence -/

/-- **The identity, well-typed.** The floor's complexity IS the infinitude of zeros: the complexity at the
floor equals the supremum of the complexities across the infinitude of members. (Immediate from the
requirement; the content is exhibiting a witness — see § IV / the ℤ₂ instance.) -/
theorem infinite_complexity_is_infinitude_of_zeros (α : Type*) [I : InfinitudeFloor α] :
    I.cx I.floor = ⨆ n, I.cx (I.member n) :=
  I.cx_floor_eq_iSup

/-- **The consequence — the infinitude FORCES infinite complexity.** A strictly climbing infinitude of
distinct members drives the floor's complexity to ⊤: an `ℕ → ℕ∞` that is `StrictMono` is unbounded, so its
supremum is `⊤`. This recovers `addVal_bot` (v₂(0) = ⊤) as a fact about the infinitude of zeros, not a
separate axiom. -/
theorem infinitude_forces_infinite_complexity (α : Type*) [I : InfinitudeFloor α] :
    I.cx I.floor = ⊤ := by
  rw [I.cx_floor_eq_iSup]
  exact iSup_strictMono_top I.cx_member_strictMono

end ZeroParadox

/-! ### § IV. Toy witness (inhabitability) — the ℤ₂ witness follows -/

namespace ZeroParadox

/-- **Toy witness.** `ℕ∞` itself: `floor = ⊤`, `cx = id`, `member n = (n : ℕ∞)`. Degenerate (it collapses
an element with its own complexity) — included only to show the requirements are inhabitable and consistent.
The real, non-degenerate witness is ℤ₂ (floor = 0, cx = v₂), where the floor is the *bottom* yet carries
*top* complexity — the 0 = ∞ inversion the toy loses. -/
instance : InfinitudeFloor ℕ∞ where
  floor := ⊤
  cx := id
  member := fun n => (n : ℕ∞)
  member_ne_floor := fun n => by simp
  cx_member_strictMono := by intro a b h; simp only [id_eq]; exact_mod_cast h
  cx_floor_eq_iSup := by simp only [id_eq]; exact iSup_coe_top.symm

/-! ### § V. The substantive witness — a discrete valuation ring, AS a frame-change

The non-degenerate witness, and the point of the whole spike. In `R⟦X⟧` (a discrete valuation ring), the
`floor` is `0` — the genuine *bottom* — yet it carries `⊤` complexity (`order 0 = ⊤`, the framework's
`powerSeries_order_bot`). The infinitude of zeros is the chain `X, X², X³, …`, distinct nulls whose orders
climb `1, 2, 3, …`. The identity `order 0 = ⨆ order (Xⁿ⁺¹)` is not a surprising coincidence: it is the
**change of perspective** on one object — the order *at the limit* is the supremum of the orders *along the
infinitude climbing to it*. This is the complexity ↔ infinitude frame-flip, a sibling of `snap_is_frameflip`
/ `catseam_is_frameflip`: the same pole, looked at from the valuation chart and the infinitude chart. -/

open PowerSeries in
/-- **The DVR witness.** `R⟦X⟧` instantiates `InfinitudeFloor`: floor `0` (order `⊤`), the infinitude the
uniformizer powers `Xⁿ⁺¹` (orders climbing to `⊤`). The floor is the bottom, its complexity is the top —
the 0 = ∞ inversion, realized on the framework's own concrete floor witness. -/
noncomputable instance powerSeriesInfinitudeFloor {R : Type*} [CommRing R] [Nontrivial R] :
    InfinitudeFloor (PowerSeries R) where
  floor := 0
  cx := PowerSeries.order
  member := fun n => X ^ (n + 1)
  member_ne_floor := fun n => by
    intro hc
    have h1 : (X ^ (n + 1) : PowerSeries R).order = ⊤ := by rw [hc]; exact order_zero
    rw [order_X_pow] at h1
    exact (ENat.coe_ne_top (n + 1)) h1
  cx_member_strictMono := by
    intro a b h
    simp only [order_X_pow]
    exact_mod_cast Nat.add_lt_add_right h 1
  cx_floor_eq_iSup := by
    rw [order_zero]
    symm
    apply iSup_strictMono_top
    intro a b h
    simp only [order_X_pow]
    exact_mod_cast Nat.add_lt_add_right h 1

end ZeroParadox

namespace ZeroParadox

open Filter Topology

/-! ### § VI. The inversion — both poles, concurrently AND one after the other

The final condition. `InfinitudeFloor` already gives: the 0-pole (`floor`), the ∞-pole (`cx floor = ⊤`),
and the two **concurrently** at one point. This section adds the **descent** — the members converge to the
floor AS ELEMENTS (`member → floor`) — so that, paired with the complexity **ascent** (`cx∘member → ⊤`), the
chart flip `z ↦ 1/z` is realized: the 0-pole (element ↓ floor) and the ∞-pole (complexity ↑ ⊤) are the two
sides of one pole, traversed **one after the other** along the chain. Both poles, both concurrently (at the
floor) and sequentially (the inversion). The framework's `inversion_reverses_filtration` /
`nat_orbit_tendsto_zero_iff_two_dvd` are the 2-adic realization of this flip. -/

/-- **The inversion extension.** `InfinitudeFloor` plus a topology in which the infinitude descends to the
floor as elements. -/
class InfinitudeFloorInversion (α : Type*) [TopologicalSpace α] extends InfinitudeFloor α where
  /-- the members descend to the floor as elements (the 0-pole approach). -/
  member_tendsto_floor : Tendsto member atTop (nhds floor)

/-- **All four in one shape.** Along the infinitude the element descends to the 0-pole (`member → floor`)
while the complexity ascends to the ∞-pole (`cx∘member → ⊤`) — both poles, concurrently at the floor
(`cx floor = ⊤`) and one after the other along the chain (the `z ↦ 1/z` chart flip). One typeclass holds the
zero pole, the infinity pole, their coincidence, and their inversion. -/
theorem pole_inversion (α : Type*) [TopologicalSpace α] [I : InfinitudeFloorInversion α] :
    Tendsto I.member atTop (nhds I.floor) ∧
      Tendsto (fun n => I.cx (I.member n)) atTop (nhds (⊤ : ℕ∞)) := by
  refine ⟨I.member_tendsto_floor, ?_⟩
  have h := tendsto_atTop_iSup I.cx_member_strictMono.monotone
  rwa [iSup_strictMono_top I.cx_member_strictMono] at h

/-- Toy inversion witness (degenerate): in `ℕ∞`, `n → ⊤`. Here the element and the complexity climb
together, so there is no genuine inversion — the real one is the 2-adic witness (element ↓ 0 while
valuation ↑ ⊤). Included only to confirm the extended shape is inhabitable. -/
instance : InfinitudeFloorInversion ℕ∞ :=
  { (inferInstance : InfinitudeFloor ℕ∞) with
    member_tendsto_floor := by
      have h := tendsto_atTop_iSup (f := fun n : ℕ => (n : ℕ∞)) (fun a b hab => by dsimp only; exact_mod_cast hab)
      rwa [iSup_coe_top] at h }

/-! ### § VII. The 2-adic witness — the genuine inversion (element ↓ 0, valuation ↑ ∞)

The non-degenerate witness, on the framework's actual bottom `ℚ_[2]`. Floor `0` carries `⊤` complexity; the
infinitude `2ⁿ⁺¹` **descends** to `0` (the framework's `two_is_contraction` / `nat_orbit_tendsto_zero`)
while its valuation **ascends** to `⊤`. Element down, complexity up — the genuine `z ↦ 1/z` flip, unlike the
`ℕ∞` toy where they climb together. -/

open Classical in
/-- The ℕ∞-valued 2-adic complexity: `⊤` at the floor `0`, the p-adic valuation elsewhere. -/
noncomputable def cxQ2 (x : Q₂) : ℕ∞ := if x = 0 then ⊤ else (x.valuation.toNat : ℕ∞)

/-- The 2-adic valuation of `2ᵏ` is `k`. -/
lemma two_pow_valuation (k : ℕ) : ((2 : Q₂) ^ k).valuation = (k : ℤ) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h2 : (2 : Q₂) ≠ 0 := two_ne_zero
    have hpow : (2 : Q₂) ^ n ≠ 0 := pow_ne_zero n h2
    have hv2 : (2 : Q₂).valuation = 1 := by
      rw [show (2 : Q₂) = ((2 : ℕ) : Q₂) by norm_cast]
      exact_mod_cast Padic.valuation_p
    rw [pow_succ, Padic.valuation_mul hpow h2, ih, hv2]
    push_cast; ring

lemma cxQ2_two_pow (k : ℕ) : cxQ2 ((2 : Q₂) ^ k) = (k : ℕ∞) := by
  unfold cxQ2
  rw [if_neg (pow_ne_zero k two_ne_zero), two_pow_valuation]
  simp

lemma cxQ2_zero : cxQ2 (0 : Q₂) = ⊤ := by unfold cxQ2; rw [if_pos rfl]

/-- **The 2-adic witness — `InfinitudeFloor`.** Floor `0` (complexity `⊤`), infinitude `2ⁿ⁺¹`. -/
noncomputable instance q2InfinitudeFloor : InfinitudeFloor Q₂ where
  floor := 0
  cx := cxQ2
  member := fun n => (2 : Q₂) ^ (n + 1)
  member_ne_floor := fun n => pow_ne_zero (n + 1) two_ne_zero
  cx_member_strictMono := by
    intro a b h
    show cxQ2 ((2 : Q₂) ^ (a + 1)) < cxQ2 ((2 : Q₂) ^ (b + 1))
    rw [cxQ2_two_pow, cxQ2_two_pow]
    exact_mod_cast Nat.add_lt_add_right h 1
  cx_floor_eq_iSup := by
    show cxQ2 (0 : Q₂) = ⨆ n, cxQ2 ((2 : Q₂) ^ (n + 1))
    rw [cxQ2_zero]
    symm
    apply iSup_strictMono_top
    intro a b h
    show cxQ2 ((2 : Q₂) ^ (a + 1)) < cxQ2 ((2 : Q₂) ^ (b + 1))
    rw [cxQ2_two_pow, cxQ2_two_pow]
    exact_mod_cast Nat.add_lt_add_right h 1

/-- **The 2-adic witness — the full inversion.** The infinitude `2ⁿ⁺¹` descends to `0` while its valuation
ascends to `⊤`: the genuine `z ↦ 1/z` flip on the framework's actual bottom, all four conditions in one. -/
noncomputable instance : InfinitudeFloorInversion Q₂ :=
  { q2InfinitudeFloor with
    member_tendsto_floor := by
      have hbase : Tendsto (fun n : ℕ => (2 : Q₂) ^ n) atTop (nhds 0) :=
        (pure_orbit_tendsto_zero_iff_norm_lt_one 2).mpr two_is_contraction
      exact hbase.comp (tendsto_add_atTop_nat 1) }

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms infinite_complexity_is_infinitude_of_zeros
#print axioms infinitude_forces_infinite_complexity
#print axioms pole_inversion
#print axioms two_pow_valuation

end PurityCheck
