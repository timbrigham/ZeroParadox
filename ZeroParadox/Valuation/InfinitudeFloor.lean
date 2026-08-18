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

## Formal Overview
The claim *"the floor's infinite complexity IS its being an infinitude of zeros"*, well-typed — as a
REQUIREMENTS class rather than a cross-type `=`. Substance is in the WITNESS (ℚ₂); the class itself
pins down only that the carrier is infinite. Requirements, witnesses and the NO-GO: `ZeroParadox/Valuation/InfinitudeFloor.md`.
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
  /-- the members' complexities climb strictly (so they are pairwise distinct and unbounded in ℕ∞). -/
  cx_member_strictMono : StrictMono (fun n => cx (member n))
  /-- **the identity**: the floor's complexity is the supremum of the infinitude's. -/
  cx_floor_eq_iSup : cx floor = ⨆ n, cx (member n)

/-! ### § II. Two support lemmas about `ℕ∞` -/

/-- The supremum of all naturals in `ℕ∞` is `⊤` (`ℕ∞` is Archimedean-unbounded). -/
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

/-! ### § III-b. The OFFSET structure — the floor is the only point at infinite distance

**Why the tower's `+1` is FORCED, not conventional** (Tim's question, 2026-08-05): no member can be
the floor (`member_ne_floor` below — a member there would sit at `⊤` with nothing able to climb past
it), so an enumeration seeded at the floor begins at the successor, exactly `towerInfinitudeFloor`'s
`member n = cnfToZp2 (towerNONote (n + 1))`. ⊥ admits no offset because its down-set is `{⊥}`
(`ZeroParadox/Order/Snap.lean`) and a difference needs two points.
⚠ **`Reading:` that the approximation index, the `+1`, and the transport asymmetry are ONE phenomenon
is the framework's interpretation** — a shared shape across distinct structures, hence a **type
boundary, never a common theorem**. -/

namespace ZeroParadox


/-- **`Statement:` every member sits at FINITE complexity.** A strictly increasing `ℕ∞`-valued sequence
cannot take the value `⊤`: a term equal to `⊤` would need a successor strictly above it. Note this is
**not** assumed — the class asks only that the complexities climb. -/
theorem member_cx_lt_top {α : Type*} [I : InfinitudeFloor α] (n : ℕ) :
    I.cx (I.member n) < ⊤ := by
  rcases eq_or_lt_of_le (le_top : I.cx (I.member n) ≤ ⊤) with h | h
  · exfalso
    have hstep : I.cx (I.member n) < I.cx (I.member (n + 1)) :=
      I.cx_member_strictMono (Nat.lt_succ_self n)
    rw [h] at hstep
    exact absurd hstep (not_lt.mpr le_top)
  · exact h

/-- **`Statement:` no member shares the floor's complexity.** The measurement-level statement:
members differ from the floor not merely as elements, but in **how far out they sit**. Proved from
`infinitude_forces_infinite_complexity` and `member_cx_lt_top` (which is where `cx_member_strictMono`
enters, one step further back). -/
theorem member_cx_ne_floor_cx {α : Type*} [I : InfinitudeFloor α] (n : ℕ) :
    I.cx (I.member n) ≠ I.cx I.floor := by
  rw [infinitude_forces_infinite_complexity α]
  exact ne_of_lt (member_cx_lt_top n)

/-- **`Statement:` no member IS the floor** — a "new" null, never the floor itself. Immediate from
`member_cx_ne_floor_cx`: equal elements would have equal complexity. -/
theorem member_ne_floor {α : Type*} [I : InfinitudeFloor α] (n : ℕ) :
    I.member n ≠ I.floor :=
  fun h => member_cx_ne_floor_cx n (congrArg I.cx h)

/-- **`Statement:` the offset is recoverable WITHIN the carrier** — distinct indices give distinct
members, because the complexities strictly climb.

`Reading:` (conjectural, and **narrower than a first draft claimed**) contrast this with the
**notation** map `e0Repr`, where distinct representations provably collapse (`e0Repr_not_injective`) —
there position is not recoverable. ⚠ **Do not generalize that to "transport" as such**: the very
citation offered alongside it, `tower_repr_orderEmbedding` (`ZeroParadox/Ordinal/CnfBridge.lean`),
shows the index's **order** crossing intact on that map, and `seed_maps_to_bot_both` pins index 0 on
both sides. So recoverability varies **by map**, not by "inside vs between carriers". -/
theorem member_injective {α : Type*} [I : InfinitudeFloor α] :
    Function.Injective (I.member) := fun _ _ hab =>
  I.cx_member_strictMono.injective (congrArg I.cx hab)

/-- **`Statement:` the floor is the UNIQUE point of the family at infinite distance.** Restricted to
the floor and its members, `cx x = ⊤` holds exactly at the floor.

⚠ **Scoped to the family on purpose.** The class says nothing about arbitrary elements of `α`, so this
is **not** a uniqueness claim about the carrier — `infinitude_forces_infinite_complexity` gives no such
thing, and `ZeroParadox/Category/WellFoundedCoalgebra.lean` records the same **shape** of fence (there
it scopes `Type u` against the MC-1 carriers — related in shape, not the same fence). -/
theorem floor_unique_at_top {α : Type*} [I : InfinitudeFloor α] (x : α)
    (hx : x = I.floor ∨ ∃ n, x = I.member n) :
    I.cx x = ⊤ ↔ x = I.floor := by
  constructor
  · intro htop
    rcases hx with rfl | ⟨n, rfl⟩
    · rfl
    · exact absurd htop (ne_of_lt (member_cx_lt_top n))
  · rintro rfl
    exact infinitude_forces_infinite_complexity α

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
  cx_member_strictMono := by intro a b h; simp only [id_eq]; exact_mod_cast h
  cx_floor_eq_iSup := by simp only [id_eq]; exact iSup_coe_top.symm

/-! ### § V. The substantive witness — a power-series ring, AS a frame-change

The non-degenerate witness, and the point of the whole spike. In `R⟦X⟧`, the
`floor` is `0` — the genuine *bottom* — yet it carries `⊤` complexity (`order 0 = ⊤`, the framework's
`powerSeries_order_bot`). The infinitude of zeros is the chain `X, X², X³, …`, distinct nulls whose orders
climb `1, 2, 3, …`. The identity `order 0 = ⨆ order (Xⁿ⁺¹)` is not a surprising coincidence: it is the
**change of perspective** on one object — the order *at the limit* is the supremum of the orders *along the
infinitude climbing to it*. This is the complexity ↔ infinitude frame-flip, a sibling of `snap_is_frameflip`
/ `catseam_is_frameflip`: the same pole, looked at from the valuation chart and the infinitude chart. -/

open PowerSeries in
/-- **The power-series witness.** `R⟦X⟧` instantiates `InfinitudeFloor`: floor `0` (order `⊤`), the infinitude the
uniformizer powers `Xⁿ⁺¹` (orders climbing to `⊤`). The floor is the bottom, its complexity is the top —
the 0 = ∞ inversion, realized on the framework's own concrete floor witness. -/
noncomputable instance powerSeriesInfinitudeFloor {R : Type*} [CommRing R] [Nontrivial R] :
    InfinitudeFloor (PowerSeries R) where
  floor := 0
  cx := PowerSeries.order
  member := fun n => X ^ (n + 1)
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
(`cx floor = ⊤`) and one after the other along the chain (the `z ↦ 1/z` chart flip). One **typeclass**
holds the zero pole, the infinity pole, their coincidence, and their inversion.

⚠ **This THEOREM holds only the DRIFT.** Its conclusion is the two `Tendsto` conjuncts and contains
no `cx floor = ⊤`; the coincidence is carried by the *class*, and its witness is the separate
declaration `infinitude_forces_infinite_complexity`. Do not cite this theorem for the coincidence.
(`CLAUDE.md` named it the coincidence witness until 2026-08-06, contradicting its own KIND table,
which had it under DRIFT all along. The table was right.) -/
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

/-! ### § VIII. NO-GO — what the requirements class does and does not pin down

**A CHARACTERISATION, not a bare negative:** `member_injective` supplies `ℕ ↪ α`, so the class **forces
`α` INFINITE** — and `infinitudeFloor_nonempty_iff_infinite` below proves it pins down nothing else.
⚠ Do not say the class "carries no content"; `member_injective` refutes that. The precedent, why
non-degeneracy must be an INEQUATION (Burris & Sankappanavar), and the unbuilt extension: `ZeroParadox/Valuation/InfinitudeFloor.md`. -/

/-- **`Statement:` the class DOES constrain its carrier — it forces infinitude.** `member_injective`
(§ III-b) gives `ℕ ↪ α`; the conclusion is Mathlib's `Infinite.of_injective` applied to it. This is
the reason the "says nothing about `α`" reading is false. -/
theorem infinitudeFloor_forces_infinite {α : Type*} [I : InfinitudeFloor α] : Infinite α :=
  Infinite.of_injective I.member member_injective

/-- **`Statement:` so NO FINITE TYPE carries the class** — stated for every finite carrier, not just
`PUnit`. An earlier version proved only the `PUnit` case while its gloss claimed the general one. -/
theorem no_infinitudeFloor_of_finite (α : Type*) [Finite α] : IsEmpty (InfinitudeFloor α) :=
  ⟨fun I => by haveI := @infinitudeFloor_forces_infinite α I; exact not_finite α⟩

/-- The bookkeeping carrier: `ℕ` with one extra point adjoined. ⚠ Canonically equivalent to `ℕ∞` — see
the section header; it is § IV's witness transported, chosen because every `InfinitudeFloor` field
below is then discharged from data written down by hand. -/
abbrev BookkeepingCarrier : Type := ℕ ⊕ Unit

/-- **`Statement:` the requirements class is satisfied with all fields hand-supplied.**

Deliberately a `def` and **not** an `instance`: registering it globally would put a junk
`InfinitudeFloor` into instance search, and the instance hazard is a recorded defect class here. -/
@[reducible] def bookkeepingInfinitudeFloor : InfinitudeFloor BookkeepingCarrier where
  floor := Sum.inr ()
  cx := Sum.elim (fun n => (n : ℕ∞)) (fun _ => ⊤)
  member := Sum.inl
  cx_member_strictMono := by intro a b h; dsimp only [Sum.elim_inl]; exact_mod_cast h
  cx_floor_eq_iSup := iSup_coe_top.symm

/-- **`Statement:` the no-go, as a theorem rather than a definition.** -/
theorem bookkeeping_nonempty : Nonempty (InfinitudeFloor BookkeepingCarrier) :=
  ⟨bookkeepingInfinitudeFloor⟩

/-- **The converse construction:** every infinite carrier admits an `InfinitudeFloor`. The floor is
`e 0` and the members are `e (n+1)` for an embedding `e : ℕ ↪ α`; `cx` sends the floor to `⊤` and each
other point to its index. Noncomputable and classical — `cx` must be defined on ALL of `α`, which is
exactly the obstruction an earlier draft named when it declined to claim this. -/
@[reducible] noncomputable def infinitudeFloorOfInfinite (α : Type*) [Infinite α] :
    InfinitudeFloor α :=
  letI := Classical.decEq α
  let e := Infinite.natEmbedding α
  have hinv : ∀ k : ℕ, Function.invFun e (e k) = k := Function.leftInverse_invFun e.injective
  have hne : ∀ k : ℕ, e (k + 1) ≠ e 0 := fun k h => by have := e.injective h; omega
  { floor := e 0
    cx := fun x => if x = e 0 then ⊤ else ((Function.invFun e x : ℕ) : ℕ∞)
    member := fun n => e (n + 1)
    cx_member_strictMono := by
      intro a b hab
      dsimp only
      rw [if_neg (hne a), if_neg (hne b), hinv, hinv]
      exact_mod_cast Nat.succ_lt_succ hab
    cx_floor_eq_iSup := by
      have hstep : ∀ n : ℕ,
          (if e (n + 1) = e 0 then (⊤ : ℕ∞) else ((Function.invFun e (e (n + 1)) : ℕ) : ℕ∞))
            = ((n + 1 : ℕ) : ℕ∞) := fun n => by rw [if_neg (hne n), hinv]
      have key : ⨆ n : ℕ, ((n + 1 : ℕ) : ℕ∞) = ⊤ := by
        rw [iSup_eq_top]
        intro b hb
        lift b to ℕ using hb.ne
        exact ⟨b, by exact_mod_cast Nat.lt_succ_self b⟩
      rw [if_pos rfl, iSup_congr hstep, key] }

/-- **`Statement:` THE CHARACTERISATION — the class pins down infinitude and nothing else.**

Forward: `infinitudeFloor_forces_infinite`. Converse: `infinitudeFloorOfInfinite`. Together they say
`[InfinitudeFloor α]` is exactly as informative as `Infinite α` — which is what makes the hand-built
witness below a fair gauge rather than a curiosity, and what a non-degeneracy predicate would have to
strengthen. -/
theorem infinitudeFloor_nonempty_iff_infinite (α : Type*) :
    Nonempty (InfinitudeFloor α) ↔ Infinite α :=
  ⟨fun ⟨I⟩ => @infinitudeFloor_forces_infinite α I,
   fun h => ⟨@infinitudeFloorOfInfinite α h⟩⟩

/-- **`Statement:` § III's headline theorem holds of the bookkeeping carrier.** Instantiated here it
says a two-constructor bookkeeping type has a floor of infinite complexity — true, and empty of the
content the substantive witnesses carry. That contrast is the whole point of the gauge. -/
theorem bookkeeping_forces_infinite_complexity :
    bookkeepingInfinitudeFloor.cx bookkeepingInfinitudeFloor.floor = ⊤ :=
  infinitude_forces_infinite_complexity (I := bookkeepingInfinitudeFloor) BookkeepingCarrier

/-- **`Statement:` the members are distinct from the floor here.** A readability specialization of
`member_ne_floor`, which holds of EVERY `InfinitudeFloor` — so it witnesses nothing specific to this
hand-built one. ⚠ It says nothing about limits or convergence. -/
theorem bookkeeping_members_ne_floor (n : ℕ) :
    bookkeepingInfinitudeFloor.member n ≠ bookkeepingInfinitudeFloor.floor :=
  member_ne_floor (I := bookkeepingInfinitudeFloor) n

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms infinite_complexity_is_infinitude_of_zeros
#print axioms infinitude_forces_infinite_complexity
#print axioms member_cx_lt_top
#print axioms member_cx_ne_floor_cx
#print axioms member_ne_floor
#print axioms member_injective
#print axioms floor_unique_at_top
#print axioms pole_inversion
#print axioms two_pow_valuation
#print axioms infinitudeFloor_forces_infinite
#print axioms no_infinitudeFloor_of_finite
#print axioms infinitudeFloorOfInfinite
#print axioms infinitudeFloor_nonempty_iff_infinite
#print axioms bookkeepingInfinitudeFloor
#print axioms bookkeeping_nonempty
#print axioms bookkeeping_forces_infinite_complexity
#print axioms bookkeeping_members_ne_floor

end PurityCheck
