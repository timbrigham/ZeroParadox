-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the glb, first-step, atom and strong-atomicity hypotheses at ⊥ do not force a binary tree above it; depth at every element with strong atomicity does, one way. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.CellsJoint
import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.Atoms
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Finset.Grade
import Mathlib.Tactic

/-!
# The binary tree above ⊥ of a join-semilattice: not forced by ⊥ as glb of non-⊥ members, a first step, infinitely many atoms and strong atomicity; forced, one way, by depth at every element with strong atomicity

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
`Comb` has ⊥ as the glb of non-⊥ members, a first step, infinitely many atoms and `IsStronglyAtomic`, and no order embedding of `End` or of the binary tree `BTree` (`comb_no_End`, `comb_no_BTree`): these hypotheses at ⊥ do NOT force the tree.
Depth at every element with `IsStronglyAtomic` does, one way (`btree_embeds_of_hereditary_depth`; ZP-A's order, `zp_btree_embeds_of_hereditary_depth`), through the weaker "every element has infinitely many covers" (`btree_embeds_of_covers_infinite`), which `Finset ℕ` meets without depth (`finset_covers_infinite`); `End` embeds the tree and fails depth at its top (`end_top_no_depth`), so sufficient, not necessary. An independent sequence is also sufficient (`btree_embeds_of_independent`), one direction of Chakir–Pouzet, arXiv:0812.2300, Thm 1.4.
Each such hypothesis is explicit on the theorem that uses it, never a class field. Complementary case: Mathlib's Kőnig lemma `exists_seq_covby_of_forall_covby_finite` (`Mathlib/Order/KonigLemma.lean`); topological analogue: `Perfect.exists_nat_bool_injection` (`Mathlib/Topology/MetricSpace/Perfect.lean`).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

/-! ### § 0. The binary tree: `List Bool` under the prefix order, wrapped so `List`'s `≤` stays out. -/

/-- `Statement:` the binary tree, a node a finite `Bool` word. -/
structure BTree where
  val : List Bool

instance : PartialOrder BTree where
  le l l' := List.IsPrefix l.val l'.val
  le_refl l := List.prefix_refl l.val
  le_trans _ _ _ h1 h2 := List.IsPrefix.trans h1 h2
  le_antisymm a b h1 h2 := by
    cases a; cases b
    exact congrArg BTree.mk (h1.eq_of_length (le_antisymm h1.length_le h2.length_le))

/-- `Statement:` `l ≤ l'` in `BTree` iff `l.val` is a prefix of `l'.val`. -/
theorem btree_le_iff (l l' : BTree) : l ≤ l' ↔ List.IsPrefix l.val l'.val := Iff.rfl

/-- `Statement:` `BTree` is infinite. -/
theorem btree_infinite : Infinite BTree :=
  Infinite.of_injective (fun n => BTree.mk (List.replicate n false)) fun a b h => by
    have := congrArg (fun t : BTree => t.val.length) h
    simpa using this

/-- `Statement:` `End` is infinite. -/
theorem end_infinite : Infinite End := Infinite.of_injective unitEnd unitEnd_injective

/-! ### § I. The obstruction: linear up-sets above every non-⊥ point admit no fork. -/

/-- `Statement:` if every non-⊥ point of `P` has a linearly ordered up-set, no order embedding sends
`r`, `x`, `y0`, `y1` with `¬ x ≤ r`, `x ≤ y0`, `x ≤ y1`, `y0`, `y1` incomparable, into `P`. -/
theorem no_embed_of_upchains {α P : Type*} [Preorder α] [PartialOrder P] [OrderBot P]
    (hchain : ∀ z : P, z ≠ ⊥ → ∀ u v, z ≤ u → z ≤ v → u ≤ v ∨ v ≤ u)
    (r x y0 y1 : α) (hxr : ¬ x ≤ r) (h0 : x ≤ y0) (h1 : x ≤ y1)
    (hinc0 : ¬ y0 ≤ y1) (hinc1 : ¬ y1 ≤ y0) (f : α ↪o P) : False := by
  have hx : f x ≠ ⊥ := fun h => by
    have hle : f x ≤ f r := by rw [h]; exact bot_le
    exact hxr (f.le_iff_le.1 hle)
  rcases hchain (f x) hx (f y0) (f y1) (f.le_iff_le.2 h0) (f.le_iff_le.2 h1) with h | h
  · exact hinc0 (f.le_iff_le.1 h)
  · exact hinc1 (f.le_iff_le.1 h)

/-- `Statement:` the end with `1` at positions 0 and 1. -/
def endPair01 : End := fun n => if n = 0 ∨ n = 1 then 1 else 0
/-- `Statement:` the end with `1` at positions 0 and 2. -/
def endPair02 : End := fun n => if n = 0 ∨ n = 2 then 1 else 0

/-- `Statement:` `botEnd < unitEnd 0`, and `endPair01`, `endPair02` lie above `unitEnd 0` and are
incomparable. -/
theorem end_split_witness :
    botEnd ≤ unitEnd 0 ∧ ¬ unitEnd 0 ≤ botEnd ∧ unitEnd 0 ≤ endPair01 ∧ unitEnd 0 ≤ endPair02 ∧
      ¬ endPair01 ≤ endPair02 ∧ ¬ endPair02 ≤ endPair01 := by
  refine ⟨fun n => Fin.zero_le _, fun h => ?_, fun n => ?_, fun n => ?_, fun h => ?_, fun h => ?_⟩
  · exact absurd (h 0) (by decide)
  · by_cases hn : n = 0
    · subst hn; decide
    · rw [unitEnd_ne hn]; exact Fin.zero_le _
  · by_cases hn : n = 0
    · subst hn; decide
    · rw [unitEnd_ne hn]; exact Fin.zero_le _
  · exact absurd (h 1) (by decide)
  · exact absurd (h 2) (by decide)

/-- `Statement:` in `BTree`, `[] < [false]`, and `[false, false]`, `[false, true]` lie above
`[false]` and are incomparable. -/
theorem btree_split_witness :
    BTree.mk [] ≤ BTree.mk [false] ∧ ¬ BTree.mk [false] ≤ BTree.mk [] ∧
      BTree.mk [false] ≤ BTree.mk [false, false] ∧ BTree.mk [false] ≤ BTree.mk [false, true] ∧
      ¬ BTree.mk [false, false] ≤ BTree.mk [false, true] ∧
      ¬ BTree.mk [false, true] ≤ BTree.mk [false, false] := by
  simp only [btree_le_iff]; decide

/-- `Statement:` linear up-sets above every non-⊥ point of `P` give no order embedding `End ↪o P`. -/
theorem no_End_embed_of_upchains {P : Type*} [PartialOrder P] [OrderBot P]
    (hchain : ∀ z : P, z ≠ ⊥ → ∀ u v, z ≤ u → z ≤ v → u ≤ v ∨ v ≤ u) :
    IsEmpty (End ↪o P) := by
  obtain ⟨-, b, c, d, e, g⟩ := end_split_witness
  exact ⟨no_embed_of_upchains hchain _ _ _ _ b c d e g⟩

/-- `Statement:` linear up-sets above every non-⊥ point of `P` give no order embedding `BTree ↪o P`. -/
theorem no_BTree_embed_of_upchains {P : Type*} [PartialOrder P] [OrderBot P]
    (hchain : ∀ z : P, z ≠ ⊥ → ∀ u v, z ≤ u → z ≤ v → u ≤ v ∨ v ≤ u) :
    IsEmpty (BTree ↪o P) := by
  obtain ⟨-, b, c, d, e, g⟩ := btree_split_witness
  exact ⟨no_embed_of_upchains hchain _ _ _ _ b c d e g⟩

/-! ### § II. `Comb`: ⊥, infinitely many atoms `atom k`, and one descending chain `mem n` above them,
`atom k ≥ mem n` for `n ≤ k`. -/

/-- `Statement:` the carrier: ⊥, the atoms `atom k`, the chain members `mem n`. -/
inductive Comb
  | bot
  | atom (k : ℕ)
  | mem (n : ℕ)
  deriving DecidableEq

namespace Comb

/-- `Statement:` the order on `Comb`. -/
def le : Comb → Comb → Prop
  | bot, _ => True
  | atom _, bot => False
  | atom j, atom k => j = k
  | atom k, mem n => n ≤ k
  | mem _, bot => False
  | mem _, atom _ => False
  | mem m, mem n => n ≤ m

/-- `Statement:` the join on `Comb`. -/
def sup : Comb → Comb → Comb
  | bot, y => y
  | atom j, bot => atom j
  | atom j, atom k => if j = k then atom j else mem (min j k)
  | atom j, mem n => mem (min j n)
  | mem m, bot => mem m
  | mem m, atom k => mem (min m k)
  | mem m, mem n => mem (min m n)

instance : SemilatticeSup Comb where
  le := le
  le_refl x := by cases x <;> simp [le]
  le_trans x y z := by
    rcases x with _ | j | m <;> rcases y with _ | k | n <;> rcases z with _ | i | p <;>
      simp [le] <;> omega
  le_antisymm x y := by
    rcases x with _ | j | m <;> rcases y with _ | k | n <;> simp [le] <;> omega
  sup := sup
  le_sup_left x y := by
    rcases x with _ | j | m <;> rcases y with _ | k | n <;> simp only [sup] <;>
      (try split_ifs) <;> simp [le]
  le_sup_right x y := by
    rcases x with _ | j | m <;> rcases y with _ | k | n <;> simp only [sup] <;>
      (try split_ifs) <;> simp [le]
    omega
  sup_le x y z h1 h2 := by
    rcases x with _ | j | m <;> rcases y with _ | k | n <;> rcases z with _ | i | p <;>
      simp only [sup] <;> (try split_ifs) <;> simp only [le] at h1 h2 ⊢ <;> omega

instance : OrderBot Comb where
  bot := bot
  bot_le x := by cases x <;> trivial

/-- `Statement:` `x ≤ y` in `Comb` is `Comb.le x y`. -/
theorem le_def (x y : Comb) : x ≤ y ↔ le x y := Iff.rfl

end Comb

/-- `Statement:` ZP-A's semilattice on `Comb`: join `⊔`, ⊥ of `Comb` the point `Comb.bot`. -/
instance combZPS : ZPSemilattice Comb where
  join := (· ⊔ ·)
  bot := ⊥
  join_assoc := sup_assoc
  join_comm := sup_comm
  join_idem := sup_idem
  bot_join := bot_sup_eq

/-- `Statement:` ZP-A's induced order on `Comb` is the `SemilatticeSup` above. -/
theorem comb_zps_eq : zpSemilatticeSup Comb = (inferInstance : SemilatticeSup Comb) :=
  SemilatticeSup.ext fun x y => by
    show x ⊔ y = y ↔ x ≤ y
    exact sup_eq_right

/-- `Statement:` ZP-A's `≤` on `Comb` is `≤`. -/
theorem comb_zle_iff (x y : Comb) : ZPSemilattice.le x y ↔ x ≤ y := by
  show x ⊔ y = y ↔ x ≤ y
  exact sup_eq_right

/-- `Statement:` every `atom k` covers ⊥ of `Comb`. -/
theorem comb_atom_covBy (k : ℕ) : (⊥ : Comb) ⋖ Comb.atom k := by
  refine ⟨lt_of_le_not_ge bot_le (fun h => h), fun c h1 h2 => ?_⟩
  rcases c with _ | j | m
  · exact h1.ne rfl
  · have := h2.le; simp only [Comb.le_def, Comb.le] at this; subst this; exact h2.ne rfl
  · exact h2.le

/-- `Statement:` ⊥ of `Comb` has a first step in ZP-A's order (`BotHasFirstStep`). -/
theorem comb_botHasFirstStep : BotHasFirstStep Comb := by
  unfold BotHasFirstStep
  rw [comb_zps_eq]
  exact ⟨Comb.atom 0, comb_atom_covBy 0⟩

/-- `Statement:` the `mem n` are non-⊥, strictly descending in ZP-A's order, and ⊥ of `Comb` is their
glb (`branching_forced`'s `hmem` and `hglb`). -/
theorem comb_depth :
    (∀ n, Comb.mem n ≠ ZPSemilattice.bot) ∧
    (∀ n, ZPSemilattice.le (Comb.mem (n + 1)) (Comb.mem n) ∧
      ¬ ZPSemilattice.le (Comb.mem n) (Comb.mem (n + 1))) ∧
    (∀ c : Comb, (∀ n, ZPSemilattice.le c (Comb.mem n)) → c = ZPSemilattice.bot) := by
  refine ⟨fun n h => Comb.noConfusion h, fun n => ?_, fun c hc => ?_⟩
  · simp only [comb_zle_iff, Comb.le_def, Comb.le]; omega
  · rcases c with _ | j | m
    · rfl
    · have := (comb_zle_iff _ _).1 (hc (j + 1)); simp [Comb.le_def, Comb.le] at this
    · have := (comb_zle_iff _ _).1 (hc (m + 1)); simp [Comb.le_def, Comb.le] at this

/-- `Statement:` `x < y` in `Comb` is `Comb.le x y ∧ ¬ Comb.le y x`. -/
theorem comb_lt_iff (x y : Comb) : x < y ↔ Comb.le x y ∧ ¬ Comb.le y x := lt_iff_le_not_ge

/-- `Statement:` `Comb` is strongly atomic (Mathlib's `IsStronglyAtomic`). -/
instance comb_stronglyAtomic : IsStronglyAtomic Comb where
  exists_covBy_le_of_lt a b hab := by
    rw [comb_lt_iff] at hab
    match a, b, hab with
    | .bot, .bot, h => exact absurd trivial h.2
    | .bot, .atom k, _ => exact ⟨Comb.atom k, comb_atom_covBy k, le_rfl⟩
    | .bot, .mem n, _ => exact ⟨Comb.atom n, comb_atom_covBy n, show n ≤ n from le_rfl⟩
    | .atom j, .bot, h => exact absurd h.1 id
    | .atom j, .atom k, h => exact absurd h.1.symm h.2
    | .atom j, .mem n, h =>
      refine ⟨Comb.mem j, ⟨(comb_lt_iff _ _).2 ⟨show j ≤ j from le_rfl, id⟩, fun c h1 h2 => ?_⟩,
        show n ≤ j from h.1⟩
      rw [comb_lt_iff] at h1 h2
      rcases c with _ | i | p
      · exact h1.1
      · simp only [Comb.le] at h1; exact h1.2 h1.1.symm
      · simp only [Comb.le] at h1 h2; omega
    | .mem m, .bot, h => exact absurd h.1 id
    | .mem m, .atom k, h => exact absurd h.1 id
    | .mem m, .mem n, h =>
      simp only [Comb.le] at h
      refine ⟨Comb.mem (m - 1), ⟨(comb_lt_iff _ _).2 ⟨show m - 1 ≤ m by omega,
        show ¬ (m ≤ m - 1) by omega⟩, fun c h1 h2 => ?_⟩, show n ≤ m - 1 by omega⟩
      rw [comb_lt_iff] at h1 h2
      rcases c with _ | i | p
      · exact h1.1
      · exact h1.1
      · simp only [Comb.le] at h1 h2; omega

/-- `Statement:` every non-⊥ point of `Comb` has a linearly ordered up-set, so `Comb` minus ⊥ is the
dual of an ordered forest (terminology of Laflamme–Pouzet–Sauer, arXiv:1508.01123v2 § 2). -/
theorem comb_upchains : ∀ z : Comb, z ≠ ⊥ → ∀ u v, z ≤ u → z ≤ v → u ≤ v ∨ v ≤ u := by
  intro z hz u v hu hv
  rcases z with _ | j | m
  · exact absurd rfl hz
  all_goals rcases u with _ | k | n <;> rcases v with _ | i | p <;>
    simp [Comb.le_def, Comb.le] at hu hv ⊢ <;> omega

/-- `Statement:` no order embedding `End ↪o Comb`. -/
theorem comb_no_End : IsEmpty (End ↪o Comb) := no_End_embed_of_upchains comb_upchains

/-- `Statement:` no order embedding `BTree ↪o Comb`. -/
theorem comb_no_BTree : IsEmpty (BTree ↪o Comb) := no_BTree_embed_of_upchains comb_upchains

/-- `Statement:` ⊥ of `Comb` has infinitely many covers. -/
theorem comb_atoms_infinite : {a : Comb | ⊥ ⋖ a}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := Comb.atom) (fun _ _ h => by cases h; rfl) comb_atom_covBy

/-- `Statement:` complexity on `Comb`: ⊤ of `ℕ∞` at ⊥, `0` at atoms, `n` at `mem n`. -/
def combCx : Comb → ℕ∞
  | .bot => ⊤
  | .atom _ => 0
  | .mem n => n

/-- `Statement:` the `InfinitudeFloor Comb`: floor ⊥ of `Comb`, members `mem n`, complexity `combCx`. -/
@[reducible] def combFloor : InfinitudeFloor Comb where
  floor := ⊥
  cx := combCx
  member := Comb.mem
  cx_member_strictMono := fun a b h => by simp only [combCx]; exact_mod_cast h
  cx_floor_eq_iSup := by
    show (⊤ : ℕ∞) = ⨆ n : ℕ, ((n : ℕ) : ℕ∞)
    exact iSup_natCast_eq_top_enat.symm

/-! ### § III. What the depth hypothesis does force: infinitely many atoms. -/

/-- `Statement:` if ⊥ is the glb of an antitone `m` and below every `m n` sits an atom, the atoms are
infinite. -/
theorem atoms_infinite_of_depth {P : Type*} [PartialOrder P] [OrderBot P]
    (m : ℕ → P) (hm : Antitone m) (hglb : ∀ c, (∀ n, c ≤ m n) → c = ⊥)
    (hat : ∀ n, ∃ a, ⊥ ⋖ a ∧ a ≤ m n) : {a : P | ⊥ ⋖ a}.Infinite := by
  intro hfin
  have hex : ∀ a ∈ {a : P | ⊥ ⋖ a}, ∃ n, ¬ a ≤ m n := fun a ha => by
    by_contra h
    simp only [not_exists, not_not] at h
    exact ha.1.ne' (hglb a h)
  choose! g hg using hex
  obtain ⟨N, hN⟩ := (hfin.image g).bddAbove
  obtain ⟨b, hb, hbm⟩ := hat N
  exact hg b hb (hbm.trans (hm (hN ⟨b, hb, rfl⟩)))

/-! ### § IV. Controls on the depth reading of `branching_forced`'s `hglb`. -/

section Diamond

/-- `Statement:` ZP-A's semilattice on `Bool × Bool` under `⊔`. -/
abbrev diamondZPS : ZPSemilattice (Bool × Bool) where
  join := (· ⊔ ·)
  bot := ⊥
  join_assoc := sup_assoc
  join_comm := sup_comm
  join_idem := sup_idem
  bot_join := bot_sup_eq

attribute [local instance] diamondZPS

/-- `Statement:` members alternating `(true, false)` and `(false, true)`. -/
def diamondMember (n : ℕ) : Bool × Bool := if n % 2 = 0 then (true, false) else (false, true)

/-- `Statement:` CONTROL, finite `Bool × Bool` meets `hmem`, `hglb` and `BotHasFirstStep`, and admits
no order embedding of `End` or `BTree`. `Reading:` `branching_forced`'s `hglb` is "⊥ is the glb of
non-⊥ members", not depth: depth is sufficient for it (`end_glb_unitEnd`), not required. -/
theorem diamond_meets_hglb :
    (∀ n, diamondMember n ≠ ZPSemilattice.bot) ∧
    (∀ c : Bool × Bool, (∀ n, ZPSemilattice.le c (diamondMember n)) → c = ZPSemilattice.bot) ∧
    BotHasFirstStep (Bool × Bool) ∧ Finite (Bool × Bool) ∧
    IsEmpty (End ↪o Bool × Bool) ∧ IsEmpty (BTree ↪o Bool × Bool) := by
  refine ⟨fun n => ?_, fun c hc => ?_, ⟨(true, false), ?_, fun c h1 h2 => ?_⟩, inferInstance,
    ⟨fun f => ?_⟩, ⟨fun f => ?_⟩⟩
  · unfold diamondMember; split_ifs <;> decide
  · have h0 : c ⊔ (true, false) = (true, false) := hc 0
    have h1 : c ⊔ (false, true) = (false, true) := hc 1
    clear hc
    revert h0 h1; revert c; decide
  · exact ⟨(show (⊥ : Bool × Bool) ⊔ (true, false) = (true, false) by decide),
      show ¬ ((true, false) ⊔ (⊥ : Bool × Bool) = ⊥) by decide⟩
  · have e1 : (⊥ : Bool × Bool) ⊔ c = c := h1.1
    have e1' : ¬ (c ⊔ (⊥ : Bool × Bool) = ⊥) := h1.2
    have e2 : c ⊔ (true, false) = (true, false) := h2.1
    have e2' : ¬ ((true, false) ⊔ c = c) := h2.2
    clear h1 h2
    revert e1 e1' e2 e2'; revert c; decide
  · have := end_infinite
    have := Finite.of_injective f f.injective
    exact not_finite End
  · have := btree_infinite
    have := Finite.of_injective f f.injective
    exact not_finite BTree

end Diamond

/-- `Statement:` CONTROL, no order embedding `End ↪o ℕ × ℕ` (`WellQuasiOrderedLE`: no infinite
antichain). -/
theorem natSq_no_End : IsEmpty (End ↪o ℕ × ℕ) := by
  refine ⟨fun f => ?_⟩
  have hanti : IsAntichain (· ≤ ·) (Set.range (f ∘ unitEnd)) := by
    rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hne hle
    have hjk : j ≠ k := fun h => hne (by rw [h])
    exact unitEnd_incomparable hjk ((endZle_iff_le _ _).2 (f.le_iff_le.1 hle))
  have hinf : (Set.range (f ∘ unitEnd)).Infinite :=
    Set.infinite_range_of_injective (f.injective.comp unitEnd_injective)
  exact hinf (WellQuasiOrderedLE.finite_of_isAntichain hanti)

/-- `Statement:` every `x : ℕ × ℕ` has two incomparable covers whose common lower bounds are below
`x`. `Reading:` with `natSq_no_End`, a fork at every point does not give `End`. -/
theorem natSq_hereditary (x : ℕ × ℕ) :
    x ⋖ (x.1 + 1, x.2) ∧ x ⋖ (x.1, x.2 + 1) ∧
    ¬ ((x.1 + 1, x.2) ≤ (x.1, x.2 + 1)) ∧ ¬ ((x.1, x.2 + 1) ≤ (x.1 + 1, x.2)) ∧
    (∀ c, c ≤ (x.1 + 1, x.2) → c ≤ (x.1, x.2 + 1) → c ≤ x) := by
  obtain ⟨a, b⟩ := x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Prod.lt_iff.2 (Or.inl ⟨by simp, le_rfl⟩), fun c h1 h2 => ?_⟩
    obtain ⟨p, q⟩ := c
    rw [Prod.lt_iff] at h1 h2; simp at h1 h2; omega
  · refine ⟨Prod.lt_iff.2 (Or.inr ⟨le_rfl, by simp⟩), fun c h1 h2 => ?_⟩
    obtain ⟨p, q⟩ := c
    rw [Prod.lt_iff] at h1 h2; simp at h1 h2; omega
  · simp [Prod.le_def]
  · simp [Prod.le_def]
  · rintro ⟨p, q⟩ h1 h2; simp [Prod.le_def] at *; omega

/-! ### § V. A sufficient hypothesis, one way: an independent sequence. -/

/-- `Statement:` the nonempty prefixes of `l`. -/
def prefixCodes (l : List Bool) : Finset (List Bool) := (l.inits.toFinset).erase []

/-- `Statement:` `prefixCodes l ⊆ prefixCodes l'` iff `l` is a prefix of `l'`; both directions. -/
theorem prefixCodes_subset_iff (l l' : List Bool) :
    prefixCodes l ⊆ prefixCodes l' ↔ List.IsPrefix l l' := by
  constructor
  · intro h
    by_cases hl : l = []
    · subst hl; exact List.nil_prefix
    · have : l ∈ prefixCodes l := Finset.mem_erase.2 ⟨hl, List.mem_toFinset.2 ((List.mem_inits _ _).2
        (List.prefix_refl l))⟩
      have := Finset.mem_erase.1 (h this)
      exact (List.mem_inits _ _).1 (List.mem_toFinset.1 this.2)
  · intro h s hs
    obtain ⟨hs0, hs1⟩ := Finset.mem_erase.1 hs
    exact Finset.mem_erase.2 ⟨hs0, List.mem_toFinset.2 ((List.mem_inits _ _).2
      (((List.mem_inits _ _).1 (List.mem_toFinset.1 hs1)).trans h))⟩

/-- `Statement:` `prefixCodes [] = ∅`. -/
theorem prefixCodes_nil : prefixCodes [] = ∅ := by decide

/-- `Statement:` if `a : ℕ → L` is independent (`S.sup a ≤ T.sup a ↔ S ⊆ T` for finite `S`, `T`),
`BTree` order-embeds in `L` with root at ⊥ of `L`; one way. This is the (i)⇒(iii) direction of
Chakir–Pouzet, arXiv:0812.2300, Thm 1.4 (an independent set of size ω gives a copy of the finite subsets
of ω; credited there to Chakir–Pouzet, Algebra Universalis 53(2) (2005) 211–225, and Lawson–Mislove–
Priestley, Discrete Math. 63 (1987) 225–230), composed with the prefix-code embedding of `BTree`. -/
theorem btree_embeds_of_independent {L : Type*} [SemilatticeSup L] [OrderBot L] (a : ℕ → L)
    (ha : ∀ S T : Finset ℕ, S.sup a ≤ T.sup a ↔ S ⊆ T) :
    ∃ f : BTree ↪o L, f (BTree.mk []) = ⊥ := by
  let F : BTree → L := fun l => ((prefixCodes l.val).image Encodable.encode).sup a
  have hF : ∀ l l' : BTree, F l ≤ F l' ↔ l ≤ l' := fun l l' => by
    simp only [F, ha, Finset.image_subset_image_iff Encodable.encode_injective, btree_le_iff]
    exact prefixCodes_subset_iff _ _
  refine ⟨OrderEmbedding.ofMapLEIff F hF, ?_⟩
  show F (BTree.mk []) = ⊥
  simp only [F, prefixCodes_nil, Finset.image_empty, Finset.sup_empty]

/-- `Statement:` `(S.sup unitEnd) n` is `1` if `n ∈ S`, else `0`. -/
theorem sup_unitEnd_apply (S : Finset ℕ) (n : ℕ) : S.sup unitEnd n = if n ∈ S then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty => simp; rfl
  | insert k S hk ih =>
    simp only [Finset.sup_insert, Pi.sup_apply, ih, Finset.mem_insert]
    by_cases h1 : n = k
    · subst h1
      have h2 : ∀ b : Fin 2, (1 : Fin 2) ⊔ b = 1 := by decide
      simpa [unitEnd_self] using h2 (if n ∈ S then 1 else 0)
    · rw [unitEnd_ne h1]; simp [h1]

/-- `Statement:` the unit vectors `unitEnd` are independent in `End`; both directions. -/
theorem unitEnd_independent (S T : Finset ℕ) : S.sup unitEnd ≤ T.sup unitEnd ↔ S ⊆ T := by
  constructor
  · intro h k hk
    have := h k
    rw [sup_unitEnd_apply, sup_unitEnd_apply] at this
    by_contra hkT
    simp [hk, hkT] at this
  · intro h n
    rw [sup_unitEnd_apply, sup_unitEnd_apply]
    by_cases hn : n ∈ S
    · simp [hn, h hn]
    · simp only [hn, ite_false]; exact Fin.zero_le _

/-- `Statement:` `BTree` order-embeds in `End` with root at `botEnd`. -/
theorem btree_embeds_End : ∃ f : BTree ↪o End, f (BTree.mk []) = botEnd := by
  obtain ⟨f, hf⟩ := btree_embeds_of_independent unitEnd unitEnd_independent
  exact ⟨f, hf.trans rfl⟩

/-! ### § VI. A sufficient hypothesis, one way: depth at every element, with `IsStronglyAtomic`. -/

/-- `Statement:` if `x` is the glb of an antitone sequence strictly above it, and the order is
strongly atomic, then `x` has infinitely many covers. -/
theorem covers_infinite_of_depth {P : Type*} [PartialOrder P] [IsStronglyAtomic P] (x : P)
    (m : ℕ → P) (hm : Antitone m) (habove : ∀ n, x < m n) (hglb : ∀ c, (∀ n, c ≤ m n) → c ≤ x) :
    {c : P | x ⋖ c}.Infinite := by
  intro hfin
  have hex : ∀ a ∈ {c : P | x ⋖ c}, ∃ n, ¬ a ≤ m n := fun a ha => by
    by_contra h
    simp only [not_exists, not_not] at h
    exact (ha.lt.not_ge) (hglb a h)
  choose! g hg using hex
  obtain ⟨N, hN⟩ := (hfin.image g).bddAbove
  obtain ⟨b, hb, hbm⟩ := exists_covBy_le_of_lt (habove N)
  exact hg b hb (hbm.trans (hm (hN ⟨b, hb, rfl⟩)))

/-- `Statement:` in a join-semilattice, a cover `c` of `p` lying above some `f ≰ p` is `p ⊔ f`. -/
theorem covBy_eq_sup_of_le {P : Type*} [SemilatticeSup P] {p c f : P} (hc : p ⋖ c)
    (hf : ¬ f ≤ p) (hfc : f ≤ c) : c = p ⊔ f := by
  have h1 : p ⊔ f ≤ c := sup_le hc.le hfc
  have h2 : p < p ⊔ f := lt_of_le_of_ne le_sup_left (fun h => hf (h ▸ le_sup_right))
  rcases hc.eq_or_eq h2.le h1 with h | h
  · exact absurd h h2.ne'
  · exact h.symm

/-- `Statement:` two distinct covers of `p` are incomparable. -/
theorem covBy_not_le_of_ne {P : Type*} [PartialOrder P] {p c d : P} (hc : p ⋖ c) (hd : p ⋖ d)
    (hne : c ≠ d) : ¬ c ≤ d := fun h => by
  rcases hd.eq_or_eq hc.le h with e | e
  · exact hc.lt.ne' e
  · exact hne e

/-- `Statement:` if `p` has infinitely many covers, then for every finite `F` there are two distinct
covers of `p`, neither equal to any `p ⊔ f`, `f ∈ F`. -/
theorem exists_two_covers {P : Type*} [SemilatticeSup P] (p : P)
    (hinf : {c : P | p ⋖ c}.Infinite) (F : Finset P) : ∃ c0 c1 : P, p ⋖ c0 ∧ p ⋖ c1 ∧ c0 ≠ c1 ∧
      (∀ f ∈ F, c0 ≠ p ⊔ f) ∧ (∀ f ∈ F, c1 ≠ p ⊔ f) := by
  classical
  have hS : ({c : P | p ⋖ c} \ ((F.image (p ⊔ ·) : Finset P) : Set P)).Infinite :=
    hinf.sdiff (Finset.finite_toSet _)
  obtain ⟨a, ha, b, hb, hab⟩ := hS.nontrivial
  refine ⟨a, b, ha.1, hb.1, hab, fun f hf e => ha.2 ?_, fun f hf e => hb.2 ?_⟩
  · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨f, hf, e.symm⟩)
  · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨f, hf, e.symm⟩)

section Build
variable {P : Type*} [SemilatticeSup P] [DecidableEq P] (c0 c1 : P → Finset P → P)

/-- `Statement:` one step: go to a chosen cover, and forbid the sibling for the rest of the subtree. -/
def treeStep (s : P × Finset P) (b : Bool) : P × Finset P :=
  if b then (c1 s.1 s.2, insert (c0 s.1 s.2) s.2) else (c0 s.1 s.2, insert (c1 s.1 s.2) s.2)

/-- `Statement:` the node reached from state `s` along the path `l`, read from the root. -/
def treeGo (s : P × Finset P) (l : List Bool) : P × Finset P := l.foldl (treeStep c0 c1) s

/-- `Statement:` the invariant: nothing forbidden lies below the current element. -/
def TreeInv (s : P × Finset P) : Prop := ∀ f ∈ s.2, ¬ f ≤ s.1

variable {c0 c1}
variable (hc : ∀ p F, p ⋖ c0 p F ∧ p ⋖ c1 p F ∧ c0 p F ≠ c1 p F ∧
  (∀ f ∈ F, c0 p F ≠ p ⊔ f) ∧ (∀ f ∈ F, c1 p F ≠ p ⊔ f))
include hc

/-- `Statement:` a step goes strictly up. -/
theorem treeStep_lt (s : P × Finset P) (b : Bool) : s.1 < (treeStep c0 c1 s b).1 := by
  cases b
  · exact (hc s.1 s.2).1.lt
  · exact (hc s.1 s.2).2.1.lt

/-- `Statement:` a step keeps `TreeInv`. -/
theorem treeStep_inv (s : P × Finset P) (hs : TreeInv s) (b : Bool) :
    TreeInv (treeStep c0 c1 s b) := by
  obtain ⟨h0, h1, hne, hF0, hF1⟩ := hc s.1 s.2
  have key : ∀ c, s.1 ⋖ c → (∀ f ∈ s.2, c ≠ s.1 ⊔ f) → ∀ f ∈ s.2, ¬ f ≤ c :=
    fun c hcv hF f hf hfc => hF f hf (covBy_eq_sup_of_le hcv (hs f hf) hfc)
  cases b
  · intro f hf
    rcases Finset.mem_insert.1 hf with rfl | hf
    · exact covBy_not_le_of_ne h1 h0 hne.symm
    · exact key _ h0 hF0 f hf
  · intro f hf
    rcases Finset.mem_insert.1 hf with rfl | hf
    · exact covBy_not_le_of_ne h0 h1 hne
    · exact key _ h1 hF1 f hf

omit hc [SemilatticeSup P] in
/-- `Statement:` a step only adds forbidden elements. -/
theorem treeStep_sub (s : P × Finset P) (b : Bool) : s.2 ⊆ (treeStep c0 c1 s b).2 := by
  cases b <;> exact Finset.subset_insert _ _

omit hc [SemilatticeSup P] in
/-- `Statement:` `treeGo` on `b :: l` is `treeGo` on `l` after one step. -/
theorem treeGo_cons (s : P × Finset P) (b : Bool) (l : List Bool) :
    treeGo c0 c1 s (b :: l) = treeGo c0 c1 (treeStep c0 c1 s b) l := rfl

/-- `Statement:` `treeGo` goes up. -/
theorem treeGo_le (s : P × Finset P) (l : List Bool) : s.1 ≤ (treeGo c0 c1 s l).1 := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons b l ih => rw [treeGo_cons]; exact (treeStep_lt hc s b).le.trans (ih _)

/-- `Statement:` along any path from a state meeting `TreeInv`, its forbidden elements stay
non-below. -/
theorem treeGo_avoids (s : P × Finset P) (hs : TreeInv s) (l : List Bool) :
    ∀ f ∈ s.2, ¬ f ≤ (treeGo c0 c1 s l).1 := by
  induction l generalizing s with
  | nil => exact hs
  | cons b l ih =>
    intro f hf
    rw [treeGo_cons]
    exact ih _ (treeStep_inv hc s hs b) f (treeStep_sub s b hf)

/-- `Statement:` `treeGo` is monotone in the prefix order. -/
theorem treeGo_mono (s : P × Finset P) (l l' : List Bool) (h : l <+: l') :
    (treeGo c0 c1 s l).1 ≤ (treeGo c0 c1 s l').1 := by
  obtain ⟨t, rfl⟩ := h
  simp only [treeGo, List.foldl_append]
  exact treeGo_le hc _ t

/-- `Statement:` from a state meeting `TreeInv`, `treeGo` reflects the order onto the prefix order. -/
theorem treeGo_reflect (s : P × Finset P) (hs : TreeInv s) (l l' : List Bool)
    (h : (treeGo c0 c1 s l).1 ≤ (treeGo c0 c1 s l').1) : l <+: l' := by
  induction l generalizing s l' with
  | nil => exact List.nil_prefix
  | cons b u ih =>
    cases l' with
    | nil =>
      exfalso
      have h1 : (treeGo c0 c1 s []).1 < (treeGo c0 c1 s (b :: u)).1 :=
        (treeStep_lt hc s b).trans_le (treeGo_le hc _ u)
      exact h1.not_ge h
    | cons b' v =>
      by_cases hb : b = b'
      · subst hb
        exact List.cons_prefix_cons.2 ⟨rfl, ih _ (treeStep_inv hc s hs b) v h⟩
      · exfalso
        have hsib : (treeStep c0 c1 s b).1 ∈ (treeStep c0 c1 s b').2 := by
          cases b <;> cases b' <;> simp_all [treeStep]
        have hle : (treeStep c0 c1 s b).1 ≤ (treeGo c0 c1 s (b' :: v)).1 :=
          (treeGo_le hc _ u).trans h
        exact treeGo_avoids hc _ (treeStep_inv hc s hs b') v _ hsib hle

end Build

/-- `Statement:` in a join-semilattice with ⊥ where every element has infinitely many covers,
`BTree` order-embeds with root at ⊥; one way. -/
theorem btree_embeds_of_covers_infinite {P : Type*} [SemilatticeSup P] [OrderBot P]
    (hinf : ∀ x : P, {c : P | x ⋖ c}.Infinite) : ∃ f : BTree ↪o P, f (BTree.mk []) = ⊥ := by
  classical
  have hpick : ∀ (p : P) (F : Finset P), ∃ c : P × P, p ⋖ c.1 ∧ p ⋖ c.2 ∧ c.1 ≠ c.2 ∧
      (∀ f ∈ F, c.1 ≠ p ⊔ f) ∧ (∀ f ∈ F, c.2 ≠ p ⊔ f) := fun p F => by
    obtain ⟨a, b, h⟩ := exists_two_covers p (hinf p) F
    exact ⟨(a, b), h⟩
  choose c hc using hpick
  let c0 : P → Finset P → P := fun p F => (c p F).1
  let c1 : P → Finset P → P := fun p F => (c p F).2
  have hc' : ∀ p F, p ⋖ c0 p F ∧ p ⋖ c1 p F ∧ c0 p F ≠ c1 p F ∧
      (∀ f ∈ F, c0 p F ≠ p ⊔ f) ∧ (∀ f ∈ F, c1 p F ≠ p ⊔ f) := hc
  have hinv : TreeInv ((⊥ : P), (∅ : Finset P)) := fun f hf => absurd hf (Finset.notMem_empty f)
  let F : BTree → P := fun l => (treeGo c0 c1 (⊥, ∅) l.val).1
  have hF : ∀ l l' : BTree, F l ≤ F l' ↔ l ≤ l' := fun l l' =>
    ⟨fun h => treeGo_reflect hc' _ hinv _ _ h, fun h => treeGo_mono hc' _ _ _ h⟩
  exact ⟨OrderEmbedding.ofMapLEIff F hF, rfl⟩

/-- `Statement:` if every element is the glb of a strictly descending sequence strictly above it
(`hdepth`) and the order is strongly atomic, `BTree` order-embeds with root at ⊥; one way. -/
theorem btree_embeds_of_hereditary_depth {P : Type*} [SemilatticeSup P] [OrderBot P]
    [IsStronglyAtomic P]
    (hdepth : ∀ x : P, ∃ m : ℕ → P, StrictAnti m ∧ (∀ n, x < m n) ∧ IsGLB (Set.range m) x) :
    ∃ f : BTree ↪o P, f (BTree.mk []) = ⊥ := by
  refine btree_embeds_of_covers_infinite fun x => ?_
  obtain ⟨m, hm, habove, hglb⟩ := hdepth x
  exact covers_infinite_of_depth x m hm.antitone habove fun c hc =>
    hglb.2 (by rintro _ ⟨n, rfl⟩; exact hc n)

/-- `Statement:` the same in ZP-A's induced order on a `ZPSemilattice`, root at ⊥ of `L`; one way.
`Reading:` depth at every point forces forks everywhere; depth only at ⊥ does not (`comb_no_End`). -/
theorem zp_btree_embeds_of_hereditary_depth {L : Type*} [ZPSemilattice L]
    (hatom : @IsStronglyAtomic L (zpSemilatticeSup L).toPreorder)
    (hdepth : ∀ x : L, ∃ m : ℕ → L, @StrictAnti ℕ L _ (zpSemilatticeSup L).toPreorder m ∧
      (∀ n, (zpSemilatticeSup L).lt x (m n)) ∧
      @IsGLB L (zpSemilatticeSup L).toPreorder.toLE (Set.range m) x) :
    ∃ f : @OrderEmbedding BTree L _ (zpSemilatticeSup L).toPreorder.toLE,
      f (BTree.mk []) = ZPSemilattice.bot := by
  let _ := zpSemilatticeSup L
  let _ := zpOrderBot L
  have _ := hatom
  exact btree_embeds_of_hereditary_depth hdepth

/-! ### § VII. Controls on § VI. -/

-- Statement: CONTROL, `hinf` is not vacuous: on `ℕ`, `0` has finitely many covers.
example : ¬ ({c : ℕ | 0 ⋖ c}.Infinite) := by
  intro h
  apply h
  apply Set.Finite.subset (Set.finite_singleton 1)
  intro c hc
  simp only [Set.mem_ofPred_eq, Nat.covBy_iff_add_one_eq] at hc
  simp [← hc]

/-- `Statement:` every `s : Finset ℕ` has infinitely many covers (`insert n s`, `n ∉ s`). -/
theorem finset_covers_infinite (s : Finset ℕ) : {t : Finset ℕ | s ⋖ t}.Infinite := by
  have hc : ((s : Set ℕ)ᶜ).Infinite := s.finite_toSet.infinite_compl
  refine Set.infinite_of_injOn_mapsTo (f := fun n => insert n s) ?_ ?_ hc
  · intro a ha b _ h
    have h' : insert a s = insert b s := h
    have : a ∈ insert b s := h' ▸ Finset.mem_insert_self a s
    rcases Finset.mem_insert.1 this with e | e
    · exact e
    · exact absurd e ha
  · intro n hn; exact Finset.covBy_insert hn

-- Statement: CONTROL, `btree_embeds_of_covers_infinite` applies to `Finset ℕ`, which has no
-- strictly descending sequence (`no_strictAnti_of_wf` below): covers suffice without depth.
example : ∃ f : BTree ↪o Finset ℕ, f (BTree.mk []) = ⊥ :=
  btree_embeds_of_covers_infinite finset_covers_infinite

/-- `Statement:` the five-point order: ⊥, `a`, `b` above it, `c`, `d` above both. -/
inductive Bowtie | bot | a | b | c | d deriving DecidableEq

namespace Bowtie

/-- `Statement:` the order on `Bowtie`, as a `Bool`. -/
def le : Bowtie → Bowtie → Bool
  | bot, _ => true
  | a, a | a, c | a, d => true
  | b, b | b, c | b, d => true
  | c, c => true
  | d, d => true
  | _, _ => false

instance : PartialOrder Bowtie where
  le x y := le x y = true
  le_refl x := by cases x <;> rfl
  le_trans x y z := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm x y := by cases x <;> cases y <;> decide

instance : DecidableRel (α := Bowtie) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (le x y = true))
instance : DecidableRel (α := Bowtie) (· < ·) := fun x y =>
  inferInstanceAs (Decidable (le x y = true ∧ ¬ le y x = true))

/-- `Statement:` `x ⋖ y` in `Bowtie` unfolded with `<`. -/
theorem cov_iff (x y : Bowtie) : x ⋖ y ↔ x < y ∧ ∀ z, x < z → ¬ z < y := by
  constructor
  · exact fun h => ⟨h.1, fun z h1 h2 => h.2 h1 h2⟩
  · exact fun h => ⟨h.1, fun {z} h1 h2 => h.2 z h1 h2⟩

/-- `Statement:` CONTROL for `covBy_eq_sup_of_le`, which needs joins: `Bowtie` (no join of `a`, `b`)
has `b ⋖ c`, `b ⋖ d`, `c ≠ d`, `a ≰ b`, and `a` below both covers of `b`. -/
theorem two_killed : b ⋖ c ∧ b ⋖ d ∧ c ≠ d ∧ ¬ a ≤ b ∧ a ≤ c ∧ a ≤ d := by
  refine ⟨(cov_iff _ _).2 ⟨by decide, fun z => by cases z <;> decide⟩,
    (cov_iff _ _).2 ⟨by decide, fun z => by cases z <;> decide⟩, by decide, by decide, by decide,
    by decide⟩

end Bowtie

/-- `Statement:` CONTROL, a well-founded order carries no strictly descending sequence, so `hdepth`
fails in every one. -/
theorem no_strictAnti_of_wf {P : Type*} [Preorder P] [WellFoundedLT P] (m : ℕ → P)
    (hm : StrictAnti m) : False := by
  obtain ⟨_, ⟨n, rfl⟩, hmin⟩ := (wellFounded_lt (α := P)).has_min (Set.range m) ⟨m 0, 0, rfl⟩
  exact hmin _ ⟨n + 1, rfl⟩ (hm (Nat.lt_succ_self n))

-- Statement: no strictly descending sequence in `ℕ × ℕ`.
example : ¬ ∃ m : ℕ → ℕ × ℕ, StrictAnti m := fun ⟨m, hm⟩ => no_strictAnti_of_wf m hm
-- Statement: none in `Bool × Bool`.
example : ¬ ∃ m : ℕ → Bool × Bool, StrictAnti m := fun ⟨m, hm⟩ => no_strictAnti_of_wf m hm
-- Statement: none in `Finset ℕ`.
example : ¬ ∃ m : ℕ → Finset ℕ, StrictAnti m := fun ⟨m, hm⟩ => no_strictAnti_of_wf m hm

/-- `Statement:` CONTROL, nothing lies strictly above ⊤ of `End`, so `hdepth` fails there, while
`BTree` embeds in `End` (`btree_embeds_End`). -/
theorem end_top_no_depth : ¬ ∃ m : ℕ → End, ∀ n, (⊤ : End) < m n :=
  fun ⟨_, h⟩ => not_top_lt (h 0)

namespace Comb

/-- `Statement:` `n ↦ mem n` is strictly antitone. -/
theorem mem_strictAnti : StrictAnti Comb.mem := fun a b h =>
  (comb_lt_iff _ _).2 ⟨show a ≤ b by omega, show ¬ b ≤ a by omega⟩

/-- `Statement:` ⊥ of `Comb` is the only lower bound of all `mem n`. -/
theorem glb_mem (c : Comb) (hc : ∀ n, c ≤ Comb.mem n) : c = ⊥ := by
  rcases c with _ | j | m
  · rfl
  · have := hc (j + 1); simp [Comb.le_def, Comb.le] at this
  · have := hc (m + 1); simp [Comb.le_def, Comb.le] at this

/-- `Statement:` CONTROL, `hdepth` fails at `atom 0`: only `mem 0` lies strictly above it, so no
strictly descending sequence does. -/
theorem atom0_no_depth : ¬ ∃ m : ℕ → Comb, StrictAnti m ∧ ∀ n, Comb.atom 0 < m n := by
  rintro ⟨m, hm, h⟩
  have key : ∀ c, Comb.atom 0 < c → c = Comb.mem 0 := fun c hc => by
    rw [comb_lt_iff] at hc
    rcases c with _ | j | p
    · exact absurd hc.1 id
    · exact absurd hc.1.symm hc.2
    · have hp : p ≤ 0 := hc.1
      rw [show p = 0 by omega]
  exact (hm (Nat.zero_lt_one)).ne ((key _ (h 1)).trans (key _ (h 0)).symm)

end Comb

/-- `Statement:` the finitely supported sequences of `Comb`, pointwise order. -/
def FinComb : Set (ℕ → Comb) := {f | ∃ N, ∀ i, N ≤ i → f i = ⊥}

/-- `Statement:` `FinComb` is closed under `⊔`. -/
theorem finComb_sup (f g : ℕ → Comb) (hf : f ∈ FinComb) (hg : g ∈ FinComb) : f ⊔ g ∈ FinComb := by
  obtain ⟨N, hN⟩ := hf
  obtain ⟨M, hM⟩ := hg
  exact ⟨max N M, fun i hi => by
    simp only [Pi.sup_apply, hN i (le_of_max_le_left hi), hM i (le_of_max_le_right hi), sup_idem]⟩

instance : SemilatticeSup FinComb := Subtype.semilatticeSup finComb_sup
instance : OrderBot FinComb := Subtype.orderBot ⟨0, fun _ _ => rfl⟩

/-- `Statement:` updating one coordinate of a member of `FinComb` stays in `FinComb`. -/
theorem finComb_update (x : FinComb) (j : ℕ) (d : Comb) :
    Function.update x.1 j d ∈ FinComb := by
  obtain ⟨N, hN⟩ := x.2
  refine ⟨max N (j + 1), fun i hi => ?_⟩
  rw [Function.update_of_ne (by omega)]
  exact hN i (le_of_max_le_left hi)

/-- `Statement:` the order on `FinComb` is pointwise. -/
theorem finComb_le_iff (x y : FinComb) : x ≤ y ↔ ∀ i, x.1 i ≤ y.1 i := Iff.rfl

/-- `Statement:` `FinComb` is strongly atomic: raise one coordinate by a cover. -/
instance finComb_stronglyAtomic : IsStronglyAtomic FinComb where
  exists_covBy_le_of_lt a b hab := by
    classical
    have hle : ∀ i, a.1 i ≤ b.1 i := (finComb_le_iff _ _).1 hab.le
    obtain ⟨j, hj⟩ : ∃ j, ¬ b.1 j ≤ a.1 j := by
      by_contra h
      push Not at h
      exact hab.not_ge ((finComb_le_iff _ _).2 h)
    obtain ⟨d, hd, hdb⟩ := exists_covBy_le_of_lt (lt_of_le_not_ge (hle j) hj)
    let c : FinComb := ⟨Function.update a.1 j d, finComb_update a j d⟩
    have hac : a ≤ c := (finComb_le_iff _ _).2 fun i => by
      by_cases hi : i = j
      · subst hi; simp [c, hd.le]
      · simp [c, Function.update_of_ne hi]
    have hca : ¬ c ≤ a := fun h => hd.lt.not_ge (by simpa [c] using h j)
    refine ⟨c, ⟨lt_of_le_not_ge hac hca, fun z h1 h2 => ?_⟩, (finComb_le_iff _ _).2 fun i => ?_⟩
    · have hz : ∀ i, i ≠ j → z.1 i = a.1 i := fun i hi => le_antisymm
        (by simpa [c, Function.update_of_ne hi] using h2.le i) (h1.le i)
      rcases hd.eq_or_eq (h1.le j) (by simpa [c] using h2.le j) with e | e
      · exact h1.ne (Subtype.ext (funext fun i => by
          by_cases hi : i = j
          · subst hi; exact e.symm
          · exact (hz i hi).symm))
      · exact h2.ne (Subtype.ext (funext fun i => by
          by_cases hi : i = j
          · subst hi; simp [c, e]
          · simp [c, Function.update_of_ne hi, hz i hi]))
    · by_cases hi : i = j
      · subst hi; simpa [c] using hdb
      · simpa [c, Function.update_of_ne hi] using hle i

/-- `Statement:` CONTROL, `FinComb` meets `hdepth`: above every `x`, run one free coordinate through
`mem n`. -/
theorem finComb_depth (x : FinComb) :
    ∃ m : ℕ → FinComb, StrictAnti m ∧ (∀ n, x < m n) ∧ IsGLB (Set.range m) x := by
  classical
  obtain ⟨N, hN⟩ := x.2
  let m : ℕ → FinComb := fun n => ⟨Function.update x.1 N (Comb.mem n), finComb_update x N _⟩
  have hxN : x.1 N = ⊥ := hN N le_rfl
  refine ⟨m, fun a b hab => ?_, fun n => ?_, ⟨?_, fun c hc => ?_⟩⟩
  · refine lt_of_le_not_ge ((finComb_le_iff _ _).2 fun i => ?_) fun h => ?_
    · by_cases hi : i = N
      · subst hi; simpa [m] using (Comb.mem_strictAnti hab).le
      · simp [m, Function.update_of_ne hi]
    · exact (Comb.mem_strictAnti hab).not_ge (by simpa [m] using h N)
  · refine lt_of_le_not_ge ((finComb_le_iff _ _).2 fun i => ?_) fun h => ?_
    · by_cases hi : i = N
      · subst hi; simp [m, hxN]
      · simp [m, Function.update_of_ne hi]
    · have := h N
      simp only [m, Function.update_self, hxN] at this
      exact absurd (le_bot_iff.1 this) (by intro e; cases e)
  · rintro _ ⟨n, rfl⟩
    refine (finComb_le_iff _ _).2 fun i => ?_
    by_cases hi : i = N
    · subst hi; simp [m, hxN]
    · simp [m, Function.update_of_ne hi]
  · refine (finComb_le_iff _ _).2 fun i => ?_
    by_cases hi : i = N
    · rw [hi]
      exact (Comb.glb_mem (c.1 N) fun n => by simpa [m] using hc ⟨n, rfl⟩ N).le.trans bot_le
    · simpa [m, Function.update_of_ne hi] using hc ⟨0, rfl⟩ i

/-- `Statement:` `BTree` order-embeds in `FinComb` with root at ⊥ of `FinComb`. -/
theorem finComb_btree : ∃ f : BTree ↪o FinComb, f (BTree.mk []) = ⊥ :=
  btree_embeds_of_hereditary_depth finComb_depth

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms BTree
#print axioms btree_le_iff
#print axioms btree_infinite
#print axioms end_infinite
#print axioms no_embed_of_upchains
#print axioms endPair01
#print axioms endPair02
#print axioms end_split_witness
#print axioms btree_split_witness
#print axioms no_End_embed_of_upchains
#print axioms no_BTree_embed_of_upchains
#print axioms Comb
#print axioms Comb.le
#print axioms Comb.sup
#print axioms Comb.le_def
#print axioms combZPS
#print axioms comb_zps_eq
#print axioms comb_zle_iff
#print axioms comb_atom_covBy
#print axioms comb_botHasFirstStep
#print axioms comb_depth
#print axioms comb_lt_iff
#print axioms comb_stronglyAtomic
#print axioms comb_upchains
#print axioms comb_no_End
#print axioms comb_no_BTree
#print axioms comb_atoms_infinite
#print axioms combCx
#print axioms combFloor
#print axioms atoms_infinite_of_depth
#print axioms diamondZPS
#print axioms diamondMember
#print axioms diamond_meets_hglb
#print axioms natSq_no_End
#print axioms natSq_hereditary
#print axioms prefixCodes
#print axioms prefixCodes_subset_iff
#print axioms prefixCodes_nil
#print axioms btree_embeds_of_independent
#print axioms sup_unitEnd_apply
#print axioms unitEnd_independent
#print axioms btree_embeds_End
#print axioms covers_infinite_of_depth
#print axioms covBy_eq_sup_of_le
#print axioms covBy_not_le_of_ne
#print axioms exists_two_covers
#print axioms treeStep
#print axioms treeGo
#print axioms TreeInv
#print axioms treeStep_lt
#print axioms treeStep_inv
#print axioms treeStep_sub
#print axioms treeGo_cons
#print axioms treeGo_le
#print axioms treeGo_avoids
#print axioms treeGo_mono
#print axioms treeGo_reflect
#print axioms btree_embeds_of_covers_infinite
#print axioms btree_embeds_of_hereditary_depth
#print axioms zp_btree_embeds_of_hereditary_depth
#print axioms finset_covers_infinite
#print axioms Bowtie
#print axioms Bowtie.le
#print axioms Bowtie.cov_iff
#print axioms Bowtie.two_killed
#print axioms no_strictAnti_of_wf
#print axioms end_top_no_depth
#print axioms Comb.mem_strictAnti
#print axioms Comb.glb_mem
#print axioms Comb.atom0_no_depth
#print axioms FinComb
#print axioms finComb_sup
#print axioms finComb_update
#print axioms finComb_le_iff
#print axioms finComb_stronglyAtomic
#print axioms finComb_depth
#print axioms finComb_btree
end PurityCheck
