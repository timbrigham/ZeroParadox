-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): one-point self-reference at ⊥ does not force the binary tree; an order embedding of the square into the carrier and a point other than ⊥ of the carrier do, one way (sufficient, not necessary); four formalizations of "⊥ is one point and two" measured against the tree. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.TreeNotForced
import ZeroParadox.Valuation.Interleave
import ZeroParadox.Computability.SelfCopyReference
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Settheory.QuineHost
import ZeroParadox.Ordinal.Epsilon0LeastFP
import Mathlib.Basic.NNReal.Basic
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# Doubling and the binary tree: one-point self-reference does not force it, the square embedded in the carrier and a point other than ⊥ of the carrier do, one way (sufficient, not necessary)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
One-point self-reference at ⊥ does not force the binary tree `BTree` (`comb_quine_and_no_tree`); an order embedding `X × X ↪o X` and
one point other than ⊥ of `X` do, one way (`square_embed_forces_btree`). Four readings of "⊥ is one point and two" are measured in
§§ V–VIII. Doubling is always a hypothesis. § IX holds carrier controls for the die's doubling premises (`ZeroParadox/Die.lean` § XXVI).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

/-! ### § I. One-point self-reference at ⊥ of `Comb`. -/

/-- `Statement:` the shift on `Comb`: ⊥ to ⊥, `atom k` to `atom (k + 1)`, `mem n` to `mem (n + 1)`. -/
def combShift : Comb → Comb
  | .bot => .bot
  | .atom k => .atom (k + 1)
  | .mem n => .mem (n + 1)

/-- `Statement:` `combShift` preserves and reflects `≤`. -/
theorem combShift_le_iff (x y : Comb) : combShift x ≤ combShift y ↔ x ≤ y := by
  rcases x with _ | j | m <;> rcases y with _ | k | n <;>
    simp [combShift, Comb.le_def, Comb.le]

/-- `Statement:` `combShift` as an order embedding. -/
def combShiftEmb : Comb ↪o Comb := OrderEmbedding.ofMapLEIff combShift combShift_le_iff

/-- `Statement:` `combShift` preserves joins. -/
theorem combShift_sup (x y : Comb) : combShift (x ⊔ y) = combShift x ⊔ combShift y := by
  show combShift (Comb.sup x y) = Comb.sup (combShift x) (combShift y)
  rcases x with _ | j | m <;> rcases y with _ | k | n <;> simp only [Comb.sup, combShift]
  all_goals first
    | (by_cases h : j = k
       · subst h; simp
       · simp only [h, ite_false, Nat.add_right_cancel_iff]
         congr 1; omega)
    | (congr 1; omega)

/-- `Statement:` `combShift` is one-to-one, not onto, with ⊥ of `Comb` its only fixed point
(`SelfCopyRef`). -/
theorem combShift_selfCopyRef : SelfCopyRef combShift := by
  refine ⟨fun a b h => combShiftEmb.injective h, fun hs => ?_, ⟨Comb.bot, rfl, fun y hy => ?_⟩⟩
  · obtain ⟨x, hx⟩ := hs (Comb.atom 0)
    rcases x with _ | k | n <;> simp [combShift] at hx
  · rcases y with _ | k | n
    · rfl
    · simp [combShift] at hy
    · simp [combShift] at hy

/-- `Statement:` a join-preserving order embedding of `Comb` into itself fixing ⊥ of `Comb`, with
`SelfCopyRef`, exists, and `Comb` embeds no `BTree`. -/
theorem selfCopy_at_bot_not_forcing :
    (∃ s : Comb ↪o Comb, SelfCopyRef s ∧ s ⊥ = ⊥ ∧ ∀ x y, s (x ⊔ y) = s x ⊔ s y) ∧
      IsEmpty (BTree ↪o Comb) :=
  ⟨⟨combShiftEmb, combShift_selfCopyRef, rfl, combShift_sup⟩, comb_no_BTree⟩

/-- `Statement:` `Comb` with `combShift` as its `AbstractSelfApp`. -/
instance combSelfApp : AbstractSelfApp Comb where
  selfApp := combShift
  fixed_bot := rfl
  unique_fp := fun _ hx => (combShift_selfCopyRef.2.2).unique hx (rfl : combShift Comb.bot = Comb.bot)

/-- `Statement:` ⊥ of `Comb` is a Quine atom under `combSelfApp`. -/
theorem comb_bot_quine : IsQuineAtom (ZPSemilattice.bot : Comb) := bot_is_quine_atom

/-- `Statement:` `combSelfApp` is not the constant map to ⊥ of `Comb`, ⊥ of `Comb` is a Quine atom,
every Quine atom of `Comb` is ⊥ of `Comb`, and `Comb` embeds no `BTree`. -/
theorem comb_quine_and_no_tree :
    AbstractSelfApp.selfApp (Comb.atom 0) ≠ (ZPSemilattice.bot : Comb) ∧
    IsQuineAtom (ZPSemilattice.bot : Comb) ∧
    (∀ q : Comb, IsQuineAtom q → q = ZPSemilattice.bot) ∧ IsEmpty (BTree ↪o Comb) :=
  ⟨fun h => Comb.noConfusion h, comb_bot_quine, t_exec, comb_no_BTree⟩

/-- `Statement:` a `QuineAtomHost` on any order with ⊥: membership is the cover relation plus one loop
at ⊥. -/
@[reducible] def coverQuineAtomHost (P : Type*) [PartialOrder P] [OrderBot P] : QuineAtomHost P where
  mem y x := y ⋖ x ∨ (y = ⊥ ∧ x = ⊥)
  bot := ⊥
  bot_mem_iff _ := ⟨fun h => h.elim (fun hc => absurd hc.lt not_lt_bot) And.left,
    fun h => Or.inr ⟨h, rfl⟩⟩
  reflexive_unique x hx := ((hx x).2 rfl).elim (fun hc => absurd hc.lt (lt_irrefl _)) And.right

/-- `Statement:` on `Comb` that host's bottom is ⊥ of `Comb`, ⊥ of `Comb` is a member of `atom 0`,
and `Comb` embeds no `BTree`. -/
theorem comb_coverHost :
    (coverQuineAtomHost Comb).bot = ⊥ ∧ (coverQuineAtomHost Comb).mem ⊥ (Comb.atom 0) ∧
      IsEmpty (BTree ↪o Comb) :=
  ⟨rfl, Or.inl (comb_atom_covBy 0), comb_no_BTree⟩

/-- `Statement:` `natSCR` is strictly monotone. -/
theorem natSCR_strictMono : StrictMono natSCR := by
  intro a b h
  unfold natSCR
  split_ifs <;> omega

/-- `Statement:` a linear order embeds no `BTree`. -/
theorem linear_no_btree {L : Type*} [LinearOrder L] : IsEmpty (BTree ↪o L) := ⟨fun f => by
  rcases le_total (f (BTree.mk [false])) (f (BTree.mk [true])) with h | h
  · have := f.le_iff_le.1 h; rw [btree_le_iff] at this; simp at this
  · have := f.le_iff_le.1 h; rw [btree_le_iff] at this; simp at this⟩

/-! ### § II. Two inside one: the square embedded in the carrier. -/

section Square
variable {X : Type*} [PartialOrder X] [OrderBot X]

/-- `Statement:` the two cells `j (a, ⊥)` and `j (⊥, a)`. -/
def sqC (j : X × X ↪o X) (a : X) : Bool → X
  | false => j (a, ⊥)
  | true => j (⊥, a)

/-- `Statement:` the node of a word: `[]` to ⊥ of `X`, `b :: l` to `j (sqC j a b, sqTree j a l)`. -/
def sqTree (j : X × X ↪o X) (a : X) : List Bool → X
  | [] => ⊥
  | b :: l => j (sqC j a b, sqTree j a l)

/-- `Statement:` for `a ≠ ⊥`, the two cells are incomparable. -/
theorem sqC_le_iff (j : X × X ↪o X) (a : X) (ha : a ≠ ⊥) (b b' : Bool) :
    sqC j a b ≤ sqC j a b' ↔ b = b' := by
  cases b <;> cases b'
  · exact ⟨fun _ => rfl, fun _ => le_rfl⟩
  · refine ⟨fun h => absurd (le_bot_iff.1 (j.le_iff_le.1 h).1) ha, fun h => by cases h⟩
  · refine ⟨fun h => absurd (le_bot_iff.1 (j.le_iff_le.1 h).2) ha, fun h => by cases h⟩
  · exact ⟨fun _ => rfl, fun _ => le_rfl⟩

/-- `Statement:` for `a ≠ ⊥`, no cell lies below ⊥ of `X`. -/
theorem sqC_not_le_bot (j : X × X ↪o X) (a : X) (ha : a ≠ ⊥) (b : Bool) :
    ¬ sqC j a b ≤ ⊥ := fun h => by
  have h' : sqC j a b ≤ j ⊥ := h.trans bot_le
  cases b
  · exact ha (le_bot_iff.1 (j.le_iff_le.1 h').1)
  · exact ha (le_bot_iff.1 (j.le_iff_le.1 h').2)

/-- `Statement:` for `a ≠ ⊥`, `sqTree j a l ≤ sqTree j a l'` iff `l` is a prefix of `l'`. -/
theorem sqTree_le_iff (j : X × X ↪o X) (a : X) (ha : a ≠ ⊥) :
    ∀ l l' : List Bool, sqTree j a l ≤ sqTree j a l' ↔ l <+: l'
  | [], _ => ⟨fun _ => List.nil_prefix, fun _ => bot_le⟩
  | b :: l, [] => by
    refine ⟨fun h => ?_, fun h => absurd (List.prefix_nil.1 h) (List.cons_ne_nil _ _)⟩
    have h' : sqTree j a (b :: l) ≤ j ⊥ := h.trans bot_le
    exact absurd (j.le_iff_le.1 h').1 (sqC_not_le_bot j a ha b)
  | b :: l, b' :: l' => by
    show j _ ≤ j _ ↔ _
    rw [j.le_iff_le, Prod.mk_le_mk, sqC_le_iff j a ha, sqTree_le_iff j a ha l l',
      List.cons_prefix_cons]

/-- `Statement:` an order embedding `X × X ↪o X` and one `a ≠ ⊥` give `BTree ↪o X` with root at ⊥
of `X`; one way. No joins and no surjectivity are assumed. -/
theorem square_embed_forces_btree (j : X × X ↪o X) (a : X) (ha : a ≠ ⊥) :
    ∃ f : BTree ↪o X, f (BTree.mk []) = ⊥ :=
  ⟨OrderEmbedding.ofMapLEIff (fun t => sqTree j a t.val)
    (fun t t' => (sqTree_le_iff j a ha t.val t'.val).trans (btree_le_iff t t').symm), rfl⟩

/-- `Statement:` an order isomorphism `X ≃o X × X` and one `a ≠ ⊥` give `BTree ↪o X` with root at ⊥
of `X`; one way. -/
theorem doubling_forces_btree (e : X ≃o X × X) (a : X) (ha : a ≠ ⊥) :
    ∃ f : BTree ↪o X, f (BTree.mk []) = ⊥ :=
  square_embed_forces_btree e.symm.toOrderEmbedding a ha

/-- `Statement:` under any `e : X ≃o X × X`, `e ⊥ = (⊥, ⊥)`. -/
theorem pole_is_pair (e : X ≃o X × X) : e ⊥ = (⊥, ⊥) := by rw [e.map_bot]; rfl

/-- `Statement:` `x ↦ e⁻¹ (⊥, x)`, an order embedding of `X` into itself. -/
def dblShift (e : X ≃o X × X) : X ↪o X :=
  OrderEmbedding.ofMapLEIff (fun x => e.symm (⊥, x)) (fun x y => by simp [Prod.mk_le_mk])

/-- `Statement:` `dblShift e` fixes ⊥ of `X`. -/
theorem dblShift_bot (e : X ≃o X × X) : dblShift e ⊥ = ⊥ := by
  show e.symm (⊥, ⊥) = ⊥
  exact e.symm.map_bot

/-- `Statement:` for some `a ≠ ⊥`, `dblShift e` is not onto. Uniqueness of its fixed point is not
claimed. -/
theorem dblShift_not_surj (e : X ≃o X × X) (a : X) (ha : a ≠ ⊥) :
    ¬ Function.Surjective (dblShift e) := fun hs => by
  obtain ⟨x, hx⟩ := hs (e.symm (a, ⊥))
  have := e.symm.injective hx
  exact ha (congrArg Prod.fst this).symm

end Square

/-- `Statement:` two points of `BTree` below a common point are comparable. -/
theorem btree_down_chain (x y z : BTree) (hx : x ≤ z) (hy : y ≤ z) : x ≤ y ∨ y ≤ x := by
  simp only [btree_le_iff] at *
  rcases le_total x.val.length y.val.length with h | h
  · exact Or.inl (List.prefix_of_prefix_length_le hx hy h)
  · exact Or.inr (List.prefix_of_prefix_length_le hy hx h)

/-- `Statement:` no order embedding `BTree × BTree ↪o BTree`. `Reading:` the converse of
`square_embed_forces_btree` fails. -/
theorem btree_no_square_embed : IsEmpty (BTree × BTree ↪o BTree) := ⟨fun j => by
  have hp : ((BTree.mk [false], BTree.mk []) : BTree × BTree) ≤ (BTree.mk [false], BTree.mk [false]) := by
    simp only [Prod.mk_le_mk, btree_le_iff]; decide
  have hq : ((BTree.mk [], BTree.mk [false]) : BTree × BTree) ≤ (BTree.mk [false], BTree.mk [false]) := by
    simp only [Prod.mk_le_mk, btree_le_iff]; decide
  rcases btree_down_chain _ _ _ (j.le_iff_le.2 hp) (j.le_iff_le.2 hq) with h | h
  · have := j.le_iff_le.1 h
    simp only [Prod.mk_le_mk, btree_le_iff] at this
    exact absurd this.1 (by decide)
  · have := j.le_iff_le.1 h
    simp only [Prod.mk_le_mk, btree_le_iff] at this
    exact absurd this.2 (by decide)⟩

/-- `Statement:` CONTROL, with a local `OrderBot BTree` whose bottom is `BTree.mk []`: `BTree` embeds
`BTree` with root at that bottom, has a point other than it, and admits no `BTree × BTree ↪o BTree`. -/
example :
    letI : OrderBot BTree :=
      { bot := BTree.mk [], bot_le := fun _ => (btree_le_iff _ _).2 List.nil_prefix }
    (∃ f : BTree ↪o BTree, f (BTree.mk []) = ⊥) ∧ BTree.mk [false] ≠ ⊥ ∧
      IsEmpty (BTree × BTree ↪o BTree) :=
  ⟨⟨RelEmbedding.refl _, rfl⟩, fun h => List.cons_ne_nil _ _ (congrArg BTree.val h),
    btree_no_square_embed⟩

/-! ### § III. Doubling makes an independent sequence (the Chakir–Pouzet route). -/

section Doubling
variable {X : Type*} [SemilatticeSup X] [OrderBot X]

/-- `Statement:` `dblSeq e a 0 = e⁻¹ (a, ⊥)`, `dblSeq e a (n + 1) = e⁻¹ (⊥, dblSeq e a n)`. -/
def dblSeq (e : X ≃o X × X) (a : X) : ℕ → X
  | 0 => e.symm (a, ⊥)
  | n + 1 => e.symm (⊥, dblSeq e a n)

/-- `Statement:` the `n`-th coordinate: `dblProj e 0 = fst ∘ e`, `dblProj e (n + 1) = dblProj e n ∘ snd ∘ e`. -/
def dblProj (e : X ≃o X × X) : ℕ → X → X
  | 0 => fun x => (e x).1
  | n + 1 => fun x => dblProj e n (e x).2

omit [OrderBot X] in
/-- `Statement:` `dblProj e n` is monotone. -/
theorem dblProj_mono (e : X ≃o X × X) (n : ℕ) : Monotone (dblProj e n) := by
  induction n with
  | zero => intro x y h; exact (e.monotone h).1
  | succ n ih => intro x y h; exact ih (e.monotone h).2

/-- `Statement:` `dblProj e n ⊥ = ⊥`. -/
theorem dblProj_bot (e : X ≃o X × X) (n : ℕ) : dblProj e n ⊥ = ⊥ := by
  induction n with
  | zero => show (e ⊥).1 = ⊥; rw [e.map_bot]; rfl
  | succ n ih => show dblProj e n (e ⊥).2 = ⊥; rw [e.map_bot]; exact ih

omit [OrderBot X] in
/-- `Statement:` `dblProj e n` preserves joins. -/
theorem dblProj_sup (e : X ≃o X × X) (n : ℕ) (x y : X) :
    dblProj e n (x ⊔ y) = dblProj e n x ⊔ dblProj e n y := by
  induction n generalizing x y with
  | zero => show (e (x ⊔ y)).1 = (e x).1 ⊔ (e y).1; rw [e.map_sup]; rfl
  | succ n ih =>
    show dblProj e n (e (x ⊔ y)).2 = dblProj e n (e x).2 ⊔ dblProj e n (e y).2
    rw [e.map_sup]; exact ih _ _

/-- `Statement:` `dblProj e n (dblSeq e a m)` is `a` if `m = n`, else ⊥. -/
theorem dblProj_seq (e : X ≃o X × X) (a : X) (n m : ℕ) :
    dblProj e n (dblSeq e a m) = if m = n then a else ⊥ := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => show (e (e.symm (a, ⊥))).1 = _; simp
    | succ m => show (e (e.symm (⊥, dblSeq e a m))).1 = _; simp
  | succ n ih =>
    cases m with
    | zero => show dblProj e n (e (e.symm (a, ⊥))).2 = _; simp [dblProj_bot]
    | succ m => show dblProj e n (e (e.symm (⊥, dblSeq e a m))).2 = _; simp [ih]

/-- `Statement:` `dblProj e n` commutes with finite joins. -/
theorem dblProj_finset_sup (e : X ≃o X × X) (n : ℕ) (T : Finset ℕ) (u : ℕ → X) :
    dblProj e n (T.sup u) = T.sup (fun m => dblProj e n (u m)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [dblProj_bot]
  | insert k T hk ih => rw [Finset.sup_insert, Finset.sup_insert, dblProj_sup, ih]

/-- `Statement:` for `a ≠ ⊥`, `dblSeq e a` is independent: `S.sup ≤ T.sup ↔ S ⊆ T`; both directions.
With `btree_embeds_of_independent` it gives the tree again, under joins. `Reading:` this step, doubling
⇒ independent sequence, was not located as of 2026-11-11, searched: `exact?` on
`Nonempty (Finset ℕ ↪o Y)` from `Y ≃o Y × Y` and `a ≠ ⊥` (no result, an uninformative null). Nearest
corpus relatives: `biprod_diagonal_only_zero`, `freeNat_biprod_self`. -/
theorem dblSeq_independent (e : X ≃o X × X) (a : X) (ha : a ≠ ⊥) (S T : Finset ℕ) :
    S.sup (dblSeq e a) ≤ T.sup (dblSeq e a) ↔ S ⊆ T := by
  constructor
  · intro h k hk
    by_contra hkT
    have h1 : a ≤ dblProj e k (S.sup (dblSeq e a)) := by
      have := dblProj_mono e k (Finset.le_sup (f := dblSeq e a) hk)
      rwa [dblProj_seq, ite_eq_left rfl] at this
    have h2 : dblProj e k (T.sup (dblSeq e a)) = ⊥ := by
      rw [dblProj_finset_sup, Finset.sup_eq_bot_iff]
      intro m hm
      rw [dblProj_seq, ite_eq_right (fun hmk : m = k => hkT (hmk ▸ hm))]
    exact ha (le_bot_iff.1 (h2 ▸ h1.trans (dblProj_mono e k h)))
  · intro h; exact Finset.sup_mono h

end Doubling

/-! ### § IV. Controls on § II and § III. -/

/-- `Statement:` `End` doubles (`interleaveEnd`), so `BTree ↪o End` with root at ⊥ of `End`. -/
theorem end_doubling_btree : ∃ f : BTree ↪o End, f (BTree.mk []) = ⊥ :=
  doubling_forces_btree interleaveEnd (unitEnd 0) (fun h => by
    have := congrFun h 0
    rw [unitEnd_self] at this
    exact absurd this (by decide))

/-- `Statement:` `Comb` is not order-isomorphic to its square. -/
theorem comb_not_doubling : IsEmpty (Comb ≃o Comb × Comb) :=
  ⟨fun e => by
    obtain ⟨f, -⟩ := doubling_forces_btree e (Comb.atom 0) (fun h => Comb.noConfusion h)
    exact comb_no_BTree.false f⟩

/-- `Statement:` a subsingleton order doubles: `x ↦ (x, x)`. -/
def subsingletonDouble (X : Type*) [PartialOrder X] [Subsingleton X] : X ≃o X × X where
  toFun x := (x, x)
  invFun p := p.1
  left_inv _ := rfl
  right_inv p := Prod.ext rfl (Subsingleton.elim _ _)
  map_rel_iff' := by intro a b; simp

/-- `Statement:` CONTROL, `Unit` doubles, has no `a ≠ ⊥`, and embeds no `BTree`. -/
theorem unit_control :
    Nonempty (Unit ≃o Unit × Unit) ∧ (∀ a : Unit, a = ⊥) ∧ IsEmpty (BTree ↪o Unit) := by
  refine ⟨⟨subsingletonDouble Unit⟩, fun _ => rfl, ⟨fun f => ?_⟩⟩
  have := f.injective (Subsingleton.elim (f (BTree.mk [])) (f (BTree.mk [false])))
  cases this

/-- `Statement:` `WithBot (Finset ℕ)`. -/
abbrev WBF := WithBot (Finset ℕ)

/-- `Statement:` in `WBF`, every `x ≠ ⊥` lies above `↑∅`. -/
theorem wbf_min (x : WBF) (hx : x ≠ ⊥) : ((∅ : Finset ℕ) : WBF) ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl hx
  | coe s => exact WithBot.coe_le_coe.2 (Finset.empty_subset s)

/-- `Statement:` `WBF` is not order-isomorphic to its square. -/
theorem wbf_not_doubling : IsEmpty (WBF ≃o WBF × WBF) :=
  ⟨fun e => by
    set c : WBF := ((∅ : Finset ℕ) : WBF) with hcdef
    have hc : c ≠ ⊥ := WithBot.coe_ne_bot
    have h1 : e.symm (c, ⊥) ≠ ⊥ := fun h => hc (by
      have := e.symm.injective (h.trans e.symm.map_bot.symm)
      exact congrArg Prod.fst this)
    have h2 : e.symm (⊥, c) ≠ ⊥ := fun h => hc (by
      have := e.symm.injective (h.trans e.symm.map_bot.symm)
      exact congrArg Prod.snd this)
    have k1 : e c ≤ (c, ⊥) := by simpa using e.monotone (wbf_min _ h1)
    have k2 : e c ≤ (⊥, c) := by simpa using e.monotone (wbf_min _ h2)
    have hb : e c ≤ ⊥ := ⟨k2.1, k1.2⟩
    exact hc (e.injective ((le_bot_iff.1 hb).trans e.map_bot.symm))⟩

/-- `Statement:` the singletons `{n}` are independent in `WBF`; both directions. -/
theorem wbf_independent (S T : Finset ℕ) :
    S.sup (fun n => (({n} : Finset ℕ) : WBF)) ≤ T.sup (fun n => (({n} : Finset ℕ) : WBF)) ↔
      S ⊆ T := by
  have hT : ∀ T : Finset ℕ, T.sup (fun n => (({n} : Finset ℕ) : WBF)) ≤ (T : WBF) :=
    fun T => Finset.sup_le fun n hn => WithBot.coe_le_coe.2 (Finset.singleton_subset_iff.2 hn)
  constructor
  · intro h k hk
    have := ((Finset.le_sup (f := fun n => (({n} : Finset ℕ) : WBF)) hk).trans h).trans (hT T)
    exact Finset.singleton_subset_iff.1 (WithBot.coe_le_coe.1 this)
  · intro h; exact Finset.sup_mono h

/-- `Statement:` CONTROL, `BTree ↪o WBF` with root at ⊥ of `WBF`, while `WBF` does not double
(`wbf_not_doubling`): the tree does not force doubling. -/
theorem wbf_btree : ∃ f : BTree ↪o WBF, f (BTree.mk []) = ⊥ :=
  btree_embeds_of_independent _ wbf_independent

/-! ### § V. "One and two" at ⊥ only. -/

/-- `Statement:` the cell `Set.Iic ⊥` of any `X` is order-isomorphic to its square. -/
def poleCellDouble (X : Type*) [PartialOrder X] [OrderBot X] :
    Set.Iic (⊥ : X) ≃o Set.Iic (⊥ : X) × Set.Iic (⊥ : X) where
  toFun x := (x, x)
  invFun p := p.1
  left_inv _ := rfl
  right_inv p := Prod.ext rfl (Subtype.ext ((le_bot_iff.1 p.1.2).trans (le_bot_iff.1 p.2.2).symm))
  map_rel_iff' := by intro a b; simp [Prod.mk_le_mk]

/-- `Statement:` `x ↦ (x, ⊥)`, an order embedding `X ↪o X × X` in every `X`. -/
def oneInTwo (X : Type*) [PartialOrder X] [OrderBot X] : X ↪o X × X :=
  OrderEmbedding.ofMapLEIff (fun x => (x, ⊥)) (fun x y => by simp [Prod.mk_le_mk])

/-- `Statement:` the square `Bool × Bool` placed at ⊥ of `Comb`. -/
def combSq : Bool × Bool → Comb
  | (false, false) => .bot
  | (true, false) => .atom 0
  | (false, true) => .atom 1
  | (true, true) => .mem 0

/-- `Statement:` `combSq` preserves and reflects `≤`. -/
theorem combSq_le_iff (p q : Bool × Bool) : combSq p ≤ combSq q ↔ p ≤ q := by
  rcases p with ⟨_ | _, _ | _⟩ <;> rcases q with ⟨_ | _, _ | _⟩ <;>
    simp [combSq, Comb.le_def, Comb.le, Prod.mk_le_mk]

/-- `Statement:` `combSq` as an order embedding. -/
def combSqEmb : Bool × Bool ↪o Comb := OrderEmbedding.ofMapLEIff combSq combSq_le_iff

/-- `Statement:` the cell at ⊥ of `Comb` doubles, a square sits at ⊥ of `Comb`, `Comb` embeds in its
square, and `Comb` embeds neither `BTree` nor its square. -/
theorem comb_local_pair_no_tree :
    Nonempty (Set.Iic (⊥ : Comb) ≃o Set.Iic (⊥ : Comb) × Set.Iic (⊥ : Comb)) ∧
    (∃ s : Bool × Bool ↪o Comb, s ⊥ = ⊥) ∧ Nonempty (Comb ↪o Comb × Comb) ∧
    IsEmpty (BTree ↪o Comb) ∧ IsEmpty (Comb × Comb ↪o Comb) :=
  ⟨⟨poleCellDouble Comb⟩, ⟨combSqEmb, rfl⟩, ⟨oneInTwo Comb⟩, comb_no_BTree,
    ⟨fun j => by
      obtain ⟨f, -⟩ := square_embed_forces_btree j (Comb.atom 0) (fun h => Comb.noConfusion h)
      exact comb_no_BTree.false f⟩⟩

/-! ### § VI. "One and two" as a wedge: two copies glued at ⊥ only. -/

/-- `Statement:` the axes of `X × X`: pairs with one coordinate ⊥ of `X`. -/
abbrev BotWedge (X : Type*) [PartialOrder X] [OrderBot X] := {p : X × X // p.1 = ⊥ ∨ p.2 = ⊥}

/-- `Statement:` `BotWedge X` has ⊥ the pair (⊥, ⊥). -/
instance botWedge_orderBot (X : Type*) [PartialOrder X] [OrderBot X] : OrderBot (BotWedge X) :=
  Subtype.orderBot (Or.inl rfl)

/-- `Statement:` in a join-semilattice with some `a ≠ ⊥`, no order isomorphism `X ≃o BotWedge X`.
`Reading:` `BotWedge X` is, as a poset, the wedge product `X ∨ X` (disjoint union with the least
elements identified) of Beall–Kuzmanovski–Li–Seceleanu, arXiv:2510.22843v2, Def. 3.14. -/
theorem wedge_double_impossible_of_sup {X : Type*} [SemilatticeSup X] [OrderBot X] (a : X)
    (ha : a ≠ ⊥) : IsEmpty (X ≃o BotWedge X) := ⟨fun e => by
  let w1 : BotWedge X := ⟨(a, ⊥), Or.inr rfl⟩
  let w2 : BotWedge X := ⟨(⊥, a), Or.inl rfl⟩
  set z := e (e.symm w1 ⊔ e.symm w2) with hz
  have h1 : w1 ≤ z := by
    have := e.monotone (le_sup_left : e.symm w1 ≤ e.symm w1 ⊔ e.symm w2)
    rwa [e.apply_symm_apply] at this
  have h2 : w2 ≤ z := by
    have := e.monotone (le_sup_right : e.symm w2 ≤ e.symm w1 ⊔ e.symm w2)
    rwa [e.apply_symm_apply] at this
  have k1 : a ≤ z.1.1 := (show ((a, ⊥) : X × X) ≤ z.1 from h1).1
  have k2 : a ≤ z.1.2 := (show ((⊥, a) : X × X) ≤ z.1 from h2).2
  rcases z.2 with h | h
  · rw [h] at k1; exact ha (le_bot_iff.1 k1)
  · rw [h] at k2; exact ha (le_bot_iff.1 k2)⟩

-- Statement: the same in ZP-A's induced order on any `ZPSemilattice` with a point other than its ⊥.
example {L : Type*} [ZPSemilattice L] (a : L) (ha : a ≠ ZPSemilattice.bot) :
    letI := zpSemilatticeSup L; letI := zpOrderBot L; IsEmpty (L ≃o BotWedge L) := by
  let _ := zpSemilatticeSup L; let _ := zpOrderBot L
  exact wedge_double_impossible_of_sup a ha

/-- `Statement:` ⊥ plus ℕ-many disjoint copies of the chain ℕ (`pt i n`: chain `i`, height `n`). -/
inductive ChainFan
  | bot
  | pt (i n : ℕ)
  deriving DecidableEq

namespace ChainFan

/-- `Statement:` the order on `ChainFan`. -/
def le : ChainFan → ChainFan → Prop
  | bot, _ => True
  | pt _ _, bot => False
  | pt i n, pt j m => i = j ∧ n ≤ m

instance : PartialOrder ChainFan where
  le := le
  le_refl x := by cases x <;> simp [le]
  le_trans x y z := by
    rcases x with _ | ⟨i, n⟩ <;> rcases y with _ | ⟨j, m⟩ <;> rcases z with _ | ⟨k, p⟩ <;>
      simp [le]
    all_goals omega
  le_antisymm x y := by
    rcases x with _ | ⟨i, n⟩ <;> rcases y with _ | ⟨j, m⟩ <;> simp [le]
    all_goals omega

instance : OrderBot ChainFan where
  bot := bot
  bot_le _ := trivial

/-- `Statement:` `x ≤ y` in `ChainFan` is `ChainFan.le x y`. -/
theorem le_def (x y : ChainFan) : x ≤ y ↔ le x y := Iff.rfl

end ChainFan

/-- `Statement:` even chains to the left arm, odd chains to the right arm. -/
def chainFanToWedge : ChainFan → BotWedge ChainFan
  | .bot => ⟨(.bot, .bot), Or.inl rfl⟩
  | .pt i n => if i % 2 = 0 then ⟨(.pt (i / 2) n, .bot), Or.inr rfl⟩
      else ⟨(.bot, .pt (i / 2) n), Or.inl rfl⟩

/-- `Statement:` `chainFanToWedge` preserves and reflects `≤`. -/
theorem chainFanToWedge_le_iff (x y : ChainFan) :
    chainFanToWedge x ≤ chainFanToWedge y ↔ x ≤ y := by
  rcases x with _ | ⟨i, n⟩ <;> rcases y with _ | ⟨j, m⟩
  · exact ⟨fun _ => trivial, fun _ => le_rfl⟩
  · exact ⟨fun _ => trivial, fun _ => bot_le⟩
  · refine ⟨fun h => ?_, fun h => absurd h id⟩
    by_cases hi : i % 2 = 0
    · have := (show ((ChainFan.pt (i / 2) n, ChainFan.bot) : ChainFan × ChainFan) ≤
          (ChainFan.bot, ChainFan.bot) by
        have h' := h; simp only [chainFanToWedge, hi, ↓reduceIte] at h'; exact h').1
      exact absurd this id
    · have := (show ((ChainFan.bot, ChainFan.pt (i / 2) n) : ChainFan × ChainFan) ≤
          (ChainFan.bot, ChainFan.bot) by
        have h' := h; simp only [chainFanToWedge, hi, ↓reduceIte] at h'; exact h').2
      exact absurd this id
  · rw [ChainFan.le_def]
    show chainFanToWedge (.pt i n) ≤ chainFanToWedge (.pt j m) ↔ (i = j ∧ n ≤ m)
    by_cases hi : i % 2 = 0 <;> by_cases hj : j % 2 = 0 <;>
      simp only [chainFanToWedge, hi, hj, ↓reduceIte, Subtype.mk_le_mk, Prod.mk_le_mk,
        ChainFan.le_def, ChainFan.le] <;>
      constructor <;> intro h
    all_goals first
      | (obtain ⟨⟨h1, h2⟩, -⟩ := h; exact ⟨by omega, h2⟩)
      | (obtain ⟨h1, h2⟩ := h; exact ⟨⟨by omega, h2⟩, trivial⟩)
      | (obtain ⟨-, ⟨h1, h2⟩⟩ := h; exact ⟨by omega, h2⟩)
      | (obtain ⟨h1, h2⟩ := h; exact ⟨trivial, ⟨by omega, h2⟩⟩)
      | (obtain ⟨h1, -⟩ := h; exact absurd h1 id)
      | (obtain ⟨-, h1⟩ := h; exact absurd h1 id)
      | (obtain ⟨h1, h2⟩ := h; exfalso; omega)

/-- `Statement:` `chainFanToWedge` is onto. -/
theorem chainFanToWedge_surj : Function.Surjective chainFanToWedge := by
  rintro ⟨⟨x, y⟩, h⟩
  rcases x with _ | ⟨i, n⟩ <;> rcases y with _ | ⟨j, m⟩
  · exact ⟨.bot, rfl⟩
  · refine ⟨.pt (2 * j + 1) m, ?_⟩
    have h1 : ¬ (2 * j + 1) % 2 = 0 := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    simp only [chainFanToWedge, ite_eq_right h1, h2]
  · refine ⟨.pt (2 * i) n, ?_⟩
    have h1 : (2 * i) % 2 = 0 := by omega
    have h2 : (2 * i) / 2 = i := by omega
    simp only [chainFanToWedge, ite_eq_left h1, h2]
  · exfalso
    rcases h with h | h <;> cases h

/-- `Statement:` `ChainFan ≃o BotWedge ChainFan`. -/
noncomputable def chainFanWedge : ChainFan ≃o BotWedge ChainFan :=
  OrderIso.ofSurjective (OrderEmbedding.ofMapLEIff chainFanToWedge chainFanToWedge_le_iff)
    chainFanToWedge_surj

/-- `Statement:` `chainFanWedge` sends ⊥ of `ChainFan` to ⊥ of the wedge. -/
theorem chainFanWedge_bot : chainFanWedge ⊥ = ⊥ := rfl

/-- `Statement:` every non-⊥ point of `ChainFan` has a linearly ordered up-set. -/
theorem chainFan_upchains :
    ∀ z : ChainFan, z ≠ ⊥ → ∀ u v, z ≤ u → z ≤ v → u ≤ v ∨ v ≤ u := by
  intro z hz u v hu hv
  rcases z with _ | ⟨i, n⟩
  · exact absurd rfl hz
  rcases u with _ | ⟨j, m⟩ <;> rcases v with _ | ⟨k, p⟩ <;>
    simp [ChainFan.le_def, ChainFan.le] at hu hv ⊢
  all_goals omega

/-- `Statement:` no order embedding `BTree ↪o ChainFan`. -/
theorem chainFan_no_btree : IsEmpty (BTree ↪o ChainFan) :=
  no_BTree_embed_of_upchains chainFan_upchains

/-- `Statement:` `ChainFan` is order-isomorphic to its wedge with itself, ⊥ to ⊥, and embeds neither
`BTree` nor its square. -/
theorem wedge_double_no_tree :
    (∃ e : ChainFan ≃o BotWedge ChainFan, e ⊥ = ⊥) ∧ IsEmpty (BTree ↪o ChainFan) ∧
      IsEmpty (ChainFan × ChainFan ↪o ChainFan) :=
  ⟨⟨chainFanWedge, chainFanWedge_bot⟩, chainFan_no_btree, ⟨fun j => by
    obtain ⟨f, -⟩ := square_embed_forces_btree j (ChainFan.pt 0 0) (fun h => ChainFan.noConfusion h)
    exact chainFan_no_btree.false f⟩⟩

/-- `Statement:` CONTROL, `End` (which doubles and carries the tree) is not order-isomorphic to its
wedge. -/
theorem end_not_wedge_double : IsEmpty (End ≃o BotWedge End) :=
  wedge_double_impossible_of_sup (unitEnd 0) (fun h => by
    have := congrFun h 0
    rw [unitEnd_self] at this
    exact absurd this (by decide))

/-! ### § VII. "One and two" as two poles exchanged by an order-reversing involution. -/

/-- `Statement:` `Fin.rev` on `Fin 3` swaps ⊥ and ⊤, is an involution, reverses `≤`; `Fin 3` embeds
no `BTree`. -/
theorem fin3_exchange_no_tree :
    Fin.rev (⊥ : Fin 3) = ⊤ ∧ Fin.rev (⊤ : Fin 3) = ⊥ ∧ (∀ x : Fin 3, Fin.rev (Fin.rev x) = x) ∧
    (∀ x y : Fin 3, Fin.rev x ≤ Fin.rev y ↔ y ≤ x) ∧ IsEmpty (BTree ↪o Fin 3) :=
  ⟨rfl, rfl, Fin.rev_rev, fun _ _ => Fin.rev_le_rev, linear_no_btree⟩

/-- `Statement:` the interval `[-1, 1]` of ℚ. -/
abbrev Q11 := Set.Icc (-1 : ℚ) 1

/-- `Statement:` negation on `Q11`. -/
def q11Neg (x : Q11) : Q11 := ⟨-x.1, by linarith [x.2.2], by linarith [x.2.1]⟩
/-- `Statement:` `-1` in `Q11`. -/
def q11Lo : Q11 := ⟨-1, le_rfl, by norm_num⟩
/-- `Statement:` `1` in `Q11`. -/
def q11Hi : Q11 := ⟨1, by norm_num, le_rfl⟩

/-- `Statement:` on the infinite chain `Q11`, negation swaps its least and greatest points, is an
involution and reverses `≤`; `Q11` embeds no `BTree`. -/
theorem q11_exchange_no_tree :
    IsBot q11Lo ∧ IsTop q11Hi ∧ q11Neg q11Lo = q11Hi ∧ q11Neg q11Hi = q11Lo ∧
    (∀ x, q11Neg (q11Neg x) = x) ∧ (∀ x y, q11Neg x ≤ q11Neg y ↔ y ≤ x) ∧ Infinite Q11 ∧
    IsEmpty (BTree ↪o Q11) := by
  refine ⟨fun x => x.2.1, fun x => x.2.2, ?_, ?_, fun x => ?_, fun x y => ?_,
    (Set.Icc_infinite (by norm_num : (-1 : ℚ) < 1)).to_subtype, linear_no_btree⟩
  · apply Subtype.ext; simp [q11Neg, q11Lo, q11Hi]
  · apply Subtype.ext; simp [q11Neg, q11Lo, q11Hi]
  · apply Subtype.ext; simp [q11Neg]
  · show -x.1 ≤ -y.1 ↔ y.1 ≤ x.1
    exact neg_le_neg_iff

/-- `Statement:` on `Set ℕ`, complement swaps ⊥ and ⊤, is an involution and reverses `≤`; `BTree`
embeds with root at ⊥ of `Set ℕ`. -/
theorem setNat_exchange_tree :
    (⊥ : Set ℕ)ᶜ = ⊤ ∧ (⊤ : Set ℕ)ᶜ = ⊥ ∧ (∀ s : Set ℕ, sᶜᶜ = s) ∧
    (∀ s t : Set ℕ, sᶜ ≤ tᶜ ↔ t ≤ s) ∧ ∃ f : BTree ↪o Set ℕ, f (BTree.mk []) = ⊥ := by
  refine ⟨compl_bot, compl_top, compl_compl, fun s t => compl_le_compl_iff_le, ?_⟩
  obtain ⟨f, hf⟩ := btree_embeds_of_covers_infinite finset_covers_infinite
  exact ⟨f.trans Finset.coeEmb, by simp [hf]⟩

/-! ### § VIII. "One and two" as a point identity, and as a pair of charts. -/

/-- `Statement:` in a bounded order, ⊥ = ⊤ makes it a subsingleton, which doubles and embeds no
`BTree`. -/
theorem pole_identity_collapses {X : Type*} [PartialOrder X] [BoundedOrder X]
    (h : (⊥ : X) = ⊤) :
    Subsingleton X ∧ Nonempty (X ≃o X × X) ∧ IsEmpty (BTree ↪o X) := by
  have hs : Subsingleton X := subsingleton_of_bot_eq_top h
  refine ⟨hs, ⟨subsingletonDouble X⟩, ⟨fun f => ?_⟩⟩
  have := f.injective (Subsingleton.elim (f (BTree.mk [])) (f (BTree.mk [false])))
  cases this

/-- `Statement:` the chart swap on `X × Xᵒᵈ`: `(x, y) ↦ (y, x)` across the dual. -/
def chartSwap {X : Type*} (p : X × Xᵒᵈ) : X × Xᵒᵈ := (OrderDual.ofDual p.2, OrderDual.toDual p.1)

/-- `Statement:` ⊥ of `X × Xᵒᵈ` is the pair (⊥ of `X`, ⊤ of `X`); `chartSwap` sends it to ⊤ and back,
is an involution and reverses `≤`. -/
theorem chartSwap_props {X : Type*} [PartialOrder X] [BoundedOrder X] :
    (⊥ : X × Xᵒᵈ) = (⊥, OrderDual.toDual ⊤) ∧ chartSwap (⊥ : X × Xᵒᵈ) = ⊤ ∧
    chartSwap (⊤ : X × Xᵒᵈ) = ⊥ ∧ (∀ p : X × Xᵒᵈ, chartSwap (chartSwap p) = p) ∧
    (∀ p q : X × Xᵒᵈ, chartSwap p ≤ chartSwap q ↔ q ≤ p) :=
  ⟨rfl, rfl, rfl, fun _ => rfl, fun p q => by
    simp only [chartSwap, Prod.mk_le_mk, OrderDual.toDual_le_toDual, OrderDual.ofDual_le_ofDual]
    exact and_comm.trans (by rw [Prod.le_def])⟩

/-- `Statement:` `Fin 3 × (Fin 3)ᵒᵈ` embeds no `BTree`. -/
theorem fin3_twoChart_no_tree : IsEmpty (BTree ↪o Fin 3 × (Fin 3)ᵒᵈ) := ⟨fun f => by
  have := btree_infinite
  have := Finite.of_injective f f.injective
  exact not_finite BTree⟩

/-- `Statement:` the ternary code of a word, `false ↦ 1`, `true ↦ 2`. -/
def ternFwd : List Bool → ℚ
  | [] => 0
  | b :: l => ((if b then 2 else 1) + ternFwd l) / 3

/-- `Statement:` the ternary code with the digits reversed, `false ↦ 2`, `true ↦ 1`. -/
def ternRev : List Bool → ℚ
  | [] => 0
  | b :: l => ((if b then 1 else 2) + ternRev l) / 3

/-- `Statement:` `0 ≤ ternFwd l < 1`. -/
theorem ternFwd_bounds : ∀ l, 0 ≤ ternFwd l ∧ ternFwd l < 1
  | [] => by simp [ternFwd]
  | b :: l => by
    obtain ⟨h0, h1⟩ := ternFwd_bounds l
    cases b <;> simp only [ternFwd, ite_true, ite_false, Bool.false_eq_true] <;> constructor <;>
      linarith

/-- `Statement:` `0 ≤ ternRev l < 1`. -/
theorem ternRev_bounds : ∀ l, 0 ≤ ternRev l ∧ ternRev l < 1
  | [] => by simp [ternRev]
  | b :: l => by
    obtain ⟨h0, h1⟩ := ternRev_bounds l
    cases b <;> simp only [ternRev, ite_true, ite_false, Bool.false_eq_true] <;> constructor <;>
      linarith

/-- `Statement:` both codes rise from `l` to `l'` iff `l` is a prefix of `l'`. -/
theorem tern_le_iff : ∀ l l' : List Bool,
    (ternFwd l ≤ ternFwd l' ∧ ternRev l ≤ ternRev l') ↔ l <+: l'
  | [], l' => ⟨fun _ => List.nil_prefix, fun _ => ⟨(ternFwd_bounds l').1, (ternRev_bounds l').1⟩⟩
  | b :: l, [] => by
    refine ⟨fun h => ?_, fun h => absurd (List.prefix_nil.1 h) (List.cons_ne_nil _ _)⟩
    obtain ⟨h0, -⟩ := ternFwd_bounds l
    have := h.1
    cases b <;> simp only [ternFwd, ite_true, ite_false, Bool.false_eq_true] at this <;> linarith
  | b :: l, b' :: l' => by
    rw [List.cons_prefix_cons, ← tern_le_iff l l']
    obtain ⟨a0, a1⟩ := ternFwd_bounds l
    obtain ⟨b0, b1⟩ := ternFwd_bounds l'
    obtain ⟨c0, c1⟩ := ternRev_bounds l
    obtain ⟨d0, d1⟩ := ternRev_bounds l'
    cases b <;> cases b' <;> simp only [ternFwd, ternRev, Bool.false_eq_true, ↓reduceIte]
    · constructor
      · rintro ⟨h1, h2⟩; exact ⟨by trivial, by linarith, by linarith⟩
      · rintro ⟨-, h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · constructor
      · rintro ⟨h1, h2⟩; exfalso; linarith
      · rintro ⟨h, -⟩; exact absurd h (by decide)
    · constructor
      · rintro ⟨h1, h2⟩; exfalso; linarith
      · rintro ⟨h, -⟩; exact absurd h (by decide)
    · constructor
      · rintro ⟨h1, h2⟩; exact ⟨by trivial, by linarith, by linarith⟩
      · rintro ⟨-, h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- `Statement:` a word's point of `Q11 × Q11ᵒᵈ`: `ternFwd` in the first chart, `-ternRev` in the dual. -/
def twoChartCode (l : List Bool) : Q11 × Q11ᵒᵈ :=
  (⟨ternFwd l, by linarith [(ternFwd_bounds l).1], (ternFwd_bounds l).2.le⟩,
   OrderDual.toDual ⟨-ternRev l, by linarith [(ternRev_bounds l).2], by linarith [(ternRev_bounds l).1]⟩)

/-- `Statement:` `BTree` order-embeds in `Q11 × Q11ᵒᵈ`, though `Q11` embeds no `BTree`. -/
theorem q11_twoChart_tree : Nonempty (BTree ↪o Q11 × Q11ᵒᵈ) := by
  refine ⟨OrderEmbedding.ofMapLEIff (fun t => twoChartCode t.val) (fun t t' => ?_)⟩
  rw [btree_le_iff, ← tern_le_iff]
  show (ternFwd t.val ≤ ternFwd t'.val ∧ -ternRev t'.val ≤ -ternRev t.val) ↔ _
  rw [neg_le_neg_iff]

/-! ### § IX. The die's doubling premises on carriers; the tree without discreteness. -/

-- Statement: `square_embed_forces_btree` is the order case of `Motion.tree_of_square`
-- (`ZeroParadox/Die.lean` § XXVI), `L` the order `≤` and the root ⊥ of `X`.
example {X : Type} [PartialOrder X] [OrderBot X] (j : X × X ↪o X) (a : X) (ha : a ≠ ⊥) :
    ∃ f : BTree ↪o X, f (BTree.mk []) = ⊥ := by
  obtain ⟨f, hf0, hf⟩ := Motion.tree_of_square (α := X) (· ≤ ·) (fun _ => le_rfl)
    (fun _ _ _ => le_trans) j (fun p q => by rw [j.le_iff_le]; rfl) ⊥ a bot_le bot_le
    (fun h => ha (le_bot_iff.1 h))
  exact ⟨OrderEmbedding.ofMapLEIff (fun t => f t.val)
    (fun t t' => (hf t.val t'.val).trans (btree_le_iff t t').symm), hf0⟩

open Motion

/-- `Statement:` on `End`, set one `0` digit to `1`. -/
def endBitFlip (x y : End) : Prop := ∃ k, x k = 0 ∧ y = Function.update x k 1

/-- `Statement:` the motion on `End`: UP constant ⊥ of `End`, a step `endBitFlip`. -/
def endFlipMotion : Motion End := ofTotal (fun _ => botEnd) (fun _ => rfl) endBitFlip

/-- `Statement:` the first component of `interleaveEnd x` reads the even digits of `x`. -/
theorem interleaveEnd_fst_eval (x : End) (m : ℕ) : (interleaveEnd x).1 m = x (2 * m) := by
  rw [interleaveEnd_apply]

/-- `Statement:` the second component of `interleaveEnd x` reads the odd digits of `x`. -/
theorem interleaveEnd_snd_eval (x : End) (m : ℕ) : (interleaveEnd x).2 m = x (2 * m + 1) := by
  rw [interleaveEnd_apply]

/-- `Statement:` setting digit `2 m` to `1` sets digit `m` of the first component. -/
theorem interleaveEnd_update_even (x : End) (m : ℕ) :
    interleaveEnd (Function.update x (2 * m) 1) =
      (Function.update (interleaveEnd x).1 m 1, (interleaveEnd x).2) := by
  rw [interleaveEnd_apply, interleaveEnd_apply]
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · by_cases h : n = m
    · subst h; simp
    · have h2 : 2 * n ≠ 2 * m := by omega
      simp [h, h2]
  · have h2 : 2 * n + 1 ≠ 2 * m := by omega
    simp [h2]

/-- `Statement:` setting digit `2 m + 1` to `1` sets digit `m` of the second component. -/
theorem interleaveEnd_update_odd (x : End) (m : ℕ) :
    interleaveEnd (Function.update x (2 * m + 1) 1) =
      ((interleaveEnd x).1, Function.update (interleaveEnd x).2 m 1) := by
  rw [interleaveEnd_apply, interleaveEnd_apply]
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · have h2 : 2 * n ≠ 2 * m + 1 := by omega
    simp [h2]
  · by_cases h : n = m
    · subst h; simp
    · simp [h]

/-- `Statement:` `interleaveEnd` is an isomorphism of `endFlipMotion` onto its interleaving square. -/
def endFlipIsoAProd : StrictIso endFlipMotion (endFlipMotion.aprod endFlipMotion) where
  hom := ⟨interleaveEnd, fun {x y} h => by
      obtain ⟨k, hk, rfl⟩ := h
      obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [interleaveEnd_update_even]
        exact Prod.gameAdd_iff.2 (Or.inl ⟨⟨m, by rw [interleaveEnd_fst_eval]; exact hk, rfl⟩, rfl⟩)
      · rw [interleaveEnd_update_odd]
        exact Prod.gameAdd_iff.2 (Or.inr ⟨⟨m, by rw [interleaveEnd_snd_eval]; exact hk, rfl⟩, rfl⟩),
    fun x => by
      show upPair (Part.some botEnd) (Part.some botEnd) = (Part.some botEnd).map _
      rw [upPair_some, Part.map_some, interleaveEnd_bot]⟩
  inv := ⟨interleaveEnd.symm, fun {p q} h => by
      rcases Prod.gameAdd_iff.1 h with ⟨⟨m, hm, hq1⟩, hq2⟩ | ⟨⟨m, hm, hq2⟩, hq1⟩
      · refine ⟨2 * m, ?_, ?_⟩
        · rw [← interleaveEnd_fst_eval (interleaveEnd.symm p) m, OrderIso.apply_symm_apply]
          exact hm
        · apply interleaveEnd.injective
          rw [OrderIso.apply_symm_apply, interleaveEnd_update_even, OrderIso.apply_symm_apply,
            ← hq1, hq2]
      · refine ⟨2 * m + 1, ?_, ?_⟩
        · rw [← interleaveEnd_snd_eval (interleaveEnd.symm p) m, OrderIso.apply_symm_apply]
          exact hm
        · apply interleaveEnd.injective
          rw [OrderIso.apply_symm_apply, interleaveEnd_update_odd, OrderIso.apply_symm_apply,
            ← hq2, hq1],
    fun p => by
      show Part.some botEnd = (upPair (Part.some botEnd) (Part.some botEnd)).map _
      rw [upPair_some, Part.map_some, ← interleaveEnd_bot, OrderIso.symm_apply_apply]⟩
  left_inv x := interleaveEnd.symm_apply_apply x
  right_inv p := interleaveEnd.apply_symm_apply p

/-- `Statement:` an `endBitFlip` step rises in the pointwise order. -/
theorem endBitFlip_le {x y : End} (h : endBitFlip x y) : x ≤ y := by
  obtain ⟨k, hk, rfl⟩ := h
  intro n
  by_cases hn : n = k
  · subst hn; simp [hk]
  · simp [hn]

/-- `Statement:` reachability under `endBitFlip` rises in the pointwise order. -/
theorem rtg_endBitFlip_le {x y : End} (h : Relation.ReflTransGen endBitFlip x y) : x ≤ y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact ih.trans (endBitFlip_le hbc)

/-- `Statement:` CONTROL: `endFlipMotion` meets `ADoubling`, loops, fires the corner and does not
    climb; with ⊥ of `End` a fixed pole and one flip above it, reachability carries the prefix order
    on `Bool` words, `[]` at ⊥ of `End`. -/
theorem endFlip_doubling_control : endFlipMotion.ADoubling ∧ endFlipMotion.Loop ∧
    endFlipMotion.Corner ∧ ¬ endFlipMotion.Climb ∧
    ∃ f : List Bool → End, f [] = botEnd ∧
      ∀ l l', Relation.ReflTransGen endFlipMotion.step (f l) (f l') ↔ l <+: l' := by
  have hloop : endFlipMotion.Loop :=
    ⟨botEnd, Function.update botEnd 0 1, Part.mem_some _, ⟨0, rfl, rfl⟩,
      fun h => by have := congrFun h 0; simp [botEnd] at this, Part.mem_some _⟩
  refine ⟨⟨endFlipIsoAProd⟩, hloop, loop_corner _ hloop, ?_, ?_⟩
  · rintro ⟨y, b, z, hy, -, hz, -, hzy⟩
    exact hzy ((Part.mem_some_iff.1 hz).trans (Part.mem_some_iff.1 hy).symm)
  · refine tree_of_aDoubling_pole endFlipIsoAProd botEnd interleaveEnd_bot
      ⟨Function.update botEnd 0 1, .single ⟨0, rfl, rfl⟩, fun h => ?_⟩
    have := rtg_endBitFlip_le h 0
    simp [botEnd] at this

/-- `Statement:` the motion on `Comb`: UP the identity, a step `≤`. -/
def combLeMotion : Motion Comb := ofTotal id (fun _ => rfl) (· ≤ ·)

/-- `Statement:` in a preorder, reachability under `≤` is `≤`; both directions. -/
theorem rtg_le_iff_le {P : Type} [Preorder P] (x y : P) :
    Relation.ReflTransGen (· ≤ ·) x y ↔ x ≤ y :=
  ⟨fun h => by
    induction h with
    | refl => exact le_rfl
    | tail _ hbc ih => exact ih.trans hbc, fun h => .single h⟩

/-- `Statement:` CONTROL: `combLeMotion` does not meet `ADoubling`. -/
theorem comb_not_aDoubling : ¬ combLeMotion.ADoubling := by
  rintro ⟨e⟩
  obtain ⟨f, -, hf⟩ := tree_of_aDoubling_root e ⊥ (fun x => (rtg_le_iff_le _ _).2 bot_le)
    (Comb.atom 0) (fun h => Comb.noConfusion (le_bot_iff.1 ((rtg_le_iff_le _ _).1 h)))
  exact comb_no_BTree.false (OrderEmbedding.ofMapLEIff (fun t => f t.val) fun t t' =>
    ((rtg_le_iff_le _ _).symm.trans (hf t.val t'.val)).trans (btree_le_iff t t').symm)

/-- `Statement:` the all-`1` point of `End`. -/
def topEnd : End := fun _ => 1

/-- `Statement:` the motion on `End` in which every point steps to `topEnd`. -/
def endTopMotion : Motion End := ofFun (fun _ => topEnd)

/-- `Statement:` `interleaveEnd topEnd = (topEnd, topEnd)`. -/
theorem interleaveEnd_topEnd : interleaveEnd topEnd = (topEnd, topEnd) := by
  rw [interleaveEnd_apply]; rfl

/-- `Statement:` `interleaveEnd` is an isomorphism of `endTopMotion` onto its lockstep square. -/
def endTopIsoProd : StrictIso endTopMotion (endTopMotion.prod endTopMotion) where
  hom := ⟨interleaveEnd, fun {x y} (h : y = topEnd) => by
      subst h; rw [interleaveEnd_topEnd]; exact ⟨rfl, rfl⟩,
    fun x => by
      show upPair (Part.some _) (Part.some _) = (Part.some x).map _
      rw [upPair_some, Part.map_some]; rfl⟩
  inv := ⟨interleaveEnd.symm, fun {p q} (h : q.1 = topEnd ∧ q.2 = topEnd) => by
      show interleaveEnd.symm q = topEnd
      rw [OrderIso.symm_apply_eq, interleaveEnd_topEnd]; exact Prod.ext h.1 h.2,
    fun p => by
      show Part.some _ = (upPair (Part.some p.1) (Part.some p.2)).map _
      rw [upPair_some, Part.map_some]; rfl⟩
  left_inv x := interleaveEnd.symm_apply_apply x
  right_inv p := interleaveEnd.apply_symm_apply p

/-- `Statement:` in `endTopMotion`, `x` reaches only `x` and `topEnd`. -/
theorem rtg_endTop {x y : End} (h : Relation.ReflTransGen endTopMotion.step x y) :
    y = x ∨ y = topEnd := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hbc _ => exact Or.inr hbc

/-- `Statement:` ⊥ of `End` is not `topEnd`. -/
theorem botEnd_ne_topEnd : botEnd ≠ topEnd := fun h => by
  have := congrFun h 0; simp [botEnd, topEnd] at this

/-- `Statement:` CONTROL: `endTopMotion` meets `Doubling` (lockstep) with ⊥ of `End` a fixed pole and
    `NonDegenerateAt` ⊥ of `End`, and no map from `Bool` words carries reachability as the prefix
    order. -/
theorem sync_no_bridge :
    endTopMotion.Doubling ∧ FixedPole endTopIsoProd botEnd ∧ endTopMotion.NonDegenerateAt botEnd ∧
    ¬ ∃ f : List Bool → End,
      ∀ l l', Relation.ReflTransGen endTopMotion.step (f l) (f l') ↔ l <+: l' := by
  refine ⟨⟨endTopIsoProd⟩, interleaveEnd_bot, ⟨topEnd, .single rfl, fun h => ?_⟩, ?_⟩
  · rcases rtg_endTop h with h | h
    · exact botEnd_ne_topEnd h
    · exact botEnd_ne_topEnd h
  · rintro ⟨f, hf⟩
    have h01 : ¬ Relation.ReflTransGen endTopMotion.step (f [false]) (f []) :=
      fun h => absurd ((hf _ _).1 h) (by decide)
    have h12 : ¬ Relation.ReflTransGen endTopMotion.step (f [false, false]) (f [false]) :=
      fun h => absurd ((hf _ _).1 h) (by decide)
    have r01 := (hf [] [false]).2 (by decide)
    have r12 := (hf [false] [false, false]).2 (by decide)
    rcases rtg_endTop r01 with e1 | e1
    · exact h01 (e1 ▸ .refl)
    · rcases rtg_endTop r12 with e2 | e2
      · exact h12 (e2 ▸ .refl)
      · exact h12 (by rw [e1, e2])

/-- `Statement:` in `endTopMotion`, ⊥ of `End` reaches itself and `topEnd`, and in its lockstep square
    (⊥, ⊥) does not reach (⊥, `topEnd`): lockstep reachability is not the product of reachabilities. -/
theorem sync_rtg_not_product :
    (Relation.ReflTransGen endTopMotion.step botEnd botEnd ∧
      Relation.ReflTransGen endTopMotion.step botEnd topEnd) ∧
    ¬ Relation.ReflTransGen (endTopMotion.prod endTopMotion).step (botEnd, botEnd)
      (botEnd, topEnd) := by
  refine ⟨⟨.refl, .single rfl⟩, fun h => ?_⟩
  have key : ∀ q, Relation.ReflTransGen (endTopMotion.prod endTopMotion).step (botEnd, botEnd) q →
      q = (botEnd, botEnd) ∨ q = (topEnd, topEnd) := by
    intro q hq
    induction hq with
    | refl => exact Or.inl rfl
    | tail _ hbc _ => exact Or.inr (Prod.ext hbc.1 hbc.2)
  rcases key _ h with e | e
  · exact botEnd_ne_topEnd (congrArg Prod.snd e).symm
  · exact botEnd_ne_topEnd (congrArg Prod.fst e)

open NNReal

/-- `Statement:` `ℕ → ℝ≥0` is order-isomorphic to its square, by the even/odd split. -/
def nnDouble : (ℕ → ℝ≥0) ≃o (ℕ → ℝ≥0) × (ℕ → ℝ≥0) :=
  (reindexOrderIso ℝ≥0 Equiv.natSumNatEquivNat).trans (sumSplitOrderIso ℝ≥0 ℕ ℕ)

/-- `Statement:` ⊥ of `ℕ → ℝ≥0` has no cover. -/
theorem nn_not_botCovered : ¬ BotCovered (ℕ → ℝ≥0) := by
  rintro ⟨a, ha⟩
  obtain ⟨n, hn⟩ : ∃ n, (⊥ : ℕ → ℝ≥0) n < a n := (Pi.lt_def.1 ha.lt).2
  have hpos : 0 < a n := hn
  refine ha.2 (c := fun i => a i / 2) ?_ ?_
  · exact Pi.lt_def.2 ⟨fun i => zero_le, n, by simpa using half_pos hpos⟩
  · exact Pi.lt_def.2 ⟨fun i => half_le_self (zero_le), n, half_lt_self hpos⟩

/-- `Statement:` `ℕ → ℝ≥0` is not strongly atomic. -/
theorem nn_not_stronglyAtomic : ¬ IsStronglyAtomic (ℕ → ℝ≥0) := by
  intro h
  have hlt : (⊥ : ℕ → ℝ≥0) < fun _ => 1 :=
    Pi.lt_def.2 ⟨fun _ => zero_le, 0, by simp⟩
  obtain ⟨x, hx, -⟩ := h.exists_covBy_le_of_lt ⊥ _ hlt
  exact nn_not_botCovered ⟨x, hx⟩

/-- `Statement:` `ℕ → ℝ≥0` is not strongly atomic and ⊥ of it has no cover, and `BTree` order-embeds
    with root at ⊥, by `doubling_forces_btree` at `nnDouble`. -/
theorem nn_tree : ¬ IsStronglyAtomic (ℕ → ℝ≥0) ∧ ¬ BotCovered (ℕ → ℝ≥0) ∧
    ∃ f : BTree ↪o (ℕ → ℝ≥0), f (BTree.mk []) = ⊥ :=
  ⟨nn_not_stronglyAtomic, nn_not_botCovered, doubling_forces_btree nnDouble (fun _ => 1)
    (fun h => by have := congrFun h 0; simp at this)⟩

/-- `Statement:` `Comb` is strongly atomic and embeds no `BTree`. -/
theorem comb_atomic_no_tree : IsStronglyAtomic Comb ∧ IsEmpty (BTree ↪o Comb) :=
  ⟨comb_stronglyAtomic, comb_no_BTree⟩

open Ordinal in
/-- `Statement:` ε₀ is not ⊥ of `Ordinal` (`epsilon0_ne_bot`), and `Ordinal` embeds no `BTree`, no
    order embedding of its square, and is not order-isomorphic to its square. -/
theorem epsilon0_control :
    (ε₀ : Ordinal.{0}) ≠ ⊥ ∧ IsEmpty (BTree ↪o Ordinal.{0}) ∧
      IsEmpty (Ordinal.{0} × Ordinal.{0} ↪o Ordinal.{0}) ∧
      IsEmpty (Ordinal.{0} ≃o Ordinal.{0} × Ordinal.{0}) := by
  have hne : (ε₀ : Ordinal.{0}) ≠ ⊥ := epsilon0_ne_bot
  have hnt : IsEmpty (BTree ↪o Ordinal.{0}) := linear_no_btree
  have hemb : IsEmpty (Ordinal.{0} × Ordinal.{0} ↪o Ordinal.{0}) := ⟨fun j => by
    obtain ⟨f, -⟩ := square_embed_forces_btree j ε₀ hne
    exact hnt.false f⟩
  exact ⟨hne, hnt, hemb, ⟨fun e => hemb.false e.symm.toOrderEmbedding⟩⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms combShift
#print axioms combShift_le_iff
#print axioms combShiftEmb
#print axioms combShift_sup
#print axioms combShift_selfCopyRef
#print axioms selfCopy_at_bot_not_forcing
#print axioms combSelfApp
#print axioms comb_bot_quine
#print axioms comb_quine_and_no_tree
#print axioms coverQuineAtomHost
#print axioms comb_coverHost
#print axioms natSCR_strictMono
#print axioms linear_no_btree
#print axioms sqC
#print axioms sqTree
#print axioms sqC_le_iff
#print axioms sqC_not_le_bot
#print axioms sqTree_le_iff
#print axioms square_embed_forces_btree
#print axioms doubling_forces_btree
#print axioms pole_is_pair
#print axioms dblShift
#print axioms dblShift_bot
#print axioms dblShift_not_surj
#print axioms btree_down_chain
#print axioms btree_no_square_embed
#print axioms dblSeq
#print axioms dblProj
#print axioms dblProj_mono
#print axioms dblProj_bot
#print axioms dblProj_sup
#print axioms dblProj_seq
#print axioms dblProj_finset_sup
#print axioms dblSeq_independent
#print axioms end_doubling_btree
#print axioms comb_not_doubling
#print axioms subsingletonDouble
#print axioms unit_control
#print axioms WBF
#print axioms wbf_min
#print axioms wbf_not_doubling
#print axioms wbf_independent
#print axioms wbf_btree
#print axioms poleCellDouble
#print axioms oneInTwo
#print axioms combSq
#print axioms combSq_le_iff
#print axioms combSqEmb
#print axioms comb_local_pair_no_tree
#print axioms BotWedge
#print axioms botWedge_orderBot
#print axioms wedge_double_impossible_of_sup
#print axioms ChainFan
#print axioms ChainFan.le
#print axioms ChainFan.le_def
#print axioms chainFanToWedge
#print axioms chainFanToWedge_le_iff
#print axioms chainFanToWedge_surj
#print axioms chainFanWedge
#print axioms chainFanWedge_bot
#print axioms chainFan_upchains
#print axioms chainFan_no_btree
#print axioms wedge_double_no_tree
#print axioms end_not_wedge_double
#print axioms fin3_exchange_no_tree
#print axioms Q11
#print axioms q11Neg
#print axioms q11Lo
#print axioms q11Hi
#print axioms q11_exchange_no_tree
#print axioms setNat_exchange_tree
#print axioms pole_identity_collapses
#print axioms chartSwap
#print axioms chartSwap_props
#print axioms fin3_twoChart_no_tree
#print axioms ternFwd
#print axioms ternRev
#print axioms ternFwd_bounds
#print axioms ternRev_bounds
#print axioms tern_le_iff
#print axioms twoChartCode
#print axioms q11_twoChart_tree
#print axioms endBitFlip
#print axioms endFlipMotion
#print axioms interleaveEnd_fst_eval
#print axioms interleaveEnd_snd_eval
#print axioms interleaveEnd_update_even
#print axioms interleaveEnd_update_odd
#print axioms endFlipIsoAProd
#print axioms endBitFlip_le
#print axioms rtg_endBitFlip_le
#print axioms endFlip_doubling_control
#print axioms combLeMotion
#print axioms rtg_le_iff_le
#print axioms comb_not_aDoubling
#print axioms topEnd
#print axioms endTopMotion
#print axioms interleaveEnd_topEnd
#print axioms endTopIsoProd
#print axioms rtg_endTop
#print axioms botEnd_ne_topEnd
#print axioms sync_no_bridge
#print axioms sync_rtg_not_product
#print axioms nnDouble
#print axioms nn_not_botCovered
#print axioms nn_not_stronglyAtomic
#print axioms nn_tree
#print axioms comb_atomic_no_tree
#print axioms epsilon0_control
end PurityCheck
