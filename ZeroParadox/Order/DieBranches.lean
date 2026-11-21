-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): if L is carried as the prefix order on Bool words by some f, then sending each s : ℕ → Bool to its branch of nodes is injective, L-increasing in depth, and L-incomparable past the first difference; composed with tree_of_square. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Die
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# If f carries L as the prefix order on Bool words, the map from s to its branch n ↦ f (first n bits of s) is injective, each branch is L-increasing, branches are L-incomparable past the first difference, and every L-increasing length-indexed node sequence is exactly one branch; under tree_of_square's hypotheses such f exists

## Engineer's Take

I get the feeling this shape is of the die as well. It's concurrently an object in motion and motion of
an object.

---

## Formal Overview (AI-assisted)
`Statement:` the § II lemmas hold for any relation `L` on any type `α` given `hf`, without `Motion.tree_of_square`
(`ZeroParadox/Die.lean`); only `square_branches` is its corollary, and it needs `L` reflexive and transitive.
No topology on `α` and no map from `α` to `ℕ → Bool` is stated.
-/

namespace ZeroParadox

/-! ### § I. Prefixes of a tape -/

/-- `Statement:` the first `n` bits of `s`; the same definition as `prefixOf`
(`ZeroParadox/Information/MaxEntropy.lean`), kept local so this file does not import that one. -/
def tapePrefix (s : ℕ → Bool) (n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => s i)

/-- `Statement:` `tapePrefix s m` is a prefix of `tapePrefix t n` iff `m ≤ n` and `s`, `t` agree below
`m`; both directions. -/
theorem tapePrefix_prefix_iff (s t : ℕ → Bool) (m n : ℕ) :
    tapePrefix s m <+: tapePrefix t n ↔ m ≤ n ∧ ∀ i, i < m → s i = t i := by
  rw [List.prefix_iff_getElem]
  simp only [tapePrefix, List.length_ofFn, List.getElem_ofFn]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨h, fun i hi => h' i hi⟩
  · rintro ⟨h, h'⟩; exact ⟨h, fun i hi => h' i hi⟩

/-! ### § II. Branches of a word tree -/

section Branch
variable {α : Type*} (L : α → α → Prop) (f : List Bool → α)
  (hf : ∀ l l', L (f l) (f l') ↔ l <+: l')

-- Reading: standard name: `f` is an order embedding of the full binary tree, whose set of infinite
-- branches is Cantor space.

/-- `Statement:` `wordBranch f s n = f (tapePrefix s n)`: depth `n` of `s` is the node of its first `n` bits. -/
def wordBranch (s : ℕ → Bool) (n : ℕ) : α := f (tapePrefix s n)

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order, `L (wordBranch f s m) (wordBranch f t n)` iff `m ≤ n` and `s`, `t` agree below `m`;
both directions. -/
theorem wordBranch_le_iff (s t : ℕ → Bool) (m n : ℕ) :
    L (wordBranch f s m) (wordBranch f t n) ↔ m ≤ n ∧ ∀ i, i < m → s i = t i := by
  rw [wordBranch, wordBranch, hf, tapePrefix_prefix_iff]

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order, `m ≤ n` implies `L (wordBranch f s m) (wordBranch f s n)`. -/
theorem wordBranch_mono (s : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    L (wordBranch f s m) (wordBranch f s n) :=
  (wordBranch_le_iff L f hf s s m n).2 ⟨h, fun _ _ => rfl⟩

/-- `Statement:` if `s`, `t` agree below `n`, `wordBranch f s n = wordBranch f t n`; no hypothesis on `f`. -/
theorem wordBranch_eq_of_agree (s t : ℕ → Bool) (n : ℕ) (h : ∀ i, i < n → s i = t i) :
    wordBranch f s n = wordBranch f t n := by
  unfold wordBranch tapePrefix; congr 1; exact List.ofFn_inj.2 (funext fun i => h i i.isLt)

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order, `s k ≠ t k`, `k < m` and `k < n`, then `L` holds in neither direction between
`wordBranch f s m` and `wordBranch f t n`. -/
theorem wordBranch_incomparable (s t : ℕ → Bool) (k : ℕ) (hk : s k ≠ t k) {m n : ℕ}
    (hm : k < m) (hn : k < n) :
    ¬ L (wordBranch f s m) (wordBranch f t n) ∧ ¬ L (wordBranch f t n) (wordBranch f s m) := by
  rw [wordBranch_le_iff L f hf, wordBranch_le_iff L f hf]
  exact ⟨fun h => hk (h.2 k hm), fun h => hk (h.2 k hn).symm⟩

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order, `s ↦ wordBranch f s` is one-to-one. -/
theorem wordBranch_injective : Function.Injective (wordBranch f) := by
  intro s t h
  funext k
  have : L (wordBranch f s (k+1)) (wordBranch f t (k+1)) := by
    rw [h]; exact (hf _ _).2 (List.prefix_refl _)
  exact ((wordBranch_le_iff L f hf s t _ _).1 this).2 k (Nat.lt_succ_self k)

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order, `w n` has length `n` and `L (f (w n)) (f (w (n + 1)))` for all `n`, then exactly one
`s` has `f (w n) = wordBranch f s n` for all `n`. -/
theorem wordBranch_surj (w : ℕ → List Bool) (hlen : ∀ n, (w n).length = n)
    (hinc : ∀ n, L (f (w n)) (f (w (n + 1)))) :
    ∃! s : ℕ → Bool, ∀ n, f (w n) = wordBranch f s n := by
  have hpre : ∀ m n, m ≤ n → w m <+: w n := by
    intro m n h
    induction h with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans ((hf _ _).1 (hinc _))
  let s : ℕ → Bool := fun k => (w (k+1))[k]'(by rw [hlen]; omega)
  have hw : ∀ n, w n = tapePrefix s n := by
    intro n
    apply List.ext_getElem (by simp [tapePrefix, hlen])
    intro i h1 h2
    simp only [tapePrefix, List.getElem_ofFn, s]
    obtain ⟨_, hg⟩ := List.prefix_iff_getElem.1 (hpre (i+1) n (by rw [hlen] at h1; omega))
    exact (hg i (by rw [hlen]; omega)).symm
  refine ⟨s, fun n => by rw [hw n]; rfl, fun t ht => wordBranch_injective L f hf ?_⟩
  funext n; rw [← ht n, hw n]; rfl

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order, for every `s` and `n` some `t ≠ s` has a different branch agreeing with that of `s`
at depths `0..n`. -/
theorem wordBranch_near (s : ℕ → Bool) (n : ℕ) :
    ∃ t, t ≠ s ∧ wordBranch f t ≠ wordBranch f s ∧ ∀ m, m ≤ n → wordBranch f t m = wordBranch f s m := by
  refine ⟨Function.update s n (!s n), fun h => ?_, fun h => ?_, fun m hm => ?_⟩
  · have := congrFun h n; simp at this
  · have := congrFun (wordBranch_injective L f hf h) n; simp at this
  · apply wordBranch_eq_of_agree
    intro i hi
    rw [Function.update_of_ne (by omega)]

end Branch

/-! ### § III. Composed with `tree_of_square` -/

/-- `Statement:` under the hypotheses of `Motion.tree_of_square`, some `c : (ℕ → Bool) → ℕ → α` is
injective, has `c s 0 = r`, is `L`-increasing in depth, is `L`-incomparable past a first difference,
and has for every `s`, `n` a different branch agreeing with `c s` at depths `0..n`; one way. -/
theorem square_branches {α : Type*} (L : α → α → Prop) (hrefl : ∀ x, L x x)
    (htr : ∀ x y z, L x y → L y z → L x z) (j : α × α → α)
    (hj : ∀ p q, L (j p) (j q) ↔ L p.1 q.1 ∧ L p.2 q.2) (r a : α) (hr : L r (j (r, r)))
    (hra : L r a) (hna : ¬ L a r) :
    ∃ c : (ℕ → Bool) → ℕ → α, Function.Injective c ∧ (∀ s, c s 0 = r) ∧
      (∀ s m n, m ≤ n → L (c s m) (c s n)) ∧
      (∀ s t k, s k ≠ t k → ∀ m n, k < m → k < n → ¬ L (c s m) (c t n)) ∧
      (∀ s n, ∃ t, c t ≠ c s ∧ ∀ m, m ≤ n → c t m = c s m) := by
  obtain ⟨f, hf0, hf⟩ := Motion.tree_of_square L hrefl htr j hj r a hr hra hna
  refine ⟨wordBranch f, wordBranch_injective L f hf, fun s => hf0,
    fun s m n h => wordBranch_mono L f hf s h,
    fun s t k hk m n hm hn => (wordBranch_incomparable L f hf s t k hk hm hn).1, fun s n => ?_⟩
  obtain ⟨t, -, h1, h2⟩ := wordBranch_near L f hf s n
  exact ⟨t, h1, h2⟩

/-- `Statement:` CONTROL, on a subsingleton carrier no `f : List Bool → α` carries any relation as
the prefix order. -/
theorem no_tree_subsingleton {α : Type*} [Subsingleton α] (L : α → α → Prop) :
    ¬ ∃ f : List Bool → α, ∀ l l', L (f l) (f l') ↔ l <+: l' := by
  rintro ⟨f, hf⟩
  have h1 := (hf [false] [false]).2 (List.prefix_refl _)
  rw [Subsingleton.elim (f [false]) (f [])] at h1
  exact absurd ((hf [false] []).1 (by rwa [Subsingleton.elim (f [false]) (f [])])) (by decide)

/-- `Statement:` CONTROL, on a finite carrier no `f : List Bool → α` carries any relation as the
prefix order; such an `f` is one-to-one, and `List Bool` is infinite. -/
theorem no_tree_finite {α : Type*} [Finite α] (L : α → α → Prop) :
    ¬ ∃ f : List Bool → α, ∀ l l', L (f l) (f l') ↔ l <+: l' := by
  rintro ⟨f, hf⟩
  refine not_injective_infinite_finite f fun l l' h => ?_
  have h1 : l <+: l' := (hf l l').1 (by rw [h]; exact (hf l' l').2 (List.prefix_refl _))
  have h2 : l' <+: l := (hf l' l).1 (by rw [h]; exact (hf l' l').2 (List.prefix_refl _))
  exact h1.eq_of_length (le_antisymm h1.length_le h2.length_le)

-- Statement: `no_tree_subsingleton` is the subsingleton case of `no_tree_finite`, and `Bool` is finite
-- and not a subsingleton.
example {α : Type*} [Subsingleton α] (L : α → α → Prop) :
    ¬ ∃ f : List Bool → α, ∀ l l', L (f l) (f l') ↔ l <+: l' := no_tree_finite L
example : Finite Bool ∧ ¬ Subsingleton Bool :=
  ⟨inferInstance, fun h => absurd (h.elim true false) (by decide)⟩

-- Statement: the `unitMotion` case, also stated in `ZeroParadox/DieCannotBe.lean`.
example : ¬ ∃ f : List Bool → Unit, ∀ l l',
    Relation.ReflTransGen ZeroParadox.Motion.unitMotion.step (f l) (f l') ↔ l <+: l' :=
  no_tree_subsingleton _

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms tapePrefix
#print axioms tapePrefix_prefix_iff
#print axioms wordBranch
#print axioms wordBranch_le_iff
#print axioms wordBranch_mono
#print axioms wordBranch_eq_of_agree
#print axioms wordBranch_incomparable
#print axioms wordBranch_injective
#print axioms wordBranch_surj
#print axioms wordBranch_near
#print axioms square_branches
#print axioms no_tree_subsingleton
#print axioms no_tree_finite
end PurityCheck
