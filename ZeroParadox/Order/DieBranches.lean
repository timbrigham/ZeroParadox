-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): if L is carried as the prefix order on Bool words by some f, then sending each s : ℕ → Bool to its branch of nodes is injective, L-increasing in depth, and L-incomparable past the first difference; composed with tree_of_square. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Die
import ZeroParadox.Valuation.DepthIsWait
import Mathlib.Topology.MetricSpace.PiNat
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
§ IV–VI add topology, metric, ℤ_[2]; no map `α → (ℕ → Bool)`, no order on branches (`wordBranch_incomparable`).
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

/-! ### § IV. The branch map: shift square, topology, metric, ℤ_[2]
`Reading:` the prefix map from Cantor space to the ends of the binary tree is a homeomorphism
(Ramírez Maluendas–Valdez, arXiv:1603.00503, Remark 1.2; compare Mathlib `CantorScheme.inducedMap`);
for the tree of a degree-`d` sausage shift, the end space is a Cantor set on which the shift polynomial
acts conjugately to the one-sided shift on `d` letters (Calegari, arXiv:2105.11265, Cor. 9.7); a
boundary distance is the weight `ε(v) = diam [v]` of the meet vertex (Pearson–Bellissard,
arXiv:0802.1336, Prop. 6 and its proof, App. A.2). -/

/-- `Statement:` `tapePrefix (tapeCons b s) (n + 1) = b :: tapePrefix s n`. -/
theorem tapePrefix_tapeCons (b : Bool) (s : ℕ → Bool) (n : ℕ) :
    tapePrefix (tapeCons b s) (n + 1) = b :: tapePrefix s n := by
  simp only [tapePrefix, List.ofFn_succ]
  rfl

section Square
variable {α : Type*} (j : α × α → α) (r a : α)

/-- `Statement:` the layer on node sequences: depth `0` is `r`, depth `n + 1` is
`j (Motion.sqCell j r a b, β n)`. -/
def sqLayer (b : Bool) (β : ℕ → α) : ℕ → α := fun n => match n with
  | 0 => r
  | n + 1 => j (Motion.sqCell j r a b, β n)

/-- `Statement:` depth `n + 1` of the `sqWord` branch of `tapeCons b s` is
`j (sqCell b, depth n of the branch of s)`. -/
theorem wordBranch_tapeCons (b : Bool) (s : ℕ → Bool) (n : ℕ) :
    wordBranch (Motion.sqWord j r a) (tapeCons b s) (n + 1) =
      j (Motion.sqCell j r a b, wordBranch (Motion.sqWord j r a) s n) := by
  simp only [wordBranch, tapePrefix_tapeCons]; rfl

/-- `Statement:` the `sqWord` branch map sends prepend-`b` on tapes to `sqLayer b` on branches.
`Reading:` this follows from the construction `sqWord`, not from the prefix-order hypothesis alone
(the `flipSecond` control below). -/
theorem sqWord_branch_semiconj_cons (b : Bool) :
    Function.Semiconj (wordBranch (Motion.sqWord j r a)) (tapeCons b) (sqLayer j r a b) :=
  fun s => by
    funext n
    cases n with
    | zero => rfl
    | succ n => exact wordBranch_tapeCons j r a b s n

/-- `Statement:` for any left inverse `g` of `j`, the `sqWord` branch map sends the tail shift on tapes
to `β ↦ fun n => (g (β (n + 1))).2` on branches. -/
theorem sqWord_branch_semiconj_tail (g : α → α × α) (hg : ∀ p, g (j p) = p) :
    Function.Semiconj (wordBranch (Motion.sqWord j r a)) (fun s n => s (n + 1))
      (fun β n => (g (β (n + 1))).2) := fun s => by
  funext n
  have hs : s = tapeCons (s 0) (fun n => s (n + 1)) := by funext k; cases k <;> rfl
  show _ = (g (wordBranch (Motion.sqWord j r a) s (n + 1))).2
  conv_rhs => rw [hs, wordBranch_tapeCons, hg]

end Square

/-- `Statement:` the involution on `Bool` words negating the second letter. -/
def flipSecond : List Bool → List Bool
  | [] => []
  | [x] => [x]
  | x :: y :: l => x :: (!y) :: l

/-- `Statement:` `flipSecond l <+: flipSecond l' ↔ l <+: l'`. -/
theorem flipSecond_prefix_iff (l l' : List Bool) : flipSecond l <+: flipSecond l' ↔ l <+: l' := by
  have inv : ∀ l, flipSecond (flipSecond l) = l := fun l => by
    match l with
    | [] => rfl
    | [x] => rfl
    | x :: y :: l => simp [flipSecond]
  have mono : ∀ {l l' : List Bool}, l <+: l' → flipSecond l <+: flipSecond l' := by
    intro l l' h
    obtain ⟨t, rfl⟩ := h
    match l, t with
    | [], t => exact List.nil_prefix
    | [x], [] => exact List.prefix_refl _
    | [x], y :: t => exact ⟨(!y) :: t, rfl⟩
    | x :: y :: l, t => exact ⟨t, by simp [flipSecond]⟩
  exact ⟨fun h => by simpa [inv] using mono h, mono⟩

-- Statement: CONTROL, `sqWord ∘ flipSecond` also carries `L` as the prefix order, and no `c'` makes
-- `j (c', ·)` its prepend-`b` square at every depth.
example {α : Type*} (L : α → α → Prop) (hrefl : ∀ x, L x x)
    (htr : ∀ x y z, L x y → L y z → L x z) (j : α × α → α)
    (hj : ∀ p q, L (j p) (j q) ↔ L p.1 q.1 ∧ L p.2 q.2) (r a : α) (hr : L r (j (r, r)))
    (hra : L r a) (hna : ¬ L a r) (b : Bool) :
    (∀ l l', L (Motion.sqWord j r a (flipSecond l)) (Motion.sqWord j r a (flipSecond l')) ↔
      l <+: l') ∧
    ¬ ∃ c' : α, ∀ s : ℕ → Bool, ∀ n,
      wordBranch (fun l => Motion.sqWord j r a (flipSecond l)) (tapeCons b s) (n + 1) =
        j (c', wordBranch (fun l => Motion.sqWord j r a (flipSecond l)) s n) := by
  refine ⟨fun l l' => by
    rw [Motion.sqWord_le_iff L hrefl htr j hj r a hr hra hna, flipSecond_prefix_iff], ?_⟩
  rintro ⟨c', hc⟩
  have h := hc (fun _ => false) 1
  have e1 : wordBranch (fun l => Motion.sqWord j r a (flipSecond l)) (tapeCons b (fun _ => false)) 2 =
      j (Motion.sqCell j r a b, j (Motion.sqCell j r a true, r)) := rfl
  have e2 : wordBranch (fun l => Motion.sqWord j r a (flipSecond l)) (fun _ => false) 1 =
      j (Motion.sqCell j r a false, r) := rfl
  rw [e1, e2] at h
  have hL0 : L (j (Motion.sqCell j r a b, j (Motion.sqCell j r a true, r)))
      (j (c', j (Motion.sqCell j r a false, r))) := by
    rw [h]; exact hrefl _
  have hL2 := (hj _ _).1 ((hj _ _).1 hL0).2
  exact absurd ((Motion.sqCell_le_iff L hrefl j hj r a hna true false).1 hL2.1) (by decide)

section Topo
variable {α : Type*} (L : α → α → Prop) (f : List Bool → α)
  (hf : ∀ l l', L (f l) (f l') ↔ l <+: l')

/-- `Statement:` for any topology on `α`, `wordBranch f` is continuous into `ℕ → α` (product
topology); no hypothesis on `f`. -/
theorem continuous_wordBranch [TopologicalSpace α] : Continuous (wordBranch f) := by
  refine continuous_pi fun n => ?_
  have : (fun s : ℕ → Bool => wordBranch f s n) =
      (fun w : Fin n → Bool => f (List.ofFn w)) ∘ (fun s i => s i) := rfl
  rw [this]
  exact continuous_of_discreteTopology.comp (continuous_pi fun i => continuous_apply _)

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order, then for any T2 topology on `α`, `wordBranch f`
is a closed embedding into `ℕ → α` (product topology). `Reading:` a transport: continuity is automatic
and the rest is Mathlib `Continuous.isClosedEmbedding`. -/
theorem wordBranch_isClosedEmbedding [TopologicalSpace α] [T2Space α] :
    Topology.IsClosedEmbedding (wordBranch f) :=
  (continuous_wordBranch f).isClosedEmbedding (wordBranch_injective L f hf)

end Topo

-- Statement: CONTROL, with the indiscrete topology on `List Bool`, the identity tree (`L` the prefix
-- order) has a branch map that is not an embedding.
example : ¬ @Topology.IsEmbedding (ℕ → Bool) (ℕ → List Bool) _ (@Pi.topologicalSpace ℕ _ fun _ => ⊤)
    (wordBranch (fun l : List Bool => l)) := by
  let _ : TopologicalSpace (List Bool) := ⊤
  intro h
  have hopen : IsOpen ((fun s : ℕ → Bool => s 0) ⁻¹' {true}) :=
    (isOpen_discrete _).preimage (continuous_apply 0)
  rw [h.isInducing.isOpen_iff] at hopen
  obtain ⟨U, hU, hpre⟩ := hopen
  have hU' : U = ∅ ∨ U = Set.univ := by
    have : IndiscreteTopology (ℕ → List Bool) := by
      constructor
      show (Pi.topologicalSpace : TopologicalSpace (ℕ → List Bool)) = ⊤
      simp only [Pi.topologicalSpace]
      show (⨅ i, TopologicalSpace.induced (fun f : ℕ → List Bool => f i) ⊤) = ⊤
      simp [induced_top]
    exact (IndiscreteTopology.isOpen_iff U).1 hU
  rcases hU' with rfl | rfl
  · have := congrArg (fun S => (fun _ => true : ℕ → Bool) ∈ S) hpre
    simp at this
  · have := congrArg (fun S => (fun _ => false : ℕ → Bool) ∈ S) hpre
    simp at this

section Metric
attribute [local instance] PiNat.dist
variable {α : Type*} (L : α → α → Prop) (f : List Bool → α)
  (hf : ∀ l l', L (f l) (f l') ↔ l <+: l')

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order, `wordBranch f s n = wordBranch f t n` iff `s`,
`t` agree below `n`; both directions. -/
theorem wordBranch_eq_iff (s t : ℕ → Bool) (n : ℕ) :
    wordBranch f s n = wordBranch f t n ↔ ∀ i, i < n → s i = t i := by
  refine ⟨fun h => ?_, wordBranch_eq_of_agree f s t n⟩
  exact ((wordBranch_le_iff L f hf s t n n).1
    (by rw [h]; exact (hf _ _).2 (List.prefix_refl _))).2

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order and `s ≠ t`, the branches first differ one depth
after the tapes: `PiNat.firstDiff (wordBranch f s) (wordBranch f t) = PiNat.firstDiff s t + 1`. -/
theorem firstDiff_wordBranch {s t : ℕ → Bool} (hst : s ≠ t) :
    PiNat.firstDiff (wordBranch f s) (wordBranch f t) = PiNat.firstDiff s t + 1 := by
  have hc : wordBranch f s ≠ wordBranch f t := fun h => hst (wordBranch_injective L f hf h)
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have := PiNat.apply_eq_of_lt_firstDiff hlt
    rw [wordBranch_eq_iff L f hf] at this
    exact PiNat.apply_firstDiff_ne hst (this _ (Nat.lt_succ_self _))
  · by_contra hlt
    push Not at hlt
    apply PiNat.apply_firstDiff_ne hc
    rw [wordBranch_eq_iff L f hf]
    intro i hi
    exact PiNat.apply_eq_of_lt_firstDiff (by omega)

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order, `wordBranch f` scales `PiNat.dist` by exactly
`1 / 2`. -/
theorem dist_wordBranch (s t : ℕ → Bool) :
    dist (wordBranch f s) (wordBranch f t) = dist s t / 2 := by
  by_cases hst : s = t
  · subst hst; simp [PiNat.dist_self]
  · have hc : wordBranch f s ≠ wordBranch f t := fun h => hst (wordBranch_injective L f hf h)
    rw [PiNat.dist_eq_of_ne hc, PiNat.dist_eq_of_ne hst, firstDiff_wordBranch L f hf hst, pow_succ]
    ring

include hf in
/-- `Statement:` if `f` carries `L` as the prefix order, dropping depth `0` of each branch gives an
isometry for `PiNat.dist`. -/
theorem dist_wordBranch_succ (s t : ℕ → Bool) :
    dist (fun n => wordBranch f s (n + 1)) (fun n => wordBranch f t (n + 1)) = dist s t := by
  by_cases hst : s = t
  · subst hst; simp [PiNat.dist_self]
  · have hc : (fun n => wordBranch f s (n + 1)) ≠ (fun n => wordBranch f t (n + 1)) := by
      intro h
      apply hst; funext k
      have := congrFun h k
      rw [wordBranch_eq_iff L f hf] at this
      exact this k (Nat.lt_succ_self k)
    rw [PiNat.dist_eq_of_ne hc, PiNat.dist_eq_of_ne hst]
    congr 1
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have := PiNat.apply_eq_of_lt_firstDiff hlt
      beta_reduce at this
      rw [wordBranch_eq_iff L f hf] at this
      exact PiNat.apply_firstDiff_ne hst (this _ (Nat.lt_succ_self _))
    · by_contra hlt
      push Not at hlt
      apply PiNat.apply_firstDiff_ne hc
      rw [wordBranch_eq_iff L f hf]
      intro i hi
      exact PiNat.apply_eq_of_lt_firstDiff (by omega)

include hf in
-- Statement: CONTROL, `wordBranch f` is not an isometry for `PiNat.dist`.
example : ¬ ∀ s t, dist (wordBranch f s) (wordBranch f t) = dist s t := by
  intro h
  have hne : (fun _ => false : ℕ → Bool) ≠ fun _ => true := fun e => by
    have := congrFun e 0; simp at this
  have h1 := h (fun _ => false) (fun _ => true)
  rw [dist_wordBranch L f hf] at h1
  have hpos : 0 < dist (fun _ => false : ℕ → Bool) (fun _ => true) := by
    rw [PiNat.dist_eq_of_ne hne]; positivity
  linarith

end Metric

section Composite
variable {α : Type*} (j : α × α → α) (r a : α)

/-- `Statement:` the composite `x ↦ wordBranch (sqWord j r a) (tapeIso (padicEndHomeo x))` sends `2 * x`
on ℤ_[2] to `sqLayer false` on branches. -/
theorem padic_sqWord_branch_semiconj :
    Function.Semiconj
      (fun x : ℤ_[2] => wordBranch (Motion.sqWord j r a) (tapeIso (padicEndHomeo x)))
      (fun x => 2 * x) (sqLayer j r a false) := fun x => by
  show wordBranch (Motion.sqWord j r a) (tapeIso (padicEndHomeo (2 * x))) = _
  rw [padicEndHomeo_semiconj.eq, tapeIso_boundaryDouble]
  exact sqWord_branch_semiconj_cons j r a false _

end Composite

section Relabel
variable {α : Type*} (L : α → α → Prop) (hrefl : ∀ x, L x x)
  (htr : ∀ x y z, L x y → L y z → L x z)
  (j : α × α → α) (hj : ∀ p q, L (j p) (j q) ↔ L p.1 q.1 ∧ L p.2 q.2)
  (r a : α) (hr : L r (j (r, r))) (hra : L r a) (hna : ¬ L a r)

/-- `Statement:` `l.map not <+: l'.map not ↔ l <+: l'`. -/
theorem map_not_prefix_iff (l l' : List Bool) : l.map not <+: l'.map not ↔ l <+: l' :=
  ⟨fun h => by simpa [Function.comp_def] using h.map not, fun h => h.map not⟩

include hrefl htr hj hr hra hna in
/-- `Statement:` the `not`-relabelled tree `l ↦ sqWord j r a (l.map not)` also carries `L` as the
prefix order. -/
theorem notTree_hf (l l' : List Bool) :
    L (Motion.sqWord j r a (l.map not)) (Motion.sqWord j r a (l'.map not)) ↔ l <+: l' := by
  rw [Motion.sqWord_le_iff L hrefl htr j hj r a hr hra hna, map_not_prefix_iff]

/-- `Statement:` the branch of `s` in the `not`-relabelled tree is the `sqWord` branch of
`fun n => !s n`. `Reading:` both trees carry `L` as the prefix order (`notTree_hf`), so which branch
is the image of 0 of ℤ_[2] (the branch whose tape is ⊥ of `ℕ → Bool`) is a labelling convention. -/
theorem notTree_branch (s : ℕ → Bool) :
    wordBranch (fun l => Motion.sqWord j r a (l.map not)) s =
      wordBranch (Motion.sqWord j r a) (fun n => !s n) := by
  funext n
  simp only [wordBranch, tapePrefix, List.map_ofFn]
  rfl

include hrefl htr hj hr hra hna in
/-- `Statement:` `L` runs from depth `n` of the `sqWord` branch of `s` to depth `n + 1` of its
`sqLayer false` image iff the first `n` bits of `s` are `false`; both directions. -/
theorem sqLayer_false_along_iff (s : ℕ → Bool) (n : ℕ) :
    L (wordBranch (Motion.sqWord j r a) s n)
        (sqLayer j r a false (wordBranch (Motion.sqWord j r a) s) (n + 1)) ↔
      ∀ i, i < n → s i = false := by
  rw [← congrFun (sqWord_branch_semiconj_cons j r a false s) (n + 1),
    wordBranch_le_iff L _ (Motion.sqWord_le_iff L hrefl htr j hj r a hr hra hna)]
  constructor
  · rintro ⟨-, h⟩
    intro i hi
    induction i with
    | zero => exact h 0 (by omega)
    | succ k ih => rw [h (k + 1) hi]; exact ih (by omega)
  · intro h
    refine ⟨by omega, fun i hi => ?_⟩
    cases i with
    | zero => exact h 0 hi
    | succ k => rw [h _ hi]; exact (h k (by omega)).symm

end Relabel

/-! ### § V. The complement on ℤ_[2] -/

/-- `Statement:` `(-1 - x).appr n + x.appr n + 1 = 2 ^ n` on ℤ_[2]. -/
theorem appr_neg_one_sub_add (x : ℤ_[2]) (n : ℕ) :
    (-1 - x).appr n + x.appr n + 1 = 2 ^ n := by
  have hx := PadicInt.appr_lt x n
  have h : (-1 - x).appr n = 2 ^ n - 1 - x.appr n := by
    apply appr_two_eq_of _ _ _ (by omega)
    have hcast : (((2 ^ n - 1 - x.appr n : ℕ)) : ℤ_[2]) = 2 ^ n - 1 - (x.appr n : ℤ_[2]) := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [Nat.cast_sub (by omega), Nat.cast_sub h1]; push_cast; ring
    rw [hcast]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n x)
    exact ⟨-c - 1, by linear_combination -hc⟩
  omega

/-- `Statement:` the digit tape of `-1 - x` is the bitwise complement of the digit tape of `x`.
`Reading:` Black's two spheres (M. Black, "The Identity of Indiscernibles", Mind 61 (1952) 153–164,
p. 156: "every quality and relational characteristic of the one would also be a property of the
other"): the word tree's prefix order cannot tell the two branches apart (`map_not_prefix_automorphism`,
`sqWord_map_not_iff`), while the die's named start points `r`, `a` do separate them (the second CONTROL
in § VI); which of them carries 0 of ℤ_[2] is fixed by the choice of labelling. -/
theorem padicTape_neg_one_sub (x : ℤ_[2]) : padicTape (-1 - x) = fun n => !(padicTape x n) := by
  funext k
  have hy := appr_two_succ (-1 - x) k
  have hx := appr_two_succ x k
  have e0 := appr_neg_one_sub_add x k
  have e1 := appr_neg_one_sub_add x (k + 1)
  have hp : 0 < 2 ^ k := by positivity
  rw [pow_succ] at e1
  generalize padicTape (-1 - x) k = a at hy ⊢
  generalize padicTape x k = b at hx ⊢
  generalize (2 : ℕ) ^ k = P at *
  cases a <;> cases b <;> simp at hy hx ⊢ <;> omega

-- Statement: `x ↦ -1 - x` swaps 0 and -1 of ℤ_[2].
example : (-1 - (0 : ℤ_[2])) = -1 ∧ (-1 - (-1 : ℤ_[2])) = 0 := by constructor <;> ring

/-- `Statement:` `x ↦ -1 - x` on ℤ_[2] sends `x ↦ 2 * x` to `x ↦ 2 * x + 1`. -/
theorem neg_one_sub_semiconj_two_mul :
    Function.Semiconj (fun x : ℤ_[2] => -1 - x) (fun x => 2 * x) (fun x => 2 * x + 1) :=
  fun x => by ring

/-- `Statement:` the digit tape of `2 * x + 1` is prepend-`true` on the digit tape of `x`. -/
theorem padicTape_two_mul_add_one (x : ℤ_[2]) :
    padicTape (2 * x + 1) = tapeCons true (padicTape x) := by
  have e : 2 * x + 1 = -1 - 2 * (-1 - x) := by ring
  rw [e, padicTape_neg_one_sub, padicTape_two_mul, padicTape_neg_one_sub]
  funext n; cases n <;> simp [tapeCons]

/-- `Statement:` in the `not`-relabelled tree, `x ↦ wordBranch _ (padicTape x)` sends `2 * x + 1` on
ℤ_[2] to `sqLayer false` on branches. `Reading:` the swap is not INVARIANT: the doubling square of one
labelling is the `2 * x + 1` square of the other, with 0 and -1 of ℤ_[2] exchanged. -/
theorem padic_notTree_branch_semiconj {α : Type*} (j : α × α → α) (r a : α) :
    Function.Semiconj
      (fun x : ℤ_[2] => wordBranch (fun l => Motion.sqWord j r a (l.map not)) (padicTape x))
      (fun x => 2 * x + 1) (sqLayer j r a false) := fun x => by
  show wordBranch (fun l => Motion.sqWord j r a (l.map not)) (padicTape (2 * x + 1)) =
    sqLayer j r a false (wordBranch (fun l => Motion.sqWord j r a (l.map not)) (padicTape x))
  rw [notTree_branch, notTree_branch, padicTape_two_mul_add_one]
  have h : (fun n => !(tapeCons true (padicTape x) n)) = tapeCons false (fun n => !(padicTape x n)) := by
    funext n; cases n <;> rfl
  rw [h]
  exact sqWord_branch_semiconj_cons j r a false _

/-! ### § VI. The cell swap is a symmetry of the word tree -/

/-- `Statement:` `List.map not` is an involution on `Bool` words preserving and reflecting the prefix
order: an order automorphism of `(List Bool, <+:)`. -/
theorem map_not_prefix_automorphism :
    Function.Involutive (List.map not) ∧ ∀ l l' : List Bool, l.map not <+: l'.map not ↔ l <+: l' :=
  ⟨fun l => by simp [Function.comp_def], map_not_prefix_iff⟩

/-- `Statement:` under `Motion.sqWord_le_iff`'s hypotheses, the swap preserves and reflects `L` on the
image of `Motion.sqWord`. -/
theorem sqWord_map_not_iff {α : Type*} (L : α → α → Prop) (hrefl : ∀ x, L x x)
    (htr : ∀ x y z, L x y → L y z → L x z) (j : α × α → α)
    (hj : ∀ p q, L (j p) (j q) ↔ L p.1 q.1 ∧ L p.2 q.2) (r a : α) (hr : L r (j (r, r)))
    (hra : L r a) (hna : ¬ L a r) (l l' : List Bool) :
    L (Motion.sqWord j r a (l.map not)) (Motion.sqWord j r a (l'.map not)) ↔
      L (Motion.sqWord j r a l) (Motion.sqWord j r a l') := by
  rw [notTree_hf L hrefl htr j hj r a hr hra hna, Motion.sqWord_le_iff L hrefl htr j hj r a hr hra hna]

/-- `Statement:` a predicate on tapes invariant under the swap `s ↦ fun n => !s n` holds at the
all-false tape iff at the all-true tape. `Reading:` read "definable from the tree" as "invariant under
its automorphisms"; then no definable predicate separates the two branches (`notTree_branch` carries
the branch of one tape to that of the other). -/
theorem swap_not_separates (P : (ℕ → Bool) → Prop) (hP : ∀ s, P (fun n => !s n) ↔ P s) :
    P (fun _ => false) ↔ P (fun _ => true) :=
  (hP fun _ => false).symm

-- Statement: CONTROL, a predicate not invariant under the swap (`s 0 = false`) does separate them.
example : (fun s : ℕ → Bool => s 0 = false) (fun _ => false) ∧
    ¬ (fun s : ℕ → Bool => s 0 = false) (fun _ => true) := ⟨rfl, by decide⟩

-- Statement: CONTROL, the die's start points separate the two branches: depth 1 of the `sqWord`
-- branch of the all-false tape is `j (j (a, r), r)`, and given `¬ L a r` that of the all-true tape is not.
example {α : Type*} (L : α → α → Prop) (hrefl : ∀ x, L x x) (j : α × α → α)
    (hj : ∀ p q, L (j p) (j q) ↔ L p.1 q.1 ∧ L p.2 q.2) (r a : α) (hna : ¬ L a r) :
    let P : (ℕ → Bool) → Prop := fun s =>
      wordBranch (Motion.sqWord j r a) s 1 = j (j (a, r), r)
    P (fun _ => false) ∧ ¬ P (fun _ => true) := by
  intro P
  refine ⟨rfl, fun h => ?_⟩
  have h' : wordBranch (Motion.sqWord j r a) (fun _ => true) 1 = j (j (r, a), r) := rfl
  change wordBranch (Motion.sqWord j r a) (fun _ => true) 1 = j (j (a, r), r) at h
  rw [h'] at h
  have hL : L (j (j (a, r), r)) (j (j (r, a), r)) := by rw [h]; exact hrefl _
  exact hna ((hj _ _).1 ((hj _ _).1 hL).1).1

-- Reading: the two-pole contrast: add a join and ⊥ of `M` is picked out positively,
-- `(∀ x, join S x = x) ↔ S = bot` in any `ZPSemilattice M` (`da2_bottom_characterization`,
-- `ZeroParadox/Order/Snap.lean`); in the die the two cells are `L`-incomparable
-- (`Motion.sqCell_le_iff`), so this indistinguishability is a fact about the die's order on its word
-- tree, not every chart.

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
#print axioms tapePrefix_tapeCons
#print axioms sqLayer
#print axioms wordBranch_tapeCons
#print axioms sqWord_branch_semiconj_cons
#print axioms sqWord_branch_semiconj_tail
#print axioms flipSecond
#print axioms flipSecond_prefix_iff
#print axioms continuous_wordBranch
#print axioms wordBranch_isClosedEmbedding
#print axioms wordBranch_eq_iff
#print axioms firstDiff_wordBranch
#print axioms dist_wordBranch
#print axioms dist_wordBranch_succ
#print axioms padic_sqWord_branch_semiconj
#print axioms map_not_prefix_iff
#print axioms notTree_hf
#print axioms notTree_branch
#print axioms sqLayer_false_along_iff
#print axioms appr_neg_one_sub_add
#print axioms padicTape_neg_one_sub
#print axioms neg_one_sub_semiconj_two_mul
#print axioms padicTape_two_mul_add_one
#print axioms padic_notTree_branch_semiconj
#print axioms map_not_prefix_automorphism
#print axioms sqWord_map_not_iff
#print axioms swap_not_separates
end PurityCheck
