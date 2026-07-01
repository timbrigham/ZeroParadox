import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic

set_option maxHeartbeats 1000000

/-!
# Kruskal's Tree Theorem (labeled) — finite rose trees are well-quasi-ordered

**Kruskal (1960):** the finite trees, ordered by homeomorphic (inf-preserving) embedding, form a
well-quasi-order (WQO): every infinite sequence of trees has `i < j` with `Tᵢ` embedding into `Tⱼ`.
Here we prove the **labeled** version — trees whose nodes carry labels from a WQO `(α, r)` — which is
the general theorem (the unlabeled case is `α = Unit`).

The proof is the Nash-Williams **minimal bad sequence** argument: a minimal bad sequence of trees has
WQO immediate-subtrees (by minimality), so Higman's lemma makes the *lists of subtrees* WQO, and the
labels are WQO by hypothesis — contradicting badness at the roots.

## What is reused vs. built
Mathlib supplies the heavy reusable engine, on which this file builds (and which it cites, not
re-proves):
- `Set.PartiallyWellOrderedOn` — the WQO predicate (`Mathlib.Order.WellFoundedSet`).
- `Set.PartiallyWellOrderedOn.IsBadSeq` / `exists_min_bad_of_exists_bad` — the Nash-Williams minimal
  bad sequence construction.
- `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂` — **Higman's lemma** (lists under
  `List.SublistForall₂` are WQO when the alphabet is).

Mathlib does **not** contain Kruskal's tree theorem (its `Kruskal*` lemmas are Kruskal-Katona, an
unrelated set-family result). The rose-tree type, the embedding order, and the Nash-Williams assembly
on top of Higman are the original content here.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.Kruskal

open Set

/-- A finite rose tree (finitely-branching, node-labeled): a label and an ordered list of subtrees. -/
inductive RoseTree (α : Type*) where
  | node : α → List (RoseTree α) → RoseTree α

namespace RoseTree

variable {α : Type*}

/-- The label at the root. -/
def root : RoseTree α → α
  | node a _ => a

/-- The list of immediate subtrees. -/
def children : RoseTree α → List (RoseTree α)
  | node _ ts => ts

@[simp] lemma root_node (a : α) (ts : List (RoseTree α)) : root (node a ts) = a := rfl
@[simp] lemma children_node (a : α) (ts : List (RoseTree α)) : children (node a ts) = ts := rfl

@[simp] lemma node_root_children : ∀ t : RoseTree α, node (root t) (children t) = t
  | node _ _ => rfl

/-- The number of nodes in the tree (used as the rank for the minimal-bad-sequence construction). -/
def size : RoseTree α → ℕ
  | node _ ts => 1 + (ts.map size).sum

/-- An immediate subtree is strictly smaller. -/
lemma size_decrease {a : α} {ts : List (RoseTree α)} {t' : RoseTree α} (h : t' ∈ ts) :
    size t' < size (node a ts) := by
  have hmem : size t' ∈ ts.map size := List.mem_map_of_mem h
  have hle : size t' ≤ (ts.map size).sum := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  simp only [size]
  omega

/-- Strong induction principle over rose trees: to prove `motive t`, prove it for `node a ts` given it
    for every immediate subtree. -/
theorem ind {motive : RoseTree α → Prop}
    (hnode : ∀ (a : α) (ts : List (RoseTree α)), (∀ t ∈ ts, motive t) → motive (node a ts)) :
    ∀ t, motive t := by
  have key : ∀ n, ∀ t : RoseTree α, size t = n → motive t := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro t ht
      cases t with
      | node a ts =>
        apply hnode
        intro t' ht'
        exact IH (size t') (by rw [← ht]; exact size_decrease ht') t' rfl
  exact fun t => key (size t) t rfl

end RoseTree

open RoseTree

variable {α : Type*} {r : α → α → Prop}

/-- The homeomorphic (inf-preserving) embedding of rose trees over a label relation `r`.
    `TreeEmbeds r s t` ("`s` embeds into `t`") holds when either
    * `s` embeds into one of `t`'s immediate subtrees (the *dive* case), or
    * the roots are `r`-related and `s`'s subtree list embeds into `t`'s subtree list pointwise and in
      order, via `List.SublistForall₂` (the *match* case). -/
inductive TreeEmbeds (r : α → α → Prop) : RoseTree α → RoseTree α → Prop
  | dive {s : RoseTree α} {b : α} {ts : List (RoseTree α)} (t' : RoseTree α)
      (hmem : t' ∈ ts) (h : TreeEmbeds r s t') : TreeEmbeds r s (RoseTree.node b ts)
  | match' {a b : α} {ss ts : List (RoseTree α)} (hab : r a b)
      (h : List.SublistForall₂ (TreeEmbeds r) ss ts) :
      TreeEmbeds r (RoseTree.node a ss) (RoseTree.node b ts)

/-- A list of self-embeddings lifts to `SublistForall₂` self-embedding. -/
theorem sublistForall₂_refl_of {l : List (RoseTree α)} (h : ∀ t ∈ l, TreeEmbeds r t t) :
    List.SublistForall₂ (TreeEmbeds r) l l := by
  induction l with
  | nil => exact List.SublistForall₂.nil
  | cons x xs ih =>
      exact List.SublistForall₂.cons (h x (List.mem_cons.2 (Or.inl rfl)))
        (ih (fun t ht => h t (List.mem_cons.2 (Or.inr ht))))

/-- Membership transfer through `SublistForall₂`: each left element embeds into some right element. -/
theorem sublistForall₂_mem {l₁ l₂ : List (RoseTree α)}
    (h : List.SublistForall₂ (TreeEmbeds r) l₁ l₂) :
    ∀ {x : RoseTree α}, x ∈ l₁ → ∃ y ∈ l₂, TreeEmbeds r x y := by
  induction h with
  | nil => intro x hx; simp at hx
  | @cons a₁ a₂ k₁ k₂ hab _ ih =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact ⟨a₂, List.mem_cons.2 (Or.inl rfl), hab⟩
      · obtain ⟨y, hy, hxy⟩ := ih hx'
        exact ⟨y, List.mem_cons.2 (Or.inr hy), hxy⟩
  | @cons_right a k₁ k₂ _ ih =>
      intro x hx
      obtain ⟨y, hy, hxy⟩ := ih hx
      exact ⟨y, List.mem_cons.2 (Or.inr hy), hxy⟩

/-- Transitivity of `SublistForall₂` with the per-element transitivity localized to the right list.
    (We cannot use the global `SublistForall₂.is_trans` because element-transitivity is only available
    by induction hypothesis at strictly smaller subtrees.) -/
theorem sublistForall₂_trans_of :
    ∀ {l₃ l₁ l₂ : List (RoseTree α)},
      (∀ z ∈ l₃, ∀ x y, TreeEmbeds r x y → TreeEmbeds r y z → TreeEmbeds r x z) →
      List.SublistForall₂ (TreeEmbeds r) l₁ l₂ → List.SublistForall₂ (TreeEmbeds r) l₂ l₃ →
      List.SublistForall₂ (TreeEmbeds r) l₁ l₃ := by
  intro l₃
  induction l₃ with
  | nil => intro l₁ l₂ _ h1 h2; cases h2; exact h1
  | cons z c ih =>
      intro l₁ l₂ htr h1 h2
      rcases h2 with _ | ⟨hbz, tbc⟩ | btc
      · cases h1; exact List.SublistForall₂.nil
      · rcases h1 with _ | ⟨hab, tab⟩ | atb
        · exact List.SublistForall₂.nil
        · exact List.SublistForall₂.cons
            (htr z (List.mem_cons.2 (Or.inl rfl)) _ _ hab hbz)
            (ih (fun z' hz' x y hxy hyz => htr z' (List.mem_cons.2 (Or.inr hz')) x y hxy hyz) tab tbc)
        · exact List.SublistForall₂.cons_right
            (ih (fun z' hz' x y hxy hyz => htr z' (List.mem_cons.2 (Or.inr hz')) x y hxy hyz) atb tbc)
      · exact List.SublistForall₂.cons_right
          (ih (fun z' hz' x y hxy hyz => htr z' (List.mem_cons.2 (Or.inr hz')) x y hxy hyz) h1 btc)

/-- The tree embedding is reflexive. -/
theorem treeEmbeds_refl [IsPreorder α r] (t : RoseTree α) : TreeEmbeds r t t := by
  induction t using RoseTree.ind with
  | hnode a ts IH => exact TreeEmbeds.match' (refl a) (sublistForall₂_refl_of IH)

/-- The tree embedding is transitive (strong induction on the size of the third tree). -/
theorem treeEmbeds_trans [IsPreorder α r] :
    ∀ {a b c : RoseTree α}, TreeEmbeds r a b → TreeEmbeds r b c → TreeEmbeds r a c := by
  have key : ∀ n, ∀ c : RoseTree α, RoseTree.size c = n →
      ∀ a b, TreeEmbeds r a b → TreeEmbeds r b c → TreeEmbeds r a c := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro c hc a b hab hbc
      have trans_into : ∀ c' : RoseTree α, RoseTree.size c' < n →
          ∀ x y, TreeEmbeds r x y → TreeEmbeds r y c' → TreeEmbeds r x c' :=
        fun c' hc' x y => IH (RoseTree.size c') hc' c' rfl x y
      cases hbc with
      | dive u' hmem hbu' =>
          exact TreeEmbeds.dive u' hmem
            (trans_into u' (by rw [← hc]; exact size_decrease hmem) a b hab hbu')
      | @match' b_t b_u ts us hbtu hsfb =>
          cases hab with
          | dive t' hmemt hat' =>
              obtain ⟨u', hu'mem, htu'⟩ := sublistForall₂_mem hsfb hmemt
              exact TreeEmbeds.dive u' hu'mem
                (trans_into u' (by rw [← hc]; exact size_decrease hu'mem) a t' hat' htu')
          | @match' b_s _ ss _ hbst hsfa =>
              have htr_us : ∀ z ∈ us, ∀ x y, TreeEmbeds r x y → TreeEmbeds r y z → TreeEmbeds r x z :=
                fun z hz x y => trans_into z (by rw [← hc]; exact size_decrease hz) x y
              exact TreeEmbeds.match' (_root_.trans hbst hbtu)
                (sublistForall₂_trans_of htr_us hsfa hsfb)
  exact fun {a b c} hab hbc => key (RoseTree.size c) c rfl a b hab hbc

instance treeEmbeds_isPreorder [IsPreorder α r] : IsPreorder (RoseTree α) (TreeEmbeds r) where
  refl := treeEmbeds_refl
  trans := fun _ _ _ => treeEmbeds_trans

/-- **Kruskal's Tree Theorem (labeled).** If the label relation `r` is a well-quasi-order on `α`, then
    the homeomorphic embedding `TreeEmbeds r` is a well-quasi-order on the finite rose trees. -/
theorem partiallyWellOrderedOn_treeEmbeds (r : α → α → Prop) [IsPreorder α r]
    (hr : (Set.univ : Set α).PartiallyWellOrderedOn r) :
    (Set.univ : Set (RoseTree α)).PartiallyWellOrderedOn (TreeEmbeds r) := by
  rw [Set.PartiallyWellOrderedOn.iff_not_exists_isMinBadSeq RoseTree.size]
  rintro ⟨f, hf1, hf2⟩
  -- The set of immediate subtrees occurring in the minimal bad sequence.
  set Sub : Set (RoseTree α) := {t | ∃ n, t ∈ RoseTree.children (f n)} with hSubdef
  -- Sub-claim: `Sub` is well-quasi-ordered, by minimality of `f`.
  have hSub : Sub.PartiallyWellOrderedOn (TreeEmbeds r) := by
    rw [Set.PartiallyWellOrderedOn.iff_forall_not_isBadSeq]
    intro S hS
    have hSmem : ∀ k, ∃ n, S k ∈ RoseTree.children (f n) := fun k => hS.1 k
    choose N hN using hSmem
    have hne : (Set.range N).Nonempty := ⟨N 0, 0, rfl⟩
    set m := sInf (Set.range N) with hmdef
    obtain ⟨k₀, hk₀⟩ := Nat.sInf_mem hne
    have hmle : ∀ k, m ≤ N k := fun k => Nat.sInf_le ⟨k, rfl⟩
    -- Splice: keep `f` below `m`, then continue with `S` from index `k₀`.
    set f' : ℕ → RoseTree α := fun i => if i < m then f i else S (k₀ + (i - m)) with hf'def
    have hagree : ∀ i, i < m → f i = f' i := fun i hi => by simp [hf'def, hi]
    have hrk : RoseTree.size (f' m) < RoseTree.size (f m) := by
      have hf'm : f' m = S k₀ := by simp [hf'def]
      rw [hf'm]
      have hmemSk0 : S k₀ ∈ RoseTree.children (f m) := by have := hN k₀; rwa [hk₀] at this
      calc RoseTree.size (S k₀)
          < RoseTree.size (RoseTree.node (RoseTree.root (f m)) (RoseTree.children (f m))) :=
            RoseTree.size_decrease (a := RoseTree.root (f m)) hmemSk0
        _ = RoseTree.size (f m) := by rw [RoseTree.node_root_children]
    apply hf2 m f' hagree hrk
    refine ⟨fun _ => mem_univ _, ?_⟩
    intro i j hij hemb
    simp only [hf'def] at hemb
    by_cases hjm : j < m
    · rw [if_pos (hij.trans hjm), if_pos hjm] at hemb
      exact hf1.2 i j hij hemb
    · by_cases him : i < m
      · rw [if_pos him, if_neg hjm] at hemb
        have hmemS : S (k₀ + (j - m)) ∈ RoseTree.children (f (N (k₀ + (j - m)))) := hN _
        have hdive : TreeEmbeds r (f i) (f (N (k₀ + (j - m)))) := by
          have h := TreeEmbeds.dive (s := f i) (b := RoseTree.root (f (N (k₀ + (j - m)))))
            (ts := RoseTree.children (f (N (k₀ + (j - m))))) (S (k₀ + (j - m))) hmemS hemb
          rwa [RoseTree.node_root_children] at h
        exact hf1.2 i _ (lt_of_lt_of_le him (hmle _)) hdive
      · rw [if_neg him, if_neg hjm] at hemb
        exact hS.2 _ _ (by omega) hemb
  -- Higman's lemma on the children-lists (which live over `Sub`).
  have hHig := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ (TreeEmbeds r) hSub
  -- A monotone subsequence along which the roots are `r`-increasing.
  obtain ⟨g, hg⟩ := hr.exists_monotone_subseq (f := fun n => RoseTree.root (f n)) (fun _ => mem_univ _)
  have hchild_mem : ∀ n, RoseTree.children (f (g n)) ∈
      {l : List (RoseTree α) | ∀ x, x ∈ l → x ∈ Sub} := fun n x hx => ⟨g n, hx⟩
  obtain ⟨i, j, hij, hsf⟩ := hHig.exists_lt (f := fun n => RoseTree.children (f (g n))) hchild_mem
  have hemb : TreeEmbeds r (f (g i)) (f (g j)) := by
    have h := TreeEmbeds.match' (a := RoseTree.root (f (g i))) (b := RoseTree.root (f (g j)))
      (ss := RoseTree.children (f (g i))) (ts := RoseTree.children (f (g j))) (hg i j hij.le) hsf
    rwa [RoseTree.node_root_children, RoseTree.node_root_children] at h
  exact hf1.2 (g i) (g j) (g.strictMono hij) hemb

end ZeroParadox.Kruskal

section PurityCheck
open ZeroParadox.Kruskal

#print axioms partiallyWellOrderedOn_treeEmbeds

end PurityCheck
