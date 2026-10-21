import ZeroParadox.Settheory.FixedPointFork
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Order.FixedPoints
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Membership graphs up to bisimulation: what is well defined on sets

## Engineer's Take

We have been working through the different ways of representing zero, such as a perfectly blank
infinite tape for one of the representations of bottom. Do any of those representations map to what
set theory calls the empty set? My raw reaction is that we could use the other form, a set that is
both itself and the empty set, if we had an appropriate transformation in place. The quines here,
and the up and over, decide whether it is a dead perfect zero or an imperfect zero allowing local
movement in the other direction. Omega can be drawn as one node that loops to itself or as two
nodes that loop to one another, and what we are looking at is the force that keeps those two nodes
pulled into an overlapping position. It is a perpendicular force that draws them together.

---

## Formal Overview (AI-assisted)
Under AFA, an operation on membership graphs is well defined on sets only if it preserves `Same`:
`wfPart` does (`wfPart_same`), the control `dropLoops` does not (`dropLoops_not_same`). The Ω, ∅,
0* pattern as a `QuineAtomHost` toy: § VII of `ZeroParadox/Settheory/QuineHost.lean`.
-/

namespace ZeroParadox

/-! ## § I. Graphs and bisimulation -/

/-- `Statement:` a finite pointed graph: a relation `edge` on `Fin n` and a point `root`.
`Reading:` `edge a b` is "a is a member of b", the direction of Mostowski's `fa = {fx | xRa}`
(Aczel 1988, *Non-Well-Founded Sets*, p. 116). -/
-- [ZP-CUSTOM] extends: Mathlib.Combinatorics.Digraph.Basic | reason: Mathlib's `Digraph (Fin n)` already has a Prop-valued `Adj`; it lacks only the distinguished point, and `MemGraph n ≃ Digraph (Fin n) × Fin n` (the `example` below). Kept as its own structure so `edge` reads member-to-set at every use site. `Quiver` edges are Type-valued, and as the corpus's `APG` (ZeroParadox/Settheory/APG.lean) uses them they point set to member, while `Acc` and bisimulation across two carriers want this Prop-valued member-to-set relation.
structure MemGraph (n : ℕ) where
  /-- `edge a b`: `a` is a member of `b`. -/
  edge : Fin n → Fin n → Prop
  /-- The point. -/
  root : Fin n

-- Statement: NO-GO gauge: `MemGraph` is data, not a requirement: `MemGraph 0` is empty (the point
-- needs a node) and every `MemGraph (n + 1)` is inhabited.
example : IsEmpty (MemGraph 0) ∧ ∀ n, Nonempty (MemGraph (n + 1)) :=
  ⟨⟨fun G => G.root.elim0⟩, fun _ => ⟨⟨fun _ _ => False, 0⟩⟩⟩

-- Statement: a `MemGraph n` is exactly a Mathlib `Digraph (Fin n)` with a point.
example (n : ℕ) : MemGraph n ≃ Digraph (Fin n) × Fin n :=
  ⟨fun G => (⟨G.edge⟩, G.root), fun p => ⟨p.1.Adj, p.2⟩, fun _ => rfl, fun _ => rfl⟩

namespace MemGraph

variable {m n : ℕ}

/-- `Statement:` `plus A B R a b`: every member of `a` is `R`-related to some member of `b`, and
back. Aczel's `R⁺` (1988, p. 20), here between two graphs. -/
def plus (A : MemGraph m) (B : MemGraph n) (R : Fin m → Fin n → Prop) : Fin m → Fin n → Prop :=
  fun a b => (∀ a', A.edge a' a → ∃ b', B.edge b' b ∧ R a' b') ∧
    (∀ b', B.edge b' b → ∃ a', A.edge a' a ∧ R a' b')

/-- `Statement:` `R` is a bisimulation: `R a b` implies `plus A B R a b`. -/
def IsBisim (A : MemGraph m) (B : MemGraph n) (R : Fin m → Fin n → Prop) : Prop :=
  ∀ a b, R a b → plus A B R a b

/-- `Statement:` some bisimulation relates the two roots. `Reading:` under AFA, `Same` graphs picture
one set (Aczel 1988: Ex. 2.11, Prop. 2.13(1), Prop. 2.10, pp. 23–24); no AFA is assumed here. -/
def Same (A : MemGraph m) (B : MemGraph n) : Prop :=
  ∃ R, IsBisim A B R ∧ R A.root B.root

/-- `Statement:` `plus A B` is monotone. Aczel 1988, p. 20; his bisimulation is Park's (Park 1981,
credited p. 92) with one action label. -/
theorem plus_mono (A : MemGraph m) (B : MemGraph n) : Monotone (plus A B) := by
  intro R S h a b ⟨h1, h2⟩
  refine ⟨fun a' ha => ?_, fun b' hb => ?_⟩
  · obtain ⟨b', hb', r⟩ := h1 a' ha
    exact ⟨b', hb', h _ _ r⟩
  · obtain ⟨a', ha', r⟩ := h2 b' hb
    exact ⟨a', ha', h _ _ r⟩

/-- `Statement:` `plus A B` as an order homomorphism. -/
def plusHom (A : MemGraph m) (B : MemGraph n) :
    (Fin m → Fin n → Prop) →o (Fin m → Fin n → Prop) := ⟨plus A B, plus_mono A B⟩

/-- `Statement:` `Same A B` iff the greatest fixed point of `plus A B` relates the roots. Aczel's
maximum bisimulation (Thm 2.4, p. 20; Prop. 2.7, p. 22); for labelled transitions, `∼ = gfp(F∼)`
(Sangiorgi, *An Introduction to Bisimulation and Coinduction*, MSR summer-school slides 2012, p. 121). -/
theorem same_iff_gfp (A : MemGraph m) (B : MemGraph n) :
    Same A B ↔ (plusHom A B).gfp A.root B.root := by
  constructor
  · rintro ⟨R, hR, hr⟩
    exact (plusHom A B).le_gfp (fun a b h => hR a b h) _ _ hr
  · intro h
    refine ⟨(plusHom A B).gfp, fun a b hab => ?_, h⟩
    rw [← (plusHom A B).map_gfp] at hab
    exact hab

-- Statement: Mathlib's `PSet.equiv_iff`: two pre-sets are `Equiv` iff each member of either is
-- `Equiv` to some member of the other. Reading: `plus`'s clause, on well-founded pre-sets.
#check @PSet.equiv_iff

/-! ## § II. Two operations on graphs -/

/-- `Statement:` delete every self-loop. -/
def dropLoops (A : MemGraph n) : MemGraph n := ⟨fun a b => A.edge a b ∧ a ≠ b, A.root⟩

/-- `Statement:` keep an arrow `a → b` only when `a` is accessible (`Acc A.edge a`). -/
def wfPart (A : MemGraph n) : MemGraph n := ⟨fun a b => A.edge a b ∧ Acc A.edge a, A.root⟩

/-! `Reading:` a relative of `ZeroParadox.wfPart` (`ZeroParadox/Category/WellFoundedCoalgebra.lean`),
Adámek–Milius–Moss 2020 (arXiv:1910.09401) Def 5.1 and Construction 5.2, p. 22, with graphs as
power-set coalgebras (Ex 2.1(1), p. 4) and their next-time operator (Ex 4.2(1), p. 15). Theirs
keeps a subcoalgebra of nodes; this keeps every node and drops arrows. Their Prop 5.5, p. 23
(coreflection) is the categorical neighbour of `wfPart_same`. No graph-level statement of
`wfPart_same` was located as of 2026-10-20 (Aczel 1988, AMM 2020, Barwise–Moss 1991, Taylor
*Well founded coalgebras and recursion*, Rutten *Universal coalgebra* 2000, Rutten–Turi
*Foundations of final semantics* 1993; theoremsearch, three phrasings). -/

/-- `Statement:` the converse of a bisimulation is a bisimulation. -/
theorem isBisim_flip {A : MemGraph m} {B : MemGraph n} {R : Fin m → Fin n → Prop}
    (hR : IsBisim A B R) : IsBisim B A (fun b a => R a b) :=
  fun b a h => ⟨(hR a b h).2, (hR a b h).1⟩

/-- `Statement:` `Same` is symmetric. -/
theorem same_symm {A : MemGraph m} {B : MemGraph n} (h : Same A B) : Same B A :=
  let ⟨_, hR, hr⟩ := h
  ⟨_, isBisim_flip hR, hr⟩

/-- `Statement:` `Same` is transitive, through the composite relation. -/
theorem same_trans {k : ℕ} {A : MemGraph k} {B : MemGraph m} {C : MemGraph n}
    (h1 : Same A B) (h2 : Same B C) : Same A C := by
  obtain ⟨R, hR, hr⟩ := h1
  obtain ⟨S, hS, hs⟩ := h2
  refine ⟨fun a c => ∃ b, R a b ∧ S b c, ?_, ⟨B.root, hr, hs⟩⟩
  rintro a c ⟨b, hab, hbc⟩
  refine ⟨fun a' ha => ?_, fun c' hc => ?_⟩
  · obtain ⟨b', hb', r'⟩ := (hR a b hab).1 a' ha
    obtain ⟨c', hc', s'⟩ := (hS b c hbc).1 b' hb'
    exact ⟨c', hc', b', r', s'⟩
  · obtain ⟨b', hb', s'⟩ := (hS b c hbc).2 c' hc
    obtain ⟨a', ha', r'⟩ := (hR a b hab).2 b' hb'
    exact ⟨a', ha', b', r', s'⟩

/-- `Statement:` a bisimulation carries accessibility from `a` to every `b` related to it. -/
theorem acc_transfer {A : MemGraph m} {B : MemGraph n} {R : Fin m → Fin n → Prop}
    (hR : IsBisim A B R) : ∀ a, Acc A.edge a → ∀ b, R a b → Acc B.edge b := by
  intro a ha
  induction ha with
  | intro a _ ih =>
    intro b hab
    constructor
    intro b' hb'
    obtain ⟨a', ha', hr⟩ := (hR a b hab).2 b' hb'
    exact ih a' ha' b' hr

/-- `Statement:` `wfPart` preserves `Same`, by the same relation. `Reading:` collapse direction:
many graphs to one set, and `wfPart` is many-to-one (`wfPart_not_recoverable`). Aczel 1988,
Prop. 1.4, p. 7 (an apg pictures Ω iff every node has a child) is not formalized here; its
two-picture instance is `omegaLoop_same_omegaPair`. -/
theorem wfPart_same {A : MemGraph m} {B : MemGraph n} (h : Same A B) :
    Same A.wfPart B.wfPart := by
  obtain ⟨R, hR, hr⟩ := h
  refine ⟨R, fun a b hab => ⟨fun a' ha => ?_, fun b' hb => ?_⟩, hr⟩
  · obtain ⟨b', hb', hr'⟩ := (hR a b hab).1 a' ha.1
    exact ⟨b', ⟨hb', acc_transfer hR a' ha.2 b' hr'⟩, hr'⟩
  · obtain ⟨a', ha', hr'⟩ := (hR a b hab).2 b' hb.1
    exact ⟨a', ⟨ha', acc_transfer (isBisim_flip hR) b' hb.2 a' hr'⟩, hr'⟩

/-- `Statement:` in `wfPart A`, every member of the root is accessible. -/
theorem wfPart_below_root (A : MemGraph n) :
    ∀ a, A.wfPart.edge a A.root → Acc A.wfPart.edge a :=
  fun _ h => Subrelation.accessible (fun h => h.1) h.2

/-- `Statement:` on a well-founded graph `wfPart` keeps every arrow. -/
theorem wfPart_of_wf (A : MemGraph n) (hA : WellFounded A.edge) (a b : Fin n) :
    A.wfPart.edge a b ↔ A.edge a b :=
  ⟨fun h => h.1, fun h => ⟨h, hA.apply a⟩⟩

/-- `Statement:` so a well-founded graph is `Same` as its `wfPart`. -/
theorem wfPart_same_self (A : MemGraph n) (hA : WellFounded A.edge) : Same A.wfPart A :=
  ⟨(· = ·), by
    rintro a b rfl
    exact ⟨fun a' ha => ⟨a', ha.1, rfl⟩, fun b' hb => ⟨b', (wfPart_of_wf A hA b' a).2 hb, rfl⟩⟩,
    rfl⟩

/-- `Statement:` an accessible point has no self-loop. -/
theorem acc_no_loop {r : Fin n → Fin n → Prop} {a : Fin n} (h : Acc r a) : ¬ r a a := by
  induction h with
  | intro a _ ih => exact fun h => ih a h h

/-- `Statement:` an accessible point lies on no two-cycle. -/
theorem acc_no_two_cycle {r : Fin n → Fin n → Prop} {a : Fin n} (h : Acc r a) :
    ∀ b, r b a → r a b → False := by
  induction h with
  | intro a _ ih => exact fun b hba hab => ih b hba a hab hba

/-- `Statement:` a point with no members is accessible. -/
theorem acc_of_no_members {r : Fin n → Fin n → Prop} {a : Fin n} (h : ∀ x, ¬ r x a) :
    Acc r a :=
  Acc.intro a fun x hx => absurd hx (h x)

/-! ## § III. The examples -/

/-- `Statement:` one node with a self-loop. `Reading:` Ω = {Ω} (Aczel 1988, Ex. 1.3, p. 6). -/
def omegaLoop : MemGraph 1 := ⟨fun _ _ => True, 0⟩

/-- `Statement:` two nodes, each the only member of the other. `Reading:` Ω (Prop. 1.4, p. 7). -/
def omegaPair : MemGraph 2 := ⟨fun a b => a ≠ b, 0⟩

/-- `Statement:` one node, no arrows. `Reading:` ∅. -/
def empty : MemGraph 1 := ⟨fun _ _ => False, 0⟩

/-- `Statement:` both nodes are members of node 0. `Reading:` 0* = {∅, 0*} (Ex. 1.5, p. 7). -/
def zeroStar : MemGraph 2 := ⟨fun _ b => b = 0, 0⟩

/-- `Statement:` node 1 is the only member of node 0. `Reading:` 1 = {∅}. -/
def one : MemGraph 2 := ⟨fun a b => a = 1 ∧ b = 0, 0⟩

/-- `Statement:` arrows 2 → 0, 1 → 0, 0 → 1. `Reading:` x = {∅, y}, y = {x} at nodes 0, 1. -/
def cycle : MemGraph 3 :=
  ⟨fun a b => (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1), 0⟩

/-- `Statement:` the other node of `Fin 2`. -/
def flip2 : Fin 2 → Fin 2 := fun a => ⟨1 - a.val, by omega⟩

/-- `Statement:` `flip2 a ≠ a`. -/
theorem flip2_ne (a : Fin 2) : flip2 a ≠ a := by
  intro h
  have := congrArg Fin.val h
  simp only [flip2] at this
  omega

/-- `Statement:` the two drawings of Ω are `Same`. -/
theorem omegaLoop_same_omegaPair : Same omegaLoop omegaPair :=
  ⟨fun _ _ => True, fun _ b _ => ⟨fun _ _ => ⟨flip2 b, flip2_ne b, trivial⟩,
    fun _ _ => ⟨0, trivial, trivial⟩⟩, trivial⟩

/-- `Statement:` CONTROL: `dropLoops` does not preserve `Same`: the two drawings of Ω are `Same`,
their loop-free versions are not. -/
theorem dropLoops_not_same :
    Same omegaLoop omegaPair ∧ ¬ Same omegaLoop.dropLoops omegaPair.dropLoops := by
  refine ⟨omegaLoop_same_omegaPair, ?_⟩
  rintro ⟨R, hR, hr⟩
  obtain ⟨a', ha', _⟩ :=
    (hR _ _ hr).2 1 (⟨by decide, by decide⟩ : (1 : Fin 2) ≠ 0 ∧ (1 : Fin 2) ≠ 0)
  exact ha'.2 (Subsingleton.elim _ _)

/-- `Statement:` `dropLoops omegaLoop` is `Same` as `empty`. -/
theorem dropLoops_omegaLoop : Same omegaLoop.dropLoops empty :=
  ⟨fun _ _ => True, fun a _ _ =>
    ⟨fun a' ha' => absurd (Subsingleton.elim a' a) ha'.2, fun _ hb' => hb'.elim⟩, trivial⟩

/-- `Statement:` `dropLoops zeroStar` is `Same` as `one`. -/
theorem dropLoops_zeroStar : Same zeroStar.dropLoops one := by
  refine ⟨(· = ·), ?_, rfl⟩
  rintro a b rfl
  refine ⟨fun a' ha' => ⟨a', ?_, rfl⟩, fun b' hb' => ⟨b', ?_, rfl⟩⟩
  · obtain ⟨h1, h2⟩ := ha'
    change a = 0 at h1
    subst h1
    refine ⟨?_, rfl⟩
    match a', h2 with
    | 0, h => exact absurd rfl h
    | 1, _ => rfl
  · obtain ⟨h1, h2⟩ := hb'
    subst h1; subst h2
    exact ⟨rfl, by decide⟩

/-- `Statement:` in `cycle`, nodes 0 and 1 are not `Same`. -/
theorem cycle_not_same : ¬ Same cycle ⟨cycle.edge, 1⟩ := by
  rintro ⟨R, hR, hr⟩
  obtain ⟨b', hb', h20⟩ := (hR 0 1 hr).1 2 (Or.inl ⟨rfl, rfl⟩)
  have hb0 : b' = 0 := by
    rcases hb' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  subst hb0
  obtain ⟨a', ha', _⟩ := (hR 2 0 h20).2 2 (Or.inl ⟨rfl, rfl⟩)
  rcases ha' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)

/-- `Statement:` `dropLoops cycle` is not well-founded. -/
theorem dropLoops_cycle_not_wf : ¬ WellFounded cycle.dropLoops.edge := fun h =>
  h.asymmetric 0 1 ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), by decide⟩
    ⟨Or.inr (Or.inl ⟨rfl, rfl⟩), by decide⟩

/-- `Statement:` on `omegaPair`, the empty relation is a fixed point of `plus`. -/
theorem omegaPair_plus_empty :
    plus omegaPair omegaPair (fun _ _ => False) = fun _ _ => False := by
  funext a b
  apply propext
  refine ⟨fun ⟨h, _⟩ => ?_, False.elim⟩
  obtain ⟨_, _, hf⟩ := h (flip2 a) (flip2_ne a)
  exact hf

/-- `Statement:` on `omegaPair`, the full relation is a fixed point of `plus`. -/
theorem omegaPair_plus_full :
    plus omegaPair omegaPair (fun _ _ => True) = fun _ _ => True := by
  funext a b
  apply propext
  exact ⟨fun _ => trivial, fun _ => ⟨fun _ _ => ⟨flip2 b, flip2_ne b, trivial⟩,
    fun _ _ => ⟨flip2 a, flip2_ne a, trivial⟩⟩⟩

/-- `Statement:` so the least fixed point of `plus omegaPair omegaPair` relates nothing. Compare
Sangiorgi 2012 slides, p. 107, Exercise: rules all with non-empty premises have empty `lfp`. -/
theorem omegaPair_lfp : (plusHom omegaPair omegaPair).lfp = ⊥ :=
  le_antisymm (OrderHom.lfp_le _ (le_of_eq omegaPair_plus_empty)) bot_le

/-- `Statement:` and the greatest relates everything, nodes 0 and 1 included. -/
theorem omegaPair_gfp : (plusHom omegaPair omegaPair).gfp = ⊤ :=
  le_antisymm le_top (OrderHom.le_gfp _ (le_of_eq omegaPair_plus_full.symm))

-- Statement: so `plus omegaPair omegaPair` has no unique fixed point (`fork_collapse_iff`,
-- `ZeroParadox/Settheory/FixedPointFork.lean`).
example : ¬ ∃! R, plusHom omegaPair omegaPair R = R := fun h => by
  have h01 := congrFun (congrFun ((fork_collapse_iff _).2 h) 0) 1
  rw [omegaPair_lfp, omegaPair_gfp] at h01
  exact (h01 ▸ trivial : (⊥ : Fin 2 → Fin 2 → Prop) 0 1)

/-- `Statement:` `wfPart omegaLoop` is `Same` as `empty`. -/
theorem wfPart_omegaLoop : Same omegaLoop.wfPart empty :=
  ⟨fun _ _ => True, fun a _ _ => ⟨fun a' ha => by
    have : a' = a := Subsingleton.elim _ _
    subst this
    exact (acc_no_loop ha.2 ha.1).elim, fun _ hb => hb.elim⟩, trivial⟩

/-- `Statement:` `wfPart omegaPair` is `Same` as `empty`. -/
theorem wfPart_omegaPair : Same omegaPair.wfPart empty :=
  ⟨fun _ _ => True, fun a _ _ => ⟨fun _ ha =>
    (acc_no_two_cycle ha.2 a (Ne.symm ha.1) ha.1).elim, fun _ hb => hb.elim⟩, trivial⟩

/-- `Statement:` `wfPart zeroStar` is `Same` as `one`. -/
theorem wfPart_zeroStar : Same zeroStar.wfPart one := by
  refine ⟨(· = ·), ?_, rfl⟩
  rintro a b rfl
  refine ⟨fun a' ha => ⟨a', ?_, rfl⟩, fun b' hb => ⟨b', ?_, rfl⟩⟩
  · obtain ⟨h1, h2⟩ := ha
    change a = 0 at h1
    subst h1
    refine ⟨?_, rfl⟩
    match a', h2 with
    | 0, h => exact (acc_no_loop h rfl).elim
    | 1, _ => rfl
  · obtain ⟨h1, h2⟩ := hb
    subst h1; subst h2
    exact ⟨rfl, acc_of_no_members fun _ h => (by decide : (1 : Fin 2) ≠ 0) h⟩

/-- `Statement:` `wfPart cycle` is `Same` as `one`. -/
theorem wfPart_cycle : Same cycle.wfPart one := by
  have ny : ¬ Acc cycle.edge 1 := fun h =>
    acc_no_two_cycle h 0 (Or.inr (Or.inr ⟨rfl, rfl⟩)) (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have ne : Acc cycle.edge 2 := acc_of_no_members fun x h => by
    rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)
  refine ⟨fun a b => (a = 0 ∧ b = 0) ∨ (a = 2 ∧ b = 1), ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · refine ⟨fun a' ha => ⟨1, ⟨rfl, rfl⟩, Or.inr ⟨?_, rfl⟩⟩,
      fun b' hb => ⟨2, ⟨Or.inl ⟨rfl, rfl⟩, ne⟩, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := ha
      rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · subst h; exact absurd h2 ny
      · exact absurd h (by decide)
    · obtain ⟨h1, _⟩ := hb
      subst h1
      exact Or.inr ⟨rfl, rfl⟩
  · refine ⟨fun a' ha => ?_, fun b' hb => ?_⟩
    · rcases ha.1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)
    · exact absurd hb.2 (by decide)

/-- `Statement:` `zeroStar` and `one` are not `Same`. -/
theorem zeroStar_not_same_one : ¬ Same zeroStar one := by
  rintro ⟨R, hR, hr⟩
  obtain ⟨b', hb', h01⟩ := (hR 0 0 hr).1 0 rfl
  obtain ⟨rfl, -⟩ := hb'
  obtain ⟨b'', hb'', _⟩ := (hR 0 1 h01).1 0 rfl
  exact absurd hb''.2 (by decide)

/-- `Statement:` `one` is well-founded. -/
theorem one_wf : WellFounded one.edge := by
  have h1 : Acc one.edge 1 := acc_of_no_members fun _ h => absurd h.2 (by decide)
  refine ⟨fun a => ?_⟩
  match a with
  | 0 => exact Acc.intro 0 fun x hx => by obtain ⟨rfl, -⟩ := hx; exact h1
  | 1 => exact h1

-- Statement: `zeroStar` and `one` are not `Same`, and both `wfPart`s are `Same` as `one`.
example : ¬ Same zeroStar one ∧ Same zeroStar.wfPart one ∧ Same one.wfPart one :=
  ⟨zeroStar_not_same_one, wfPart_zeroStar, wfPart_same_self one one_wf⟩

/-- `Statement:` `wfPart zeroStar` and `wfPart one` are equal as graphs. -/
theorem zeroStar_wfPart_eq_one_wfPart : zeroStar.wfPart = one.wfPart := by
  have z0 : ¬ Acc zeroStar.edge 0 := fun h => acc_no_loop h rfl
  have z1 : Acc zeroStar.edge 1 := acc_of_no_members fun _ h => (by decide : (1 : Fin 2) ≠ 0) h
  have o1 : Acc one.edge 1 := acc_of_no_members fun _ h => (by decide : (1 : Fin 2) ≠ 0) h.2
  show MemGraph.mk _ _ = MemGraph.mk _ _
  congr 1
  funext a b
  apply propext
  match a with
  | 0 => exact ⟨fun h => absurd h.2 z0, fun h => absurd h.1.1 (by decide)⟩
  | 1 => exact ⟨fun h => ⟨⟨rfl, h.1⟩, o1⟩, fun h => ⟨h.1.2, z1⟩⟩

/-- `Statement:` no map `g` on `MemGraph 2` sends `wfPart zeroStar` to a graph `Same` as `zeroStar`
and `wfPart one` to a graph `Same` as `one`. -/
theorem wfPart_not_recoverable :
    ¬ ∃ g : MemGraph 2 → MemGraph 2, Same (g zeroStar.wfPart) zeroStar ∧ Same (g one.wfPart) one :=
  fun ⟨_, h0, h1⟩ => zeroStar_not_same_one
    (same_trans (same_symm h0) (zeroStar_wfPart_eq_one_wfPart ▸ h1))

end MemGraph

end ZeroParadox

/-! ## Axiom Purity Check

Of the declarations printed below, `Classical.choice` appears only in `same_iff_gfp`, `omegaPair_lfp`
and `omegaPair_gfp`, and sits in their TYPES: a statement naming `⊤ : Fin 2 → Fin 2 → Prop` alone
reports it. The anonymous `¬ ∃!` example in § III, which uses the last two, carries it as well. The
equations `omegaPair_plus_empty` and `omegaPair_plus_full` carry none. -/

section PurityCheck
open ZeroParadox MemGraph

#print axioms MemGraph
#print axioms plus
#print axioms IsBisim
#print axioms Same
#print axioms plus_mono
#print axioms plusHom
#print axioms same_iff_gfp
#print axioms dropLoops
#print axioms wfPart
#print axioms isBisim_flip
#print axioms same_symm
#print axioms same_trans
#print axioms acc_transfer
#print axioms wfPart_same
#print axioms wfPart_below_root
#print axioms wfPart_of_wf
#print axioms wfPart_same_self
#print axioms acc_no_loop
#print axioms acc_no_two_cycle
#print axioms acc_of_no_members
#print axioms omegaLoop
#print axioms omegaPair
#print axioms empty
#print axioms zeroStar
#print axioms one
#print axioms cycle
#print axioms flip2
#print axioms flip2_ne
#print axioms omegaLoop_same_omegaPair
#print axioms dropLoops_not_same
#print axioms dropLoops_omegaLoop
#print axioms dropLoops_zeroStar
#print axioms cycle_not_same
#print axioms dropLoops_cycle_not_wf
#print axioms omegaPair_plus_empty
#print axioms omegaPair_plus_full
#print axioms omegaPair_lfp
#print axioms omegaPair_gfp
#print axioms wfPart_omegaLoop
#print axioms wfPart_omegaPair
#print axioms wfPart_zeroStar
#print axioms wfPart_cycle
#print axioms zeroStar_not_same_one
#print axioms one_wf
#print axioms zeroStar_wfPart_eq_one_wfPart
#print axioms wfPart_not_recoverable

end PurityCheck
