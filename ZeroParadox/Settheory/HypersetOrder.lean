import ZeroParadox.Settheory.GraphBisim
import ZeroParadox.Order.UpAndOver
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Closure
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Hypersets ordered by subset: pruning as a kernel operator, and the wrap-once step

## Engineer's Take

I think the pruning is half of a condition to make a leg, that comes along with the application of something more. Putting it into the project language, I think the pruning might be the hinge. With the states described, it sounds a whole lot like what we already solved for the ω-towers.

---

## Formal Overview (AI-assisted)
`HSet n` orders hypersets by `Sub`; pruning is a kernel operator there (`pruneKernel`), the UP of no
`UpAndOver` (see `no_upAndOver_prune` for scope). `wrap` draws `x ↦ {x}`; its fixed points up to `Same` are `Same` as `omegaLoop`, no AFA assumed.
-/

namespace ZeroParadox

namespace MemGraph

variable {k m n : ℕ}

/-! ## § I. Re-rooting and the set order -/

/-- `Statement:` the same edges, rooted at `a`. -/
def at' (A : MemGraph n) (a : Fin n) : MemGraph n := ⟨A.edge, a⟩

/-- `Statement:` `Same` is reflexive, by equality. -/
theorem same_refl (A : MemGraph n) : Same A A :=
  ⟨(· = ·), by rintro a b rfl; exact ⟨fun a' h => ⟨a', h, rfl⟩, fun b' h => ⟨b', h, rfl⟩⟩, rfl⟩

/-- `Statement:` a bisimulation gives `Same` at every pair it relates, re-rooted there. -/
theorem same_at_of {A : MemGraph m} {B : MemGraph n} {R : Fin m → Fin n → Prop}
    (hR : IsBisim A B R) {a : Fin m} {b : Fin n} (h : R a b) : Same (A.at' a) (B.at' b) :=
  ⟨R, hR, h⟩

/-- `Statement:` every member of `A`'s root is `Same`, re-rooted, as some member of `B`'s root.
    `Reading:` the set `A` pictures is a subset of the set `B` pictures. -/
def Sub (A : MemGraph m) (B : MemGraph n) : Prop :=
  ∀ a, A.edge a A.root → ∃ b, B.edge b B.root ∧ Same (A.at' a) (B.at' b)

/-- `Statement:` `Sub` is reflexive. -/
theorem sub_refl (A : MemGraph n) : Sub A A := fun a h => ⟨a, h, same_refl _⟩

/-- `Statement:` `Sub` is transitive. -/
theorem sub_trans {A : MemGraph k} {B : MemGraph m} {C : MemGraph n}
    (h1 : Sub A B) (h2 : Sub B C) : Sub A C := fun a ha => by
  obtain ⟨b, hb, s1⟩ := h1 a ha
  obtain ⟨c, hc, s2⟩ := h2 b hb
  exact ⟨c, hc, same_trans s1 s2⟩

/-- `Statement:` `Sub` both ways gives `Same`. -/
theorem same_of_sub_sub {A : MemGraph m} {B : MemGraph n} (h1 : Sub A B) (h2 : Sub B A) :
    Same A B := by
  refine ⟨fun x y => (x = A.root ∧ y = B.root) ∨ Same (A.at' x) (B.at' y), ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro x y (⟨rfl, rfl⟩ | ⟨Q, hQ, hq⟩)
  · refine ⟨fun a' ha => ?_, fun b' hb => ?_⟩
    · obtain ⟨b', hb', s⟩ := h1 a' ha
      exact ⟨b', hb', Or.inr s⟩
    · obtain ⟨a', ha', s⟩ := h2 b' hb
      exact ⟨a', ha', Or.inr (same_symm s)⟩
  · refine ⟨fun a' ha => ?_, fun b' hb => ?_⟩
    · obtain ⟨b', hb', hq'⟩ := (hQ x y hq).1 a' ha
      exact ⟨b', hb', Or.inr (same_at_of hQ hq')⟩
    · obtain ⟨a', ha', hq'⟩ := (hQ x y hq).2 b' hb
      exact ⟨a', ha', Or.inr (same_at_of hQ hq')⟩

/-- `Statement:` `Same` gives `Sub`. -/
theorem sub_of_same {A : MemGraph m} {B : MemGraph n} (h : Same A B) : Sub A B := by
  obtain ⟨R, hR, hr⟩ := h
  intro a ha
  obtain ⟨b, hb, hab⟩ := (hR _ _ hr).1 a ha
  exact ⟨b, hb, same_at_of hR hab⟩

/-- `Statement:` extensionality: `Same A B` iff `Sub A B` and `Sub B A`; both directions.
    `Reading:` Aczel 1988, pp. 19–20, motivates AFA by strengthening extensionality for `x = {x}`. -/
theorem same_iff_sub_sub {A : MemGraph m} {B : MemGraph n} : Same A B ↔ Sub A B ∧ Sub B A :=
  ⟨fun h => ⟨sub_of_same h, sub_of_same (same_symm h)⟩, fun ⟨h1, h2⟩ => same_of_sub_sub h1 h2⟩

/-- `Statement:` `Sub` respects `Same` on both sides. -/
theorem sub_congr {A A' : MemGraph m} {B B' : MemGraph n} (ha : Same A A') (hb : Same B B') :
    Sub A B ↔ Sub A' B' :=
  ⟨fun h => sub_trans (sub_of_same (same_symm ha)) (sub_trans h (sub_of_same hb)),
   fun h => sub_trans (sub_of_same ha) (sub_trans h (sub_of_same (same_symm hb)))⟩

/-! ## § II. Pruning, member by member -/

/-- `Statement:` below an accessible node, pruning changes nothing up to `Same`. -/
theorem wfPart_at_same (A : MemGraph n) {a : Fin n} (ha : Acc A.edge a) :
    Same (A.wfPart.at' a) (A.at' a) := by
  refine ⟨fun x y => x = y ∧ Acc A.edge x, ?_, ⟨rfl, ha⟩⟩
  rintro x y ⟨rfl, hx⟩
  exact ⟨fun x' h => ⟨x', h.1, rfl, h.2⟩, fun y' h => ⟨y', ⟨h, hx.inv h⟩, rfl, hx.inv h⟩⟩

/-- `Statement:` the root's members after pruning are exactly its accessible members.
    `Reading:` at the root, pruning is `x ↦ x ∩ WF`. -/
theorem wfPart_root_mem (A : MemGraph n) (a : Fin n) :
    A.wfPart.edge a A.wfPart.root ↔ A.edge a A.root ∧ Acc A.edge a := Iff.rfl

/-- `Statement:` after pruning, every node is accessible. -/
theorem wfPart_acc_all (A : MemGraph n) (a : Fin n) : Acc A.wfPart.edge a :=
  Acc.intro a fun _ hc => Subrelation.accessible (fun h => h.1) hc.2

/-- `Statement:` pruning is idempotent as an equation of graphs. -/
theorem wfPart_wfPart (A : MemGraph n) : A.wfPart.wfPart = A.wfPart := by
  cases A with
  | mk e r =>
    simp only [wfPart, MemGraph.mk.injEq, and_true]
    funext a b
    apply propext
    exact ⟨fun h => h.1, fun h => ⟨h, wfPart_acc_all ⟨e, r⟩ a⟩⟩

/-- `Statement:` pruning is deflationary: `Sub A.wfPart A`. -/
theorem wfPart_sub (A : MemGraph n) : Sub A.wfPart A := fun a ha =>
  ⟨a, ha.1, wfPart_at_same A ha.2⟩

/-- `Statement:` pruning is monotone under `Sub`. -/
theorem wfPart_sub_mono {A : MemGraph m} {B : MemGraph n} (h : Sub A B) :
    Sub A.wfPart B.wfPart := fun a ha => by
  obtain ⟨b, hb, s⟩ := h a ha.1
  obtain ⟨Q, hQ, hq⟩ := s
  have hacc : Acc B.edge b := acc_transfer (A := A.at' a) (B := B.at' b) hQ a ha.2 b hq
  exact ⟨b, ⟨hb, hacc⟩, wfPart_same (A := A.at' a) (B := B.at' b) ⟨Q, hQ, hq⟩⟩

/-- `Statement:` edge inclusion with the same root. -/
def Grow (A B : MemGraph n) : Prop := A.root = B.root ∧ ∀ a b, A.edge a b → B.edge a b

/-- `Statement:` node 1 is a member of node 0 and of itself. `Reading:` {Ω}. -/
def omegaIn : MemGraph 2 := ⟨fun a _ => a = 1, 0⟩

/-- `Statement:` two nodes, no arrows. `Reading:` ∅. -/
def bare2 : MemGraph 2 := ⟨fun _ _ => False, 0⟩

/-- `Statement:` CONTROL: edge inclusion is not `Sub`: `one` grows to `omegaIn` and is not `Sub`
    it, since the added self-loop turns the member ∅ into Ω. -/
theorem le_not_sub : Grow one omegaIn ∧ ¬ Sub one omegaIn := by
  refine ⟨⟨rfl, fun _ _ h => h.1⟩, fun h => ?_⟩
  obtain ⟨b, hb, Q, hQ, hq⟩ := h 1 ⟨rfl, rfl⟩
  have hb1 : b = 1 := hb
  subst hb1
  obtain ⟨a', ha', -⟩ := (hQ 1 1 hq).2 1 rfl
  exact absurd ha'.2 (by decide)

/-- `Statement:` pruning is not monotone under edge inclusion (`le_not_sub`): on the same pair, the pruned
    `one` keeps `1 → 0` and the pruned `omegaIn` drops it. -/
theorem wfPart_not_monotone : Grow one omegaIn ∧ ¬ Grow one.wfPart omegaIn.wfPart := by
  refine ⟨le_not_sub.1, fun ⟨_, h⟩ => ?_⟩
  have hA : Acc one.edge 1 := acc_of_no_members fun _ h => absurd h.2 (by decide)
  have := h 1 0 ⟨⟨rfl, rfl⟩, hA⟩
  exact acc_no_loop this.2 (show omegaIn.edge 1 1 from rfl)

/-! ## § III. One added member -/

section Fork
variable {y : MemGraph m} {b : MemGraph n} {x : Fin n}

/-- `Statement:` if every member of `y`'s root is accessible, `Sub y b`, every member of `b`'s root
    is `Same` as a member of `y`'s or is `x`, and `x` is not accessible, then pruning `b` gives a
    graph `Same` as `y`. -/
theorem fork_loop (hy : ∀ a, y.edge a y.root → Acc y.edge a) (hyb : Sub y b)
    (hb : ∀ c, b.edge c b.root → (∃ a, y.edge a y.root ∧ Same (y.at' a) (b.at' c)) ∨ c = x)
    (hx : ¬ Acc b.edge x) : Same b.wfPart y := by
  refine same_of_sub_sub (fun c hc => ?_) (fun a ha => ?_)
  · rcases hb c hc.1 with ⟨a, ha, s⟩ | rfl
    · exact ⟨a, ha, same_trans (wfPart_at_same b hc.2) (same_symm s)⟩
    · exact (hx hc.2).elim
  · obtain ⟨c, hc, s⟩ := hyb a ha
    obtain ⟨Q, hQ, hq⟩ := s
    have hacc : Acc b.edge c := acc_transfer (A := y.at' a) (B := b.at' c) hQ a (hy a ha) c hq
    exact ⟨c, ⟨hc, hacc⟩, same_trans ⟨Q, hQ, hq⟩ (same_symm (wfPart_at_same b hacc))⟩

/-- `Statement:` if every member of `y`'s root is accessible, every member of `b`'s root is `Same` as a
    member of `y`'s or is `x`, and `x` is accessible, then pruning `b` gives a graph `Same` as `b`. -/
theorem fork_stay (hy : ∀ a, y.edge a y.root → Acc y.edge a)
    (hb : ∀ c, b.edge c b.root → (∃ a, y.edge a y.root ∧ Same (y.at' a) (b.at' c)) ∨ c = x)
    (hx : Acc b.edge x) : Same b.wfPart b := by
  have hall : ∀ c, b.edge c b.root → Acc b.edge c := fun c hc => by
    rcases hb c hc with ⟨a, ha, Q, hQ, hq⟩ | rfl
    · exact acc_transfer (A := y.at' a) (B := b.at' c) hQ a (hy a ha) c hq
    · exact hx
  exact same_of_sub_sub (wfPart_sub b) (fun c hc => ⟨c, ⟨hc, hall c hc⟩,
    same_symm (wfPart_at_same b (hall c hc))⟩)

end Fork

/-- `Statement:` pruning fixes `A` up to `Same` iff every member of `A`'s root is accessible; both
    directions. -/
theorem same_wfPart_iff_acc (A : MemGraph n) :
    Same A.wfPart A ↔ ∀ a, A.edge a A.root → Acc A.edge a := by
  constructor
  · intro hA a ha
    obtain ⟨a', ha', s⟩ := sub_of_same (same_symm hA) a ha
    obtain ⟨Q, hQ, hq⟩ := same_trans (same_symm (wfPart_at_same A ha'.2)) (same_symm s)
    exact acc_transfer (A := A.at' a') (B := A.at' a) hQ a' ha'.2 a hq
  · intro h
    exact same_of_sub_sub (wfPart_sub A) (fun a ha => ⟨a, ⟨ha, h a ha⟩,
      same_symm (wfPart_at_same A (h a ha))⟩)

/-- `Statement:` the graphs pruning fixes up to `Same` are closed downward under `Sub`.
    `Reading:` a subset of a well-founded set is well-founded. -/
theorem landing_down {A : MemGraph m} {B : MemGraph n} (h : Sub B A) (hA : Same A.wfPart A) :
    Same B.wfPart B := by
  have accA : ∀ a, A.edge a A.root → Acc A.edge a := fun a ha => by
    obtain ⟨a', ha', s⟩ := sub_of_same (same_symm hA) a ha
    have s2 : Same (A.at' a') (A.at' a) :=
      same_trans (same_symm (wfPart_at_same A ha'.2)) (same_symm s)
    obtain ⟨Q, hQ, hq⟩ := s2
    exact acc_transfer (A := A.at' a') (B := A.at' a) hQ a' ha'.2 a hq
  have accB : ∀ b, B.edge b B.root → Acc B.edge b := fun b hb => by
    obtain ⟨a, ha, Q, hQ, hq⟩ := h b hb
    exact acc_transfer (A := A.at' a) (B := B.at' b) (isBisim_flip hQ) a (accA a ha) b hq
  exact same_of_sub_sub (wfPart_sub B) (fun b hb => ⟨b, ⟨hb, accB b hb⟩,
    same_symm (wfPart_at_same B (accB b hb))⟩)

/-! ## § IV. Hypersets, and pruning as a kernel operator -/

/-- `Statement:` the preorder `Sub` on graphs with `n` nodes. -/
instance instPreorder (n : ℕ) : Preorder (MemGraph n) where
  le := Sub
  le_refl := sub_refl
  le_trans _ _ _ := sub_trans

/-- `Statement:` mutual `≤` (Mathlib's `AntisymmRel`) is `Same`; both directions. -/
theorem antisymmRel_iff_same {A B : MemGraph n} : AntisymmRel (· ≤ ·) A B ↔ Same A B :=
  ⟨fun h => same_of_sub_sub h.1 h.2, fun h => ⟨sub_of_same h, sub_of_same (same_symm h)⟩⟩

/-- `Statement:` Mathlib's `Antisymmetrization` of `Sub`: graphs on `n` nodes up to `Same`. -/
abbrev HSet (n : ℕ) := Antisymmetrization (MemGraph n) (· ≤ ·)

/-- `Statement:` pruning as an order homomorphism of `Sub` (`wfPart_sub_mono`). -/
def pruneHom (n : ℕ) : MemGraph n →o MemGraph n := ⟨wfPart, fun _ _ h => wfPart_sub_mono h⟩

/-- `Statement:` pruning on hypersets: `pruneHom` passed to the quotient. -/
def prune (n : ℕ) : HSet n →o HSet n := (pruneHom n).antisymmetrization

/-- `Statement:` pruning is a closure operator on the order dual of `HSet n`: deflationary,
    monotone and idempotent. Its fixed points are the classes of graphs whose root members are all
    accessible (the `example` below, from `same_wfPart_iff_acc`). `Reading:` an interior (kernel) operator; the set-level
    neighbour of Adámek–Milius–Moss 2020, Prop. 5.5, p. 23 (the well-founded part is a
    coreflection), whose well-founded part keeps a subcoalgebra of nodes where `wfPart` keeps
    every node and drops arrows. -/
def pruneKernel (n : ℕ) : ClosureOperator (HSet n)ᵒᵈ :=
  ClosureOperator.mk' (fun x => OrderDual.toDual (prune n (OrderDual.ofDual x)))
    (fun _ _ h => (prune n).monotone h)
    (fun x => Antisymmetrization.ind (· ≤ ·) (p := fun q => prune n q ≤ q)
      (fun A => wfPart_sub A) (OrderDual.ofDual x))
    (fun x => Antisymmetrization.ind (· ≤ ·) (p := fun q => prune n q ≤ prune n (prune n q))
      (fun A => show Sub A.wfPart A.wfPart.wfPart by rw [wfPart_wfPart]; exact sub_refl _)
      (OrderDual.ofDual x))

-- Statement: a class is fixed by `pruneKernel` iff the root members of a representative are all accessible.
example {n : ℕ} (A : MemGraph n) :
    (pruneKernel n).IsClosed (OrderDual.toDual (toAntisymmetrization (· ≤ ·) A)) ↔
      ∀ a, A.edge a A.root → Acc A.edge a := by
  constructor
  · intro h
    have h' := congrArg OrderDual.ofDual h.closure_eq
    exact (same_wfPart_iff_acc A).1 (antisymmRel_iff_same.1 (Quotient.exact h'))
  · intro h
    exact (pruneKernel n).isClosed_iff.2 (congrArg OrderDual.toDual
      (Quotient.sound (antisymmRel_iff_same.2 ((same_wfPart_iff_acc A).2 h))))

/-- `Statement:` pruning is the UP of no `UpAndOver` on the order dual of `HSet n`: the corner's
    cover lies below its landing in `Sub`, and `landing_down` makes pruning fix it. `Reading:` no
    `UpAndOver (HSet n)ᵒᵈ` is constructed in this corpus (not located in `ZeroParadox/` as of
    2026-10-21, grep `UpAndOver (HSet`), so whether this excludes any structure is not shown here. -/
theorem no_upAndOver_prune : ¬ ∃ U : UpAndOver (HSet n)ᵒᵈ, U.up = pruneKernel n := by
  rintro ⟨U, hU⟩
  obtain ⟨y, b, hy, hyb, hb⟩ := U.corner
  rw [hU] at hy hb
  apply hb
  induction y using Antisymmetrization.ind with | _ A => ?_
  induction b using Antisymmetrization.ind with | _ B => ?_
  have hle : Sub B A := hyb.le
  have hA : Same A.wfPart A := antisymmRel_iff_same.1 (Quotient.exact hy.closure_eq)
  exact Quotient.sound (antisymmRel_iff_same.2 (landing_down hle hA))

/-- `Statement:` pruning is constant up to `Same` on the interval from `X.wfPart` to `X` under
    `Sub`. `Reading:` the mirror of `UpAndOver.up_eq_of_mem_Icc`, which holds here. -/
theorem prune_const_of_between {X : MemGraph m} {S : MemGraph k}
    (h1 : Sub X.wfPart S) (h2 : Sub S X) : Same S.wfPart X.wfPart :=
  same_of_sub_sub (wfPart_sub_mono h2)
    (sub_trans (by rw [wfPart_wfPart]; exact sub_refl _) (wfPart_sub_mono h1))

/-- `Statement:` on two nodes: pruning `omegaPair` (Ω) gives a graph `Same` as `bare2` (∅), `bare2`
    is `Sub` `one` = {∅}, and pruning `one` gives a graph not `Same` as `bare2`. -/
theorem empty_cell_has_omega_not_one :
    Same omegaPair.wfPart bare2 ∧ Sub bare2 one ∧ ¬ Same one.wfPart bare2 := by
  have he : Same empty bare2 :=
    ⟨fun _ _ => True, fun _ _ _ => ⟨fun _ h => h.elim, fun _ h => h.elim⟩, trivial⟩
  refine ⟨same_trans wfPart_omegaPair he, fun _ h => h.elim, fun h => ?_⟩
  obtain ⟨b, hb, -⟩ := sub_of_same h 1 ⟨⟨rfl, rfl⟩, one_wf.apply 1⟩
  exact hb

/-- `Statement:` on one node, every graph prunes to a graph `Same` as `empty`. -/
theorem wfPart_same_empty_of_one_node (A : MemGraph 1) : Same A.wfPart empty := by
  have hno : ∀ a b : Fin 1, ¬ A.wfPart.edge a b := by
    rintro a b ⟨h, hacc⟩
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha; subst hb
    exact acc_no_loop hacc h
  exact ⟨fun _ _ => True, fun a _ _ =>
    ⟨fun a' ha => (hno a' a ha).elim, fun _ hb => (show False from hb).elim⟩, trivial⟩

/-! ## § V. Pruning as a die motion (`ZeroParadox/Die.lean` § I) -/

/-- `Statement:` UP `wfPart`, OVER `Grow`. -/
def pruneMotion (n : ℕ) : Motion (MemGraph n) := Motion.ofTotal wfPart wfPart_wfPart Grow

/-- `Statement:` the motion loops: the landing `bare2` grows to `omegaIn`, which prunes back. -/
theorem pruneMotion_loop : (pruneMotion 2).Loop := by
  have hland : bare2.wfPart = bare2 := by simp only [wfPart, bare2, false_and]
  have hprune : omegaIn.wfPart = bare2 := by
    simp only [wfPart, omegaIn, bare2, MemGraph.mk.injEq, and_true]
    funext a b
    apply propext
    refine ⟨fun ⟨h, hacc⟩ => ?_, False.elim⟩
    subst h
    exact acc_no_loop hacc (show omegaIn.edge 1 1 from rfl)
  refine ⟨bare2, omegaIn, ?_, ⟨rfl, fun _ _ h => h.elim⟩, ?_, ?_⟩
  · show bare2 ∈ Part.some bare2.wfPart
    rw [hland]; exact Part.mem_some _
  · intro h
    have : omegaIn.edge 1 0 := rfl
    rw [h] at this; exact this
  · show bare2 ∈ Part.some omegaIn.wfPart
    rw [hprune]; exact Part.mem_some _

/-- `Statement:` node 0 has members 1 and 2; node 1 is its own member; node 2 has none. -/
def mixed3 : MemGraph 3 := ⟨fun a b => a = 2 ∧ b = 0 ∨ a = 1 ∧ b ≠ 2, 0⟩

/-- `Statement:` the motion climbs: the landing with no arrows grows to `mixed3`, which prunes to
    the graph with the single arrow `2 → 0`, neither start nor step. -/
theorem pruneMotion_climb : (pruneMotion 3).Climb := by
  let bare3 : MemGraph 3 := ⟨fun _ _ => False, 0⟩
  let one3 : MemGraph 3 := ⟨fun a b => a = 2 ∧ b = 0, 0⟩
  have h2 : Acc mixed3.edge 2 := acc_of_no_members fun x h => by
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h (by decide)
    · exact h rfl
  have h1 : ¬ Acc mixed3.edge 1 := fun h => acc_no_loop h (Or.inr ⟨rfl, by decide⟩)
  have hprune : mixed3.wfPart = one3 := by
    simp only [wfPart, mixed3, one3, MemGraph.mk.injEq, and_true]
    funext a b
    apply propext
    constructor
    · rintro ⟨h | ⟨rfl, -⟩, hacc⟩
      · exact h
      · exact (h1 hacc).elim
    · rintro ⟨rfl, rfl⟩
      exact ⟨Or.inl ⟨rfl, rfl⟩, h2⟩
  have hland : bare3.wfPart = bare3 := by simp only [bare3, wfPart, false_and]
  refine ⟨bare3, mixed3, one3, ?_, ⟨rfl, fun _ _ h => h.elim⟩, ?_, ?_, ?_⟩
  · show bare3 ∈ Part.some bare3.wfPart
    rw [hland]; exact Part.mem_some _
  · show one3 ∈ Part.some mixed3.wfPart
    rw [hprune]; exact Part.mem_some _
  · intro h
    have : mixed3.edge 1 0 := Or.inr ⟨rfl, by decide⟩
    rw [← h] at this
    exact absurd this.1 (by decide)
  · intro h
    have : one3.edge 2 0 := ⟨rfl, rfl⟩
    rw [h] at this; exact this

/-- `Statement:` under `Sub`, UP lowers (`wfPart_sub`), at every node count. -/
theorem pruneMotion_upLowers : (pruneMotion n).UpLowers := fun x _ h =>
  (Part.mem_some_iff.1 h) ▸ wfPart_sub x

/-- `Statement:` on two nodes, under `Sub`, OVER does not raise (`le_not_sub`). -/
theorem pruneMotion_not_stepRaises : ¬ (pruneMotion 2).StepRaises := fun h =>
  le_not_sub.2 (h one omegaIn le_not_sub.1)

/-- `Statement:` on two nodes the legs neither agree nor oppose (`pruneMotion_not_stepRaises`). -/
theorem pruneMotion_two_neither : ¬ (pruneMotion 2).Agree ∧ ¬ (pruneMotion 2).Oppose :=
  ⟨fun h => pruneMotion_not_stepRaises h.2, fun h => pruneMotion_not_stepRaises h.2⟩

/-- `Statement:` on one node, under `Sub`, OVER raises. -/
theorem pruneMotion_one_stepRaises : (pruneMotion 1).StepRaises := by
  rintro x y ⟨hr, he⟩ a ha
  have hx : ∀ i j : Fin 1, x.edge i j := by
    intro i j; rw [Subsingleton.elim i a, Subsingleton.elim j x.root]; exact ha
  exact ⟨a, hr ▸ he a x.root ha, ⟨fun _ _ => True, fun i j _ =>
    ⟨fun a' _ => ⟨a', he a' j (hx a' j), trivial⟩, fun b' _ => ⟨b', hx b' i, trivial⟩⟩, trivial⟩⟩

/-- `Statement:` on one node the legs oppose (`pruneMotion_upLowers`, `pruneMotion_one_stepRaises`). -/
theorem pruneMotion_one_oppose : (pruneMotion 1).Oppose :=
  ⟨pruneMotion_upLowers, pruneMotion_one_stepRaises⟩

/-- `Statement:` on one node the motion loops: `empty` grows to `omegaLoop`, which prunes back. -/
theorem pruneMotion_one_loop : (pruneMotion 1).Loop := by
  have hland : empty.wfPart = empty := by simp only [wfPart, empty, false_and]
  have hprune : omegaLoop.wfPart = empty := by
    simp only [wfPart, omegaLoop, empty, MemGraph.mk.injEq, and_true, true_and]
    funext a b
    apply propext
    exact ⟨fun hacc => acc_no_loop hacc (show omegaLoop.edge a a from trivial), False.elim⟩
  refine ⟨empty, omegaLoop, ?_, ⟨rfl, fun _ _ h => h.elim⟩, ?_, ?_⟩
  · show empty ∈ Part.some empty.wfPart
    rw [hland]; exact Part.mem_some _
  · intro h
    have : omegaLoop.edge 0 0 := trivial
    rw [h] at this; exact this
  · show empty ∈ Part.some omegaLoop.wfPart
    rw [hprune]; exact Part.mem_some _

/-! ## § VI. Wrapping once -/

/-- `Statement:` a new root `0`, the old nodes shifted by `Fin.succ`, and one new arrow from the
    old root to the new root. `Reading:` `x ↦ {x}`. -/
def wrap (A : MemGraph n) : MemGraph (n + 1) :=
  ⟨fun a b => (∃ x y, a = x.succ ∧ b = y.succ ∧ A.edge x y) ∨ (a = A.root.succ ∧ b = 0), 0⟩

/-- `Statement:` the members of the new root are exactly the old root. -/
theorem wrap_mem_zero (A : MemGraph n) (w : Fin (n + 1)) :
    (wrap A).edge w 0 ↔ w = A.root.succ := by
  constructor
  · rintro (⟨x, y, -, hy, -⟩ | ⟨h, -⟩)
    · exact absurd hy.symm (Fin.succ_ne_zero y)
    · exact h
  · intro h; exact Or.inr ⟨h, rfl⟩

/-- `Statement:` the members of a shifted node are the shifted members. -/
theorem wrap_mem_succ (A : MemGraph n) (w : Fin (n + 1)) (y : Fin n) :
    (wrap A).edge w y.succ ↔ ∃ x, w = x.succ ∧ A.edge x y := by
  constructor
  · rintro (⟨x, y', hw, hy, he⟩ | ⟨-, h⟩)
    · exact ⟨x, hw, (Fin.succ_injective _ hy) ▸ he⟩
    · exact absurd h (Fin.succ_ne_zero y)
  · rintro ⟨x, hw, he⟩; exact Or.inl ⟨x, y, hw, rfl, he⟩

/-- `Statement:` each shifted node of `wrap A`, re-rooted, is `Same` as the old node. -/
theorem wrap_at_succ (A : MemGraph n) (x : Fin n) : Same ((wrap A).at' x.succ) (A.at' x) := by
  refine ⟨fun w a => w = a.succ, ?_, rfl⟩
  rintro w a rfl
  refine ⟨fun w' hw => ?_, fun a' ha => ⟨a'.succ, (wrap_mem_succ A _ a).2 ⟨a', rfl, ha⟩, rfl⟩⟩
  obtain ⟨x', rfl, he⟩ := (wrap_mem_succ A w' a).1 hw
  exact ⟨x', he, rfl⟩

/-- `Statement:` wrapping `omegaLoop` gives a graph `Same` as `omegaLoop`. -/
theorem wrap_omegaLoop : Same (wrap omegaLoop) omegaLoop := by
  refine ⟨fun _ _ => True, ?_, trivial⟩
  intro w b _
  refine ⟨fun _ _ => ⟨0, trivial, trivial⟩, fun _ _ => ?_⟩
  refine Fin.cases ?_ (fun y => ?_) w
  · exact ⟨(0 : Fin 1).succ, (wrap_mem_zero omegaLoop _).2 rfl, trivial⟩
  · exact ⟨(0 : Fin 1).succ, (wrap_mem_succ omegaLoop _ y).2 ⟨0, rfl, trivial⟩, trivial⟩

/-- `Statement:` CONTROL: wrapping `zeroStar` gives a graph not `Same` as `zeroStar`. -/
theorem wrap_zeroStar_not_same : ¬ Same (wrap zeroStar) zeroStar := by
  rintro ⟨R, hR, hr⟩
  obtain ⟨w, hw, h1⟩ := (hR 0 0 hr).2 1 (rfl : zeroStar.edge 1 0)
  have hw' : w = (0 : Fin 2).succ := (wrap_mem_zero zeroStar w).1 hw
  subst hw'
  obtain ⟨b', hb', -⟩ := (hR _ 1 h1).1 (0 : Fin 2).succ
    ((wrap_mem_succ zeroStar _ 0).2 ⟨0, rfl, rfl⟩)
  have h10 : (1 : Fin 2) = 0 := hb'
  exact absurd h10 (by decide)

/-- `Statement:` every `A` with `Same (wrap A) A` is `Same` as `omegaLoop`; no AFA is assumed.
    `Reading:` up to bisimulation, `x = {x}` has the one solution Ω. Neighbours in Aczel 1988:
    Prop. 1.4, p. 7, "An apg is a picture of Ω if and only if every node of the apg has a child";
    p. 19, "AFA implies that there is at most one solution to the equation [x = {x}], namely Ω";
    p. 57, at most one reflexive set under FAFA₂ (hence under any AFA~), while under BA₁ the
    reflexive sets form a proper class (Prop. 5.1). -/
theorem same_omegaLoop_of_wrap_same (A : MemGraph n) (h : Same (wrap A) A) :
    Same A omegaLoop := by
  obtain ⟨R, hR, hr⟩ := h
  have mem_root : ∀ r', A.edge r' A.root → Same (A.at' r') (A.at' A.root) := by
    intro r' hr'
    obtain ⟨w, hw, hwr⟩ := (hR 0 A.root hr).2 r' hr'
    have hw' := (wrap_mem_zero A w).1 hw
    subst hw'
    have h1 : Same ((wrap A).at' A.root.succ) (A.at' r') := same_at_of hR hwr
    exact same_trans (same_symm h1) (wrap_at_succ A A.root)
  have root_has : ∃ r', A.edge r' A.root := by
    obtain ⟨r', hr', -⟩ := (hR 0 A.root hr).1 A.root.succ ((wrap_mem_zero A _).2 rfl)
    exact ⟨r', hr'⟩
  refine ⟨fun a _ => Same (A.at' a) (A.at' A.root), ?_, same_refl _⟩
  intro a _ ha
  obtain ⟨Q, hQ, hq⟩ := ha
  refine ⟨fun a' haa => ?_, fun _ _ => ?_⟩
  · obtain ⟨r', hr', hq'⟩ := (hQ a A.root hq).1 a' haa
    exact ⟨0, trivial, same_trans (same_at_of hQ hq') (mem_root r' hr')⟩
  · obtain ⟨r', hr'⟩ := root_has
    obtain ⟨a', haa, hq'⟩ := (hQ a A.root hq).2 r' hr'
    exact ⟨a', haa, same_trans (same_at_of hQ hq') (mem_root r' hr')⟩

end MemGraph

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox MemGraph

#print axioms at'
#print axioms same_refl
#print axioms same_at_of
#print axioms MemGraph.Sub
#print axioms sub_refl
#print axioms sub_trans
#print axioms same_of_sub_sub
#print axioms sub_of_same
#print axioms same_iff_sub_sub
#print axioms sub_congr
#print axioms wfPart_at_same
#print axioms wfPart_root_mem
#print axioms wfPart_acc_all
#print axioms wfPart_wfPart
#print axioms wfPart_sub
#print axioms wfPart_sub_mono
#print axioms Grow
#print axioms omegaIn
#print axioms bare2
#print axioms le_not_sub
#print axioms wfPart_not_monotone
#print axioms fork_loop
#print axioms fork_stay
#print axioms same_wfPart_iff_acc
#print axioms landing_down
#print axioms instPreorder
#print axioms antisymmRel_iff_same
#print axioms HSet
#print axioms pruneHom
#print axioms prune
#print axioms pruneKernel
#print axioms no_upAndOver_prune
#print axioms prune_const_of_between
#print axioms empty_cell_has_omega_not_one
#print axioms wfPart_same_empty_of_one_node
#print axioms pruneMotion
#print axioms pruneMotion_loop
#print axioms mixed3
#print axioms pruneMotion_climb
#print axioms pruneMotion_upLowers
#print axioms pruneMotion_not_stepRaises
#print axioms pruneMotion_two_neither
#print axioms pruneMotion_one_stepRaises
#print axioms pruneMotion_one_oppose
#print axioms pruneMotion_one_loop
#print axioms wrap
#print axioms wrap_mem_zero
#print axioms wrap_mem_succ
#print axioms wrap_at_succ
#print axioms wrap_omegaLoop
#print axioms wrap_zeroStar_not_same
#print axioms same_omegaLoop_of_wrap_same

end PurityCheck
