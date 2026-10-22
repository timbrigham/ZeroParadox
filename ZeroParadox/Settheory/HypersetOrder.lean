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
`UpAndOver` (see `no_upAndOver_prune` for scope). `wrap` draws `x ↦ {x}`; its fixed points up to `Same` are `Same` as `omegaLoop`, no AFA assumed. § VII: the member motion (`forcedTop_same`), and quotients by `Same` (`drawing_vs_set`,
`eq_omegaLoop_of_wrapMotion_step_self`).
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

/-- `Statement:` on two nodes, pruning is not monotone under edge inclusion: on the pair of
    `le_not_sub`, the pruned `one` keeps `1 → 0` and the pruned `omegaIn` drops it. -/
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
    directions. `Reading:` neighbours: Aczel 1988, p. 6, under AFA "any non-well-founded apg will
    have to picture a non-well-founded set"; Adámek–Milius–Moss 2020, Cor. 4.13, p. 18 (Taylor), "A
    coalgebra for a set functor preserving intersections is well-founded iff its canonical graph is
    well-founded". -/
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
    cover lies below its landing in `Sub`, and `landing_down` makes pruning fix it. `Reading:` at
    `n = 2` some `UpAndOver (HSet 2)ᵒᵈ` exists (`nonempty_upAndOver_hset2`); for other n, whether
    some `UpAndOver (HSet n)ᵒᵈ` exists is not shown here. -/
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

/-- `Statement:` two graphs whose roots have no members are `Same`. -/
theorem same_of_no_members {A : MemGraph m} {B : MemGraph n}
    (hA : ∀ a, ¬ A.edge a A.root) (hB : ∀ b, ¬ B.edge b B.root) : Same A B :=
  ⟨fun x y => x = A.root ∧ y = B.root, by
    rintro x y ⟨rfl, rfl⟩
    exact ⟨fun a h => (hA a h).elim, fun b h => (hB b h).elim⟩, ⟨rfl, rfl⟩⟩

/-- `Statement:` node 1 of `zeroStar` and node 1 of `one`, re-rooted, are `Same` (both ∅). -/
theorem same_zeroStar_one_at_one : Same (zeroStar.at' 1) (one.at' 1) :=
  same_of_no_members (fun _ h => (by decide : (1 : Fin 2) ≠ 0) h)
    (fun _ h => (by decide : (1 : Fin 2) ≠ 0) h.2)

/-- `Statement:` `bare2` is `Sub` every graph. -/
theorem bare2_sub (X : MemGraph n) : Sub bare2 X := fun _ h => h.elim

/-- `Statement:` `Sub one zeroStar`. -/
theorem one_sub_zeroStar : Sub one zeroStar := by
  rintro a ⟨rfl, -⟩
  exact ⟨1, rfl, same_symm same_zeroStar_one_at_one⟩

/-- `Statement:` if `Sub one S`, `Sub S zeroStar` and not `Sub zeroStar S`, then `Sub S one`. -/
theorem sub_one_of_between {S : MemGraph k} (h1 : Sub one S) (h2 : Sub S zeroStar)
    (hn : ¬ Sub zeroStar S) : Sub S one := by
  intro s hs
  obtain ⟨t, -, hst⟩ := h2 s hs
  match t, hst with
  | 0, hst =>
    exfalso; apply hn
    intro z hz
    match z, hz with
    | 0, _ => exact ⟨s, hs, same_symm hst⟩
    | 1, _ =>
      obtain ⟨s', hs', h'⟩ := h1 1 ⟨rfl, rfl⟩
      exact ⟨s', hs', same_trans same_zeroStar_one_at_one h'⟩
  | 1, hst => exact ⟨1, ⟨rfl, rfl⟩, same_trans hst same_zeroStar_one_at_one⟩

/-- `Statement:` not `Sub one bare2`. -/
theorem one_not_sub_bare2 : ¬ Sub one bare2 := by
  intro h
  obtain ⟨b, hb, -⟩ := h 1 ⟨rfl, rfl⟩
  exact hb

/-- `Statement:` `UpAndOver (HSet 2)ᵒᵈ` is inhabited: `nonempty_upAndOver_dual_of_covBy_classical`
    with least point the class of `bare2`, `a` the class of `zeroStar`, `b` the class of `one`, and
    `b ⋖ a` under `Sub`. `Reading:` the three graphs draw ∅, x = {∅, x} and {∅}. -/
theorem nonempty_upAndOver_hset2 : Nonempty (UpAndOver (HSet 2)ᵒᵈ) := by
  refine nonempty_upAndOver_dual_of_covBy_classical (toAntisymmetrization (· ≤ ·) bare2)
    (toAntisymmetrization (· ≤ ·) zeroStar) (toAntisymmetrization (· ≤ ·) one) ?_ ?_ ?_
  · intro x
    induction x using Antisymmetrization.ind with | _ X => exact bare2_sub X
  · refine ⟨?_, ?_⟩
    · exact ⟨one_sub_zeroStar, fun h => zeroStar_not_same_one (same_of_sub_sub h one_sub_zeroStar)⟩
    · intro c hc1 hc2
      induction c using Antisymmetrization.ind with | _ S => ?_
      have l1 : Sub one S := hc1.1
      have l2 : Sub S zeroStar := hc2.1
      have n2 : ¬ Sub zeroStar S := fun h => hc2.2 h
      exact hc1.2 (sub_one_of_between l1 l2 n2)
  · intro h
    exact one_not_sub_bare2 (sub_of_same (antisymmRel_iff_same.1 (Quotient.exact h)))

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

/-- `Statement:` every `A` with `Same (wrap A) A` is `Same` as `omegaLoop`; no AFA is assumed, and
    `Same` is the equality AFA installs.
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

/-! ## § VII. The member motion: what the drawing shows, and what the set shows -/

/-- `Statement:` UP the identity; OVER from `a` to `b` when `b` is a member of `a` (`G.edge b a`). -/
def memberMotion (G : MemGraph n) : Motion (Fin n) :=
  Motion.ofTotal id (fun _ => rfl) (fun a b => G.edge b a)

/-- `Statement:` in `memberMotion omegaLoop`, node 0 steps to itself only. -/
theorem omegaLoop_selfOnlyAt : (memberMotion omegaLoop).SelfOnlyAt 0 :=
  ⟨trivial, fun b _ => Subsingleton.elim b 0⟩

/-- `Statement:` in `memberMotion zeroStar`, node 0 steps to itself and steps elsewhere (to node 1);
    node 1 has no step. -/
theorem zeroStar_cells :
    ((memberMotion zeroStar).step 0 0 ∧ (memberMotion zeroStar).LeavesAt 0) ∧
      (memberMotion zeroStar).NoStepAt 1 :=
  ⟨⟨rfl, ⟨1, rfl, by decide⟩⟩, fun _ h => absurd (show (1 : Fin 2) = 0 from h) (by decide)⟩

/-- `Statement:` in `memberMotion omegaPair`, no node steps to itself and every node steps
    elsewhere. -/
theorem omegaPair_no_step_self (x : Fin 2) :
    ¬ (memberMotion omegaPair).step x x ∧ (memberMotion omegaPair).LeavesAt x :=
  ⟨fun h => h rfl, ⟨flip2 x, fun h => flip2_ne x h, flip2_ne x⟩⟩

/-- `Statement:` `Same omegaLoop omegaPair`, the root of `omegaLoop` steps to itself only, and the
    root of `omegaPair` does not step to itself. `Reading:` stepping to itself is a property of the
    drawing, not of the set drawn. -/
theorem selfOnlyAt_root_not_same_invariant :
    Same omegaLoop omegaPair ∧ (memberMotion omegaLoop).SelfOnlyAt omegaLoop.root ∧
      ¬ (memberMotion omegaPair).step omegaPair.root omegaPair.root :=
  ⟨omegaLoop_same_omegaPair, omegaLoop_selfOnlyAt, fun h => h rfl⟩

/-- `Statement:` in `memberMotion zeroStar`, node 0 reaches node 1 ≠ 0, and node 0 does not arrive at
    node 1 (the run staying at node 0 is a run). -/
theorem zeroStar_reaches_not_arrives :
    Relation.ReflTransGen (memberMotion zeroStar).step 0 1 ∧ (1 : Fin 2) ≠ 0 ∧
      ¬ (memberMotion zeroStar).Arrives 1 0 := by
  refine ⟨Relation.ReflTransGen.single rfl, by decide, fun h => ?_⟩
  obtain ⟨k, hk⟩ := Motion.exists_run_eq_of_arrives h (fun _ => 0) (fun _ => rfl) rfl
  exact absurd hk (by decide)

/-- `Statement:` every rank `v : Fin n → ℕ∞` dropping by at least one along every step of
    `memberMotion G` has `v a = ⊤`. -/
def ForcedTop (G : MemGraph n) (a : Fin n) : Prop :=
  ∀ v : Fin n → ℕ∞, (∀ x y, (memberMotion G).step x y → v y + 1 ≤ v x) → v a = ⊤

/-- `Statement:` `ForcedTop G a` iff `a` is not accessible (`Acc G.edge a`). -/
theorem forcedTop_iff_not_acc (G : MemGraph n) (a : Fin n) : ForcedTop G a ↔ ¬ Acc G.edge a :=
  Motion.forall_rank_eq_top_iff_not_acc G.edge

/-- `Statement:` `ForcedTop G a` iff some node reachable from `a` by steps lies on a cycle of steps. -/
theorem forcedTop_iff_reaches_cycle (G : MemGraph n) (a : Fin n) :
    ForcedTop G a ↔ ∃ c, Relation.ReflTransGen (memberMotion G).step a c ∧
      Relation.TransGen (memberMotion G).step c c := by
  rw [forcedTop_iff_not_acc, Motion.not_acc_iff_reaches_cycle]
  constructor
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, Relation.ReflTransGen.swap h1, Relation.TransGen.swap h2⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, Relation.ReflTransGen.swap h1, Relation.TransGen.swap h2⟩

/-- `Statement:` if a bisimulation relates `a` and `b`, `ForcedTop A a ↔ ForcedTop B b`. -/
theorem forcedTop_bisim {A : MemGraph m} {B : MemGraph n} {R : Fin m → Fin n → Prop}
    (hR : IsBisim A B R) {a : Fin m} {b : Fin n} (hab : R a b) :
    ForcedTop A a ↔ ForcedTop B b := by
  rw [forcedTop_iff_not_acc, forcedTop_iff_not_acc]
  exact not_congr ⟨fun ha => acc_transfer hR a ha b hab,
    fun hb => acc_transfer (isBisim_flip hR) b hb a hab⟩

/-- `Statement:` if `Same A B`, `ForcedTop A A.root ↔ ForcedTop B B.root`. -/
theorem forcedTop_same {A : MemGraph m} {B : MemGraph n} (h : Same A B) :
    ForcedTop A A.root ↔ ForcedTop B B.root :=
  let ⟨_, hR, hr⟩ := h
  forcedTop_bisim hR hr

/-- `Statement:` `ForcedTop` holds at the roots of `omegaLoop` and `omegaPair`, the second by
    `forcedTop_same` along `omegaLoop_same_omegaPair`. -/
theorem omega_forcedTop : ForcedTop omegaLoop omegaLoop.root ∧ ForcedTop omegaPair omegaPair.root :=
  have h : ForcedTop omegaLoop omegaLoop.root :=
    (forcedTop_iff_not_acc _ _).2 fun h => acc_no_loop h trivial
  ⟨h, (forcedTop_same omegaLoop_same_omegaPair).1 h⟩

/-- `Statement:` `ForcedTop` holds at node 0 of `zeroStar`, fails at its node 1, and fails at the root
    of `empty`. -/
theorem zeroStar_empty_forcedTop :
    ForcedTop zeroStar 0 ∧ ¬ ForcedTop zeroStar 1 ∧ ¬ ForcedTop empty empty.root :=
  ⟨(forcedTop_iff_not_acc _ _).2 fun h => acc_no_loop h rfl,
    fun h => (forcedTop_iff_not_acc _ _).1 h
      (acc_of_no_members fun _ h => (by decide : (1 : Fin 2) ≠ 0) h),
    fun h => (forcedTop_iff_not_acc _ _).1 h (acc_of_no_members fun _ h => h)⟩

/-- `Statement:` two nodes, one arrow `1 → 1`, root 0. -/
def junkLoop : MemGraph 2 := ⟨fun a b => a = 1 ∧ b = 1, 0⟩

/-- `Statement:` CONTROL: `Same junkLoop empty`; `ForcedTop` holds at node 1 of `junkLoop`;
    `junkLoop.edge` is not well-founded; `ForcedTop` fails at the root of `junkLoop` and at every
    node of `empty`. `Reading:` `forcedTop_same` is a fact about the root, not about every node. -/
theorem junkLoop_control :
    Same junkLoop empty ∧ ForcedTop junkLoop 1 ∧ ¬ WellFounded junkLoop.edge ∧
      ¬ ForcedTop junkLoop junkLoop.root ∧ ∀ x, ¬ ForcedTop empty x := by
  refine ⟨⟨fun a _ => a = 0, fun a b hab => ⟨fun a' ha' => ?_, fun b' hb' => hb'.elim⟩, rfl⟩,
    (forcedTop_iff_not_acc _ _).2 fun h => acc_no_loop h ⟨rfl, rfl⟩,
    fun h => acc_no_loop (h.apply 1) ⟨rfl, rfl⟩,
    fun h => (forcedTop_iff_not_acc _ _).1 h
      (acc_of_no_members fun x hx => absurd hx.2 (by decide)),
    fun x h => (forcedTop_iff_not_acc _ _).1 h (acc_of_no_members fun _ h => h)⟩
  exact absurd (hab.symm.trans ha'.2) (by decide)

/-! The same split through a quotient of a motion (`ZeroParadox/Die.lean` § XVIII): the motion on
graphs, and its quotient by `Same`, whose classes are `HSet n` (the `example` below). -/

/-- `Statement:` on graphs with `n` nodes, UP the identity; OVER from `A` to `A` re-rooted at each
    member of its root. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: the member step on whole graphs (`memberMotion` steps on
-- nodes of one graph), so that its quotient by `Same` acts on `HSet n`.
def graphMotion (n : ℕ) : Motion (MemGraph n) :=
  Motion.ofTotal id (fun _ => rfl) (fun A B => ∃ b, A.edge b A.root ∧ B = A.at' b)

/-- `Statement:` `Same`, as mutual `Sub` (`antisymmRel_iff_same`), is step-compatible with
    `graphMotion n`. -/
theorem graphMotion_stepCompat (n : ℕ) :
    (graphMotion n).StepCompat (AntisymmRel.setoid (MemGraph n) (· ≤ ·)) := by
  rintro A A' B hAA' ⟨b, hb, rfl⟩
  obtain ⟨R, hR, hr⟩ := antisymmRel_iff_same.1 hAA'
  obtain ⟨b', hb', hbb'⟩ := (hR _ _ hr).1 b hb
  exact ⟨A'.at' b', ⟨b', hb', rfl⟩, antisymmRel_iff_same.2 (same_at_of hR hbb')⟩

-- Statement: the classes of that setoid are `HSet 2`, by definition.
example : Quotient (AntisymmRel.setoid (MemGraph 2) (· ≤ ·)) = HSet 2 := rfl

/-- `Statement:` each node of `omegaPair`, as root, is `Same` as `omegaPair`. -/
theorem omegaPair_at_same (b : Fin 2) : Same (omegaPair.at' b) omegaPair :=
  ⟨fun _ _ => True, fun _ y _ => ⟨fun _ _ => ⟨flip2 y, flip2_ne y, trivial⟩,
    fun _ _ => ⟨flip2 _, flip2_ne _, trivial⟩⟩, trivial⟩

/-- `Statement:` `omegaPair` does not step to itself in `graphMotion 2`, and its class steps to itself
    only in the quotient. `Reading:` one representative of Ω's class has no self-step and the class
    has one; `graphMotion_omegaLoop_step_self` is a representative that has one. -/
theorem drawing_vs_set :
    ¬ (graphMotion 2).step omegaPair omegaPair ∧
      ((graphMotion 2).quot (AntisymmRel.setoid (MemGraph 2) (· ≤ ·))).SelfOnlyAt
        (Quotient.mk _ omegaPair) := by
  refine ⟨fun ⟨b, hb, he⟩ => hb (congrArg MemGraph.root he).symm, ?_⟩
  rw [Motion.quot_selfOnlyAt_mk_iff (graphMotion_stepCompat 2)]
  refine ⟨⟨omegaPair.at' 1, ⟨1, show (1 : Fin 2) ≠ 0 by decide, rfl⟩,
    antisymmRel_iff_same.2 (omegaPair_at_same 1)⟩, ?_⟩
  rintro B ⟨b, -, rfl⟩
  exact antisymmRel_iff_same.2 (omegaPair_at_same b)

/-- `Statement:` `omegaLoop` steps to itself in `graphMotion 1`. -/
theorem graphMotion_omegaLoop_step_self : (graphMotion 1).step omegaLoop omegaLoop :=
  ⟨0, trivial, rfl⟩

/-- `Statement:` `Same` on graphs of every node count, as a setoid on `Σ n, MemGraph n`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: `HSet n` fixes `n`; wrapping changes it, so the classes
-- are taken on the sigma type with `same_refl`, `same_symm`, `same_trans`.
def sameSetoid : Setoid (Σ n, MemGraph n) where
  r p q := Same p.2 q.2
  iseqv := ⟨fun p => same_refl p.2, fun h => same_symm h, fun h1 h2 => same_trans h1 h2⟩

/-- `Statement:` if `Same A B`, then `Same (wrap A) (wrap B)`. -/
theorem wrap_same_of_same {A : MemGraph m} {B : MemGraph n} (h : Same A B) :
    Same (wrap A) (wrap B) := by
  refine same_of_sub_sub (fun a ha => ?_) (fun b hb => ?_)
  · have ha' := (wrap_mem_zero A a).1 ha
    subst ha'
    exact ⟨B.root.succ, (wrap_mem_zero B _).2 rfl,
      same_trans (wrap_at_succ A A.root) (same_trans h (same_symm (wrap_at_succ B B.root)))⟩
  · have hb' := (wrap_mem_zero B b).1 hb
    subst hb'
    exact ⟨A.root.succ, (wrap_mem_zero A _).2 rfl,
      same_trans (wrap_at_succ B B.root) (same_trans (same_symm h) (same_symm (wrap_at_succ A A.root)))⟩

/-- `Statement:` on graphs of every node count, `ofFun` of `(n, A) ↦ (n + 1, wrap A)`. `Reading:` the
    step `MemGraph n → MemGraph (n + 1)` changes the carrier; on the sigma type it is one motion. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: `wrap` as a self-map of `Σ n, MemGraph n`.
def wrapMotion : Motion (Σ n, MemGraph n) := Motion.ofFun fun p => ⟨p.1 + 1, wrap p.2⟩

/-- `Statement:` `sameSetoid` is step-compatible with `wrapMotion` (`wrap_same_of_same`). -/
theorem wrapMotion_stepCompat : wrapMotion.StepCompat sameSetoid :=
  Motion.stepCompat_ofFun fun _ _ h => wrap_same_of_same h

-- Statement: no point steps to itself in `wrapMotion` (the node count rises by one).
example (p : Σ n, MemGraph n) : ¬ wrapMotion.step p p := fun h => by
  have h1 : p.1 = p.1 + 1 := congrArg Sigma.fst h
  omega

/-- `Statement:` the class of `p` steps to itself only in the quotient iff `Same (wrap p.2) p.2`. -/
theorem wrapMotion_quot_selfOnlyAt_iff (p : Σ n, MemGraph n) :
    (wrapMotion.quot sameSetoid).SelfOnlyAt (Quotient.mk sameSetoid p) ↔ Same (wrap p.2) p.2 := by
  rw [Motion.quot_selfOnlyAt_mk_iff wrapMotion_stepCompat]
  exact ⟨fun ⟨⟨b, hb, h⟩, _⟩ => by
      have hb' : b = ⟨p.1 + 1, wrap p.2⟩ := hb
      subst hb'
      exact h,
    fun h => ⟨⟨_, rfl, h⟩, fun b hb => by
      have hb' : b = ⟨p.1 + 1, wrap p.2⟩ := hb
      subst hb'
      exact h⟩⟩

/-- `Statement:` the class of `omegaLoop` steps to itself only (`wrap_omegaLoop`). -/
theorem wrapMotion_omegaLoop_selfOnlyAt :
    (wrapMotion.quot sameSetoid).SelfOnlyAt (Quotient.mk sameSetoid ⟨1, omegaLoop⟩) :=
  (wrapMotion_quot_selfOnlyAt_iff _).2 wrap_omegaLoop

/-- `Statement:` every class that steps to itself is the class of `omegaLoop`
    (`same_omegaLoop_of_wrap_same`). -/
theorem eq_omegaLoop_of_wrapMotion_step_self {X : Quotient sameSetoid}
    (h : (wrapMotion.quot sameSetoid).step X X) : X = Quotient.mk sameSetoid ⟨1, omegaLoop⟩ := by
  induction X using Quotient.ind with
  | _ p =>
    obtain ⟨b, hb, he⟩ := (Motion.quot_step_mk_iff wrapMotion_stepCompat p _).1 h
    have hb' : b = ⟨p.1 + 1, wrap p.2⟩ := hb
    subst hb'
    exact Quotient.sound (same_omegaLoop_of_wrap_same p.2 (Quotient.exact he))

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
#print axioms same_of_no_members
#print axioms same_zeroStar_one_at_one
#print axioms bare2_sub
#print axioms one_sub_zeroStar
#print axioms sub_one_of_between
#print axioms one_not_sub_bare2
#print axioms nonempty_upAndOver_hset2
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
#print axioms memberMotion
#print axioms omegaLoop_selfOnlyAt
#print axioms zeroStar_cells
#print axioms omegaPair_no_step_self
#print axioms selfOnlyAt_root_not_same_invariant
#print axioms zeroStar_reaches_not_arrives
#print axioms ForcedTop
#print axioms forcedTop_iff_not_acc
#print axioms forcedTop_iff_reaches_cycle
#print axioms forcedTop_bisim
#print axioms forcedTop_same
#print axioms omega_forcedTop
#print axioms zeroStar_empty_forcedTop
#print axioms junkLoop
#print axioms junkLoop_control
#print axioms graphMotion
#print axioms graphMotion_stepCompat
#print axioms omegaPair_at_same
#print axioms drawing_vs_set
#print axioms graphMotion_omegaLoop_step_self
#print axioms sameSetoid
#print axioms wrap_same_of_same
#print axioms wrapMotion
#print axioms wrapMotion_stepCompat
#print axioms wrapMotion_quot_selfOnlyAt_iff
#print axioms wrapMotion_omegaLoop_selfOnlyAt
#print axioms eq_omegaLoop_of_wrapMotion_step_self

end PurityCheck
