import ZeroParadox.Category.Lawvere
import ZeroParadox.Die
import Mathlib.Order.UpperLower.Basic

/-!
# The minimum requirements to be a diagonal fixed point — the relativized Lawvere witness

## Engineer's Take

Definition of a minimal set of criteria across the faces, including Cantor, Russell, Turing, Kleene,
Tarski, Curry, Löb, Gödel, and Rice. We focused our work around behavior at bottom, and have been able
to build a topological map.

---

## Formal Overview (AI-assisted)
A diagonal witness relative to a class of admissible endomaps (`HasWitnessRel`), its engine and wall,
the topology of the witness set, and the floor in the effective category. Argument, level sets,
topology and prior art: `ZeroParadox/Category/DiagonalWitness.md`.
-/

namespace ZeroParadox

open Function

universe u

/-- **The minimal requirement (relativized diagonal hypothesis).** `β` has a diagonal witness *relative
    to* an admissible endomap class `M` when some self-application `e : α → (α → β)` has, in its range,
    the diagonal `fun x => g (e x x)` for every admissible `g`. `HasLawvereWitness` relativized to the
    maps the diagonal must dodge — the underlying level beneath the μ/ν fork. (`α` shares `β`'s universe:
    the self-reference faces encode maps on the same object.) -/
def HasWitnessRel (β : Type u) (M : (β → β) → Prop) : Prop :=
  ∃ (α : Type u) (e : α → (α → β)), ∀ g : β → β, M g → ∃ a, (fun x => g (e x x)) = e a

/-- **The engine, relativized.** A relative witness forces every *admissible* endomap to have a fixed
    point (Lawvere's diagonal, restricted to `M`). -/
theorem fixedPoint_of_witnessRel {β : Type*} {M : (β → β) → Prop}
    (h : HasWitnessRel β M) {g : β → β} (hg : M g) : ∃ b, g b = b := by
  obtain ⟨α, e, he⟩ := h
  obtain ⟨a, ha⟩ := he g hg
  exact ⟨e a a, congrFun ha a⟩

/-- **The obstruction, relativized (the wall).** If an admissible endomap is fixed-point-free, there is
    no relative witness. Cantor, restricted to `M`. -/
theorem no_witnessRel_of_admissible_fpf {β : Type*} {M : (β → β) → Prop}
    {g : β → β} (hg : M g) (hgf : ∀ x, g x ≠ x) : ¬ HasWitnessRel β M := by
  intro h
  obtain ⟨b, hb⟩ := fixedPoint_of_witnessRel h hg
  exact hgf b hb

-- Statement: with literal equality the computable endomaps of codes carry no relativized witness:
--   `fun c => Code.pair c c` is computable and fixes no code.
example : ¬ HasWitnessRel Nat.Partrec.Code Computable :=
  no_witnessRel_of_admissible_fpf (g := fun c => Nat.Partrec.Code.pair c c)
    (Nat.Partrec.Code.primrec₂_pair.comp Primrec.id Primrec.id).to_comp
    (fun c h => by have := congrArg sizeOf h; simp at this)

/-- **Antitone in the admissible class (the topology spine).** Shrinking the admissible endomap class
    can only help the witness. So `{M | HasWitnessRel β M}` is downward-closed in `⊆` — a lower set /
    Alexandrov-closed set on the lattice of admissible-map-classes. -/
theorem witnessRel_antitone {β : Type*} {M M' : (β → β) → Prop}
    (hsub : ∀ g, M g → M' g) (h : HasWitnessRel β M') : HasWitnessRel β M := by
  obtain ⟨α, e, he⟩ := h
  exact ⟨α, e, fun g hg => he g (hsub g hg)⟩

/-- A surjective self-application gives a relative witness for the *entire* endomap class — the top of
    the lattice, where the engine forces a fixed point for every map. This is the framework's absolute
    `HasLawvereWitness` content, stated directly in `β`'s universe (`Category/Lawvere.lean` phrases it
    with a universe-independent `α`). -/
theorem hasWitnessRel_top_of_surjective {β : Type u} {α : Type u} (f : α → (α → β))
    (hf : Surjective f) : HasWitnessRel β (fun _ => True) := by
  refine ⟨α, f, fun g _ => ?_⟩
  obtain ⟨a, ha⟩ := hf (fun x => g (f x x))
  exact ⟨a, ha.symm⟩

/-- **The coarse-M level set (Cantor recovered).** At the top of the lattice — every endomap admissible —
    any nontrivial carrier has NO witness: the fixed-point-free swap is admissible and kills it. This is
    the Set-level Cantor obstruction as a level set of `HasWitnessRel`, and it is exactly why the lattice
    and 2-adic faces are *posited* (a designated self-map has a fixed point without a witness), not
    genuine, at the coarse end. Mirrors `no_witness_of_nontrivial` (`Category/Lawvere.lean`). -/
theorem no_witnessRel_top_of_nontrivial {β : Type u} [DecidableEq β] [Nontrivial β] :
    ¬ HasWitnessRel β (fun _ => True) := by
  -- Choice-free: with `DecidableEq β` the swap needs no classical decision (constructive-footprint audit,
  -- 2026-07-18). This is the base-level, choice-free form; the `DecidableEq` restriction is what buys
  -- the purity. The construction inlined below is the one that
  -- `ZeroParadox/Category/Lawvere.lean`'s `fixedPointFree_of_nontrivial` produces, and THAT theorem's
  -- `classical` is essential in the sense, and on the premise, of
  -- `ZeroParadox/Category/ChoiceCannotBe.lean` § IV (`wem_of_fixedPointFree` derives weak excluded
  -- middle from its ∀-closure). **That is a fact about that theorem, not about this one:
  -- essentiality does not transfer, and there is no dependency here — the swap is inlined, and this
  -- statement measures `[propext]`, which is what proves the independence.**
  obtain ⟨b₀, b₁, hne⟩ := exists_pair_ne β
  refine no_witnessRel_of_admissible_fpf (g := fun x => if x = b₀ then b₁ else b₀) trivial (fun x => ?_)
  by_cases hx : x = b₀
  · subst hx; simpa using hne.symm
  · simp only [if_neg hx]; exact fun h => hx h.symm

/-- **The fine end is inhabited (non-degeneracy).** A one-element carrier has a witness for *every*
    admissible class — there is no fixed-point-free endomap to obstruct it, so the diagonal always
    closes. This is the trivial genuine floor; it keeps the witness set (hence the topology) from being
    empty. The nontrivial genuine floor is the computability face, up to `eval` (§ Axis 2). -/
theorem hasWitnessRel_of_subsingleton {β : Type u} [Nonempty β] [Subsingleton β]
    (M : (β → β) → Prop) : HasWitnessRel β M := by
  obtain ⟨b₀⟩ := ‹Nonempty β›
  refine ⟨β, fun b _ => b, fun g _ => ⟨b₀, ?_⟩⟩
  funext x
  exact Subsingleton.elim _ _

/-! ## § The topology — the witness set is Alexandrov-closed on the lattice of map-classes -/

/-- **The topology, made explicit.** On the lattice of admissible-map-classes `Set (β → β)` (ordered by
    inclusion), the set of classes carrying a diagonal witness is a **lower set** — downward closed. A
    lower set is exactly a closed set of the Alexandrov topology on the poset, so this is the topology
    the diagonal-fixed-point collection sits on: the fork (wall vs floor) is the boundary of one closed
    set, crossed as the admissible class shrinks past the fixed-point-free diagonal. Immediate from
    `witnessRel_antitone`. -/
theorem witnessSet_isLowerSet {β : Type u} :
    IsLowerSet {M : Set (β → β) | HasWitnessRel β M} := by
  intro a b hab hb
  exact witnessRel_antitone (fun g hg => hab hg) hb

/-! ## § Axis 2 — the genuine floor in the effective category (joining the effective-topos program)

The `HasWitnessRel` topology above is axis 1: the admissible map-class M *within* a fixed category
(raw functions, raw equality). The genuine NONTRIVIAL floor lives one axis out — in the **effective
category**, where "endomap" means computable and "equality" means eval-equality. There the Cantor
obstruction lifts, and the diagonal genuinely closes: Rogers' fixed-point / Kleene's recursion theorem. This is the
recognized **effective-topos / Turing-category** setting (Lawvere 1969; Hyland 1982, "The effective
topos"; Cockett–Hofstra 2008, "Introduction to Turing categories"; van Oosten). Located and cited here,
NOT claimed — the framework joins that program. -/

/-- **Axis-2 genuine floor.** Every *computable* self-map on codes has an eval-fixed point —
    **Rogers' fixed-point theorem** (`computability_face_fixedPoint` = Mathlib
    `Nat.Partrec.Code.fixed_point`). Mathlib reserves the name *Kleene's second recursion theorem*
    for `fixed_point₂`, and literally derives `fixed_point₂` from `fixed_point`, so the two are
    inter-derivable. `ZeroParadox/Category/Lawvere.lean` attaches **both** names to `fixed_point` as a
    slash-alias ("Rogers / Kleene's recursion theorem") rather than making this split — compatible, but
    not the same convention. The fine end of axis 2. -/
theorem effective_floor_fixedPoint {g : Nat.Partrec.Code → Nat.Partrec.Code} (hg : Computable g) :
    ∃ c, Nat.Partrec.Code.eval (g c) = Nat.Partrec.Code.eval c :=
  computability_face_fixedPoint hg

/-- **Why the wall lifts in the effective category (the axis-2 mechanism).** There is no *computable*
    self-map on codes that is eval-fixed-point-free: the recursion theorem forces a fixed point. So the
    diagonal swap that refutes the witness at the Set level (`no_witnessRel_of_admissible_fpf`) has NO
    computable representative up to `eval`; with literal equality one exists (the `example` after
    `no_witnessRel_of_admissible_fpf`). This is why the floor can switch on along axis 2. -/
theorem no_computable_evalFixedPointFree {g : Nat.Partrec.Code → Nat.Partrec.Code} (hg : Computable g) :
    ¬ (∀ c, Nat.Partrec.Code.eval (g c) ≠ Nat.Partrec.Code.eval c) := by
  intro hfpf
  obtain ⟨c, hc⟩ := effective_floor_fixedPoint hg
  exact hfpf c hc

/-! ## § Axis 2, on the quotient — a witness relative to the computable maps that respect `eval` -/

section EvalQuotient

open Nat.Partrec

/-- `Statement:` codes identified when `Code.eval` agrees (`Setoid.ker Code.eval`). -/
def evalSetoid : Setoid Code := Setoid.ker Code.eval

/-- `Statement:` the classes of codes under equal `Code.eval`. -/
abbrev EvalClass : Type := Quotient evalSetoid

/-- `Statement:` `g` sends codes with equal `Code.eval` to codes with equal `Code.eval`. -/
def EvalRespecting (g : Code → Code) : Prop :=
  ∀ a b, Code.eval a = Code.eval b → Code.eval (g a) = Code.eval (g b)

/-- `Statement:` an `eval`-respecting map of codes, induced on the classes. -/
def liftEval (g : Code → Code) (hg : EvalRespecting g) : EvalClass → EvalClass :=
  Quotient.map g (fun a b h => hg a b h)

/-- `Statement:` the admissible class: maps on `EvalClass` induced by a computable `eval`-respecting
    map of codes. -/
def ComputableOnEval (G : EvalClass → EvalClass) : Prop :=
  ∃ g, Computable g ∧ ∃ hg : EvalRespecting g, G = liftEval g hg

/-- `Statement:` if `g` is computable, some code `a` has, at every `x`, the `Code.eval` of
    `curry a ⌜x⌝` equal to that of `g (curry x ⌜x⌝)`, where `⌜x⌝` is `x`'s Gödel number. -/
theorem exists_code_diagonal (g : Code → Code) (hc : Computable g) :
    ∃ a : Code, ∀ x, Code.eval (Code.curry a (Encodable.encode x)) =
      Code.eval (g (Code.curry x (Encodable.encode x))) := by
  let G : Code × ℕ →. ℕ := fun p => Code.eval (g (Code.curry p.1 (Encodable.encode p.1))) p.2
  have hcode : Computable fun p : Code × ℕ => g (Code.curry p.1 (Encodable.encode p.1)) :=
    hc.comp (Code.primrec₂_curry.comp Primrec.fst (Primrec.encode.comp Primrec.fst)).to_comp
  have hG : Partrec G := Code.eval_part.comp hcode Computable.snd
  have hG' : Partrec fun m : ℕ => G (Denumerable.ofNat Code m.unpair.1, m.unpair.2) :=
    hG.comp (Computable.pair ((Computable.ofNat Code).comp (Computable.fst.comp Computable.unpair))
      (Computable.snd.comp Computable.unpair))
  obtain ⟨a, ha⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hG')
  refine ⟨a, fun x => ?_⟩
  funext n
  rw [Code.eval_curry, ha]
  simp only [G, Nat.unpair_pair, Denumerable.ofNat_encode]

-- Reading (cited, not claimed): this is the square of Yanofsky 2003, Theorem 5 (p. 18), on the unary
-- computable functions, with his Remark 5 (p. 15): only the constructed maps need be representable,
-- the relativization `HasWitnessRel` makes. The curried self-application `e` below is ours, not his `f`.
-- Reading (ours): `EvalRespecting` is the condition under which a map of codes induces a map on
-- functions, φ_n ↦ φ_{h(n)}.
/-- `Statement:` `EvalClass` carries a diagonal witness relative to `ComputableOnEval`, with
    `e a x` the class of `curry a ⌜x⌝`. -/
theorem hasWitnessRel_evalClass : HasWitnessRel EvalClass ComputableOnEval := by
  refine ⟨Code, fun a x => ⟦Code.curry a (Encodable.encode x)⟧, ?_⟩
  rintro G ⟨g, hc, hg, rfl⟩
  obtain ⟨a, ha⟩ := exists_code_diagonal g hc
  exact ⟨a, funext fun x => Quotient.sound (ha x).symm⟩

-- Statement: Rogers' fixed-point theorem for computable `eval`-respecting maps, from the witness
-- (`Nat.Partrec.Code.fixed_point` is the general form, with no `eval`-respecting hypothesis).
-- Reading (cited, not claimed): an instance of Ershov's recursion theorem for precomplete numberings
-- (Ershov 1975, Z. Math. Logik Grundlagen Math. 21, 473–584; as stated in Barendregt and Terwijn 2018,
-- arXiv:1809.06233, Theorem 3.1, p. 4, where n ↦ φ_n is "the prime example", p. 2).
example (g : Code → Code) (hc : Computable g) (hg : EvalRespecting g) :
    ∃ c, Code.eval (g c) = Code.eval c := by
  obtain ⟨b, hb⟩ := fixedPoint_of_witnessRel hasWitnessRel_evalClass ⟨g, hc, hg, rfl⟩
  induction b using Quotient.ind with
  | _ c => exact ⟨c, Quotient.exact hb⟩

/-- `Statement:` CONTROL: relative to the class of all maps on `EvalClass` there is no witness: the
    map sending the class of `Code.zero` to that of a nowhere-defined code, and every other class to
    the class of `Code.zero`, fixes no class. -/
theorem no_witnessRel_evalClass_top : ¬ HasWitnessRel EvalClass (fun _ => True) := by
  classical
  obtain ⟨cn, hcn⟩ := Code.exists_code.1 Nat.Partrec.none
  have hne : (⟦Code.zero⟧ : EvalClass) ≠ ⟦cn⟧ := fun h => by
    have e := congrFun (Quotient.exact h : Code.eval Code.zero = Code.eval cn) 0
    have hd : (Code.eval Code.zero 0).Dom := (trivial : (Part.some 0).Dom)
    rw [e, hcn] at hd
    exact (hd : False)
  refine no_witnessRel_of_admissible_fpf
    (g := fun y => if y = ⟦Code.zero⟧ then ⟦cn⟧ else ⟦Code.zero⟧) trivial (fun y hy => ?_)
  dsimp only at hy
  by_cases h : y = ⟦Code.zero⟧
  · rw [if_pos h] at hy; exact hne (h ▸ hy.symm)
  · rw [if_neg h] at hy; exact h hy.symm

end EvalQuotient

/-! ## § The engine in the die's motion (`ZeroParadox/Die.lean` § XI) -/

/-- `Statement:` if `β` has a witness relative to `M` and `M g`, then the motion `Motion.ofFun g`
    (UP the identity, OVER the graph of `g`) has a point that steps to itself only; one way. -/
theorem selfOnlyAt_of_witnessRel {β : Type u} {M : (β → β) → Prop} (h : HasWitnessRel β M)
    {g : β → β} (hg : M g) : ∃ y, (Motion.ofFun g).SelfOnlyAt y := by
  obtain ⟨b, hb⟩ := fixedPoint_of_witnessRel h hg
  exact ⟨b, (Motion.selfOnlyAt_ofFun_iff g b).2 hb⟩

/-- `Statement:` under the same hypotheses, `Motion.ofFixedPoints g` (UP the partial identity on the
    fixed points of `g`) has a landing; one way. -/
theorem hasLanding_ofFixedPoints_of_witnessRel {β : Type u} {M : (β → β) → Prop}
    (h : HasWitnessRel β M) {g : β → β} (hg : M g) : (Motion.ofFixedPoints g).HasLanding := by
  obtain ⟨b, hb⟩ := fixedPoint_of_witnessRel h hg
  exact ⟨b, (Motion.isLanding_ofFixedPoints_iff g b).2 hb⟩

/-- `Statement:` if `M g` and `Motion.ofFun g` steps elsewhere at every point, `β` has no witness
    relative to `M`; one way (Cantor's form). -/
theorem no_witnessRel_of_leavesAt {β : Type u} {M : (β → β) → Prop} {g : β → β} (hg : M g)
    (hl : ∀ y, (Motion.ofFun g).LeavesAt y) : ¬ HasWitnessRel β M :=
  no_witnessRel_of_admissible_fpf hg fun x => (Motion.leavesAt_ofFun_iff g x).1 (hl x)

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms HasWitnessRel
#print axioms fixedPoint_of_witnessRel
#print axioms no_witnessRel_of_admissible_fpf
#print axioms witnessRel_antitone
#print axioms hasWitnessRel_top_of_surjective
#print axioms no_witnessRel_top_of_nontrivial
#print axioms hasWitnessRel_of_subsingleton
#print axioms witnessSet_isLowerSet
#print axioms effective_floor_fixedPoint
#print axioms no_computable_evalFixedPointFree
#print axioms evalSetoid
#print axioms EvalClass
#print axioms EvalRespecting
#print axioms liftEval
#print axioms ComputableOnEval
#print axioms exists_code_diagonal
#print axioms hasWitnessRel_evalClass
#print axioms no_witnessRel_evalClass_top
#print axioms selfOnlyAt_of_witnessRel
#print axioms hasLanding_ofFixedPoints_of_witnessRel
#print axioms no_witnessRel_of_leavesAt

end PurityCheck
