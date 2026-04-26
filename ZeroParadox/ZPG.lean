import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Iso
import Mathlib.Tactic

/-!
# ZP-G: Category Theory

Formal verification of ZP-G v1.1 (Category Theory layer).
Self-contained in category theory with one named import (I-KC, Kolmogorov complexity).

Axioms: AX-G1 (initial object exists; no terminal object), AX-G2 (source asymmetry).
Theorems: T1 (initial uniqueness), T2 (universal constituent), T3 (unreachability),
T4 (forward-only chains), T6-a/b/c (surprisal properties), T6 (informational singularity),
T7 (Categorical Zero Paradox).
T5 (functors preserve initial objects) deferred to ZP-H T-H1.
D7' (native categorical surprisal) modelled as abstract class parameter (I-KC import).
-/

namespace ZeroParadox.ZPG

open CategoryTheory CategoryTheory.Limits

/-! ## I. ZPCategory — AX-G1 + AX-G2 -/

/-- ZPCategory bundles the two ZP-G foundational axioms onto a given category.
    AX-G1: there is an initial object 0; there is no terminal object.
    AX-G2: hom(X, 0) = ∅ for any X not isomorphic to 0 (source asymmetry). -/
class ZPCategory (C : Type*) [Category C] where
  zpInitial : C
  zpIsInitial : IsInitial zpInitial
  ax_g1_no_terminal : ∀ t : C, IsEmpty (IsTerminal t)
  ax_g2 : ∀ (X : C), IsEmpty (X ≅ zpInitial) → IsEmpty (X ⟶ zpInitial)

/-! ## II. ZPSurprisal — I-KC Import (D7') -/

/-- ZPSurprisal models the I-KC import: conditional Kolmogorov complexity K(x_B | x_A).
    D7' assigns surprisal I(f) = K(x_B | x_A) to each morphism f: A → B.
    K is well-defined up to additive constant c; structural claims (zero/undefined/finite)
    are constant-invariant. T6-a (I(id_A) = 0) is an I-KC axiom, not Lean-derivable. -/
class ZPSurprisal (C : Type*) [Category C] [ZPCategory C] where
  surp : {A B : C} → (A ⟶ B) → ℕ
  surp_id : ∀ (A : C), surp (𝟙 A) = 0

/-! ## III. T1–T4 — Core Categorical Theorems -/

/-- T1 — Uniqueness of the Initial Object.
    Any two initial objects in C are uniquely isomorphic.
    Standard category theory; immediate from IsInitial.uniqueUpToIso. -/
theorem t1_initial_unique {C : Type*} [Category C] [ZPCategory C]
    {A B : C} (hA : IsInitial A) (hB : IsInitial B) : Nonempty (A ≅ B) :=
  ⟨hA.uniqueUpToIso hB⟩

/-- T2 — Universal Constituent (AX-G1 / D3).
    The initial object 0 maps uniquely to every object X. -/
theorem t2_universal_constituent {C : Type*} [Category C] [ZPC : ZPCategory C] (X : C) :
    ∃ f : ZPC.zpInitial ⟶ X, ∀ g : ZPC.zpInitial ⟶ X, f = g :=
  ⟨ZPC.zpIsInitial.to X, fun g => ZPC.zpIsInitial.hom_ext _ g⟩

/-- T3 — Unreachability of 0 (AX-G2).
    For any X not isomorphic to 0, hom(X, 0) = ∅. Direct from AX-G2. -/
theorem t3_unreachability {C : Type*} [Category C] [ZPC : ZPCategory C]
    (X : C) (hne : IsEmpty (X ≅ ZPC.zpInitial)) :
    IsEmpty (X ⟶ ZPC.zpInitial) :=
  ZPC.ax_g2 X hne

/-- T4 — Chains are Forward-Only (AX-G2).
    No morphism chain starting at 0 can return to 0 through a non-initial object.
    Consequence of T3: the terminal node of any such chain satisfies T3. -/
theorem t4_chains_forward_only {C : Type*} [Category C] [ZPC : ZPCategory C]
    (X : C) (hne : IsEmpty (X ≅ ZPC.zpInitial))
    (_f : ZPC.zpInitial ⟶ X) :
    IsEmpty (X ⟶ ZPC.zpInitial) :=
  t3_unreachability X hne

/-! ## IV. T6 — Informational Singularity (D7', I-KC) -/

/- Lean Scope Note — T6-b/c versus PDF Claims
   The PDF's T6-b proves strict inequality: I(f) > 0 when A ≇ 0 (the empty program
   cannot reproduce x_B from x_A when they encode distinct states). The PDF's T6-c
   establishes monotone accumulation via subadditivity of K:
     K(x_n|x_0) ≤ ∑ K(x_{k+1}|x_k) + O(n·c).
   Neither claim is captured by ZPSurprisal. That typeclass abstracts only the
   structural skeleton of K — surp_id (zero identity surprisal) and surp : hom → ℕ
   (non-negative by type). The Lean proofs of T6-b and T6-c reduce to Nat.zero_le _,
   which is trivially true for any ℕ-valued function, not K-specifically derived.
   This is the same category as DA-1 Path 3 (AIT bridge) in ZPE.lean §VI: the
   K-specific content is mathematically sound and drives the PDF derivation, but
   requires a full K-formalization to verify in Lean. The I-KC import marks this
   boundary: structural implications are Lean-verified; AIT content is not. -/

/-- T6-a — Surprisal of Identity is Zero.
    I(id_A) = K(x_A | x_A) = 0 (up to c): the empty program reproduces x_A given x_A.
    From I-KC (ZPSurprisal.surp_id). -/
theorem t6a_identity_surprisal {C : Type*} [Category C] [ZPCategory C]
    [ZPS : ZPSurprisal C] (A : C) :
    ZPS.surp (𝟙 A) = 0 :=
  ZPS.surp_id A

/-- T6-b — Non-Negative Surprisal.
    I(f) = K(x_B | x_A) ≥ 0: program length is non-negative.
    Trivially true since surp : ... → ℕ. -/
theorem t6b_surprisal_nonneg {C : Type*} [Category C] [ZPCategory C]
    [ZPS : ZPSurprisal C] {A B : C} (f : A ⟶ B) :
    0 ≤ ZPS.surp f :=
  Nat.zero_le _

/-- T6-c — Surprisal Sum is Non-Negative.
    The total surprisal ∑ I(X_k → X_{k+1}) over a morphism chain of length n is ≥ 0.
    Proved by non-negativity of ℕ (Nat.zero_le). This establishes a lower bound only;
    the divergence claim (surprisal → ∞ along sequences approaching 0) is a separate
    result proved in ZPC.t2_diverges, which uses the specific structure of Q₂. -/
theorem t6c_surprisal_sum_nonneg {C : Type*} [Category C] [ZPCategory C]
    [ZPS : ZPSurprisal C] {n : ℕ}
    (objs : Fin (n + 1) → C)
    (morphs : ∀ k : Fin n, objs k.castSucc ⟶ objs k.succ) :
    0 ≤ Finset.sum Finset.univ (fun k => ZPS.surp (morphs k)) :=
  Nat.zero_le _

/-- T6 — Informational Singularity of 0.
    Part I: outward surprisal from 0 is defined and non-negative (T6-b).
    Part II: inward surprisal to 0 is undefined — no morphism X → 0 exists for X ≇ 0 (T3).
    The initial object is the unique informational singularity: accessible outward, a dead
    end inward. The singularity is structural (domain-absent), not numerical (divergence). -/
theorem t6_informational_singularity {C : Type*} [Category C] [ZPC : ZPCategory C]
    [ZPS : ZPSurprisal C]
    (X : C) (hne : IsEmpty (X ≅ ZPC.zpInitial)) :
    (∀ f : ZPC.zpInitial ⟶ X, 0 ≤ ZPS.surp f) ∧
    IsEmpty (X ⟶ ZPC.zpInitial) :=
  ⟨fun f => t6b_surprisal_nonneg f, t3_unreachability X hne⟩

/-! ## V. T7 — The Categorical Zero Paradox (Closing Theorem) -/

/-- T7 — The Categorical Zero Paradox.
    Assembly of T2, T3, T4, T6. 0 is simultaneously the universal categorical source
    (Part I) and the unique object unreachable from outside (Part II). Chains from 0 are
    forward-only (Part III). 0 is an informational singularity: defined outward,
    undefined inward (Part IV). The paradox is a structural inversion, not a contradiction.
    Dependencies: AX-G1, AX-G2, D3, D5, D7', I-KC, T2, T3, T4, T6. BA-G1 not a dependency. -/
theorem t7_categorical_zero_paradox {C : Type*} [Category C] [ZPC : ZPCategory C]
    [ZPS : ZPSurprisal C] :
    (∀ X : C, ∃ f : ZPC.zpInitial ⟶ X, ∀ g : ZPC.zpInitial ⟶ X, f = g) ∧
    (∀ X : C, IsEmpty (X ≅ ZPC.zpInitial) → IsEmpty (X ⟶ ZPC.zpInitial)) ∧
    (∀ X : C, IsEmpty (X ≅ ZPC.zpInitial) → ∀ _f : ZPC.zpInitial ⟶ X,
      IsEmpty (X ⟶ ZPC.zpInitial)) ∧
    (∀ X : C, IsEmpty (X ≅ ZPC.zpInitial) →
      (∀ f : ZPC.zpInitial ⟶ X, 0 ≤ ZPS.surp f) ∧ IsEmpty (X ⟶ ZPC.zpInitial)) :=
  ⟨t2_universal_constituent, ZPC.ax_g2,
   fun X hne _f => t3_unreachability X hne,
   fun X hne => t6_informational_singularity X hne⟩

/-! T5 — Functors Preserve Initial Objects. Deferred to ZP-H T-H1.
    For each instantiation functor F ∈ {F_A, F_B, F_C, F_D}, F(0) is initial in the codomain.
    Verified by direct universal property check in ZP-H. No Lean theorem here — a vacuous
    `True := trivial` stub would misrepresent the theorem list. -/

end ZeroParadox.ZPG

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPG CategoryTheory

#print axioms t1_initial_unique
#print axioms t2_universal_constituent
#print axioms t3_unreachability
#print axioms t4_chains_forward_only
#print axioms t6a_identity_surprisal
#print axioms t6b_surprisal_nonneg
#print axioms t6c_surprisal_sum_nonneg
#print axioms t6_informational_singularity
#print axioms t7_categorical_zero_paradox

end PurityCheck

/-! ## Appendix — ForkCat: A Concrete ZPCategory Instance

Closes the vacuity risk identified in peer review: every ZPG theorem is universally
quantified over [ZPCategory C] with no concrete C exhibited. ForkCat provides one.

Objects: zero (initial), left, right. Morphisms: identities plus zero → left and
zero → right, nothing else. Zero is initial; no terminal object exists; AX-G2 holds.
-/

section ForkCat

open ZeroParadox.ZPG CategoryTheory CategoryTheory.Limits

/-- Three objects: the initial zero and two non-initial leaves. -/
inductive ForkObj : Type | zero | left | right deriving DecidableEq

/-- Morphisms: one identity per object, plus two arrows out of zero. Nothing else. -/
inductive ForkHom : ForkObj → ForkObj → Type
  | idZ : ForkHom .zero  .zero
  | toL : ForkHom .zero  .left
  | toR : ForkHom .zero  .right
  | idL : ForkHom .left  .left
  | idR : ForkHom .right .right

instance {X Y : ForkObj} : Subsingleton (ForkHom X Y) :=
  ⟨fun f g => by cases f <;> cases g <;> rfl⟩

private def forkId : ∀ (X : ForkObj), ForkHom X X
  | .zero  => .idZ
  | .left  => .idL
  | .right => .idR

private def forkComp : ∀ {X Y Z : ForkObj}, ForkHom X Y → ForkHom Y Z → ForkHom X Z
  | _, _, _, .idZ, .idZ => .idZ
  | _, _, _, .idZ, .toL => .toL
  | _, _, _, .idZ, .toR => .toR
  | _, _, _, .toL, .idL => .toL
  | _, _, _, .toR, .idR => .toR
  | _, _, _, .idL, .idL => .idL
  | _, _, _, .idR, .idR => .idR

instance forkCategory : Category ForkObj where
  Hom   := ForkHom
  id    := forkId
  comp  := forkComp
  id_comp := fun f => by cases f <;> rfl
  comp_id := fun f => by cases f <;> rfl
  assoc   := fun f g h => by cases f <;> cases g <;> cases h <;> rfl

instance (Y : ForkObj) : Unique (ForkObj.zero ⟶ Y) where
  default := match Y with | .zero => .idZ | .left => .toL | .right => .toR
  uniq    := fun f => by cases f <;> rfl

noncomputable instance forkZPCategory : ZPCategory ForkObj where
  zpInitial        := .zero
  zpIsInitial      := IsInitial.ofUnique ForkObj.zero
  ax_g1_no_terminal := by
    intro t; exact ⟨fun ht =>
      match t with
      | .zero  => nomatch (ht.from .left)
      | .left  => nomatch (ht.from .right)
      | .right => nomatch (ht.from .left)⟩
  ax_g2 := by
    intro X hX
    match X with
    | .zero  => exact hX.elim (Iso.refl ForkObj.zero)
    | .left  => exact ⟨fun f => nomatch f⟩
    | .right => exact ⟨fun f => nomatch f⟩

end ForkCat
