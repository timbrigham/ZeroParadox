-- EXPERIMENTAL (branch scaffolding): the next-time operator and intrinsic well-foundedness for
-- polynomial-functor coalgebras. Curated/load-bearing results are indexed in
-- ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Settheory.Coalgebra
import Mathlib.Data.PFunctor.Univariate.M
import Mathlib.Order.FixedPoints
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The next time operator: μ/ν as an INTRINSIC property, not a construction

## Engineer's Take

TODO (Tim): <your take, in your own voice.>

---

## Formal Overview (AI-assisted)

**The problem this addresses.** The corpus distinguishes the μ side from the ν side **by
construction** — `Fix`/`W` is the one built inductively, `Cofix`/`M` the one built coinductively
(`ZeroParadox/Category/CoalgebraForkPlace.lean`, `ZeroParadox/Settheory/Coalgebra.lean`). That is a
fact about *provenance*. This file gives the fork an **intrinsic test**: a property you can evaluate
on an arbitrary coalgebra without knowing how it was made.

**PRIOR ART — this is a FORMALIZATION OF PUBLISHED DEFINITIONS, not a new notion.** The operator and
the well-foundedness criterion are Adámek-Milius-Moss 2020 (arXiv:1910.09401v2), *On Well-Founded and
Recursive Coalgebras*, § 4, who credit the characterization to **Taylor** [28, Exercise VI.17] and the
operator itself to **Jacobs** (the 'next time' operator of temporal logic, there for Kripke polynomial
set functors). Source PDFs: `.claude-local/papers/adamek_milius_moss_wellfounded_recursive_coalgebras.pdf`,
`.claude-local/papers/taylor_wellfounded_coalgebras_recursion.pdf`. Their statements, quoted:

* **Def 4.1** — every coalgebra `α : A → F A` induces `⃝ : Sub(A) → Sub(A)`, `⃝(s) = α⁻¹(F s)`.
* **Ex 4.2(1)** — for a graph as a `P`-coalgebra, *"`⃝ S` is the set of vertices all of whose
  successors belong to `S`."*
* **Def 4.3** — *"A coalgebra is well-founded if `id_A` is the only fixed point of its next time
  operator."*
* **Ex 4.5(1)** — a `P`-coalgebra as a graph *"is well-founded iff it has no infinite directed path."*
* **Ex 4.5(3)** — *"If a set functor `F` fulfils `F∅ = ∅`, then the only well-founded coalgebra is the
  empty one."*

**SCOPE — deliberately the `Type`-level shadow, NOT the categorical theorem.** AMM work in a complete,
well-powered category with smooth monomorphisms, over `Sub(A)`. Here `Sub(A)` is `Set X`, the functor
is a `PFunctor`, and `⃝` is the concrete `{x | ∀ b, (α x).2 b ∈ S}`. **Nothing here formalizes AMM's
Thm 7.6, their coreflection, or recursive coalgebras**, and no claim is made that the framework's
categories satisfy their hypotheses — see
`.claude-local/notes/future-research/amm_coreflection_requirements_gap_2026-08-04.md` for what is and
is not established there.

**What this file adds over restating the definitions:** the two `Statement:` results in § III/§ IV
place the corpus's own W- and M-types on the fork **intrinsically**, so the μ/ν split stops depending
on how the objects were built. § IV is an instance of AMM Ex 4.5(3) and is credited as such.

## Structure

- § I   `nextTime`, its monotonicity, and the bundled `OrderHom`.
- § II  `IsWellFoundedCoalg`, the well-founded part as `lfp`, and their equivalence.
- § III The μ side: the W-type is well-founded (intrinsically).
- § IV  The ν side: the leaf-free M-type is NOT (intrinsically), via `∅` as a proper fixed point.
-/

namespace ZeroParadox

open PFunctor

universe u

/-! ### § I. The next time operator -/

/-- **The next time operator (AMM Def 4.1, at the `Type` level).** For a `P`-coalgebra
`α : X → P.Obj X`, `nextTime` sends a set `S` to the set of points **all of whose children lie in
`S`**. This is AMM's `⃝(s) = α⁻¹(F s)` made concrete for a polynomial functor: `F s` as a subobject of
`P.Obj X` is `{⟨a, f⟩ | ∀ b, f b ∈ S}`, and its inverse image under `α` is exactly this. -/
def nextTime {X : Type u} {P : PFunctor.{u, u}} (α : X → P.Obj X) (S : Set X) : Set X :=
  {x | ∀ b, (α x).2 b ∈ S}

/-- `nextTime` is monotone: enlarging the target set can only enlarge the set of points whose
children all land in it. (AMM note `⃝` is monotone; it is what lets Knaster-Tarski apply.) -/
theorem nextTime_mono {X : Type u} {P : PFunctor.{u, u}} (α : X → P.Obj X) :
    Monotone (nextTime α) := by
  sorry

/-- `nextTime` bundled as an order homomorphism on the complete lattice `Set X`, so Mathlib's
fixed-point API applies. -/
def nextTimeHom {X : Type u} {P : PFunctor.{u, u}} (α : X → P.Obj X) : Set X →o Set X :=
  ⟨nextTime α, nextTime_mono α⟩

/-! ### § II. Well-foundedness, intrinsically -/

/-- **Well-founded coalgebra (AMM Def 4.3).** The only fixed point of the next time operator is the
whole carrier. AMM state it as *"`id_A` is the only fixed point"*; `id_A` as a subobject of `X` is
`Set.univ`. **Note this is a property of `α` alone** — nothing about how `X` was constructed. -/
def IsWellFoundedCoalg {X : Type u} {P : PFunctor.{u, u}} (α : X → P.Obj X) : Prop :=
  ∀ S : Set X, nextTime α S = S → S = Set.univ

/-- **The well-founded part (AMM § 5), as a least fixed point.** AMM prove the well-founded part is
the least fixed point of the next time operator; Knaster-Tarski supplies it here because `Set X` is a
complete lattice and `nextTime` is monotone. **NOT claimed:** that this is the coreflection into
well-founded coalgebras — that is AMM's theorem and is not formalized here. -/
def wfPart {X : Type u} {P : PFunctor.{u, u}} (α : X → P.Obj X) : Set X :=
  OrderHom.lfp (nextTimeHom α)

/-- **The two agree.** A coalgebra is well-founded exactly when its well-founded part is everything.
(⟸ every fixed point contains the least one, so if `lfp` is already `univ` nothing smaller can be
fixed; ⟹ `lfp` is itself a fixed point, so it must be `univ`.) -/
theorem isWellFoundedCoalg_iff_wfPart_univ {X : Type u} {P : PFunctor.{u, u}}
    (α : X → P.Obj X) : IsWellFoundedCoalg α ↔ wfPart α = Set.univ := by
  sorry

/-! ### § III. The μ side — the W-type is well-founded INTRINSICALLY -/

/-- **`Statement:` the W-type passes the intrinsic test.** For any polynomial functor `P`, the
canonical coalgebra `W.dest : W P → P.Obj (W P)` is well-founded in AMM's sense: the only set closed
under "all children lie in it" is everything. **The proof is structural induction on the W-type** —
which is the honest content: well-foundedness of `W` *is* the availability of that induction,
restated as a fixed-point property. Compare AMM Ex 4.5(2) (the initial algebra, as a coalgebra, is
well-founded); this is the concrete W-type case. -/
theorem wtype_wellFounded {P : PFunctor.{u, u}} :
    IsWellFoundedCoalg (P := P) W.dest := by
  sorry

/-! ### § IV. The ν side — the leaf-free M-type FAILS the test -/

/-- The leaf-free M-type is inhabited: corecursion builds the infinite unary tree. (The corpus's
`cofix_nonempty` is the `QPF.Cofix` counterpart; this is the `PFunctor.M` one, stated here because
§ IV's separation needs an inhabitant.) -/
theorem idPF_M_nonempty : Nonempty (M idPF_Coalgebra) := by
  sorry

/-- `∅` is a fixed point of the next time operator on the leaf-free M-type. Every node of
`idPF_Coalgebra = ⟨PUnit, fun _ => PUnit⟩` has a child, so "all children lie in `∅`" is unsatisfiable
— `nextTime` sends `∅` to `∅`. **This is the whole obstruction**: a proper fixed point exists. -/
theorem idPF_M_nextTime_empty :
    nextTime (P := idPF_Coalgebra) M.dest ∅ = ∅ := by
  sorry

/-- **`Statement:` the M-type FAILS the intrinsic test.** `∅` is a fixed point of next time and the
carrier is inhabited, so `∅ ≠ Set.univ` and well-foundedness fails. **This is an instance of AMM
Ex 4.5(3)** (`F∅ = ∅` forces the only well-founded coalgebra to be the empty one) — the credit is
theirs; what is added is the concrete witness on the corpus's own leaf-free functor. -/
theorem idPF_M_not_wellFounded :
    ¬ IsWellFoundedCoalg (P := idPF_Coalgebra) M.dest := by
  sorry

/-- **The fork, intrinsically.** Same functor, two carriers: the W-type passes AMM's test and the
M-type fails it. `Reading:` the framework reads this as the μ/ν root cut — but note what is and is not
proved. **`Statement:`** the two carriers differ on a property of the coalgebra alone. **NOT proved:**
that this property *is* the μ/ν distinction in general, or that either carrier is initial/final (that
is `CoalgebraForkPlace.lean`'s scope, and `QPF.Fix.rec_unique` is where the uniqueness half lives). -/
theorem fork_is_intrinsic :
    IsWellFoundedCoalg (P := idPF_Coalgebra) W.dest ∧
      ¬ IsWellFoundedCoalg (P := idPF_Coalgebra) M.dest := by
  sorry

end ZeroParadox

/-! ## Axiom Purity Check

Measured, not predicted — `#print axioms` follows the STATEMENT, so the `M` results are expected to
carry choice via `M.dest` (see the measured table in `CLAUDE.md`: `PFunctor.M.dest` is
`[propext, Classical.choice, Quot.sound]`) while the `W` side should be clean. Read the output; do not
assume it. -/

section PurityCheck
open ZeroParadox

#print axioms nextTime
#print axioms nextTime_mono
#print axioms IsWellFoundedCoalg
#print axioms wfPart
#print axioms isWellFoundedCoalg_iff_wfPart_univ
#print axioms wtype_wellFounded
#print axioms idPF_M_nonempty
#print axioms idPF_M_nextTime_empty
#print axioms idPF_M_not_wellFounded
#print axioms fork_is_intrinsic

end PurityCheck
