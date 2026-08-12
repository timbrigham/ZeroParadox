-- EXPERIMENTAL (branch scaffolding): the next-time operator and intrinsic well-foundedness for
-- polynomial-functor coalgebras. Curated/load-bearing results are indexed in
-- ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Settheory.Coalgebra
import ZeroParadox.Computability.NatListRegime
import Mathlib.Data.PFunctor.Univariate.M
import Mathlib.Order.FixedPoints
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The next time operator: μ/ν as an INTRINSIC property, not a construction

## Engineer's Take

While working through the span question with my AI assistant, we ran into this. I do not recognize the
nomenclature here and I recognize the concept. That is the short version of why this got built.

When the category list came back, three of the four lines sounded really damn familiar. That is what
made me want to keep pulling on it.

The question I was actually asking is whether this is one of those meta level cases where these are the
requirements we need to meet, and the commonly named version of the requirements that need to be met
already has a name somewhere. It turned out that it does.

A build is fine here assuming step zero has been properly taken. I defer to my AI assistant regarding
the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

**The problem this addresses.** The corpus distinguishes the μ side from the ν side **by
construction** — `Fix`/`W` is the one built inductively, `Cofix`/`M` the one built coinductively
(`ZeroParadox/Category/CoalgebraForkPlace.lean`, `ZeroParadox/Settheory/Coalgebra.lean`). That is a
fact about *provenance*. This file gives the fork an **intrinsic test**: a property you can evaluate
on an arbitrary coalgebra without knowing how it was made.

**PRIOR ART — this is a FORMALIZATION OF PUBLISHED DEFINITIONS, not a new notion.** The operator and
the well-foundedness criterion are Adámek-Milius-Moss 2020 (arXiv:1910.09401v2), *On Well-Founded and
Recursive Coalgebras*, § 4. They credit the characterization to **Taylor** and the operator itself to
**Jacobs** (the 'next time' operator of temporal logic, there for Kripke polynomial set functors).

⚠ **Where to verify the Taylor credit.** AMM cite it as their ref [28, Exercise VI.17], and their [28]
is **Taylor, *Practical Foundations of Mathematics* (CUP 1999)** — which this project does **not**
hold. The Taylor PDF that *is* in `.claude-local/papers/` is his *Well founded coalgebras and
recursion*, a **different document, which does not contain Exercise VI.17**; do not send a reader
there for it.

Source PDF for every quotation below:
`.claude-local/papers/adamek_milius_moss_wellfounded_recursive_coalgebras.pdf`. Their statements —
the bulleted ones in quote marks are verbatim; Def 4.1 is their notation transcribed:

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
Thm 7.6, their coreflection, or recursive coalgebras.**

⚠ **But the hypotheses ARE now checked for THIS setting — see § V, and read that table for which.**
This paragraph previously also said *"no claim is made that the framework's categories satisfy their
hypotheses"*, which § V made false and which sat here contradicting it. **Scope the two apart:** § V
covers `Type u` with `ofTypeFunctor P.Obj` only, and **says nothing about the MC-1 carriers**
(`TopCat`, `ModuleCat ℂ`, `KleisliCat PMF`) — those remain unchecked, and that is what
`.claude-local/notes/future-research/amm_coreflection_requirements_gap_2026-08-04.md` tracks.

**What this file adds over restating the definitions:** the two `Statement:` results in § III/§ IV
place the corpus's own W- and M-types on the fork **intrinsically**, so the μ/ν split stops depending
on how the objects were built. § IV is an instance of AMM Ex 4.5(3) and is credited as such.

## Structure

- § I   `nextTime`, its monotonicity, and the bundled `OrderHom`.
- § II  `IsWellFoundedCoalg`, the well-founded part as `lfp`, and their equivalence.
- § III The μ side: the W-type is well-founded (intrinsically).
- § IV  The ν side: the leaf-free M-type is NOT (intrinsically), via `∅` as a proper fixed point;
        then the fork bundle — **whose μ half is vacuous at that functor, disclosed in place** — and a
        non-vacuous μ witness at the leaf-carrying `1 + X`.
- § V   AMM Thm 7.6's ambient hypotheses, verified for this setting: `F`-preservation and smoothness
        clauses (b) and (c); plus `wtypeFixedPoint` / `mtypeFixedPoint`, the bridges to its subject.
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
  intro S T hST x hx b
  exact hST (hx b)

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
  constructor
  · intro hwf
    exact hwf _ (OrderHom.map_lfp (nextTimeHom α))
  · intro hlfp S hS
    have hle : wfPart α ≤ S := OrderHom.lfp_le _ (le_of_eq hS)
    rw [hlfp] at hle
    exact Set.eq_univ_of_univ_subset hle

/-! ### The corpus's other contact with this literature — the RECURSIVE side, not formalized here.

AMM's companion notion is **recursive**: every algebra admits a *unique* coalgebra-to-algebra
morphism (Def 3.2 p. 11). `ZeroParadox/Settheory/APG.lean`'s `decoration_unique` proves exactly that
uniqueness clause for a finite quiver — and NOT via the well-foundedness above, since those quivers
may carry cycles. It closes because its target sends every cyclic vertex to ⊥. -/

/-! ### § III. The μ side — the W-type is well-founded INTRINSICALLY -/

/-- **`Statement:` the W-type passes the intrinsic test.** For any polynomial functor `P`, the
canonical coalgebra `W.dest : W P → P.Obj (W P)` is well-founded in AMM's sense: the only set closed
under "all children lie in it" is everything. **The proof is structural induction on the W-type**, and
that is the honest content: the induction principle *yields* AMM-well-foundedness here. `Reading:` the
framework reads the two as one fact in different clothes — a **COINCIDENCE** kind, and conjectural:
**only that direction is proved, and no converse is claimed.** Compare AMM Ex 4.5(2) (the initial
algebra, as a coalgebra, is well-founded); this is the concrete W-type case. -/
theorem wtype_wellFounded {P : PFunctor.{u, u}} :
    IsWellFoundedCoalg (P := P) W.dest := by
  intro S hS
  ext x
  simp only [Set.mem_univ, iff_true]
  induction x with
  | mk a f ih =>
      have hmem : (WType.mk a f) ∈ nextTime (P := P) W.dest S := fun b => ih b
      rw [hS] at hmem
      exact hmem

/-! ### § IV. The ν side — the leaf-free M-type FAILS the test -/

/-- The leaf-free M-type is inhabited: corecursion builds the infinite unary tree. (The corpus's
`cofix_nonempty` is the `QPF.Cofix` counterpart; this is the `PFunctor.M` one, stated here because
§ IV's separation needs an inhabitant.) -/
theorem idPF_M_nonempty : Nonempty (M idPF_Coalgebra) :=
  ⟨M.corec (fun _ : Unit => (⟨(), fun _ => ()⟩ : idPF_Coalgebra.Obj Unit)) ()⟩

/-- `∅` is a fixed point of the next time operator on the leaf-free M-type. Every node of
`idPF_Coalgebra = ⟨PUnit, fun _ => PUnit⟩` has a child, so "all children lie in `∅`" is unsatisfiable
— `nextTime` sends `∅` to `∅`. ⚠ This proves only that `∅` is **a** fixed point; that it is a
**proper** one needs the carrier to be inhabited, which is `idPF_M_nonempty`, and the two are combined
in `idPF_M_not_wellFounded` below. -/
theorem idPF_M_nextTime_empty :
    nextTime (P := idPF_Coalgebra) M.dest ∅ = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hx PUnit.unit

/-- **`Statement:` the M-type FAILS the intrinsic test.** `∅` is a fixed point of next time and the
carrier is inhabited, so `∅ ≠ Set.univ` and well-foundedness fails. **This is an instance of AMM
Ex 4.5(3)** (`F∅ = ∅` forces the only well-founded coalgebra to be the empty one) — the credit is
theirs; what is added is the concrete witness on the corpus's own leaf-free functor. -/
theorem idPF_M_not_wellFounded :
    ¬ IsWellFoundedCoalg (P := idPF_Coalgebra) M.dest := by
  intro hwf
  obtain ⟨m⟩ := idPF_M_nonempty
  have huniv : (∅ : Set (M idPF_Coalgebra)) = Set.univ := hwf ∅ idPF_M_nextTime_empty
  have : m ∈ (∅ : Set (M idPF_Coalgebra)) := by rw [huniv]; exact Set.mem_univ m
  exact this

/-- **The fork at the leaf-free functor — and it is DEGENERATE on the μ side. Read the fence.**

`Statement:` the two carriers differ on a property of the coalgebra alone.

⚠ **The μ half here is VACUOUS, and saying so is the point.** `W idPF_Coalgebra` is **empty** — the
corpus proves it axiom-free as `w_isEmpty` (`ZeroParadox/Computability/ChoicePurityInvariant.lean`) —
so this conjunct holds because `∅ = Set.univ` on an empty carrier. (The proof term used is
`wtype_wellFounded`, which inducts. `w_isEmpty` discharges the conjunct directly instead — but it is
itself `WType.recOn`, so the induction is **relocated, not removed**.) That
is not a surprise: it is forced by **AMM Ex 4.5(3)**, quoted in this file's overview (`F∅ = ∅` makes the
empty coalgebra the only well-founded one), and `F∅ = ∅` holds for `idPF_Coalgebra`. **So at THIS
functor the bundle carries the same content as the corpus's existing `categorical_fork_strict`
(`ZeroParadox/Settheory/Coalgebra.lean`), and emptiness is a fact about how the carrier was built —
exactly what an "intrinsic" test was supposed to stop depending on.** For a non-vacuous μ witness see
`natPF_wtype_wellFounded_and_inhabited` below; the general `wtype_wellFounded` (arbitrary `P`) is
untouched by this and is where the non-degenerate content lives.

`Reading:` **CARRIER kind**, conjectural — the framework reads the two carriers' disagreement as the
μ/ν root cut. **NOT proved:** that this property *is* the μ/ν distinction in general, nor that either
carrier is initial/final. On initiality, `QPF.Fix.rec_unique` is the Mathlib route;
`ZeroParadox/Category/CoalgebraForkPlace.lean` explicitly does **not** prove it (it states existence +
commutation only, and repeats that fence throughout).

**Prior art for the general shape.** **AMM Thm 7.6** (p. 30) says *"the only well-founded fixed point is
the initial algebra."* This file's fork has the **shape** of that statement.

**Every hypothesis of Thm 7.6 is now verified for this setting, and both bridges to its subject are
built.** Ambient hypotheses: see the table below, all four. Subject: `wtypeFixedPoint` /
`mtypeFixedPoint` (§ V) put both carriers among its *fixed points*, and
`ZeroParadox/Category/NextTimeCategorical.lean`'s `isWellFoundedCoalgCat_iff` transports the predicate.

⚠ **AND THAT IS STILL NOT A PROOF OF Thm 7.6, so read what it does license carefully.** Thm 7.6 is
**not formalized** anywhere in this corpus, and Mathlib has no well-founded-coalgebra machinery to
formalize it with. What is now available is its **conclusion, by citation**, for this setting — because
its assumptions are discharged and its subject is connected. That is what "instance of" means here and
it is strictly weaker than a Lean derivation. **Do not write "we proved Thm 7.6."**

⚠ **Two further fences on the ambient table.**

**(1) How the separately-indexed clauses cover AMM's λ-chains — including λ = 0, which is the case that
needs saying.** Clause (a) is the Mathlib instance `Types.hasColimitsOfShape`; clauses (b) and (c) are
proved here over `IsFilteredOrEmpty` and over filtered-and-connected index categories respectively. For
**λ > 0** a λ-chain is filtered and connected, so all three apply directly. For **λ = 0** — which AMM
§ 2.5 explicitly includes — the empty category is **neither** filtered nor connected, and the coverage
is instead: (a) still applies; **(b) is vacuous**, an empty cocone having no legs; and (c)'s λ = 0
instance **is** AMM's trailing *"every morphism from 0 is monic"*, which is why they write "In
particular" — immediate in `Type u`, since every map out of the empty type is injective. ⚠ So the
`IsFilteredOrEmpty` weakening on (b) buys applicability where there is **no content**; do not read it
as covering more mathematics than the `IsFiltered` version did.

⚠ **But AMM's Def 2.14 itself is NOT formalized**, and no declaration here asserts "`Type u` has smooth
monomorphisms" as a single proposition — the paragraph above is the argument that the pieces suffice,
written in prose and checkable by reading, not a theorem.

**(2)** The whole table is about **`Type u` with `ofTypeFunctor P.Obj`** and says nothing
about the MC-1 carriers (`TopCat`, `ModuleCat ℂ`, `KleisliCat PMF`), which remain unchecked — see
`.claude-local/notes/future-research/amm_coreflection_requirements_gap_2026-08-04.md`. Both smoothness
theorems also take `{J : Type u}`, so they reach λ-chains for `Type u`-small λ; AMM quantify over every
ordinal.

*(Earlier rounds counted the ambient hypotheses — one, then two, then three, now four — as though the
count were the whole story. It never was: Thm 7.6 is about fixed points and initial algebras, so
connecting to its **subject** was always a separate axis from its **hypotheses**. Both axes are now
closed; the record is kept because the counting recurred four times.)*

The bridges to its subject:

1. **The predicate transport — CLOSED 2026-08-05.** `IsWellFoundedCoalg` is stated over `Set X` with
   `nextTime`; AMM Def 4.3 is stated over `Sub(A)` in a **category**. Both are now built and proved
   equivalent in `ZeroParadox/Category/NextTimeCategorical.lean` (`isWellFoundedCoalgCat_iff`).
   ⚠ **This paragraph previously prescribed going through `Types.subobjectEquivSet` and called that
   "bounded work, not research". THAT ROUTE DOES NOT WORK** — that iso is built from
   `Equivalence.thinSkeletonOrderIso`, which selects quotient representatives, so it is
   `noncomputable` and nothing reduces through it; Mathlib supplies no computation lemmas for it. The
   route that works descends with `Quotient.lift` instead, taking well-definedness from `Set X` being a
   partial order. **Do not re-attempt the `subobjectEquivSet` route** — see that file's technique note.
2. **"Fixed point" in AMM's sense — CLOSED.** AMM mean the structure map is **invertible**. Now
   witnessed: `wtypeFixedPoint` and `mtypeFixedPoint` in § V.

**Both axes are now closed** — the ambient hypotheses (all four, table below) and the subject (both
bridges). The counting recurred for four rounds because it was never the whole story; the subject was
always the other half. The ambient hypotheses are
recorded below anyway: measuring them was worth doing, the results are reusable, and they are simply
**not the blocker**. Thm 7.6 holds in *"a complete and well-powered category with smooth
monomorphisms"* for *"F preserving monomorphisms."* The setting here is **`Type u`**, Lean's category of
types — the type-theoretic analogue of **Set** (AMM's Ex 2.15(1) grants Set universally smooth
monomorphisms), and not literally Set, which is why each was checked rather than inherited:

| hypothesis | status | where |
|---|---|---|
| complete | **HOLDS** | `Limits.Types.hasLimitsOfSize` |
| well-powered | **HOLDS** | `instWellPoweredType`, `Mathlib/CategoryTheory/Subobject/Types.lean` |
| smooth monomorphisms | **all three clauses witnessed** | (a) `Types.hasColimitsOfShape`; (b) `mono_colimit_ι_of_mono` in § V; (c) `smooth_monos_factorizing` in § V. AMM's trailing *"every morphism from 0 is monic"* is immediate — every map out of the empty type is injective |
| `F` preserves monomorphisms | **HOLDS** | `preservesMonomorphisms_ofTypeFunctor` in § V |

⚠ **CLAUSE (b) WAS THE LAST HOLE AND IS NOW CLOSED** (`mono_colimit_ι_of_mono`, § V) — the record of
how it was got wrong is kept because it was got wrong twice. Def 2.14(1)'s clause (b) is *"its colimit
cocone is formed by monomorphisms"*, a statement about the **legs** `c.ι.app j`. An earlier version of
this table cited `Types.instIsStableUnderFilteredColimitsMonomorphismsType` for it; **that instance
states a different proposition** — given a natural transformation with monic components between two
diagrams, the induced map *between the two colimit vertices* is monic. **The legs and the vertex map
are not the same statement**, and the obvious instantiation (second diagram constant at `X.obj j`) does
not bridge them: such a transformation is a cone over `X` with that vertex, and need not exist. A
second attempt named `IsStableUnderTransfiniteComposition` plus cofinality of the tail `[j, λ)` — a
real route, and longer than the one actually used. **Do not restore either citation.**

⚠ **Verified hypotheses are not a formalized theorem, and what the citation buys is narrow.** AMM
Thm 7.6 is **not** proved in Lean here, and Mathlib has no well-founded-coalgebra machinery to prove it
with. What Thm 7.6 would deliver, given its hypotheses, is that a well-founded fixed point **is the
initial algebra** — i.e. it *concludes* initiality rather than assuming it, which is why the
`fork_is_intrinsic` fence above ("not proved: that either carrier is initial/final") is consistent with
citing it. That conclusion is available **by citation only**. Do not upgrade this to "we proved
Thm 7.6," and do not read the fence as denying what Thm 7.6 offers.

⚠ **THIS TABLE WAS WRONG FOUR TIMES, AND THAT IS THE LESSON.** Measured from this file's own history:
*one* (`477e2f9`) → *two* (`1d9683f`) → **_four_, wrongly** (`c2b3e95`) → *three* (`8648d90`) → four,
correctly (`00f6c67`). ⚠ **The direction was NOT always the same** — an earlier version of this line
claimed it was. The `c2b3e95` state **over**counted, on the strength of a mis-citation for clause (b),
and was corrected back down; that one was an unverified **positive**, the mirror of the rest. **Not one of those errors was a wrong theorem — each
was an unverified negative**: `WellPowered (Type 0)` fails on an unimported name and an unresolved
universe parameter; `PreservesMonomorphisms` "does not synthesize" is true of the *instance database*
and false of the *fact*; and smooth monomorphisms is **assembled from** pieces in the pin though no
declaration bears the name. A failed `#synth` is evidence about the probe. See `CLAUDE.md`
§ *"NOT IN THE LIBRARY" IS A CLAIM*, and
`.claude-local/notes/future-research/amm_coreflection_requirements_gap_2026-08-04.md` § 4b. -/
theorem fork_is_intrinsic :
    IsWellFoundedCoalg (P := idPF_Coalgebra) W.dest ∧
      ¬ IsWellFoundedCoalg (P := idPF_Coalgebra) M.dest :=
  ⟨wtype_wellFounded, idPF_M_not_wellFounded⟩

/-- **`Statement:` a NON-VACUOUS μ witness.** At the leaf-carrying functor
`natPF_NatListRegime = ⟨Bool, fun b => cond b PUnit PEmpty⟩` (the polynomial functor `1 + X`), the
W-type is **inhabited** — the `b = false` head is a leaf, so `W.mk ⟨false, PEmpty.elim⟩` is a tree —
**and** it passes AMM's test. So here well-foundedness is not the empty-carrier artifact it is at
`idPF_Coalgebra`: the test is passed by a carrier that actually has elements, and the proof is the
structural induction of `wtype_wellFounded`.

**Open, and deliberately not attempted:** the matching non-vacuous ν half. At this functor `∅` is
*not* a fixed point of `nextTime` (the leaf node has no children, so it lies in `nextTime … ∅`
vacuously), so the `idPF_Coalgebra` argument does not transfer. The natural witness is the
"eventually reaches a leaf" subset, which excludes `natInfinity`
(`ZeroParadox/Computability/NatListRegime.lean`) — establishing it is a fixed point needs
M-bisimulation, and that file's `EventuallyLeaf` is stated over `QPF.Cofix`, a different carrier. -/
theorem natPF_wtype_wellFounded_and_inhabited :
    IsWellFoundedCoalg (P := natPF_NatListRegime) W.dest ∧
      Nonempty (W natPF_NatListRegime) :=
  ⟨wtype_wellFounded, ⟨W.mk ⟨false, fun e => e.elim⟩⟩⟩

/-! ### § V. AMM Thm 7.6's hypotheses, VERIFIED for this setting

**What this section is for.** Thm 7.6 holds in *"a complete and well-powered category with smooth
monomorphisms"* for *"F preserving monomorphisms."* Earlier versions of this file recorded that count
wrong **four times, in both directions** — see the ⚠ block in the overview for the measured sequence
and the commits. Most were unverified **negatives** (`CLAUDE.md` § *"NOT IN THE LIBRARY" IS A CLAIM*);
one was an unverified positive. **All four are now discharged**: complete and well-powered are Mathlib instances, and the
three theorems below supply `F`-preservation plus smoothness clauses (b) and (c) — clause (a) being
`Types.hasColimitsOfShape`, and AMM's trailing *"every morphism from 0 is monic"* immediate in `Type u`.

⚠ **Verifying the hypotheses is NOT proving the theorem.** AMM Thm 7.6 is **not formalized here** and
Mathlib has no well-founded-coalgebra machinery. What § V establishes is that this setting **satisfies
the theorem's assumptions**, so its conclusion applies *by citation* — never as a Lean derivation.

⚠ **And satisfying the hypotheses is not, by itself, the whole instance-of claim either.** Thm 7.6 is
about **fixed points** and **initial algebras**; connecting to that *subject* is a separate axis, closed
by `wtypeFixedPoint` / `mtypeFixedPoint` below and by `isWellFoundedCoalgCat_iff` in
`ZeroParadox/Category/NextTimeCategorical.lean`. **Both axes closed is what earns the citation.** ⚠ Note
also that AMM's **Def 2.14 itself is not formalized** — its three clauses are proved as separate
statements, and no declaration here asserts "`Type u` has smooth monomorphisms" as one proposition. -/

open CategoryTheory CategoryTheory.Limits MorphismProperty

/-- **Hypothesis 4 — `F` preserves monomorphisms.** For a polynomial functor, the action on maps is
post-composition on the child-indexed family, and post-composing with an injection is injective.
`Reading:` none — this is a plain structural fact.

⚠ **No such instance is registered in the pin** (`PreservesMonomorphisms (ofTypeFunctor P.Obj)` does not
synthesize), which is a true statement about the *instance database* and was twice mistaken here for a
statement about the *fact*. The fact is a dozen lines. -/
instance preservesMonomorphisms_ofTypeFunctor {P : PFunctor.{u, u}} :
    (ofTypeFunctor P.Obj).PreservesMonomorphisms := by
  constructor
  intro X Y f hf
  rw [CategoryTheory.mono_iff_injective] at hf ⊢
  rintro ⟨a, g⟩ ⟨a', g'⟩ h
  simp only [ofTypeFunctor_map] at h
  have h' : (⟨a, (f : X → Y) ∘ g⟩ : P.Obj Y) = ⟨a', (f : X → Y) ∘ g'⟩ := h
  simp only [Sigma.mk.injEq] at h'
  obtain ⟨rfl, h2⟩ := h'
  simp only [heq_eq_eq] at h2
  have hg : g = g' := by
    funext b
    exact hf (congrFun h2 b)
  subst hg
  rfl

/-- **BRIDGE 2 — `W.dest` is a FIXED POINT in AMM's sense.** AMM's *fixed point* (Thm 7.6, p. 30:
*"(co)algebras whose structure is invertible"*) means the structure map is **invertible**, not merely
that some map exists. Mathlib supplies both round trips (`W.mk_dest`, `W.dest_mk`), so the destructor is
an equivalence. Stated because the overview's appeal to Thm 7.6 rests on it and previously cited
nothing.

**PRIOR ART, in this corpus:** `fix_isFixedPoint` (`ZeroParadox/Category/CoalgebraForkPlace.lean`) is
**the same fact one layer up** — `⟨Fix.mk_dest, Fix.dest_mk⟩`, the identical proof shape over the QPF
carrier. It does not discharge this one, because `QPF.Fix` is the *quotient* of `PFunctor.W` and this
file's theorems are stated over `W.dest`; but it is the sibling and should be read alongside. (Found by
a Step-0 grep that should have run **before** this definition was written, not after — the unstated-adjacency
defect, committed in a file about adjacency.) -/
def wtypeFixedPoint {P : PFunctor.{u, u}} : W P ≃ P.Obj (W P) where
  toFun := W.dest
  invFun := W.mk
  left_inv := W.mk_dest
  right_inv := W.dest_mk

/-- **BRIDGE 2, ν side — `M.dest` is a fixed point in the same sense.** Same two round trips
(`M.mk_dest`, `M.dest_mk`). With `wtypeFixedPoint` this puts both carriers under Thm 7.6's *subject*.
**Bridge 1, the predicate transport, is also CLOSED** (2026-08-05,
`ZeroParadox/Category/NextTimeCategorical.lean`). With smoothness clause (b) closed below, **both axes
are now shut** — see the ⚠ blocks in the module overview and § V for what that does and does not
license. -/
noncomputable def mtypeFixedPoint {P : PFunctor.{u, u}} : M P ≃ P.Obj (M P) where
  toFun := M.dest
  invFun := M.mk
  left_inv := M.mk_dest
  right_inv := M.dest_mk

/-- **Smooth monomorphisms, clause (b)** — AMM Def 2.14(1)'s second clause: the colimit cocone of a
chain of monomorphisms *"is formed by monomorphisms"*, i.e. its **legs** are monic.

The proof is `Types.FilteredColimit.isColimit_eq_iff'`: two elements of the same stage collide in the
colimit exactly when some transition map identifies them, and injective transitions push that back.

**PRIOR ART, and it must be cited rather than worked around.** `IsColimit.mono_ι_app_of_isFiltered`
(`Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Colim.lean`) **is this statement**, over an
arbitrary ambient category rather than `Type u`. ⚠ **It is not uniformly more general**: it requires
`[IsFiltered J]` on the *index*, where the version below needs only `IsFilteredOrEmpty`, so it does not
reach the λ = 0 case noted below. And it does **not fire here** — it needs
`colim.PreservesMonomorphisms`, which does not synthesize for `Type u`. Hence the hand proof is kept
and the library name cited, exactly the `CovBy` precedent recorded in `CLAUDE.md`.

⚠ **This clause was mis-cited twice before it was proved.** An earlier version pointed at
`Types.instIsStableUnderFilteredColimitsMonomorphismsType`, which states a **different** proposition —
the induced map between two colimit *vertices* is monic, not that the legs are. A second attempt named
`IsStableUnderTransfiniteComposition` plus cofinality of the tail; that route is real but longer than
this one. **The legs and the vertex map are not the same statement**; keep them apart.

**Hypothesis note:** `IsFilteredOrEmpty` rather than `IsFiltered`, deliberately. AMM's λ-chains
*"include the initial object 0 (the case λ = 0)"* (§ 2.5), and the empty category is **not** filtered —
so the stronger hypothesis would leave their λ = 0 case uncovered. `isColimit_eq_iff'` needs only the
weaker one. -/
theorem mono_colimit_ι_of_mono {J : Type u} [SmallCategory J] [IsFilteredOrEmpty J]
    (F : J ⥤ Type u) (hF : ∀ {i j : J} (f : i ⟶ j), Mono (F.map f))
    {t : Cocone F} (ht : IsColimit t) (i : J) : Mono (t.ι.app i) := by
  rw [mono_iff_injective]
  intro x y h
  obtain ⟨j, f, hf⟩ := Types.FilteredColimit.isColimit_eq_iff' ht x y |>.mp h
  exact (mono_iff_injective (F.map f)).mp (hF f) hf

/-- **Smooth monomorphisms, clause (c)** — AMM Def 2.14(1)'s third clause: *"for every cone of C formed
by monomorphisms, the factorizing morphism from `colim C` is monic."*

**This is not absent from the pin; it is assembled from it.** `IsStableUnderColimitsOfShape.condition`
already has exactly this shape, and the missing step is to take the second diagram to be the
**constant** functor at `D` — whose colimit is `D` itself precisely because the index is connected
(`isColimitConstCocone`). Clause (a) is the Mathlib instance `Types.hasColimitsOfShape`. AMM's trailing
*"every morphism from 0 is monic"* is immediate in `Type u` — every map out of the empty type is
injective.

⚠ **Clause (b) is `mono_colimit_ι_of_mono` above — and must NOT be cited to
`Types.instIsStableUnderFilteredColimitsMonomorphismsType`**, which concludes the induced map *between
two colimit vertices* is monic, whereas clause (b) is about the cocone **legs**
`c.ι.app j : X.obj j ⟶ c.pt`. Those are different propositions; keep them apart.

**A definition can be available without any declaration bearing its name.** Grepping `smooth` in
`Mathlib/CategoryTheory/` returns nothing; the condition is nonetheless satisfied. -/
theorem smooth_monos_factorizing {J : Type u} [SmallCategory J] [IsFiltered J] [IsConnected J]
    (X : J ⥤ Type u) (c : Cocone X) (hc : IsColimit c) (D : Type u)
    (f : X ⟶ (Functor.const J).obj D) (hf : ∀ j, Mono (f.app j))
    (φ : c.pt ⟶ D) (hφ : ∀ j, c.ι.app j ≫ φ = f.app j) :
    Mono φ := by
  have hstable : (monomorphisms (Type u)).IsStableUnderColimitsOfShape J := inferInstance
  have hfun : (monomorphisms (Type u)).functorCategory J f := fun j => hf j
  have := hstable.condition X ((Functor.const J).obj D) c (constCocone J D) hc
    (isColimitConstCocone J D) f hfun φ ?_
  · exact this
  · intro j
    simpa [constCocone] using hφ j

end ZeroParadox

/-! ## Axiom Purity Check

**Measured 2026-08-04, not inferred.** `#print axioms` follows the STATEMENT, so read the split by
what each statement mentions:

```
nextTime                            no axioms          -- the operator itself
IsWellFoundedCoalg                  no axioms          -- set EQUALITY only, no order structure
idPF_M_nonempty                     no axioms          -- corecursion INTO M is free
wtype_wellFounded                   [propext, Quot.sound]                    <- the μ side, CHOICE-FREE
natPF_wtype_wellFounded_and_inhabited  [propext, Quot.sound]                 <- the non-vacuous μ witness
nextTime_mono / wfPart / _iff_      [propext, Classical.choice, Quot.sound]
idPF_M_nextTime_empty               [propext, Classical.choice, Quot.sound]
idPF_M_not_wellFounded              [propext, Classical.choice, Quot.sound]
fork_is_intrinsic                   [propext, Classical.choice, Quot.sound]
preservesMonomorphisms_ofTypeFunctor   [propext, Quot.sound]                 <- hypothesis 4, CHOICE-FREE
mono_colimit_ι_of_mono              [propext, Classical.choice, Quot.sound]  -- via the colimit API
smooth_monos_factorizing            [propext, Classical.choice, Quot.sound]  -- via the colimit API
wtypeFixedPoint                     no axioms                                <- bridge 2, μ side: FREE
mtypeFixedPoint                     [propext, Classical.choice, Quot.sound]  -- via M.dest, the origin
```
**The μ/ν purity split holds at the bridge too:** `W`'s fixed-point property costs nothing, `M`'s costs
choice — the same shape as `fix_isEmpty` vs `cofix_nonempty`, and for the same reason (destructing `M`).

**Two origins, measured separately.** (Where each footprint *enters* is measured below. ⚠ No claim is
made that either is avoidable — origin 1 enters precisely *because* this file states `Monotone` on
`Set X`, which is this file's own choice of formulation.)

1. **The `Set` lattice instance** (the instance hazard `CLAUDE.md` documents). Measured:
   `Set.instBooleanAlgebra` is `[propext, Classical.choice, Quot.sound]`, inheriting from
   `Prop.instBooleanAlgebra` (same footprint) whose sibling `Prop.instHeytingAlgebra` is `[propext]`.
   **Knaster-Tarski itself is choice-free** — `OrderHom.lfp`, `OrderHom.map_lfp` and `OrderHom.lfp_le`
   all measure `[propext, Quot.sound]`. So the fixed-point machinery costs nothing; mentioning
   `Monotone` on `Set X` is what costs.
2. **`M.dest`**, the documented origin on the M side (`CLAUDE.md`'s measured table).

**Why `wtype_wellFounded` escapes both:** `IsWellFoundedCoalg` is stated with set *equality*
(`nextTime α S = S → S = Set.univ`) and mentions no order instance, and the W side never destructs an
M-type. So the μ-side result is choice-free while its ν-side counterpart is not — matching
`ZeroParadox/Settheory/Coalgebra.lean`, where `fix_isEmpty` is `[propext, Quot.sound]` and `cofix_nonempty`
carries choice.

⚠ **NOT CLAIMED: that any of this is removable.** That is a modal claim, and per `CLAUDE.md` it needs
an *exhibited* clean proof (accidental) or a *reduction* to a taboo (essential); a footprint
measurement can establish neither. What is claimed is only what was measured above.

**One measured aside worth recording:** `idPF_M_nonempty` is **axiom-free**, where the corpus's
`cofix_nonempty` (`ZeroParadox/Settheory/Coalgebra.lean`) carries choice for the same functor. The difference
is the carrier, not the argument — `PFunctor.M` with `M.corec` versus `QPF.Cofix` and its quotient
layer. This is the "build without destructing" pattern already recorded for `strict_cofix_nonempty`. -/

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
#print axioms natPF_wtype_wellFounded_and_inhabited
#print axioms preservesMonomorphisms_ofTypeFunctor
#print axioms mono_colimit_ι_of_mono
#print axioms smooth_monos_factorizing
#print axioms wtypeFixedPoint
#print axioms mtypeFixedPoint

end PurityCheck
