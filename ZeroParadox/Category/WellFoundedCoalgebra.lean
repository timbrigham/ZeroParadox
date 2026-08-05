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

⚠ **NO instance-of claim is made. TWO things are open, and only one of them is a hypothesis.** Three
review rounds were spent counting which of Thm 7.6's four *ambient* hypotheses `Type u` satisfies (one,
then two, then three) — as though that count were the whole story. It is not: **no count of ambient
hypotheses alone can earn the claim**, because Thm 7.6 is a statement about **fixed points** and
**initial algebras**, and connecting this file's results to its *subject* is a separate matter. The two
open items:
* **smoothness clause (b)** — an ambient hypothesis, true of `Type u`, unwitnessed here (see the table
  and § V);
* **bridge 1 below** — the predicate transport, which is not a hypothesis of the theorem at all.

The bridges to its subject:

1. **The predicate is not transported. STILL OPEN.** `IsWellFoundedCoalg` is stated over `Set X` with
   `nextTime`; AMM Def 4.3 is stated over `Sub(A)` in a **category**. The key ingredient exists in the
   pin — `Types.subobjectEquivSet (α : Type u) : Subobject α ≃o Set α`
   (`Mathlib/CategoryTheory/Subobject/Types.lean`) — so this is **bounded work, not research**: define
   `⃝` over `Subobject X`, and show it matches `nextTime` across that order isomorphism. The step
   carrying the real content is how `ofTypeFunctor P.Obj` acts on subobjects.
2. **"Fixed point" in AMM's sense — CLOSED.** AMM mean the structure map is **invertible**. Now
   witnessed: `wtypeFixedPoint` and `mtypeFixedPoint` in § V.

**Until bridge 1 is written, no count of ambient hypotheses can earn an instance-of claim** — which is
why the counting kept recurring and why it is no longer the headline. The ambient hypotheses are
recorded below anyway: measuring them was worth doing, the results are reusable, and they are simply
**not the blocker**. Thm 7.6 holds in *"a complete and well-powered category with smooth
monomorphisms"* for *"F preserving monomorphisms."* The setting here is **`Type u`**, Lean's category of
types — the type-theoretic analogue of **Set** (AMM's Ex 2.15(1) grants Set universally smooth
monomorphisms), and not literally Set, which is why each was checked rather than inherited:

| hypothesis | status | where |
|---|---|---|
| complete | **HOLDS** | `Limits.Types.hasLimitsOfSize` |
| well-powered | **HOLDS** | `instWellPoweredType`, `Mathlib/CategoryTheory/Subobject/Types.lean` |
| smooth monomorphisms | **(a) and (c) witnessed here; (b) true of `Type u` but NOT witnessed here — see ⚠ below** | (a) `Types.hasColimitsOfShape`; (c) `smooth_monos_factorizing` in § V |
| `F` preserves monomorphisms | **HOLDS** | `preservesMonomorphisms_ofTypeFunctor` in § V |

⚠ **CLAUSE (b) IS THE HOLE, and it is recorded rather than papered over.** Def 2.14(1)'s clause (b) is
*"its colimit cocone is formed by monomorphisms"* — a statement about the legs `c.ι.app j`. An earlier
version of this table cited `Types.instIsStableUnderFilteredColimitsMonomorphismsType` for it; **that
instance states a different proposition** (given a natural transformation with monic components between
two diagrams, the induced map *between the two colimit vertices* is monic). Def 2.14(1) quantifies over
**λ-chains of monomorphisms**, and clause (b)'s subject is the cocone **legs** — a different
proposition, so the obvious instantiation (second diagram constant at `X.obj j`) does not deliver it:
such a natural transformation is a cone over `X` with that vertex, and need not exist. Clause (b) *is*
true of `Type u` — the route is `IsStableUnderTransfiniteComposition` (which **does** synthesize in the
pin) plus
cofinality of the tail `[j, λ)` — but **neither step is in this file, so the row is not fully
witnessed.** Next-touch work; do not restore the old citation.

⚠ **Verified hypotheses are not a formalized theorem, and what the citation buys is narrow.** AMM
Thm 7.6 is **not** proved in Lean here, and Mathlib has no well-founded-coalgebra machinery to prove it
with. What Thm 7.6 would deliver, given its hypotheses, is that a well-founded fixed point **is the
initial algebra** — i.e. it *concludes* initiality rather than assuming it, which is why the
`fork_is_intrinsic` fence above ("not proved: that either carrier is initial/final") is consistent with
citing it. That conclusion is available **by citation only**, and only once clause (b) is closed. Do
not upgrade this to "we proved Thm 7.6," and do not read the fence as denying what Thm 7.6 offers.

⚠ **THIS TABLE WAS WRONG TWICE, IN THE SAME DIRECTION, AND THAT IS THE LESSON.** It first recorded
*one* of four, then *two*; the true count is four. **Not one of those errors was a wrong theorem — each
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
monomorphisms"* for *"F preserving monomorphisms."* Earlier versions of this file recorded first one,
then two, of those four as available and withheld any instance-of claim. **Both counts were wrong, and
each was an unverified negative rather than a wrong theorem** — see `CLAUDE.md` § *"NOT IN THE LIBRARY"
IS A CLAIM*. **Three of the four are now discharged**: two are Mathlib instances, and the two theorems
below supply `F`-preservation and clause (c) of smoothness. **Clause (b) of smoothness is still open
here** — true of `Type u`, but witnessed by nothing in this file (see the ⚠ in the overview).

⚠ **Verifying the hypotheses is NOT proving the theorem.** AMM Thm 7.6 is **not formalized here** and
Mathlib has no well-founded-coalgebra machinery. What § V establishes is that this setting **satisfies
the theorem's assumptions**, so its conclusion applies *by citation*. That is the honest upgrade from
"shares the shape" — but it is **not yet a completed instance-of** while clause (b) is unwitnessed, and
it would never be a Lean derivation of Thm 7.6 in any case. -/

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
**The remaining gap is bridge 1**, the predicate transport — see the ⚠ in the module overview. -/
noncomputable def mtypeFixedPoint {P : PFunctor.{u, u}} : M P ≃ P.Obj (M P) where
  toFun := M.dest
  invFun := M.mk
  left_inv := M.mk_dest
  right_inv := M.dest_mk

/-- **Smooth monomorphisms, clause (c)** — AMM Def 2.14(1)'s third clause: *"for every cone of C formed
by monomorphisms, the factorizing morphism from `colim C` is monic."*

**This is not absent from the pin; it is assembled from it.** `IsStableUnderColimitsOfShape.condition`
already has exactly this shape, and the missing step is to take the second diagram to be the
**constant** functor at `D` — whose colimit is `D` itself precisely because the index is connected
(`isColimitConstCocone`). Clause (a) is the Mathlib instance `Types.hasColimitsOfShape`. AMM's trailing
*"every morphism from 0 is monic"* is immediate in `Type u` — every map out of the empty type is
injective.

⚠ **Clause (b) is NOT discharged here, and must not be cited to
`Types.instIsStableUnderFilteredColimitsMonomorphismsType`** — that instance concludes the induced map
*between two colimit vertices* is monic, whereas clause (b) is about the cocone **legs**
`c.ι.app j : X.obj j ⟶ c.pt`. The two are different propositions. Clause (b) is true of `Type u`; the
route is `IsStableUnderTransfiniteComposition` (which does synthesize in the pin) plus cofinality of
the tail, and neither step is written here. See the ⚠ in the module overview.

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
#print axioms smooth_monos_factorizing
#print axioms wtypeFixedPoint
#print axioms mtypeFixedPoint

end PurityCheck
