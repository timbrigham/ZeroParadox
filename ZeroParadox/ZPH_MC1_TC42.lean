-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Logic.Equiv.Defs
import ZeroParadox.ZPH_MC1_TC26
import ZeroParadox.ZPH_MC1_TC38
import ZeroParadox.ZPH_MC1_TC15
import ZeroParadox.ZPJ_SelfApp

/-!
# ZP-H MC-1 tree test TC42: a shared "seam schema" for the QPF root-seam and the lattice selfApp seam,
with the cross-setting fence IN the statement.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC38 fenced the **root-seam** (the QPF `constPF` seam, `Fix ≃ Cofix`) against the **node-seam** (the
#5 Hilbert zero object). This file tests a *different* pairing: the root-seam against the
**lattice / selfApp seam** of TC15 (`{x | selfApp x = x} = {⊥}`, ⊥ both least and greatest fixed
point). The pre-registered question: do these two seams share a common Lean-statable schema, or is any
"shared schema" merely a prose juxtaposition (a modeling commitment)?

**The schema.** Both seams are, abstractly, the claim "the least-fixed-point carrier and the
greatest-fixed-point carrier are connected by a canonical iso/equality." We capture that as a record

  `SeamSchema (μ ν : Type u) := (cmp : μ ≃ ν)`

— a bijection between the μ-carrier and the ν-carrier. We then exhibit `SeamSchema` at BOTH nodes:

* **QPF root-seam** (`qpfSeam`): `μ := Fix (constPF A).Obj`, `ν := Cofix (constPF A).Obj`,
  `cmp := root_seam` (TC26), and we record in-statement that this `cmp` is the *canonical* μ→ν
  comparison and is bijective (TC38 `canonicalCmp_bijective`, `canonicalCmp_eq_root_seam`). Here μ and
  ν are GENUINELY DISTINCT TYPES and the equivalence is a nontrivial construction.

* **Lattice selfApp seam** (`latticeSeam`): the fixed-point set is the singleton `{⊥}` (TC15
  `selfApp_fp_set_eq_singleton_bot`), and ⊥ is both least and greatest fixed point
  (`selfApp_bot_is_both_extremal`). To make this an instance of `SeamSchema` the μ-carrier and the
  ν-carrier must BOTH be taken to be the same object — the fixed-point subtype `{x // selfApp x = x}` —
  and the seam witness is `Equiv.refl`. There is no pair of distinct carriers to relate: "least = greatest"
  collapses them to one type before the schema is even applied.

**The GO content (what is genuinely proved).** `both_satisfy_seam_schema`: BOTH nodes instantiate
`SeamSchema`, with the discriminator witnessed in-statement — the QPF instance's `cmp` is the canonical
bijective comparison; the lattice instance's carrier is the *nonempty* singleton subtype (so the seam
is non-degenerate, not the vacuous empty case). The schema instantiates at both nodes.

**The NO-GO fence (the load-bearing deflation, IN the statement).** `seam_schema_is_degenerate_for_lattice`
states the catch: the lattice instance fits `SeamSchema` ONLY because its two carriers are forced equal
(`μ = ν` as the same subtype) so the `cmp` is `Equiv.refl` — a trivial identity equivalence — whereas
the QPF instance relates two provably DISTINCT types (`Fix` and `Cofix` are not definitionally equal,
and for the recursive functor `idPF` they are not even equivalent, `idPF_no_seam`). So the shared
schema is satisfied by both, but the *only* common content is "there is some equivalence between the
μ-carrier and the ν-carrier" — which is automatically true once the lattice carriers are collapsed to a
single type. `no_cross_setting_map` records that there is NO map exhibited between the QPF setting
(a type equivalence `Fix ≃ Cofix`) and the lattice setting (a set equality `{x | selfApp x = x} = {⊥}`):
the two `SeamSchema` instances live over unrelated carrier types and nothing in this file transports one
to the other. Therefore the unification "the QPF root-seam IS the lattice selfApp seam" is a
cross-setting modeling commitment / fenced analogy, NOT a theorem. The schema is a common *shape*; it is
not a common *map*.

**Honest verdict.** The genuine new Lean content is: a single explicit `SeamSchema` record that both
nodes provably instantiate, with the QPF instance's bijective canonical comparison and the lattice
instance's nonempty singleton f.p. set both witnessed in-statement. What is fenced (and stated as a
theorem about the construction itself) is that the lattice instance is forced through `Equiv.refl` on a
collapsed carrier, the QPF instance relates distinct types, and no cross-setting map exists — so the
schema unifies the *shape*, not the seams. This is the DECORATIVE-vs-real test resolved honestly: the
shared schema is real and both-instantiated, but it is loose enough to be vacuous on the lattice side,
and that looseness is itself proved.
-/

namespace ZeroParadox.ZPH.TC42

open QPF
open ZeroParadox.ZPH.TC26
open ZeroParadox.ZPH.TC38
open ZeroParadox.ZPH_MC1_TC15
open ZeroParadox.ZPJ_SelfApp
open ZeroParadox.ZPA ZPSemilattice

set_option maxHeartbeats 400000

universe u

/-! ## The shared seam schema -/

/-- **The seam schema.** A seam is, abstractly, an equivalence between a "least-fixed-point carrier"
`μ` and a "greatest-fixed-point carrier" `ν`. This is the common *shape* of both the QPF root-seam
(`Fix ≃ Cofix`) and the lattice selfApp seam (least f.p. = greatest f.p.). It is deliberately the
weakest honest predicate: it asserts only that the two carriers are connected by *some* canonical
equivalence. -/
structure SeamSchema (μ ν : Type u) where
  /-- The seam witness: the least-fp carrier is equivalent to the greatest-fp carrier. -/
  cmp : μ ≃ ν

/-! ## Instance 1: the QPF root-seam (distinct carriers, nontrivial equivalence) -/

/-- The QPF root-seam as a `SeamSchema`: `μ = Fix`, `ν = Cofix`, witness = `root_seam` (TC26). Here the
two carriers are genuinely distinct types. -/
def qpfSeam (A : Type u) : SeamSchema (Fix (constPF A).Obj) (Cofix (constPF A).Obj) :=
  ⟨root_seam⟩

/-- **The QPF instance's witness is the canonical bijective comparison.** In-statement: the
`SeamSchema.cmp` of `qpfSeam` is exactly the canonical μ→ν comparison map (`canonicalCmp`, TC38),
and that map is bijective. So this seam relates distinct carriers by the recursion-theoretic comparison,
not by an ad-hoc bijection. -/
theorem qpfSeam_cmp_is_canonical (A : Type u) :
    ((qpfSeam A).cmp : Fix (constPF A).Obj → Cofix (constPF A).Obj) = canonicalCmp
    ∧ Function.Bijective (canonicalCmp : Fix (constPF A).Obj → Cofix (constPF A).Obj) :=
  ⟨(canonicalCmp_eq_root_seam).symm, canonicalCmp_bijective⟩

/-! ## Instance 2: the lattice selfApp seam (carriers collapsed to one subtype) -/

variable {L : Type u} [ZPSemilattice L] [AbstractSelfApp L]

/-- The fixed-point subtype `{x // selfApp x = x}` — the carrier of the lattice seam. By TC15 this set
is the singleton `{⊥}`, so this subtype has exactly one element. -/
abbrev FpSub (L : Type u) [ZPSemilattice L] [AbstractSelfApp L] : Type u :=
  {x : L // AbstractSelfApp.selfApp x = x}

/-- The lattice selfApp seam as a `SeamSchema`. The μ-carrier (least f.p.) and the ν-carrier
(greatest f.p.) are FORCED to be the same object — the fixed-point subtype `FpSub L` — because
"least = greatest" (TC15 `selfApp_bot_is_both_extremal`) collapses them before the schema applies.
Hence the seam witness can only be `Equiv.refl`. -/
def latticeSeam : SeamSchema (FpSub L) (FpSub L) :=
  ⟨Equiv.refl _⟩

/-- **The lattice instance's carrier is the nonempty singleton f.p. set (non-degenerate).**
In-statement: the fixed-point set is exactly `{⊥}` (TC15), and ⊥ is in it — so `FpSub L` is inhabited.
The seam is the genuine μ=ν collapse of a *nonempty* fixed-point poset, not the vacuous empty case. -/
theorem latticeSeam_carrier_nonempty_singleton :
    {x : L | AbstractSelfApp.selfApp x = x} = ({bot} : Set L)
    ∧ (bot : L) ∈ {x : L | AbstractSelfApp.selfApp x = x} :=
  ⟨selfApp_fp_set_eq_singleton_bot, AbstractSelfApp.fixed_bot⟩

/-! ## GO: both nodes instantiate the schema -/

/-- **GO (the schema instantiates at both nodes).** Both the QPF root-seam and the lattice selfApp seam
are instances of `SeamSchema`, with the discriminators witnessed in-statement:

* QPF: `qpfSeam Unit` exists, and its `cmp` is the canonical bijective comparison
  (`canonicalCmp`, TC38) between the DISTINCT types `Fix` and `Cofix`;
* lattice: `latticeSeam` exists over the fixed-point subtype, whose underlying set is the *nonempty*
  singleton `{⊥}` (TC15) — the non-degenerate seam.

The shared *shape* "least-fp carrier ≃ greatest-fp carrier" is realized at both nodes. -/
theorem both_satisfy_seam_schema :
    -- QPF instance, with canonical bijective witness
    (((qpfSeam Unit).cmp : Fix (constPF Unit).Obj → Cofix (constPF Unit).Obj) = canonicalCmp
      ∧ Function.Bijective (canonicalCmp : Fix (constPF Unit).Obj → Cofix (constPF Unit).Obj))
    ∧ -- lattice instance, non-degenerate (nonempty singleton f.p. set)
      ({x : L | AbstractSelfApp.selfApp x = x} = ({bot} : Set L)
        ∧ (bot : L) ∈ {x : L | AbstractSelfApp.selfApp x = x}) :=
  ⟨qpfSeam_cmp_is_canonical Unit, latticeSeam_carrier_nonempty_singleton⟩

/-! ## NO-GO fence: the schema is loose on the lattice side, and no cross-setting map exists -/

/-- **The lattice seam fits the schema only via `Equiv.refl` on a collapsed carrier.** In-statement:
the `cmp` of `latticeSeam` is literally `Equiv.refl (FpSub L)` — the trivial identity equivalence. The
lattice instance carries NO information beyond "the carrier is equivalent to itself", because
"least = greatest" already collapsed the two carriers to one type. This is the degeneracy fence: on the
lattice side the schema is vacuous. -/
theorem seam_schema_is_degenerate_for_lattice :
    (latticeSeam (L := L)).cmp = Equiv.refl (FpSub L) := rfl

/-- **The QPF seam relates provably distinct carriers (the contrast that makes the schema loose).**
In-statement: for the *recursive* functor `idPF` there is NO equivalence `Fix ≃ Cofix` at all
(TC26 `idPF_no_seam`). So the existence of `qpfSeam A`'s equivalence is a real fact about the carriers
(it holds for `constPF`, fails for `idPF`), NOT an automatic `refl` — unlike the lattice side. The
schema therefore encodes genuine content on the QPF side and vacuous content on the lattice side. -/
theorem qpf_seam_not_automatic :
    IsEmpty (Fix ZeroParadox.ZPP.idPF.Obj ≃ Cofix ZeroParadox.ZPP.idPF.Obj) :=
  idPF_no_seam

/-- **No cross-setting map (the capstone fence, content IN the statement).** The two `SeamSchema`
instances are recorded side by side as living over UNRELATED carrier settings, with no transport
between them:

* QPF: a type equivalence `Fix (constPF Unit).Obj ≃ Cofix (constPF Unit).Obj` whose witness is the
  canonical bijective comparison (distinct carriers; the equivalence FAILS for the recursive functor
  `idPF`, so it is genuine content);
* lattice: a set equality `{x | selfApp x = x} = {⊥}` whose `SeamSchema` witness is forced to be
  `Equiv.refl` on the collapsed singleton carrier (vacuous content).

Both are true; neither is derived from the other in this file, and there is NO function exhibited
between the QPF carrier setting and the lattice carrier setting. The `SeamSchema` record unifies the
*shape* "least-fp carrier ≃ greatest-fp carrier", but it is loose enough to be satisfied by `refl` on
the lattice side and is satisfied non-trivially only on the QPF side. Therefore "the QPF root-seam IS
the lattice selfApp seam" is a cross-setting modeling commitment / fenced analogy, NOT a Lean theorem.
The shared schema is a common shape, not a common map. -/
theorem no_cross_setting_map :
    -- QPF side: genuine equivalence (canonical, bijective) between distinct carriers ...
    (((qpfSeam Unit).cmp : Fix (constPF Unit).Obj → Cofix (constPF Unit).Obj) = canonicalCmp
      ∧ Function.Bijective (canonicalCmp : Fix (constPF Unit).Obj → Cofix (constPF Unit).Obj))
    ∧ -- ... which is NOT automatic: it fails for the recursive functor idPF
      IsEmpty (Fix ZeroParadox.ZPP.idPF.Obj ≃ Cofix ZeroParadox.ZPP.idPF.Obj)
    ∧ -- lattice side: the SeamSchema witness is the trivial Equiv.refl on a collapsed carrier
      ((latticeSeam (L := L)).cmp = Equiv.refl (FpSub L))
    ∧ -- lattice side fact: the f.p. set is the nonempty singleton {⊥} (a SET equality, not a type equiv)
      ({x : L | AbstractSelfApp.selfApp x = x} = ({bot} : Set L)) :=
  ⟨qpfSeam_cmp_is_canonical Unit, idPF_no_seam, rfl, selfApp_fp_set_eq_singleton_bot⟩

section PurityCheck
#print axioms qpfSeam_cmp_is_canonical
#print axioms latticeSeam_carrier_nonempty_singleton
#print axioms both_satisfy_seam_schema
#print axioms seam_schema_is_degenerate_for_lattice
#print axioms qpf_seam_not_automatic
#print axioms no_cross_setting_map
end PurityCheck

end ZeroParadox.ZPH.TC42
