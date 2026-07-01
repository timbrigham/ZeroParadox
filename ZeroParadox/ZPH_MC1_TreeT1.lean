-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1_Linearize
import ZeroParadox.ZPH_InfoFunctor
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, edge T1 — the within-μ edge: proof-theory floor ↔ categorical-initial bottoms

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file tests **T1**, the within-μ internal edge of the bottom-diagram tree
(`thread_obstruction_table_2026-06-29.md` §7): are the proof-theory bottom (#1, the floor of a
well-founded order) and the categorical-initial bottoms (#4 Kleisli `Fin 0`, #5 Hilbert
`StateSpace 0`) **reconcilable** — i.e. connected by structure-preserving comparisons — as the tree
predicts for siblings under the μ root?

**Pre-registered no-go (the obstruction this edge would hit if the tree is wrong at level 1):** a
universal-property clash like the cross-root edges — the order floor failing to be an initial object,
or no functor carrying the floor to a categorical bottom while preserving initiality (the analogue of
E4's well-founded-vs-not or SPLIT's limit-vs-initial). If that obstruction were provable, the μ/ν root
cut would be wrong.

**Verdict: GO (the μ-siblings connect by genuine maps).** No obstruction; instead:

- `nat_floor_isInitial` — the well-founded order floor `0` is the **initial object** of the order
  category `ℕ` (the proof-theory descent floor is genuinely μ / initial, not merely "a least element").
- `fC_functor : ℕ ⥤ KleisliCat PMF` and `fD_functor : ℕ ⥤ ModuleCat ℂ` (built earlier) are **real
  functors out of this order**; `fC_floor_transport`/`fD_floor_transport` prove they carry the
  floor's descent morphism `0 ⟶ n` to the categorical bottom's *canonical initiality morphism* — so
  #4 and #5 are the image of #1 *with its universal role preserved*: a witnessed span `#4 ⟵ #1 ⟶ #5`
  (bundled in `t1_mu_cluster_glue`), not merely three objects that independently happen to be initial.
- `linObj_iso_hilbert` — a **direct #4↔#5 edge for the whole tower**: the linearization of the info
  object `Fin n →₀ ℂ` is ℂ-linearly isomorphic to the Hilbert object `StateSpace n`, for *every* `n`
  (not just the bottom). This genuinely extends `ZPH_MC1.lin_carries_bottom`, which only handled the
  bottom via the vacuous "any two initial objects are iso".

**Honest scope.** The #4↔#5 connection is realized object-wise (a per-`n` module iso) and via the
common apex #1; a single *functor* `KleisliCat PMF ⥤ ModuleCat ℂ` is not built here (it is genuinely
obstructed on infinite types — `ZPH_MC1_Linearize` — clean only on the finite snap tower). So T1 is GO
at the level of "connected by real bottom-preserving maps", which is exactly the tree's sibling
prediction; it is not the stronger claim of a single unifying functor.
-/

namespace ZeroParadox.ZPH_MC1_TreeT1

open CategoryTheory
open ZeroParadox.ZPD ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_InfoFunctor ZeroParadox.ZPH_MC1

/-- #1 as a μ/initial object: the floor `0` is the initial object of the well-founded order category
    `ℕ` (the base of the transfinite descent the proof-theory layer uses, Goodstein/KP/Kruskal). -/
noncomputable def nat_floor_isInitial : Limits.IsInitial (0 : ℕ) := by
  haveI : ∀ Y : ℕ, Unique ((0 : ℕ) ⟶ Y) := fun Y =>
    { default := homOfLE (Nat.zero_le Y)
      uniq := fun _ => Subsingleton.elim _ _ }
  exact Limits.IsInitial.ofUnique (0 : ℕ)

/-- The direct #4↔#5 edge, all `n`: the linearization of the info object `Fin n →₀ ℂ` is ℂ-linearly
    isomorphic to the Hilbert object `StateSpace n`. Genuine transform — extends `lin_carries_bottom`
    (bottom only, via initiality) to the whole snap tower via an explicit linear equivalence. -/
noncomputable def linObj_iso_hilbert (n : ℕ) : linObj (Fin n) ≅ fD_functor.obj n :=
  (((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin n)).trans
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm)).toModuleIso

/-- Genuine #1→#4 span witness: `fC_functor` carries the order floor's descent morphism `0 ⟶ n`
    (the well-founded "least element → level n") to the categorical bottom's **canonical initiality
    morphism**. So #4 is not merely an object that happens to be initial — it is the image of the
    floor under a real functor that *respects the floor's universal role*. -/
theorem fC_floor_transport (n : ℕ) :
    fC_functor.map (homOfLE (Nat.zero_le n)) = fC_zero_isInitial.to (fC_functor.obj n) :=
  fC_zero_isInitial.hom_ext _ _

/-- Genuine #1→#5 span witness: `fD_functor` carries the order floor's descent morphism to the
    Hilbert bottom's canonical initiality morphism (same content as `fC_floor_transport`). -/
theorem fD_floor_transport (n : ℕ) :
    fD_functor.map (homOfLE (Nat.zero_le n)) = fD_zero_isInitial.to (fD_functor.obj n) :=
  fD_zero_isInitial.hom_ext _ _

/-- **T1 GO capstone (span witnessed, not narrated).** The μ-cluster reconciles by genuine maps:
    (a) the order floor `0` is initial (#1 is μ); (b) `fC_functor`/`fD_functor` carry the floor's
    descent morphisms to the categorical bottoms' initiality morphisms — the span `#4 ⟵ #1 ⟶ #5`,
    now IN the statement via `fC_floor_transport`/`fD_floor_transport`; (c) the linearization iso
    connects #4 to #5 directly at the bottom. No universal-property clash (contrast the cross-root
    edges E4/SPLIT): the siblings under the μ root are reconcilable, as the tree predicts. -/
theorem t1_mu_cluster_glue :
    Nonempty (Limits.IsInitial (0 : ℕ)) ∧
    (∀ n, fC_functor.map (homOfLE (Nat.zero_le n)) = fC_zero_isInitial.to (fC_functor.obj n)) ∧
    (∀ n, fD_functor.map (homOfLE (Nat.zero_le n)) = fD_zero_isInitial.to (fD_functor.obj n)) ∧
    Nonempty (linObj (Fin 0) ≅ fD_functor.obj 0) :=
  ⟨⟨nat_floor_isInitial⟩, fC_floor_transport, fD_floor_transport, ⟨linObj_iso_hilbert 0⟩⟩

end ZeroParadox.ZPH_MC1_TreeT1

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TreeT1

#print axioms nat_floor_isInitial
#print axioms linObj_iso_hilbert
#print axioms fC_floor_transport
#print axioms fD_floor_transport
#print axioms t1_mu_cluster_glue

end PurityCheck
