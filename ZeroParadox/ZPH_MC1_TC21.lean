-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPP_Coalgebra

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC18 (module TC21) — the ROOT cut is a strict, non-glueable μ/ν obstruction

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This module tests **TC18 — strict-fork canonicity of the root**. The tree hypothesis roots the whole
bottom-diagram at the μ/ν fork. ZP-P (`ZPP_Coalgebra.lean`) places that fork on the leaf-free identity
polynomial functor `idPF`: its initial algebra (W-type, μ) `Fix idPF.Obj` is **empty**
(`fix_isEmpty`) and its final coalgebra (M-type, ν) `Cofix idPF.Obj` is **inhabited**
(`cofix_nonempty`). The pre-registered question: is the root cut a *genuine* obstruction — i.e. is
there no map reconciling the two roots — or is it cosmetic?

**Race outcome: GO for the obstruction (a hard one-direction wall, in-statement).**

The load-bearing content is `root_cut_no_map_nu_to_mu`:

  `IsEmpty (Cofix idPF.Obj → Fix idPF.Obj)`

There is **no function** from the inhabited ν-root to the empty μ-root: a function applied to the
witness element of `Cofix` would produce an element of the empty `Fix`. The obstruction is IN the
theorem statement (the function type is what is shown empty), not narrated in prose. Paired with the
trivially-existing vacuous map the other way (`root_cut_mu_to_nu_unique`: out of the empty `Fix` there
is a unique function, by `Fin.elim0`-style emptiness), this exhibits the root μ/ν cut as a strict,
non-invertible obstruction in the cleanest possible ambient (the identity functor's own two fixed
points). The capstone `root_cut_strict_asymmetric` bundles both directions: ν→μ impossible, μ→ν
unique — a one-way wall.

**SCOPE FENCE (what this proves vs. what is interpretation).** The Lean content is exactly:
empty-vs-inhabited forces the asymmetric function-type emptiness. This is, honestly, the **generic**
empty/inhabited cardinality wall — the same `IsEmpty (Nonempty → Empty)` content that any
empty-vs-inhabited pair exhibits (and the same Axis-III content as the Kleisli `Fin 0` bottom, #4).
What is ZP-P-specific is only the *identification* of the two empty/inhabited objects as the μ and ν
fixed points of one functor (carried by `fix_isEmpty` / `cofix_nonempty`, proved in
`ZPP_Coalgebra.lean`); that those two objects ARE the well-founded vs non-well-founded fixed points is
the structural claim, and it is borrowed, not re-proved here. So:

- **Proved here (in-statement):** the root cut is a strict, non-invertible map obstruction
  (`root_cut_no_map_nu_to_mu`, `root_cut_strict_asymmetric`).
- **Interpretation (NOT a new Lean result):** that this obstruction *certifies a μ/ν root distinct
  from mere cardinality*. The separating invariant exhibited here is cardinality (empty vs inhabited);
  the well-foundedness/polarity content lives upstream in `fix_isEmpty`/`cofix_nonempty`, which this
  module imports rather than re-establishes. The pre-registered NO-GO caveat therefore stands as a
  HONEST scope limit: at the level of *this* module's own theorems, the separating invariant is
  Axis-III cardinality. The root cut is real (the map wall is genuine and strict), but its
  *distinctively-μ/ν* character is inherited from ZP-P, not freshly witnessed here.
-/

namespace ZeroParadox.ZPH_MC1_TC21

open QPF
open ZeroParadox.ZPP

/-- **The root cut, hard direction (in-statement obstruction).** There is no function from the
    inhabited ν-root `Cofix idPF.Obj` to the empty μ-root `Fix idPF.Obj`. A map would send the
    witnessing element of `Cofix` (from `cofix_nonempty`) to an element of the empty `Fix` (from
    `fix_isEmpty`) — impossible. The obstruction is the emptiness of the *function type*. -/
theorem root_cut_no_map_nu_to_mu :
    IsEmpty (Cofix idPF.Obj → Fix idPF.Obj) := by
  refine ⟨fun f => ?_⟩
  obtain ⟨c⟩ := cofix_nonempty
  exact fix_isEmpty.elim (f c)

/-- **The root cut, vacuous direction.** Out of the empty μ-root there is a (unique) function to the
    ν-root: any two such functions agree, since the domain is empty. This is the trivial half of the
    asymmetry — a map exists one way and not the other. -/
theorem root_cut_mu_to_nu_unique
    (f g : Fix idPF.Obj → Cofix idPF.Obj) : f = g := by
  funext x
  exact fix_isEmpty.elim x

/-- **Strict asymmetry of the root cut (capstone, in-statement).** The μ/ν root cut is a one-way wall:
    there is NO function ν→μ (`IsEmpty (Cofix idPF.Obj → Fix idPF.Obj)`), while every two functions
    μ→ν coincide (the μ→ν map is unique, by emptiness of the domain). So the cut is strict and
    non-invertible: it cannot be a relabeling of one object, because a relabeling would give an
    invertible map in both directions. -/
theorem root_cut_strict_asymmetric :
    IsEmpty (Cofix idPF.Obj → Fix idPF.Obj) ∧
      (∀ f g : Fix idPF.Obj → Cofix idPF.Obj, f = g) :=
  ⟨root_cut_no_map_nu_to_mu, root_cut_mu_to_nu_unique⟩

/-- **No equivalence across the root cut.** As an immediate consequence, the two roots are not
    equivalent (no bijection): an equivalence would supply a function `Cofix → Fix`, which is
    impossible. This is the cleanest "not a relabeling" statement — the root cut is not a cosmetic
    renaming of a single object. -/
theorem root_cut_no_equiv :
    IsEmpty (Cofix idPF.Obj ≃ Fix idPF.Obj) := by
  refine ⟨fun e => ?_⟩
  exact root_cut_no_map_nu_to_mu.elim e.toFun

end ZeroParadox.ZPH_MC1_TC21

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC21

-- Footprint (measured): all four carry [propext, Classical.choice, Quot.sound]. Choice is the
-- Mathlib M-type / `Cofix` artifact (fenced in ZPP_Coalgebra) — it enters through the `Cofix idPF.Obj`
-- type that every statement here mentions, not through any necessity of the obstruction. The
-- obstruction's mathematical content (empty domain/codomain → asymmetric function-type emptiness) is
-- itself choice-free; the footprint reflects the ambient M-type machinery, consistent with
-- `cofix_nonempty`'s choice-carrying footprint upstream.
--   root_cut_no_map_nu_to_mu   : [propext, Classical.choice, Quot.sound]  (uses cofix_nonempty)
--   root_cut_mu_to_nu_unique   : [propext, Classical.choice, Quot.sound]  (Cofix in codomain type)
--   root_cut_strict_asymmetric : [propext, Classical.choice, Quot.sound]
--   root_cut_no_equiv          : [propext, Classical.choice, Quot.sound]
#print axioms root_cut_no_map_nu_to_mu
#print axioms root_cut_mu_to_nu_unique
#print axioms root_cut_strict_asymmetric
#print axioms root_cut_no_equiv

end PurityCheck
