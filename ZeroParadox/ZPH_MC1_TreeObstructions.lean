-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_TopFunctor
import ZeroParadox.ZPH_InfoFunctor
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H: The bottom-diagram tree — machine-checked obstruction core (E4 + SPLIT, rebuilt)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file is the **canonical, in-repo rebuild** of the obstruction theorems that the 2026-06-29
identity-falsifier battery proved in scratch files and then deleted. They are the **machine-checked
core of the bottom-diagram tree** (`thread_obstruction_table_2026-06-29.md`): the failure-mode edges
that separate the framework's "bottom" objects into a tree rather than a flat family.

These are obstruction (no-go) results — each proves a *separation*, not a cross-domain identification.
None of them ties two bottoms together; they record precisely how two bottoms fail to be one object,
which is the **precondition** for the local-global reading (distinct local pieces), not its failure.

**E4 cluster — Axis I (well-founded vs not).** Separates the proof-theory bottom (the ordinal floor,
base of a well-order) from the Markov-dynamical bottom (a stationary attractor in the compact
probability simplex):
- `ordinal_carrier_wellFounded` — the ordinals are well-founded under `<`.
- `real_carrier_not_wellFounded` — ℝ is not well-founded under `<`.
- `no_strictMono_real_to_ordinal` — there is no order embedding ℝ ↪ Ordinal (a descent map from the
  attractor carrier to the well-order carrier cannot exist).
- `simplex_antichain` — on the standard simplex, `p ≤ q` (componentwise) forces `p = q`: the simplex
  is an antichain for the coordinate order, so it carries no nontrivial order to descend along.

**SPLIT cluster — Axis II (limit vs initial) and Axis III (cardinality within a polarity).**
- `padic_bottom_not_initial` — the p-adic floor (the one-point space `{0} ⊆ Q₂`, a limit/terminal-
  flavoured object) is **not** an initial object of `TopCat`. (Axis II: limit vs initial.)
- `split_kleisli_vs_hilbert` — the Kleisli bottom `Fin 0` (empty) and the Hilbert bottom
  `StateSpace 0` (a singleton) are not in bijection, even though **both are initial objects** in their
  categories. (Axis III: a finer invariant than polarity — cardinality — distinguishes same-polarity
  bottoms.) `Fin 0` is the carrier of `ZPH_InfoFunctor.fC_functor.obj 0`; `StateSpace 0` of
  `ZPH_HilbFunctor.fD_functor.obj 0`.
- `split_kleisli_vs_padic` — the Kleisli bottom `Fin 0` (empty) is not in bijection with the p-adic
  floor `{0} ⊆ Q₂` (a singleton).

**#5 straddle witness.** `fD_zero_isTerminal` — the Hilbert bottom `fD_functor.obj 0` is **terminal**
in `ModuleCat ℂ` (the initial half is `ZPH_HilbFunctor.fD_zero_isInitial`). Together they say it is a
*zero object* — initial ∧ terminal (μ ∧ ν) — which is why this node straddles the μ/ν root of the
tree. Whether the straddle is the root seam (the diagonal fixed point) or a defect of the tree is the
open question; this file only supplies the missing terminal half so the straddle is fully witnessed.
-/

namespace ZeroParadox.ZPH_MC1_TreeObstructions

open CategoryTheory
open ZeroParadox.ZPD ZeroParadox.ZPB ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_InfoFunctor

/-! ## E4 cluster — Axis I (well-founded vs non-well-founded) -/

/-- The ordinals are well-founded under `<` (the proof-theory bottom's carrier). -/
theorem ordinal_carrier_wellFounded :
    WellFounded ((· < ·) : Ordinal → Ordinal → Prop) := Ordinal.lt_wf

/-- ℝ is not well-founded under `<` (the Markov-attractor bottom's carrier). -/
theorem real_carrier_not_wellFounded :
    ¬ WellFounded ((· < ·) : ℝ → ℝ → Prop) := by
  intro h
  obtain ⟨a, ha, hmin⟩ := h.has_min (Set.range (fun n : ℕ => -(n : ℝ)))
    ⟨_, Set.mem_range_self 0⟩
  obtain ⟨n, rfl⟩ := ha
  refine hmin (-((n : ℝ) + 1)) ⟨n + 1, ?_⟩ ?_
  · push_cast; ring
  · show -((n : ℝ) + 1) < -(n : ℝ); linarith

/-- No strictly monotone map ℝ → Ordinal: the attractor carrier does not order-embed into the
    well-order carrier. The cross-cluster (E4) obstruction in order language. -/
theorem no_strictMono_real_to_ordinal :
    ¬ ∃ f : ℝ → Ordinal, StrictMono f := by
  rintro ⟨f, hf⟩
  -- pull back well-foundedness of `<` on Ordinal along `f`
  have hsub : Subrelation ((· < ·) : ℝ → ℝ → Prop) (InvImage (· < ·) f) :=
    fun {_ _} hxy => hf hxy
  exact real_carrier_not_wellFounded
    (hsub.wf (InvImage.wf f ordinal_carrier_wellFounded))

/-- The standard simplex is an antichain **for the coordinate (componentwise) order** on
    `Fin n → ℝ`: `p ≤ q` forces `p = q`. (Scope: this is the Pi order only — the simplex of course
    carries other nontrivial orders; the claim is that the natural coordinate order, the one a
    descent map would use, collapses to equality on it. Trivially true and degenerate at `n = 0`;
    the content is at `n ≥ 1`.) -/
theorem simplex_antichain {n : ℕ} (p q : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (hq : q ∈ stdSimplex ℝ (Fin n))
    (hpq : p ≤ q) : p = q := by
  have hsum : ∑ i, p i = ∑ i, q i := by rw [hp.2, hq.2]
  funext i
  by_contra hne
  have hlt : p i < q i := lt_of_le_of_ne (hpq i) hne
  have hsl : ∑ j, p j < ∑ j, q j :=
    Finset.sum_lt_sum (fun j _ => hpq j) ⟨i, Finset.mem_univ i, hlt⟩
  exact absurd hsum (ne_of_lt hsl)

/-! ## SPLIT cluster — Axis II (limit vs initial) and Axis III (cardinality) -/

/-- The p-adic floor (one-point space `{0} ⊆ Q₂`) is not an initial object of `TopCat`.
    Axis II: a limit/terminal-flavoured bottom is not the initial bottom. -/
theorem padic_bottom_not_initial :
    IsEmpty (Limits.IsInitial
      (TopCat.of (↥({(0 : Q₂)} : Set Q₂)))) := by
  refine ⟨fun hinit => ?_⟩
  -- an initial object has a (unique) map to the empty space; apply it to the point `0`
  have f := hinit.to (TopCat.of Empty)
  exact (f.hom ⟨0, rfl⟩).elim

/-- Axis III, in-statement: the Kleisli bottom `fC_functor.obj 0` and the Hilbert bottom
    `fD_functor.obj 0` are **both initial objects**, yet their carriers (`Fin 0`, empty;
    `StateSpace 0`, a singleton) are not in bijection. So initiality (polarity) is not a complete
    invariant of a bottom — a finer invariant, cardinality, distinguishes two same-polarity bottoms. -/
theorem split_kleisli_vs_hilbert :
    Nonempty (Limits.IsInitial (fC_functor.obj 0)) ∧
    Nonempty (Limits.IsInitial (fD_functor.obj 0)) ∧
    ¬ Nonempty (Fin 0 ≃ StateSpace 0) := by
  refine ⟨⟨fC_zero_isInitial⟩, ⟨fD_zero_isInitial⟩, ?_⟩
  rintro ⟨e⟩
  exact (e.symm 0).elim0

/-- The Kleisli bottom `fC_functor.obj 0` is initial, yet its carrier `Fin 0` (empty) is not in
    bijection with the p-adic floor `{0} ⊆ Q₂` (a singleton). Paired with `padic_bottom_not_initial`
    (the floor is not initial), this separates the Kleisli bottom from the p-adic bottom. -/
theorem split_kleisli_vs_padic :
    Nonempty (Limits.IsInitial (fC_functor.obj 0)) ∧
    ¬ Nonempty (Fin 0 ≃ ↥({(0 : Q₂)} : Set Q₂)) := by
  refine ⟨⟨fC_zero_isInitial⟩, ?_⟩
  rintro ⟨e⟩
  exact (e.symm ⟨0, rfl⟩).elim0

/-! ## #5 straddle — the missing terminal half of the Hilbert bottom -/

/-- The Hilbert bottom `fD_functor.obj 0` is terminal in `ModuleCat ℂ`. With
    `ZPH_HilbFunctor.fD_zero_isInitial` (initial) this witnesses it as a zero object (initial ∧
    terminal = μ ∧ tree ν): the straddling node at the μ/ν root. -/
noncomputable def fD_zero_isTerminal :
    Limits.IsTerminal (fD_functor.obj 0) := by
  haveI : Subsingleton (StateSpace 0) := ⟨fun a b => by
    apply WithLp.ofLp_injective
    funext i
    exact Fin.elim0 i⟩
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℂ (StateSpace 0))).isTerminal

end ZeroParadox.ZPH_MC1_TreeObstructions

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib ordinal / `TopCat` / `ModuleCat` / p-adic libraries —
a library dependency, not a new commitment. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TreeObstructions

#print axioms ordinal_carrier_wellFounded
#print axioms real_carrier_not_wellFounded
#print axioms no_strictMono_real_to_ordinal
#print axioms simplex_antichain
#print axioms padic_bottom_not_initial
#print axioms split_kleisli_vs_hilbert
#print axioms split_kleisli_vs_padic
#print axioms fD_zero_isTerminal

end PurityCheck
