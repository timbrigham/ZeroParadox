-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1_TreeObstructions
import ZeroParadox.ZPH_PerronFrobenius
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC16 / TC13 — the unplaced node: does the Markov attractor (#2) admit ANY order-extremal or categorical placement?

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

Node **#2** (the Markov-dynamical stationary attractor, a point of `stdSimplex ℝ (Fin n)`) is the one
framework bottom the campaign never gave a Lean witness placing on the μ/ν fork. The table records
"attractor = ν is heuristic, no Lean witness" (T2, §7.2). T2 only ruled out a *global* homeomorphism
of the two ν-ambients (the connected-vs-totally-disconnected wall); it never asked whether #2 itself
is a μ- or ν-object *in its own ambient*. TC05 placed the p-adic floor #3 dynamically, not #2.

This file probes #2 directly. The pre-registered **NO-GO** was: the stationary point has **no
order-extremal characterization** in the simplex — it is an antichain element of `stdSimplex`
(`simplex_antichain`, ZPH_MC1_TreeObstructions), so it is neither order-least nor order-greatest. The
pre-registered **GO** was a genuine categorical ν-witness (an `IsLimit` / terminal characterization of
the attractor as a cone over the orbit diagram), paralleling `fB_bottom_is_limit` for #3.

**Race outcome: NO-GO PROVEN (order-extremal characterization is impossible).**

The load-bearing content is in the statements, at two levels of specificity.

**Generic level** — for `n ≥ 2` (the nondegenerate simplex), and for **any** point `s` of the simplex
(the lemmas in fact hold for any function `Fin n → ℝ`, since the simplex membership of the *vertices*,
not of `s`, does the work):

- `stdSimplex_no_isLeast` — `s` is **not** `IsLeast (stdSimplex ℝ (Fin n)) s` (no least element in the
  coordinate order).
- `stdSimplex_no_isGreatest` — `s` is **not** `IsGreatest (stdSimplex ℝ (Fin n)) s` (no greatest).
- `stdSimplex_no_order_placement` — the conjunction.

**Framework level** — the named result that actually mentions node #2. The Markov stationary attractor is
a *specific* point: the simplex coordinates `fun i => (μ i).toReal` of a stationary distribution
`μ : PMF (Fin n)` with `μ.bind f = μ`, whose existence is `exists_stationary` (the Cesàro / Krylov–
Bogolyubov fixed point on the compact simplex). The corollary

- `stationary_attractor_no_order_placement` — for `n ≥ 2` and any finite stochastic kernel `f`, **there
  exists** a stationary distribution `μ` (i.e. `μ.bind f = μ`) whose simplex point lies in
  `stdSimplex ℝ (Fin n)` and is **neither** order-least **nor** order-greatest in it

instantiates the generic NO-GO on the genuine framework object, so the attractor enters a theorem rather
than only the prose. (The earlier `attractor_*` names that quantified over an arbitrary `s` while claiming
to be about the attractor have been renamed to `stdSimplex_*` to match exactly what they prove; the
attractor-specific claim is now carried only by `stationary_attractor_no_order_placement`.)

Both negations reduce to `simplex_antichain`: a least element would lie `≤` both distinct vertices
`Pi.single 0 1` and `Pi.single 1 1`, and the antichain property would force it equal to both, hence the
two vertices equal — false at coordinate `0`. Dually for greatest. The GO direction was **not** built:
no `IsLimit` cone over the orbit diagram is provided here.

**What this proves vs. interpretation.** Lean proves: *in the coordinate (Pi) order on the simplex, the
genuine stationary attractor `fun i => (μ i).toReal` has no least/greatest (initial/terminal-in-the-order-
category) characterization* — the framework object, not just an arbitrary point. The
interpretation — that #2's "ν" label is therefore purely **dynamical** (attractor convergence) with no
order/categorical content, confirming the table's diagnosis that #2 and #3 are "ν in different senses"
and that the genuine T2 asymmetry is a **category error** (#2 is not a tree node of the same kind as the
categorical-ν #3) — is interpretation grounded in, but not identical to, these theorems. The Lean rules
out the *coordinate-order* placement specifically; it does not rule out every conceivable category
structure on the simplex (only the natural order one a descent map would use).
-/

namespace ZeroParadox.ZPH_MC1_TC16

open ZeroParadox.ZPH_MC1_TreeObstructions

/-- The two standard basis vertices `Pi.single 0 1` and `Pi.single 1 1` of the simplex over `Fin n`
    (`n ≥ 2`) are **distinct**: they disagree at coordinate `0`. This is the nondegeneracy that drives
    the no-extremal-placement results. -/
theorem vertices_distinct {n : ℕ} (hn : 2 ≤ n) :
    (Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℝ) : Fin n → ℝ)
      ≠ (Pi.single (⟨1, by omega⟩ : Fin n) (1 : ℝ) : Fin n → ℝ) := by
  intro h
  have hne : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) := by
    apply Fin.ne_of_val_ne; simp
  have := congrFun h (⟨0, by omega⟩ : Fin n)
  rw [Pi.single_eq_same] at this
  rw [Pi.single_eq_of_ne hne] at this
  exact one_ne_zero this

/-- **NO-GO (least half).** For `n ≥ 2`, no point `s` is an `IsLeast` of the simplex in the coordinate
    (Pi) order: a least element would be `≤` both distinct vertices, and `simplex_antichain` would force
    it equal to each, hence the two vertices equal — contradiction. (Generic over `s`; the framework
    instance is `stationary_attractor_no_order_placement` below.) -/
theorem stdSimplex_no_isLeast {n : ℕ} (hn : 2 ≤ n) (s : Fin n → ℝ) :
    ¬ IsLeast (stdSimplex ℝ (Fin n)) s := by
  rintro ⟨hsmem, hlb⟩
  set e0 : Fin n → ℝ := Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℝ) with he0
  set e1 : Fin n → ℝ := Pi.single (⟨1, by omega⟩ : Fin n) (1 : ℝ) with he1
  have h0mem : e0 ∈ stdSimplex ℝ (Fin n) := single_mem_stdSimplex ℝ _
  have h1mem : e1 ∈ stdSimplex ℝ (Fin n) := single_mem_stdSimplex ℝ _
  -- s ≤ each vertex, and by the antichain property s equals each vertex
  have hse0 : s = e0 := simplex_antichain s e0 hsmem h0mem (hlb h0mem)
  have hse1 : s = e1 := simplex_antichain s e1 hsmem h1mem (hlb h1mem)
  exact vertices_distinct hn (hse0.symm.trans hse1)

/-- **NO-GO (greatest half).** Dually, for `n ≥ 2`, no point `s` is an `IsGreatest` of the simplex in
    the coordinate (Pi) order. (Generic over `s`.) -/
theorem stdSimplex_no_isGreatest {n : ℕ} (hn : 2 ≤ n) (s : Fin n → ℝ) :
    ¬ IsGreatest (stdSimplex ℝ (Fin n)) s := by
  rintro ⟨hsmem, hub⟩
  set e0 : Fin n → ℝ := Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℝ) with he0
  set e1 : Fin n → ℝ := Pi.single (⟨1, by omega⟩ : Fin n) (1 : ℝ) with he1
  have h0mem : e0 ∈ stdSimplex ℝ (Fin n) := single_mem_stdSimplex ℝ _
  have h1mem : e1 ∈ stdSimplex ℝ (Fin n) := single_mem_stdSimplex ℝ _
  -- each vertex ≤ s, and by the antichain property each vertex equals s
  have hse0 : e0 = s := simplex_antichain e0 s h0mem hsmem (hub h0mem)
  have hse1 : e1 = s := simplex_antichain e1 s h1mem hsmem (hub h1mem)
  exact vertices_distinct hn (hse0.trans hse1.symm)

/-- **NO-GO (full, generic).** For `n ≥ 2`, **any** simplex point is **neither** order-least **nor**
    order-greatest in the simplex's coordinate order. Generic over `s`; the framework instance is the
    next theorem. -/
theorem stdSimplex_no_order_placement {n : ℕ} (hn : 2 ≤ n) (s : Fin n → ℝ) :
    ¬ IsLeast (stdSimplex ℝ (Fin n)) s ∧ ¬ IsGreatest (stdSimplex ℝ (Fin n)) s :=
  ⟨stdSimplex_no_isLeast hn s, stdSimplex_no_isGreatest hn s⟩

/-- **NO-GO on the genuine node #2.** For `n ≥ 2` and any finite stochastic kernel `f`, there is an
    actual Markov stationary attractor — a distribution `μ : PMF (Fin n)` fixed by the Kleisli action
    (`μ.bind f = μ`, from `exists_stationary`) — whose simplex coordinates `fun i => (μ i).toReal` lie in
    `stdSimplex ℝ (Fin n)` and are **neither** order-least **nor** order-greatest in it.

    This is the framework-level statement: the load-bearing object (the real stationary attractor #2, not
    an arbitrary simplex point) appears *in the theorem*. The attractor admits no order-extremal
    (categorical initial/terminal-in-the-order) characterization in its own ambient; its "ν" label is
    therefore dynamical (attractor convergence), not order/categorical, content. -/
theorem stationary_attractor_no_order_placement {n : ℕ} (hn : 2 ≤ n)
    [Nonempty (Fin n)] (f : Fin n → PMF (Fin n)) :
    ∃ μ : PMF (Fin n), μ.bind f = μ ∧
      (fun i => (μ i).toReal) ∈ stdSimplex ℝ (Fin n) ∧
      ¬ IsLeast (stdSimplex ℝ (Fin n)) (fun i => (μ i).toReal) ∧
      ¬ IsGreatest (stdSimplex ℝ (Fin n)) (fun i => (μ i).toReal) := by
  obtain ⟨μ, hμ⟩ := ZeroParadox.PerronFrobenius.exists_stationary f
  refine ⟨μ, hμ, ?_, stdSimplex_no_isLeast hn _, stdSimplex_no_isGreatest hn _⟩
  refine ⟨fun i => ENNReal.toReal_nonneg, ?_⟩
  have h1 : ∑ i, μ i = 1 := by
    have h := μ.tsum_coe
    rwa [tsum_eq_sum (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)] at h
  rw [← ENNReal.toReal_sum (fun i _ => μ.apply_ne_top i), h1, ENNReal.toReal_one]

end ZeroParadox.ZPH_MC1_TC16

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib simplex / order / big-operators libraries — a library
dependency (inherited through `simplex_antichain`), not a new commitment. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC16

#print axioms vertices_distinct
#print axioms stdSimplex_no_isLeast
#print axioms stdSimplex_no_isGreatest
#print axioms stdSimplex_no_order_placement
#print axioms stationary_attractor_no_order_placement

end PurityCheck
