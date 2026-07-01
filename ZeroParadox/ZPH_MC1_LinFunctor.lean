-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators

set_option maxHeartbeats 400000

/-!
# Info → Hilbert: the linearization functor (a genuine inter-domain edge — full functoriality proved)

**Proves.** `L : FinStoch ⥤ ModuleCat ℂ` — an actual functor (object map, morphism map, AND functoriality
`map_id`/`map_comp`, no `sorry`) from finite stochastic maps to ℂ-modules: a finite type to its free
ℂ-module, a Markov kernel `Fin a → PMF (Fin b)` to its expectation linear map `δ_i ↦ Σⱼ k(i)(j)·δⱼ`.
`map_comp` is the law of total probability as matrix product (`bind_toReal_sum`). `L_bot_isInitial`: `L`
carries the Info bottom `⟨0⟩` (empty type) to an initial object of `ModuleCat ℂ` (the Hilbert zero module).

This is the real edge the cold audit said `ZPH_MC1_Linearize` only stand-in'd: it REPLACES "two initial
objects coincide" with a genuine transform between the two domains, carrying ⊥_C → ⊥_D via an honest functor.

**Prior art (cite, not novel):** linearizing a Markov category is standard — Markov categories (Fritz 2020;
already cited in `ZPH_MC1`), the classical linear representation of stochastic matrices (FinStoch ↪ Vect).
The free-module (Hilbert) side is Mathlib's (`ModuleCat.free` / `Finsupp.lift`); reused, not reproved.

**Scope (honest):** FINITE types only (objects `Fin n`). A general `PMF` can have infinite support, so its
pushforward would not be finitely supported; on `Fin n` it always is — and the snap tower is all `Fin n`,
so finite is exactly what the framework needs. Remaining (not done here): comparing `L` precomposed with the
snap-tower (`fC_functor ⋙ L`) to `fD_functor` — the tower-level tie to the existing framework objects.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.FinStoch

open CategoryTheory

/-- Objects of the finite-stochastic category: `⟨n⟩` stands for `Fin n`. -/
structure FinStoch where
  n : ℕ

/-- The finite-stochastic category: morphisms are stochastic kernels `Fin a.n → PMF (Fin b.n)`,
    composition is Kleisli (`bind`), identity is the Dirac kernel (`PMF.pure`). Laws follow from the
    PMF monad laws. -/
noncomputable instance : Category FinStoch where
  Hom a b := Fin a.n → PMF (Fin b.n)
  id a := fun i => PMF.pure i
  comp f g := fun i => (f i).bind g
  id_comp f := by funext i; simp [PMF.pure_bind]
  comp_id f := by funext i; simp [PMF.bind_pure]
  assoc f g h := by funext i; simp [PMF.bind_bind]

/-- The expectation linear map of a stochastic kernel: `δ_i ↦ Σ_j k(i)(j)·δ_j` (masses `ℝ≥0∞` → ℝ → ℂ),
    extended linearly via `Finsupp.lift`. The free-vector-space image of a Markov kernel. -/
noncomputable def linMap {a b : FinStoch} (f : Fin a.n → PMF (Fin b.n)) :
    (Fin a.n →₀ ℂ) →ₗ[ℂ] (Fin b.n →₀ ℂ) :=
  Finsupp.lift (Fin b.n →₀ ℂ) ℂ (Fin a.n)
    (fun i => Finsupp.equivFunOnFinite.symm (fun j => ((f i j).toReal : ℂ)))

/-- `linMap` on a basis vector `single i c`: `c` times the kernel's row as a free-module vector. -/
theorem linMap_single {a b : FinStoch} (f : Fin a.n → PMF (Fin b.n)) (i : Fin a.n) (c : ℂ) :
    linMap f (Finsupp.single i c)
      = c • Finsupp.equivFunOnFinite.symm (fun j => ((f i j).toReal : ℂ)) := by
  simp [linMap, Finsupp.lift_apply, Finsupp.sum_single_index]

/-- `linMap` as a matrix action: coordinate `k` of `linMap h v` is `∑ⱼ vⱼ · (h j k).toReal`. -/
theorem linMap_apply {a b : FinStoch} (h : Fin a.n → PMF (Fin b.n)) (v : Fin a.n →₀ ℂ) (k : Fin b.n) :
    (linMap h v) k = ∑ j, (v j) * ((h j k).toReal : ℂ) := by
  simp only [linMap, Finsupp.lift_apply]
  rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.coe_equivFunOnFinite_symm,
    smul_eq_mul]

/-- The law of total probability as a real identity: `toReal` of a `bind` mass is the sum of products of
    `toReal` masses (the Chapman-Kolmogorov / matrix-product step), cast to ℂ. -/
theorem bind_toReal_sum {m n : ℕ} (p : PMF (Fin m)) (q : Fin m → PMF (Fin n)) (k : Fin n) :
    (((p.bind q) k).toReal : ℂ) = ∑ j, ((p j).toReal : ℂ) * ((q j k).toReal : ℂ) := by
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top (p.apply_ne_top j) ((q j).apply_ne_top k))]
  simp only [Complex.ofReal_sum, ENNReal.toReal_mul, Complex.ofReal_mul]

/-- **The linearization functor** `FinStoch ⥤ ModuleCat ℂ`: a finite type to its free ℂ-module, a
    stochastic kernel to its expectation linear map. Functoriality (`map_id`, `map_comp`) is the real
    content — `map_comp` is the law of total probability as matrix product. -/
noncomputable def L : FinStoch ⥤ ModuleCat ℂ where
  obj a := ModuleCat.of ℂ (Fin a.n →₀ ℂ)
  map {a b} f := ModuleCat.ofHom (linMap f)
  map_id a := by
    have hid : (𝟙 a : Fin a.n → PMF (Fin a.n)) = fun i => PMF.pure i := rfl
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    apply Finsupp.lhom_ext
    intro i c
    ext k
    simp only [hid, linMap_single, Finsupp.smul_apply, Finsupp.coe_equivFunOnFinite_symm,
      LinearMap.id_coe, id_eq, Finsupp.single_apply, smul_eq_mul, PMF.pure_apply]
    rcases eq_or_ne k i with h | h
    · subst h; simp
    · simp [h, Ne.symm h]
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    apply Finsupp.lhom_ext
    intro i c
    ext k
    simp only [LinearMap.comp_apply, linMap_apply, Finsupp.single_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [show ((f ≫ g) i) = (f i).bind g from rfl, bind_toReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The functor carries the Info bottom `⟨0⟩` (the empty type `Fin 0`) to an initial object of
    `ModuleCat ℂ` — the Hilbert bottom (zero module). Bottom-preservation via the REAL functor `L`, not a
    stand-in iso: ⊥_C ↦ ⊥_D. -/
noncomputable def L_bot_isInitial : Limits.IsInitial (L.obj ⟨0⟩) := by
  haveI : Subsingleton (Fin 0 →₀ ℂ) := ⟨fun a b => Finsupp.ext fun i => i.elim0⟩
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℂ (Fin 0 →₀ ℂ))).isInitial

/-- **Verb-transport test — THIN-BUT-HONEST (cold-audited 2026-06-29).** The kernel's linear representation
    `linMap f` (the matrix of `f`) sends a fixed point of the stochastic action to a fixed vector of the
    operator: if `μ.bind f = μ` (μ stationary — a fixed point of the Markov action), then its free-module
    vector `v_μ` satisfies `linMap f v_μ = v_μ`, a unit eigenvector.

    HONEST SCOPE (corrected per cold audit — do not overstate): this is a near-trivial coordinate identity,
    resting on `bind_toReal_sum` (Chapman–Kolmogorov) plus the hypothesis. It does NOT engage the functor
    structure — `L`, `map_comp`, and naturality are not used in the proof; the carry is via the bare matrix.
    So it does carry a statement about the DYNAMICS from the stochastic side to the linear side (a fixed
    point ↦ a unit eigenvector — genuinely more than "the bottom object exists"), but by matrix coordinates,
    NOT functorially. A genuinely functorial transport (the real next step) would need the composition law
    `map_comp` to do work — e.g. iterating the kernel `fᵏ` ↦ powers of the operator `(linMap f)ᵏ`. Transports
    a KNOWN fact (Markov stationary = unit eigenvector of the transfer operator); success = faithful
    transport, NOT novelty. -/
theorem stationary_transports_to_unit_eigenvector {n : ℕ}
    (f : Fin n → PMF (Fin n)) (μ : PMF (Fin n)) (hμ : μ.bind f = μ) :
    linMap (a := ⟨n⟩) (b := ⟨n⟩) f (Finsupp.equivFunOnFinite.symm (fun i => ((μ i).toReal : ℂ)))
      = Finsupp.equivFunOnFinite.symm (fun i => ((μ i).toReal : ℂ)) := by
  ext k
  rw [linMap_apply]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [← bind_toReal_sum μ f k, hμ]

/-- **Composition transport.** The linearization of the `k`-step iterated kernel `fᵏ` (categorical
    composition in `FinStoch`) equals the `k`-th power of the transfer operator: `L(fᵏ) = (L f)ᵏ`. So the
    verb composes across the boundary — linearizing-the-iterated-action = iterating-the-linearized-operator.

    HONEST SCOPE (do not overstate): this is `map_pow` of Mathlib's `Functor.mapEnd` (the functor as a monoid
    hom on endomorphisms). It is GENERIC functoriality — every functor preserves powers of endomorphisms — so
    the proof is a one-line library application. The only framework-specific content sits underneath, in
    `mapEnd`'s `map_mul'`, which here is `map_comp` = Chapman–Kolmogorov. Faithful transport of a standard
    fact, not novelty. -/
theorem L_map_pow {n : ℕ} (f : End (⟨n⟩ : FinStoch)) (k : ℕ) :
    Functor.mapEnd (⟨n⟩ : FinStoch) L (f ^ k) = (Functor.mapEnd (⟨n⟩ : FinStoch) L f) ^ k :=
  map_pow (Functor.mapEnd (⟨n⟩ : FinStoch) L) f k

end ZeroParadox.FinStoch

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.FinStoch
#print axioms L
#print axioms L_bot_isInitial
#print axioms stationary_transports_to_unit_eigenvector
#print axioms L_map_pow
end PurityCheck
