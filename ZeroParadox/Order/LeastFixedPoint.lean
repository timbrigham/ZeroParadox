import ZeroParadox.Ordinal.Epsilon0MinMax
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Computability.Kleene
import Mathlib.Order.FixedPoints
import Mathlib.SetTheory.Ordinal.FixedPoint

set_option maxHeartbeats 400000

/-!
# The μ abstraction: least fixed point reached from a seed (the ceiling analogue of `AbstractSelfApp`)

## Engineer's Take

Define epsilon 0 as a minimum fixed point in an abstract class, instead of a fixed class for a given
framework. Denotes a common placement relative to zero.

---

## Formal Overview
`IsLeastFixedPointFrom r f seed mu` — the Knaster–Tarski least fixed point at or above a seed, over a
bare relation so it spans carriers. Three faces — ε₀ (genuine ascent), `selfApp` (degenerate), Kleene
(FENCED) — share a **SHAPE**, never one object. Schema, faces and the type-boundary fence: `ZeroParadox/Order/LeastFixedPoint.md`.
-/

namespace ZeroParadox

open Ordinal

/-! ## § I. The μ schema: least fixed point reached from a seed -/

/-- `mu` is the **least fixed point of `f` at or above `seed`**, with respect to the relation `r`.
    The order-generic Knaster–Tarski / μ characterization: `mu` is a fixed point, and any fixed
    point at or above the seed dominates it. Stated over a bare relation `r : α → α → Prop` (not a
    lattice typeclass) so the framework's distinct carriers — `Ordinal` (via `≤`) and the ZP
    semilattice `L` (via `ZPSemilattice.le`) — instantiate the same schema. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's least-fixed-point API (OrderHom.lfp, isLeast_lfp)
-- is fixed to a CompleteLattice carrier. This predicate states the SAME μ characterization
-- (least fixed point at/above a seed) over a bare relation so it applies to the framework's
-- non-lattice carriers (the axiom-clean ZPSemilattice L, and Ordinal which is not a complete
-- lattice). It is the order-generic placement schema, grounded back to OrderHom.lfp in § II.
structure IsLeastFixedPointFrom {α : Type*} (r : α → α → Prop) (f : α → α) (seed mu : α) : Prop where
  /-- The seed lies at or below the μ closure. -/
  seed_le : r seed mu
  /-- `mu` is a fixed point of `f`. -/
  fixed   : f mu = mu
  /-- `mu` is least among fixed points at or above the seed. -/
  least   : ∀ b : α, f b = b → r seed b → r mu b

/-- The schema pins a **unique** object within one carrier: given antisymmetry of `r`, any two least
    fixed points of `f` from the same seed coincide. (This is a within-carrier statement only — it
    says nothing across the distinct carriers of the faces; that identity is the ill-typed
    type-boundary fence.) -/
theorem IsLeastFixedPointFrom.unique {α : Type*} {r : α → α → Prop} {f : α → α} {seed mu mu' : α}
    (antisymm : ∀ x y : α, r x y → r y x → x = y)
    (h : IsLeastFixedPointFrom r f seed mu) (h' : IsLeastFixedPointFrom r f seed mu') :
    mu = mu' :=
  antisymm mu mu' (h.least mu' h'.fixed h'.seed_le) (h'.least mu h.fixed h.seed_le)

/-! ## § II. Grounding: the schema IS Mathlib's `OrderHom.lfp` (Knaster–Tarski)

On a complete lattice, the standard least fixed point `f.lfp` witnesses the schema from ⊥. This
anchors `IsLeastFixedPointFrom` to recognized order theory — it is not ZP-invented structure. -/

/-- On a complete lattice, Mathlib's `OrderHom.lfp` is the least fixed point from ⊥ in the sense of
    the schema. Wraps `OrderHom.map_lfp` (fixed) and `OrderHom.lfp_le_fixed` (least). -/
theorem lfp_isLeastFixedPointFrom {α : Type*} [CompleteLattice α] (f : α →o α) :
    IsLeastFixedPointFrom (· ≤ ·) (⇑f) (⊥ : α) f.lfp where
  seed_le := bot_le
  fixed := f.map_lfp
  least := fun _ hb _ => f.lfp_le_fixed hb

/-! ## § III. The general ordinal μ: `nfp` of a normal function

For any normal ordinal function, its next fixed point `nfp f a` (the supremum of the finite iterates
from `a`) is the least fixed point from `a` — the Kleene ascent μ on ordinals. Reuses Mathlib's
`le_nfp`, `nfp_fp`, `nfp_le_fp`. -/

/-- For a normal `f : Ordinal → Ordinal`, `nfp f a` is the least fixed point from the seed `a`. -/
theorem isLeastFixedPointFrom_nfp {f : Ordinal → Ordinal} (H : Order.IsNormal f) (a : Ordinal) :
    IsLeastFixedPointFrom (· ≤ ·) f a (Ordinal.nfp f a) where
  seed_le := Ordinal.le_nfp f a
  fixed := Ordinal.nfp_fp H a
  least := fun _b hb hab => Ordinal.nfp_le_fp H.strictMono.monotone hab (le_of_eq hb)

/-! ## § IV. The ε₀ face — genuine ascent μ (seed ⊥ ≠ closure ε₀)

⚠ **THE ASCENT IS GENUINE; THE SEED IS NOT DISTINGUISHED WITHIN `[0, ε₀]`.**
`nfp_seed_independent_below_epsilon0` (`ZeroParadox/Ordinal/Epsilon0LeastFP.lean`) proves
`∀ a ≤ ε₀, nfp (ω^·) a = ε₀`. ⚠ Scope is at or below ε₀, and normality is load-bearing. Veblen's
classical form, the seed-as-role reading, and the SHAPE-never-instance-of fence: `ZeroParadox/Order/LeastFixedPoint.md`. -/

/-- **ε₀ face.** ε₀ is the least fixed point of `α ↦ ω^α` from the ordinal bottom ⊥. The seed ⊥ and
    the closure ε₀ are distinct — this is the genuine ascent μ. Reuses `epsilonZero_fixedPoint`
    and `epsilonZero_le_fixedPoint` (`Ordinal/Gentzen.lean`); nothing reproved. -/
theorem epsilon0_isLeastFixedPointFrom :
    IsLeastFixedPointFrom (· ≤ ·) (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal) epsilonZero where
  seed_le := bot_le
  fixed := epsilonZero_fixedPoint
  least := fun _ hb _ => epsilonZero_le_fixedPoint hb

/-- The ε₀ face is literally the general ordinal `nfp` μ at `f = ω^·`, seed ⊥ (via
    `isLeastFixedPointFrom_nfp` on the normal function `ω^·`). With `epsilon0_eq_nfp_bot`
    (`ε₀ = nfp (ω^·) ⊥`), this identifies the two presentations of the same μ. -/
theorem epsilon0_isLeastFixedPointFrom_via_nfp :
    IsLeastFixedPointFrom (· ≤ ·) (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal)
      (Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal)) :=
  isLeastFixedPointFrom_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) ⊥

/-- The closure = supremum of the ascending iterates, for the ε₀ face: ε₀ is the supremum of the
    ω-tower stages. Re-exposes `epsilonZero_eq_iSup` (`Ordinal/Gentzen.lean`) as the Kleene-ascent
    content of the ε₀ μ. -/
theorem epsilon0_mu_eq_iSup : epsilonZero = ⨆ n : ℕ, fundamentalSeq n :=
  epsilonZero_eq_iSup

/-! ## § V. The self-reference face — degenerate/floor μ (seed = closure = ⊥) -/

/-- **Self-reference face.** In any `AbstractSelfApp` semilattice, ⊥ is the least fixed point of
    `selfApp` from the seed ⊥ (w.r.t. `ZPSemilattice.le`). Here seed = closure = ⊥: the μ
    construction collapses onto the seed. This is the floor μ — the Gödel-inversion fact that
    self-reference sits *at* the floor, the ceiling analogue's degenerate case. Uses `fixed_bot`
    and the semilattice bottom law `bot_join`. -/
theorem selfApp_isLeastFixedPointFrom {L : Type*} [ZPSemilattice L] [AbstractSelfApp L] :
    IsLeastFixedPointFrom (ZPSemilattice.le) (AbstractSelfApp.selfApp)
      (ZPSemilattice.bot : L) (ZPSemilattice.bot : L) where
  seed_le := ZPSemilattice.le_refl _
  fixed := AbstractSelfApp.fixed_bot
  least := fun b _ _ => ZPSemilattice.bot_join b

/-- On the self-reference face the schema's uniqueness collapses to the AFA uniqueness: ⊥ is the
    only least fixed point of `selfApp` from ⊥ (via `IsLeastFixedPointFrom.unique` with
    `ZPSemilattice.le_antisymm`). -/
theorem selfApp_mu_unique {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]
    {mu : L} (h : IsLeastFixedPointFrom (ZPSemilattice.le) (AbstractSelfApp.selfApp)
      (ZPSemilattice.bot : L) mu) : mu = ZPSemilattice.bot :=
  IsLeastFixedPointFrom.unique (fun _ _ => ZPSemilattice.le_antisymm)
    h selfApp_isLeastFixedPointFrom

/-! ## § VI. The Kleene face — FENCED (same shape, different setting)

Rogers'/Kleene's recursion theorem gives a fixed point of any computable self-map of `Code`. This is
the same μ-*shape* (a self-map has a fixed point) in a different *setting*: `Code` carries no
complete-lattice order, so there is no `lfp`; its fixed points are NOT unique
(`infinite_quine_family`); and there is no seed→closure ascent. Hence it does **not** instantiate
`IsLeastFixedPointFrom` — recorded as an existence statement with the fence in prose. The
cross-face identity (Ordinal μ = `L` μ = `Code` μ) is a type boundary, not a proposition. -/

open Nat.Partrec Nat.Partrec.Code in
/-- **Kleene face (fenced).** For any computable `f : Code → Code` a behavioral fixed point exists
    (`eval (f c) = eval c`). Wraps `roger_fixed_point_exists`. NOT an `IsLeastFixedPointFrom`: no
    lattice order on `Code`, fixed points non-unique, no seed→closure — same shape, different
    setting. -/
theorem kleene_fixed_point_from_exists (f : Code → Code) (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  roger_fixed_point_exists f hf

end ZeroParadox

/-! ## Axiom Purity Check

The schema's `selfApp_*` instances and `IsLeastFixedPointFrom.unique` are axiom-free (no axioms at
all); the Mathlib-`lfp` grounding `lfp_isLeastFixedPointFrom` is choice-free `[propext, Quot.sound]`.
The ordinal faces (`isLeastFixedPointFrom_nfp`, `epsilon0_*`) inherit
`Classical.choice` from Mathlib's `Ordinal`/`nfp` fixed-point theory. **Status: UNCLASSIFIED.**
⚠ **Do NOT call it "representational, not intrinsic"** — that is an **eliminability claim**, which no
footprint measurement can establish, and **no choice-free re-proof of these faces was located as of
2026-08-02**. The choice is not in the `Ordinal` type (`[propext, Quot.sound]`) but in the order
instance and the operations. ZP-N's choice-free
snap-from-below is suggestive, not a re-proof. The Kleene face inherits
`[propext, Classical.choice, Quot.sound]` from the `Code`/`Partrec` machinery. Recorded honestly. -/

section PurityCheck
open ZeroParadox

#print axioms IsLeastFixedPointFrom.unique
#print axioms lfp_isLeastFixedPointFrom
#print axioms isLeastFixedPointFrom_nfp
#print axioms epsilon0_isLeastFixedPointFrom
#print axioms epsilon0_isLeastFixedPointFrom_via_nfp
#print axioms epsilon0_mu_eq_iSup
#print axioms selfApp_isLeastFixedPointFrom
#print axioms selfApp_mu_unique
#print axioms kleene_fixed_point_from_exists

end PurityCheck
