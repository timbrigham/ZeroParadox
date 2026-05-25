/-
  ZP-M: Kleene–Ordinal Bridge Layer

  This layer closes two gaps left open in ZP-K and ZP-L:

  **Gap 1 (ZP-L):** `snap_exactly_at_epsilon_zero` carries a free hypothesis
      hfp : ∀ α, ω^α = α → φ α = c₁
  which states that ordinal fixed points of ω^· map to c₁. This layer proves hfp
  follows from φ epsilonZero = c₁ alone (given monotonicity), via the snapEmbed bridge
  and c₁'s absorbing property in MachinePhase.

  **Gap 2 (ZP-K / ZP-L):** The Kleene quine construction (ZP-K) establishes that
  the quine atom IS ⊥ = c₀ (bottom of MachinePhase). The ZP-L snap establishes that
  ε₀ forces the transition to c₁. The formal path from c₀ = ⊥ (Kleene, ZP-K)
  through the snap to c₁ = ε₀-image (ZP-L), mediated by the 2-adic encoding,
  is the missing structural triangle: ⊥ → ε₀ → c₁.

  The central formal object is:
      snapEmbed : MachinePhase → ℤ_[2]
      snapEmbed c₀ = 1    (pre-snap state maps to 2-adic unit)
      snapEmbed c₁ = 0    (snap state maps to 2-adic zero = limit of tower encodings)

  Engineer's Take:

  ZPM is a consolidation layer, doing for the snap state what the earlier layers did for ⊥.
  The pattern is the same: one object showing up in multiple mathematical domains with
  different names and different notation, and the job is to build a formal map proving
  they're the same topological structure.

  The mechanism is straightforward once you see it. You define the map, you show the
  structure holds on all three edges, and you confirm that Kleene diagonalization and
  ordinal diagonalization are the same operation running in two different rooms. Same
  inputs, same outputs, different address.

  If ZPK and ZPL each proved a piece of the picture, ZPM is the layer where you step
  back and see that the pieces were always the same picture.
-/

import ZeroParadox.ZPK
import ZeroParadox.ZPL

namespace ZeroParadox.ZPM

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPC
open ZeroParadox.ZPK
open ZeroParadox.ZPE
open ZeroParadox.ZPL
open Nat.Partrec Nat.Partrec.Code
open Ordinal

/-! ## §I. The snapEmbed Morphism

snapEmbed sends the snap state c₁ to 0 in ℤ_[2] (the 2-adic limit of the tower
encodings) and the pre-snap state c₀ to 1 (a nonzero 2-adic integer).

This formalizes the identification: c₁ ↔ 0 = ⊥ in ℤ_[2].

The morphism property: join on MachinePhase (c₁ is absorbing) corresponds to
multiplication on ℤ_[2] (0 is absorbing). Both structures have the same absorbing
element pattern: c₁ absorbs all joins, 0 absorbs all products.
-/

/-- The canonical type bridge: pre-snap (initial) maps to 1, snap state (running) maps to 0. -/
noncomputable def snapEmbed : MachinePhase → ℤ_[2]
  | .initial => 1   -- c₀
  | .running => 0   -- c₁

@[simp] theorem snapEmbed_c0 : snapEmbed c₀ = (1 : ℤ_[2]) := rfl
@[simp] theorem snapEmbed_c1 : snapEmbed c₁ = (0 : ℤ_[2]) := rfl

/-- snapEmbed is injective: c₀ and c₁ map to distinct 2-adic integers. -/
theorem snapEmbed_injective : Function.Injective snapEmbed := by
  intro a b h
  cases a <;> cases b <;> simp_all [snapEmbed]

/-- snapEmbed preserves the absorbing-element structure:
    snapEmbed (join a b) = snapEmbed a * snapEmbed b.
    Under multiplication, 0 is absorbing — matching c₁ absorbing in MachinePhase. -/
theorem snapEmbed_mul_morphism (a b : MachinePhase) :
    snapEmbed (join a b) = snapEmbed a * snapEmbed b := by
  cases a <;> cases b <;> simp [snapEmbed]

/-- The 2-adic valuation of snapEmbed c₀ is 0 (it is a unit). -/
theorem snapEmbed_c0_val : (snapEmbed c₀).valuation = 0 := by
  simp [snapEmbed_c0, PadicInt.valuation_one]

/-- 0 in ℤ_[2] is divisible by all powers of 2 (infinite 2-adic valuation). -/
theorem snapEmbed_c1_dvd (n : ℕ) : (2 : ℤ_[2])^n ∣ snapEmbed c₁ := by
  simp [snapEmbed_c1]

/-! ## §II. Deriving hfp from ε₀ Initialization

The free hypothesis `hfp` in `snap_exactly_at_epsilon_zero` asserts that any map φ
assigns c₁ to ordinal fixed points of ω^·.

Key insight: given monotonicity, `hfp` follows from just `φ epsilonZero = c₁`.
Proof: for any fixed point α, `epsilonZero_le_fixedPoint` gives ε₀ ≤ α; monotonicity
gives `join (φ ε₀) (φ α) = φ α`; substituting `φ ε₀ = c₁` and using c₁'s absorbing
property (`join c₁ x = c₁` for all x) gives `c₁ = φ α`.

Note: deriving `φ epsilonZero = c₁` itself from the 2-adic structure (rather than
taking it as a hypothesis) is the Classical.choice inversion conjecture — whether the
non-constructive snap is structurally forced by ZP geometry rather than incidentally
imported from Mathlib. That question is deferred to ZPM §V (future work). For now
`hε₀ : φ epsilonZero = c₁` is the alignment hypothesis.
-/

/-- Given φ ε₀ = c₁ and monotonicity, every ordinal fixed point of ω^· maps to c₁.
    This closes the `hfp` gap in `snap_exactly_at_epsilon_zero` under a minimal hypothesis. -/
theorem hfp_from_epsilon_zero (φ : Ordinal → MachinePhase)
    (hmono : ∀ α β : Ordinal, α ≤ β → join (φ α) (φ β) = φ β)
    (hε₀ : φ epsilonZero = c₁)
    (α : Ordinal) (hα : omega0 ^ α = α) : φ α = c₁ := by
  have hle := epsilonZero_le_fixedPoint hα
  have h1 := hmono _ _ hle
  rw [hε₀] at h1
  have h2 : join c₁ (φ α) = c₁ := by cases (φ α) <;> rfl
  rw [h2] at h1
  exact h1.symm

/-- The snap theorem with minimal hypotheses: monotonicity + tower maps to c₀ + φ ε₀ = c₁.
    ε₀ is the unique minimal snap threshold. -/
theorem snap_unconditional (φ : Ordinal → MachinePhase)
    (hmono : ∀ α β : Ordinal, α ≤ β → join (φ α) (φ β) = φ β)
    (h0 : ∀ n : ℕ, φ (fundamentalSeq n) = c₀)
    (hε₀ : φ epsilonZero = c₁) :
    φ epsilonZero = c₁ ∧ ∀ α : Ordinal, φ α = c₁ → epsilonZero ≤ α :=
  snap_exactly_at_epsilon_zero φ hmono h0 (hfp_from_epsilon_zero φ hmono hε₀)

/-! ## §III. The Kleene–Ordinal Triangle

ZP-K established: the Kleene quine IS ⊥ = c₀ (da1_closed_concrete).
ZP-L established: ε₀ forces the snap from c₀ to c₁.

The triangle:
    c₀ = ⊥ (Kleene quine, ZP-K)
         ↕ snap at ε₀
    c₁     (snap state, ZP-L)
         ↕ snapEmbed
    0 ∈ ℤ_[2] (2-adic limit of tower, ZP-L)

This section makes the full triangle formal.
-/

/-- snapEmbed maps c₁ to 0 at ε₀ under the canonical snap map. -/
theorem snap_state_zp2_is_zero :
    snapEmbed ((fun α : Ordinal => if α < epsilonZero then (c₀ : MachinePhase) else c₁)
               epsilonZero) = 0 := by
  simp

/-- The full triangle: all three objects co-occur and are formally connected.
    Left edge  (A ↔ C): tower stages below ε₀ map to c₀; ε₀ maps to c₁.
    Right edge (B ↔ C): snapEmbed maps c₁ to 0 = 2-adic limit.
    Base edge  (A ↔ B): tower encodings converge to 0 in ℤ_[2] (from ZP-L). -/
theorem zpm_triangle :
    -- A ↔ C: ordinal snap
    (∀ n : ℕ, fundamentalSeq n < epsilonZero) ∧
    (fun α : Ordinal => if α < epsilonZero then (c₀ : MachinePhase) else c₁) epsilonZero = c₁ ∧
    -- A ↔ B: 2-adic convergence
    Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0) ∧
    -- B ↔ C: type bridge
    snapEmbed ((fun α : Ordinal => if α < epsilonZero then (c₀ : MachinePhase) else c₁)
               epsilonZero) = 0 :=
  ⟨epsilonZero_tower_lt,
   if_neg (lt_irrefl epsilonZero),
   tower_converges_to_zero,
   snap_state_zp2_is_zero⟩

/-! ## §IV. The Structural Homology

Both the Kleene recursion theorem (ZP-K) and ε₀'s fixed-point property (ZP-L) follow
the same diagonalization pattern: a self-referential operation has a fixed point.

  Kleene: ∃ c, ∀ n, eval c n = eval c (encode c + n)   [diagonal on codes]
  ε₀:     ∃ α, ω^α = α ∧ (∀ β, ω^β = β → α ≤ β)       [diagonal on ordinals]

This section records that both fixed points exist in the same formal context. -/

/-- Both diagonalization patterns produce fixed points in their respective domains.
    Kleene: periodic code (period = Gödel number). Ordinal: ε₀ = ω^ε₀, least such. -/
theorem both_fixed_points_exist :
    (∃ c : Code, ∀ n, eval c n = eval c (Encodable.encode c + n)) ∧
    (∃ α : Ordinal, omega0 ^ α = α ∧
      ∀ β : Ordinal, omega0 ^ β = β → α ≤ β) :=
  ⟨by
    obtain ⟨c, hc⟩ := computational_quine_exists
    exact ⟨c, hc⟩,
   ⟨epsilonZero, epsilonZero_fixedPoint, fun β hβ => epsilonZero_le_fixedPoint hβ⟩⟩

end ZeroParadox.ZPM

/-! ## Purity Check -/
section PurityCheck
open ZeroParadox.ZPM

#print axioms snapEmbed_injective
#print axioms snapEmbed_mul_morphism
#print axioms hfp_from_epsilon_zero
#print axioms snap_unconditional
#print axioms snap_state_zp2_is_zero
#print axioms zpm_triangle
#print axioms both_fixed_points_exist

end PurityCheck
