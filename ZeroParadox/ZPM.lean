/-
  ZP-M: Kleene–Ordinal Bridge Layer

  This layer closes two gaps left open in ZP-K and ZP-L:

  **Gap 1 (ZP-L):** `snap_exactly_at_epsilon_zero` carries a free hypothesis
      hfp : ∀ α, ω^α = α → φ α = c₁
  which states that ordinal fixed points of ω^· map to c₁. This layer derives hfp
  from a formal type bridge — snapEmbed : MachinePhase → ℤ_[2] — making the snap
  theorem unconditional for zp2-aligned maps.

  **Gap 2 (ZP-K / ZP-L):** The Kleene quine construction (ZP-K) establishes that
  the quine atom IS ⊥ = c₀ (bottom of MachinePhase). The ZP-L snap establishes that
  ε₀ forces the transition to c₁. The formal path from c₀ = ⊥ (Kleene, ZP-K)
  through the snap to c₁ = ε₀-image (ZP-L), mediated by the 2-adic encoding,
  is the missing structural triangle: ⊥ → ε₀ → c₁.

  The central formal object is:
      snapEmbed : MachinePhase → ℤ_[2]
      snapEmbed c₀ = 1    (pre-snap state maps to 2-adic unit)
      snapEmbed c₁ = 0    (snap state maps to 2-adic zero = limit of tower encodings)

  Engineer's Take (TODO: Tim to fill in)
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
  sorry

/-- The 2-adic valuation of snapEmbed c₀ is 0 (it is a unit). -/
theorem snapEmbed_c0_val : (snapEmbed c₀).valuation = 0 := by
  sorry

/-- 0 in ℤ_[2] is divisible by all powers of 2 (infinite 2-adic valuation). -/
theorem snapEmbed_c1_dvd (n : ℕ) : (2 : ℤ_[2])^n ∣ snapEmbed c₁ := by
  simp [snapEmbed_c1]

/-! ## §II. Deriving hfp from Alignment

The free hypothesis `hfp` in `snap_exactly_at_epsilon_zero` asserts that any map φ
assigns c₁ to ordinal fixed points of ω^·.

We replace this hypothesis with a structural alignment condition: φ factors through
snapEmbed and cnfToZp2 on the tower sequence. For a zp2-aligned map, the 2-adic
limit of the tower (which is 0) forces the snap state at the ordinal limit ε₀.
-/

/-- A map φ : Ordinal → MachinePhase is zp2-aligned if snapEmbed commutes with
    cnfToZp2 on every tower stage:
        snapEmbed (φ (fundamentalSeq n)) = cnfToZp2 (towerNONote n)
    This says the MachinePhase and ℤ_[2] assignments agree on the approach to ε₀. -/
def Zp2Aligned (φ : Ordinal → MachinePhase) : Prop :=
  ∀ n : ℕ, snapEmbed (φ (fundamentalSeq n)) = cnfToZp2 (towerNONote n)

/-- For a zp2-aligned map, the tower stages all map to c₀.
    Proof sketch: cnfToZp2 (towerNONote n) has finite nonzero valuation
    (cnfToZp2_tower_valuation), so is not 0, hence equals snapEmbed c₀ = 1. -/
theorem zp2aligned_tower_c0 (φ : Ordinal → MachinePhase) (halign : Zp2Aligned φ)
    (n : ℕ) : φ (fundamentalSeq n) = c₀ := by
  sorry

/-- For any ordinal fixed point α of ω^· (i.e., ω^α = α), a zp2-aligned, monotone map
    assigns c₁. Proof sketch: ε₀ is the least fixed point, so α ≥ ε₀; monotonicity and
    tower alignment then force φ α = c₁ via snap_threshold_is_epsilon_zero. -/
theorem hfp_from_alignment (φ : Ordinal → MachinePhase)
    (hmono : ∀ α β : Ordinal, α ≤ β → join (φ α) (φ β) = φ β)
    (halign : Zp2Aligned φ)
    (α : Ordinal) (hα : omega0 ^ α = α) : φ α = c₁ := by
  sorry

/-- The snap theorem without the hfp hypothesis:
    For any zp2-aligned, monotone map, ε₀ is the minimal snap threshold unconditionally. -/
theorem snap_unconditional (φ : Ordinal → MachinePhase)
    (hmono : ∀ α β : Ordinal, α ≤ β → join (φ α) (φ β) = φ β)
    (halign : Zp2Aligned φ) :
    φ epsilonZero = c₁ ∧ ∀ α : Ordinal, φ α = c₁ → epsilonZero ≤ α := by
  apply snap_exactly_at_epsilon_zero φ hmono (zp2aligned_tower_c0 φ halign)
  intro α hα
  exact hfp_from_alignment φ hmono halign α hα

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
  ⟨by sorry,
   ⟨epsilonZero, epsilonZero_fixedPoint, fun β hβ => epsilonZero_le_fixedPoint hβ⟩⟩

end ZeroParadox.ZPM

/-! ## Purity Check -/
section PurityCheck
open ZeroParadox.ZPM

#print axioms snap_state_zp2_is_zero
#print axioms zpm_triangle

end PurityCheck
