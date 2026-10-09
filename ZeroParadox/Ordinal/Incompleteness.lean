/-
  ZP-M: Kleene–Ordinal Bridge Layer

  This layer closes two gaps left open in ZP-K and ZP-L:

  **Gap 1 (ZP-L):** `snap_exactly_at_epsilon_zero` carries a free hypothesis
      hfp : ∀ α, ω^α = α → φ α = c₁
  which states that ordinal fixed points of ω^· map to c₁. This layer proves hfp
  follows from φ epsilonZero = c₁ alone (given monotonicity), via c₁'s absorbing
  property in MachinePhase.

  **Gap 2 (ZP-K / ZP-L):** ZP-K establishes that the Quine atom is ⊥ = c₀ (bottom of
  MachinePhase) — an order-theoretic fact about MachinePhase, with no `Code` and no
  execution in the statement. Reading c₀ as *the Kleene quine* is ZP-K's
  `KleeneStructure` commitment, not a theorem, and no equation between a `Code` and a
  `MachinePhase` is well-formed. ZP-L establishes that ε₀ is the *minimal* threshold — **given** that the transition happens,
  it happens nowhere below ε₀. It does not establish that it happens: `snap_unconditional`
  takes `hε₀ : φ epsilonZero = c₁` as a hypothesis. See the fuller note at § III. The formal path from c₀ = ⊥ through the snap at ε₀ to c₁ (ZP-L), mediated through
  `ℤ_[2]` by `cnfToZp2` from the ordinal side and `snapEmbed` from `MachinePhase`, is the missing structural triangle: ⊥ → ε₀ → c₁.

  The central formal object is:
      snapEmbed : MachinePhase → ℤ_[2]
      snapEmbed c₀ = 1    (pre-snap state maps to 2-adic unit)
      snapEmbed c₁ = 0    (snap state maps to 2-adic zero = limit of tower images)

  Engineer's Take:

  ZPM is a consolidation layer, doing for the snap state what the earlier layers did for ⊥.
  The pattern is the same: one object showing up in multiple mathematical domains with
  different names and different notation, and the job is to build a formal map proving
  they're the same topological structure.

  The mechanism is straightforward once you see it. You define the map, you show the
  structure holds on all three edges, and you confirm that Kleene diagonalization and
  ordinal diagonalization follow the same structural pattern: a self-referential
  operation produces a forced fixed point. The two domains are formally separate —
  one over Gödel codes, one over ordinals — but the diagonalization schema is
  identical.

  If ZPK and ZPL each proved a piece of the picture, ZPM is the layer where you step
  back and see that the pieces were always the same picture.
-/

import ZeroParadox.Computability.Kleene
import ZeroParadox.Ordinal.Gentzen

namespace ZeroParadox

open ZeroParadox ZPSemilattice
open ZeroParadox
open ZeroParadox
open ZeroParadox
open ZeroParadox
open Nat.Partrec Nat.Partrec.Code
open Ordinal

/-! ## §I. The snapEmbed Morphism

snapEmbed sends the snap state c₁ to 0 in ℤ_[2] and the pre-snap state c₀ to 1 (`snapEmbed_c1`,
`snapEmbed_c0`), carrying join on MachinePhase to multiplication on ℤ_[2] (`snapEmbed_mul_morphism`).
Long form: `ZeroParadox/Ordinal/Incompleteness.md`.
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

`hfp` is the free hypothesis of `snap_exactly_at_epsilon_zero`.

`hε₀` (`φ ε₀ = c₁`; in the ℤ₂ chart, `snapEmbed (φ ε₀) = 0`) is the snap's occurrence at ε₀,
taken as a hypothesis: of the infinitely many admissible firing points that monotonicity and
tower alignment (every tower stage sent to c₀) leave open, `hε₀` selects the least, and so fixes φ
uniquely (the examples after `snap_unconditional` below). Whether `Classical.choice` is forced by
the metric collapse is a separate open question (`ZeroParadox/Ordinal/SyntacticCollapse.md`).
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

-- `Statement:` `hε₀` is not supplied by `hmono`/`h0`: the constant map c₀ meets both and fails `hε₀`
-- (a fire-at-ε₀+1 witness follows `snap_threshold_is_epsilon_zero` in `ZeroParadox/Ordinal/Gentzen.lean`).
example : ∃ φ : Ordinal → MachinePhase, (∀ α β : Ordinal, α ≤ β → join (φ α) (φ β) = φ β) ∧
    (∀ n : ℕ, φ (fundamentalSeq n) = c₀) ∧ φ epsilonZero ≠ c₁ :=
  ⟨fun _ => c₀, fun _ _ _ => rfl, fun _ => rfl, by decide⟩
-- `Statement:` under `hmono` and `h0` every β ≥ ε₀ is an admissible firing point: the threshold map at β meets both.
example (β : Ordinal) (hβ : epsilonZero ≤ β) :
    let φ : Ordinal → MachinePhase := fun α => if α < β then c₀ else c₁
    (∀ α γ : Ordinal, α ≤ γ → join (φ α) (φ γ) = φ γ) ∧ (∀ n : ℕ, φ (fundamentalSeq n) = c₀) := by
  refine ⟨fun α γ hαγ => ?_, fun n => if_pos (lt_of_lt_of_le (epsilonZero_tower_lt n) hβ)⟩
  by_cases hγ : γ < β
  · have hα : α < β := lt_of_le_of_lt hαγ hγ
    simp only [if_pos hα, if_pos hγ]; rfl
  · simp only [if_neg hγ]; split <;> rfl
-- `Statement:` among those threshold maps, `hε₀` holds exactly at β = ε₀ — it selects the least.
example (β : Ordinal) (hβ : epsilonZero ≤ β) :
    ((fun α => if α < β then (c₀ : MachinePhase) else c₁) epsilonZero = c₁) ↔ β = epsilonZero := by
  constructor
  · intro h
    by_contra hne
    have hlt : epsilonZero < β := lt_of_le_of_ne hβ (Ne.symm hne)
    simp only [if_pos hlt] at h; exact absurd h (by decide)
  · rintro rfl; simp
-- `Statement:` with `hmono`, `h0` and `hε₀`, φ is the canonical threshold map — fixed uniquely.
example (φ : Ordinal → MachinePhase)
    (hmono : ∀ α β : Ordinal, α ≤ β → join (φ α) (φ β) = φ β)
    (h0 : ∀ n : ℕ, φ (fundamentalSeq n) = c₀)
    (hε₀ : φ epsilonZero = c₁) :
    φ = fun α => if α < epsilonZero then c₀ else c₁ := by
  funext α
  by_cases h : α < epsilonZero
  · rw [if_pos h]; exact snap_threshold_is_epsilon_zero φ hmono h0 α h
  · rw [if_neg h]
    have hle : epsilonZero ≤ α := not_lt.mp h
    have h1 := hmono _ _ hle
    rw [hε₀] at h1
    have h2 : join c₁ (φ α) = c₁ := by cases (φ α) <;> rfl
    rw [h2] at h1; exact h1.symm
-- `Statement:` the ℤ₂ chart of `hε₀`: `φ ε₀ = c₁` exactly when `snapEmbed (φ ε₀) = 0`.
example (φ : Ordinal → MachinePhase) :
    φ epsilonZero = c₁ ↔ snapEmbed (φ epsilonZero) = 0 := by
  rw [← snapEmbed_c1]; exact snapEmbed_injective.eq_iff.symm
-- `Statement:` if `snapEmbed ∘ φ` is continuous along the tower into ε₀, then `h0` forces
-- `φ ε₀ = c₀`, the opposite of `hε₀`.
-- `Reading:` uses only that `snapEmbed` is injective and ℤ₂ is Hausdorff; not a 2-adic-specific fact.
example (φ : Ordinal → MachinePhase) (h0 : ∀ n : ℕ, φ (fundamentalSeq n) = c₀)
    (hcont : Filter.Tendsto (fun n => snapEmbed (φ (fundamentalSeq n))) Filter.atTop
      (nhds (snapEmbed (φ epsilonZero)))) : φ epsilonZero = c₀ := by
  have h1 : Filter.Tendsto (fun n => snapEmbed (φ (fundamentalSeq n))) Filter.atTop
      (nhds (snapEmbed c₀)) := by
    simp only [h0]; exact tendsto_const_nhds
  exact snapEmbed_injective (tendsto_nhds_unique hcont h1)
-- `Statement:` the tower stages' `cnfToZp2` images tend to `snapEmbed c₁`.
example : Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop
    (nhds (snapEmbed c₁)) := by
  rw [snapEmbed_c1]; exact tower_converges_to_zero
-- `Statement:` for every φ, `snapEmbed ∘ φ ∘ repr` disagrees with `cnfToZp2` at every tower stage n ≥ 1:
-- `snapEmbed` takes only the values 1 and 0, and stage n ≥ 1 maps to 2^n, which is neither.
example (φ : Ordinal → MachinePhase) (n : ℕ) (hn : 1 ≤ n) :
    snapEmbed (φ (NONote.repr (towerNONote n))) ≠ cnfToZp2 (towerNONote n) := by
  intro h
  have hv := cnfToZp2_tower_valuation n
  rw [← h] at hv
  rcases hφ : φ (NONote.repr (towerNONote n)) with _ | _ <;> rw [hφ] at hv <;>
    simp [snapEmbed] at hv <;> omega
-- `Statement:` under `h0` the disagreement holds at stage 0 too: there `snapEmbed c₀ = 1` and `cnfToZp2 0 = 0`.
example (φ : Ordinal → MachinePhase) (h0 : ∀ n : ℕ, φ (fundamentalSeq n) = c₀) (n : ℕ) :
    snapEmbed (φ (NONote.repr (towerNONote n))) ≠ cnfToZp2 (towerNONote n) := by
  rw [towerNONote_repr, h0, snapEmbed_c0]
  intro h
  rcases n with _ | n
  · exact one_ne_zero (h.trans cnfToZp2_zero)
  · have hv := cnfToZp2_tower_valuation (n + 1)
    rw [← h, PadicInt.valuation_one] at hv
    omega

/-! ## §III. The Kleene–Ordinal Triangle

ZP-K established: ⊥ = c₀ is the unique Quine atom of MachinePhase
(`da1_closed_concrete`). Note what that theorem does *not* say — it mentions no `Code`
and no execution. Reading c₀ as *the Kleene quine* is ZP-K's `KleeneStructure`
commitment, not a theorem, and it is not a Lean `=`: a quine is a `Code` and c₀ is a
`MachinePhase`, so no equation between them is well-formed. See ZP-K § II / § III.
ZP-L established: **given** that the snap happens at ε₀, it happens **nowhere below** it. The
same caution as the ZP-K sentence above applies here: `snap_unconditional` is named for its lack
of a fixed-point hypothesis, not for lacking hypotheses — it takes `hε₀ : φ epsilonZero = c₁` as
an argument, so the snap is assumed and its *minimality* is what is derived. ZP-L does not force
the snap. (Corrected 2026-07-31; this line read "ε₀ forces the snap from c₀ to c₁".)

The triangle (the top node read under that commitment):
    c₀ = ⊥ (the Quine atom; read as the Kleene quine, ZP-K)
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
    Base edge  (A ↔ B): tower images converge to 0 in ℤ_[2] (from ZP-L). -/
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

/-! ## §IV. Shared Diagonalization Pattern

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
    exact ⟨c, quine_period_is_goedel c hc⟩,
   ⟨epsilonZero, epsilonZero_fixedPoint, fun β hβ => epsilonZero_le_fixedPoint hβ⟩⟩

/-! ### Remark R-M.1: DA-1 Path 2 and the Limits of the Diagonalization Frame

`both_fixed_points_exist` is a conjunction of two existentials: each diagonalization yields a
fixed point in its own domain, and no equation between a `Code` and an `Ordinal` is well-formed.
Where L-INF stands relative to that schema, and how that differs from DA-1 Path 2:
`ZeroParadox/Ordinal/Incompleteness.md` § Remark R-M.1. -/

end ZeroParadox

/-! ## Purity Check -/
section PurityCheck
open ZeroParadox

#print axioms snapEmbed_injective
#print axioms snapEmbed_mul_morphism
#print axioms hfp_from_epsilon_zero
#print axioms snap_unconditional
#print axioms snap_state_zp2_is_zero
#print axioms zpm_triangle
#print axioms both_fixed_points_exist

end PurityCheck
