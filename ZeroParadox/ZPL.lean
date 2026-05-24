import ZeroParadox.ZPK
import ZeroParadox.ZPB
import ZeroParadox.ZPE
import Mathlib.SetTheory.Ordinal.FixedPoint
import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic


/-!
# ZP-L: Incomputability Convergence

## Engineer's Take

Every layer in ZP (Zero Paradox) uses a standard mathematical tool — but inverted.
ZPB uses 2-adic numbers, where the standard question is "how does arithmetic behave
at finite primes?" ZP asks what happens when the 2-adic valuation is +∞ — that is,
at 0 itself. ZPC uses information theory, where the standard question is "what is
the minimum description length?" ZP asks what happens when the description length
is infinite. ZPK uses the recursion theorem, where the standard question is "what
programs can compute what functions?" ZP asks what the fixed point of self-application
is.

ZPL maps these structurally. The central result is the Cantor Normal Form bridge:
ordinals below ε₀ encode as finite binary sequences in ℤ_[2], and as the ordinal
tower ω, ω^ω, ω^(ω^ω), ... approaches ε₀, the 2-adic valuation of these encodings
goes to +∞ — meaning they converge to 0 = ⊥ in ℤ_[2]. The ZPE T-SNAP (⊥ → ε₀,
join c₀ c₁ = c₁) is this limit, viewed in reverse. Gentzen says this ordinal bounds
PA's proof-theoretic strength. That is not our claim. The target identification
(not yet a proved Lean theorem) is that ε₀ is the ordinal whose ZPB image is ⊥.

---

## Formal Overview

ZPL has four components:

(1) Axiom Footprint Convergence — the informal observation that Classical.choice
    appears at the non-constructive diagonal step in each of the four ZP layers
    listed in §I. Not a Lean proposition — evidenced by #print axioms.

(2) Roger Fixed-Point Stability — for any computable f, some code is behaviorally
    fixed by f (eval (f c) = eval c).
    In Lean scope. Follows from ZPK's roger_fixed_point_exists.

(3) Ordinal ε₀ tower — ε₀ = nfp (ω^·) 0 is the supremum of the tower
    ω, ω^ω, ω^(ω^ω), ...; it is a fixed point of α ↦ ω^α; it is the first
    such fixed point above 0. Fully in Lean scope via Mathlib ordinals.

(4) Cantor Normal Form Bridge — ordinals below ε₀ (NONote) encode into ℤ₂
    via their Cantor normal form; the tower converges to 0 in ℤ₂; ε₀
    corresponds to ⊥ under this encoding. The snap ⊥ → ε₀ is the ordinal
    tower limit, read from ZPB. Proof partially in Lean scope.

Axiom footprint: [propext, Classical.choice, Quot.sound] throughout.
The Classical.choice dependency is load-bearing — it is the formal non-constructivity.

---

## Dependencies

ZPK (§I): KleeneStructure, roger_fixed_point_exists, IsComputationalQuine
ZPB (§IV): 2-adic topology, PadicInt 2, 2-adic valuation
ZPE (§V): T-SNAP, MachinePhase, t_snap_machine -/

namespace ZeroParadox.ZPL

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPC
open ZeroParadox.ZPK
open ZeroParadox.ZPE
open Nat.Partrec Nat.Partrec.Code
open Ordinal

/-! ## § I. Axiom Footprint Convergence

Non-constructibility appears in four formal languages across the ZP framework.
Each proved theorem in each layer requires Classical.choice at the diagonal step
where a non-constructive choice is forced.

| Layer | Formal Language | Expression of non-constructibility |
|-------|----------------|--------------------------------------|
| ZPB   | Topology        | C3: no continuous path ⊥ → x ≠ ⊥   |
| ZPC   | Information     | L-INF: infinite surprisal at ⊥       |
| ZPJ/K | Set + Compute  | bot_self_mem (AFA); botCode (Kleene) |
| ZPI   | Algorithmic IT  | K(Sₙ|n)/|Sₙ| → 1; K uncomputable    |

The reason K is absent from Lean: its existence requires Classical.choice —
exactly the axiom Nat.Partrec.Code.fixed_point₂ already uses in ZPK. The
AFA/Kleene route reaches the same fixed-point structure via a provable path. -/

-- Axiom footprint evidence: all load-bearing ZPK theorems share this footprint.
-- The Classical.choice entry is the computational expression of the diagonal.
section AxiomFootprintEvidence

#print axioms ZeroParadox.ZPK.t_comp
#print axioms ZeroParadox.ZPK.da1_paths_unified
#print axioms ZeroParadox.ZPK.isComputationalQuine_undecidable
#print axioms ZeroParadox.ZPK.infinite_quine_family

end AxiomFootprintEvidence

/-! ## § II. Roger Fixed-Point Stability

Any computable transformation of a Code has a behavioral fixed point — a code c
such that eval (f c) = eval c. This is Roger's fixed-point theorem (Kleene's
second recursion theorem): the fixed-point structure is stable under any
computable transformation.

Note on scope: the ZPL architecture initially proposed that eval (f botCode) =
eval botCode for ALL computable f. This overclaims — botCode is one specific
Classical.choose witness and carries no special stability under arbitrary f.
The existential version is the correct formalization. -/

/-- Roger's fixed-point theorem (Kleene's second recursion theorem): for any
    computable transformation f, some code is behaviorally fixed by f.
    Proved as a wrapper around ZPK's roger_fixed_point_exists. -/
theorem roger_fixed_point_stability (f : Code → Code) (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  roger_fixed_point_exists f hf

/-! ## § III. Ordinal ε₀

The ordinal ε₀ is the smallest fixed point of α ↦ ω^α. It is the supremum
of the tower 0, 1, ω, ω^ω, ω^(ω^ω), ... Each stage is strictly below ε₀;
ε₀ is not reached by any finite iteration, only by the limit.

This is entirely within Lean scope via Mathlib's ordinal machinery:
- `Ordinal.epsilon 0` is Mathlib's definition of ε₀ (= veblen 1 0)
- `Ordinal.omega0_opow_epsilon`: ω^(ε_ o) = ε_ o (fixed point)
- `Ordinal.iterate_omega0_opow_lt_epsilon_zero`: all tower stages < ε₀
- `Ordinal.epsilon_zero_eq_nfp`: ε₀ = nfp (ω^·) 0
- `Ordinal.epsilon_zero_le_of_omega0_opow_le`: ε₀ is the least such fixed point

No sorry in this section. -/

/-- ε₀ as Mathlib's Ordinal.epsilon 0 (= nfp (ω^·) 0 = veblen 1 0).
    The fundamental sequence tower: stage n = (ω^·)^[n] 0. -/
noncomputable def epsilonZero : Ordinal := Ordinal.epsilon 0

/-- The fundamental sequence: stages of the ordinal tower converging to ε₀. -/
noncomputable def fundamentalSeq : ℕ → Ordinal :=
  fun n => (fun α => Ordinal.omega0 ^ α)^[n] 0

/-- ε₀ is a fixed point of α ↦ ω^α: ω^ε₀ = ε₀. -/
theorem epsilonZero_fixedPoint : Ordinal.omega0 ^ epsilonZero = epsilonZero :=
  Ordinal.omega0_opow_epsilon 0

/-- ε₀ is the nfp of ω^·. -/
theorem epsilonZero_eq_nfp :
    epsilonZero = Ordinal.nfp (fun α => Ordinal.omega0 ^ α) 0 := by
  unfold epsilonZero
  exact Ordinal.epsilon_zero_eq_nfp

/-- ε₀ is the supremum of the tower (ω^·)^[n] 0 for n : ℕ. -/
theorem epsilonZero_eq_iSup :
    epsilonZero = ⨆ n : ℕ, fundamentalSeq n := by
  simp only [fundamentalSeq, epsilonZero_eq_nfp]
  exact (Ordinal.iSup_iterate_eq_nfp _ _).symm

/-- Every finite stage of the tower is strictly below ε₀. -/
theorem epsilonZero_tower_lt (n : ℕ) : fundamentalSeq n < epsilonZero := by
  unfold fundamentalSeq epsilonZero
  exact Ordinal.iterate_omega0_opow_lt_epsilon_zero n

/-- The fundamental sequence is strictly monotone. -/
theorem fundamentalSeq_strictMono (n : ℕ) : fundamentalSeq n < fundamentalSeq (n + 1) := by
  induction n with
  | zero =>
    simp [fundamentalSeq, Ordinal.opow_zero]
  | succ n ih =>
    simp only [fundamentalSeq, Function.iterate_succ', Function.comp_def] at *
    exact (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono ih

/-- ε₀ is the LEAST fixed point of ω^· above 0:
    any fixed point b of ω^· satisfies ε₀ ≤ b. -/
theorem epsilonZero_le_fixedPoint {b : Ordinal} (hb : Ordinal.omega0 ^ b = b) :
    epsilonZero ≤ b := by
  unfold epsilonZero
  exact Ordinal.epsilon_zero_le_of_omega0_opow_le (le_of_eq hb)

/-- The explicit tower stages. -/
theorem tower_stage_zero : fundamentalSeq 0 = 0 := rfl
theorem tower_stage_one : fundamentalSeq 1 = 1 := by
  simp [fundamentalSeq, Ordinal.opow_zero]
theorem tower_stage_two : fundamentalSeq 2 = Ordinal.omega0 := by
  simp [fundamentalSeq, Ordinal.opow_zero, Ordinal.opow_one]

/-! ## § IV. Cantor Normal Form Bridge

Every ordinal below ε₀ has a unique Cantor normal form — a finite expression
  a₁ · ω^e₁ + a₂ · ω^e₂ + ... + aₙ · ω^eₙ
with e₁ > e₂ > ... > eₙ and aᵢ < ω. In Lean: `NONote` (the type of ordinals
below ε₀ in Cantor normal form from Mathlib.SetTheory.Ordinal.Notation).

The bridge: NONote → ℤ_[2] encodes each CNF term as a 2-adic integer where
the 2-adic valuation tracks the ordinal height. For `ω^e · n + a`:
  cnfToZp2(ω^e · n + a) = 2^(v₂(cnfToZp2(e)) + 1) · n + cnfToZp2(a)

This recursion ensures that the tower stages get valuation = stage index:
  cnfToZp2(ω^[0] 0) = 0              (valuation 0 by convention)
  cnfToZp2(ω^[1] 0) = 2^1 = 2       (valuation 1)
  cnfToZp2(ω^[2] 0) = 2^2 = 4       (valuation 2)
  cnfToZp2(ω^[n] 0) = 2^n           (valuation n)

As n → ∞, valuation → +∞, so the sequence converges to 0 = ⊥ in ℤ_[2].

The target identification is that ε₀ is the ordinal whose ZPB encoding is ⊥ —
the ZPE T-SNAP (⊥ → ε₀) is this limit, viewed in reverse.

The valuation and convergence results in this section are fully in Lean scope:
- `cnfToZp2` is defined by structural recursion on the underlying ONote
- `towerNONote n` lifts each fundamentalSeq n to a NONote via NONote.oadd
- The valuation formula is proved by induction using PadicInt.valuation_pow -/

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

-- Simp lemma: repr of NONote.oadd unfolds to the ONote.repr equation.
private theorem repr_oadd (e : NONote) (n : ℕ+) (a : NONote) (h : NONote.below a e) :
    NONote.repr (NONote.oadd e n a h) =
    Ordinal.omega0 ^ NONote.repr e * ↑n + NONote.repr a := rfl

-- The encoding function on the underlying ONote (ignores the NF side-condition).
-- Structural recursion on ONote avoids NONote subtype termination issues.
private noncomputable def cnfToZp2Aux : ONote → ℤ_[2]
  | ONote.zero => 0
  | ONote.oadd e n a =>
      (2 : ℤ_[2]) ^ ((cnfToZp2Aux e).valuation + 1) * (n : ℤ_[2]) + cnfToZp2Aux a

/-- Encoding ordinals below ε₀ into ℤ_[2] via the Cantor normal form structure.
    Base: 0 ↦ 0. Recursive: (ω^e · n + a) ↦ 2^(v₂(e_val)+1) · n + a_val.
    Valuation of the n-th tower stage equals n (proved below). -/
noncomputable def cnfToZp2 (α : NONote) : ℤ_[2] := cnfToZp2Aux α.1

-- Definitional reduction lemmas (all rfl).
@[simp] private theorem cnfToZp2Aux_zero : cnfToZp2Aux ONote.zero = 0 := rfl
@[simp] theorem cnfToZp2_zero : cnfToZp2 0 = 0 := rfl

private theorem cnfToZp2_oadd (e : NONote) (n : ℕ+) (a : NONote) (h : NONote.below a e) :
    cnfToZp2 (NONote.oadd e n a h) =
    (2 : ℤ_[2]) ^ ((cnfToZp2 e).valuation + 1) * (n : ℤ_[2]) + cnfToZp2 a := rfl

/-- The n-th tower stage as a `NONote` (ordinal below ε₀).
    towerNONote 0 = 0; towerNONote (n+1) = ω^(towerNONote n) · 1 + 0.
    The below-condition is NFBelow.zero: 0 is below any bound. -/
noncomputable def towerNONote : ℕ → NONote
  | 0 => 0
  | n + 1 => NONote.oadd (towerNONote n) 1 0 ONote.NFBelow.zero

/-- The NONote tower stages represent the ordinal fundamental sequence. -/
theorem towerNONote_repr (n : ℕ) : NONote.repr (towerNONote n) = fundamentalSeq n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hunfold : towerNONote (n + 1) = NONote.oadd (towerNONote n) 1 0 ONote.NFBelow.zero := rfl
    have hzero : NONote.repr (0 : NONote) = 0 := rfl
    -- ↑(1 : ℕ+) : Ordinal needs norm_cast (coercion path differs from Nat.cast_one).
    have hcast : (↑(1 : ℕ+) : Ordinal) = 1 := by norm_cast
    -- fundamentalSeq (n+1) = ω^(fundamentalSeq n) by Function.iterate_succ' unfolding.
    have hfund : fundamentalSeq (n + 1) = Ordinal.omega0 ^ fundamentalSeq n := by
      simp only [fundamentalSeq, Function.iterate_succ', Function.comp]
    rw [hunfold, repr_oadd, ih, hzero, hcast, mul_one, add_zero, ← hfund]

/-- The valuation of cnfToZp2 at the n-th tower stage equals n. -/
theorem cnfToZp2_tower_valuation (n : ℕ) : (cnfToZp2 (towerNONote n)).valuation = n := by
  induction n with
  | zero => simp [towerNONote, cnfToZp2, cnfToZp2Aux]
  | succ n ih =>
    have hunfold : towerNONote (n + 1) = NONote.oadd (towerNONote n) 1 0 ONote.NFBelow.zero := rfl
    -- Similarly, norm_cast handles ↑(1 : ℕ+) : ℤ_[2] = 1.
    have hcast : ((1 : ℕ+) : ℤ_[2]) = 1 := by norm_cast
    have hstep : cnfToZp2 (towerNONote (n + 1)) = (2 : ℤ_[2]) ^ (n + 1) := by
      rw [hunfold, cnfToZp2_oadd, ih, cnfToZp2_zero, hcast, mul_one, add_zero]
    rw [hstep, PadicInt.valuation_pow]
    -- (2 : ℤ_[2]) is a numeral; valuation_p expects the cast form (↑p : ℤ_[p]).
    -- Nat.cast_ofNat converts the numeral to cast form so valuation_p fires.
    have hval : (2 : ℤ_[2]).valuation = 1 := by
      rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm]
      exact PadicInt.valuation_p
    simp [hval]

/-- The 2-adic valuation of cnfToZp2 is unbounded: for every k there is an ordinal
    below ε₀ whose encoding has valuation ≥ k. This is the valuation-growth property. -/
theorem cnfToZp2_valuation_unbounded :
    ∀ k : ℕ, ∃ α : NONote, k ≤ (cnfToZp2 α).valuation := fun k =>
  ⟨towerNONote k, (cnfToZp2_tower_valuation k).symm ▸ le_refl k⟩

/-- The tower converges to 0 in ℤ_[2]: for any bound k, all sufficiently late stages
    have valuation ≥ k (so norm ≤ 2^(-k) → 0). -/
theorem fundamentalSeq_zp2_converges :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      ∀ α : NONote, NONote.repr α = fundamentalSeq n →
        k ≤ (cnfToZp2 α).valuation := by
  intro k
  refine ⟨k, fun n hn α hα => ?_⟩
  have hα_eq : α = towerNONote n := by
    apply Subtype.ext
    exact ONote.repr_inj.mp (by simpa [NONote.repr] using hα.trans (towerNONote_repr n).symm)
  rw [hα_eq, cnfToZp2_tower_valuation]
  exact hn

-- Explicit value: towerNONote (n+1) encodes as 2^(n+1) in ℤ_[2].
-- Follows from cnfToZp2_tower_valuation via the oadd recursion.
private theorem cnfToZp2_tower_explicit (n : ℕ) :
    cnfToZp2 (towerNONote (n + 1)) = (2 : ℤ_[2]) ^ (n + 1) := by
  have hunfold : towerNONote (n + 1) = NONote.oadd (towerNONote n) 1 0 ONote.NFBelow.zero := rfl
  have hcast : ((1 : ℕ+) : ℤ_[2]) = 1 := by norm_cast
  rw [hunfold, cnfToZp2_oadd, cnfToZp2_tower_valuation, cnfToZp2_zero, hcast, mul_one, add_zero]

/-- The tower encodings converge to 0 = ⊥ in ℤ_[2].
    Each stage cnfToZp2(towerNONote (n+1)) = 2^(n+1) in ℤ_[2], so its 2-adic norm is
    ‖2‖^(n+1) = (1/2)^(n+1) → 0. This is the zero-infinity identification in Lean:
    the ordinal tower limit maps to ⊥ in ℤ_[2]. -/
theorem tower_converges_to_zero :
    Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h2lt : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm, PadicInt.norm_p]
    norm_num
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε h2lt
  refine ⟨N + 1, fun n hn => ?_⟩
  simp only [dist_zero_right]
  rcases n with _ | n
  · exact absurd hn (by omega)
  · rw [cnfToZp2_tower_explicit, norm_pow]
    exact (pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt h2lt) (by omega : N ≤ n + 1)).trans_lt hN

/-! ## § V. Ordinal Tower Limit and ZPB Pre-image

What this does NOT claim:
  - Gentzen's theorem: that ε₀ is the proof-theoretic ordinal of PA (not claimed)
  - Any statement about formal provability in PA
  - A "solution" to the continuum hypothesis or other independent questions
  - Anything outside the structural identification of the snap with the ordinal limit

What is proved here (§ III + § IV + tower_converges_to_zero):
  - Ordinal: ε₀ = sup{(ω^·)^[n] 0 | n : ℕ}, every finite stage strictly below ε₀
  - ZPB: cnfToZp2(towerNONote n) = 2^n in ℤ_[2]; norm = ‖2‖^n → 0, so the
    tower encodings converge to 0 = ⊥ in ℤ_[2] (tower_converges_to_zero)

The remaining gap: connecting ZPE's MachinePhase element c₁ to the ordinal
epsilonZero via a type bridge. The ordinal and ZPB sides are fully proved.
The identification requires a morphism Ordinal → MachinePhase, not Gentzen. -/

/-- Tower-stage bound and fixed-point: every finite stage of the ε₀ tower is
    strictly below ε₀, and ω^ε₀ = ε₀. The ZPB encoding identification
    (ε₀ maps to ⊥) is the remaining gap in § IV. -/
theorem zpe_snap_ordinal_correspondence :
    ∀ n : ℕ, fundamentalSeq n < epsilonZero ∧
    Ordinal.omega0 ^ epsilonZero = epsilonZero :=
  fun n => ⟨epsilonZero_tower_lt n, epsilonZero_fixedPoint⟩

/-- Tower-stage bound: every finite stage of the ε₀ fundamental sequence is
    strictly below ε₀. This is the proved ordinal component of the ZPB bridge;
    the structural correspondence between epsilonZero and ZPE's c₁ is the
    gap requiring the CNF encoding identification from § IV. -/
theorem epsilonZero_tower_bound :
    ∀ n : ℕ, fundamentalSeq n < epsilonZero := fun n => epsilonZero_tower_lt n

/-- The c₁-ε₀ snap identification: there exists a map Ordinal → MachinePhase that sends
    every finite tower stage to c₀ (pre-snap) and ε₀ itself to c₁ (post-snap).

    Witness: φ α = if α < ε₀ then c₀ else c₁. This is the structural snap boundary —
    all ordinals strictly below ε₀ map to c₀; ε₀ and beyond map to c₁. The
    ∀ n condition pins the boundary at ε₀: no finite stage triggers the snap (each
    fundamentalSeq n < ε₀ by epsilonZero_tower_lt), while ε₀ itself does.

    The stronger structural claim — an order-preserving morphism (Ordinal →o MachinePhase)
    compatible with the CNF→ℤ_[2] encoding — remains outside Lean scope: no type bridge
    between Ordinal and MachinePhase is defined in this library. -/
theorem c1_epsilon_zero_identification :
    ∃ (φ : Ordinal → MachinePhase),
      (∀ n : ℕ, φ (fundamentalSeq n) = c₀) ∧ φ epsilonZero = c₁ :=
  ⟨fun α => if α < epsilonZero then c₀ else c₁,
   fun n => if_pos (epsilonZero_tower_lt n),
   if_neg (lt_irrefl epsilonZero)⟩

end ZeroParadox.ZPL

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPL

-- § III: fully proved
#print axioms epsilonZero_fixedPoint
#print axioms epsilonZero_eq_iSup
#print axioms epsilonZero_tower_lt
#print axioms epsilonZero_le_fixedPoint
#print axioms tower_stage_zero
#print axioms tower_stage_one
#print axioms tower_stage_two
#print axioms fundamentalSeq_strictMono
-- § IV: fully proved
#print axioms towerNONote_repr
#print axioms cnfToZp2_tower_valuation
#print axioms cnfToZp2_valuation_unbounded
#print axioms fundamentalSeq_zp2_converges
-- § II: proved (wrapper around roger_fixed_point_exists)
#print axioms roger_fixed_point_stability
-- § IV: tower_converges_to_zero (proved — zero-infinity identification)
#print axioms tower_converges_to_zero
-- § V: proved
#print axioms zpe_snap_ordinal_correspondence
#print axioms epsilonZero_tower_bound
-- § V: proved — structural snap boundary (all stages < ε₀ map to c₀; ε₀ maps to c₁)
#print axioms c1_epsilon_zero_identification

end PurityCheck
