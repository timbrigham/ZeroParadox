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

-- TODO: Engineer's Take section to be written by Tim in his own voice.

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
    via their Cantor normal form; as the tower stages approach ε₀, their encodings
    converge to 0 = ⊥ in ℤ₂. The identification of these two limits is the
    remaining gap. Proof partially in Lean scope.

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
    ‖2‖^(n+1) = (1/2)^(n+1) → 0. -/
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
  - That ε₀ is the UNIQUE minimal snap boundary: snap_threshold_is_epsilon_zero
    shows no ordinal below ε₀ works (for maps satisfying the stated hypotheses),
    but does not rule out maps satisfying those hypotheses that snap at some ordinal
    strictly above ε₀
  - That the snap threshold result applies to all maps Ordinal → MachinePhase,
    regardless of the monotonicity and tower-alignment hypotheses

What is proved here (§ III + § IV + §V):
  - Ordinal: ε₀ = sup{(ω^·)^[n] 0 | n : ℕ}, every finite stage strictly below ε₀
  - ZPB: cnfToZp2(towerNONote n).valuation = n; for n ≥ 1, cnfToZp2(towerNONote n) = 2^n
    in ℤ_[2]; norm = ‖2‖^n → 0, so the tower encodings converge to 0 = ⊥ in ℤ_[2]
    (tower_converges_to_zero)
  - Cofinality: the fundamental sequence is cofinal in ε₀ — for any α < ε₀,
    some tower stage exceeds α (fundamentalSeq_cofinal)
  - Snap lower bound: any order-non-decreasing φ that maps all tower stages to c₀
    maps every ordinal below ε₀ to c₀ (snap_threshold_is_epsilon_zero). This is a
    lower bound on the snap threshold, not a uniqueness result. A witness snapping
    exactly at ε₀ is provided by c1_epsilon_zero_identification.

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

/-- Snap boundary threshold: there exists a map Ordinal → MachinePhase that sends
    every finite tower stage to c₀ and ε₀ itself to c₁.

    Witness: φ α = if α < ε₀ then c₀ else c₁. Every finite tower stage satisfies
    fundamentalSeq n < ε₀ (epsilonZero_tower_lt), so maps to c₀. ε₀ itself fails
    the strict inequality (lt_irrefl), so maps to c₁.

    The stronger structural claim — an order-preserving morphism (Ordinal →o MachinePhase)
    compatible with the CNF→ℤ_[2] encoding — remains outside Lean scope: no type bridge
    between Ordinal and MachinePhase is defined in this library. -/
theorem c1_epsilon_zero_identification :
    ∃ (φ : Ordinal → MachinePhase),
      (∀ n : ℕ, φ (fundamentalSeq n) = c₀) ∧ φ epsilonZero = c₁ :=
  ⟨fun α => if α < epsilonZero then c₀ else c₁,
   fun n => if_pos (epsilonZero_tower_lt n),
   if_neg (lt_irrefl epsilonZero)⟩

/-- The fundamental sequence is cofinal in ε₀: for any ordinal below ε₀,
    some tower stage exceeds it.
    Proof: ε₀ = nfp (ω^·) 0 (epsilonZero_eq_nfp), and the Mathlib lemma
    `lt_nfp_iff` gives a < nfp f b ↔ ∃ n, a < f^[n] b. -/
theorem fundamentalSeq_cofinal {α : Ordinal} (hα : α < epsilonZero) :
    ∃ n : ℕ, α < fundamentalSeq n := by
  rw [epsilonZero_eq_nfp, lt_nfp_iff] at hα
  simpa [fundamentalSeq] using hα

/-- Lower bound on snap threshold: for any map φ : Ordinal → MachinePhase satisfying
    (a) hmono: φ is order-non-decreasing (∀ α ≤ β, φ α ≤ φ β in MachinePhase, expressed
        via the ZPSemilattice join condition join (φ α) (φ β) = φ β), and
    (b) h0: every tower stage maps to c₀,
    every ordinal strictly below ε₀ maps to c₀.

    Proof: cofinality (fundamentalSeq_cofinal) gives a tower stage n above any α < ε₀;
    hmono gives φ α ≤ φ (fundamentalSeq n); h0 gives φ (fundamentalSeq n) = c₀;
    since c₀ = ⊥ is the bottom of MachinePhase, φ α = c₀.

    Note: this is a lower bound result — it shows no ordinal below ε₀ is a snap point
    for maps satisfying (a) and (b). It does not show ε₀ is the unique minimal snap
    threshold or that all such maps snap at ε₀ rather than later.
    c1_epsilon_zero_identification provides a witness (one specific φ) that snaps
    exactly at ε₀. -/
theorem snap_threshold_is_epsilon_zero
    (φ : Ordinal → MachinePhase)
    (hmono : ∀ α β : Ordinal, α ≤ β → join (φ α) (φ β) = φ β)
    (h0 : ∀ n : ℕ, φ (fundamentalSeq n) = c₀) :
    ∀ α : Ordinal, α < epsilonZero → φ α = c₀ := by
  intro α hα
  obtain ⟨n, hn⟩ := fundamentalSeq_cofinal hα
  have hle : join (φ α) (φ (fundamentalSeq n)) = φ (fundamentalSeq n) :=
    hmono α (fundamentalSeq n) hn.le
  rw [h0 n] at hle
  -- hle : join (φ α) c₀ = c₀
  -- join (φ α) c₀ = φ α since c₀ = bot (both cases of MachinePhase reduce by rfl)
  have hjoin : join (φ α) (c₀ : MachinePhase) = φ α := by cases (φ α) <;> rfl
  exact hjoin.symm.trans hle

/-! ## § VI. Kleene-Ordinal Fixed-Point Bridge

The ordinal fixed-point structure (ε₀ = nfp (ω^·) 0, ω^ε₀ = ε₀) and the computational
fixed-point structure (Kleene's recursion theorem, roger_fixed_point_stability) both require
Classical.choice at their non-constructive step — parallel structure, not a proved isomorphism.
This is the content of §I Axiom Footprint Convergence.

The hypothesis
  hfp : ∀ α, ω^α = α → φ α = c₁
encodes that ordinal fixed points of ω^· (the ordinal analogues of Kleene fixed points)
map to the snap state c₁. Under this hypothesis, combined with monotonicity (hmono) and
tower alignment (h0), the snap is forced to occur at ε₀ as the minimal threshold:
  - every ordinal below ε₀ maps to c₀ (snap_threshold_is_epsilon_zero)
  - ε₀ maps to c₁ (epsilonZero_fixedPoint + hfp)
  - ε₀ is the minimal ordinal assigned c₁ (from the two above)

The computational side — that the snap MUST occur — is proved in ZPE (T-SNAP). The bridge
here is structural: IF maps aligned with the fixed-point structure snap at fixed points,
THEN ε₀ is the minimal snap threshold (no snap before ε₀, and φ ε₀ = c₁). -/

/-- ε₀ is the minimal snap threshold: for any map φ : Ordinal → MachinePhase satisfying
    (a) hmono: φ is order-non-decreasing (join (φ α) (φ β) = φ β for α ≤ β),
    (b) h0: every tower stage maps to c₀,
    (c) hfp: every fixed point of ω^· maps to c₁,
    φ ε₀ = c₁ AND no ordinal below ε₀ maps to c₁.

    This is the two-sided result. The lower bound (no snap before ε₀) comes from
    snap_threshold_is_epsilon_zero. The snap at ε₀ comes from hfp applied to
    epsilonZero_fixedPoint. Together they establish ε₀ as the minimal snap threshold:
    φ assigns c₁ first at ε₀, not before.
    (Note: "minimal" not "unique" — a map satisfying these hypotheses could also assign c₁
    to ordinals above ε₀; what is ruled out is any snap strictly before ε₀.) -/
theorem snap_exactly_at_epsilon_zero
    (φ : Ordinal → MachinePhase)
    (hmono : ∀ α β : Ordinal, α ≤ β → join (φ α) (φ β) = φ β)
    (h0 : ∀ n : ℕ, φ (fundamentalSeq n) = c₀)
    (hfp : ∀ α : Ordinal, Ordinal.omega0 ^ α = α → φ α = c₁) :
    φ epsilonZero = c₁ ∧ ∀ α : Ordinal, φ α = c₁ → epsilonZero ≤ α := by
  constructor
  · exact hfp epsilonZero epsilonZero_fixedPoint
  · intro α hα
    by_contra h
    push_neg at h
    have hc0 : φ α = c₀ := snap_threshold_is_epsilon_zero φ hmono h0 α h
    rw [hc0] at hα
    exact absurd hα (by simp [c₀, c₁])

/-- A canonical witness map satisfying all four ordinal-side bridge properties.
    Witness: φ α = if α < ε₀ then c₀ else c₁.
    This map: assigns c₀ to all tower stages; assigns c₁ to all fixed points of ω^·
    (since all such α satisfy ε₀ ≤ α by epsilonZero_le_fixedPoint); assigns c₁ to ε₀
    (since ε₀ is not strictly less than itself); and ε₀ is its minimal c₁ assignment.
    Note: the theorem name refers to the informal §VI conceptual parallel between Kleene
    recursion fixed points and ordinal fixed points of ω^·; no Kleene-side content
    (Code, eval) appears in this theorem. The theorem is purely ordinal. -/
theorem kleene_ordinal_snap_bridge :
    ∃ (φ : Ordinal → MachinePhase),
      (∀ n : ℕ, φ (fundamentalSeq n) = c₀) ∧
      (∀ α : Ordinal, Ordinal.omega0 ^ α = α → φ α = c₁) ∧
      (φ epsilonZero = c₁) ∧
      (∀ α : Ordinal, φ α = c₁ → epsilonZero ≤ α) := by
  refine ⟨fun α => if α < epsilonZero then c₀ else c₁, ?_, ?_, ?_, ?_⟩
  · intro n; exact if_pos (epsilonZero_tower_lt n)
  · intro α hfp; exact if_neg (not_lt.mpr (epsilonZero_le_fixedPoint hfp))
  · exact if_neg (lt_irrefl epsilonZero)
  · intro α hα
    by_contra h
    push_neg at h
    simp only [if_pos h] at hα
    exact absurd hα (by simp [c₀, c₁])

/-! ## § VII. Canonical Snap Map — Full Closure

The canonical threshold map φ α = if α < ε₀ then c₀ else c₁ satisfies ALL three
conditions of snap_exactly_at_epsilon_zero (hmono, h0, hfp). This makes the snap
identification unconditional for this specific map — no free hypotheses remain.

The three conditions:
  (hmono) φ is order-non-decreasing — proved here as snap_map_mono
  (h0)    every tower stage maps to c₀ — from kleene_ordinal_snap_bridge
  (hfp)   every fixed point of ω^· maps to c₁ — from kleene_ordinal_snap_bridge

snap_zp2_correspondence then records both sides together: every stage of the tower is
below ε₀ in ordinals, the canonical map assigns c₀ to those stages and c₁ to ε₀,
and the 2-adic encodings converge to 0. These are independent proved facts about the
same tower sequence — not a formal structural isomorphism between ordinal and 2-adic limits. -/

/-- The canonical snap map is order-non-decreasing in the ZPSemilattice sense.
    For α ≤ β, join (φ α) (φ β) = φ β where φ = if · < ε₀ then c₀ else c₁.
    Proof: four cases from the two boolean conditions (α vs ε₀, β vs ε₀),
    with the (α ≥ ε₀, β < ε₀) case contradicting α ≤ β. Each live case is rfl
    from the MachinePhase join definition. -/
theorem snap_map_mono :
    ∀ α β : Ordinal, α ≤ β →
      join (if α < epsilonZero then (c₀ : MachinePhase) else c₁)
           (if β < epsilonZero then c₀ else c₁) =
      if β < epsilonZero then c₀ else c₁ := by
  intro α β hab
  by_cases hα : α < epsilonZero <;> by_cases hβ : β < epsilonZero
  · simp only [if_pos hα, if_pos hβ]; rfl   -- join c₀ c₀ = c₀
  · simp only [if_pos hα, if_neg hβ]; rfl   -- join c₀ c₁ = c₁
  · exact absurd (lt_of_le_of_lt hab hβ) hα  -- α ≥ ε₀ and α ≤ β < ε₀: impossible
  · simp only [if_neg hα, if_neg hβ]; rfl   -- join c₁ c₁ = c₁

/-- There exists a map satisfying all five conditions simultaneously: order-non-decreasing,
    tower-aligned (every stage maps to c₀), fixed-point-respecting (every fixed point of ω^·
    maps to c₁), snapping at ε₀ (φ ε₀ = c₁), and minimal (ε₀ ≤ any c₁-assigned ordinal).
    All five are verified for the explicit witness φ α = if α < ε₀ then c₀ else c₁,
    with no free hypotheses remaining for this witness.
    Monotonicity (hmono) comes from snap_map_mono. The other four conditions are direct
    consequences of ε₀'s ordinal properties. -/
theorem epsilon_zero_snap_canonical :
    ∃ (φ : Ordinal → MachinePhase),
      (∀ α β : Ordinal, α ≤ β → join (φ α) (φ β) = φ β) ∧
      (∀ n : ℕ, φ (fundamentalSeq n) = c₀) ∧
      (∀ α : Ordinal, Ordinal.omega0 ^ α = α → φ α = c₁) ∧
      φ epsilonZero = c₁ ∧
      ∀ α : Ordinal, φ α = c₁ → epsilonZero ≤ α := by
  refine ⟨fun α => if α < epsilonZero then c₀ else c₁, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β hab; exact snap_map_mono α β hab
  · intro n; exact if_pos (epsilonZero_tower_lt n)
  · intro α hfp; exact if_neg (not_lt.mpr (epsilonZero_le_fixedPoint hfp))
  · exact if_neg (lt_irrefl epsilonZero)
  · intro α hα
    by_contra h
    push_neg at h
    simp only [if_pos h] at hα
    exact absurd hα (by simp [c₀, c₁])

/-- Four independent facts about the same tower sequence, stated together:
    (i)   Every tower stage is strictly below ε₀ in ordinals (epsilonZero_tower_lt)
    (ii)  The canonical map sends every tower stage to c₀ (pre-snap zone)
    (iii) The 2-adic encodings of the tower converge to 0 = ⊥ (tower_converges_to_zero)
    (iv)  The canonical map sends ε₀ to c₁ (the snap)
    All four are provable from already-established theorems. The theorem records that the
    same tower sequence witnesses both the ordinal approach to ε₀ and the 2-adic approach
    to 0. The full structural identification (ε₀ ↔ ⊥ via a type bridge) remains outside
    Lean scope — see §V. -/
theorem snap_zp2_correspondence :
    (∀ n : ℕ, fundamentalSeq n < epsilonZero) ∧
    (∀ n : ℕ, (fun α : Ordinal =>
      if α < epsilonZero then (c₀ : MachinePhase) else c₁) (fundamentalSeq n) = c₀) ∧
    Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0) ∧
    (fun α : Ordinal =>
      if α < epsilonZero then (c₀ : MachinePhase) else c₁) epsilonZero = c₁ :=
  ⟨epsilonZero_tower_lt,
   fun n => if_pos (epsilonZero_tower_lt n),
   tower_converges_to_zero,
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
-- § IV: tower_converges_to_zero (proved — tower encodings converge to ⊥ in ℤ_[2])
#print axioms tower_converges_to_zero
-- § V: proved
#print axioms zpe_snap_ordinal_correspondence
#print axioms epsilonZero_tower_bound
-- § V: proved — structural snap boundary (all stages < ε₀ map to c₀; ε₀ maps to c₁)
#print axioms c1_epsilon_zero_identification
-- § V: proved — tower cofinality in ε₀
#print axioms fundamentalSeq_cofinal
-- § V: proved — for any order-non-decreasing φ mapping all tower stages to c₀,
--      every ordinal below ε₀ also maps to c₀ (lower bound on snap threshold)
#print axioms snap_threshold_is_epsilon_zero
-- § VI: proved — ε₀ is the minimal snap threshold for any monotone, tower-aligned,
--      fixed-point-respecting map (snap is forced at ε₀, not before)
#print axioms snap_exactly_at_epsilon_zero
-- § VI: proved — canonical witness map exhibiting the bridge properties
#print axioms kleene_ordinal_snap_bridge
-- § VII: proved — canonical map is order-non-decreasing (fills hmono gap)
#print axioms snap_map_mono
-- § VII: proved — snap unconditionally forced at ε₀ for the canonical map
#print axioms epsilon_zero_snap_canonical
-- § VII: proved — two-sided correspondence: ordinal and 2-adic witnesses to the snap boundary
#print axioms snap_zp2_correspondence

end PurityCheck
