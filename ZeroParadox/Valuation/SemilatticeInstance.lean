import ZeroParadox.Order.Snap
import ZeroParadox.Computability.Kleene
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# ZP-I: Inside Zero

## Engineer's Take

Everything up to this point has been from the perspective of one bottom reaching
upward. The chain approaches zero by continuing forward and not by reversing,
because in the 2-adic metric climbing higher in the lattice is the same motion as
landing closer to zero.

This file took five rounds of review before I trusted it, and what those rounds
mostly did was take away things I thought the theorem used. Writing down what it
actually consumes is the useful part, so that is what the rest of this is.

Three hypotheses and one identity reach the norm bound. The chain has to climb
strictly at every index, which is IsStrictStateSequence. The 2-adic valuation has
to track that climb, which is IsDepthChain. The chain has to be nowhere zero, or
the norm and the valuation are not related at all. And the proof leans on the norm
and the valuation being inverse to each other, 2 to the minus v, which comes from
ZP-B's valuation construction. Remove any of them and it does not close.

Four other things were credited here and do no work. Having no top element only
says a next state exists, and the constant sequence in the naturals satisfies it
while never moving. No subtraction holds in the one point lattice, where there is
nowhere to go at all, so it is not what leaves the chain room. T3 is monotone and
not strict, so it permits standing still, and standing still breaks the bound at
the first step. Completeness of the 2-adics is never used, because we hand the
limit over as zero rather than going looking for one, and completeness is what the
other direction needs.

The way we settled each of those was to build the thing that should not exist and
watch it compile. A chain that satisfies every condition we cited and still fails
the conclusion is not an argument, it is a counterexample, and it ends the
discussion. That method found errors that four rounds of careful reading had walked
straight past, including two I introduced while fixing the round before.

IsDepthChain is the one I would point a reviewer at first. It is an interface
contract between two subsystems. The lattice says it moved, the 2-adics say their
valuation went up, and nothing derives that these are the same motion. We assert it.
Everything downstream inherits that assertion, and section Ib says so.

At the far end the same discipline applies. Convergence to zero is proved. That
anything filling the bottom role in a lattice is that lattice's bottom is proved, as
an implication. Reading the 2-adic limit as the thing filling that role is a
commitment, and the two do not live in the same type, so the condition is not even
statable of the limit. Calling what you arrive at a new bottom rather than the one
you started from is a further commitment, and in the one realization we can compute,
the arc returns to the same zero.

On the Classical.choice in the convergence proof, do not re-derive it here and do
not read a commitment into it. The framing is settled elsewhere and this file should
point rather than restate. AxiomProfile.lean is the home: the core is choice-free and
T-SNAP depends on no axioms at all, while choice appears in the realization layers,
mostly inherited from Mathlib. There is also a standing conjecture that the choice is
forced by the metric collapse rather than imposed by the library, and its two halves
are in different states. The snap half is resolved and incidental. The metric half has
a choice-free syntactic surrogate in SyntacticCollapse.lean, which is evidence and not
proof, because the bridge from the syntactic side to the 2-adic statement is not
verified. That file also already records what I went and measured again for myself,
which is that the choice arrives through Mathlib's instance packaging and can sit in a
single tactic call. Read it before repeating the experiment.

I defer to my AI assistant on how the internals are put together.

---

T-IZ proves convergence to 0 in Q₂; reading it as an occupant of the ⊥ role, and that occupant as
a successor null, are further COMMITMENTS. Overview and fences: `SemilatticeInstance.md`.

Key results: t_iz_cauchy (topological core; inherits Classical.choice from Mathlib analysis), t_iz_complete (all steps formal).
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice
open ZeroParadox ZeroParadox

/-! ## I. Cauchy Convergence — Topological Core of T-IZ

The 2-adic norm satisfies ‖x‖₂ = 2^{-v₂(x)}. An ascending chain with v₂(Sₙ) → ∞
therefore has ‖Sₙ‖₂ → 0, and in a normed group norm → 0 gives convergence to 0.
⚠ COMPLETENESS IS NOT CONSUMED: the limit is exhibited as 0, never obtained from a
Cauchy criterion. Completeness is what the CONVERSE needs (Cauchy ⇒ a limit exists),
and T-IZ never takes that direction.

These three theorems are the entire topological content of T-IZ. -/

/-- Norms bounded by the geometric sequence (2⁻¹)ⁿ tend to 0.
    Formal content of "v₂(Sₙ) ≥ n": the 2-adic norm ‖Sₙ‖₂ = 2^{-v₂(Sₙ)} ≤ 2^{-n} → 0.
    Proof: squeeze between 0 and the geometric bound, both of which tend to 0. -/
theorem t_iz_norm_tendsto_zero
    (S : ℕ → Q₂)
    (h_bound : ∀ n : ℕ, ‖S n‖ ≤ (2⁻¹ : ℝ) ^ n) :
    Filter.Tendsto (fun n => ‖S n‖) Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun n => norm_nonneg _) h_bound
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- A sequence in Q₂ whose norms tend to 0 converges to 0.
    Follows from: in a normed group, ‖f n‖ → 0 iff f n → 0. -/
theorem t_iz_conv_zero
    (S : ℕ → Q₂)
    (h : Filter.Tendsto (fun n => ‖S n‖) Filter.atTop (nhds 0)) :
    Filter.Tendsto S Filter.atTop (nhds 0) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h

/-- T-IZ (Cauchy core): An ascending chain with v₂(Sₙ) ≥ n converges to 0 in Q₂.
    Not axiom-free: the proof inherits Classical.choice from Mathlib analysis (squeeze_zero,
    tendsto_zero_iff_norm_tendsto_zero). This is the topological
    half of T-IZ — the half that lives in pure analysis without AIT or ZF+AFA. -/
theorem t_iz_cauchy
    (S : ℕ → Q₂)
    (h_bound : ∀ n : ℕ, ‖S n‖ ≤ (2⁻¹ : ℝ) ^ n) :
    Filter.Tendsto S Filter.atTop (nhds 0) :=
  t_iz_conv_zero S (t_iz_norm_tendsto_zero S h_bound)

/-! ## Ia. Strict Ascent → Geometric Bound — Deriving h_bound from ZP-A Conditions

h_bound (∀ n, ‖Sₙ‖ ≤ (2⁻¹)ⁿ), a hypothesis of `t_iz_cauchy`, is proved here from:
  IsStrictStateSequence → a PROPER step at every index (T3 rides inside it)
  IsDepthChain          → the 2-adic valuation tracks the ℕ depth index
  Together → v₂(Sₙ) ≥ v₂(S₀) + n  →  ‖Sₙ‖₂ ≤ ‖S₀‖₂ · (2⁻¹)ⁿ

⚠ `HasNoTop` is NOT among these and appears in NO binder of this file: it is the order condition
making ascent available, never a premise here. Nor is it ZP-A's R1 (no-subtraction). Gauge: § Ib. -/

/-- Integer arithmetic: a strictly increasing ℤ-valued sequence satisfies v 0 + n ≤ v n.
    Proved by induction. No axioms beyond propext (from linarith). -/
private lemma int_strict_mono_ge (v : ℕ → ℤ)
    (h : ∀ n, v n < v (n + 1)) : ∀ n : ℕ, v 0 + (n : ℤ) ≤ v n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      push_cast
      linarith [h n]

/-- Strict valuation growth → geometric norm bound in Q₂.
    h_strict is the strict valuation growth condition. It can be derived from
    ZP-A axioms via h_strict_from_r1_t3 (§ Ib) given an IsDepthChain and
    IsStrictStateSequence — h_strict is no longer a bare assumption (R-IZ-A closed).
    From h_strict we derive ‖Sₙ‖₂ ≤ ‖S₀‖₂ · (2⁻¹)ⁿ — the h_bound for t_iz_cauchy. -/
theorem t_iz_r1_t3_geometric_bound
    (S : ℕ → Q₂)
    (hS : ∀ n, S n ≠ 0)
    (h_strict : ∀ n, (S n).valuation < (S (n + 1)).valuation) :
    ∀ n : ℕ, ‖S n‖ ≤ ‖S 0‖ * (2⁻¹ : ℝ) ^ n := by
  intro n
  have hval : (S 0).valuation + (n : ℤ) ≤ (S n).valuation :=
    int_strict_mono_ge (fun k => (S k).valuation) h_strict n
  rw [Padic.norm_eq_zpow_neg_valuation (hS n), Padic.norm_eq_zpow_neg_valuation (hS 0)]
  have h_ineq : -(S n).valuation ≤ -(S 0).valuation - (n : ℤ) := by linarith
  calc (2 : ℝ) ^ (-(S n).valuation)
      ≤ (2 : ℝ) ^ (-(S 0).valuation - (n : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_ineq
    _ = (2 : ℝ) ^ (-(S 0).valuation) * (2⁻¹ : ℝ) ^ n := by
          rw [show -(S 0).valuation - (n : ℤ) = -(S 0).valuation + (-(n : ℤ)) from by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          congr 1
          rw [zpow_neg (2 : ℝ), zpow_natCast]
          exact (inv_pow 2 n).symm

/-- "sup v₂(Sₙ) = ∞": a strictly increasing ℤ-sequence is unbounded above.

    Given h_strict (the Q₂ expression of a chain that actually ascends — `IsStrictStateSequence`
    is the hypothesis that supplies it),
    the 2-adic valuation has no ceiling. For any target K, some term Sₙ satisfies
    v₂(Sₙ) ≥ K.

    This is the formal content of proof obligation table row 3 ("sup v₂(S(n)) = ∞").
    Proof: int_strict_mono_ge gives (S 0).valuation + n ≤ (S n).valuation; take
    N = (K − v₀).toNat; then (S N).valuation ≥ v₀ + N ≥ K by integer arithmetic. -/
theorem t_iz_valuation_unbounded
    (S : ℕ → Q₂)
    (h_strict : ∀ n, (S n).valuation < (S (n + 1)).valuation) :
    ∀ K : ℤ, ∃ N : ℕ, K ≤ (S N).valuation := by
  intro K
  have hge : ∀ n : ℕ, (S 0).valuation + (n : ℤ) ≤ (S n).valuation :=
    int_strict_mono_ge (fun k => (S k).valuation) h_strict
  exact ⟨(K - (S 0).valuation).toNat, by have := hge (K - (S 0).valuation).toNat; omega⟩

/-! ## Ib. Formal Closure of R-IZ-A: h_strict from IsDepthChain + IsStrictStateSequence

Previously `h_strict` was a parameter in `t_iz_r1_t3_geometric_bound` (R-IZ-A gap):
the formal connection between ZP-A lattice axioms and strict valuation growth was absent.

Strategy: (ℕ, max, 0) is a ZPSemilattice (T3: max is monotone; `HasNoTop`: ℕ has no top).
A strict state sequence on ℕ yields strictly increasing depth indices.
A Q₂ chain whose valuations track those depths inherits `h_strict` from the abstract
lattice theorem — deriving it rather than assuming it. -/

/-- (ℕ, max, 0) is a ZPSemilattice. The induced partial order is the natural ≤ on ℕ.
    `HasNoTop`: ℕ has no top element (∀ n, n + 1 > n).
    T3: max(S n, α n) ≥ S n always, so state sequences are monotone. -/
instance natZPSemilattice_zpi : ZPSemilattice ℕ where
  join       := max
  bot        := 0
  join_assoc := fun x y z => by omega
  join_comm  := fun x y   => by omega
  join_idem  := fun x     => by omega
  bot_join   := fun x     => by omega

/-- `HasNoTop` holds for ℕ: every natural number has a strictly greater successor. -/
theorem nat_has_no_top : HasNoTop ℕ :=
  fun x => ⟨x + 1, by change max x (x + 1) = x + 1; omega, by omega⟩

/-- A strict state sequence on ℕ has strictly increasing values.
    Proof: T3 gives depths n ≤ depths (n+1); the strict condition gives ≠; hence <. -/
theorem nat_strict_of_strict_state_seq
    (depths : ℕ → ℕ) (h : IsStrictStateSequence depths) :
    ∀ n, depths n < depths (n + 1) := by
  intro n
  have hmono : le (depths n) (depths (n + 1)) :=
    state_sequence_monotone depths h.1 n
  have hle : depths n ≤ depths (n + 1) := by
    change max (depths n) (depths (n + 1)) = depths (n + 1) at hmono
    omega
  exact Nat.lt_of_le_of_ne hle (h.2 n)

/-- Depth chain: a Q₂ sequence whose 2-adic valuations track a ℕ depth index. -/
def IsDepthChain (S : ℕ → Q₂) (depths : ℕ → ℕ) : Prop :=
  ∀ n, (S n).valuation = (depths n : ℤ)

/-- h_strict from IsDepthChain + IsStrictStateSequence — formal closure of R-IZ-A.
    Given a Q₂ chain tracking a strict ℕ state sequence via depth valuations,
    strict valuation growth follows from ZP-A lattice axioms rather than being assumed.
    This is the theorem the outside observer identified as missing. -/
theorem h_strict_from_r1_t3
    (S : ℕ → Q₂) (depths : ℕ → ℕ)
    (h_depth : IsDepthChain S depths)
    (h_seq : IsStrictStateSequence depths) :
    ∀ n, (S n).valuation < (S (n + 1)).valuation := by
  intro n
  rw [h_depth n, h_depth (n + 1)]
  exact_mod_cast nat_strict_of_strict_state_seq depths h_seq n

/-! ### NO-GO gauge — no-top buys the POSSIBILITY of ascent, never its OCCURRENCE

`ℕ` has no top (`nat_has_no_top`), and the constant chain is a state sequence *in that same
lattice* which never moves. `HasNoTop` appears nowhere in the binders of `h_strict_from_r1_t3`
above; what that theorem consumes is `IsStrictStateSequence`. So no-top cannot be what drives
the valuation — it makes the next step AVAILABLE, and something else has to take it.
Only `nat_has_no_top` is carrier-specific — the stalling half is generic, and the SECOND example
below proves that rather than asserting it. Both anonymous, so neither owes a purity entry (DC-32). -/

example :
    HasNoTop ℕ ∧
    IsStateSequence (fun _ : ℕ => (0 : ℕ)) ∧
    ¬ IsStrictStateSequence (fun _ : ℕ => (0 : ℕ)) :=
  ⟨nat_has_no_top,
   ⟨fun _ => 0, fun _ => (join_idem 0).symm⟩,
   fun h => h.2 0 rfl⟩

example {L : Type*} [ZPSemilattice L] (x : L) :
    IsStateSequence (fun _ : ℕ => x) ∧ ¬ IsStrictStateSequence (fun _ : ℕ => x) :=
  ⟨⟨fun _ => x, fun _ => (join_idem x).symm⟩, fun h => h.2 0 rfl⟩

/-! ## II. Valuation-Complexity Bridge — SUPERSEDED

This section described the informal route: v₂(Sₙ) → ∞ ⟹ K(Sₙ|n)/|Sₙ| → 1 ⟹ DA-1 fires.
It was Outside Lean Scope because Kolmogorov complexity K is uncomputable and absent from Mathlib.

**This bridge is not needed for the Lean route.** The reason is narrower than it once read here:
step 4 of `t_iz_complete` is `IsQuineAtom (bot : L')`, discharged from `AFAStructure` fields alone,
so no Kolmogorov complexity enters the proof. It is NOT that ZP-K showed the two paths to be one
thing — `da1_paths_unified` is a *conjunction* of two witnesses, and ZP-K states explicitly that a
conjunction is not an identity and that the two sides cannot be equated in Lean (different types).
Reading the AFA/Kleene path and the K/AIT path as the same structural property is the framework's
interpretation, and it is not what retires this bridge.

Steps 2–6 of T-IZ are formalized in § III-B without computing Kolmogorov complexity. The K
bridge is bypassed, not shown closed, and is retained here as a record of the original
motivating argument. -/

/-! ## III. T-IZ — Inside Zero Theorem -/

/-- T-IZ: Every maximal ascending chain in Q₂ with unbounded 2-adic valuation
    converges to 0; reading that as generating its own successor null is the framework's.

    The theorem has six steps (see ZP-I PDF § III):
    (1) Cauchy convergence to 0: t_iz_cauchy — proved in § I.
    (2) Valuation-complexity bridge: outside Lean scope — see § II.
    (3) P₀ satisfied at limit: ZP-C D1 (informal; same route as DA-1 Path 3).
    (4) DA-1 fires: ZP-E (TrackedOutput formal core; Path 3 informal).
    (5) T-SNAP fires, generating ⊥': ZP-E t_snap_derived.
    (6) DA-2 licenses ⊥' as successor null: ZP-E da2_bottom_characterization.

    Steps (2)–(6) are formalized in § III-B without computing Kolmogorov complexity —
    see t_iz_complete. Step 2's K bridge is bypassed rather than shown closed: the
    remaining steps route through AFAStructure fields. -/
theorem t_inside_zero
    (S : ℕ → Q₂)
    (_h_start : S 0 ≠ 0)
    (h_bound : ∀ n : ℕ, ‖S n‖ ≤ (2⁻¹ : ℝ) ^ n) :
    Filter.Tendsto S Filter.atTop (nhds 0) :=
  -- _h_start: semantic guard — chain begins away from null (unused in convergence proof)
  -- h_bound: v₂(Sₙ) ≥ n — the ascending chain has unbounded valuation
  -- Complete formal statement: t_iz_complete (§ III-B) — all six steps formal.
  t_iz_cauchy S h_bound

/-! ## IV. Successor Null and Framework Closure -/

/-- DA-2 at the ordinal limit: any state satisfying the join-identity condition
    is the bottom element of its semilattice — the structural role of ⊥.
    ⚠ The role property is the HYPOTHESIS, never the conclusion, and this says nothing
    about Q₂: `ZPSemilattice ℚ_[2]` does not synthesize, so the join-identity is not
    statable of `0 : ℚ₂`. Nor is novelty (SnapCannotBe.lean:43). See CLAIMS.md's T-IZ row. -/
theorem t_iz_limit_is_new_null
    {L : Type*} [ZPSemilattice L]
    (terminal : L)
    (h_role : ∀ x : L, join terminal x = x) :
    terminal = bot :=
  (da2_bottom_characterization terminal).mp h_role

/-- C-T-IZ (Null Balance). `Statement:` a non-bottom state cannot satisfy the join-identity
    role — the role is EXCLUSIVE to ⊥, one direction, inside one semilattice.
    `Reading:` occupancy of that role by the 2-adic limit is a COMMITMENT, not a theorem —
    `ZPSemilattice ℚ_[2]` does not synthesize, so the condition is not statable of that limit;
    successor-hood is a further commitment (C-DA2). The additive balance is NOT carried here:
    a `ZPSemilattice` has `join` and `bot` and no additive inverse. See `SemilatticeInstance.md`. -/
theorem c_t_iz_null_balance
    {L : Type*} [ZPSemilattice L]
    (S : L)
    (h_not_bot : S ≠ bot) :
    ¬(∀ x : L, join S x = x) :=
  c_da2_novelty S h_not_bot

/-- T-IZ (C3 compatible): Cauchy sequence convergence and continuous-path irreversibility
    are distinct structures. C3 (ZP-B) closes every continuous path from x ≠ 0 to 0.
    T-IZ uses Cauchy sequence convergence — a sequence (Sₙ)_{n∈ℕ} tending to 0,
    not a continuous function [0,1] → Q₂. The two results do not conflict.
    Formal: c3_irreversible is literally applied here to show C3 holds without change. -/
theorem t_iz_c3_compatible :
    ∀ (x : Q₂), x ≠ 0 →
    ¬∃ γ : C(Set.Icc (0 : ℝ) 1, Q₂),
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = 0 :=
  ZeroParadox.c3_irreversible

/-! ## III-B. T-IZ (Formally Complete) — AFA/Kleene Path

The § II Kolmogorov bridge is not needed here: this route discharges step 4 from
`AFAStructure` fields and never computes K. That is a fact about this proof, not evidence
the AFA and K/AIT paths are one property — ZP-K's `da1_paths_unified` is a conjunction of
witnesses and fences the identity reading as a commitment.

`t_iz_complete` carries the four steps as a CONJUNCTION, not a chain; its type is the step
list. `ZPSemilattice ℚ_[2]` does not synthesize, so the role condition is not statable of the
2-adic limit — the two are distinct MEMBERS of the bottom family, not one object (MC-1). -/

/-- T-IZ: all four formal steps in one theorem — a CONJUNCTION, not a chain.
    L' carries a KleeneStructure; the terminal element's join-identity is a HYPOTHESIS
    (h_role), and NOTHING here relates that terminal to the Q₂ limit. Discharging it at an
    unrelated L' elaborates, which is what "not a chain" means. No K on this route. -/
theorem t_iz_complete
    (S : ℕ → Q₂)
    (h_bound : ∀ n : ℕ, ‖S n‖ ≤ (2⁻¹ : ℝ) ^ n)
    {L' : Type*} [ZPSemilattice L'] [ZeroParadox.KleeneStructure L']
    (terminal : L') (ε₀' : L')
    (h_role : ∀ x : L', join terminal x = x) :
    -- Step 1: chain converges to 0 in Q₂
    Filter.Tendsto S Filter.atTop (nhds 0) ∧
    -- Steps 3/6: terminal plays the ⊥ role, hence IS bot (DA-2); "successor" is the reading
    terminal = bot ∧
    -- Step 4: DA-1 fires at the successor null via AFA/Kleene — no K required
    ZeroParadox.IsQuineAtom (bot : L') ∧
    -- Step 5: T-SNAP fires from ⊥' to ε₀' (A4 = bot_join, definitional)
    join (bot : L') ε₀' = ε₀' :=
  ⟨t_iz_cauchy S h_bound,
   t_iz_limit_is_new_null terminal h_role,
   ZeroParadox.da1_computational,
   bot_join ε₀'⟩

/-- NO-GO gauge for `t_iz_complete`: it is a CONJUNCTION, not a chain.
    `terminal` is discharged at `MachinePhase` — ZP-C's TWO-ELEMENT type, with no
    relation whatever to the 2-adic sequence — while `S` is the constant `0` in `Q₂`.
    Both halves elaborate side by side, so the theorem carries NO link between the
    Cauchy limit and the ⊥ role. That link is a commitment, not a consequence. -/
example :
    Filter.Tendsto (fun _ : ℕ => (0 : Q₂)) Filter.atTop (nhds 0) ∧
    (bot : MachinePhase) = bot ∧
    ZeroParadox.IsQuineAtom (bot : MachinePhase) ∧
    join (bot : MachinePhase) bot = bot :=
  t_iz_complete (fun _ => (0 : Q₂))
    (fun n => by simp)
    bot bot bot_join

/-! ## III-C. Depth-Chain Bridge — Closing the strict-ascent → t_iz_complete Chain

An *optional transparency layer*: `t_iz_complete` (§ III-B) is formally complete without it.
It closes the one-factor gap between §Ib and `t_iz_complete`'s `h_bound` hypothesis —
`t_iz_r1_t3_geometric_bound` yields `‖Sₙ‖ ≤ ‖S₀‖ · (2⁻¹)ⁿ`, and `IsDepthChain` forces
`‖S₀‖₂ ≤ 1`, which absorbs the factor. Worked through in `SemilatticeInstance.md`. -/

/-- h_bound derived from ZP-A axioms via depth chain.
    Optional transparency lemma — t_iz_complete functions without it.
    `IsDepthChain` ties v₂(Sₙ) to a ℕ depth index; `IsStrictStateSequence` (the occurrence)
    gives strict growth; `depths 0 : ℕ` forces ‖S 0‖₂ ≤ 1, absorbing the S₀ factor. -/
theorem t_iz_h_bound_from_depth_chain
    (S : ℕ → Q₂) (depths : ℕ → ℕ)
    (hS : ∀ n, S n ≠ 0)
    (h_depth : IsDepthChain S depths)
    (h_seq : IsStrictStateSequence depths) :
    ∀ n : ℕ, ‖S n‖ ≤ (2⁻¹ : ℝ) ^ n := by
  have h_strict := h_strict_from_r1_t3 S depths h_depth h_seq
  have h_geom   := t_iz_r1_t3_geometric_bound S hS h_strict
  have h0_le_one : ‖S 0‖ ≤ 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation (hS 0), h_depth 0]
    calc (2 : ℝ) ^ (-(depths 0 : ℤ))
        ≤ (2 : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1                  := zpow_zero _
  intro n
  calc ‖S n‖ ≤ ‖S 0‖ * (2⁻¹ : ℝ) ^ n := h_geom n
    _ ≤ 1    * (2⁻¹ : ℝ) ^ n          := mul_le_mul_of_nonneg_right h0_le_one (by positivity)
    _ = (2⁻¹ : ℝ) ^ n                 := one_mul _

/-- T-IZ (from first principles): replaces the bare h_bound hypothesis in t_iz_complete
    with THREE hypotheses, of which only `IsStrictStateSequence` is a ZP-A lattice condition
    (and it constrains the DEPTH INDEX). The other two live in ℚ_[2]: `hS`, that the chain is
    nowhere zero, and `IsDepthChain`, the BRIDGE asserting the 2-adic valuation tracks that
    index — it binds no `ZPSemilattice` at all and is an undischarged modelling commitment.
    Optional transparency variant — t_iz_complete is the canonical theorem.
    A peer reviewer can now trace the full chain from the ZP-A conditions to convergence
    without encountering an ungrounded hypothesis. -/
theorem t_iz_complete_from_axioms
    (S : ℕ → Q₂) (depths : ℕ → ℕ)
    (hS : ∀ n, S n ≠ 0)
    (h_depth : IsDepthChain S depths)
    (h_seq : IsStrictStateSequence depths)
    {L' : Type*} [ZPSemilattice L'] [ZeroParadox.KleeneStructure L']
    (terminal : L') (ε₀' : L')
    (h_role : ∀ x : L', join terminal x = x) :
    Filter.Tendsto S Filter.atTop (nhds 0) ∧
    terminal = bot ∧
    ZeroParadox.IsQuineAtom (bot : L') ∧
    join (bot : L') ε₀' = ε₀' :=
  t_iz_complete S (t_iz_h_bound_from_depth_chain S depths hS h_depth h_seq) terminal ε₀' h_role

end ZeroParadox

/-! ## Axiom Purity Check

Verified results (all sorries filled; no sorryAx anywhere):
- t_iz_norm_tendsto_zero: propext, Classical.choice, Quot.sound
    (squeeze_zero + tendsto_pow_atTop_nhds_zero_of_lt_one — standard Mathlib analysis)
- t_iz_conv_zero: propext, Classical.choice, Quot.sound
    (tendsto_zero_iff_norm_tendsto_zero — standard Mathlib normed group)
- t_iz_cauchy: propext, Classical.choice, Quot.sound (no sorryAx)
- t_inside_zero: propext, Classical.choice, Quot.sound (no sorryAx)
- t_iz_r1_t3_geometric_bound: propext, Classical.choice, Quot.sound
    (Padic.norm_eq_zpow_neg_valuation + zpow_le_zpow_right₀ — standard Mathlib p-adics)
- t_iz_valuation_unbounded: propext, Classical.choice, Quot.sound
    ("sup v₂ = ∞" — proof obligation table row 3, now formally proved)
- t_iz_limit_is_new_null: does not depend on any axioms (axiom-free!)
- c_t_iz_null_balance: propext (via c_da2_novelty)
- t_iz_c3_compatible: propext, Classical.choice, Quot.sound
    (inherited from c3_irreversible — standard Mathlib topology axioms)
- t_iz_h_bound_from_depth_chain: propext, Classical.choice, Quot.sound
    (Padic.norm_eq_zpow_neg_valuation + zpow_le_zpow_right₀ + mul_le_mul_of_nonneg_right;
     optional transparency lemma — t_iz_complete verified without it)
- t_iz_complete_from_axioms: propext, Classical.choice, Quot.sound
    (delegates to t_iz_h_bound_from_depth_chain + t_iz_complete — same axiom set;
     optional transparency variant — t_iz_complete is the canonical theorem) -/

section PurityCheck
open ZeroParadox ZeroParadox ZPSemilattice ZeroParadox ZeroParadox

#print axioms nat_has_no_top
#print axioms nat_strict_of_strict_state_seq
#print axioms h_strict_from_r1_t3
#print axioms t_iz_complete
#print axioms t_iz_norm_tendsto_zero
#print axioms t_iz_conv_zero
#print axioms t_iz_cauchy
#print axioms t_inside_zero
#print axioms t_iz_r1_t3_geometric_bound
#print axioms t_iz_valuation_unbounded
#print axioms t_iz_limit_is_new_null
#print axioms c_t_iz_null_balance
#print axioms t_iz_c3_compatible
#print axioms t_iz_h_bound_from_depth_chain
#print axioms t_iz_complete_from_axioms

end PurityCheck
