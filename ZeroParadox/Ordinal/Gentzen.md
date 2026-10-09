# The Kleene-ordinal bridge: where the value changes, and why that is not occurrence

Moved from `ZeroParadox/Ordinal/Gentzen.lean` § VI. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** It has since carried corrective edits, but its claims are unverified until a claim review says otherwise.

Two senses of "occurrence" appear below, and both are meant: in the table chart, hε₀ (φ ε₀ = c₁) is the entry the tower does not force; in the dynamics chart, occurrence is the separate commitment that instantiation occurs (`ZeroParadox/Order/Snap.lean`, the NO-GO gauge, `tsnap_holds_but_nothing_moves`).

## Formal Overview

Moved from `ZeroParadox/Ordinal/Gentzen.lean`'s module doc (2026-09-19) — editing that block
un-grandfathered it against the prose-length cap, and the long form belongs here.

ZPL has four components:

1. **Axiom Footprint Convergence** — a survey of where `Classical.choice` appears across the
   layers tabulated in §I. The footprints are not uniform:
   `ZeroParadox/Computability/Kleene.lean` §V proves one statement both ways with opposite
   footprints, and ZP-K §IV tabulates the measurements. Not a Lean proposition — and
   `#print axioms` measures a proof's dependencies, never a theorem's need; necessity takes a
   reduction to a taboo (`ZeroParadox/Category/ChoiceCannotBe.lean` §IV).
2. **Rogers' Fixed-Point Stability** — for any computable `f`, some code is behaviourally
   fixed by `f` (`eval (f c) = eval c`). In Lean scope; follows from ZPK's
   `roger_fixed_point_exists`.
3. **Ordinal ε₀ tower** — `ε₀ = nfp (ω^·) 0` is the supremum of the tower `ω, ω^ω, ω^(ω^ω), …`;
   it is a fixed point of `α ↦ ω^α`; it is the first such fixed point above 0. Fully in Lean
   scope via Mathlib ordinals.
4. **Cantor Normal Form Bridge** — `cnfToZp2` maps ordinals below ε₀ (`NONote`) into `ℤ₂` by
   recursion on their Cantor normal form; as the tower stages approach ε₀ their images converge to `0 = ⊥` in
   `ℤ₂`; ε₀ itself has no image, and the two limits correspond as in
   `ZeroParadox/Ordinal/Epsilon0CannotBe.lean` § V. For a map φ : Ordinal → MachinePhase,
   the tower forces the floor of where the value can change: nothing fires below ε₀
   (`snap_threshold_is_epsilon_zero`), which is not occurrence. That φ fires there is
   hε₀ (φ ε₀ = c₁; in the ℤ₂ chart, snapEmbed (φ ε₀) = 0), the snap's occurrence at ε₀ (the table chart),
   taken as a hypothesis: of the infinitely many admissible firing points that monotonicity
   and tower alignment (every tower stage sent to c₀) leave open, hε₀ selects the least, and
   so fixes φ uniquely (`ZeroParadox/Ordinal/Incompleteness.lean` § II, the examples after
   `snap_unconditional`). Whether Classical.choice is forced by the metric collapse is a
   separate open question (`ZeroParadox/Ordinal/SyntacticCollapse.md`).
   Proof partially in Lean scope.

Axiom footprint: `[propext, Classical.choice, Quot.sound]` throughout `Gentzen.lean`, measured.

### Dependencies

- ZPK (§I): `KleeneStructure`, `roger_fixed_point_exists`, `IsComputationalQuine`
- ZPB (§IV): 2-adic topology, `PadicInt 2`, 2-adic valuation
- ZPE (§V): T-SNAP, `MachinePhase`, `t_snap_machine`

## § I. Axiom Footprint Convergence

Moved from `ZeroParadox/Ordinal/Gentzen.lean` § I (2026-09-15), carried in the same accepted-defect baseline as § VI, so the warning above applies to it too.

Non-constructibility appears across the layers tabulated below. The axiom footprints are not
uniform — the ZPJ/K row names a witness on each side, `AFAStructure.bot_self_mem` measuring no
axioms and `botCode` carrying them — and ZP-K § IV tabulates the measured footprints.
Whether any of that dependence is necessary (forced by ZP geometry rather than incidental)
is the open Classical.choice inversion conjecture (`ZeroParadox/Ordinal/SyntacticCollapse.md`): #print axioms on a
proof shows dependence, not a principle's necessity.

| Layer | Formal Language | Expression of non-constructibility |
|-------|----------------|--------------------------------------|
| ZPB   | Topology        | C3: no continuous path ⊥ → x ≠ ⊥   |
| ZPC   | Information     | L-INF: infinite surprisal at ⊥       |
| ZPJ/K | Set + Compute  | bot_self_mem (AFA); botCode (Kleene) |
| ZPI   | Algorithmic IT  | K uncomputable; the K-ratio bridge is superseded (ZeroParadox/Valuation/SemilatticeInstance.lean § II) |

K is not computed in Lean in this framework. The AFA/Kleene route reaches the same
fixed-point structure via a path whose Kleene step is a KleeneStructure requirement.

## § IV. Cantor Normal Form Bridge

Moved from `ZeroParadox/Ordinal/Gentzen.lean` § IV (2026-09-30), carried in the same accepted-defect baseline as § VI, so the warning above applies to it too.

Every ordinal below ε₀ has a unique Cantor normal form — a finite expression
  ω^e₁ · a₁ + ω^e₂ · a₂ + ... + ω^eₙ · aₙ
with e₁ > e₂ > ... > eₙ and 0 < aᵢ < ω. In Lean: `NONote` (the type of ordinals
below ε₀ in Cantor normal form from Mathlib.SetTheory.Ordinal.Notation).

The bridge: `cnfToZp2 : NONote → ℤ_[2]` maps each CNF term to a 2-adic integer. From tower
stage 1 on, the 2-adic valuation of the image tracks ordinal height (`tower_orders_agree`,
`ZeroParadox/Ordinal/CnfBridge.lean`). For `ω^e · n + a`:
  cnfToZp2(ω^e · n + a) = 2^(v₂(cnfToZp2(e)) + 1) · n + cnfToZp2(a)

This recursion ensures that the images of the tower stages get valuation = stage index:
  cnfToZp2(ω^[0] 0) = 0              (valuation 0 by convention)
  cnfToZp2(ω^[1] 0) = 2^1 = 2       (valuation 1)
  cnfToZp2(ω^[2] 0) = 2^2 = 4       (valuation 2)
  cnfToZp2(ω^[n] 0) = 2^n           (valuation n; n ≥ 1)

As n → ∞, valuation → +∞, so the sequence converges to 0 = ⊥ in ℤ_[2].

The valuation and convergence results in this section are fully in Lean scope:
- `cnfToZp2` is defined by structural recursion on the underlying ONote
- `towerNONote n` lifts each fundamentalSeq n to a NONote via NONote.oadd
- The valuation formula is proved by induction using PadicInt.valuation_pow

## § V. Ordinal Tower Limit and ZPB Pre-image

Moved from `ZeroParadox/Ordinal/Gentzen.lean` § V (2026-10-01), carried in the same accepted-defect baseline as § VI, so the warning above applies to it too, corrective edits since the move included. The section's last paragraph (the bridge to ZPE's MachinePhase) is new text written 2026-10-01, not moved, and is not covered by that banner.

What this does NOT claim:
  - That ε₀ is the proof-theoretic ordinal of PA (two results, credited in ZP-L Remark R-L.1; not claimed)
  - Any statement about formal provability in PA
  - A "solution" to the continuum hypothesis or other independent questions
  - Anything outside the structural identification of the snap with the ordinal limit
  - That ε₀ is the UNIQUE minimal snap boundary: snap_threshold_is_epsilon_zero
    shows no ordinal below ε₀ works (for maps satisfying the stated hypotheses),
    but does not rule out maps satisfying those hypotheses that snap at some ordinal
    strictly above ε₀
  - That the snap threshold result applies to all maps Ordinal → MachinePhase,
    regardless of the monotonicity and tower-alignment hypotheses

What is proved in `ZeroParadox/Ordinal/Gentzen.lean` (§ III + § IV + § V):
  - Ordinal: ε₀ = sup{(ω^·)^[n] 0 | n : ℕ}, every finite stage strictly below ε₀
  - ZPB: cnfToZp2(towerNONote n).valuation = n; for n ≥ 1, cnfToZp2(towerNONote n) = 2^n
    in ℤ_[2]; norm = ‖2‖^n → 0, so the tower images converge to 0 = ⊥ in ℤ_[2]
    (tower_converges_to_zero)
  - Cofinality: the fundamental sequence is cofinal in ε₀ — for any α < ε₀,
    some tower stage exceeds α (fundamentalSeq_cofinal)
  - Snap lower bound: any order-non-decreasing φ that maps all tower stages to c₀
    maps every ordinal below ε₀ to c₀ (snap_threshold_is_epsilon_zero). This is a
    lower bound on the snap threshold, not a uniqueness result. A witness snapping
    exactly at ε₀ is provided by c1_epsilon_zero_identification.

The bridge to ZPE's MachinePhase: the canonical threshold map is order-non-decreasing
(`snap_map_mono`); no φ : Ordinal → MachinePhase and g : MachinePhase → ℤ_[2] make `g ∘ φ`
agree with `cnfToZp2` along the tower (the `example` after `c1_epsilon_zero_identification`).
Through `snapEmbed` the two disagree at every stage n ≥ 1, and the stages' `cnfToZp2` images
tend to `snapEmbed c₁` = 0 (`ZeroParadox/Ordinal/Incompleteness.lean` § II).

## § VI. Kleene-Ordinal Fixed-Point Bridge

The ordinal fixed-point structure (ε₀ = nfp (ω^·) 0, ω^ε₀ = ε₀) and the computational
fixed-point structure (Rogers' fixed-point theorem, roger_fixed_point_stability) both carry
Classical.choice in the proofs recorded here — parallel structure, not a proved isomorphism,
and a fact about those proofs rather than a necessity.
This is the content of §I Axiom Footprint Convergence.

The hypothesis
  hfp : ∀ α, ω^α = α → φ α = c₁
encodes that ordinal fixed points of ω^· (the ordinal analogues of Kleene fixed points)
map to the snap state c₁. Under this hypothesis, combined with monotonicity (hmono) and
tower alignment (h0), φ is forced to take the value c₁ at ε₀ and at no smaller ordinal — a statement
about WHERE the value changes, not that anything occurs (the dynamics chart):
  - every ordinal below ε₀ maps to c₀ (snap_threshold_is_epsilon_zero)
  - ε₀ maps to c₁ (epsilonZero_fixedPoint + hfp)
  - ε₀ is the minimal ordinal assigned c₁ (from the two above)

**⚠ CORRECTED 2026-07-31. This paragraph read "The computational side — that the snap MUST
occur — is proved in ZPE (T-SNAP)", and that is FALSE.** T-SNAP constrains the *shape* of a
transition, never that one occurs: `ZeroParadox/Order/Snap.lean` says so in its own NO-GO gauge (the "T-SNAP constrains the SHAPE of a transition, not that one occurs" block) and
makes it checkable with `tsnap_holds_but_nothing_moves`, a machine-checked model in which
T-SNAP holds and **nothing moves** (`stuckPhase := id`). `t_snap_derived` is `⟨l_run, tq_ih,
rfl⟩`, where `l_run` is `by decide` — it proves the two phases are distinct and that the join
absorbs. That the snap occurs follows from the **occurrence commitment** (instantiation occurs)
together with DA-1 (closed given DP-2); `Information/Surprisal.lean`'s `l_inf` docstring is
the framework's designated honest statement of where the argument for it stops.

So nothing below is unconditional. The bridge here is structural, and note that `hfp` **is**
the snap rather than a route to it: IF maps aligned with the fixed-point structure snap at
fixed points, THEN ε₀ is the minimal snap threshold (no snap before ε₀, and φ ε₀ = c₁).
