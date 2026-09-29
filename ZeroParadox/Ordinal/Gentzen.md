# The Kleene-ordinal bridge: where the value changes, and why that is not occurrence

Moved from `ZeroParadox/Ordinal/Gentzen.lean` § VI. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

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
4. **Cantor Normal Form Bridge** — ordinals below ε₀ (`NONote`) encode into `ℤ₂` via their
   Cantor normal form; as the tower stages approach ε₀ their encodings converge to `0 = ⊥` in
   `ℤ₂`. The identification of these two limits is the remaining gap. Proof partially in Lean
   scope.

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
is the open Classical.choice inversion conjecture (cf. ZPM §II): #print axioms shows dependence,
not necessity.

| Layer | Formal Language | Expression of non-constructibility |
|-------|----------------|--------------------------------------|
| ZPB   | Topology        | C3: no continuous path ⊥ → x ≠ ⊥   |
| ZPC   | Information     | L-INF: infinite surprisal at ⊥       |
| ZPJ/K | Set + Compute  | bot_self_mem (AFA); botCode (Kleene) |
| ZPI   | Algorithmic IT  | K(Sₙ|n)/|Sₙ| → 1; K uncomputable    |

K is not computed in Lean in this framework. The AFA/Kleene route reaches the same
fixed-point structure via a path whose Kleene step is a KleeneStructure requirement.

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
about WHERE the value changes, not that anything occurs:
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
