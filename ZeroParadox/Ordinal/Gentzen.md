# The Kleene-ordinal bridge: where the value changes, and why that is not occurrence

Moved from `ZeroParadox/Ordinal/Gentzen.lean` § VI. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## § I. Axiom Footprint Convergence

Moved from `ZeroParadox/Ordinal/Gentzen.lean` § I (2026-09-15), carried in the same accepted-defect baseline as § VI, so the warning above applies to it too.

Non-constructibility appears in four formal languages across the ZP framework.
Each proved theorem in each layer, as currently written, depends on Classical.choice at the
diagonal step. Whether that dependence is necessary (forced by ZP geometry rather than incidental)
is the open Classical.choice inversion conjecture (cf. ZPM §II): #print axioms shows dependence,
not necessity.

| Layer | Formal Language | Expression of non-constructibility |
|-------|----------------|--------------------------------------|
| ZPB   | Topology        | C3: no continuous path ⊥ → x ≠ ⊥   |
| ZPC   | Information     | L-INF: infinite surprisal at ⊥       |
| ZPJ/K | Set + Compute  | bot_self_mem (AFA); botCode (Kleene) |
| ZPI   | Algorithmic IT  | K(Sₙ|n)/|Sₙ| → 1; K uncomputable    |

The reason K is absent from Lean: its existence requires Classical.choice —
exactly the axiom Nat.Partrec.Code.fixed_point₂ already uses in ZPK. The
AFA/Kleene route reaches the same fixed-point structure via a path whose Kleene step is a
KleeneStructure requirement.

## § VI. Kleene-Ordinal Fixed-Point Bridge

The ordinal fixed-point structure (ε₀ = nfp (ω^·) 0, ω^ε₀ = ε₀) and the computational
fixed-point structure (Rogers' fixed-point theorem, roger_fixed_point_stability) both require
Classical.choice at their non-constructive step — parallel structure, not a proved isomorphism.
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
