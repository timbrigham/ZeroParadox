# Zero Paradox Claims Ledger

The Zero Paradox is not one claim — it is a set of individual, separately-stated claims, each carrying its own status: **proved** (and at what axiom cost), **argued**, **committed**, or **open**. This ledger is where every one of those claims lives in one place, with its Lean witness and the Lean kernel's exact axiom dependency, so the proved / argued / open boundary can be checked directly rather than reconstructed from the prose of the individual layers. Stating each claim's status individually and honestly — and making the boundary mechanically checkable — is a deliberate design value of the project: the framework is developed in public precisely so the line between what is proved and what is believed is never blurred.

This ledger is a *view*, not a new source of truth. The authorities it consolidates are:

- **Axiom profiles** — [ZeroParadox/AxiomProfile.lean](ZeroParadox/AxiomProfile.lean) (the checkable artifact; CI-built on every push).
- **The Lean sources** — under [`ZeroParadox/`](ZeroParadox/) in this repository.
- **The "argued, not proved" tier** — [fmc.md](fmc.md) (Forced Metatheoretic Commitment: definition, conditions, falsifiers).
- **Versions and script hashes** — [register.md](register.md).

**How to verify the axiom column yourself.** Lean's kernel reports the complete axiom dependency of each theorem:

```
lake build ZeroParadox.AxiomProfile      # compiles the curated artifact
lake env lean ZeroParadox/AxiomProfile.lean   # prints each #print axioms result
```

Notation: **(none)** = `'<thm>' does not depend on any axioms` (stronger than choice-free — not even `propext`). **[propext, Quot.sound]** = choice-free, uses only propositional extensionality and quotient soundness (both Lean 4 standard). **[propext, Classical.choice, Quot.sound]** = inherits `Classical.choice` from a Mathlib library; in this framework that occurs only in the analytic *realization* layers, never in a core claim (see Tier 3).

---

## Tier 1 — Proved, axiom-free (depends on no axioms at all)

The framework's load-bearing claims. The Lean kernel reports no axiom dependency whatsoever.

| Claim | Readable name | Lean witness | Axioms |
|-------|---------------|--------------|--------|
| T-SNAP | The Binary Snap (⊥ → ε₀) — the central theorem | `ZPE.t_snap_derived`, `t_snap_machine`, `t_snap_join`, `t_snap_irreversible` | (none) |
| DA-1 (given DP-2) | Instantiation alignment, minimal path — *closed conditional on DP-2 (Tier 5)* | `ZPE.da1_minimal_path` | (none) |
| DP-2 (formalized) | Execution distinguishability lemma — *the proved lemma; the modeling commitment it encodes is Tier 5* | `ZPE.dp2_execution_distinguishability` | (none) |
| ⊥ = minimum | Lattice bottom is the least element (ZP-A) | `ZPA.ZPSemilattice.bot_le` | (none) |
| CC-1 (in ZP-A) | S₀ = ⊥ as a lattice fact | `ZPA.ZPSemilattice.cc1` | (none) |
| Quine atom = ⊥ | The self-containing bottom is executable self-reference (ZP-J) | `ZPJ.bot_is_quine_atom` | (none) |
| CC-1 derived | S₀ = ⊥ derived axiom-free in any AFAStructure | `ZPJ.cc1_derived` | (none) |
| T-EXEC | Self-execution forces the diagonal fixed point | `ZPJ.t_exec` | (none) |
| Quine atom unique | The fixed point is unique | `ZPJ.quine_atom_unique` | (none) |
| Aczel J largest | DC-free Aczel uniqueness (J is the largest self) | `ZPJ_AczelConn.J_self_is_largest` | (none) |
| T-IZ (limit step) | Every maximal chain's limit is its own successor ⊥ | `ZPI.t_iz_limit_is_new_null` | (none) |

## Tier 2 — Proved, choice-free `[propext, Quot.sound]`

No `Classical.choice`; at most propositional extensionality and quotient soundness.

| Claim | Readable name | Lean witness | Axioms |
|-------|---------------|--------------|--------|
| Power-set floor | Structural floor in the power-set model | `ZPH_PowerSet.ps_structural_floor` | [propext, Quot.sound] |
| Wheel instance | Wheel of fractions is a wheel (Carlström Def 1.1) | `ZPJ_WheelFrac.instWheel` | [propext, Quot.sound] |
| ∞ ≠ ⊥ | The wheel's infinity is distinct from its bottom | `ZPJ_WheelFrac.inf_ne_bot` | [propext, Quot.sound] |
| Fixed-point fork | lfp/gfp collapse iff the operator has a unique fixed point | `ZPP.fork_collapse_iff` (with `fork_le`, `collapse_of_unique`, `unique_of_collapse`) | [propext, Quot.sound] |
| Coalgebra fork (μ side) | `Fix` empty — choice-free | `ZPP.fix_isEmpty` | [propext, Quot.sound] |
| Quine-atom identity | The self-referential fixed points are exactly {⊥} (unique, and = ⊥) | `ZPJ_QuineDichotomy.quine_self_members_eq_bot` | [propext, Quot.sound] |

## Tier 3 — Proved, inherits `Classical.choice` from Mathlib (analytic realizations)

These *realize* the snap floor inside standard analytic structures and inherit `Classical.choice` from Mathlib's classically-built topology / inner-product / category / probability / computability / ordinal libraries. **The dependence is in the realization, not in any core claim** (those are Tier 1–2). All report `[propext, Classical.choice, Quot.sound]`.

| Claim | Realization | Lean witness |
|-------|-------------|--------------|
| Snap irreversibility | p-adic topology (ℚ₂) | `ZPB.c3_irreversible` |
| Snap orthogonality | Hilbert space | `ZPD.t4_snap_orthogonal` |
| ⊥ as inverse limit | TopCat | `ZPH_TopFunctor.fB_functor` |
| ⊥ as initial object | ModuleCat ℂ | `ZPH_HilbFunctor.fD_functor` |
| ⊥ as initial object | KleisliCat PMF (`fC_no_return` = AX-G2 as theorem) | `ZPH_InfoFunctor.fC_functor` |
| ε₀ as exact snap threshold | ordinal tower, 2-adic convergence | `ZPL.c1_epsilon_zero_identification`, `ZPL.snap_zp2_correspondence` |
| Computational grounding | Kleene fixed point | `ZPK.da1_closed_concrete` |
| Kleene–ordinal bridge | MachinePhase → ℤ₂; quine ∧ ε₀ co-witnessed | `ZPM.zpm_triangle` |
| ℝ ≠ ℚ₂ (Ostrowski) | number-system instance of the fork | `ZPP.real_not_equiv_padic`, `ZPP.completions_exhaustive` |
| No snap in ordered fields | ℝ, ℚ as counterexamples | `ZPF.f_snap_impossible`, `ZPF.r_snap_impossible` |
| Snap-occurrence dichotomy | completions of ℚ: ℚ_p totally disconnected = snap, ℝ connected = no snap; Ostrowski exhaustive + exclusive | `ZPF_SnapDichotomy.snap_dichotomy` (with `padic_snaps`, `real_no_snap`) |
| Quine-atom dichotomy (structural) | μ/ν fork — the self-referential object exists on ν (non-well-founded), not μ; the "Quine atom ⟺ AFA" reading is metatheoretic (Tier 4), not this theorem | `ZPJ_QuineDichotomy.quine_dichotomy` |
| T-IZ (full chain) | the complete Inside-Zero chain — inherits choice only via its ZP-K/DA-1 step (the limit-step lemma alone is axiom-free, Tier 1) | `ZPI.t_iz_complete` |

*Whether this inherited dependence is structurally forced by the snap geometry or merely incidental to Mathlib's implementation is **open** (see Tier 6). The one layer classified so far (the `ZPB_PadicTree` choice-probe) found it mostly incidental and routable.*

## Tier 4 — Argued, not proved (Forced Metatheoretic Commitments)

Foundational choices the framework's internal structure rules out alternatives to *by argument, not proof*, and falsifiably. Each is metatheoretic — it lives in the ZF+AFA framing, not the Lean kernel — and carries a named falsifier. See [fmc.md](fmc.md).

| Commitment | What is argued | Proved part (separate) | Named falsifier |
|------------|----------------|------------------------|-----------------|
| AFA necessity (R-AFA, ZP-E) | That ⊥ = {⊥} forces ZF+AFA over Foundation (a metatheoretic squeeze: Foundation too restrictive, Boffa too permissive, AFA the unique fit) | The *structural* self-application fixed point is Lean-proved: `ZPJ.t_exec` (Tier 1, axiom-free) | A well-founded (Foundation-respecting) model of ⊥ consistent with R3 and L-INF would overturn the forcing |
| CC-2 set-membership reading | The literal ⊥ ∈ ⊥ (the Quine atom as a set fact) | The structural fixed point `ZPJ.t_exec` is axiom-free; only the set-membership reading is metatheoretic | Same as above — a Foundation-respecting realization of the same structural role |

## Tier 5 — Modeling commitments (chosen, not derived; not open questions)

Explicit, motivated commitments. Listed so the open register holds only genuinely unresolved questions.

| Commitment | Nature | Lean note |
|------------|--------|-----------|
| The diagonal fixed point (cross-layer identity) | ⊥ is one self-referential fixed point; each framework's face is that single attribute in its own language | Faces proved per-framework (Quine atom `ZPJ.t_exec`, Tier 1; Kleene quine ZP-K, v₂(0)=∞ ZP-B, categorical initial ZP-G, Tier 3). That they are *one object* carrying the attribute is the identity commitment; MC-1 (below) is its categorical instance. The Lawvere identification is conjectural (Tier 6). |
| MC-1 identity half | Reading the four domain bottoms as numerically *one* object | The *correspondence* half is a theorem (`ZPH_MC1.mc1_correspondence`, Tier 3); the identity half is the chosen identification |
| DP-2 (execution distinguishability) | The commitment DA-1 rests on; motivated by ZP-C D7, not freely chosen | *Listed in two tiers by design:* the formalized lemma is proved and axiom-free (`ZPE.dp2_execution_distinguishability`, Tier 1); the modeling choice that lemma encodes is the commitment, recorded here |
| BA-1 (temperature T) | A universe-contingent scale parameter; specific value irrelevant to structure | Not formalized - the framework's only bridge to physical units, via Landauer's `E = kT ln2` (referenced in ZP-C/E/H). The information-thermodynamics of the snap is an open direction, not a claim. |

A commitment marked "not a novel commitment" in the layers means its content is formally grounded in prior layers and derivable there; it is stated as a local axiom only for the self-containment of that layer — the same pattern by which AX-1 was stated as an axiom before being derived as T-SNAP. **AX-1 (Binary Snap Causality) is no longer an axiom:** it is Theorem T-SNAP, derived in ZP-E from A4, the standard bottom-element axiom of join-semilattice theory (∀ x, ⊥ ∨ x = x). AX-1 was redundant — any join-semilattice with bottom already has this property.

<details>
<summary><b>The single bottom (MC-1) — in full</b> - click to expand</summary>

The bottom elements across the layers - the algebraic ⊥, the 0 of Q₂, the Turing initial configuration c₀, and the categorical initial object - are identified as one object, the same self-referential (diagonal) fixed point in each framework. This identification splits into a correspondence half, now formally realized in Lean, and an identity half - that the four are numerically one object - which remains a modeling commitment rather than a proven identity. Its faces are the Quine atom (⊥ = {⊥}) in set theory, the Kleene quine in computation, the point v₂(0) = ∞ in valuation, and the initial object in category theory. This identification is substantially grounded rather than stipulated: each domain locates its own bottom through its own logic first, and the cross-layer agreement is then enforced formally (the ZP-E typeclass instance ties ZP-A ⊥ to ZP-C c₀; AX-G1 grounds the categorical initial in ZP-A ⊥; ZP-H T-H3 proves snap consistency across all four functors). The categorical correspondence is now realized in the standard domain categories of Mathlib: the snap floor is the inverse limit in `TopCat`, the initial object in `ModuleCat ℂ`, and the initial object in the Kleisli category of the probability monad `KleisliCat PMF` - with no morphism returning to it in the stochastic case (the bundled witness is `mc1_correspondence`). What remains is the interpretive choice to call these one object.

</details>

<details>
<summary><b>The metatheoretic stance — ZF + AFA, and why AFA is forced</b> - click to expand</summary>

This framework is stated over ZF + AFA (Zermelo-Fraenkel with Anti-Foundation Axiom), not standard ZFC, and AFA permits self-containing sets (x = {x}). This affects only one commitment, the Quine atom (CC-2); the remaining results do not depend on non-well-founded sets. The Axiom of Choice is not assumed. The move to AFA is not a free choice — it is argued to be forced by the framework's own results (Tier 4). What "forced" means here, and the discipline every such claim must meet, is defined in [fmc.md](fmc.md).

Standard ZFC is incompatible with CC-2: a well-founded ⊥ would admit an external interpreter, contradicting the self-execution argument. The forcing comes from the framework's results: ZP-A R3 and ZP-C L-INF together establish that ⊥ admits no finite external description, which is incompatible with the Foundation axiom's well-foundedness requirement (no infinite descending ∈-chains). The full argument for why AFA specifically is the appropriate extension - rather than simply removing Foundation - is developed in ZP-E Remark R-AFA. (This is an argument, not a derivation in the formal system — see Tier 4 and its named falsifier.)

</details>

<details>
<summary><b>The supporting commitments</b> (label, type, statement) - click to expand</summary>

| Label | Type | Statement |
|-------|------|-----------|
| **AX-B1** | Directly Verifiable | A state either exists or it does not. Directly verifiable by computation (OntologicalStates derives DecidableEq; ax_b1_distinct proved by `decide` without classical axioms) - not a novel commitment of this framework. |
| **AX-G1** | Axiom | An initial object exists in the category C. The bottom element ⊥ is the universal origin of all structure: a unique object from which every other object is reachable, and to which no morphism returns. Not a novel commitment - ⊥'s existence as the bottom element of the ZP-A semilattice already guarantees this; ZP-G names it in categorical language. |
| **AX-G2** | Axiom | Source asymmetry: hom(X, 0) = ∅ for X ≠ 0. Once something emerges, it cannot return to nothing. Not a novel commitment - follows from antisymmetry of the ZP-A partial order and is independently confirmed by ZP-B C3 (topological irreversibility). |
| **MP-1** | Principle | The representational base is the minimum sufficient base for AX-B1. Derives p = 2. |
| **RP-1** | Principle | The probabilistic representation of a state in the two-element state space is a point-mass distribution. |
| **DP-1** | Design Commitment | Clopen separation in Q₂ is represented by orthogonality in H. |

</details>

## Tier 6 — Open

| Item | Status |
|------|--------|
| `Classical.choice` necessity (analytic layers) | **Core is choice-free (verified); analytic-layer necessity is open.** The central results carry no `Classical.choice` — T-SNAP depends on no axioms at all, and the lattice (ZP-A), the Quine-atom self-reference (ZP-J), and the structural floor are choice-free. `Classical.choice` appears only where the framework builds on Mathlib's classically-built topology / analysis / ordinal / computability libraries (Tier 3) and auxiliary constructions on them. Whether that inherited dependence is structurally forced or merely incidental is the open question; the one layer classified so far (`ZPB_PadicTree`, the choice-probe) found it mostly incidental and routable. Testable via constructive ordinal fixed-point theory over ONote/NONote (future ZP-N). |
| OQ-E2: cardinality ↔ semilattice correspondence | **Partially closed — ZP-I T-IZ.** Ordinal indexing Ω = ω forced by the countable binary substrate (ZP-C D4, Q₂ separability, binary alphabet); internal/external perspective relativity is ordinal, not set-theoretically free. The formal connection between specific semilattice structures and specific CH instances remains open. |
| ε₀ / proof-theoretic ordinal | **Partially closed — ZP-L.** `c1_epsilon_zero_identification` establishes the canonical snap map with ε₀ as the exact transition point; `snap_zp2_correspondence` proves the four-way conjunction. Structural alignment with Gentzen's proof-theoretic ordinal (PA consistency) is documented in ZP-L Remark R-L.1. Full type-theoretic identity across universes (MachinePhase vs Ordinal) is outside Lean scope, deferred pending OQ-E2. |
| DA-3: perspective-relative cardinality | Closed (definitional, via D7 exhaustiveness) / Candidate (DA-3-C1); formal cardinality derivation deferred to OQ-E2. |
| Lawvere unification of the diagonal fixed point | **Conjecture / connection, not proved.** That the shared self-referential-fixed-point attribute (Tier 5) is an instance of Lawvere's fixed-point theorem (Lawvere 1969) is a connection, not a ZP result. Yanofsky (2003) restated that theorem in plain set/function terms and unified Cantor, Russell, Gödel, Tarski, Turing, and the recursion theorem (quine) as one scheme - those faces are prior art, cited not claimed. ZP's contribution relative to this literature: candidate faces outside their scope (the 2-adic valuation v₂(0)=∞, ε₀, the wheel), the machine-checked axiom/choice footprint of each face, and the location claim (the fixed point at the floor ⊥, the Gödel inversion) - a framing, not a theorem. The numerical "one object" identity is MC-1, a commitment (Tier 5), strictly beyond the "same scheme" Lawvere/Yanofsky establish. See the Convergence section below. **Update (machine-checked, ZPJ_Lawvere):** the face-by-face question is now proved - in Set no face is a Lawvere instance (Cantor obstruction), the computability face is a genuine instance (wraps Mathlib's recursion theorem); the cross-face unification into one object remains the MC-1 commitment. |
| The well-foundedness boundary (full Taylor coalgebraic; "Rung C") | **Best-effort done; full version open.** The snap as a ν→μ (non-well-founded → well-founded) crossing is formalized at the relation level (`ZPJ_Boundary`: `floor_not_wellFounded` axiom-free, `snap_crossing`) and bundled with ZP-P's categorical μ/ν fork (`ZPJ_BoundaryBridge`: `snap_boundary_two_registers`). The single-carrier "snap is one crossing" picture introduces no *new* commitment - it rests on the framework's existing ⊥/ε₀ identification (MC-1; the ε₀ identity open under OQ-E2), with the endpoints (the floor non-well-founded via ZP's real ⊥, axiom-free; the ascent well-founded) independently proved. The full Taylor coalgebraic statement - well-founded coalgebras and the General Recursion Theorem (well-founded ⟺ recursive) - is not formalized: Mathlib lacks the machinery (next-time operator, Pataraia's fixed-point theorem, the recursion theorem). Cited to Taylor / Adámek-Milius-Moss; flagged as an open contribution point. |
| Second-prover cross-check | A Rocq (or other) independent re-verification is **not yet done**. |

Open questions are also discussed publicly in the [GitHub Discussions Open Questions category](https://github.com/timbrigham/ZeroParadox/discussions/categories/open-questions).

<details>
<summary><b>Resolved questions</b> (closed) - click to expand</summary>

| Item | Status |
|------|--------|
| OQ-A1: Increment selection | Closed - ZP-E T5 (Iterative Forcing Theorem) |
| OQ-B1: p = 2 justification | Closed - ZP-B T0 (derived from AX-B1 + MP-1) |
| S1: Distribution stipulation | Closed - ZP-C T1 (derived from AX-B1 + RP-1) |
| OQ-C1: Non-conservatism of DF | Closed - ZP-C T2 (rebuilt within extended D6) |
| CC-1 (S₀ = ⊥) derivability | **Closed - ZP-J cc1_derived (axiom-free, Lean)** - was ZP-A Conditional Claim; now derived via ZP-J T-EXEC in any AFAStructure lattice |
| CC-2 (⊥ = {⊥}, the Quine atom) as commitment | **Structural fixed point closed - ZP-J T-EXEC** (axiom-free); the literal set-membership reading remains a Forced Metatheoretic Commitment (Tier 4), not a freestanding modelling choice |
| AX-1: Binary Snap Causality | **Closed - ZP-E T-SNAP (derived theorem)** |
| OQ-E1: Sequence vs. tree structure | Closed - ZP-E DA-2 (directed instantiation tree; branching mandatory via T-SNAP) |
| DA-2: Instantiation succession | Closed - ZP-E DA-2 (terminal state of I_n satisfies ⊥ role for I_n+1; C-DA2 derives each instantiation produces a provably distinct ⊥) |
| DA-1: Instantiation alignment | **Closed given DP-2 - ZP-E / ZP-K.** da1_minimal_path proved axiom-free; Paths 1 and 3 closed via da1_closed_concrete (ZP-K). The former Path 2 (AIT bridge) is a foundational commitment carried by DP-2's motivational grounding (Tier 5) - a chosen principle rather than a proof gap. |
| OQ-G1: Native categorical surprisal | Closed - ZP-G D7' and I-KC (Kolmogorov import; BA-G1 demoted to compatibility remark R-BA) |
| OQ-G2: Left adjoint verification | Closed - ZP-H T-H1 (initial-object universal property verified for all four domain instantiations) |
| OQ-G3: Functor construction | **Closed - ZP-H functor files.** F_A (NatSLat) plus sorry-free functors into standard Mathlib categories (TopCat, ModuleCat ℂ, KleisliCat PMF); bundled as `mc1_correspondence`. Cross-category identity residual is a design commitment (MC-1 identity, Tier 5). |
| OQ-G4: Singularity reconciliation | Closed - ZP-H T-H2 (categorical and ZP-C characterizations shown to be the same obstruction) |
| T-IZ: Inside Zero Theorem | **Fully derived - Lean.** Every maximal ascending chain converges to its own successor null; `t_iz_complete` chains all four steps (Cauchy convergence, DA-2 successor-null identification, DA-1 via AFA/Kleene, T-SNAP). |
| Null balance | **Closed - T-IZ + DA-2.** Every branch starts at ⊥, ascends ω state changes (T3), generates a successor ⊥ at the ordinal limit (T-IZ + T-SNAP + DA-2). |

</details>

---

## Convergence with established work

The Zero Paradox is, in large part, a body of inferences resting on a choice-free, machine-checked core. The strongest non-proof support for the framing is that **independent traditions - set theory, number theory, proof theory, computability, category theory - each arrive near the same structure at zero.** This section maps that convergence honestly.

Three things to read it correctly:

1. **This is convergence evidence, not proof.** It raises the prior that there is a real object at the floor; it closes nothing. Each row's *link status* says exactly how tight the connection is.
2. **The direction of credit points outward.** In every row the established result is the prior work; ZP is an *instance joining* that program, never a frame that subsumes it. Where ZP claims the faces are literally one object, that is a commitment (MC-1), offered to these communities, not imposed on them.
3. **Not all of these are independent of each other.** Lawvere, the coalgebra line, and the categorical face are one tradition, not three; counted honestly, the genuinely separate roads are set theory, valuation / number theory, proof theory, computability, and category theory.

**Named falsifier.** If a framework's bottom were shown *not* to carry the fixed-point / snap structure, or if a listed face turned out structurally dissimilar under scrutiny, the convergence weakens accordingly.

**Prior-art search is ongoing.** This map is certainly incomplete. We treat finding additional prior work as a standing obligation, not a finished task - and corrections, especially "you have missed X," are welcome and will be added here with attribution.

| Established result (prior work, cited) | ZP face | Link status | How ZP reached it |
|---|---|---|---|
| **Lawvere (1969)**, *Diagonal Arguments and Cartesian Closed Categories*; **Yanofsky (2003)** - the diagonal fixed point unifies Cantor, Russell, Gödel, Tarski, Turing, the recursion theorem | ⊥ as the self-referential (diagonal) fixed point - the keystone | **Conjectured unification; face-split now machine-checked** (ZPJ_Lawvere): no Set-level face is a Lawvere instance (Cantor - `nontrivial_lattice_no_witness`, `q2_no_witness`); the computability face is a genuine recursion-theorem instance (`computability_face_fixedPoint`); the one-object unification stays an MC-1 commitment | Connected retrospectively - the keystone framing predated the citation |
| **Taylor** *Well-founded coalgebras and recursion*; **Adámek-Milius-Moss (2020)** (arXiv:1910.09401) - well-founded ⟺ recursive; the μ/ν divide | The snap as the well-foundedness boundary crossing: ⊥ the non-well-founded floor (self-loop), the ε₀ ascent well-founded (ZPJ_Boundary, ZPJ_BoundaryBridge) | **Best-effort formalized + cited for depth** - relation-level boundary + QPF μ/ν bridge proved (`snap_crossing`, `snap_boundary_two_registers`); the well-founded ⟺ recursive depth (Taylor Prop 111) cited, not re-proved (full coalgebraic version awaits Mathlib tooling - Tier 6) | Connected via the back-edge insight - the keystone's structural home (ZP-P already adjacent via Adámek-Rutten) |
| **Aczel (1988)** AFA; **Forti-Honsell (1983)**; **Paulson** - the Quine atom ⊥={⊥}, non-well-founded sets, final-coalgebra theorem | ⊥={⊥} (CC-2); the ZFC/AFA contact point | **Theorem-grounded + commitment**: the structural self-application fixed point (`ZPJ.t_exec`) is axiom-free Lean; the literal set-membership identity is metatheoretic | Independent → later converged (the ⊥ question reached x={x}; matched to AFA after) |
| **Ostrowski's theorem** - every nontrivial absolute value on ℚ is the real or a p-adic one (the complete dichotomy) | ZP-B / ZP-F: the snap fails in ℝ, holds in ℚ₂; v₂(0)=∞ | **Theorem used** - Ostrowski is a classification theorem ZP directly invokes (Mathlib) | Independent → later converged (Riemann-sphere 0/∞ intuition → ℚ₂; Ostrowski recognized as the backing after) |
| **Gentzen** - ε₀ is the proof-theoretic ordinal of PA | ZP-L / ZP-M: ε₀ as the exact snap threshold | **Theorem-aligned** - structural alignment documented (ZP-L Remark R-L.1); full type-theoretic identity deferred (OQ-E2) | Built on the cited work - ε₀ chosen deliberately as PA's ordinal |
| **Kleene's recursion theorem** (quines / self-reproduction) | ZP-K: the Kleene quine; the periodicity fixed-point construction | **Theorem + external novelty signal** - the quine face is standard; the periodicity construction was flagged novel by a computability specialist | Built on the cited work; the periodicity construction is the new piece |
| **Lambek**; **Adámek-Rutten**; **Veltri (2021)**, **Ahrens et al.** - initial-algebra / final-coalgebra (μ/ν) fork; the constructive choice boundary | ZP-P: the lfp/gfp fork spine (`fork_collapse_iff`); the strict instance (`categorical_fork_strict`) | **Theorem + cited boundary** - the fork spine `fork_collapse_iff` is choice-free Lean `[propext, Quot.sound]`; the strict μ-empty/ν-inhabited instance carries `Classical.choice` on the coalgebra side, inherited from Mathlib (per Veltri) | Built on the cited work - the fork is the categorical parent; Veltri connected retrospectively |
| **Carboni-Lack-Walters (1993)** strict initial objects; **Fritz (2020)** Markov categories (Kleisli of the Giry monad) | ZP-G / ZP-H: ⊥ as each domain category's categorical bottom - a strict initial object, or the inverse limit in TopCat (which has a terminal object); AX-G2 = strict initiality; `mc1_correspondence` | **Theorem-grounded + commitment** - each domain bottom is the categorical bottom of its own real Mathlib category (per-category Lean: `fD_zero_isInitial`, `fC_zero_isInitial`, the TopCat limit); the cross-category "one object" identity is the MC-1 commitment | Built on the cited work - standard categorical structure, assembled across the ZP domains |
| **van der Put basis** (indicator functions of clopen balls as an orthonormal system); **Kozyrev (2002)** p-adic wavelet basis of L²(ℚ_p) | ZP-D: `T : Q₂ → H` represents clopen balls as an orthonormal system (clopen separation ↦ orthogonality, DP-1) | **Standard construction, applied** - `T` instantiates the recognized p-adic ball→ONB / wavelet construction; ZP-D's own contribution is the snap-into-state-layer reading (DP-1), not the embedding | Connected retrospectively - `T` was built in-house, recognized as the standard construction afterward |
| **Carlström** - wheels (consistent division by zero) | ZP-J: the wheel of fractions (`ZPJ_WheelFrac`) | **Theorem** - faithful to Carlström's Def 1.1, choice-free; under specialist review | Built on the cited work - developed with Carlström in hand |
| **Chaitin** - algorithmic information theory / incompressibility | ZP-C: unbounded surprisal at ⊥ / no external description | **Analogy / referenced** - lighter; Yanofsky also notes AIT fits the scheme | Parallel - not a load-bearing identity |

---

## Verification by document (Lean 4)

Machine-checked proofs of the formal documents using Lean 4 + Mathlib. Source lives under [`ZeroParadox/`](ZeroParadox/); the full theorem-by-theorem detail is in each source file. The reproducibility commands are in the [README](README.md#reproducing-the-verification).

| Document | Lean Source | Verifies | Build |
|----------|-------------|----------|-------|
| ZP-A Lattice Algebra | [ZPA.lean](ZeroParadox/ZPA.lean) | Partial order, ⊥ as the minimum, monotonicity of state change | Clean - April 2026 |
| ZP-B p-Adic Topology | [ZPB.lean](ZeroParadox/ZPB.lean) | p = 2 forced; Q₂ ultrametric, clopen balls, total disconnectedness, snap irreversibility | Clean - April 2026 |
| ZP-C Information Theory | [ZPC.lean](ZeroParadox/ZPC.lean) | Distinct state distributions, 1-bit divergence, execution as a nonzero change, unbounded surprisal at ⊥ | Clean - April 2026 |
| ZP-D State Layer | [ZPD.lean](ZeroParadox/ZPD.lean) | Transition operator into Hilbert space: existence, uniqueness up to unitary, orthogonality under the snap | Clean - April 2026 |
| ZP-E Bridge Document | [ZPE.lean](ZeroParadox/ZPE.lean) | The snap as a derived theorem (T-SNAP); instantiation succession; axiom-free minimal path | Clean - April 2026 |
| ZP-F The Counterexamples | [ZPF.lean](ZeroParadox/ZPF.lean) | The snap cannot occur in any ordered field (ℝ, ℚ as instances) | Clean - May 2026 |
| ZP-G Category Theory | [ZPG.lean](ZeroParadox/ZPG.lean) | Initial object and its universal property; forward-only structure; the informational singularity | Clean - April 2026 |
| ZP-H Categorical Bridge | [ZPH.lean](ZeroParadox/ZPH.lean) | The snap under all four domain functors; singularity reconciliation | Clean - April 2026 |
| ZP-H Native Categories | [ZPH_TopFunctor.lean](ZeroParadox/ZPH_TopFunctor.lean), [ZPH_HilbFunctor.lean](ZeroParadox/ZPH_HilbFunctor.lean), [ZPH_InfoFunctor.lean](ZeroParadox/ZPH_InfoFunctor.lean), [ZPH_MC1.lean](ZeroParadox/ZPH_MC1.lean) | The snap floor realized in real Mathlib categories: ⊥ as inverse limit in TopCat, initial object in ModuleCat ℂ and KleisliCat PMF; mc1_correspondence bundle | Clean - June 2026 |
| ZP-I Inside Zero | [ZPI.lean](ZeroParadox/ZPI.lean) | Every maximal chain is Cauchy and converges to its own successor ⊥ (Inside Zero) | Clean - April 2026 |
| ZP-J Self-Reference (Core) | [ZPJ.lean](ZeroParadox/ZPJ.lean) | The Quine atom is ⊥ (executable self-reference); CC-1 derived axiom-free | Clean - April 2026 |
| ZP-J AFA Derivation Chain | [ZPJ_AczelConn.lean](ZeroParadox/ZPJ_AczelConn.lean), [ZPJ_SelfApp.lean](ZeroParadox/ZPJ_SelfApp.lean), [ZPJ_Scale.lean](ZeroParadox/ZPJ_Scale.lean), [ZPJ_OntBridge.lean](ZeroParadox/ZPJ_OntBridge.lean), [ZPJ_Model.lean](ZeroParadox/ZPJ_Model.lean), [ZPJ_ScaleBridge.lean](ZeroParadox/ZPJ_ScaleBridge.lean) | ValuationStructure → AbstractSelfApp → AFAStructure; DC-free Aczel uniqueness; ValBridge common ancestor unifying the lattice track and ℤ₂; concrete ℤ₂ and ℕ∞ instances | Clean - June 2026 |
| ZP-J APG Decoration Uniqueness | [ZPJ_APG.lean](ZeroParadox/ZPJ_APG.lean) | Decoration uniqueness for finite accessible pointed graphs, by induction on reachable size | Clean - May 2026 |
| ZP-J Wheel of Fractions | [ZPJ_Wheel.lean](ZeroParadox/ZPJ_Wheel.lean), [ZPJ_WheelFrac.lean](ZeroParadox/ZPJ_WheelFrac.lean) | The wheel of fractions is a wheel (Carlström Def 1.1), choice-free; ∞ ≠ ⊥ | Clean - June 2026 |
| ZP-K Computational Grounding | [ZPK.lean](ZeroParadox/ZPK.lean) | Computational grounding via a Kleene fixed point; the snap closed concretely | Clean - April 2026 |
| ZP-L Incomputability Convergence | [ZPL.lean](ZeroParadox/ZPL.lean) | ε₀ as the exact snap threshold; the ordinal tower converges 2-adically to 0 | Clean - May 2026 |
| ZP-M Kleene-Ordinal Bridge | [ZPM.lean](ZeroParadox/ZPM.lean) | Type bridge MachinePhase → ℤ₂; Kleene quine and ε₀ fixed point co-witnessed | Clean - May 2026 |
| ZP-P The Fixed-Point Fork | [ZPP.lean](ZeroParadox/ZPP.lean), [ZPP_Ostrowski.lean](ZeroParadox/ZPP_Ostrowski.lean), [ZPP_Coalgebra.lean](ZeroParadox/ZPP_Coalgebra.lean) | The least/greatest fixed-point fork collapses iff the operator has a unique fixed point (choice-free); number-system instance ℝ vs ℚ₂ via Ostrowski; categorical-parent instance (Fix empty / Cofix inhabited) via QPF | Clean - June 2026 |
| Keystone probes (Lawvere / boundary) | [ZPJ_Lawvere.lean](ZeroParadox/ZPJ_Lawvere.lean), [ZPJ_Boundary.lean](ZeroParadox/ZPJ_Boundary.lean), [ZPJ_BoundaryBridge.lean](ZeroParadox/ZPJ_BoundaryBridge.lean) | Face-relative Lawvere verdict (no Set-level face an instance, computability face genuine); the snap as a well-foundedness boundary crossing (relation level + QPF μ/ν bridge); best-effort, full Taylor coalgebraic version open (Tier 6) | Clean - June 2026 |

<details>
<summary><b>Per-file axiom footprint</b> - click to expand</summary>

All proofs are machine-checked. The classical axioms that appear (`Classical.choice`) come from Mathlib's computability, analysis, and ordinal libraries — they are infrastructure dependencies, not Zero Paradox commitments, and `Classical.choice` in Lean is distinct from the set-theoretic Axiom of Choice.

ZP-H, ZP-I, ZP-J (extension files), ZP-K, ZP-L, and ZP-M use `Classical.choice` via Mathlib computability, analysis, and ordinal infrastructure (Kleene's theorem, Roger's fixed-point theorem, metric space completion, ordinal arithmetic, and p-adic valuation). `Classical.choice` is the Lean kernel axiom that grounds classical excluded middle; it does not introduce non-constructive selection over infinite families of sets. The `#print axioms` check reports `[propext, Classical.choice, Quot.sound]` across ZP-I, ZP-K, ZP-L, ZP-M, and the ZP-J extension files (ZPJ_Scale, ZPJ_Model, ZPJ_APG); the classical axioms enter through Code/Partrec, analysis machinery, ordinal fixed-point theory, and p-adic library infrastructure, not through the ZPSemilattice or AFAStructure fields. The ZP-J core file (ZPJ.lean) and ZPJ_AczelConn, ZPJ_SelfApp, ZPJ_OntBridge, and ZPJ_WheelFrac are `Classical.choice`-free. ZP-P is mixed: the fork core (ZPP.lean — `fork_collapse_iff`, `fix_isEmpty`) is choice-free `[propext, Quot.sound]`, while the Ostrowski number-system instance (ZPP_Ostrowski.lean — `real_not_equiv_padic`, `completions_exhaustive`) and the greatest-fixed-point side of the coalgebra instance (ZPP_Coalgebra.lean — `cofix_nonempty`) carry `Classical.choice`. ZP-A through ZP-G are `Classical.choice`-free except where standard Mathlib theorems require it. The keystone probe files are mixed: ZPJ_Lawvere's `fixedPoint_of_witness` / `no_witness_of_fixedPointFree` and ZPJ_Boundary's `floor_not_wellFounded` are **fully axiom-free** (`#print axioms` reports no dependencies at all); the remaining results (the Lawvere face negatives, `computability_face_fixedPoint`, the ordinal-ascent and carrier theorems, and `snap_boundary_two_registers`) carry `Classical.choice` via Mathlib's ordinal, recursion-theorem, and QPF machinery.

</details>

---

*This ledger is maintained alongside `AxiomProfile.lean`, `fmc.md`, and `register.md`. On any change to a claim's status or axiom profile, update those sources first, then this view.*
