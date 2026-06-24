> **A note on transparency:** This file lives in the public repository but is intentionally unlinked from the main project index. It is the release history for GitHub releases and Zenodo snapshots. The main entry point for the Zero Paradox is [README.md](README.md).

# Zero Paradox - Release History

Each GitHub release triggers an automatic Zenodo snapshot with a permanent DOI. This file is the human-readable record of what warranted each release and what the next threshold is.

---

## v1.0 - 2026-05-07

**Why this release:** First public Zenodo snapshot. Ten formal layers fully verified sorry-free in Lean 4 + Mathlib. Zenodo integration established via `.zenodo.json`.

**What is included:**
- ZP-A through ZP-K (ten layers; ZP-F intentionally skipped)
- All formal PDFs and illustrated companions
- Lean 4 source with clean build (no sorries)
- Full scripts/ transparency copy of PDF build tooling

**Document versions at this release:**
| Document | Version |
|----------|---------|
| ZP-A Lattice Algebra | v1.13 |
| ZP-B p-Adic Topology | v1.6 |
| ZP-C Information Theory | v1.12 |
| ZP-D State Layer | v1.8 |
| ZP-E Bridge Document | v3.12 |
| ZP-G Category Theory | v1.7 |
| ZP-H Categorical Bridge | v1.11 |
| ZP-I Inside Zero | v1.8 |
| ZP-J Self-Reference | v1.1 |
| ZP-K Computational Grounding | v1.3 |

**Next threshold:** v1.1 on first substantive reviewer feedback round; v2.0 if a new formal layer is added or a major theorem status changes.

---

## v1.1 - 2026-05-09

**Why this release:** ZP-F (The Counterexamples) added - the Archimedean counterexample layer completing the ZP-F / ZP-B Ostrowski classification pair.

**What changed:**
- ZP-F added: formal layer, Lean proof (sorry-free), and illustrated companion
- Ostrowski classification notes cross-referenced in ZPF.lean and ZPB.lean
- Foreword v1.7: ZP-K Classical.choice dependency scoped as Lean infrastructure
- ZP-J companion v1.1: CC-2 status corrected to metatheoretic commitment within ZF+AFA
- ABOUTME: Riemann sphere as early geometric intuition

**Document versions at this release:**
| Document | Version |
|----------|---------|
| ZP-F The Counterexamples | v1.0 (new) |
| ZP-F Illustrated Companion | v1.7 (new) |
| ZP-J Illustrated Companion | v1.1 |
| Foreword | v1.7 |

**Next threshold:** v1.2 on first substantive reviewer feedback round addressed; v2.0 if a new formal layer is added or a major theorem status changes.

---

## v2.0 - 2026-05-24

**Why this release:** Two new formal Lean layers added (ZP-L and ZP-M), clearing the stated v2.0 threshold. ZP-L establishes ε₀ as the exact ordinal snap threshold with 24 sorry-free theorems. ZP-M formally bridges the Kleene quine (ZP-K) and ordinal fixed-point (ZP-L) as the same diagonalization pattern.

**What changed:**
- ZP-L Incomputability Convergence: new formal layer — axiom footprint convergence, Roger fixed-point stability, ε₀ as snap threshold, 2-adic tower convergence to 0, Kleene-ordinal snap bridge, canonical snap map (24 theorems, sorry-free, May 2026)
- ZP-M Kleene-Ordinal Bridge: new formal Lean layer — snapEmbed type bridge (MachinePhase → ℤ_[2]), hfp closure theorem, zpm_triangle (ordinal-2adic-phase triangle co-proved), both_fixed_points_exist (Kleene and ε₀ fixed points in same formal context), Remark R-M.1 (DA-1 Path 2 retrospective analysis). Lean source only at this release; formal PDF document pending.
- ZP-K Computational Grounding: v1.3 → v1.6 — Lean proof completed sorry-free; ZPK.lean covers IsKleeneFixedPoint, selfApply_partrec, T-COMP four-way equivalence, da1_closed_concrete
- ZP-E Bridge Document: v3.12 → v3.15 — multiple adversary-review precision fixes; DA-1 Path 2 forward reference to ZP-M R-M.1 added
- ZP-B, ZP-C, ZP-D, ZP-F, ZP-G, ZP-H, ZP-I, ZP-J: accumulated adversary-review fixes and companion updates across all layers
- README: ZPM added to Lean verification table; Classical.choice necessity added to Question Register; purity note updated
- scripts/: three AR-2026-05-23 prose fixes synced (scope overclaim in Philosophical Question, reachability claim in Foreword, false universal in ZP-K companion)

**Document versions at v2.0:**
| Document | Version |
|----------|---------|
| ZP-A Lattice Algebra | v1.13 |
| ZP-B p-Adic Topology | v1.8 |
| ZP-C Information Theory | v1.13 |
| ZP-D State Layer | v1.9 |
| ZP-E Bridge Document | v3.15 |
| ZP-F The Counterexamples | v1.1 |
| ZP-G Category Theory | v1.8 |
| ZP-H Categorical Bridge | v1.12 |
| ZP-I Inside Zero | v1.9 |
| ZP-J Self-Reference | v1.2 |
| ZP-K Computational Grounding | v1.6 |
| ZP-L Incomputability Convergence | v1.0 (new) |
| ZP-M Kleene-Ordinal Bridge | Lean source only (ZPM.lean) at v2.0 — PDF added in v2.1 |

**Next threshold:** v2.1 on first substantive reviewer feedback round addressed after v2.0; v3.0 if another new formal layer is added (ZP-N constructive ordinal validation is the current candidate).

---

## v2.1 - 2026-05-28

**Why this release:** ZP-J v2.0 is a major document update (seven new sections added: Aczel DC-free connection, ValuationStructure→AbstractSelfApp→AFAStructure abstraction chain, concrete instances, APG decoration uniqueness). The ZPJ Lean sub-layer is correspondingly expanded with a complete sorry-free chain from valuation structure through APG decoration uniqueness — the most substantial new formal content since v2.0.

**What changed:**
- ZP-M Kleene-Ordinal Bridge: Lean source only → v1.0 full document — formal PDF and illustrated companion added. snapEmbed type bridge (MachinePhase → ℤ_[2]), hfp gap closed (hfp_from_epsilon_zero), zpm_triangle (all three triangle edges co-proved), both_fixed_points_exist, Remark R-M.1 (DA-1 Path 2 boundary). Companion v1.0 with triangle diagram and diagonalization pattern diagram.
- ZP-J Self-Reference: v1.2 → v2.0 — Sections VII-X added covering the DC-free Aczel fixed-point connection (ZPJ_AczelConn), the full abstraction chain (ZPJ_SelfApp, ZPJ_Scale, ZPJ_ScaleBridge, ZPJ_Model, ZPJ_OntBridge), and APG decoration uniqueness (ZPJ_APG). Companion v1.4 → v1.6 with five new sections matching the document. All adversary-reviewed.
- ZPJ Lean sub-layer (new sorry-free files): `ZPJ_SelfApp` (AbstractSelfApp typeclass), `ZPJ_Scale` (ValuationStructure + ℤ_[2] parallel), `ZPJ_ScaleBridge` (ValBridge drops ZPSemilattice constraint; formal ℤ_[2] instance closes AFA/ZFC gap), `ZPJ_Model` (ℕ∞ concrete instance with inverted order), `ZPJ_OntBridge` (OntologicalStates direct AbstractSelfApp path), `ZPJ_APG` (Accessible Pointed Graph definition + DecorationUniverse + decoration uniqueness proved via strong induction on reach cardinality)
- ZP-A Lattice Algebra: v1.13 → v1.14 — CC-2 label updated from "Conditional Claim" to "Forced Metatheoretic Commitment"; three-layer Lean scope note distinguishing ZFC-clean results, AFAStructure-conditional results, and prose-level set-theoretic commitment
- Foreword: v1.8 → v2.1 — orthogonal/contact-point framing for the ZFC/AFA relationship; CC-2 row updated to Forced Metatheoretic Commitment with Foundation/AFA dual framing
- Philosophical Question: v1.3 → v1.5 — §II addition: orthogonal framing, contact point v₂(0)=∞, machine-verified ZPJ_ScaleBridge result, AFA dependency made precise
- LEAN_CUSTOM_REGISTRY.md: new public document — register of all custom Lean definitions, typeclasses, and instances with Mathlib relationship and engineering rationale for each
- `[ZP-CUSTOM]` inline comments: 23 structured comments added across 13 Lean files, greppable format for register regeneration
- Companion fixes (across all layers): version numbers stripped from companion body prose and cross-document references per CLAUDE.md standing rule; ZP-C v1.13→v1.14, ZP-D v1.9→v1.10, ZP-E v3.15→v3.16, ZP-G v1.8→v1.9, ZP-H v1.12→v1.13 (Open Items Register header cleanup)
- scripts/: all modified build scripts synced to scripts/ folder

**Document versions at v2.1:**
| Document | Version |
|----------|---------|
| ZP-A Lattice Algebra | v1.14 |
| ZP-B p-Adic Topology | v1.8 |
| ZP-C Information Theory | v1.14 |
| ZP-D State Layer | v1.10 |
| ZP-E Bridge Document | v3.16 |
| ZP-F The Counterexamples | v1.2 |
| ZP-G Category Theory | v1.9 |
| ZP-H Categorical Bridge | v1.13 |
| ZP-I Inside Zero | v1.9 |
| ZP-J Self-Reference | v2.0 |
| ZP-K Computational Grounding | v1.6 |
| ZP-L Incomputability Convergence | v1.0 |
| ZP-M Kleene-Ordinal Bridge | v1.0 (new) |

**Next threshold:** v2.2 on next substantive reviewer feedback round; v3.0 on new formal layer (ZP-N constructive ordinal validation remains the current candidate).

---

## v2.2 - 2026-05-31

**Why this release:** K-series vocabulary round (K-11 through K-24) applied across all layers — systematic replacement of imprecise terms (topological isolation → clopen separation, first atomic state → minimum nonzero state, null state → ⊥). New sorry-free Lean proofs in ZPJ_APG. ZP-E companion Goodstein/proof-theoretic context for ε₀. Full palette standardization pass — all 16 PDFs rebuilt from zp_utils to ensure consistent colors and formatting across the document set.

**What changed:**
- ZP-B p-Adic Topology: v1.8 → v1.9 — K-17 vocab fix ("First Atomic State" → "minimum nonzero state, ε₀")
- ZP-C Information Theory: v1.14 → v1.17 — K-19/K-21 vocab fixes; null state → ⊥ throughout body prose; palette rebuild; companion v2.4 → v2.6; version strings removed from Remark R5 label_box
- ZP-D State Layer: v1.10 → v1.11 — K-11/K-18 vocab fixes; companion v1.9 → v1.11
- ZP-E Bridge Document: v3.16 → v3.19 — K-22 vocab fix; null state → ⊥ and version refs removed from body prose; palette rebuild; companion v1.10 → v1.11 (Goodstein/proof-theoretic context for ε₀); version string removed from T-BUF li() call
- ZP-F The Counterexamples: v1.2 → v1.4 — K-16 vocab fix; null state → ⊥ in preamble; palette rebuild; companion v1.10 → v1.12
- ZP-G Category Theory: v1.9 → v1.11 — local make_doc override removed; version subheader style fixed; version refs stripped from body prose; palette rebuild; companion v1.5 → v1.8
- ZP-H Categorical Bridge: v1.13 → v1.15 — K-13 vocab fix; CC-1 framing updated (derived theorem in ZP-J, not freestanding modelling commitment); version ref stripped; palette rebuild; companion v1.5 → v1.13
- ZP-I Inside Zero: v1.8 → v1.10 — null state → ⊥ and version refs removed from body prose; palette rebuild; companion updated
- ZP-J Self-Reference: v1.2 → v2.1 — Sections VII-X added; version changelog removed from preamble; version strings stripped from section headers and endnote; ZPJ_APG.lean val_iterate and scale_iterate_unique_fp proved sorry-free; companion v1.4 → v1.23
- ZP-J AFA Addendum: v1.0 → v1.2 — COMP_BLUE header banner added; version changelog removed from preamble; palette rebuild
- ZP-K Computational Grounding: v1.3 → v1.7 — Lean proof completed sorry-free; version changelog removed from preamble; stale version refs stripped; palette rebuild; companion v1.6 → v1.8
- ZP-L Incomputability Convergence: v1.0 — palette rebuild; companion v1.0 → v1.4
- ZP-M Kleene-Ordinal Bridge: v1.0 — palette rebuild; companion v1.0 → v1.2
- Foreword: v2.1 → v2.5 — porthole precision, ZF/ZFC scope, fix() coverage; palette rebuild
- Philosophical Question: v1.3 → v1.11 — bridge → connecting argument, scope fixes; palette rebuild
- README/GUIDE: Question Register Open Questions link; vocabulary and prose precision pass; version table updated
- LEAN_CUSTOM_REGISTRY.md: [ZP-CUSTOM] inline comments across 13 Lean files
- zp_utils: build gate added enforcing banned vocabulary and version-in-prose rules on all future PDF builds

**Document versions at v2.2:**
| Document | Version |
|----------|---------|
| ZP-A Lattice Algebra | v1.14 |
| ZP-B p-Adic Topology | v1.9 |
| ZP-C Information Theory | v1.17 |
| ZP-D State Layer | v1.11 |
| ZP-E Bridge Document | v3.19 |
| ZP-F The Counterexamples | v1.4 |
| ZP-G Category Theory | v1.11 |
| ZP-H Categorical Bridge | v1.15 |
| ZP-I Inside Zero | v1.10 |
| ZP-J Self-Reference | v2.1 |
| ZP-J AFA Addendum | v1.2 |
| ZP-K Computational Grounding | v1.7 |
| ZP-L Incomputability Convergence | v1.0 |
| ZP-M Kleene-Ordinal Bridge | v1.0 |

**Next threshold:** v2.3 on next substantive reviewer feedback round; v3.0 on new formal layer.

---

## v2.3 - 2026-06-10

**Why this release:** Accumulated documentation and formal-content work since v2.2 - the ZP-J Wheel Addendum (the wheel of fractions proved a wheel, conjecture to theorem) and the diagonal fixed point keystone surfaced across the README and Foreword - a meaningful, reader-facing state of the framework.

**What changed:**
- ZP-J Wheel Addendum: new v1.0 formal document - the wheel of fractions ⊙_S A = (A×A)/≡_S is a wheel (Carlström Definition 1.1, all eight axioms / 14 unbundled fields) for any commutative ring A and multiplicative submonoid S; choice-free (`[propext, Quot.sound]`); `inf_ne_bot` porthole (∞ ≠ ⊥ given 0 ∉ S). Machine-verified in `ZPJ_WheelFrac.lean` (Lean source predates this release). Carlström citation verified against the 2001:11 primary source. Linked in README and GUIDE.
- Foreword: v2.5 → v2.7 - §IV gains the diagonal fixed point keystone (⊥ as the same self-referential fixed point across the layers; Quine atom / Kleene quine / v₂(0)=∞ / categorical initial as faces; the Gödel inversion), anchored to Lawvere's fixed-point theorem as the recognized unification of the classical diagonal family. Honesty fence throughout - ZP situated in the Lawvere lineage, not claimed as a proved instance.
- README: front-matter overhaul (five rounds) - Central Result reordered (plain claim + scope lead, derivation chain folded); Framework tables condensed, Lean-verification table moved above the PDF table; Axiomatic Commitments table, closed Question Register items, and the Purity note folded into collapsible blocks; MC-1 surfaced as a visible note; internal labels de-jargoned from the cold-reader path.
- Naming conventions (CLAUDE.md + README): CC-2 presented as "the Quine atom" (additive); the keystone named "the diagonal fixed point."
- `.zenodo.json`: ZP-J clause updated to include the wheel of fractions; ZP-F phrasing aligned to "ordered fields" (with a matching README tweak).

**Document versions at v2.3:**
| Document | Version |
|----------|---------|
| ZP-A Lattice Algebra | v1.14 |
| ZP-B p-Adic Topology | v1.9 |
| ZP-C Information Theory | v1.17 |
| ZP-D State Layer | v1.11 |
| ZP-E Bridge Document | v3.19 |
| ZP-F The Counterexamples | v1.4 |
| ZP-G Category Theory | v1.11 |
| ZP-H Categorical Bridge | v1.15 |
| ZP-I Inside Zero | v1.10 |
| ZP-J Self-Reference | v2.1 |
| ZP-J AFA Addendum | v1.2 |
| ZP-J Wheel Addendum | v1.0 (new) |
| ZP-K Computational Grounding | v1.7 |
| ZP-L Incomputability Convergence | v1.0 |
| ZP-M Kleene-Ordinal Bridge | v1.0 |

**Next threshold:** v3.0 on a new formal layer (ZP-N constructive ordinal validation candidate); a v2.4 doc release if the OQ-G3 / MC-1-theorem work lands (MC-1's correspondence upgraded from modeling commitment to theorem).

---

## v2.4 - 2026-06-11

**Why this release:** The OQ-G3 / MC-1 work landed - the snap floor is now realized as genuine functors into the real domain categories, MC-1's correspondence half is formal, and the choice-free core is surfaced as a checkable artifact - the v2.4 doc release the v2.3 threshold anticipated, plus accumulated cleanup.

**What changed:**
- MC-1 remediation / OQ-G3: the snap floor realized as sorry-free Lean `CategoryTheory.Functor` terms into the real Mathlib categories - F_B into `TopCat` (⊥ = the inverse limit of the clopen-ball tower, ⋂ B(0,2⁻ⁿ) = {0}), F_D into `ModuleCat ℂ` (⊥ = `StateSpace 0`, the initial zero object; embeddings proved isometric), F_C into `KleisliCat PMF` (⊥ = `Fin 0` initial, with no stochastic map returning to it - AX-G2 realized as a theorem). Bundled as `mc1_correspondence`. MC-1's correspondence half is upgraded from a modeling commitment to a formal result; the literal cross-category identity stays a chosen commitment (the residue). New Lean files `ZPH_TopFunctor`/`ZPH_HilbFunctor`/`ZPH_InfoFunctor`/`ZPH_MC1`. The earlier ℕ-shaped proxy categories are superseded; the ZP-H "OQ-G3 fully closed" docstring overclaim was corrected.
- ZP-H Native Categories Addendum: new v1.0 formal document presenting the above ("The Snap Floor in Native Categories"). Linked in README and GUIDE.
- The Choice-Free Core: new v1.0 framework-wide addendum, plus the checkable artifact `ZeroParadox/AxiomProfile.lean` - the central theorem T-SNAP is machine-verified to depend on no axioms at all; the lattice (ZP-A) and the Quine-atom self-reference (ZP-J) are choice-free; `Classical.choice` is confined to the analytic realizations, inherited from Mathlib, with its necessity there open. Surfaced in README (Central Result, Formal Verification, Question Register) and recorded as the lead outreach artifact.
- Question Register restructure: split into genuinely-open questions, a new **Design Commitments** table (Temperature T parameter, DP-2, MC-1 identity), and resolved-with-commitment. DA-1 moved to resolved (closed given DP-2; "Path 2" reframed as a foundational commitment, not a gap); OQ-G3 moved to resolved (functor construction closed). Verification-status and Classical.choice rows sharpened.
- Engineer's Takes: filled in Tim's voice for the four new functor files, ZP-L, and AxiomProfile; a hard pre-release gate added to CLAUDE.md (no release while any `TODO (Tim)` Engineer's Take is unfilled).
- Naming convention (CLAUDE.md): MC-1 status convention (correspondence derived / identity a commitment; additive, no new readable name).
- Cleanup: `.gitignore` now ignores all `*.log`; `.zenodo.json` description updated (choice-free core + the native-category functors).

**Document versions at v2.4:**
| Document | Version |
|----------|---------|
| ZP-A Lattice Algebra | v1.14 |
| ZP-B p-Adic Topology | v1.9 |
| ZP-C Information Theory | v1.17 |
| ZP-D State Layer | v1.11 |
| ZP-E Bridge Document | v3.19 |
| ZP-F The Counterexamples | v1.4 |
| ZP-G Category Theory | v1.11 |
| ZP-H Categorical Bridge | v1.15 |
| ZP-H Native Categories Addendum | v1.0 (new) |
| ZP-I Inside Zero | v1.10 |
| ZP-J Self-Reference | v2.1 |
| ZP-J AFA Addendum | v1.2 |
| ZP-J Wheel Addendum | v1.0 |
| ZP-K Computational Grounding | v1.7 |
| ZP-L Incomputability Convergence | v1.0 |
| ZP-M Kleene-Ordinal Bridge | v1.0 |
| ZP Choice-Free Core Addendum | v1.0 (new) |

**Next threshold:** v3.0 on a new formal layer (ZP-N constructive-ordinal validation, which doubles as the unit test for the Classical.choice-necessity question); a v2.5 doc release on the next substantive reviewer-feedback round or accumulated documentation work.

---

## v2.5 - 2026-06-17

**Why this release:** ZP-P "The Fixed-Point Fork" added as a synthesis layer, plus the new ZP-J Wheel illustrated companion and a project-wide rendered-version cleanup (C1). A minor doc release per the v2.4 threshold: ZP-P proves no new foundational result, so v3.0 stays reserved for a new foundational layer.

**What changed:**
- ZP-P The Fixed-Point Fork: new synthesis layer (PDF + Lean `ZPP.lean` / `ZPP_Coalgebra.lean` / `ZPP_Ostrowski.lean`, wired into `Basic.lean`). The μ/ν fork schema (least and greatest fixed point collapse to one point iff the self-map has a unique fixed point) is choice-free `[propext, Quot.sound]`; the categorical-parent instance (the leaf-free functor's W-type empty / M-type inhabited) and the number-system instance (ℝ vs ℚ₂ via Ostrowski) are theorem-backed, with `Classical.choice` confined to the non-well-founded / analytic realizations and inherited from Mathlib. Three tiers (schema / instances / unification); hard fence (cross-instance identity = type boundary) and soft fence (not every fork is μ/ν). Renamed from ZP-O to avoid O/0 collision in a zero-themed framework. Engineer's Takes filled in Tim's voice (the choice boundary: the framework-defining theorems are choice-free, the tooling realizations carry inherited choice).
- ZP-J Wheel Illustrated Companion v1.0: new plain-language companion for the wheel of fractions (division by zero made total; ∞ = /0, ⊥ = 0·/0; wheel-vs-meadow diagram).
- ZP-J Self-Reference companion v1.24 → v1.25: APG directed-graph diagram and depth/analogy fixes (Dan feedback); §6 future-work bridge retired (the 2-adic argument is now formalized); ValBridge common-ancestor framing and a ℤ₂ model added; ScaleBridge wired into the maintained build with its Engineer's Take.
- C1 cleanup: rendered self-version references stripped across 11 documents (a document's own version now appears only on the subtitle / footer meta line); glyph and vocab fixes; the no-rendered-changelog rule codified in CLAUDE.md.
- Hotfix: a leaked private-note phrase removed from the `ZPJ_WheelFrac.lean` docstring (surfaced in Bergstra correspondence).
- `.zenodo.json`: updated to fourteen layers (ZP-P added, with the choice fence).

**Document versions at v2.5:**
| Document | Version |
|----------|---------|
| ZP-A Lattice Algebra | v1.14 |
| ZP-B p-Adic Topology | v1.10 |
| ZP-C Information Theory | v1.18 |
| ZP-D State Layer | v1.12 |
| ZP-E Bridge Document | v3.20 |
| ZP-F The Counterexamples | v1.4 |
| ZP-G Category Theory | v1.12 |
| ZP-H Categorical Bridge | v1.16 |
| ZP-H Native Categories Addendum | v1.0 |
| ZP-I Inside Zero | v1.11 |
| ZP-J Self-Reference | v2.2 |
| ZP-J AFA Addendum | v1.3 |
| ZP-J Wheel Addendum | v1.0 |
| ZP-J Wheel Illustrated Companion | v1.0 (new) |
| ZP-K Computational Grounding | v1.7 |
| ZP-L Incomputability Convergence | v1.1 |
| ZP-M Kleene-Ordinal Bridge | v1.1 |
| ZP-P The Fixed-Point Fork | v1.1 (new) |
| ZP Choice-Free Core Addendum | v1.0 |

**Next threshold:** v3.0 on a new foundational layer (ZP-N constructive-ordinal validation, the unit test for the Classical.choice-necessity question); a further v2.x doc release on the next substantive reviewer-feedback round or accumulated documentation work.

---

## v2.6 - 2026-06-24

**Why this release:** Consolidates the un-tagged v2.5 (ZP-P "The Fixed-Point Fork" layer) with the subsequent framework-wide prior-art / transparency pass and the keystone investigation - the Lawvere face-split and the well-foundedness boundary - into one Zenodo snapshot. v2.5 was written to this file but never tagged; v2.6 supersedes it and reflects the current state of main.

**What changed (since the last tagged release, v2.4):**
- **ZP-P "The Fixed-Point Fork"** (the 14th layer, originally staged as v2.5): the mu/nu fork schema (least vs greatest fixed point collapse to one point iff the self-map has a unique fixed point) choice-free `[propext, Quot.sound]`; the categorical-parent (W-type empty / M-type inhabited) and number-system (R vs Q_2 via Ostrowski) instances theorem-backed. Renamed from ZP-O to avoid an O/0 collision. Now at v1.3 after the Veltri correction below.
- **Prior-art pass + Claims Ledger:** a new "Convergence with established work" ledger in CLAIMS.md maps each ZP face to the established prior art that owns it - Lawvere/Yanofsky, Aczel/Forti-Honsell/Paulson, Ostrowski, Gentzen, Kleene, Lambek/Adamek-Rutten/Veltri/Ahrens, Carboni-Lack-Walters/Fritz, van der Put/Kozyrev, Carlstroem, Chaitin - each with an honest delta and credit pointing outward. Citations added across ZP-D (van der Put / Kozyrev p-adic ball-indicator ONB), ZP-G/H (strict initial objects / Markov categories), and ZP-P (Veltri FSCD 2021, which corrected the nu-side choice claim from "structural" to a Mathlib artifact).
- **Keystone arc:** the new ZP-J Keystone Addendum plus Lean (ZPJ_Lawvere, ZPJ_Boundary, ZPJ_BoundaryBridge). The Lawvere face-split is machine-checked (in Set no face is a Lawvere instance - Cantor; the computability face is a genuine recursion-theorem instance). The binary snap is framed as a crossing of the well-foundedness boundary (Taylor / Adamek-Milius-Moss) - relation level plus a QPF mu/nu bridge, best-effort, with the full Taylor coalgebraic version flagged open (Mathlib lacks the next-time operator, Pataraia's theorem, and the General Recursion Theorem). Honest fences throughout: the single-carrier picture carries no new commitment beyond the framework's existing bottom/epsilon-0 identification (MC-1 / OQ-E2), and the endpoints are proved (the floor non-well-founded via the real bottom, axiom-free).
- **FMC defined and applied:** fmc.md publishes the Forced Metatheoretic Commitment rubric (argued-not-proved, with a named falsifier - a disciplined form of intrinsic justification); the FMC uniformity sweep softened AFA-necessity language from "forced/derived" to "argued" across ZP-A, ZP-E, the Foreword, and companions.
- **Transparency + reproducibility:** CLAIMS.md is the claim-level ledger (proved / argued / committed / open tiers, verified against live `#print axioms` via AxiomProfile.lean); a README "Reproducing the verification" section (clone, toolchain pin, lake build, axiom profile).
- **C8 dual-date templating:** every document's meta line now renders "Initial / Current" dates from a single source (drift-proof); rendered self-version changelogs retired across the corpus.
- **Process controls:** a prior-art review gate (synthesis-layer detection routing to a deep literature-scout review); Lean namespace standardization (namespace = filename stem); a line-ending policy (.gitattributes, eol=lf) so build-script hash fingerprints are byte-stable across machines.

**Document versions at v2.6:**
| Document | Version |
|----------|---------|
| ZP-A Lattice Algebra | v1.17 |
| ZP-B p-Adic Topology | v1.11 |
| ZP-C Information Theory | v1.19 |
| ZP-D State Layer | v1.14 |
| ZP-E Bridge Document | v3.22 |
| ZP-F The Counterexamples | v1.5 |
| ZP-G Category Theory | v1.14 |
| ZP-H Categorical Bridge | v1.17 |
| ZP-H Native Categories Addendum | v1.1 |
| ZP-I Inside Zero | v1.12 |
| ZP-J Self-Reference | v2.3 |
| ZP-J AFA Addendum | v1.4 |
| ZP-J Wheel Addendum | v1.2 |
| ZP-J Keystone Addendum | v1.1 (new) |
| ZP-K Computational Grounding | v1.8 |
| ZP-L Incomputability Convergence | v1.2 |
| ZP-M Kleene-Ordinal Bridge | v1.2 |
| ZP-P The Fixed-Point Fork | v1.3 |
| Zero Paradox Foreword | v2.10 |
| ZP Philosophical Question | v1.12 |
| ZP Choice-Free Core Addendum | v1.2 |

**Next threshold:** v3.0 on a new foundational layer (ZP-N constructive-ordinal validation, the unit test for the Classical.choice-necessity question) or a theorem status change; a further v2.x on the next substantive reviewer-feedback round or accumulated documentation work.
