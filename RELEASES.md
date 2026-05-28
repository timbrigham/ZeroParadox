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
| ZP-M Kleene-Ordinal Bridge | Lean source only (ZPM.lean) — PDF pending |

**Next threshold:** v2.1 on first substantive reviewer feedback round addressed after v2.0; v3.0 if another new formal layer is added (ZP-N constructive ordinal validation is the current candidate).

---

## v2.1 - 2026-05-28

**Why this release:** ZP-J v2.0 is a major document update (seven new sections added: Aczel DC-free connection, ValuationStructure→AbstractSelfApp→AFAStructure abstraction chain, concrete instances, APG decoration uniqueness). The ZPJ Lean sub-layer is correspondingly expanded with a complete sorry-free chain from valuation structure through APG decoration uniqueness — the most substantial new formal content since v2.0.

**What changed:**
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
| ZP-M Kleene-Ordinal Bridge | Lean source only (ZPM.lean) — PDF pending |

**Next threshold:** v2.2 on next substantive reviewer feedback round; v3.0 on new formal layer (ZP-N constructive ordinal validation remains the current candidate).
