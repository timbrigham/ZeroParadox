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
