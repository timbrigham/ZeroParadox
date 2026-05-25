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
