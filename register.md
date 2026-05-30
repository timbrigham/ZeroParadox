> **A note on transparency:** This file lives in the public repository but is intentionally unlinked from the main project index. It is a canonical version registry used during active development to keep README.md and GUIDE.md in sync. The main entry point for the Zero Paradox is [README.md](README.md).

# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table and GUIDE.md Reading Paths are verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.14 | ZP-A_Lattice_Algebra.pdf | v1.9 | STALE | v1.14: CC-2 label → Forced Metatheoretic Commitment; ZPJ_ScaleBridge reference added — formal:c20e847b comp:37db9ee0 |
| ZP-B p-Adic Topology | v1.9 | ZP-B_pAdic_Topology.pdf | v1.10 | STALE | v1.9: K-17 vocab fix — "First Atomic State" → "minimum nonzero state, ε₀" in §I; comp v1.10: vocab sweep — "null state (0)" → "zero (0)" — formal:75ac399e comp:6117d309 |
| ZP-F The Counterexamples | v1.3 | ZP-F_The_Counterexamples.pdf | v1.12 | STALE | v1.3: K-16 vocab fix; comp v1.12: vocab sweep — null state fix — formal:ed2402fd comp:4f8d9904 |
| ZP-C Information Theory | v1.15 | ZP-C_Information_Theory.pdf | v2.6 | STALE | v1.15: K-19/K-21 vocab fixes; comp v2.6: vocab sweep — null state fixes throughout — formal:a7dbf220 comp:8eb51699 |
| ZP-D State Layer | v1.11 | ZP-D_State_Layer.pdf | v1.11 | STALE | v1.11: K-11/K-18 vocab fixes — "Topological Isolation" → "Clopen Separation" in DP-1; "first atomic state" → "minimum nonzero state"; comp v1.11: vocab sweep — null state fixes — formal:7f432037 comp:a37151e6 |
| ZP-E Bridge Document | v3.17 | ZP-E_Bridge_Document.pdf | v1.11 | STALE | v1.11 comp: Goodstein/proof-theoretic context for ε₀; K-3/K-4 vocab fixes (null state → ⊥; ontological → structural) — formal:323bd69e comp:1b4c17b0 |
| ZP-G Category Theory | v1.10 | ZP-G_Category_Theory.pdf | v1.8 | STALE | v1.10: hash sync — script modified without full workflow; rebuilt to sync; comp v1.8: category_diagram overlap fix — fixed cy, dh increased, redundant title removed — formal:f9ceca3f comp:0673dc77 |
| ZP-H Categorical Bridge | v1.14 | ZP-H_Categorical_Bridge.pdf | v1.13 | STALE | v1.14: K-13 vocab fix + endnote version corrected (v1.10→v1.14); comp v1.13: "any state change" scoped to "transition from bottom state in this framework (ZP-C T1b)" — Category 5 precision fix — formal:1e26ca53 comp:5e23b02f |
| ZP-I Inside Zero | v1.9 | ZP-I_Inside_Zero.pdf | v1.12 | STALE | Companion v1.12: disclaimer leads with p-adic math before brand name (AR fix) — formal:298f2e30 comp:e96e1bd9 |
| ZP-J Self-Reference | v2.0 | ZP-J_Self_Reference.pdf | v1.13 | STALE | v2.0: Sections VII-X added; comp v1.13: disclaimer leads with AFA math before brand name (AR fix) — formal:f39311c3 comp:ad356233 |
| ZP-J AFA Addendum | v1.1 | ZP-J_AFA_Addendum.pdf | N/A | N/— | v1.1: COMP_BLUE header banner added — formal:c6be6b33 |
| ZP-K Computational Grounding | v1.6 | ZP-K_Computational_Grounding.pdf | v1.8 | STALE | Companion v1.8: strip footer version — formal:8c00d4aa comp:1286a4a7 |
| ZP-L Incomputability Convergence | v1.0 | ZP-L_Incomputability_Convergence.pdf | v1.4 | STALE | Companion v1.4: strip footer version — formal:7825902f comp:fb745d9b |
| ZP-M Kleene-Ordinal Bridge | v1.0 | ZP-M_Kleene_Ordinal_Bridge.pdf | v1.2 | N/— | v1.0: Initial release — snapEmbed type bridge, hfp gap closed, zpm_triangle, R-M.1. Lean source promoted to full document; comp v1.2: HTML entity fix; validate_drawing wired; triangle dh increased; internal caption removed (overlapped edge label) — formal:24dd8909 comp:d264b283 |
| Zero Paradox Foreword | v2.5 | Zero_Paradox_Foreword.pdf | N/A | N/A | v2.5: AR/ER fixes — "standard ZFC" → "ZF" in porthole; fix() guard; "every" → "every finite" self-referential graph (Fintype scope) — formal:e475b28a |
| ZP Philosophical Question | v1.11 | ZP_Philosophical_Question.pdf | N/A | N/A | v1.11: fix() guard via Paragraph override; "bridge" → "connecting argument"; "in ZP's reading" de-duplicated — formal:9b4905de |

**Comp AR column key:** `Y/Y` = current comp hash adversary-reviewed + remediated (or confirmed clean). `Y/N` = reviewed, fixes identified but not yet applied. `N/—` = not yet reviewed.

*Last updated: May 2026*

---

## Script Hash Verification + AR Tracking

The `formal:XXXXXXXX comp:XXXXXXXX` tokens in the Notes column above are SHA-256 (first 8 chars) fingerprints of the corresponding build scripts in `.claude-local/`. The `Comp AR` column tracks adversary-review status for each companion, backed by `.claude-local/ar_status.json`.

**Session start** — run once before touching any build script:
```
python .claude-local/check_hashes.py
```
A hash `MISMATCH` means a script was modified without a version bump and PDF rebuild. An AR status of `STALE` means the companion script changed since its last adversary review — re-review required before merge.

**Post-fix workflow** — after applying adversary-review fixes, rebuilding the PDF, and updating the hash in register.md, run one command to close the loop:
```
python .claude-local/check_hashes.py --mark-remediated ZP-X
```
This computes the current comp hash, writes it to `ar_status.json` as remediated, and updates the `Comp AR` column in this file automatically. For fixes identified but not yet applied, use `--mark-reviewed ZP-X` instead (sets Y/N).
