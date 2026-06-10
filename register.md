> **A note on transparency:** This file lives in the public repository but is intentionally unlinked from the main project index. It is a canonical version registry used during active development to keep README.md and GUIDE.md in sync. The main entry point for the Zero Paradox is [README.md](README.md).

# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table and GUIDE.md Reading Paths are verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.14 | ZP-A_Lattice_Algebra.pdf | v1.9 | STALE | v1.14: CC-2 label → Forced Metatheoretic Commitment; ZPJ_ScaleBridge reference added — formal:c20e847b comp:37db9ee0 |
| ZP-B p-Adic Topology | v1.9 | ZP-B_pAdic_Topology.pdf | v1.10 | STALE | v1.9: K-17 vocab fix — "First Atomic State" → "minimum nonzero state, ε₀" in §I; comp v1.10: vocab sweep — "null state (0)" → "zero (0)" — formal:75ac399e comp:6117d309 |
| ZP-F The Counterexamples | v1.4 | ZP-F_The_Counterexamples.pdf | v1.12 | STALE | v1.4: vocab fix — "null state" → "⊥" in preamble; palette rebuild — formal:b04efdb1 comp:4f8d9904 |
| ZP-C Information Theory | v1.17 | ZP-C_Information_Theory.pdf | v2.6 | STALE | v1.17: version strings removed from Remark R5 label_box (li/label_box gate gap) — formal:8932e8eb comp:8eb51699 |
| ZP-D State Layer | v1.11 | ZP-D_State_Layer.pdf | v1.11 | STALE | v1.11: K-11/K-18 vocab fixes — "Topological Isolation" → "Clopen Separation" in DP-1; "first atomic state" → "minimum nonzero state"; comp v1.11: vocab sweep — null state fixes — formal:7f432037 comp:a37151e6 |
| ZP-E Bridge Document | v3.19 | ZP-E_Bridge_Document.pdf | v1.11 | STALE | v3.19: version string removed from T-BUF li() call (li/label_box gate gap) — formal:9a471539 comp:1b4c17b0 |
| ZP-G Category Theory | v1.11 | ZP-G_Category_Theory.pdf | v1.8 | STALE | v1.11: local make_doc override removed; version subheader style fixed; version refs stripped from body prose; palette rebuild — formal:0a34ff48 comp:0673dc77 |
| ZP-H Categorical Bridge | v1.15 | ZP-H_Categorical_Bridge.pdf | v1.13 | STALE | v1.15: CC-1 framing updated — CC-1 is a derived theorem in ZP-J (cc1_derived, Lean 4); version ref stripped; palette rebuild — formal:d5a30ab9 comp:5e23b02f |
| ZP-H Native Categories Addendum | v1.0 | ZP-H_Native_Categories_Addendum.pdf | N/A | N/— | v1.0: Initial release — snap floor realized in native Mathlib categories: fB_functor → TopCat (⊥ = inverse limit ⋂ B(0,2⁻ⁿ) = {0}), fD_functor → ModuleCat ℂ (⊥ = StateSpace 0 initial; isometric embeddings), fC_functor → KleisliCat PMF (⊥ = Fin 0 initial; fC_no_return = AX-G2 as theorem); mc1_correspondence capstone. Correspondence half of MC-1 formal; identity half a commitment. Lean: ZPH_TopFunctor/ZPH_HilbFunctor/ZPH_InfoFunctor/ZPH_MC1.lean; [propext, Classical.choice, Quot.sound] — formal:25677fda |
| ZP-I Inside Zero | v1.10 | ZP-I_Inside_Zero.pdf | v1.21 | STALE | v1.10: vocab fixes — "null state" → "⊥"; version refs removed from body prose; palette rebuild — formal:f83a46d9 comp:f4707408 |
| ZP-J Self-Reference | v2.1 | ZP-J_Self_Reference.pdf | v1.23 | STALE | v2.1: version changelog removed from preamble; version strings stripped from section headers and endnote; "null state" → "⊥"; palette rebuild — formal:0bb21606 comp:9fd0957b |
| ZP-J AFA Addendum | v1.2 | ZP-J_AFA_Addendum.pdf | N/A | N/— | v1.2: version changelog removed from preamble; palette rebuild — formal:bb4ab5b8 |
| ZP-J Wheel Addendum | v1.0 | ZP-J_Wheel_Addendum.pdf | N/A | N/— | v1.0: Initial release — wheel of fractions ⊙_S A = (A×A)/≡_S is a Wheel (Carlström Def 1.1, 14 fields), choice-free [propext, Quot.sound]; inf_ne_bot porthole (∞≠⊥ given 0∉S). Lean: ZPJ_WheelFrac.lean; fix() guard added (PDF build standards) — formal:2d404fdb |
| ZP-K Computational Grounding | v1.7 | ZP-K_Computational_Grounding.pdf | v1.8 | STALE | v1.7: version changelog removed from preamble; stale v1.5 refs stripped; "description-instantiation gap" bypassed in DA-1 Path 2 context; palette rebuild — formal:0c822fa6 comp:1286a4a7 |
| ZP-L Incomputability Convergence | v1.0 | ZP-L_Incomputability_Convergence.pdf | v1.4 | STALE | Companion v1.4: strip footer version — formal:7825902f comp:fb745d9b |
| ZP-M Kleene-Ordinal Bridge | v1.0 | ZP-M_Kleene_Ordinal_Bridge.pdf | v1.2 | N/— | v1.0: Initial release — snapEmbed type bridge, hfp gap closed, zpm_triangle, R-M.1. Lean source promoted to full document; comp v1.2: HTML entity fix; validate_drawing wired; triangle dh increased; internal caption removed (overlapped edge label) — formal:24dd8909 comp:d264b283 |
| Zero Paradox Foreword | v2.7 | Zero_Paradox_Foreword.pdf | N/A | N/A | v2.7: §IV names Lawvere's fixed-point theorem as the recognized unification of the diagonal family (Cantor/Russell/Gödel fixed-point lemma/Kleene); fence firmed — ZP "locates" the diagonal fixed point, not "is". v2.6 added the keystone — formal:324c7977 |
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
