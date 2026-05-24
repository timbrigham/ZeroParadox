> **A note on transparency:** This file lives in the public repository but is intentionally unlinked from the main project index. It is a canonical version registry used during active development to keep README.md and GUIDE.md in sync. The main entry point for the Zero Paradox is [README.md](README.md).

# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table and GUIDE.md Reading Paths are verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.13 | ZP-A_Lattice_Algebra.pdf | v1.6 | Y/Y | Companion v1.6: disclaimer "formal ontology" → "formal document" — formal:130d0acd comp:b47e99d6 |
| ZP-B p-Adic Topology | v1.8 | ZP-B_pAdic_Topology.pdf | v1.8 | Y/Y | Companion v1.8: "dense" → "densely ordered"; ℚ₂ no-minimum clarification added; ε₀ framework note added; VERSION bump fix; "singularity" → valuation gap; remember box universe-contingent claim removed — formal:42af38ce comp:454decc4 |
| ZP-F The Counterexamples | v1.1 | ZP-F_The_Counterexamples.pdf | v1.9 | Y/Y | Companion v1.9: comparison table "isolated" → "valuatively distinct" (kill-level AR fix) — formal:52672134 comp:ea91ad01 |
| ZP-C Information Theory | v1.13 | ZP-C_Information_Theory.pdf | v1.9 | Y/Y | Companion v1.9: "informational singularity" defined in first paragraph — formal:45164ac2 comp:af22429f |
| ZP-D State Layer | v1.9 | ZP-D_State_Layer.pdf | v1.7 | Y/Y | Companion v1.7: disclaimer updated — formal:a80de810 comp:198ff647 |
| ZP-E Bridge Document | v3.14 | ZP-E_Bridge_Document.pdf | v1.8 | Y/Y | Companion v1.8: title "converge" → "four frameworks, one event"; diagram captions "independent proof" → "independent mathematical description" — formal:f6326831 comp:a4cf4aa1 |
| ZP-G Category Theory | v1.8 | ZP-G_Category_Theory.pdf | v1.5 | Y/Y | Companion v1.5: "Informational Singularity" section renamed/rewritten — structural surprisal definition; section title → "Informational Asymmetry of 0" — formal:bde00483 comp:869c0ccc |
| ZP-H Categorical Bridge | v1.12 | ZP-H_Categorical_Bridge.pdf | v1.4 | Y/Y | Companion v1.4: structural floor section added; snap diagram overlap fixed (internal title removed, dh increased) — formal:d14f2b36 comp:8f504038 |
| ZP-I Inside Zero | v1.9 | ZP-I_Inside_Zero.pdf | v1.2 | Y/Y | Companion v1.2: disclaimer + opener updated — formal:298f2e30 comp:2b408089 |
| ZP-J Self-Reference | v1.2 | ZP-J_Self_Reference.pdf | v1.3 | Y/Y | Companion v1.3: disclaimer updated; formal doc: "asserted coincidence" removed — formal:1dd8e34f comp:39ff4bac |
| ZP-K Computational Grounding | v1.6 | ZP-K_Computational_Grounding.pdf | v1.3 | Y/Y | Companion v1.3: "IS the Turing machine" → "IS an instance of a Turing machine" — formal:8c00d4aa comp:409a45d1 |
| ZP-L Incomputability Convergence | v1.0 | ZP-L_Incomputability_Convergence.pdf | — | N/— | Initial release: axiom footprint convergence, Roger fixed-point stability, ε₀ as snap threshold, CNF bridge, Kleene-ordinal bridge, canonical snap map — formal:7825902f comp:— |

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
