> **A note on transparency:** This file lives in the public repository but is intentionally unlinked from the main project index. It is a canonical version registry used during active development to keep README.md and GUIDE.md in sync. The main entry point for the Zero Paradox is [README.md](README.md).

# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table and GUIDE.md Reading Paths are verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.13 | ZP-A_Lattice_Algebra.pdf | v1.8 | Y/Y | Companion v1.8: strip version number from CC-2 section cross-ref — formal:130d0acd comp:41081132 |
| ZP-B p-Adic Topology | v1.8 | ZP-B_pAdic_Topology.pdf | v1.8 | Y/Y | Companion v1.8: "dense" → "densely ordered"; ℚ₂ no-minimum clarification added; ε₀ framework note added; VERSION bump fix; "singularity" → valuation gap; remember box universe-contingent claim removed — formal:42af38ce comp:454decc4 |
| ZP-F The Counterexamples | v1.2 | ZP-F_The_Counterexamples.pdf | v1.10 | Y/Y | v1.2: vocab fix + dual-limit remark bullets (AR-clean); companion v1.10: new §VIII squeeze-as-structural-necessity (AR-clean) — formal:72f2aed0 comp:6935af00 |
| ZP-C Information Theory | v1.14 | ZP-C_Information_Theory.pdf | v2.1 | Y/Y | v1.14: version number removed from Open Items Register header — formal:273410c8 comp:5d88ff1e |
| ZP-D State Layer | v1.10 | ZP-D_State_Layer.pdf | v1.7 | Y/Y | v1.10: version number removed from Open Items Register header — formal:ed26f6c9 comp:198ff647 |
| ZP-E Bridge Document | v3.16 | ZP-E_Bridge_Document.pdf | v1.9 | Y/Y | v3.16: version numbers removed from register section headers — formal:c8732b44 comp:3754260f |
| ZP-G Category Theory | v1.9 | ZP-G_Category_Theory.pdf | v1.5 | Y/Y | v1.9: version number removed from Open Items Register header — formal:e6c366d4 comp:869c0ccc |
| ZP-H Categorical Bridge | v1.13 | ZP-H_Categorical_Bridge.pdf | v1.4 | Y/Y | v1.13: version number removed from Open Items Register header — formal:1f9d6ae2 comp:8f504038 |
| ZP-I Inside Zero | v1.9 | ZP-I_Inside_Zero.pdf | v1.4 | Y/Y | Companion v1.4: strip ZPI.lean version refs; disclaimer updated — formal:298f2e30 comp:a5d6bdee |
| ZP-J Self-Reference | v1.2 | ZP-J_Self_Reference.pdf | v1.4 | Y/Y | Companion v1.4: strip version from disclaimer cross-ref — formal:1dd8e34f comp:0a72dda0 |
| ZP-K Computational Grounding | v1.6 | ZP-K_Computational_Grounding.pdf | v1.7 | Y/Y | Companion v1.7: fix four_way_diagram String() HTML entity encoding (⊥ ≤ ∨ as raw Unicode) — formal:8c00d4aa comp:4e347005 |
| ZP-L Incomputability Convergence | v1.0 | ZP-L_Incomputability_Convergence.pdf | v1.3 | Y/Y | Companion v1.3: Gentzen/ε₀ proof-theoretic ordinal section added; AR-clean — formal:7825902f comp:812be345 |

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
