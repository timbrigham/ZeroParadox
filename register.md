> **A note on transparency:** This file lives in the public repository but is intentionally unlinked from the main project index. It is a canonical version registry used during active development to keep README.md and GUIDE.md in sync. The main entry point for the Zero Paradox is [README.md](README.md).

# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table and GUIDE.md Reading Paths are verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.14 | ZP-A_Lattice_Algebra.pdf | v1.9 | Y/Y | v1.14: CC-2 label → Forced Metatheoretic Commitment; ZPJ_ScaleBridge reference added — formal:c20e847b comp:d83fd4c7 |
| ZP-B p-Adic Topology | v1.8 | ZP-B_pAdic_Topology.pdf | v1.9 | Y/Y | Companion v1.9: strip version number from companion footer — formal:42af38ce comp:8e7b73c6 |
| ZP-F The Counterexamples | v1.2 | ZP-F_The_Counterexamples.pdf | v1.10 | Y/Y | v1.2: vocab fix + dual-limit remark bullets (AR-clean); companion v1.10: new §VIII squeeze-as-structural-necessity (AR-clean) — formal:72f2aed0 comp:6935af00 |
| ZP-C Information Theory | v1.14 | ZP-C_Information_Theory.pdf | v2.2 | Y/Y | v1.14: version number removed from Open Items Register header; comp v2.2: strip footer version — formal:273410c8 comp:8912617c |
| ZP-D State Layer | v1.10 | ZP-D_State_Layer.pdf | v1.9 | Y/Y | v1.10: version number removed from Open Items Register header; comp v1.9: strip footer version — formal:ed26f6c9 comp:5824ada6 |
| ZP-E Bridge Document | v3.16 | ZP-E_Bridge_Document.pdf | v1.10 | Y/Y | v3.16: version numbers removed from register section headers; comp v1.10: strip footer version — formal:c8732b44 comp:f877b143 |
| ZP-G Category Theory | v1.9 | ZP-G_Category_Theory.pdf | v1.6 | Y/Y | v1.9: version number removed from Open Items Register header; comp v1.6: strip footer version — formal:e6c366d4 comp:9ecf37e9 |
| ZP-H Categorical Bridge | v1.13 | ZP-H_Categorical_Bridge.pdf | v1.5 | Y/Y | v1.13: version number removed from Open Items Register header; comp v1.5: strip footer version — formal:1f9d6ae2 comp:3d10d767 |
| ZP-I Inside Zero | v1.9 | ZP-I_Inside_Zero.pdf | v1.5 | Y/Y | Companion v1.5: strip footer version — formal:298f2e30 comp:c78d212d |
| ZP-J Self-Reference | v2.0 | ZP-J_Self_Reference.pdf | v1.6 | Y/Y | v2.0: Sections VII-X added; comp v1.6: five new sections matching v2.0 content; AR fixes applied to both — formal:f39311c3 comp:a5561b33 |
| ZP-K Computational Grounding | v1.6 | ZP-K_Computational_Grounding.pdf | v1.8 | Y/Y | Companion v1.8: strip footer version — formal:8c00d4aa comp:1286a4a7 |
| ZP-L Incomputability Convergence | v1.0 | ZP-L_Incomputability_Convergence.pdf | v1.4 | Y/Y | Companion v1.4: strip footer version — formal:7825902f comp:3a10ee7b |
| ZP-M Kleene-Ordinal Bridge | v1.0 | ZP-M_Kleene_Ordinal_Bridge.pdf | v1.0 | N/— | v1.0: Initial release — snapEmbed type bridge, hfp gap closed, zpm_triangle, R-M.1. Lean source promoted to full document — formal:24dd8909 comp:702ff724 |

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
