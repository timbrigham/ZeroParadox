> **A note on transparency:** This file lives in the public repository but is intentionally unlinked from the main project index. It is a canonical version registry used during active development to keep README.md and GUIDE.md in sync. The main entry point for the Zero Paradox is [README.md](README.md).

# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table and GUIDE.md Reading Paths are verified against this register.

| Document | Formal Version | Filename | Companion Version | Notes |
|----------|---------------|----------|-------------------|-------|
| ZP-A Lattice Algebra | v1.13 | ZP-A_Lattice_Algebra_v1_13.pdf | v1.6 | Companion v1.6: disclaimer "formal ontology" → "formal document" — formal:fbcc46ac comp:3d8b14d5 |
| ZP-B p-Adic Topology | v1.7 | ZP-B_pAdic_Topology_v1_7.pdf | v1.7 | Formal v1.7: "Topological isolation of 0" → "Clopen gap at 0" throughout. Companion v1.7: stale PDF rebuilt — script had been updated with isolation fixes (v1.4-v1.7) but PDF was never regenerated. — formal:f4ec4bd3 comp:2ee84380 |
| ZP-F The Counterexamples | v1.1 | ZP-F_The_Counterexamples_v1_1.pdf | v1.8 | Companion v1.8: topological/valuative distinction corrected; Riemann sphere analogy added — formal:e632bd76 comp:ef61332d |
| ZP-C Information Theory | v1.12 | ZP-C_Information_Theory_v1_12.pdf | v1.8 | Companion v1.8: disclaimer updated — formal:dfdd8268 comp:d376d5cf |
| ZP-D State Layer | v1.8 | ZP-D_State_Layer_v1_8.pdf | v1.7 | Companion v1.7: disclaimer updated — formal:3e295113 comp:85c6e4d9 |
| ZP-E Bridge Document | v3.13 | ZP-E_Bridge_Document_v3_13.pdf | v1.7 | Companion v1.7: title, remember boxes updated; "universal ontology" removed — formal:8f6e418f comp:074c2c2f |
| ZP-G Category Theory | v1.8 | ZP-G_Category_Theory_v1_8.pdf | v1.4 | Companion v1.4: title "Structure independent of domain"; formal doc: "Internal Working Document" removed — formal:e9adaed1 comp:b0e98acc |
| ZP-H Categorical Bridge | v1.12 | ZP-H_Categorical_Bridge_v1_12.pdf | v1.3 | Companion v1.3: disclaimer updated; formal doc: scaffolding note removed — formal:9f023969 comp:0f1c7362 |
| ZP-I Inside Zero | v1.8 | ZP-I_Inside_Zero_v1_8.pdf | v1.2 | Companion v1.2: disclaimer + opener updated — formal:1fc606fd comp:78767395 |
| ZP-J Self-Reference | v1.2 | ZP-J_Self_Reference_v1_2.pdf | v1.3 | Companion v1.3: disclaimer updated; formal doc: "asserted coincidence" removed — formal:75007933 comp:39ff4bac |
| ZP-K Computational Grounding | v1.4 | ZP-K_Computational_Grounding_v1_4.pdf | v1.2 | Companion v1.2: disclaimer updated; formal doc: preamble claim scoped — formal:da96d602 comp:20f7004b |

*Last updated: May 2026*

---

## Script Hash Verification

The `formal:XXXXXXXX comp:XXXXXXXX` tokens in the Notes column above are SHA-256 (first 8 chars) fingerprints of the corresponding build scripts in `.claude-local/`. Run `.claude-local/check_hashes.py` at the start of any session touching build scripts to confirm scripts and register are in sync. A mismatch means a script was modified without a version bump and PDF rebuild — not just a rebuild, a full version bump with archive step.
