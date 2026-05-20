> **A note on transparency:** This file lives in the public repository but is intentionally unlinked from the main project index. It is a canonical version registry used during active development to keep README.md and GUIDE.md in sync. The main entry point for the Zero Paradox is [README.md](README.md).

# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table and GUIDE.md Reading Paths are verified against this register.

| Document | Formal Version | Filename | Companion Version | Notes |
|----------|---------------|----------|-------------------|-------|
| ZP-A Lattice Algebra | v1.13 | ZP-A_Lattice_Algebra.pdf | v1.6 | Companion v1.6: disclaimer "formal ontology" → "formal document" — formal:130d0acd comp:3d8b14d5 |
| ZP-B p-Adic Topology | v1.7 | ZP-B_pAdic_Topology.pdf | v1.7 | Formal v1.7: "Topological isolation of 0" → "Clopen gap at 0" throughout. Companion v1.7: stale PDF rebuilt — script had been updated with isolation fixes (v1.4-v1.7) but PDF was never regenerated. — formal:84db2ad4 comp:2ee84380 |
| ZP-F The Counterexamples | v1.1 | ZP-F_The_Counterexamples.pdf | v1.8 | Companion v1.8: topological/valuative distinction corrected; Riemann sphere analogy added — formal:8b35d28e comp:ef61332d |
| ZP-C Information Theory | v1.12 | ZP-C_Information_Theory.pdf | v1.8 | Companion v1.8: disclaimer updated — formal:4a59f304 comp:d376d5cf |
| ZP-D State Layer | v1.8 | ZP-D_State_Layer.pdf | v1.7 | Companion v1.7: disclaimer updated — formal:255b169c comp:85c6e4d9 |
| ZP-E Bridge Document | v3.13 | ZP-E_Bridge_Document.pdf | v1.7 | Companion v1.7: title, remember boxes updated; "universal ontology" removed — formal:be86fe89 comp:074c2c2f |
| ZP-G Category Theory | v1.8 | ZP-G_Category_Theory.pdf | v1.4 | Companion v1.4: title "Structure independent of domain"; formal doc: "Internal Working Document" removed — formal:bde00483 comp:b0e98acc |
| ZP-H Categorical Bridge | v1.12 | ZP-H_Categorical_Bridge.pdf | v1.4 | Companion v1.4: structural floor section added; snap diagram overlap fixed (internal title removed, dh increased) — formal:d14f2b36 comp:8f504038 |
| ZP-I Inside Zero | v1.8 | ZP-I_Inside_Zero.pdf | v1.2 | Companion v1.2: disclaimer + opener updated — formal:b3138d52 comp:78767395 |
| ZP-J Self-Reference | v1.2 | ZP-J_Self_Reference.pdf | v1.3 | Companion v1.3: disclaimer updated; formal doc: "asserted coincidence" removed — formal:1dd8e34f comp:39ff4bac |
| ZP-K Computational Grounding | v1.5 | ZP-K_Computational_Grounding.pdf | v1.2 | Companion v1.2: disclaimer updated; v1.5: precision fixes (periodicity framing, typeclass commitment language, Kolmogorov claims scoped) — PDF rebuild pending — formal:d11d3565 comp:20f7004b |

*Last updated: May 2026*

---

## Script Hash Verification

The `formal:XXXXXXXX comp:XXXXXXXX` tokens in the Notes column above are SHA-256 (first 8 chars) fingerprints of the corresponding build scripts in `.claude-local/`. Run `.claude-local/check_hashes.py` at the start of any session touching build scripts to confirm scripts and register are in sync. A mismatch means a script was modified without a version bump and PDF rebuild — not just a rebuild, a full version bump with archive step.
