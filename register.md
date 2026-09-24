# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table and GUIDE.md Reading Paths are verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.29 | ZP-A_Lattice_Algebra.pdf | v1.11 | N/— | formal:8c003b4e comp:8e00c888 |
| ZP-B p-Adic Topology | v1.18 | ZP-B_pAdic_Topology.pdf | v1.16 | N/— | formal:df43d2f5 comp:79b374cc |
| ZP-F The Counterexamples | v1.8 | ZP-F_The_Counterexamples.pdf | v1.14 | N/— | formal:bfed0e0f comp:d6bdb1f7 |
| ZP-C Information Theory | v1.24 | ZP-C_Information_Theory.pdf | v2.9 | N/— | formal:b206f0a9 comp:e98d8d80 |
| ZP-D State Layer | v1.15 | ZP-D_State_Layer.pdf | v1.13 | N/— | formal:923468a5 comp:32064117 |
| ZP-E Bridge Document | v3.42 | ZP-E_Bridge_Document.pdf | v1.19 | Y/Y | formal:26b7b72e comp:8a727d24 |
| ZP-G Category Theory | v1.15 | ZP-G_Category_Theory.pdf | v1.9 | N/— | formal:2af3526b comp:9b61e514 |
| ZP-H Categorical Bridge | v1.23 | ZP-H_Categorical_Bridge.pdf | v1.16 | N/— | formal:cece605b comp:c89777ab |
| ZP-H Native Categories Addendum | v1.6 | ZP-H_Native_Categories_Addendum.pdf | N/A | N/— | formal:c9da80f9 |
| ZP-I Inside Zero | v1.26 | ZP-I_Inside_Zero.pdf | v1.32 | N/— | formal:e2ed66c0 comp:fdeb337f |
| ZP-J Self-Reference | v2.8 | ZP-J_Self_Reference.pdf | v1.32 | N/— | formal:d4d99541 comp:c2a20ceb |
| ZP-J AFA Addendum | v1.16 | ZP-J_AFA_Addendum.pdf | N/A | N/— | formal:7e46e9e2 |
| ZP-J Wheel Addendum | v1.7 | ZP-J_Wheel_Addendum.pdf | v1.6 | N/— | formal:014fe9b9 comp:5f817977 |
| ZP-J Keystone Addendum | v1.13 | ZP-J_Keystone_Addendum.pdf | N/A | N/— | formal:840acb6d |
| ZP-K Computational Grounding | v1.24 | ZP-K_Computational_Grounding.pdf | v1.22 | N/— | formal:1a307934 comp:ce5fd785 |
| ZP-L Incomputability Convergence | v1.20 | ZP-L_Incomputability_Convergence.pdf | v1.14 | N/— | formal:c52c64a2 comp:70a48615 |
| ZP-M Kleene-Ordinal Bridge | v1.7 | ZP-M_Kleene_Ordinal_Bridge.pdf | v1.6 | N/— | formal:589cbf08 comp:d2106aba |
| ZP-N The Constructive Snap | v2.0 | ZP-N_The_Constructive_Snap.pdf | N/A | N/— | formal:5011bb68 |
| ZP-P The Fixed-Point Fork | v1.24 | ZP-P_The_Fixed_Point_Fork.pdf | N/A | N/— | formal:4b914ac3 |
| ZP-R Cross-Category Fixed Point | v1.6 | ZP-R_Cross_Category_Fixed_Point.pdf | N/A | N/— | formal:cfe3495f |
| ZP-R Diagonal Family Addendum | v1.1 | ZP-R_Diagonal_Family_Addendum.pdf | N/A | N/— | formal:937a0e90 |
| ZP-Q The Frame-Change | v1.11 | ZP-Q_The_Frame_Change.pdf | N/A | N/— | formal:dcf69119 |
| Zero Paradox Foreword | v2.27 | Zero_Paradox_Foreword.pdf | N/A | N/A | formal:867a2fe5 |
| ZP Philosophical Question | v1.21 | ZP_Philosophical_Question.pdf | N/A | N/A | formal:ed65d90b |
| ZP Choice-Free Core Addendum | v1.10 | ZP_Choice_Free_Core_Addendum.pdf | N/A | N/A | formal:1834c1f5 |

**Comp AR column key:** `Y/Y` = current comp hash adversary-reviewed + remediated (or confirmed clean). `Y/N` = reviewed, fixes identified but not yet applied. `N/—` = not yet reviewed.

---

## Script Hash Verification + AR Tracking

The `formal:XXXXXXXX comp:XXXXXXXX` tokens in the Notes column above are SHA-256 (first 8 chars) fingerprints of the corresponding build scripts in [`scripts/`](scripts/) — public and tracked, so a reader can recompute them. They moved there on 2026-08-15; the tokens were recomputed from the normalised (LF) bytes at the same time, because a fingerprint of one machine's CRLF working copy is not provenance. The `Comp AR` column tracks adversary-review status for each companion, backed by `.claude-local/ar_status.json`, which is private — its absence is reported as unavailable, never as a mismatch.

**Session start** — run once before touching any build script:
```
python tools/verify/check_hashes.py
```
A hash `MISMATCH` means a script was modified without a version bump and PDF rebuild. An AR status of `STALE` means the companion script changed since its last adversary review — re-review required before merge.

**Post-fix workflow** — after applying adversary-review fixes, rebuilding the PDF, and updating the hash in register.md, run one command to close the loop:
```
python tools/verify/check_hashes.py --mark-remediated ZP-X
```
This computes the current comp hash, writes it to `ar_status.json` as remediated, and updates the `Comp AR` column in this file automatically. For fixes identified but not yet applied, use `--mark-reviewed ZP-X` instead (sets Y/N).
