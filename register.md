# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table is verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.35 | ZP-A_Lattice_Algebra.pdf | v1.15 | N/— | formal:c5e0f124 comp:f675d360 |
| ZP-B p-Adic Topology | v1.31 | ZP-B_pAdic_Topology.pdf | v1.21 | N/— | formal:8bc90240 comp:4d3ce35e |
| ZP-F The Counterexamples | v1.20 | ZP-F_The_Counterexamples.pdf | v1.19 | N/— | formal:b99fbdbb comp:dee59dce |
| ZP-C Information Theory | v1.34 | ZP-C_Information_Theory.pdf | v2.13 | N/— | formal:ceb54c72 comp:559cd1d2 |
| ZP-D State Layer | v1.20 | ZP-D_State_Layer.pdf | v1.18 | N/— | formal:c9f3d049 comp:6be72c57 |
| ZP-E Bridge Document | v3.72 | ZP-E_Bridge_Document.pdf | v1.33 | Y/Y | formal:e36b7658 comp:1ced0b1e |
| ZP-G Category Theory | v1.26 | ZP-G_Category_Theory.pdf | v1.15 | N/— | formal:d79621a4 comp:52664fdb |
| ZP-H Categorical Bridge | v1.29 | ZP-H_Categorical_Bridge.pdf | v1.22 | N/— | formal:e3c9ad18 comp:efcb14ba |
| ZP-H Native Categories Addendum | v1.7 | ZP-H_Native_Categories_Addendum.pdf | N/A | N/— | formal:6055c8d4 |
| ZP-I Inside Zero | v1.29 | ZP-I_Inside_Zero.pdf | v1.35 | N/— | formal:e66b092c comp:fddad2fc |
| ZP-J Self-Reference | v2.15 | ZP-J_Self_Reference.pdf | v1.36 | N/— | formal:b88a1317 comp:95ae8632 |
| ZP-J AFA Addendum | v1.20 | ZP-J_AFA_Addendum.pdf | N/A | N/— | formal:8327eacf |
| ZP-J Wheel Addendum | v1.10 | ZP-J_Wheel_Addendum.pdf | v1.8 | N/— | formal:3b8c71b6 comp:c51d1e09 |
| ZP-J Keystone Addendum | v1.28 | ZP-J_Keystone_Addendum.pdf | N/A | N/— | formal:5a58ae31 |
| ZP-K Computational Grounding | v1.32 | ZP-K_Computational_Grounding.pdf | v1.27 | N/— | formal:5c6b9081 comp:b14071a0 |
| ZP-L Incomputability Convergence | v1.33 | ZP-L_Incomputability_Convergence.pdf | v1.22 | N/— | formal:fce3758c comp:66d5f4ec |
| ZP-M Kleene-Ordinal Bridge | v1.18 | ZP-M_Kleene_Ordinal_Bridge.pdf | v1.13 | N/— | formal:3750c9b6 comp:79fea5a7 |
| ZP-N The Constructive Snap | v2.8 | ZP-N_The_Constructive_Snap.pdf | N/A | N/— | formal:aba9b464 |
| ZP-P The Fixed-Point Fork | v1.31 | ZP-P_The_Fixed_Point_Fork.pdf | N/A | N/— | formal:77ae1fdb |
| ZP-R Cross-Category Fixed Point | v1.23 | ZP-R_Cross_Category_Fixed_Point.pdf | N/A | N/— | formal:ccea95a3 |
| ZP-R Diagonal Family Addendum | v1.23 | ZP-R_Diagonal_Family_Addendum.pdf | N/A | N/— | formal:acc8bce8 |
| ZP-Q The Frame-Change | v1.15 | ZP-Q_The_Frame_Change.pdf | N/A | N/— | formal:47223c42 |
| Zero Paradox Foreword | v2.36 | Zero_Paradox_Foreword.pdf | N/A | N/A | formal:ce7e929a |
| ZP Tools | N/A | ZP_Tools_and_Methods.pdf | N/A | N/A | formal:8847b972 |
| ZP Choice-Free Core Addendum | v1.15 | ZP_Choice_Free_Core_Addendum.pdf | N/A | N/A | formal:919e4689 |

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
