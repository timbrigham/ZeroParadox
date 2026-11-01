# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table is verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.34 | ZP-A_Lattice_Algebra.pdf | v1.13 | N/— | formal:f05cb67e comp:22b29604 |
| ZP-B p-Adic Topology | v1.30 | ZP-B_pAdic_Topology.pdf | v1.21 | N/— | formal:6080b209 comp:4d3ce35e |
| ZP-F The Counterexamples | v1.20 | ZP-F_The_Counterexamples.pdf | v1.19 | N/— | formal:b99fbdbb comp:dee59dce |
| ZP-C Information Theory | v1.33 | ZP-C_Information_Theory.pdf | v2.12 | N/— | formal:d6fe6c3f comp:9f80c438 |
| ZP-D State Layer | v1.19 | ZP-D_State_Layer.pdf | v1.18 | N/— | formal:339590dd comp:6be72c57 |
| ZP-E Bridge Document | v3.68 | ZP-E_Bridge_Document.pdf | v1.33 | Y/Y | formal:b7f4c8c3 comp:1ced0b1e |
| ZP-G Category Theory | v1.25 | ZP-G_Category_Theory.pdf | v1.14 | N/— | formal:d84c3ca4 comp:c39d201c |
| ZP-H Categorical Bridge | v1.29 | ZP-H_Categorical_Bridge.pdf | v1.21 | N/— | formal:e3c9ad18 comp:b85ebaf7 |
| ZP-H Native Categories Addendum | v1.7 | ZP-H_Native_Categories_Addendum.pdf | N/A | N/— | formal:6055c8d4 |
| ZP-I Inside Zero | v1.28 | ZP-I_Inside_Zero.pdf | v1.34 | N/— | formal:37707b03 comp:8e589905 |
| ZP-J Self-Reference | v2.14 | ZP-J_Self_Reference.pdf | v1.35 | N/— | formal:45c84687 comp:27580463 |
| ZP-J AFA Addendum | v1.19 | ZP-J_AFA_Addendum.pdf | N/A | N/— | formal:2919b9d3 |
| ZP-J Wheel Addendum | v1.9 | ZP-J_Wheel_Addendum.pdf | v1.7 | N/— | formal:56bdf47c comp:7d7af230 |
| ZP-J Keystone Addendum | v1.27 | ZP-J_Keystone_Addendum.pdf | N/A | N/— | formal:4d81f4c4 |
| ZP-K Computational Grounding | v1.31 | ZP-K_Computational_Grounding.pdf | v1.26 | N/— | formal:439071fb comp:a5f421ad |
| ZP-L Incomputability Convergence | v1.32 | ZP-L_Incomputability_Convergence.pdf | v1.19 | N/— | formal:fbfd9fa3 comp:59b7ba9a |
| ZP-M Kleene-Ordinal Bridge | v1.18 | ZP-M_Kleene_Ordinal_Bridge.pdf | v1.13 | N/— | formal:3750c9b6 comp:79fea5a7 |
| ZP-N The Constructive Snap | v2.7 | ZP-N_The_Constructive_Snap.pdf | N/A | N/— | formal:a2a2e5ed |
| ZP-P The Fixed-Point Fork | v1.28 | ZP-P_The_Fixed_Point_Fork.pdf | N/A | N/— | formal:c89e28c4 |
| ZP-R Cross-Category Fixed Point | v1.22 | ZP-R_Cross_Category_Fixed_Point.pdf | N/A | N/— | formal:f2804409 |
| ZP-R Diagonal Family Addendum | v1.22 | ZP-R_Diagonal_Family_Addendum.pdf | N/A | N/— | formal:f8542abc |
| ZP-Q The Frame-Change | v1.14 | ZP-Q_The_Frame_Change.pdf | N/A | N/— | formal:b988c043 |
| Zero Paradox Foreword | v2.36 | Zero_Paradox_Foreword.pdf | N/A | N/A | formal:ce7e929a |
| ZP Tools | N/A | ZP_Tools_and_Methods.pdf | N/A | N/A | formal:e6eb108d |
| ZP Choice-Free Core Addendum | v1.14 | ZP_Choice_Free_Core_Addendum.pdf | N/A | N/A | formal:62d54fe6 |

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
