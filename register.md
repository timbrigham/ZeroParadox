# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table is verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.32 | ZP-A_Lattice_Algebra.pdf | v1.12 | N/— | formal:9f668734 comp:aa71c65d |
| ZP-B p-Adic Topology | v1.19 | ZP-B_pAdic_Topology.pdf | v1.17 | N/— | formal:37aa09a7 comp:7e572009 |
| ZP-F The Counterexamples | v1.11 | ZP-F_The_Counterexamples.pdf | v1.14 | N/— | formal:c5b13743 comp:628abeb2 |
| ZP-C Information Theory | v1.26 | ZP-C_Information_Theory.pdf | v2.11 | N/— | formal:7ba26d82 comp:51d4a5bc |
| ZP-D State Layer | v1.16 | ZP-D_State_Layer.pdf | v1.14 | N/— | formal:7d0fe54d comp:c8f82222 |
| ZP-E Bridge Document | v3.55 | ZP-E_Bridge_Document.pdf | v1.26 | Y/Y | formal:c77af4ec comp:26260e42 |
| ZP-G Category Theory | v1.23 | ZP-G_Category_Theory.pdf | v1.14 | N/— | formal:7b23b058 comp:c39d201c |
| ZP-H Categorical Bridge | v1.26 | ZP-H_Categorical_Bridge.pdf | v1.20 | N/— | formal:f758a03d comp:6d92c3fd |
| ZP-H Native Categories Addendum | v1.7 | ZP-H_Native_Categories_Addendum.pdf | N/A | N/— | formal:6055c8d4 |
| ZP-I Inside Zero | v1.28 | ZP-I_Inside_Zero.pdf | v1.34 | N/— | formal:37707b03 comp:8e589905 |
| ZP-J Self-Reference | v2.11 | ZP-J_Self_Reference.pdf | v1.33 | N/— | formal:5ba1bb07 comp:7cfd99e4 |
| ZP-J AFA Addendum | v1.19 | ZP-J_AFA_Addendum.pdf | N/A | N/— | formal:2919b9d3 |
| ZP-J Wheel Addendum | v1.8 | ZP-J_Wheel_Addendum.pdf | v1.6 | N/— | formal:1711b209 comp:feb49592 |
| ZP-J Keystone Addendum | v1.26 | ZP-J_Keystone_Addendum.pdf | N/A | N/— | formal:4f3bf1da |
| ZP-K Computational Grounding | v1.26 | ZP-K_Computational_Grounding.pdf | v1.25 | N/— | formal:26f567db comp:7ecb1d32 |
| ZP-L Incomputability Convergence | v1.30 | ZP-L_Incomputability_Convergence.pdf | v1.18 | N/— | formal:e9597380 comp:c273dc84 |
| ZP-M Kleene-Ordinal Bridge | v1.13 | ZP-M_Kleene_Ordinal_Bridge.pdf | v1.8 | N/— | formal:e7f71e6d comp:139f50be |
| ZP-N The Constructive Snap | v2.5 | ZP-N_The_Constructive_Snap.pdf | N/A | N/— | formal:5bb204ce |
| ZP-P The Fixed-Point Fork | v1.25 | ZP-P_The_Fixed_Point_Fork.pdf | N/A | N/— | formal:d0811d04 |
| ZP-R Cross-Category Fixed Point | v1.20 | ZP-R_Cross_Category_Fixed_Point.pdf | N/A | N/— | formal:b73d52ec |
| ZP-R Diagonal Family Addendum | v1.18 | ZP-R_Diagonal_Family_Addendum.pdf | N/A | N/— | formal:386d90ea |
| ZP-Q The Frame-Change | v1.12 | ZP-Q_The_Frame_Change.pdf | N/A | N/— | formal:e839ba53 |
| Zero Paradox Foreword | v2.35 | Zero_Paradox_Foreword.pdf | N/A | N/A | formal:fa11bda5 |
| ZP Tools | N/A | ZP_Tools_and_Methods.pdf | N/A | N/A | formal:419d6b50 |
| ZP Choice-Free Core Addendum | v1.12 | ZP_Choice_Free_Core_Addendum.pdf | N/A | N/A | formal:c5aa9a12 |

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
