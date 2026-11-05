# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table is verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.37 | ZP-A_Lattice_Algebra.pdf | v1.23 | N/— | formal:8ac90a09 comp:3d18bb87 |
| ZP-B p-Adic Topology | v1.32 | ZP-B_pAdic_Topology.pdf | v1.21 | N/— | formal:5ccc5dd3 comp:4d3ce35e |
| ZP-F The Counterexamples | v1.25 | ZP-F_The_Counterexamples.pdf | v1.24 | N/— | formal:7bd01deb comp:43e4294e |
| ZP-C Information Theory | v1.39 | ZP-C_Information_Theory.pdf | v2.14 | N/— | formal:4a46b049 comp:10cbc861 |
| ZP-D State Layer | v1.21 | ZP-D_State_Layer.pdf | v1.18 | N/— | formal:af01d656 comp:6be72c57 |
| ZP-E Bridge Document | v3.78 | ZP-E_Bridge_Document.pdf | v1.38 | Y/Y | formal:37cdfdd9 comp:ae4f6d28 |
| ZP-G Category Theory | v1.27 | ZP-G_Category_Theory.pdf | v1.16 | N/— | formal:e901301e comp:668a9008 |
| ZP-H Categorical Bridge | v1.35 | ZP-H_Categorical_Bridge.pdf | v1.26 | N/— | formal:aff5d535 comp:5b4b5638 |
| ZP-H Native Categories Addendum | v1.14 | ZP-H_Native_Categories_Addendum.pdf | N/A | N/— | formal:b961348b |
| ZP-I Inside Zero | v1.38 | ZP-I_Inside_Zero.pdf | v1.40 | N/— | formal:2ace4e79 comp:c0208f01 |
| ZP-J Self-Reference | v2.17 | ZP-J_Self_Reference.pdf | v1.41 | N/— | formal:d486cc53 comp:676aa6d7 |
| ZP-J AFA Addendum | v1.21 | ZP-J_AFA_Addendum.pdf | N/A | N/— | formal:bd77b297 |
| ZP-J Wheel Addendum | v1.11 | ZP-J_Wheel_Addendum.pdf | v1.15 | N/— | formal:849e279d comp:7812acd4 |
| ZP-J Keystone Addendum | v1.30 | ZP-J_Keystone_Addendum.pdf | N/A | N/— | formal:8c1a77c3 |
| ZP-K Computational Grounding | v1.37 | ZP-K_Computational_Grounding.pdf | v1.32 | N/— | formal:15d32701 comp:c7dec003 |
| ZP-L Incomputability Convergence | v1.38 | ZP-L_Incomputability_Convergence.pdf | v1.22 | N/— | formal:f9a872b7 comp:66d5f4ec |
| ZP-M Kleene-Ordinal Bridge | v1.19 | ZP-M_Kleene_Ordinal_Bridge.pdf | v1.14 | N/— | formal:ec671c9d comp:9888babd |
| ZP-N The Constructive Snap | v2.8 | ZP-N_The_Constructive_Snap.pdf | N/A | N/— | formal:aba9b464 |
| ZP-P The Fixed-Point Fork | v1.37 | ZP-P_The_Fixed_Point_Fork.pdf | N/A | N/— | formal:794df5a8 |
| ZP-R Cross-Category Fixed Point | v1.26 | ZP-R_Cross_Category_Fixed_Point.pdf | N/A | N/— | formal:d74402f0 |
| ZP-R Diagonal Family Addendum | v1.24 | ZP-R_Diagonal_Family_Addendum.pdf | N/A | N/— | formal:6144f567 |
| ZP-Q The Frame-Change | v1.22 | ZP-Q_The_Frame_Change.pdf | N/A | N/— | formal:df5dfc56 |
| Zero Paradox Foreword | v2.45 | Zero_Paradox_Foreword.pdf | N/A | N/A | formal:4deba2da |
| ZP Tools | N/A | ZP_Tools_and_Methods.pdf | N/A | N/A | formal:db9fdb1e |
| ZP Choice-Free Core Addendum | v1.16 | ZP_Choice_Free_Core_Addendum.pdf | N/A | N/A | formal:efef9227 |

**Comp AR column key:** `Y/Y` = current comp hash adversary-reviewed + remediated (or confirmed clean). `Y/N` = reviewed, fixes identified but not yet applied. `N/—` = not yet reviewed.

---

## Script Hash Verification + AR Tracking

The `formal:XXXXXXXX comp:XXXXXXXX` tokens in the Notes column above are SHA-256 (first 8 chars) fingerprints of the corresponding build scripts in [`scripts/`](scripts/) — public and tracked, so a reader can recompute them. They moved there on 2026-08-15; the tokens were recomputed from the normalised (LF) bytes at the same time, because a fingerprint of one machine's CRLF working copy is not provenance. The `Comp AR` column tracks adversary-review status for each companion, backed by `.claude-local/ar_status.json`, which is private — its absence is reported as unavailable, never as a mismatch.

**Session start** — run once before touching any build script:
```
python tools/verify/check_hashes.py
```
A hash `MISMATCH` means a script was modified without a version bump and PDF rebuild. An AR status (`STALE` included) comes from a legacy per-document tracker that gates nothing: review coverage is a verdict in the ledger, and `check_hashes.py` prints that these columns are to be ignored.

**Post-fix workflow** — after applying adversary-review fixes, rebuilding the PDF, and updating the hash in register.md, run one command to close the loop:
```
python tools/verify/check_hashes.py --mark-remediated ZP-X
```
This computes the current comp hash, writes it to `ar_status.json` as remediated, and updates the `Comp AR` column in this file automatically. For fixes identified but not yet applied, use `--mark-reviewed ZP-X` instead (sets Y/N).
