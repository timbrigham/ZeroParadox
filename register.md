# Zero Paradox Version Registry

Update this file first on any version bump. README.md Framework table and GUIDE.md Reading Paths are verified against this register.

| Document | Formal Version | Filename | Companion Version | Comp AR | Notes |
|----------|---------------|----------|-------------------|---------|-------|
| ZP-A Lattice Algebra | v1.15 | ZP-A_Lattice_Algebra.pdf | v1.9 | STALE | v1.15: FMC precision (sweep Step 4, against fmc.md) — CC-2 box "structurally required"/"ruled out"/"incompatible" softened to "argued"; named falsifier added; status line marked argued, not a derivation. v1.14: CC-2 label → Forced Metatheoretic Commitment — formal:5e77e053 comp:37db9ee0 |
| ZP-B p-Adic Topology | v1.10 | ZP-B_pAdic_Topology.pdf | v1.10 | STALE | v1.10: rendered self-version tags removed from C2/C3 corollary titles + "null state" → ⊥ in AX-B1 note (C1 sweep) — formal:c5ae423d comp:6117d309 |
| ZP-F The Counterexamples | v1.4 | ZP-F_The_Counterexamples.pdf | v1.12 | STALE | v1.4: vocab fix — "null state" → "⊥" in preamble; palette rebuild — formal:b04efdb1 comp:4f8d9904 |
| ZP-C Information Theory | v1.18 | ZP-C_Information_Theory.pdf | v2.6 | STALE | v1.18: rendered self-version refs removed — P₀ note ("Version 1.4 updates this") + Open Items row (C1 sweep) — formal:853c18ad comp:8eb51699 |
| ZP-D State Layer | v1.12 | ZP-D_State_Layer.pdf | v1.11 | STALE | v1.12: rendered self-version refs removed — DP-1 title tag + T2 "R3 (v1.6)" (C1 sweep) — formal:353b2557 comp:a37151e6 |
| ZP-E Bridge Document | v3.21 | ZP-E_Bridge_Document.pdf | v1.11 | STALE | v3.21: FMC precision (sweep Step 4, against fmc.md) — R-AFA "the metatheoretic necessity of AFA is derived" → "argued, not proved (a metatheoretic squeeze, not a derivation)" + named falsifier added; CC-2 status lines split the proved structural fixed point (T-EXEC, axiom-free) from the argued set-membership reading; "establish that Foundation is incompatible" → "make the case that" — formal:56cb9167 comp:1b4c17b0 |
| ZP-G Category Theory | v1.12 | ZP-G_Category_Theory.pdf | v1.8 | STALE | v1.12: rendered self-version refs removed — 24 status/provenance tags + "Version 1.0…1.1" narratives + Supersedes (C1 sweep; cross-doc ZP-H v1.0 citations kept) — formal:cff222f4 comp:0673dc77 |
| ZP-H Categorical Bridge | v1.16 | ZP-H_Categorical_Bridge.pdf | v1.13 | STALE | v1.16: rendered self-version removed — endnote + R-FORCING tag (C1 sweep; 21 cross-doc citations kept per scope) — formal:2aaa8275 comp:5e23b02f |
| ZP-H Native Categories Addendum | v1.0 | ZP-H_Native_Categories_Addendum.pdf | N/A | N/— | v1.0: Initial release — snap floor realized in native Mathlib categories: fB_functor → TopCat (⊥ = inverse limit ⋂ B(0,2⁻ⁿ) = {0}), fD_functor → ModuleCat ℂ (⊥ = StateSpace 0 initial; isometric embeddings), fC_functor → KleisliCat PMF (⊥ = Fin 0 initial; fC_no_return = AX-G2 as theorem); mc1_correspondence capstone. Correspondence half of MC-1 formal; identity half a commitment. Lean: ZPH_TopFunctor/ZPH_HilbFunctor/ZPH_InfoFunctor/ZPH_MC1.lean; [propext, Classical.choice, Quot.sound] — formal:25677fda |
| ZP-I Inside Zero | v1.11 | ZP-I_Inside_Zero.pdf | v1.21 | STALE | v1.11: rendered self-version removed — register section headers + T-IZ status cells + endnote (C1 sweep) — formal:5b84859a comp:f4707408 |
| ZP-J Self-Reference | v2.2 | ZP-J_Self_Reference.pdf | v1.26 | STALE | v2.2: rendered self-version refs removed (C1 sweep); null glyphs fixed. comp v1.26: FMC precision (sweep Step 4) — Key Results box + T-EXEC body line split the proved structural fixed point (axiom-free) from the argued set-membership reading. comp v1.25: ScaleBridge wired into maintained build → §6 "future work" bridge retired (2-adic argument now formalized), §7 common-ancestor (ValBridge) framing added, §8 adds ℤ₂ as 3rd concrete model (flagged Classical.choice-carrying vs axiom-free T-EXEC). comp v1.24: APG directed-graph diagram (self-loop), arithmetic analogy scoped, depth rephrased to intrinsic descent, self-loop redrawn as dashed curve (Dan 2026-06-15) — formal:19cf7b64 comp:15a84916 |
| ZP-J AFA Addendum | v1.3 | ZP-J_AFA_Addendum.pdf | N/A | N/— | v1.3: rendered self-version ref removed from endnote (C1 sweep); fixed scaleᵏ null glyph — formal:89775f6d |
| ZP-J Wheel Addendum | v1.0 | ZP-J_Wheel_Addendum.pdf | v1.0 | N/— | v1.0: Initial release — wheel of fractions ⊙_S A = (A×A)/≡_S is a Wheel (Carlström Def 1.1, 14 fields), choice-free [propext, Quot.sound]; inf_ne_bot porthole (∞≠⊥ given 0∉S). Lean: ZPJ_WheelFrac.lean; fix() guard added (PDF build standards). comp v1.0: ZP-J_Wheel_Illustrated_Companion.pdf — plain-language (division-by-zero made total; ∞=/0, ⊥=0·/0; wheel-vs-meadow diagram; instWheel + inf_ne_bot; porthole connection) — formal:2d404fdb comp:d3d0548e |
| ZP-K Computational Grounding | v1.7 | ZP-K_Computational_Grounding.pdf | v1.10 | STALE | v1.7: version changelog removed from preamble; palette rebuild. comp v1.10: four_way_diagram — removed the redundant internal caption String that overlapped the "Computation (Kleene)" box (Diagram Rule 4). comp v1.9: FMC precision (sweep Step 4) — DA-1 Path 1 splits the axiom-free structural fixed point from the literal ⊥={⊥} (ZF+AFA setting) — formal:0c822fa6 comp:10629d03 |
| ZP-L Incomputability Convergence | v1.1 | ZP-L_Incomputability_Convergence.pdf | v1.4 | STALE | v1.1: rendered version changelog removed + 3 null glyphs fixed (subscript-letter entities ₙ/ₒ → <sub> markup) (C1 sweep); comp v1.4: strip footer version — formal:88af2eaa comp:fb745d9b |
| ZP-M Kleene-Ordinal Bridge | v1.1 | ZP-M_Kleene_Ordinal_Bridge.pdf | v1.3 | N/— | v1.1: rendered version changelog removed from title note + endnote (C1 sweep); v1.0: snapEmbed type bridge, hfp gap closed, zpm_triangle, R-M.1; comp v1.3: rendered self-version removed from Key Results header (C1) — formal:ee244180 comp:b8dab924 |
| ZP-P The Fixed-Point Fork | v1.1 | ZP-P_The_Fixed_Point_Fork.pdf | N/A | N/— | v1.1: Added categorical-parent instance as Lean witness (ZPP_Coalgebra.lean: fix_isEmpty μ-empty choice-free, cofix_nonempty ν-inhabited Classical.choice, categorical_fork_strict); set theory/computation referenced (ZP-J/ZP-K) not re-framed. v1.0: synthesis layer — abstract fork schema (lfp/gfp collapses iff unique fixed point) choice-free in Lean: fork_le, collapse_of_unique, unique_of_collapse, fork_collapse_iff [propext, Quot.sound]; number-system instance via Ostrowski: completions_exhaustive, real_not_equiv_padic [propext, Classical.choice, Quot.sound]. Generalizes ZFC+Foundation/AFA orthogonal-contact-point claim; three tiers (schema/instances/unification), hard fence (cross-instance identity = type boundary) + soft fence (not every fork is μ/ν). Lean: ZPP.lean, ZPP_Ostrowski.lean, ZPP_Coalgebra.lean — formal:7ea97be8 |
| Zero Paradox Foreword | v2.7 | Zero_Paradox_Foreword.pdf | N/A | N/A | v2.7: §IV names Lawvere's fixed-point theorem as the recognized unification of the diagonal family (Cantor/Russell/Gödel fixed-point lemma/Kleene); fence firmed — ZP "locates" the diagonal fixed point, not "is". v2.6 added the keystone — formal:324c7977 |
| ZP Philosophical Question | v1.11 | ZP_Philosophical_Question.pdf | N/A | N/A | v1.11: fix() guard via Paragraph override; "bridge" → "connecting argument"; "in ZP's reading" de-duplicated — formal:9b4905de |
| ZP Choice-Free Core Addendum | v1.0 | ZP_Choice_Free_Core_Addendum.pdf | N/A | N/A | v1.0: Initial release — the conceptual core is choice-free; T-SNAP axiom-free; Classical.choice confined to the analytic realizations (inherited from Mathlib); dependence ≠ necessity (open). Anchored on AxiomProfile.lean — formal:b6b92987 |

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
