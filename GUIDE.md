# The Zero Paradox: A Reader's Guide

*Plain-language introduction, illustrated companions, and reading paths for all audiences.*

[![Lean Action CI](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-ff69b4?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/timbrigham) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20060860.svg)](https://doi.org/10.5281/zenodo.20060860)

For a dictionary and map of ⊥ - the object the whole framework is built on - see [The Bottom Element](BOTTOMELEMENT.md). For the formal framework index, Lean verification, and complete question register, see [README](README.md).

---

## What This Is

The Zero Paradox proves that a minimum non-bottom element in a join-semilattice is structurally forced - not assumed. The result is machine-verified in Lean 4. The supporting structure examines what happens at the bottom element ⊥ across several mathematical frameworks; each independently locates the same structural constraint. One additional hypothesis per framework is required that is not derivable from that framework's axioms alone - these are catalogued in [Axiomatic Commitments](README.md#axiomatic-commitments) in README.md.

Each layer of the proof is internally closed before any cross-framework claim is made.

No snap-specific axioms appear anywhere in the framework. The Binary Snap - the forced transition from the bottom element ⊥ to the minimum non-bottom state - is a theorem proved in ZP-E from A4 - the standard bottom-element axiom (∀ x, ⊥ ∨ x = x) - together with the framework's computational commitments. A4 is a standard axiom of join-semilattice theory.

---

## What This Is Not

- **Not a physical theory** - the framework is silent on which specific state emerges first; physical theories would arise by specifying that
- **Not a claim about consciousness or the hard problem** - the framework is silent on these questions
- **Not a claim that zero is paradoxical in all of mathematics** - the paradox is local to this framework's structure
- **Not a logical contradiction** - the framework is internally consistent throughout

**On vocabulary.** The framework aims for precision by using the *established* term for each structure it describes - the recognized name from the relevant field, not a coinage of its own. (Its own results carry reference labels - T-SNAP, MC-1, and the like - as any formal development assigns; those are identifiers for specific results, not invented vocabulary for existing structures.) A deliberate consequence is that its language draws on concepts from many backgrounds: set theory, category theory, proof theory, computability, valuation theory, and others. Borrowing a field's precise vocabulary is not a claim to results in that field; the framework's assertions are confined to the mathematics it formally establishes, and where its structures resemble ideas in other domains, those resemblances are named as such, never asserted as results there.

---

## Entry Point

**Ask questions about the framework**

This repository is connected to a Copilot Space - a GitHub AI chat with the documents and Lean source indexed. It has been given project-specific context, so it can help orient you to the layer structure and terminology.

[Open Copilot Space](https://github.com/copilot/spaces/timbrigham/1) - GitHub account required.

---

| File | Description |
|------|-------------|
| [Zero Paradox Foreword](Zero_Paradox_Foreword.pdf) | Plain-language introduction for any reader. Start here. |

---

## Reading Paths

**Before any path:** [The Bottom Element (⊥)](BOTTOMELEMENT.md) - a dictionary and map of the object the whole framework is built on. It orients you to ⊥, and to what is proved versus still open about it, before you follow any route below.

**General reader:** [The Philosophical Question](ZP_Philosophical_Question.pdf) → [Foreword](Zero_Paradox_Foreword.pdf) → any [Illustrated Companion](#illustrated-companion-documents) → [ZP-E Companion](ZP-E_Illustrated_Companion.pdf) → [ZP-I Companion](ZP-I_Illustrated_Companion.pdf) (framework closure)

**Mathematician:** [ZP-A](ZP-A_Lattice_Algebra.pdf) → [ZP-B](ZP-B_pAdic_Topology.pdf) → [ZP-C](ZP-C_Information_Theory.pdf) → [ZP-D](ZP-D_State_Layer.pdf) → [ZP-E](ZP-E_Bridge_Document.pdf) → [ZP-F](ZP-F_The_Counterexamples.pdf) → [ZP-J](ZP-J_Self_Reference.pdf) → [ZP-J AFA Addendum](ZP-J_AFA_Addendum.pdf) → [ZP-J Wheel Addendum](ZP-J_Wheel_Addendum.pdf) → [ZP-K](ZP-K_Computational_Grounding.pdf) → [ZP-I](ZP-I_Inside_Zero.pdf) → [ZP-L](ZP-L_Incomputability_Convergence.pdf) (axiom footprint convergence, ε₀ as snap threshold, canonical snap map) → [ZP-M](ZP-M_Kleene_Ordinal_Bridge.pdf) (Kleene-ordinal-2-adic bridge, hereditary fixed-point gap closure) → [ZP-P](ZP-P_The_Fixed_Point_Fork.pdf) (the fixed-point fork: the Foundation/AFA contact point generalized across frameworks) → [ZP-J Keystone Addendum](ZP-J_Keystone_Addendum.pdf) (the diagonal-fixed-point keystone: the Lawvere face-split and the well-foundedness boundary) → [The Choice-Free Core](ZP_Choice_Free_Core_Addendum.pdf) (the framework's axiom profile: the core is choice-free) - see [README](README.md) for the full formal index and Lean verification record

**Category theory extension:** [ZP-G](ZP-G_Category_Theory.pdf) → [ZP-H](ZP-H_Categorical_Bridge.pdf) → [ZP-H Native Categories Addendum](ZP-H_Native_Categories_Addendum.pdf) (self-contained after ZP-E)

**For process and methods:** [ZP Tools and Methods](ZP_Tools_and_Methods.pdf)

---

## Illustrated Companion Documents

One companion per formal document. Plain language, diagrams, real-world examples.

> **Note (April 2026):** Some companions were written before significant revisions to the formal documents and are currently being updated. Treat them as introductions to the framework's structure, not authoritative statements of current theorem names or statuses.

| File | For Document | Key Diagrams |
|------|-------------|--------------|
| [ZP-A Illustrated Companion](ZP-A_Illustrated_Companion.pdf) | ZP-A | Hasse diagram, one-directional transitions |
| [ZP-B Illustrated Companion](ZP-B_Illustrated_Companion.pdf) | ZP-B | Nested clopen balls, disjoint ball separation |
| [ZP-C Illustrated Companion](ZP-C_Illustrated_Companion.pdf) | ZP-C | Surprisal field singularity, 1-bit Snap cost, L-RUN execution trace |
| [ZP-D Illustrated Companion](ZP-D_Illustrated_Companion.pdf) | ZP-D | T map: topology → orthogonality |
| [ZP-E Illustrated Companion](ZP-E_Illustrated_Companion.pdf) | ZP-E | Four-framework convergence, T-SNAP derivation chain |
| [ZP-F Illustrated Companion](ZP-F_Illustrated_Companion.pdf) | ZP-F | ℝ vs Q₂ structural comparison, pi curve density diagram |
| [ZP-G Illustrated Companion](ZP-G_Illustrated_Companion.pdf) | ZP-G | Category and functor concepts, initial object, informational singularity |
| [ZP-H Illustrated Companion](ZP-H_Illustrated_Companion.pdf) | ZP-H | Four-functor convergence, T-SNAP derivation chain, Binary Snap across the four ZP frameworks |
| [ZP-I Illustrated Companion](ZP-I_Illustrated_Companion.pdf) | ZP-I | 2-adic depth diagram, three closed doors + Cauchy passage, complete cycle diagram |
| [ZP-J Illustrated Companion](ZP-J_Illustrated_Companion.pdf) | ZP-J + ZP-J AFA Addendum | Quine atom diagram (⊥ = {⊥}), directed-graph (APG) view of the Quine atom (self-loop), three-way equivalence table, CC-1/CC-2 as derived propositions, abstraction chain (ValuationStructure → AFAStructure), APG decoration uniqueness |
| [ZP-J Wheel Illustrated Companion](ZP-J_Wheel_Illustrated_Companion.pdf) | ZP-J Wheel Addendum | Wheel vs meadow diagram (∞ ≠ ⊥), division by zero made total, ∞ = /0 and ⊥ = 0·/0, the wheel of fractions construction, wheel/meadow distinction, porthole connection |
| [ZP-K Illustrated Companion](ZP-K_Illustrated_Companion.pdf) | ZP-K | Four-way equivalence diagram, computational Quine, execution argument Lean verification |
| [ZP-L Illustrated Companion](ZP-L_Illustrated_Companion.pdf) | ZP-L | Ordinal tower with ε₀ snap threshold, dual convergence diagram |
| [ZP-M Illustrated Companion](ZP-M_Illustrated_Companion.pdf) | ZP-M | Kleene-Ordinal-2-adic triangle, diagonalization schema |

---

## Supporting Documents

| File | Description |
|------|-------------|
| [The Philosophical Question That Started This](ZP_Philosophical_Question.pdf) | The philosophical question that motivated the framework, and what the formal results say about it. |
| [ZP Tools and Methods](ZP_Tools_and_Methods.pdf) | How the framework was developed: Claude's role, what formal tools were and were not used (Rocq, Lean, etc.), the PDF rendering pipeline. |

---

## Notes on Development

This framework was developed by a human researcher in collaboration with Claude (Anthropic, April 2026). Claude served as research assistant, formal scribe, and gap identifier. All mathematical content and theoretical direction originated with the researcher. See [ZP Tools and Methods](ZP_Tools_and_Methods.pdf) for a complete account.

The PDF build tooling is publicly available in the [`scripts/`](scripts/) folder. Those scripts were generated by Claude and are included for transparency about how the documents were produced.

If you find this work valuable and would like to support its continued development, you can do so via [GitHub Sponsors](https://github.com/sponsors/timbrigham).

---

## Repository and Version History

This project is hosted on GitHub at [timbrigham/ZeroParadox](https://github.com/timbrigham/ZeroParadox). The repository uses Git for version control, allowing you to explore the evolution of the theorems and documents over time.

To view older versions of documents as the framework progressed:
- **Via GitHub web interface**: Navigate to the repository, click on a file, then "History" to browse commits.
- **Locally**: Use `git log` to see commit history and `git checkout <commit-hash>` to view specific versions.

Previous document versions are also kept in the [historical/](historical/) folder, making the development process visible without requiring Git access.

---

*For the formal framework index, axiomatic commitments, question register, and Lean verification, see [README](README.md).*

*Zero Paradox | April 2026*
