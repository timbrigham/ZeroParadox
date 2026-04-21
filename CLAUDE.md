# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Guiding Principles (from Project Instructions)

- **Logical Rigor First:** The primary goal is logical consistency and rigor. 
- **Prose Role:** Use prose only to restate mathematics into accessible language. 
- **Ontology Focus:** Finalized documents must be structured as an ontology. 
- **Persistence:** All completed work must be committed back to the repository immediately to prevent data loss.

## Repository Nature

This is a **mathematical publication repository**, not a software project. There is no build system, test suite, or source code. The repository contains:

- PDF documents (the formal mathematical framework and illustrated companions)
- Markdown documentation (README.md, ABOUTME.md, this file)
- A `historical/` folder for superseded document versions
- A `scripts/` folder with the PDF build tooling (Claude-generated, public, included for transparency)

## Private Working Folder

A `.claude-local/` folder exists locally and is **gitignored** — it does not appear in the public repository. This is intentional. It serves as a private working space for the core collaborators (Tim, Daniel, and Claude) during active development, before material is ready for public discourse. It contains:

- Reviewer feedback and correspondence (e.g. `feedback/`)
- In-progress build scripts and draft outputs
- Session notes and development artifacts

Transparency is a core value of this project. The existence of this private folder is acknowledged here precisely for that reason: readers of the public repo can see that private collaboration is occurring, understand its purpose, and know that the mathematical content and editorial decisions will be surfaced publicly as the work matures. Nothing in `.claude-local/` affects the formal mathematics — that lives entirely in the committed PDFs.

## Document Versioning Conventions

- Current documents live at the root: `ZP-X_Title_vN_N.pdf` (no numeric suffix)
- Superseded versions are moved to `historical/` and get a numeric suffix: `ZP-X_Title_vN_N-1.pdf`
- The `historical/README.md` tracks all archived files with date moved and description
- README.md always links to the non-suffixed (current) version

## README.md Link Restrictions

The following files exist in the repository but **must not be linked from README.md** until the conditions below are met:

| File | Reason | Condition to lift restriction |
|------|--------|-------------------------------|
| `ZP_Gen2_Applications.pdf` | Speculative applications document — depends on Gen 1 being formally complete and bridge documents written. Premature to surface publicly in the index. | All Gen 1 layers (ZP-A through ZP-H) fully tightened; thermodynamic bridge and OQ-E2 resolved; explicit decision by Tim to promote. |
| `ABOUTME.md` | Not ready for prominent public linking from the main index. | Explicit decision by Tim to promote. |

Do not add links to these files in README.md under any circumstances without explicit instruction. They may exist in the repo and be committed — they just must not appear in the README index.

## README.md Maintenance

The `.copilot-instructions.md` file is the authoritative style guide for README updates. Key rules:
- Links display as clean names: `[ZP-A Lattice Algebra](ZP-A_Lattice_Algebra_v1_1.pdf)` — no version or extension in display text
- Use regular hyphens (`-`), not em dashes (`—`); mathematical arrows (`→`) are fine
- Section order must follow the structure defined in `.copilot-instructions.md`
- Before editing, verify all linked files actually exist: `ls *.pdf`

## Archiving Old Document Versions

When a document is superseded:
1. Add a numeric suffix to the old file and move it: `mv ZP-X_Title_vN_N.pdf historical/ZP-X_Title_vN_N-1.pdf`
2. Add the new version to the root (no suffix)
3. Update `historical/README.md` with a table row: `| [filename](filename) | YYYY-MM-DD | description |`
4. Update the version number in README.md's Document Index table

## Framework Structure (for context)

The Zero Paradox is a multi-layer mathematical ontology proving the Binary Snap (⊥ → ε₀) as a theorem. The dependency order of the formal layers is:

**ZP-A** (lattice algebra) → **ZP-B** (p-adic topology) → **ZP-C** (information theory) → **ZP-D** (state layer) → **ZP-E** (DA-1/T-SNAP derivation)

**ZP-G** (category theory) → **ZP-H** (categorical bridge) — self-contained; depends on ZP-E conceptually but not formally.

Each formal document has a paired illustrated companion for general readers. The three remaining intentional axioms are AX-B1, AX-G1, and AX-G2. AX-1 (Binary Snap Causality) is now Theorem T-SNAP, derived in ZP-E — do not refer to it as an axiom.

## Reviewer Feedback Tracking

### Dan — ZP-A Review (April 2026)

Feedback received and reviewed. Status of each point:

| Feedback | Status | Resolution |
|----------|--------|------------|
| `:⟺` notation is non-standard for definitional biconditional | **Fixed in v1.2** | Changed to `⟺` with "define the relation ≤ by:" framing |
| D2 "Equivalently" claim has no proof | **Fixed in v1.2** | Explicit two-line proof of both directions added |
| Illustrated companion needs more concrete examples | **Fixed in v1.2** | Power set with union, [0,∞) with max, document edit history added |
| "Axiom Block A" — Dan prefers "properties" over "axioms" | Deferred — keep | A1–A4 are axioms in the standard algebraic sense; defensible |
| "State space" / "states" language feels loaded | Deferred — keep | Intentional framing for the ZP ontology; L is explicitly called a "non-empty set" in 1.1 |
| Dual structure (top/meet operator) as future work | Noted | Already addressed in R1; no action needed |

## License

CC BY-NC-ND 4.0 — share with attribution; no modifications; no commercial use.


# .claudecodes instructions for Lean 4 development
- When working on the Zero Paradox ontology, prioritize files in the root C:\Workspace\ZeroParadox folder.
- Always use 'lake build' to verify proofs before finalizing any theorem code.
- Ignore PDF rendering assets and website build artifacts in the root.
- Treat 'lake_testing' as the active branch for experimental verification.
- Always check 'lake-manifest.json' for dependency updates before adding new imports.

# Zero Paradox Project Standards

# Zero Paradox Project Standards

## Context Awareness & Branching Protocol
- **Primary Proof Workspace:** `lake_testing` branch. 
  - Goal: Formalizing the mathematical ontology using Lean 4.
  - Scope: `.lean` files, `lakefile.lean`, and mathlib integration.
- **Illustrated/Display Workspace:** `illustrated` branch.
  - Goal: Rerendering PDFs, updating illustrated companions, and site-level display logic.
  - Scope: `/pdfs`, `/site`, and PDF build tooling in `/scripts`.

## Operational Rules
1. **Branch-Task Lock:** - Lean 4 proof development **must** happen on `lake_testing`.
   - PDF creation or rendering actions **must** happen on `illustrated`.
2. **Mandatory Checkout:** If the user requests an action belonging to the other workspace, Claude must prompt the user to switch branches before reading or writing those specific assets.
3. **Math Workflow:** When on `lake_testing`, always run `lake build` to verify any theorem changes.
4. **PDF Workflow:** On the `illustrated` branch, use existing rendering scripts and strictly follow the document versioning and archiving conventions defined above.
5. **Transparency:** Maintain the `.claude-local/` folder for in-progress scripts and internal notes as a private "collaboration buffer."

## File Priority & Access
- **On `lake_testing`:** Prioritize `.lean` source files. Treat `/site` and `/pdfs` as Read-Only unless explicitly authorized for a cross-domain check.
- **On `illustrated`:** Prioritize PDF artifacts and rendering scripts. Treat `/ZeroParadox` source files as the "Ground Truth" reference for documentation updates.

## File Priority
- Focus on `.lean` and `lakefile.lean` for the ontology.
- Assets in `/site` and `/pdfs` are open for editing **only** for reredering tasks.