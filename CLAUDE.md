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

## License

CC BY-NC-ND 4.0 — share with attribution; no modifications; no commercial use.
