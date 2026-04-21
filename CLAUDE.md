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

## Transparency Notices on Unlinked Public Documents

Any file that is committed to the public repository but intentionally unlinked from README.md **must carry a transparency notice** explaining its status. This is a standing policy — apply it whenever a new unlinked file is added or discovered.

**For Markdown files:** Add a blockquote at the very top of the file:
```
> **A note on transparency:** This file lives in the public repository but is intentionally unlinked from the main project index. [One sentence on why — e.g. speculative content, development artifact, etc.] The main entry point for the Zero Paradox is [README.md](README.md).
```

**For PDF files:** Add an amber callout box as the first element in the document (before the title block), using the `callout(text, bg=AMBER_LITE, border=AMBER)` helper in the build script. Wording should follow the same pattern: explain the document is unlinked, why, and direct the reader to the README.

**If no build script exists for an unlinked PDF:** The correct action is to archive it to `historical/` rather than leave it unnoticed in the root. Standalone documents without active build scripts are almost always superseded development artifacts. Follow the archiving convention above.

## Development Environment

This project runs on **Windows 11**. Shell commands must use PowerShell syntax, not Unix/Bash.

- **File discovery:** Use the `Glob` tool — never `find` (hangs on this system) or `ls`
- **Shell commands:** Use the `PowerShell` tool — never `Bash` with Unix-style commands
- **File verification:** Use `Get-ChildItem *.pdf` not `ls *.pdf`
- **File moves:** Use `Move-Item` not `mv`
- **Path separators:** Backslash in PowerShell (`C:\Workspace\ZeroParadox`), forward slash in Lean/lake config

## README.md Maintenance

The `.copilot-instructions.md` file is the authoritative style guide for README updates. Key rules:
- Links display as clean names: `[ZP-A Lattice Algebra](ZP-A_Lattice_Algebra_v1_1.pdf)` — no version or extension in display text
- Use regular hyphens (`-`), not em dashes (`—`); mathematical arrows (`→`) are fine
- Section order must follow the structure defined in `.copilot-instructions.md`
- Before editing, verify all linked files actually exist using the `Glob` tool (pattern `*.pdf`)

## Archiving Old Document Versions

When a document is superseded:
1. Add a numeric suffix to the old file and move it: `Move-Item ZP-X_Title_vN_N.pdf historical\ZP-X_Title_vN_N-1.pdf`
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
- Always use `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` to verify proofs; the log file allows local debugging via tail.
- **Logging Rule:** When performing builds on `lake_testing`, use `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` to allow for local log tailing.
- Ignore PDF rendering assets and website build artifacts in the root.
- Treat 'lake_testing' as the active branch for experimental verification.
- Always check 'lake-manifest.json' for dependency updates before adding new imports.

- When searching for Lean source files in this project, always use the pattern ZeroParadox/**/*.lean, never **/*.lean. The .lake/ folder contains thousands of Mathlib library files that aren't mine."

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
   - **Auto-push:** After every commit on `lake_testing`, immediately run `git push origin lake_testing`. Tim has granted standing permission for this; no confirmation needed.
   - PDF creation or rendering actions **must** happen on `illustrated`.
2. **Mandatory Checkout:** If the user requests an action belonging to the other workspace, Claude must prompt the user to switch branches before reading or writing those specific assets.
3. **Math Workflow:** When on `lake_testing`, always run `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` to verify theorem changes. The log file allows local debugging via log tailing.
4. **PDF Workflow:** On the `illustrated` branch, use existing rendering scripts and strictly follow the document versioning and archiving conventions defined above.
5. **Transparency:** Maintain the `.claude-local/` folder for in-progress scripts and internal notes as a private "collaboration buffer."

## File Priority & Access
- **On `lake_testing`:** Prioritize `.lean` source files. Treat `/site` and `/pdfs` as Read-Only unless explicitly authorized for a cross-domain check.
- **On `illustrated`:** Prioritize PDF artifacts and rendering scripts. Treat `/ZeroParadox` source files as the "Ground Truth" reference for documentation updates.

## File Priority
- Focus on `.lean` and `lakefile.lean` for the ontology.
- Assets in `/site` and `/pdfs` are open for editing **only** for reredering tasks.

## Lean 4 Proof Development: Stub-First Protocol

As proofs grow more complex (ZP-D onward), always use a stub-first approach before writing full proofs. This prevents session hangs caused by heavy import chains and typeclass resolution.

**The workflow for every new ZP-X Lean file:**

1. **Symbol map** — before writing any Lean, map each PDF symbol to its Lean 4 / Mathlib equivalent. Identify which imports are required and which are dangerously heavy (p-adics + EuclideanSpace together, for example, can cause elaborator hangs).
2. **Stub file** — write the complete file with all definitions and theorem statements, but use `sorry` for every proof body. Add `set_option maxHeartbeats 400000` at the top. Do not write proof bodies during the planning or stub step — output the stub file and stop. Wait for a clean build before proceeding.
3. **Build the stub** — run `lake build` and confirm 0 errors on the skeleton. This validates that types elaborate correctly before any proof work begins.
4. **Commit the stub** — commit the sorry-stubbed file immediately after a clean build. This creates a rollback point before any proof work begins.
5. **Fill proofs incrementally** — prove one theorem at a time, building after each. Commit after each theorem is successfully proved. Do not attempt to write all proofs before checking.
6. **Final clean build** — once all `sorry`s are removed, run a final build to confirm 0 errors and 0 warnings, then proceed to the documentation workflow below.

**When to abstract away heavy dependencies:** If a layer imports both p-adic numbers and Hilbert space machinery, consider whether the cross-layer dependency can be replaced with an abstract typeclass or index type (e.g., `Fin (2^k)` instead of `ℚ_[2]`) for the purposes of the proof. Decoupling reduces elaboration load significantly.

## Proof Documentation Workflow

When a ZP-X document is successfully proved in Lean 4, the following steps are **mandatory** before the work is considered complete:

1. **Build clean** — run `lake build 2>&1 | tee build.log` and confirm zero errors and zero warnings. (Tim tails the log locally via PowerShell: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8`.)
2. **Purity check** — add a `#print axioms` block at the bottom of every ZP-X Lean file (inside a `section PurityCheck ... end PurityCheck`), one call per proved theorem. The expected result is `'theorem_name' does not depend on any axioms`. Any kernel axiom that appears (`Classical.choice`, `propext`, `Quot.sound`) must be explicitly noted and justified in the proof doc.
3. **Create proof doc** — write `proofs/ZP-X_Lean4.md` documenting: Lean file path, commit hash, build result, purity check output, theorem-by-theorem table, and proof strategy notes.
4. **Update README.md** — add a row to the `### Formal Verification (Lean 4)` subsection of the Document Index and update the Open Questions table row for `Formal verification (Lean/Rocq)`.
5. **Commit all changes together** on `lake_testing`.