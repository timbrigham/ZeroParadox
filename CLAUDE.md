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

## scripts/ Folder — Keeping It Current

The `scripts/` folder is a public transparency copy of the active build scripts from `.claude-local/`. It must be kept current: whenever a build script in `.claude-local/` produces a newly committed PDF, copy the script to `scripts/` as part of the same commit.

**Rule:** After committing a new or updated PDF on the `illustrated` branch, copy the corresponding build script:
```
Copy-Item .claude-local\build_X.py scripts\build_X.py
```
Then stage and include it in the commit (or as a follow-up commit on the same branch).

If a script is new (not yet in `scripts/`), add a row for it to `scripts/README.md` at the same time.

The `scripts/` folder is intentionally not a runnable package — the README there sets that expectation explicitly. The goal is source visibility, not distribution.

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
- **Never prepend `cd`:** The working directory is always `C:\Workspace\ZeroParadox` at session start. 
- **Never prepend `cd C:\Workspace\ZeroParadox;` or `Set-Location` to any command — doing so creates command strings that don't match the allowlist and triggers unnecessary permission prompts.
- **File verification:** Use `Get-ChildItem *.pdf` not `ls *.pdf`
- **File moves:** Use `Move-Item` not `mv`
- **Path separators:** Backslash in PowerShell (`C:\Workspace\ZeroParadox`), forward slash in Lean/lake config

## README.md Maintenance

### Document Structure

The README must maintain this section order:

1. Title and date — `# The Zero Paradox - Project Index`
2. "What This Is" — high-level introduction
3. "The Central Result" — core theorem and derivation chain
4. "What This Is Not" — explicit clarifications
5. "The Framework" — tables of all available documents
6. "Axiomatic Commitments" — formal commitments and principles
7. "Question Register" — tracked questions and resolutions
8. "Reading Order" — paths for different reader types with clickable links
9. "Notes on Development" — credits and contributor information
10. "Repository and Version History" — Git/versioning guidance
11. "Purpose of This Repository"
12. "License"
13. "Citation"
14. "Contact"

### Formatting Standards

**File links:**
- Display text uses clean names — no file extensions, no version numbers
  - Correct: `[ZP-A Lattice Algebra](ZP-A_Lattice_Algebra_v1_2.pdf)`
  - Wrong: `[ZP-A Lattice Algebra v1.2.pdf](...)`
- Link targets always point to the current (non-suffixed) version

**Text:**
- Use regular hyphens (`-`), not em dashes (`—`); mathematical arrows (`→`) are fine

**Tables:**
- Consistent column alignment; meaningful headers (File, Document, Version, Contents)
- Version numbers go in the Version column only, not in display text

### Reading Order Structure

Include four distinct paths:
1. **General reader** — Foreword → any Illustrated Companion → ZP-E Companion
2. **Mathematician** — formal path ZP-A through ZP-E
3. **Category theory extension** — ZP-G and ZP-H (after ZP-E)
4. **Process/methods** — ZP Tools and Methods

All entries must be clickable links, not plain text.

### Validation Checklist

Before committing any README update:
- [ ] All linked files verified to exist (use `Glob` tool, pattern `*.pdf`)
- [ ] No file extensions in display text
- [ ] No version numbers in display text
- [ ] No em dashes — regular hyphens only
- [ ] Reading Order has clickable links for all documents
- [ ] All four terminal sections present: License, Citation, Contact, Purpose
- [ ] "What This Is Not" section present after "The Central Result"
- [ ] Axiomatic Commitments matches current framework state (AX-1 is T-SNAP, not an axiom)
- [ ] Open questions table reflects actual current status

### README Sync Requirements — Triggers and Checklist

Certain changes require README.md to be audited for consistency. Apply this checklist whenever any of the following occur:

**Triggers:**
- A document is versioned up (e.g. ZP-A v1.3 → v1.4)
- An open question is closed (in any document)
- A claim's status changes (axiom → theorem, candidate → derived, etc.)
- A new document is added or archived

**On each trigger, verify:**
1. **Framework table** — version number matches the current file in the root
2. **Reading Order links** — all version numbers in Reading Order match Framework table (these get out of sync when only the table is updated)
3. **Question Register** — every OQ/item that changed status is updated; newly closed items are added if missing
4. **Document descriptions** — any "Candidate Theorem", "Open", or status language in the Framework table description column still accurately reflects the document's current state

**Known pattern to watch:** Reading Order links are hardcoded with version numbers separately from the Framework table. Updating the table does not update Reading Order — both must be changed together. This has caused stale links on ZP-A (v1.2 in Reading Order while Framework showed v1.4) and ZP-H (v1.0 in Reading Order while Framework showed v1.1).

### Common Updates

**Adding a new document:**
1. Add to the appropriate The Framework section
2. Use clean display name (no extension, no version)
3. Link to the current version (no `-1`, `-2` suffix)
4. Put version number in the Version column only
5. Verify file exists with `Glob` before committing

**Removing a broken link:**
- Verify with `Glob` tool (never `ls`) before removing
- Ask: should this file be created, or is it genuinely absent?

**Historical folder table format** (`historical/README.md`):
```
| [ZP-A_Lattice_Algebra_v1_1-1.pdf](ZP-A_Lattice_Algebra_v1_1-1.pdf) | YYYY-MM-DD | Brief description of what this version was |
```
- File column: use the actual archived filename in both display text and link
- Date: YYYY-MM-DD (date moved, not date of document)
- Keep entries newest-first

## Archiving Old Document Versions

When a document is superseded:
1. Add a numeric suffix to the old file and move it: `Move-Item ZP-X_Title_vN_N.pdf historical\ZP-X_Title_vN_N-1.pdf`
2. Add the new version to the root (no suffix)
3. Update `historical/README.md` with a table row: `| [filename](filename) | YYYY-MM-DD | description |`
4. Update the version number in README.md's The Framework table

## Theorem/Proposition/Lemma Naming Convention

All formal ZP documents use the following hierarchy for naming results. Apply this consistently when drafting or editing any formal layer:

- **Theorem**: The primary result of a section — of major significance for the framework. Reserve for results that drive the dependency chain or that are the central claim of a layer (e.g., T3 Monotonicity, T-SNAP).
- **Proposition**: A derived result that is rigorously proved but subsidiary to the main theorems — true and important, but not the headline claim (e.g., T1 partial order, T2 clopen balls).
- **Lemma**: A technical helper result used as a stepping stone toward proving another result (e.g., L-RUN, T2 global minimum).
- **Corollary**: A result that follows immediately from a theorem, proposition, or lemma with no substantial additional work (e.g., C1, C2, C3, T1b). Mark with "Corollary" label.
- **Conditional Claim (CC)**: A result that holds only given an explicit modelling commitment not derivable from the axioms (e.g., CC-1: S₀ = ⊥).
- **Design Principle (DP)**: A design commitment — well-motivated and explicit — that is chosen rather than derived (e.g., DP-1: orthogonality).
- **Remark (R)**: An observation providing context or clarification; does not require proof.

When assigning a label, ask: "Is this result the central claim of its section, or is it infrastructure for something else?" Central claims are Theorems; infrastructure is Propositions or Lemmas.

## Framework Structure (for context)

The Zero Paradox is a multi-layer mathematical ontology proving the Binary Snap (⊥ → ε₀) as a theorem. The dependency order of the formal layers is:

**ZP-A** (lattice algebra) → **ZP-B** (p-adic topology) → **ZP-C** (information theory) → **ZP-D** (state layer) → **ZP-E** (DA-1/T-SNAP derivation)

**ZP-G** (category theory) → **ZP-H** (categorical bridge) — self-contained; depends on ZP-E conceptually but not formally.

Each formal document has a paired illustrated companion for general readers. AX-G1 and AX-G2 are the two structural commitments of ZP-G's categorical layer. Neither is a novel commitment: AX-G1 is grounded in ZP-A's bottom element ⊥; AX-G2 follows from ZP-A antisymmetry and ZP-B C3 (topological irreversibility). ZP-G is self-contained by design and states them explicitly within that layer. AX-B1 (binary existence) is not a novel commitment — it is directly verifiable by computation (decidable equality on Fin 2 via `decide`) and depends only on `propext`, not `Classical.em`. AX-1 (Binary Snap Causality) is now Theorem T-SNAP, derived in ZP-E — do not refer to it as an axiom.

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
| Theorem/proposition/lemma hierarchy missing | **Fixed in v1.5** | Full naming convention added to CLAUDE.md and all formal docs updated |
| "State sequence" doesn't convey monotone condition | **Fixed in v1.5** | Remark R2 added after D3 connecting "state sequence" to "ascending chain" |
| CC-1: ⊥ ≤ S₀ should be free from T2, not a commitment | **Fixed in v1.5** | CC-1 corollary reworded: T2 gives ⊥ ≤ S₀ unconditionally; CC-1 strengthens to equality |
| Add examples for state sequences | Deferred to Companion | Companion already has power set and document history examples; formal doc adds companion cross-reference note |

## License

CC BY-NC-ND 4.0 — share with attribution; no modifications; no commercial use.


# .claudecodes instructions for Lean 4 development
- Always run lake build as two separate PowerShell calls to avoid allowlist prompt issues: first `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8`, then `Get-Content build.log | Select-Object -Last 1` (or with a `-match` filter). Never combine them with `;` in a single call.
- **Logging Rule:** When performing builds on `lake_testing`, run as two separate calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` then `Get-Content build.log | Select-Object -Last 1`.
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
3. **Math Workflow:** When on `lake_testing`, verify theorem changes with two separate calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` then `Get-Content build.log | Select-Object -Last 1`.
4. **PDF Workflow:** On the `illustrated` branch, use existing rendering scripts and strictly follow the document versioning and archiving conventions defined above.
5. **Transparency:** Maintain the `.claude-local/` folder for in-progress scripts and internal notes as a private "collaboration buffer."
6. **Sync before work on `illustrated`:** At the start of any session on `illustrated`, always run `git fetch origin main` then `git merge origin/main` before making any changes. Never make edits on `illustrated` against a stale base — this causes avoidable merge conflicts when the PR is opened.
7. **Verify no conflict markers after any merge:** Before committing after a merge, run `git diff --check` to confirm no conflict markers (`<<<<<<<`, `=======`, `>>>>>>>`) remain in any file. A file with unresolved markers will commit silently and corrupt the document. This has happened twice on this project.
8. **Pull request body — always use `--body-file`:** PowerShell cannot reliably pass multiline PR bodies inline (special characters, arrows, backticks, and asterisks all cause parse errors). Always write the body to `.claude-local\pr_body_<name>.md` first, then create the PR with:
   ```powershell
   gh pr create --title "..." --body-file ".claude-local\pr_body_<name>.md"
   ```

## File Priority & Access
- **On `lake_testing`:** Prioritize `.lean` source files. Treat `/site` and `/pdfs` as Read-Only unless explicitly authorized for a cross-domain check.
- **On `illustrated`:** Prioritize PDF artifacts and rendering scripts. Treat `/ZeroParadox` source files as the "Ground Truth" reference for documentation updates.
- **`proofs/` is owned by `lake_testing` exclusively.** Never edit files in `proofs/` from the `illustrated` branch — doing so causes merge conflicts when branches are reconciled.

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

1. **Build clean** — run as two separate calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` then `Get-Content build.log | Select-Object -Last 1`. Confirm zero errors and zero warnings.
2. **Purity check** — add a `#print axioms` block at the bottom of every ZP-X Lean file (inside a `section PurityCheck ... end PurityCheck`), one call per proved theorem. The expected result is `'theorem_name' does not depend on any axioms`. Any kernel axiom that appears (`Classical.choice`, `propext`, `Quot.sound`) must be explicitly noted and justified in the proof doc.
3. **Create proof doc** — write `proofs/ZP-X_Lean4.md` documenting: Lean file path, commit hash, build result, purity check output, theorem-by-theorem table, and proof strategy notes.
4. **Update README.md** — add a row to the `### Formal Verification (Lean 4)` subsection of the The Framework and update the Question Register row for `Formal verification (Lean/Rocq)`.
5. **Commit all changes together** on `lake_testing`.