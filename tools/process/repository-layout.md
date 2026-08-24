# Repository layout, guiding principles, and the private working folder

**Body for `CLAUDE.md` § `R-CONTEXT`.** The rule is there; the guiding principles, the
repository inventory, the document-versioning conventions and the transparency position
on the private working folder are here.

---

## Guiding Principles (from Project Instructions)

- **Logical Rigor First:** The primary goal is logical consistency and rigor. 
- **Prose Role:** Use prose only to restate mathematics into accessible language. 
- **Ontology Focus:** Finalized documents must be structured as an ontology. 
- **Persistence:** All completed work must be committed back to the repository immediately to prevent data loss.

## Repository Nature

This is a **mathematical publication repository** first. It is no longer true that there is "no build system, test suite, or source code" — there is a Lean 4 corpus with CI, and as of 2026-08-15 a tracked verification suite — but the PDFs and the Lean remain the point, and the tooling exists to keep them honest. The repository contains:

- PDF documents (the formal mathematical framework and illustrated companions)
- The Lean 4 corpus under `ZeroParadox/`, with `MANIFEST.md` as its by-folder index
- Markdown documentation (README.md, ABOUTME.md, this file)
- (superseded document versions are preserved in git history and per-release Zenodo snapshots; the `historical/` folder was retired in v3.0)
- `scripts/` — the PDF build tooling. Their only home since 2026-08-15, not a transparency mirror
- `tools/verify/` — the checkers, pipeline and baselines that gate every commit and push
- `tools/registry/`, `tools/render/` — the declaration extractor and the diagram generators

## Private Working Folder

A `.claude-local/` folder exists locally. **It is its OWN git repository** — its own history, a `master` branch, and a private remote (`ZeroParadoxLocal`) — and the public repo additionally ignores that path, so none of it appears here. This is intentional.

⚠ **"Gitignored" is TRUE and INCOMPLETE, and the missing half is the half that matters** (Tim, 2026-08-22). The parent really does ignore the path — that is what keeps it out of the public repo. **It is ALSO its own repository with a private remote, and that remote is what provides the off-machine copy.** Reason only from the ignore entry and you conclude the sole copy is on disk and that protecting it is someone else's problem — which is exactly what happened on 2026-08-22, when three commits sat unpushed while the `PostToolUse` robocopy that used to catch them had been dead since agents lost the ability to run that command. **Commit AND push it; the handoff's PART 0b step 4 is the procedure, and the push is what makes the copy exist.** It serves as a private working space for the project's core collaborators during active development, before material is ready for public discourse. It contains:

- Reviewer feedback and correspondence (e.g. `feedback/`)
- In-progress build scripts and draft outputs
- Session notes and development artifacts

Transparency is a core value of this project. The existence of this private folder is acknowledged here precisely for that reason: readers of the public repo can see that private collaboration is occurring, understand its purpose, and know that the mathematical content and editorial decisions will be surfaced publicly as the work matures. Nothing in `.claude-local/` affects the formal mathematics — that lives entirely in the committed PDFs.

## Document Versioning Conventions

- Current documents live at the root with **flat (version-free) filenames**: `ZP-X_Title.pdf`
- Version numbers are tracked in `register.md` (Formal Version column) and in each PDF's title block — not in the filename
- Superseded versions are **not** archived to a folder (the `historical/` folder was retired in v3.0); the flat root PDF is overwritten in place, and git history + each release's Zenodo snapshot are the record
- README.md and GUIDE.md always link to the flat root filename
