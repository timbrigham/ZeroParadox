# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

**Gate exemption — this file and operational meta.** `CLAUDE.md` itself (and other internal operating-instruction / meta files, as opposed to the mathematical publication content) is **exempt from the Editorial Review Gate and the Adversary Review Gate** below. The review gates are scoped to externally-facing publication prose — formal documents, companions, README.md/GUIDE.md, build-script prose. `CLAUDE.md` is the operating manual, not publication content, so it needs **version control only**: commit and push normally, and use `git push --no-verify` if the pre-push hook blocks on a stale review signal for a `CLAUDE.md`-only change.

## Editorial Review Gate — Hard Rule

**Any commit touching document prose requires editorial review to have completed before the commit is made.** This applies to:

- Changes to any build script `body()`, `cbody()`, `sp()`, or box-helper string content
- Changes to README.md, GUIDE.md, RELEASES.md, or any `.md` file in the repo root (except `CLAUDE.md` — see the gate exemption above)
- Changes to any companion or formal document build script
- Changes to register.md

**The protocol:**
1. Before committing any of the above, run `/editorial-review` (pre-commit mode — no arguments needed; it reads `git diff --staged` automatically)
2. Wait for the editorial agent to return a verdict
3. If FAIL: resolve every item in the kill list before committing
4. If PASS: the agent writes `.claude-local/er_cleared.txt` with the current HEAD hash — proceed with the commit

Same-session self-review does not satisfy this requirement. `/editorial-review` spawns a fresh agent with no conversation history.

The pre-push hook checks `.claude-local/er_cleared.txt` and `.claude-local/ar_cleared.txt` against HEAD before allowing any push. If either signal is missing or stale the push is blocked. Override with `git push --no-verify` only when both reviews have been run and the signal files are stale due to a trivial amendment.

## Adversary Review Gate — Hard Rule

**Any public-facing action requires adversary review to have completed before execution.** This is non-negotiable and applies to every action that puts content in front of an external reader:

- `git push` containing changes to prose in any tracked file (Lean source docstrings, build script `body()` calls, README.md, GUIDE.md, any companion script)
- Sending an email to any external party
- Posting or editing a GitHub Discussion body or follow-up comment
- Posting or editing a GitHub Issue
- Any other action that surfaces content outside this repository

**The protocol:**
1. Before executing any of the above, Claude must explicitly ask: "Adversary review complete for this content?"
2. Wait for Tim's confirmation before proceeding — do not self-assess whether review is needed
3. If review has not been run, offer to run `/adversary-review` on the relevant content first
4. If PASS: the agent writes `.claude-local/ar_cleared.txt` with the current HEAD hash
5. Only after explicit confirmation may the public-facing action execute

Same-session self-review does not satisfy this requirement. The review must be a separate adversarial context (spawned Agent with no conversation history).

**What triggered this rule:** Lean docstring and build script prose changes were pushed on 2026-05-20 before adversary review ran. The review subsequently found two additional precision errors in the already-committed content.

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

A `.claude-local/` folder exists locally and is **gitignored** — it does not appear in the public repository. This is intentional. It serves as a private working space for the project's core collaborators during active development, before material is ready for public discourse. It contains:

- Reviewer feedback and correspondence (e.g. `feedback/`)
- In-progress build scripts and draft outputs
- Session notes and development artifacts

Transparency is a core value of this project. The existence of this private folder is acknowledged here precisely for that reason: readers of the public repo can see that private collaboration is occurring, understand its purpose, and know that the mathematical content and editorial decisions will be surfaced publicly as the work matures. Nothing in `.claude-local/` affects the formal mathematics — that lives entirely in the committed PDFs.

## Document Versioning Conventions

- Current documents live at the root with **flat (version-free) filenames**: `ZP-X_Title.pdf`
- Version numbers are tracked in `register.md` (Formal Version column) and in each PDF's title block — not in the filename
- Superseded versions are moved to `historical/` **with the version number added**: `ZP-X_Title_vN_N.pdf` (no `-1` suffix needed since the root filename is flat)
- The `historical/README.md` tracks all archived files with date moved and description
- README.md and GUIDE.md always link to the flat root filename

## GitHub Releases and Zenodo Snapshots

GitHub Releases trigger automatic Zenodo snapshots with permanent DOIs. `RELEASES.md` is the human-readable record of each release.

### Release naming

`v<major>.<minor>` - e.g. `v1.0`, `v1.1`, `v2.0`

### What triggers a release

- **Major version** (`v1.0 → v2.0`): a new formal layer added, or a theorem status changes (candidate → derived), or a significant structural revision to the framework
- **Minor version** (`v1.0 → v1.1`): a substantive reviewer feedback round addressed, or accumulated document/companion updates that represent a meaningful state of the framework

**Do not release on:** every individual PR. Releases should feel like milestones worth timestamping.

**Lean-only changes are an open question, not an automatic trigger (either way).** The release model is document-centric: `RELEASES.md` is built around a "Document versions" table, and the candidate→derived trigger above refers to *tracked, labeled* results in formal documents (carried in `register.md`), not to a placeholder proved only inside a `.lean` file. When a Lean milestone lands without accompanying formal prose (e.g. a conjecture proved only in Lean, no PDF document or companion moved), do not assume it warrants a release, and do not assume it doesn't - raise it as an explicit question for Tim. The two clean resolutions are: (a) bundle it into the next document release, or (b) write the result up as formal prose first, then release. Example: the wheel of fractions (§VIII conjecture → theorem, ZPJ_Wheel/ZPJ_WheelFrac) landed 2026-06-06 as a Lean-only change and was flagged, not auto-released.

### Release workflow

When Tim initiates a release: draft the `RELEASES.md` entry → PR → after merge, draft the GitHub Release body → **wait for explicit approval** → execute:
```
gh release create <tag> --target main --title "<tag> - <title>" --notes-file ".claude-local\release_<tag>_body.md"
```
Then grab the Zenodo DOI badge and add to README.md in a follow-up commit.

**`.zenodo.json` check — mandatory before every release:** Read `.zenodo.json` and verify the `description` field accurately reflects the current layer count and layer list. Update it in the same PR as `RELEASES.md` if anything is stale. Zenodo reads this file at release creation time; it cannot be updated retroactively via the repo (only via the Zenodo web UI).

**Engineer's Take check — mandatory before every release (hard gate):** Before cutting any release, grep the Lean sources for outstanding Engineer's Take placeholders — at minimum `TODO (Tim)` and `TODO: Engineer's Take` across `ZeroParadox/*.lean` (also scan for any `## Engineer's Take` heading followed immediately by an empty section). Every ZP-X Lean file included in the release must have its Engineer's Take filled in Tim's own voice. **A release is BLOCKED until all are filled.** Claude never writes these — they must be Tim's own language (see the Engineer's Take convention) — so this gate catches the omission, it does not fill it. Surface the list of unfilled takes to Tim and wait for his prose. (Added 2026-06-11 after the four ZP-H functor takes plus ZP-L's were almost missed at the v2.4 threshold.)

**RELEASES.md format:** `## vX.Y - YYYY-MM-DD` header, then **Why this release** (one sentence), **What changed** (bullets), **Document versions at this release** (table), **Next threshold**. Match existing entries in RELEASES.md for exact formatting.

## register.md — Canonical Version Registry

`register.md` is the authoritative source for all current document version numbers, filenames, and companion versions. It is committed to the public repository but intentionally unlinked from both README.md and GUIDE.md (and carries a transparency notice per the Transparency Notices policy).

**Schema:** One row per formal document:
`| Document | Formal Version | Filename | Companion Version | Notes |`

**Rule: update register.md first.** On any version bump — before touching README.md, GUIDE.md, or build script docstrings — update register.md. README.md's Framework table and GUIDE.md's Reading Paths are then verified against it.

**On every version bump, in order:**
1. Update register.md (formal version, filename, companion version if changed)
2. Update README.md Framework table (verify against register.md)
3. Update GUIDE.md Reading Paths links (verify against register.md)
4. Update build script docstring
5. Archive old version per archiving convention

## Companion Document Versioning

Each formal ZP-X document has a paired illustrated companion (`ZP-X_Illustrated_Companion.pdf`). Companion PDFs overwrite in place — no versioned filename, no `historical/` archiving. The current companion version lives only in the title block of the PDF and the docstring of its build script.

### Companion sync rule

**Whenever a formal document is updated, review its companion in the same session.** Ask:
- Does the companion describe any result whose label or status changed? (e.g., "Candidate Theorem" → "Theorem T-SNAP", CC-2 added, RP-2 added)
- Does the companion omit a new result a general reader would benefit from? (e.g., L-INF, a new lemma or design principle)
- Does the companion's key result box or closing summary still accurately reflect the framework state?

If yes to any of these, update the companion and bump its internal version number in the same commit as the formal document. Do not leave the companion behind.

### Bumping a companion version

When updating a companion, change:
1. The subtitle paragraph in `build()`: e.g., `'Information Theory | Version 1.4'` → `'Version 1.5'`
2. The docstring at the top of the build script

Companion version numbers are independent of formal version numbers. What matters is that the companion is not materially stale.

### Version numbers and changelogs in rendered PDF content (ALL PDFs)

**This rule applies to every PDF in the project — formal layers, companions, addenda — not just companions.** (Generalized 2026-06-13, Tim: version changelogs in rendered content should be "murdered by the style guide and review." Scope is **rendered PDF content only** — build-script docstrings and `register.md`/`RELEASES.md` are the changelog of record and are exempt; git history is the real changelog.)

**The document's OWN version must appear in exactly one place in rendered PDF content: the subtitle / tagline meta line** (`'... | Version ' + VERSION + ' | ...'`; formal-doc footers via `make_doc()` may also carry it). Nowhere else in rendered content — not in disclaimers, section headers, body prose, title-block notes, endnotes, or status/provenance tags.

**No self-version changelogs or provenance tags in rendered PDF content.** A title-block "note" or endnote narrating `"v1.1: Added X. v1.0: Initial release…"` is a violation — this was the standard formal-doc pattern (e.g. ZP-M) and is now retired. The title-block note must describe what the document *is*, not its version history. Violations include: `"New in v1.6"`, `"In v2.7, DA-1 was upgraded"`, `"End of ZP-X v1.0"`, `"Updated ZP-E v3.0 | …"`, and status/provenance tags such as `[unchanged from v1.0]`, `[new in v1.7]`, `[rebuilt in v1.1]`, `Relabelled in v1.2`, `Supersedes v1.4`. Strip them on discovery and bump the version.

**EXCEPTION — cross-document version citations are ALLOWED (Tim, 2026-06-14).** A reference to *another* document's version (e.g. `"T-SNAP derived in ZP-E v2.0"`, `"Closed in ZP-G v1.1"`) is a legitimate citation, not a self-changelog, and is **not** a violation. The rule targets a document's references to *its own* version history, not citations of where a result landed in a sibling layer.

**Editorial review enforces this as a kill** for any rendered mention of the document's OWN version beyond the single meta line, or any rendered self-version changelog/provenance tag. Cross-document version citations are exempt.

### Companion sync checklist

Run this whenever a formal document version changes:
- [ ] Key result box / closing summary still accurate
- [ ] Changed theorem or claim labels updated in plain language (e.g., "AX-1 is a Candidate Theorem" → "T-SNAP is a proven theorem")
- [ ] New results relevant to a general reader added with plain-language explanation
- [ ] Internal version string bumped if any changes were made
- [ ] Build script docstring updated to match

### Companion prose precision checklist

Apply this when drafting or reviewing any companion section that makes claims about mathematical structures, properties, or comparisons. The same errors can appear in formal document preambles and contextual sections — it does not apply to formal theorem statements, which are held to a separate standard via Lean verification.

**Category 1 — Precision errors:** Using the wrong technical term for the actual mathematical property being claimed. Common risk: describing a valuative property (e.g., v₂(0) = +∞) using topological vocabulary (e.g., "topologically isolated"), or using metric language for an algebraic property. Before using any technical term, verify it names the correct property in the correct sub-field.

**Category 2 — Invented terminology:** Using informal or invented phrases as if they were recognized mathematical concepts. Any non-standard term that sounds technical risks confusing readers who know the actual vocabulary. Use standard terminology or explicitly flag non-standard usage as informal/metaphorical.

**Category 3 — Directional ambiguity:** Claims where it is unclear whether the sentence is describing a property a structure has (and saying that's bad) or prescribing what a structure should have (and saying it falls short). Any sentence of the form "X is Y" near a comparison between two mathematical structures should make the normative/descriptive distinction explicit.

**Category 4 — Context-free structural claims:** Asserting something as universally true that is only true within the ZP framework. Claims about zero or ⊥ that are true in the ZP context may be false in most mathematical frameworks. Scope all such claims explicitly to the ZP setting.

**Category 5 — Scope overclaiming:** A statement implying a broader negative conclusion than intended. Universal quantifiers ("any domain," "every structure") applied to a ZP-specific limitation overstate the claim. Narrow the scope to what is actually proved.

## Vocabulary Reference Guide — Standing Update Rule

A vocabulary reference guide lives at `.claude-local/vocabulary_reference.md`. It is the authoritative list of:
- Terms to avoid or replace (technically loaded words used incorrectly, or invented ZP jargon)
- Terms requiring a plain-language gloss for non-specialist audiences
- ZP-internal vocabulary and how to describe it externally

**Standing rule:** Whenever a vocabulary problem is surfaced — by Dan, by an adversary review kill-list, or by any external reviewer — update `.claude-local/vocabulary_reference.md` in the same session before the session ends. Add a row to the Update Log with the date, source, and term. Do not leave vocabulary fixes as one-off edits without capturing the general rule.

This rule applies to both directions:
- A term flagged as wrong (e.g., "isolated," "membership status") → add to Section 1
- A term flagged as needing a gloss (e.g., "valuation," "clopen") → add or verify in Section 2

## Build Script Hash Integrity

`register.md` records a SHA-256 fingerprint (first 8 chars) of every formal and companion build script in the `formal:XXXXXXXX comp:XXXXXXXX` token embedded in each row's Notes field.

**Standing rule — any script change requires all four steps in the same commit:**
1. Make the change and bump the internal version number
2. Rebuild the PDF and archive the old version
3. Recompute the hash: `python -c "import hashlib; print(hashlib.sha256(open('.claude-local/build_X.py','rb').read()).hexdigest()[:8])"`
4. Update the hash token in `register.md`

**Session start check:** Run `python .claude-local/check_hashes.py` at the start of any session that will touch build scripts. A mismatch means a script was modified without completing the full four-step workflow — version bump and PDF rebuild are overdue.

A hash mismatch is not just a "rebuild needed" signal — it means the version bump step was skipped. Do not rebuild without incrementing the version number.

## PDF Build Standards

**Before building any PDF in this project** — formal layer, companion, or otherwise — read `.claude-local/PDF_Rendering_Standards.md`. It is the single authoritative source for font stack, glyph rendering, table cell formatting, HTML entities, subscript/superscript rules, and pre-build verification. All rules there apply to every PDF build without exception.

## Companion PDF Diagram Layout Standards

These rules apply to every `Drawing` object in every companion build script. Violations cause diagram content to overflow the declared bounding box and render over surrounding text — a recurring issue that has required multiple retroactive fixes.

### Diagram height and cy rules

**Rule 1 — Never derive `cy` from `dh` when the diagram contains fixed-size elements (circles, boxes, labels at fixed offsets).** `cy = dh * fraction` is only safe when all content scales with `dh`. If any element has a fixed radius `r` or a fixed offset, use a fixed numeric `cy` instead.

**Rule 2 — Verify bounds before committing.** After placing all elements, check:
- `max_y = max content y` must satisfy `max_y < dh - 10`
- `min_y = min content y` must satisfy `min_y > 5`

The minimum margin is 10 pts top and 5 pts bottom. If either fails, increase `dh` or adjust `cy`.

**Rule 3 — Common overflow sources to check explicitly:**
- Labels below circles: `cy - r - label_offset` — goes negative when `cy` is too small
- Labels above circles: `cy + r + label_offset` — exceeds `dh` when `cy` is too large  
- Internal title strings at `dh - N` — conflict with top circle labels when both are near the top
- Caption strings at fixed `y=10` inside the drawing — safe, but check nothing else sits at the same y

**Rule 4 — Internal title strings are usually redundant.** Diagrams that have both a title string inside the `Drawing` and a `ccaption()` below it should drop the internal title. It adds clutter and occupies the same crowded top zone as circle labels.

### Pre-build checklist for new diagrams

- [ ] `cy` is a fixed value, not `dh * fraction` (unless all elements scale with `dh`)
- [ ] Calculated `max_y < dh - 10` and `min_y > 5` for all content
- [ ] No internal title string that duplicates the caption
- [ ] `dh` expressed in inches with comment: `# N * 72 = M pts; content top = X, content bottom = Y`

## README.md Link Restrictions

The following files exist in the repository but **must not be linked from README.md or GUIDE.md** until the conditions below are met:

| File | Reason | Condition to lift restriction |
|------|--------|-------------------------------|
| `ZP_Gen2_Applications.pdf` | Speculative applications document — depends on Gen 1 being formally complete and bridge documents written. Premature to surface publicly in the index. | All Gen 1 layers (ZP-A through ZP-H) fully tightened; thermodynamic bridge and OQ-E2 resolved; explicit decision by Tim to promote. |
| `ABOUTME.md` | Not ready for prominent public linking from the main index. | Explicit decision by Tim to promote. |

Do not add links to these files in README.md or GUIDE.md under any circumstances without explicit instruction. They may exist in the repo and be committed — they just must not appear in either index.

## scripts/ Folder — Keeping It Current

The `scripts/` folder is a public transparency copy of the active build scripts from `.claude-local/`. It must be kept current: whenever a build script in `.claude-local/` produces a newly committed PDF, copy the script to `scripts/` as part of the same commit.

**Rule:** After committing a new or updated PDF on the `illustrated` branch, copy the corresponding build script:
```
Copy-Item .claude-local\build_X.py scripts\build_X.py
```
Then stage and include it in the commit (or as a follow-up commit on the same branch).

If a script is new (not yet in `scripts/`), add a row for it to `scripts/README.md` at the same time.

The `scripts/` folder is intentionally not a runnable package — the README there sets that expectation explicitly. The goal is source visibility, not distribution.

## Lean↔PDF Consistency — AI-Assisted Workflow

There is no automated tooling that verifies theorem status labels in PDF build scripts (e.g. "Status: DERIVED", "Candidate Theorem") match the actual Lean proof state. This is a known gap.

It is closed by the Claude-assisted session workflow instead. At every session where a Lean proof changes status or a new result is added, Claude cross-checks the corresponding PDF script and companion document as part of the same work. The companion sync checklist and README sync triggers (above) formalize this discipline.

This is a deliberate choice: the mapping between Lean theorem names and PDF prose descriptions is not machine-parseable without a maintained lookup table that would itself require discipline to keep current. The AI workflow catches the same class of errors more flexibly, with lower maintenance overhead, at the project's current scale.

If the framework grows significantly or external contributors join, a lightweight parseable-marker convention (`-- LEAN_STATUS: DERIVED` in Lean files, grepped against PDF scripts) would be worth adding. For now, the session discipline is the mechanism.

**Lean encoding descriptions can also go stale.** The gap above covers theorem *status* labels. A separate gap: prose descriptions of Lean *encodings* (type names, constructor names, how a concept is represented in code) can drift when the Lean source is refactored. Before stating any Lean encoding in a PDF, companion, README, or correspondence — verify it against the actual source file. Do not rely on memory or prior documentation. Example: `Fin 2` was replaced by `OntologicalStates` in ZPB.lean; stale references persisted in README.md, CLAUDE.md, and build scripts until caught by a reviewer question in May 2026.

## Transparency Notices on Unlinked Public Documents

Any file that is committed to the public repository but intentionally unlinked from both README.md and GUIDE.md **must carry a transparency notice** explaining its status. This is a standing policy — apply it whenever a new unlinked file is added or discovered.

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

## README.md and GUIDE.md Maintenance

The project index is split across two files. README.md is the formal index (for mathematicians and reviewers). GUIDE.md is the general reader hub (plain language, companions, reading paths). Both are public.

### README.md and GUIDE.md Document Structure

Preserve the existing section order in both files. Do not add top-level sections, reorder sections, or remove terminal sections (License, Citation, Contact, Purpose in README.md; footer pointer in GUIDE.md) without agreement. README.md is the formal index for mathematicians; GUIDE.md is the general reader hub. Both must have a cross-pointer to the other near the top.

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

### Validation Checklist (both files)

Before committing any README.md or GUIDE.md update:
- [ ] All linked files exist (verify with `Glob` tool, pattern `*.pdf`)
- [ ] No file extensions in display text; no version numbers in display text
- [ ] No em dashes — regular hyphens only
- [ ] README.md: Axiomatic Commitments current (AX-1 is T-SNAP, not an axiom); Question Register reflects actual status
- [ ] GUIDE.md: Reading Paths version numbers match register.md; "What This Is Not" section present
- [ ] Cross-pointer to the other file present near top of each

### Document Sync Requirements — Triggers and Checklist

Certain changes require both README.md and GUIDE.md to be audited for consistency. Apply this checklist whenever any of the following occur:

**Triggers:**
- A document is versioned up (e.g. ZP-A v1.3 → v1.4)
- An open question is closed (in any document)
- A claim's status changes (axiom → theorem, candidate → derived, etc.)
- A new document is added or archived

**On each trigger, verify in README.md:**
1. **Framework table** — version number matches the current file in the root and matches register.md
2. **Question Register** — every OQ/item that changed status is updated; newly closed items are added if missing
3. **Document descriptions** — any "Candidate Theorem", "Open", or status language in the Framework table description column still accurately reflects the document's current state

**On each trigger, verify in GUIDE.md:**
1. **Reading Paths links** — all version numbers in Reading Paths match register.md (and therefore the Framework table in README.md)
2. **Companion table** — if a companion was updated, its row reflects current diagram list
3. **Companion staleness note** — still accurate; update or remove if companions are brought current

**Known pattern to watch:** Version numbers now appear in three places: register.md (canonical), README.md Framework table, and GUIDE.md Reading Paths. Updating any one does not update the others. Always update register.md first, then propagate to README.md and GUIDE.md in the same session. Stale reading path version numbers have caused errors before.

### Common Updates

**Adding a new formal document:**
1. Add to the Formal Framework Documents table in README.md
2. Add a companion row to the Illustrated Companion Documents table in GUIDE.md (if companion exists)
3. Add to the Mathematician reading path in GUIDE.md
4. Use clean display name (no extension, no version) in both files
5. Link to the current version (no `-1`, `-2` suffix)
6. Put version number in the Version column only
7. Verify file exists with `Glob` before committing

**Historical folder table format** (`historical/README.md`): `| [filename](filename) | YYYY-MM-DD | description |` — use actual archived filename in both display text and link; date moved (not date of document); newest-first.

## Archiving Old Document Versions

**`historical/` is a write-once, READ-ONLY archive (standing rule, Tim 2026-06-13).** Once a file is in
`historical/`, it is never modified, rebuilt, renamed, or deleted — it is the immutable record of a
superseded version. The only allowed operation is *appending* a new superseded version (write-once).
This also means `historical/` is reserved for **substantive version supersessions** worth preserving as
distinct artifacts. **Cosmetic / hygiene patches** (e.g. removing rendered version strings, vocab
fixes, palette rebuilds) **overwrite the flat root PDF in place and do NOT create a `historical/`
entry** — git history + `register.md` are their record. Do not pollute the archive with trivial churn.

When a document is superseded (substantively):
1. Move the current flat root file to historical with the version number: `Move-Item ZP-X_Title.pdf historical\ZP-X_Title_vN_N.pdf`
2. Rebuild the new version into the flat root name: `ZP-X_Title.pdf`
3. Update `historical/README.md` with a table row: `| [filename](filename) | YYYY-MM-DD | description |`
4. Update register.md with the new version number (Filename column stays flat — `ZP-X_Title.pdf`)
5. Update the version number in README.md's The Framework table

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

### Readable Name Convention — CC-2 is "the Quine atom" (framework-wide, additive)

**Standing rule (Tim, 2026-06-09).** CC-2 (⊥ = {⊥}, the self-containing bottom) is the conceptual keystone of the framework — it is what forces ZF+AFA, makes ⊥ immune to external description, and is the single contact point between ZFC+Foundation and ZF+AFA. The bare label "CC-2" undersells it on two counts: it reads as a minor sequence code, and the "CC = Conditional Claim" prefix is now **stale** — CC-2 was upgraded to a Forced Metatheoretic Commitment (closed via ZP-J T-EXEC), so it is no longer a conditional claim. This is the same situation AX-1 was in before it became T-SNAP.

**The convention — ADDITIVE, never eliminative:**
- Present CC-2 with the readable name **"the Quine atom."** This is a recognized set-theory term (Quine, Aczel) — it carries real gravity and a literature anchor, and it is NOT ZP-invented jargon (avoid inventing a ZP-branded name — that would undo the de-jargoning work).
- **Keep "CC-2" as the formal handle and note it alongside** — e.g., "the Quine atom (CC-2)" on first/significant mention. Do NOT remove or rename the CC-2 identifier anywhere; every existing cross-reference stays valid.
- Gloss once per document as "the self-containing bottom, ⊥ = {⊥}."
- **Do not overclaim status.** It remains a Forced Metatheoretic Commitment, not a Lean theorem. The structural self-application fixed point is Lean-proved (ZP-J T-EXEC); the literal set-membership ⊥ ∈ ⊥ is metatheoretic (lives in the ZF+AFA framing, not the Lean kernel). The readable name conveys significance, not proof-status.

**Rollout (phased, not a 12-PDF marathon):**
- Reader-facing surfaces first: README.md, GUIDE.md, register.md.
- Then apply to each formal document/companion **as it is next revised** (the readable name leads CC-2's introduction). Footprint as of 2026-06-09: 12 build scripts carry CC-2 (build_zpe.py 27, build_zpa.py 13, build_zpc.py 8, etc.); Lean is clean (CC-2 is never a Lean identifier — 0 occurrences).
- **Do not touch** RELEASES.md or historical/ (release record / archived — never rewrite history).

### The keystone concept — "the diagonal fixed point" (confirmed name)

**Standing rule (Tim, 2026-06-10).** The Quine atom (CC-2) is only the *set-theoretic face* of the
framework's actual keystone: **⊥ is the same self-referential fixed point in every framework, and the
floor of each structure is its point of self-reference** (the Gödel inversion — self-reference located
at the floor, not the ceiling). The confirmed readable name for this keystone is **"the diagonal fixed
point."** This language has recurred across many sessions; it is the real central concept.

- The faces of the one diagonal fixed point: the Quine atom (set theory, CC-2), the Kleene quine
  (computability, ZP-K), v₂(0)=∞ (valuation, ZP-B), the unique fixed point of `selfApp`
  (ZP-J `AbstractSelfApp`), unbounded surprisal / no external description (ZP-C), the categorical
  initial object (ZP-G). MC-1 (the single bottom) is the commitment that identifies them.
- **Name it to evoke the recognized phenomenon, do NOT claim the unification as proved.** "Diagonal"
  anchors it to the diagonal argument and Lawvere's fixed-point theorem (the recognized home for
  self-referential fixed points across Russell / Quine / Kleene / Gödel / Tarski / Cantor). What ZP has
  *formalized*: `AbstractSelfApp` + instances, T-COMP (Quine atom = Kleene fixed point = ⊥), ZP-M
  (Kleene quine ∧ ε₀ co-witnessed). That ZP's keystone *is* a manifestation of Lawvere's theorem is a
  CONNECTION / conjecture, not a ZP result — keep that fence.
- Full articulation, faces, and the formal-vs-conjectural split:
  `.claude-local/notes/keystone_self_referential_fixed_point_2026-06-10.md`.

### MC-1 status convention — correspondence half is now derived (additive, no new name)

**Standing rule (Tim, 2026-06-10).** MC-1 (the cross-framework "single bottom" identification) was
split this session, the same way AX-1 became T-SNAP and CC-2 became a Forced Metatheoretic Commitment:

- **Correspondence half — now formally realized.** Each domain bottom is the categorical bottom
  (limit or initial object) of its own *real* Mathlib category: F_B `fB_functor : ℕᵒᵖ ⥤ TopCat`
  (⊥ = inverse limit `⋂ B(0,2⁻ⁿ) = {0}`), F_D `fD_functor : ℕ ⥤ ModuleCat ℂ` (⊥ = initial object
  `StateSpace 0`), F_C `fC_functor : ℕ ⥤ KleisliCat PMF` (⊥ = initial object `Fin 0`, with
  `fC_no_return` = AX-G2 as a theorem). Bundled witness: `mc1_correspondence` (`ZPH_MC1.lean`).
  So the bare label "MC = Modeling Commitment" now **undersells** this half.
- **Identity half — still a modeling commitment.** That the four bottoms are *numerically one object*
  across four categories is a chosen identification, the irreducible residue. NOT a theorem.

**The convention (ADDITIVE, never eliminative):**
- Keep **"MC-1"** as the formal handle everywhere; do not rename it. When status is described, present
  the split: correspondence half derived (cite `mc1_correspondence`), identity half a commitment.
- **No new readable name for MC-1.** Unlike CC-2 (which *is* an object = the Quine atom), MC-1 is the
  *identification*; its underlying object already has the confirmed readable name
  [[project_diagonal_fixed_point]] ("the diagonal fixed point"). Coining an MC-branded name would be
  the ZP-invented jargon the CC-2 convention warns against — do not.
- **Do not overclaim.** The real categories are not `ZPCategory` instances (they have terminal
  objects), so ⊥ is the *limit* in `TopCat` and the *initial object* in the other two; state that
  distinction honestly. The cross-category identity is never claimed as proved.
- **Rollout:** reader-facing surfaces first (README done 2026-06-10); other formal docs/companions as
  each is next revised. Do not touch RELEASES.md or historical/.

## GitHub Issues — Transparency and Engagement Policy

The Zero Paradox project treats GitHub Issues as a public transparency mechanism, consistent with the project's core transparency commitment. Issues are not just a bug tracker — they are the public record of what is open, contested, or unresolved in the framework.

### When to check

- At the start of any session where a PR is being created or merged
- At the start of any session where outreach responses are being processed
- Any time Tim asks about external engagement or project status

### When to file a public issue

- Framework open questions that are genuinely unresolved and would benefit from external input (e.g. OQ-E2 cardinality question, AFA/CH tractability)
- Substantive technical questions that arose in review and were not closed within the session
- Questions where the framework explicitly flags something as open and outside the authors' expertise

### When NOT to file

- Anything sourced from private correspondence (reviewer feedback, outreach responses, academic group correspondence)
- Reviewer identity or feedback details
- Outreach strategy, sending schedules, or draft emails
- Editorial or prose decisions
- Anything that belongs in `.claude-local/`

### Issue framing standard

Public issues should read as genuine open questions to the mathematical community — not as requests for validation. Frame them as specific, honest about uncertainty, and standalone without requiring knowledge of the full framework.

### Identifier tracking — standing requirement

Every outreach item must have its external identifier recorded in `.claude-local/outreach/tracker.md` at the time it is created or sent. No exceptions.

**What counts as an identifier:**
- GitHub Discussion: `#N` (e.g. `#77`)
- GitHub Issue: `#N`
- MathOverflow question: full URL
- Email thread: date sent + recipient (email threads have no stable ID — date + recipient is the key)
- Zulip post: stream + topic slug
- arXiv submission: arXiv ID

**When to record it:** At the moment the item is created or sent — not after the fact. If an identifier is missing from the tracker, add it before doing any other work in that outreach session.

---

## Framework Structure (for context)

The Zero Paradox is a multi-layer mathematical ontology proving the Binary Snap (⊥ → ε₀) as a theorem. The dependency order of the formal layers is:

**ZP-A** (lattice algebra) → **ZP-B** (p-adic topology) → **ZP-C** (information theory) → **ZP-D** (state layer) → **ZP-E** (DA-1/T-SNAP derivation)

**ZP-G** (category theory) → **ZP-H** (categorical bridge) — self-contained; depends on ZP-E conceptually but not formally.

Each formal document has a paired illustrated companion for general readers. AX-G1 and AX-G2 are the two structural commitments of ZP-G's categorical layer. Neither is a novel commitment: AX-G1 is grounded in ZP-A's bottom element ⊥; AX-G2 follows from ZP-A antisymmetry and ZP-B C3 (topological irreversibility). ZP-G is self-contained by design and states them explicitly within that layer. AX-B1 (binary existence) is not a novel commitment — it is directly verifiable by computation (OntologicalStates derives DecidableEq; ax_b1_distinct proved by `decide`) and depends only on `propext`, not `Classical.em`. AX-1 (Binary Snap Causality) is now Theorem T-SNAP, derived in ZP-E — do not refer to it as an axiom.

## Four-Fingerprint Scan — Decision Log Requirement

When a four-fingerprint scan is conducted (see memory: `feedback_reader_orientation.md`), the session notes file in `.claude-local/notes/` must be updated before the session ends with:

1. **Each item reviewed** — the finding, the decision (FIXED / NO FIX / PENDING), and the version bump if fixed.
2. **Rationale for no-fix decisions** — e.g., "already addressed in vX.Y", "standard result in the relevant literature", "Lean scope already disclosed."
3. **Any technique notes** — e.g., "read the Lean file before fixing to confirm the actual proof argument."

This log is the authoritative record of what has been reviewed and why. Future sessions must read it before starting a new scan pass to avoid re-reviewing already-settled items.

**File convention:** `.claude-local/notes/framing_scan_YYYY-MM-DD.md` — one file per scan pass, named by the date the scan was run. The decision log lives at the bottom of that file under a `## Decision Log` header.

**Standing rule:** A scan pass is not complete until all reviewed items have a decision recorded. "PENDING" is a valid decision for items deferred to a future session.

## Communication Quality Feedback

During working sessions, apply the Communication Quality Rubric to evaluate Tim's statements about the framework in real time. Flag anything scoring **7 or below** on the composite scale (35% terminological accuracy, 35% structural accuracy, 15% consistency, 15% clarity). The full rubric with scoring tables and calibration notes lives at `.claude-local/communication_quality_rubric.md`. Key terms requiring extra care: ⊥ (three-way identification), T-SNAP (theorem, not axiom), DA-1 (derived proposition, conditional on DP-2), DP-2 (grounded in D7 — not freely chosen), CC-1/CC-2 (both now derived via ZP-J, not freestanding commitments).

## Session Handoff File

`.claude-local/handoff.md` is the standardized session state file. At the start of every session, read it first. At the end of every session (or before a planned context switch), overwrite it with the current state: what was just done, the immediate next action, and anything deferred. Always use this exact filename — one file, always current, always overwritten.

## High-Value Insight Capture — Standing Rule

Any observation made during a session that could lead to a new theorem, new layer,
new conjecture, or significant axiom relationship must be written to `.claude-local/notes/`
immediately — without waiting to be asked. Do not defer to the end of the session.

**Triggers — capture automatically when any of these arise:**
- A structural connection between two existing layers that hasn't been formalized
- An identification of two mathematical objects as "the same fact in different languages"
- A conjecture about axiom derivability or necessity (e.g. deriving a class field from
  upstream structure)
- An argument that could become a new ZP layer or bridge layer
- A DC-free, choice-free, or purity result not yet in a Lean file
- A new justification for an existing axiom or design principle
- Any observation that directly answers or partially closes an open question in the framework

**What the note must contain:**
1. The insight in plain language (one paragraph — legible without session context)
2. The precise mathematical claim (what exactly is being asserted)
3. What is formal vs. what is still philosophical/conjectural
4. Status: open conjecture / partial proof / architecture clear but unbuilt / etc.
5. Connected notes (link to related `.claude-local/notes/` files)

**File naming:** `.claude-local/notes/<topic>_YYYY-MM-DD.md`

**The test:** Would a future session miss something important if this wasn't written down?
If yes, write it now.

## Reviewer Feedback Tracking

Reviewer feedback and correspondence are tracked in `.claude-local/feedback/reviewer_feedback_tracking.md`. That file is private and gitignored. Do not include reviewer names or feedback details in this file.

## License

CC BY-NC-ND 4.0 — share with attribution; no modifications; no commercial use.


# .claudecodes instructions for Lean 4 development
- Always run lake build as two separate PowerShell calls: first `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8`, then `Get-Content build.log | Select-Object -Last 1` (or with a `-match` filter). Never combine them with `;` in a single call.
- Ignore PDF rendering assets and website build artifacts in the root.
- Always check 'lake-manifest.json' for dependency updates before adding new imports.

- When searching for Lean source files in this project, always use the pattern ZeroParadox/**/*.lean, never **/*.lean. The .lake/ folder contains thousands of Mathlib library files that aren't mine."

# Zero Paradox Project Standards

## Development Branch

All work — Lean 4 proofs and PDF rendering — happens on the `illustrated` branch. This is the single active development branch. `main` is production/public. The `lake_testing` branch is retired; do not switch to it or push to it.

## Operational Rules
1. **Single branch:** All Lean and PDF work happens on `illustrated`. No branch switching required.
2. **Math Workflow:** Verify theorem changes with two separate calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` then `Get-Content build.log | Select-Object -Last 1`.
3. **PDF Workflow:** Use existing rendering scripts and strictly follow the document versioning and archiving conventions defined above.
4. **Transparency:** Maintain the `.claude-local/` folder for in-progress scripts and internal notes as a private "collaboration buffer."
5. **Sync before starting work:** At the start of any session, always run `git fetch origin main` then `git merge origin/main` before making any changes. Never make edits against a stale base.
6. **Verify no conflict markers after any merge:** Before committing after a merge, run `git diff --check` to confirm no conflict markers (`<<<<<<<`, `=======`, `>>>>>>>`) remain in any file. A file with unresolved markers will commit silently and corrupt the document. This has happened twice on this project.
7. **5-minute timeout on all external tool calls:** Every `PowerShell` or `Bash` call that invokes an external process (PDF build scripts, `lake build`, `python <script>`, long-running `git` or `gh` operations) must use `timeout: 300000` (5 minutes). If the command exceeds this limit, kill it and report back — never wait indefinitely. If it times out, diagnose the cause rather than retrying blindly.
8. **Pull request body — always use `--body-file`:** PowerShell cannot reliably pass multiline PR bodies inline (special characters, arrows, backticks, and asterisks all cause parse errors). Always write the body to `.claude-local\pr_body_<name>.md` first, then create the PR with:
   ```powershell
   gh pr create --title "..." --body-file ".claude-local\pr_body_<name>.md"
   ```

9. **Keep PR description current:** If additional commits are pushed to a branch after the PR is opened, update the PR body to reflect the new content. Update `.claude-local\pr_body_<name>.md` first, then run:
   ```powershell
   gh pr edit <number> --body-file ".claude-local\pr_body_<name>.md"
   ```

10. **GitHub Discussion body updates — always use `-F body=@file`:** Passing Unicode body content through PowerShell string interpolation (`$body = Get-Content -Raw; -F body="$body"`) corrupts multi-byte UTF-8 characters (arrows, subscripts, math symbols). Always write the body to `.claude-local\temp_body.md` first, then pass the file directly:
   ```powershell
   gh api graphql -F query=@.claude-local\mutation_update_discussion.graphql -F id="NODE_ID" -F body=@.claude-local\temp_body.md
   ```
   After every update, verify the live body via `mcp__github__get_discussion` before proceeding to the next thread. This issue was discovered 2026-05-23 when ZP-C (#69) was posted with garbled math.

## File Priority
- Both `.lean` files and PDF build scripts are first-class on `illustrated`.
- All other conventions (versioning, archiving, scripts/ sync) apply as documented above.

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
2. **Purity check** — add a `#print axioms` block at the bottom of every ZP-X Lean file (inside a `section PurityCheck ... end PurityCheck`), one call per proved theorem. The expected result is `'theorem_name' does not depend on any axioms`. Any kernel axiom that appears (`Classical.choice`, `propext`, `Quot.sound`) must be explicitly noted and justified in a comment in the Lean file.
3. **Update README.md** — add or update a row in the `### Formal Verification (Lean 4)` subsection of The Framework, and update the Question Register row for `Formal verification (Lean/Rocq)`.
4. **Commit all changes together** on `illustrated`.