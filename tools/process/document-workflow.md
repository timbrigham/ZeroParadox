# Document workflow — companions, README/GUIDE, and the version-propagation path

**Opens when:** you are bumping a document version, updating a companion, editing README.md or
GUIDE.md, or adding a new formal document.

`CLAUDE.md` carries the triggers and the one-line rules. This is the checklist material — the part
you consult while doing the work rather than the part that has to fire in the moment.

## 1. The propagation path, and the one mechanical check on it

**Version numbers live in exactly two places: `register.md` (canonical) and README.md's Framework
table (the single derived copy). That is the whole path.** Update `register.md` first, propagate to
README in the same session.

⭐ **`check_hashes.py` compares the two tables on every run**, joined on the **PDF filename** — never
the `ZP-X` code, because four register rows begin `ZP-J`. It found **five** stale README rows on its
first run and caught the author drifting the same way twice more within the hour.

⚠ **GUIDE.md is deliberately NOT in the comparison, because it carries no version numbers at all.**
Measured 2026-08-19: `grep -c` returns 0. Its Reading Paths link flat filenames and delegate version
state to README. **A version number appearing in GUIDE.md is a regression to revert, not drift to
sync** — re-adding one would mint a third copy of every version and oblige the comparator to grow a
third arm to police the copy the decision created.

*(This corrects a checklist line that survived in `CLAUDE.md` until 2026-08-20 telling a reader to
verify GUIDE's version numbers against `register.md` — a check that can only ever report green,
eighteen lines above the paragraph saying GUIDE has none.)*

## 2. Companions

Each formal ZP-X document has a paired illustrated companion, `ZP-X_Illustrated_Companion.pdf`.
Companions **overwrite in place** — no versioned filename, no archiving; git history and the Zenodo
snapshots are the record. The current companion version lives in exactly two places: the title block
of the PDF and the docstring of its build script.

**Companion version numbers are independent of formal version numbers.** What matters is that the
companion is not materially stale.

### The sync questions

**Whenever a formal document is updated, review its companion in the same session.** Ask:

- Does the companion describe any result whose **label or status** changed? ("Candidate Theorem" →
  "Theorem T-SNAP", CC-2 added, RP-2 added.)
- Does it **omit a new result** a general reader would benefit from? (L-INF, a new lemma or design
  principle.)
- Does its **key result box or closing summary** still accurately reflect the framework state?

If yes to any, update the companion and bump its internal version in the **same commit** as the
formal document.

### Sync checklist

- [ ] Key result box / closing summary still accurate
- [ ] Changed theorem or claim labels updated in plain language
- [ ] New results relevant to a general reader added, with a plain-language explanation
- [ ] Internal version string bumped if anything changed
- [ ] Build script docstring updated to match

### Bumping a companion version

1. The subtitle paragraph in `build()` — `'Information Theory | Version 1.4'` → `'Version 1.5'`
2. The docstring at the top of the build script

## 3. Version numbers and changelogs in rendered PDF content — ALL PDFs

**Generalized 2026-06-13** (Tim: version changelogs in rendered content should be *"murdered by the
style guide and review"*). Scope is **rendered PDF content only** — build-script docstrings,
`register.md` and `RELEASES.md` are the changelog of record and are exempt. Git history is the real
changelog.

**A document's OWN version appears in exactly one place in rendered content: the subtitle / tagline
meta line** (`'... | Version ' + VERSION + ' | ...'`; formal-doc footers via `make_doc()` may also
carry it). Nowhere else — not in disclaimers, section headers, body prose, title-block notes,
endnotes, or status tags.

**No self-version changelogs or provenance tags.** A title-block "note" or endnote narrating
`"v1.1: Added X. v1.0: Initial release…"` is a violation — it was the standard formal-doc pattern
(ZP-M) and is retired. The title-block note describes what the document **is**, not its history.

Violations to strip on discovery: `"New in v1.6"`, `"In v2.7, DA-1 was upgraded"`, `"End of ZP-X
v1.0"`, `"Updated ZP-E v3.0 | …"`, `[unchanged from v1.0]`, `[new in v1.7]`, `[rebuilt in v1.1]`,
`Relabelled in v1.2`, `Supersedes v1.4`.

⚠ **EXCEPTION — cross-document version citations are ALLOWED** (Tim, 2026-06-14). *"T-SNAP derived in
ZP-E v2.0"*, *"Closed in ZP-G v1.1"* are legitimate citations, not self-changelogs. The rule targets
a document's references to its **own** version history.

**Editorial review enforces this as a kill.**

## 4. Companion prose precision — the five categories

Apply when drafting or reviewing any companion section making claims about mathematical structures,
properties or comparisons. The same errors appear in formal-document preambles and contextual
sections. It does **not** apply to formal theorem statements, which are held to a separate standard
via Lean.

1. **Precision errors** — the wrong technical term for the property actually being claimed. Common
   risk: describing a **valuative** property (`v₂(0) = +∞`) in **topological** vocabulary
   ("topologically isolated"), or metric language for an algebraic property. Verify the term names
   the correct property in the correct sub-field.
2. **Invented terminology** — informal or coined phrases used as if recognized. Anything
   non-standard that *sounds* technical confuses readers who know the real vocabulary. Use the
   standard term, or flag the usage as informal/metaphorical.
3. **Directional ambiguity** — is the sentence *describing* a property a structure has (and calling
   that bad), or *prescribing* what it should have (and saying it falls short)? Any "X is Y" near a
   comparison between two structures must make the normative/descriptive split explicit.
4. **Context-free structural claims** — asserting as universally true something true only inside the
   ZP framework. Claims about zero or ⊥ that hold here may be false in most frameworks. Scope them.
5. **Scope overclaiming** — universal quantifiers ("any domain", "every structure") applied to a
   ZP-specific limitation. Narrow to what is actually proved.

## 5. README.md and GUIDE.md

**README.md is the formal index** (mathematicians and reviewers). **GUIDE.md is the general-reader
hub** (plain language, companions, reading paths). Both are public, and each must carry a
cross-pointer to the other near the top.

**Preserve the existing section order in both.** Do not add top-level sections, reorder, or remove
terminal sections — License, Citation, Contact, Purpose in README; the footer pointer in GUIDE —
without agreement.

### Formatting

- **Display text uses clean names** — no file extensions, no version numbers. Correct:
  `[ZP-A Lattice Algebra](ZP-A_Lattice_Algebra_v1_2.pdf)`. Wrong:
  `[ZP-A Lattice Algebra v1.2.pdf](...)`.
- **Link targets point at the current, non-suffixed filename.**
- **Regular hyphens (`-`), not em dashes.** Mathematical arrows (`→`) are fine.
- **Version numbers go in the Version column only**, never in display text.
- Consistent column alignment; meaningful headers (File, Document, Version, Contents).

### Pre-commit checklist

- [ ] All linked files exist (`Glob`, pattern `*.pdf`)
- [ ] No file extensions and no version numbers in display text
- [ ] No em dashes
- [ ] README: Axiomatic Commitments current (AX-1 is T-SNAP, **not** an axiom); Question Register
      reflects actual status
- [ ] GUIDE: "What This Is Not" section present; Reading Path **targets resolve** (do **not** check
      version numbers — see § 1)
- [ ] Cross-pointer to the other file present near the top of each

### Sync triggers — audit both files when any of these occur

A document is versioned up · an open question is closed · a claim's status changes · a document is
added or archived.

**In README.md:**
1. **Framework table** — version matches the file in the root *and* matches `register.md`
2. **Question Register** — every item that changed status is updated; newly closed items added
3. **Document descriptions** — "Candidate Theorem" / "Open" / status language still accurate

**In GUIDE.md:**
1. **Reading Paths** — the link *targets* resolve
2. **Companion table** — an updated companion's row reflects the current diagram list
3. **Companion staleness note** — still accurate; update or remove if companions are current

### Adding a new formal document

1. Add to the Formal Framework Documents table in README.md
2. Add a companion row to the Illustrated Companion Documents table in GUIDE.md, if one exists
3. Add to the Mathematician reading path in GUIDE.md
4. Clean display name in both — no extension, no version
5. Link the current version, no `-1` / `-2` suffix
6. Version number in the Version column only
7. Verify the file exists with `Glob` before committing

---

## Routed from `CLAUDE.md`, 2026-08-23

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

When Tim initiates a release: draft the `RELEASES.md` entry + `.zenodo.json` → PR → after merge, **run the Release-Readiness Gate (`check_release_ready.py <tag>` must exit 0) and confirm its judgment checklist** → draft the GitHub Release body → **wait for explicit approval** → execute:
```
gh release create <tag> --target main --title "<tag> - <title>" --notes-file ".claude-local\release_<tag>_body.md"
```
⚠ **THIS IS TIM'S COMMAND TO RUN, NOT AN AGENT'S — `gh` is denied for agents (2026-08-22).** That is
deliberate rather than incidental: `gh release create` mints a **permanent Zenodo DOI**, and a
permanent public act is not an agent decision. An agent's role ends at drafting the body and getting
the Release-Readiness Gate to exit 0. `gitRobot` can create the annotated tag (`tag_create`) but has
no way to push one and no release verb at all.
After release, confirm the Zenodo snapshot minted (query `https://zenodo.org/api/records/<conceptID>`). The README DOI badge is the **concept DOI** (`10.5281/zenodo.20060860`), which auto-resolves to the latest version — so **no per-release badge edit is needed** (confirmed v2.6, 2026-06-24). Only verify the snapshot exists; do not chase a badge update.

**Release-Readiness Gate — mandatory hard gate before drafting the release body / cutting any tag.** Run from the repo root:
```
python tools/verify/check_release_ready.py <tag>
```
It must **exit 0** before the release body is drafted. The script mechanically verifies the deterministic release preconditions and **exits 1 (NO-GO)** on any blocking failure: Engineer's Takes filled (no `TODO (Tim)` / `TODO: Engineer` / empty take section), build-script hash integrity vs `register.md`, the `LEAN_CUSTOM_REGISTRY` invariant (`### ` entries == `[ZP-CUSTOM]` tags), `.zenodo.json` valid JSON, no conflict markers in tracked files, a `## <tag>` entry present in `RELEASES.md`, and every README/GUIDE-linked PDF exists. It also prints WARN-level hygiene checks (register↔script VERSION, `scripts/` mirror currency, untracked root PDFs) and a **judgment checklist** of the non-mechanizable items (editorial/adversary/claim-review/prior-art ran on the PR; companion sync; major-vs-minor decision; release body approved). It **consolidates** the `.zenodo.json` and Engineer's-Take checks below (kept individually documented for context) and adds the rest. The gate cannot hook `gh release create` (no git event for tag creation), so enforcement is procedural: **the gate must exit 0 AND its judgment checklist must be confirmed before the release body is drafted.** Lives in `tools/verify/` — **TRACKED, alongside every other checker (2026-08-15).** This reverses the old rule that `check_*` dev tools stay gitignored and unmirrored: they are now tracked *in place*, which is not the same as mirroring them. There is one copy, it is the public one, and a checker edit is an ordinary reviewable diff instead of a change `git diff` could not see. Reuses `check_hashes.py` for register parsing. Spec: `.claude-local/notes/release_readiness_gate_2026-06-24.md`. (Added 2026-06-24 after `LEAN_CUSTOM_REGISTRY` went 18 days stale undetected at the v2.6 threshold — the scattered-checks model let it slip.)

**`.zenodo.json` check — mandatory before every release:** Read `.zenodo.json` and verify the `description` field accurately reflects the current layer count and layer list. Update it in the same PR as `RELEASES.md` if anything is stale. Zenodo reads this file at release creation time; it cannot be updated retroactively via the repo (only via the Zenodo web UI).

**Engineer's Take check — mandatory before every release (hard gate):** Before cutting any release, grep the Lean sources for outstanding Engineer's Take placeholders — at minimum `TODO (Tim)` and `TODO: Engineer's Take` across **`ZeroParadox/**/*.lean`** (also scan for any `## Engineer's Take` heading followed immediately by an empty section). **The glob MUST be recursive.** This instruction previously read `ZeroParadox/*.lean`, which post-reorg matches only 3 files out of 187 — a manual check run that way would pass silently on an unfilled Take in any subdirectory. `check_release_ready.py` already uses the recursive form and is correct; only this prose was wrong (fixed 2026-07-19). Every ZP-X Lean file included in the release must have its Engineer's Take filled in Tim's own voice. **A release is BLOCKED until all are filled.** Claude never writes these — they must be Tim's own language (see the Engineer's Take convention) — so this gate catches the omission, it does not fill it. Surface the list of unfilled takes to Tim and wait for his prose. (Added 2026-06-11 after the four ZP-H functor takes plus ZP-L's were almost missed at the v2.4 threshold.)

**RELEASES.md format:** `## vX.Y - YYYY-MM-DD` header, then **Why this release** (one sentence), **What changed** (bullets), **Document versions at this release** (table), **Next threshold**. Match existing entries in RELEASES.md for exact formatting.

## register.md — Canonical Version Registry

`register.md` is the authoritative source for all current document version numbers, filenames, and companion versions. It is committed to the public repository and reachable from the main index via the Claims Ledger (`CLAIMS.md`, which README links to register.md), so it no longer carries an unlinked-transparency notice (removed 2026-06-21).

**Schema:** One row per formal document:
`| Document | Formal Version | Filename | Companion Version | Notes |`

**Rule: update register.md first.** On any version bump — before touching README.md or a build script docstring — update register.md. **`register.md` is canonical and README.md's Framework table is the single derived copy; that is the whole propagation path.**

**On every version bump, in order:**
1. Update register.md (formal version, filename, companion version if changed)
2. Update README.md Framework table (verify against register.md)
3. Update build script docstring
4. Archive old version per archiving convention

⚠ **GUIDE.md IS DELIBERATELY NOT A STEP HERE, AND THE OLD STEP 3 WAS WORSE THAN VACUOUS.** It said to
verify GUIDE's Reading Paths against register.md — but **GUIDE.md carries no version numbers at all**
(measured 2026-08-19, `grep -c` = 0). A rule naming a surface that cannot go stale can only ever
report green, so an audit ticks a box for a check that never ran. **That GUIDE carries no versions is
a PROPERTY TO PRESERVE, not an omission to correct:** its Reading Paths link flat filenames and
delegate version state to README, and re-adding numbers would mint a *third* copy of every version —
against § *the pointer must not become a COPY* directly, and it would oblige the README↔register
comparator to grow a third arm to police the copy the decision created. **Reintroducing a version
number to GUIDE.md is a regression, not a helpful addition.**

## Companion Document Versioning

**TRIGGER — an action: a formal document was updated, or you are touching any rendered PDF text.**

- **Review its companion IN THE SAME SESSION**, and bump the companion's internal version in the
  **same commit**. Companion versions are independent of formal versions; what matters is that the
  companion is not materially **stale**, because a general reader meets the framework there and a
  stale key-result box misdescribes what is proved.
- **A document's OWN version appears in exactly ONE place in rendered content — the subtitle meta
  line.** No self-version changelogs, no `[new in v1.7]` provenance tags. **Editorial review kills
  these.** ⚠ **Cross-document citations are exempt** (*"T-SNAP derived in ZP-E v2.0"*) — that is a
  citation, not a self-changelog, and treating it as a violation is a false kill.

📖 **THE CHECKLISTS — `tools/process/document-workflow.md`.** The companion sync questions and
checklist, the full violation list to strip on discovery, and the **five prose-precision categories**
(precision error · invented terminology · directional ambiguity · context-free structural claim ·
scope overclaiming) that every companion section is drafted and reviewed against. **Open it before
writing companion prose** — those five are the errors that recur, and they are graded by an editorial
gate that will send them back.

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

**Line endings are LF, enforced by `.gitattributes`.** Because the fingerprint is a hash of file *bytes*, line endings must be byte-stable across machines or the same script would hash differently (CRLF vs LF). `.gitattributes` declares `* text=auto eol=lf` (all text normalized to LF) and marks PDFs/images `binary` (never converted). Do not commit CRLF in tracked text files, and do not rely on `core.autocrlf` — the attributes override it. `check_hashes.py` hashes the active `.claude-local` scripts (LF); the `scripts/` mirror is the same content under the same LF policy. (Added 2026-06-21 after a CRLF/LF mismatch made the `scripts/` mirror hash differ from the active script for the same content.)

**Standing rule — any script change requires all four steps in the same commit:**
1. Make the change and bump the internal version number
2. Rebuild the PDF and archive the old version
3. Recompute the hash: `python -c "import hashlib; print(hashlib.sha256(open('scripts/build_<doc>.py','rb').read()).hexdigest()[:8])"`
4. Update the hash token in `register.md`

**Session start check:** Run `python tools/verify/check_hashes.py` at the start of any session that will touch build scripts. A mismatch means a script was modified without completing the full four-step workflow — version bump and PDF rebuild are overdue.

A hash mismatch is not just a "rebuild needed" signal — it means the version bump step was skipped. Do not rebuild without incrementing the version number.

## PDF Build Standards

**Before building any PDF in this project** — formal layer, companion, or otherwise — read `scripts/PDF_Rendering_Standards.md`. It is the single authoritative source for font stack, glyph rendering, table cell formatting, HTML entities, subscript/superscript rules, and pre-build verification. All rules there apply to every PDF build without exception.

## Companion PDF Diagram Layout Standards

These rules apply to every `Drawing` object in every companion build script. Violations cause diagram content to overflow the declared bounding box and render over surrounding text — a recurring issue that has required multiple retroactive fixes.

**Now build-enforced (automatic).** `zp_utils` validates every `Drawing` in the story at `doc.build()` time — no per-function `validate_drawing()` call required. It **hard-fails the build** when content escapes its box (`max_y > dh` or `min_y < 0`, the only case that overlaps surrounding text), and prints a **margin warning** when content is inside the box but within the 10pt-top / 5pt-bottom safety margin. The rules below are still the design discipline (write diagrams that fit), but a forgotten check can no longer ship an escape. The bounds gate cannot see the *internal-collision* class (two elements overlapping inside the box, e.g. a caption over a node box); for that, every build prints a **diagram-page report** (`[diagram pages — eyeball for internal overlaps: …]`) naming the pages to visually check. Eyeball those pages on any diagram-touching build before commit.

**Known deferred tripwire (2026-06-19):** `build_zpc_companion.py`'s surprisal diagram has a pre-existing ~2pt bottom escape (the amber origin marker) — sub-perceptible, no visible overlap. Left unfixed by decision; the gate will block that companion's next rebuild until the diagram's `dh` is bumped a few points. Fix it then, bundled with whatever change prompts the rebuild.

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

---

## Routed from `CLAUDE.md`, 2026-08-23

## Lean↔PDF Consistency — AI-Assisted Workflow

There is no automated tooling that verifies theorem status labels in PDF build scripts (e.g. "Status: DERIVED", "Candidate Theorem") match the actual Lean proof state. This is a known gap.

It is closed by the Claude-assisted session workflow instead. At every session where a Lean proof changes status or a new result is added, Claude cross-checks the corresponding PDF script and companion document as part of the same work. The companion sync checklist and README sync triggers (above) formalize this discipline.

This is a deliberate choice: the mapping between Lean theorem names and PDF prose descriptions is not machine-parseable without a maintained lookup table that would itself require discipline to keep current. The AI workflow catches the same class of errors more flexibly, with lower maintenance overhead, at the project's current scale.

If the framework grows significantly or external contributors join, a lightweight parseable-marker convention (`-- LEAN_STATUS: DERIVED` in Lean files, grepped against PDF scripts) would be worth adding. For now, the session discipline is the mechanism.

**Lean encoding descriptions can also go stale.** The gap above covers theorem *status* labels. A separate gap: prose descriptions of Lean *encodings* (type names, constructor names, how a concept is represented in code) can drift when the Lean source is refactored. Before stating any Lean encoding in a PDF, companion, README, or correspondence — verify it against the actual source file. Do not rely on memory or prior documentation. Example: `Fin 2` was replaced by `OntologicalStates` in ZPB.lean; stale references persisted in README.md, CLAUDE.md, and build scripts until caught by a reviewer question in May 2026.

### File-Reference Citation Convention (standing rule — Tim 2026-07-08, post-reorg)

References to Lean **files** in reviewer-facing / checkable surfaces must carry the **full repository path** (`ZeroParadox/<Domain>/<Name>.lean`), never a bare basename. A full path is grep-verifiable against the filesystem — it resolves or it does not — so a move/rename fails **loud**; a bare basename fails **silent** (plausible but pointing nowhere), which is exactly the stale-citation class the 2026-07-08 reorg sweep had to hunt down. For a "check it yourself" repo, loud is the point.

By reference kind and surface:
- **Declaration names** (`t_snap_derived`, `mc1_correspondence`): keep **bare** — a decl name is globally unique in the codebase and self-locating via `#print axioms ZeroParadox.<name>`. Never prefix a decl with a path or a (dead) per-layer namespace.
- **File references in checkable surfaces** — CLAIMS.md, BOTTOMELEMENT.md, README/GUIDE, and each formal document's "Lean source" box/footer: **full path**, as a markdown link href where the medium supports it. The markdown ledgers already do this; keep it uniform.
- **File references in flowing general-reader companion prose**: a bare basename is acceptable where a full path would clutter the sentence for a non-programmer — the checkable surfaces carry the path and the file is one grep away.

**Rollout is additive, not a big-bang rewrite.** Every new or edited reference uses a full path immediately. Existing formal-doc source boxes upgrade to full paths **as each document is next rebuilt** (the same as-touched model as the companion-sync and vocabulary conventions — do not burn a rebuild round retrofitting). The authoritative old→new file map is `ssot.json` (`new.file`).

**Enforcement:** a `check_paths.py`-style resolver (the one used in the 2026-07-08 sweep, in the scratch/`.claude-local` tooling) verifies every repo-relative file reference in tracked markdown resolves against the filesystem. Run it before any doc-touching commit; it should become a pre-push/CI check so a future reorg cannot silently rot the citation layer again.

## Transparency notices on unlinked files — RETIRED 2026-08-15 (Tim).

**The rule was: any tracked file unlinked from both README.md and GUIDE.md must carry a
transparency blockquote (or, for a PDF, an amber callout). It is gone.** It bound seven files
and exactly one honoured it, for months, with nothing noticing — which is past this file's own
*fix the trigger* rung and into *discipline will not work here*.

**Measured the day it was retired.** Unlinked from both indexes: `ABOUTME.md`,
`BOTTOMELEMENT_findings.md` (which no longer exists — folded into the generated `BOTTOMELEMENT.md`
on 2026-08-29, so its stale hand-written legend became computed; the measurement below stands as
recorded on the day), `CLAUDE.md`, `LEAN_CUSTOM_REGISTRY.md`, `RELEASES.md`,
`register.md`, `scripts/PDF_Rendering_Standards.md`. Only `ABOUTME.md` carried a notice. Its own
table named two files and one of them, `ZP_Gen2_Applications.pdf`, had been moved to the private
folder and was not tracked at all.

⚠ **THE TRIGGER WAS MEASURING THE WRONG THING, and that is the transferable part.** It asked
*is this linked?* when what anyone actually cared about is *would a reader be misled about why
this exists?* Those came apart twice: `register.md` is flagged unlinked while this same file
says it is deliberately reachable through the Claims Ledger, and an instruction file cannot
carry a header at all, because a notice prepended to a prompt **becomes part of the prompt**.
The exception carved for `.claude/commands/*.md` and `CLAUDE.md` was the tell that the trigger
was wrong, not that it needed one more exception.

**What replaces it: nothing mechanical, and that is deliberate.** Disclosure lives in
§ *WHERE THINGS LIVE* and § *Private Working Folder* — pages a human reads. Where a document's
STATUS could mislead (speculative, superseded, a development artifact), say so in its own
opening because it is true, not because a linkage rule fired. `ABOUTME.md` keeps its note on
exactly that basis.

**Also retired with it: § *README.md Link Restrictions*,** whose table named the same two files
and was stale the same way. Nothing is being *hidden* — if a file should not be in the index,
the reason belongs in a commit message or a defect row, not a standing table that outlives it.
