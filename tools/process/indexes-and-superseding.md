# README / GUIDE maintenance, the retired transparency rule, and superseding versions

**Body for `CLAUDE.md` § `R-INDEXES`.** The rule is there; the per-file checklists, the
measured retirement of the transparency-notice rule, and the supersede procedure are here.

---

## README.md and GUIDE.md Maintenance

**README.md is the formal index** (mathematicians and reviewers); **GUIDE.md is the general-reader
hub**. Both are public and each carries a cross-pointer to the other near the top. **Preserve the
section order in both** — do not add top-level sections, reorder, or drop terminal sections without
agreement.

**TRIGGER — audit BOTH files when any of these happens:** a document is versioned up · an open
question is closed · a claim's status changes · a document is added or archived.

⭐ **`check_hashes.py` mechanically compares `register.md` against README's Framework table** on
every run, joined on the **PDF filename** (never the `ZP-X` code — four register rows begin `ZP-J`).
**Update `register.md` FIRST and propagate to README in the same session**; the check found five
stale README rows on its first run.

⚠ **GUIDE.md carries NO version numbers, deliberately, and that is a property to preserve.** Check
its link *targets* resolve; **never** "sync" a version into it. A version number appearing in
GUIDE.md is a regression to revert — it would mint a third copy of every version and force the
comparator to grow a third arm to police the copy the decision created.

📖 **THE CHECKLISTS AND FORMATTING RULES — `tools/process/document-workflow.md`.** The per-file
pre-commit checklist, the display-name and table conventions, the per-trigger audit lists, and the
seven steps for adding a new formal document. **Open it before committing a README or GUIDE edit** —
these are the conventions a reviewer will send the diff back for.

## Superseding Document Versions

The `historical/` folder was **retired in v3.0**. Superseded versions are preserved by two records more
complete and authoritative than a hand-maintained archive: **git history** (every prior PDF stays in the
commit record) and each release's **Zenodo DOI snapshot** (the full repo - including the then-current root
PDFs - captured at a permanent, browsable DOI). The archive folder had drifted a month out of date; these
do not. Do NOT recreate `historical/`, and do NOT rewrite git history to purge old binaries (SHA-pinned
permalinks and DOI-referenced commits depend on it).

When a document is superseded (cosmetic **or** substantive), overwrite the flat root PDF in place:
1. Rebuild the new version into the flat root name `ZP-X_Title.pdf` (overwrite; do **not** create a versioned copy or a `historical/` entry).
2. Update `register.md` (version number + script hash).
3. Update the version in README.md's Framework table. (GUIDE.md carries no version numbers — see
   the version-bump section.)

The prior version is recoverable from git (`read(op='show', args=['<commit>:ZP-X_Title.pdf'])`) and lives permanently in the Zenodo snapshot of the release that last carried it.
