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
