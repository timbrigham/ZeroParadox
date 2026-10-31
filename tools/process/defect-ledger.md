# The open-defect ledger — why it exists, and the rules for keeping it

**Body for `CLAUDE.md` § `R-DEFECTS`.** The rule is there; the argument, the measured
history and the release interaction are here.

---

## The open-defect ledger — `.claude-local/DEFECTS.md`. Read it before choosing what to work on.

**A defect's home is this ledger.** Not a note, not a gate-findings archive, not a line in the handoff.
(Opened 2026-08-01, Tim.)

**Why it exists, and it is a gap this file created.** The § below correctly says *"if a finding is a
DEFECT, its home is a gate finding or a fix, never a note that cannot know when it stops being true."*
But the 2026-08-01 notes triage sorted 767 notes into `active` / `future-research` /
`archive{gate-findings, resolved, superseded}` — and **none of those is "open defect."** So the rule
forbade the wrong home without providing a right one, and defects scattered into gate-findings
archives that this same file says to *"write, never expect to read."* Tim's observation on reviewing the
triage: the classification should have been there from the start.

**The release rule it serves: A RELEASE BLOCKS ONLY ON AN OPEN CONTENT BEDROCK UNIT.** Tim,
2026-10-08, made permanent 2026-10-30: *"Content bedrock for now. Ordinary findings can pass for
now."* — *"Yes, this would imply the bedrock rule is permanent."* The rule in full is in the section
below. A GitHub Release mints a permanent Zenodo DOI; four already carry latent flaws that cannot be
withdrawn. One distinction worth carrying: deposited **files** in a Zenodo snapshot are frozen, but
record **metadata** can be corrected through the Zenodo web UI — so a wrong claim in a release
*description* is fixable; a flaw inside a published PDF is not.

**Ordinary findings still get burned down.** The rule changes what blocks a release, not what counts
as a defect: every open ordinary content finding is either fixed or carried on a public erratum issue.

**Rules for the ledger:**
- **Verify every entry AT THE ARTIFACT** before recording it open or closed. It goes stale exactly like
  the notes it replaces — that is not a reason to distrust it, it is a reason to re-check before acting.
- **GREP LOOSELY.** Measured while building it: two live defects first read as already-fixed because the
  pattern was too tight — one phrase split across a line break, one with markdown bold inside it. A
  tight-pattern miss is **not** evidence a defect is closed.
- **Burn down in FILE-SIZED BATCHES.** Gate rounds are per-push; one file fixed completely and gated
  once costs far less than one item at a time.
- **Fixing an item creates new unreviewed prose** and restarts the review obligation for the text
  changed — fix and re-sign, or push what was certified.
- Keep the ledger the SINGLE copy. Do not re-list its entries in the handoff; two copies drift.

---

## A release blocks only on open content bedrock

**The rule (Tim, 2026-10-08; permanent 2026-10-30).** A release BLOCKS only on an open
`DEFECTS.md` unit tagged **content** and **BEDROCK** (BEDROCK-CANDIDATE included until it is
graded). Content is what ships: the root PDFs and the prose of `scripts/build_*.py`,
`ZeroParadox/**`, root `.md`, `.zenodo.json` and the HTML pages. It does NOT block on ORDINARY
findings, tooling entries, published-process (`.claude/commands/**`) entries, or Tim-gated questions.
`tools/verify/check_release_ready.py` enforces this mechanically: it reads `DEFECTS.md` from the main
checkout's `.claude-local`, applies the open-unit rule printed in that file's header, fails on every
open content bedrock unit and on every open unit whose `[kind · SEVERITY]` tag cannot be read, fails
with a distinct UNREADABLE status when the ledger cannot be read, and prints the counts by kind and
severity on every run. `--ledger-only` runs that leg alone.

**Ordinary content findings ship as public erratum issues.** One issue per defect class per
document, labels `erratum` and `open question`. The ledger stays the single source, with the issue
number beside each public row. Tooling, process, reviewer and outreach material stays private
(R-ISSUES).

**What release pressure may never do:** lower a bedrock grade, or file a bedrock item as an erratum.

**The pre-2026-10-08 rule, for history.** Tim, 2026-08-01: *"I've got no desire to cut 5.0 right
now… I want to get that to as close to zero as we possibly can before a damn thing goes forward to
yet another release."* (Migrated from a private memory, 2026-08-28.) That rule blocked a release on
any open defect.

**Why bedrock still blocks:** a GitHub Release mints a permanent Zenodo DOI snapshot. **Four existing
releases already carry latent flaws that cannot be withdrawn**, and each new release freezes the
defect set it carries into another citable permanent record.

⚠ **THE DISTINCTION THAT MAKES THIS ACTIONABLE, because half of it is fixable:** deposited **files**
in a Zenodo snapshot are frozen forever, but **record METADATA** — the `.zenodo.json`-derived
description — *can* be corrected after publication through the Zenodo web UI. So a flaw inside a
published PDF is permanent and a wrong claim in a release DESCRIPTION is not. **Verify before telling
Tim something is unfixable.**

- Never present cutting a release as the recommended next step while an open content bedrock unit
  exists, or while an open ordinary content finding is neither fixed nor on a public erratum issue.
- Grade before releasing: a BEDROCK-CANDIDATE blocks until it is graded, and grading it ORDINARY to
  unblock a release is the one move this rule exists to prevent.
- **Verify each defect AT THE ARTIFACT before recording it open or closed.** Notes self-report status
  and have been false in both directions; a ledger built from notes inherits their rot.
- `check_release_ready.py <tag>` stays mandatory. Its ledger leg reads the TAGS: a bedrock finding
  recorded under the wrong kind or grade passes it, so a green leg is evidence about the ledger as
  written, not about the corpus.
