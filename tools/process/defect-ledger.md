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

**The standing rule it serves: NO RELEASE IS CUT WHILE THE LEDGER IS NON-EMPTY.** A GitHub Release
mints a permanent Zenodo DOI; four already carry latent flaws that cannot be withdrawn. A defect fixed
before a release costs one gate round; a defect shipped in one is permanent. **Never rank release
readiness above defect elimination, and never let release pressure defer a finding to next-touch debt.**
(Memory `feedback_no_release_until_defects_zero`.) One correction worth carrying: deposited **files** in
a Zenodo snapshot are frozen, but record **metadata** can be corrected through the Zenodo web UI — so a
wrong claim in a release *description* is fixable; a flaw inside a published PDF is not.

**The target is ZERO KNOWN DEFECTS, not zero defects.** The gates always find something — that is why
the severity-tiered cap exists. Do not blur the two, and do not imply a clean sheet.

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
