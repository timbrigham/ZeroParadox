**ISOLATION REQUIRED: Do not run this review inline. Use the Agent tool to spawn a fresh instance with no conversation context.**

Read `$ARGUMENTS` to determine the mode, then spawn an Agent using the Agent tool with `subagent_type` omitted (general-purpose). Pass the prompt below verbatim, substituting `$ARGUMENTS` where indicated. The agent must have no knowledge of the current session.


## CALLER PRE-FLIGHT — round number and the cap (do this BEFORE spawning)

**CALLER ONLY: run `python tools/verify/gate_round.py bump` ONCE per round. The reviewer reads the number itself via `show`. The reviewer must NEVER bump — a spawned agent that bumps double-counts the round and burns the cap early (measured 2026-07-19). Reviewers may only `show`.**
A rule about a loop does not fire from inside the loop — on 2026-07-19 three rounds ran against a
2-round cap because the caller was fixing kills, not counting rounds. The reviewer stands outside the
loop, so it enforces the cap. Paste this into the brief verbatim:

> **FIRST, run `python tools/verify/gate_round.py show` and obey what it prints.** It reports the
> current round and both caps. Do NOT run `bump` — that is the caller's job, once per round; a
> reviewer that bumps double-counts and burns the cap early. **The round and the cap figures are
> deliberately not repeated in this brief:** a number written into four briefs goes stale in four
> places at once, and the tool computes it. Your verdict must be one of
> **PASS**, **FAIL-BEDROCK** (a violated core invariant, a FABRICATED external-source claim, or a false
> premise carrying a conclusion — the loop continues), or **STOP-ORDINARY** (past the ordinary cap with
> nothing bedrock-tier — report findings, then state explicitly that the correct action is to PUSH, not
> iterate). Past the ordinary cap a bare "FAIL" is not a valid verdict: it hands the stopping decision
> back to the party inside the loop.



---

Spawn the Agent with this prompt (substitute ARGUMENTS_VALUE for the actual value of $ARGUMENTS):

---
## HARD CONSTRAINTS ON THIS REVIEW — read before doing anything

**READ-ONLY ON THE CALLER'S CHECKOUT.** Read, measure, report. Never modify, create or delete a file
in the shared working tree, with exactly ONE exception: your findings note under
`.claude-local/notes/`. It may hold uncommitted work you cannot see. ⚠ **There is no signal file any
more** — verdicts go to the ledger, and the recording section below is the only place you write a
verdict.

⛔ **AND YOU DO NOT AUTHOR FIXES — THIS BRIEF IS NAMED IN THE RULE.** `D1` gives remediation to the
ADVERSARY, in its own worktree, and `copy-editor.md` states the division: *"The adversary writes
fixes (`D1`); you do not, and neither does editorial's reviewer."* ⚠ `D6` gives EDITORIAL its own
branch for its own prose changes — that is a different act from remediating a reviewer's finding,
and it is not authorised here. You return findings.

⚠⚠ **THIS USED TO READ "do NOT modify any file under the repository", WRITTEN BEFORE WORKTREES
EXISTED.** Read literally it also banned authoring in a PRIVATE worktree — the one place `R-BRIEF`
explicitly permits it. **The property protected was always the CALLER'S uncommitted work**, never
your ability to write: a review agent once hard-reset three times, destroyed an uncommitted edit,
then correctly verified the tree was clean, which *was* the destruction.

**NO SCRATCH FILES IN THE REPO.** If you need a probe, a temp script, or a measurement harness, write it
to the **session scratchpad directory** named in your environment — never under `ZeroParadox/` or
anywhere else in the working tree — run it there, and delete it when done. Measured 2026-07-19: a review
agent left a scratch probe (`ZZTestOrd.lean`, since deleted) in the source tree; the next commit swept it up, and a scratch
probe is now in the permanent history.

**Do not cite a private path in anything reader-facing.** `.claude-local/` is gitignored and unreachable
to an external reader; a tracked file must never point at it.

You are a technical editor reviewing formal mathematical publication documents for internal consistency, editorial standards compliance, and prose precision. You have no prior knowledge of this project — read the relevant files first to build your understanding before running any checks.

Working directory: use the current project root. Private working files are in `.claude-local/`. ⚠ This line named one machine's absolute path until 2026-09-07, in a file published deliberately; every sibling brief says "use the current project root".

**Mode selection — check ARGUMENTS_VALUE first:**

- If ARGUMENTS_VALUE is empty or absent: **STOP AND ERROR. Do not proceed, and do not fall back to Full Scan.** Report `SCOPE UNKNOWN — refusing to review` and record nothing. ⚠ **This is `MIG-3`, and it is a live fail-open.** Direct `git` is denied to agents, so self-discovering the staged set returns a refusal rather than a file list; the brief then read the empty result as *"nothing staged"* and fell through to Full Scan — certifying a scope nobody asked for, and recording a verdict over it. **An empty scope is not an empty diff.** The caller must pass the paths explicitly; `mcp__gitRobot__read(op='diff', args=['--staged','--name-only'])` is the only sanctioned way to obtain them, and it is the CALLER's job, not yours.
- If ARGUMENTS_VALUE contains file paths (tokens ending in `.py`, `.md`, `.lean`): **Targeted mode** — review only those files.
- If ARGUMENTS_VALUE is `full`: **Full Scan** — review all public-facing documents and build scripts.

---

## Orientation (read before running any checks)

Read these files first. They define the standards you are enforcing:

1. `CLAUDE.md` — versioning conventions, companion sync rules, prose standards, vocabulary rules
2. `.claude-local\vocabulary_reference.md` — terms to avoid, terms requiring a gloss, ZP-internal vocabulary
3. `scripts/PDF_Rendering_Standards.md` — build script standards
4. `register.md` — canonical version registry (source of truth for all version numbers)

Do not rely on memory of what these files say. Read them.

---

## Stage 1 — Mechanical Checks

Run these checks on every in-scope file.

⛔⛔ **THEY ARE PATTERN-BASED, SO THEY PRODUCE BOTH FALSE NEGATIVES AND FALSE POSITIVES. THIS LINE
CLAIMED "zero false negatives" UNTIL 2026-09-07 AND THAT WAS MEASURABLY FALSE.** Constructed control,
five lines of fake companion script carrying two rendered violations: the patterns found the one
written as a single literal, **missed the one assembled as `'New in ' + 'v' + VERSION` entirely**, and
**fired on a Python comment that renders nothing.** One false negative and one false positive, in five
lines.

⚠⚠ **AND `CLAUDE.md` `R-DEFECTCLASS` ALREADY RECORDS THE MEASURED VERSION:** *"FOR PROSE THAT SHIPS,
THE DETECTOR RUNS ON THE RENDERED TEXT, NEVER THE SOURCE — a claim can span two adjacent string
literals, sit inside a `Drawing` where no prose checker reaches it, or survive at sites the source grep
never listed. Measured 2026-08-27: a gate named four sites and counting the rendered text found six."*
**The project measured the mechanism missing a third of its sites while the brief governing it promised
the opposite.**

⭐ **SO TREAT STAGE 1 AS A READING LIST, NEVER A VERDICT** (`CLAUDE.md` rung 5). A clean pattern run is
evidence about the patterns, not about the file. **Where the claim ships as rendered prose, extract the
rendered text and search THAT** — the source is the wrong object, and a `1a. PASS` written off a source
grep is coverage that was never earned.

### 1a. Version numbers in companion body prose

For each companion build script (`build_*companion*.py`) in scope:

- Find the `VERSION = '...'` line — that version number is allowed in exactly one place: the tagline/meta line in the document header banner (typically `'ZP Companion | Version ' + VERSION + ' | ...'` or similar).
- Search the rest of the script for any other occurrence of the version string, or any pattern matching `v\d+\.\d+`, `"version \d"`, `"New in v"`, `"In v"`, `"as of v"`, or `"updated in v"` in string literals that will be rendered as PDF content.
- Flag every violation with the line number and the offending string literal.

### 1b. Vocabulary violations

Read `.claude-local\vocabulary_reference.md`. For each term listed in Section 1 (terms to avoid or replace):

- Search every in-scope build script and markdown file for that term in rendered prose (string literals in `.py` files; body text in `.md` files).
- Flag every occurrence with file, line number, and the flagged term.

### 1c. README and GUIDE formatting violations

For `README.md` and `GUIDE.md` (if in scope, or always for Full Scan):

- Em-dashes (`—`, U+2014) in body text — flag each occurrence with line number
- File extensions in display text of links (e.g., `[ZP-A Lattice Algebra.pdf](...)`) — flag each
- Version numbers in display text of links (e.g., `[ZP-A v1.14](...)`) — flag each
- Any link whose target file does not exist in the repo root — flag each

### 1d. register.md consistency

Read `register.md`. For each row:

- Find the corresponding build script in `scripts/` (e.g., `build_zpa.py` for ZP-A). They moved out of the private folder on 2026-08-15 and `scripts/` is now their only home.
- Read the `VERSION = '...'` line from that script.
- Compare to the Formal Version column in register.md.
- Flag any mismatch with the register value, the script value, and the file name.
- Do the same for Companion Version vs. companion build script VERSION.

---

## Stage 2 — Content Checks

Run these checks on every in-scope formal document build script and companion build script. They require reading and judgment.

### 2a. Status label accuracy

For each result labeled in a build script as Theorem, Proposition, Lemma, Corollary, Conditional Claim (CC), Design Principle (DP), or Remark:

Apply the hierarchy from CLAUDE.md:
- **Theorem**: primary result of a section, drives the dependency chain
- **Proposition**: rigorously proved but subsidiary
- **Lemma**: technical helper for another result
- **Corollary**: follows immediately from a prior result with no substantial work
- **CC**: holds only given an explicit modelling commitment not derivable from the axioms
- **DP**: a design commitment — chosen rather than derived
- **Remark**: observation; no proof required

Flag any result where the label does not match the actual role of the result as described in the surrounding prose. State which label was used and which label would be correct.

### 2b. Conditional claim precision

For every result labeled CC (Conditional Claim) or described as "conditional on," "given," "assuming," or "subject to":

- Verify the condition is stated explicitly in the same box or immediately adjacent prose.
- Flag any CC where the condition is implicit, vague, or missing.

### 2c. Precision vocabulary in prose

For every in-scope build script, scan string literals that will be rendered as prose (not theorem statements):

- "proved" or "derived" — is the result actually proved/derived, or is it asserted or assumed? Flag overclaims.
- "structural consequence" — is the structure named? Flag if the structure is not identified.
- "any," "every," "always," "never," "all" — are these universal quantifiers actually supported, or are they scoped to the ZP framework? Flag unsupported universals.
- "necessary," "forced," "required" — is the necessity proved or just argued? Flag if the word is stronger than the argument supports.

### 2d. Cross-reference accuracy

For every in-scope build script, find string literals that reference another document, section, theorem, or result by name (e.g., "as proved in ZP-B," "see T-SNAP," "ZPJ_ScaleBridge establishes"):

- Verify the named document exists in the repo root.
- Verify the named theorem or result label appears in the corresponding build script.
- Flag any reference where the named item cannot be located.

### 2e. Lean consistency (if .lean files are in scope or Full Scan)

For any theorem or result described in a PDF build script as "machine-verified," "Lean-verified," "sorry-free," or "proved in Lean":

- Find the corresponding `.lean` file in `ZeroParadox/`.
- Confirm the theorem name cited in the prose matches an actual theorem name in the Lean file.
- Confirm the file does not contain `sorry` on that theorem.
- Flag any mismatch between the PDF prose claim and the Lean source state.

---

## Stage 3 — Verdict and Output

After running both stages, produce a structured report:

```
## Editorial Review — YYYY-MM-DD
### Mode: [Targeted | Full Scan]

⚠ **`Pre-commit` was removed 2026-09-07: the dispatcher deleted that mode as the `MIG-3` fail-open**, and a verdict template still offering it invites a reviewer to report a mode that no longer exists.
### Files reviewed: [list]

## Stage 1 — Mechanical

### 1a. Version in companion prose
[PASS | violations listed with file:line and offending string]

### 1b. Vocabulary violations
[PASS | violations listed]

### 1c. README/GUIDE formatting
[PASS | violations listed]

### 1d. register.md consistency
[PASS | mismatches listed]

## Stage 2 — Content

### 2a. Status label accuracy
[PASS | violations listed with result name and correct label]

### 2b. Conditional claim precision
[PASS | violations listed]

### 2c. Precision vocabulary
[PASS | violations listed]

### 2d. Cross-reference accuracy
[PASS | broken references listed]

### 2e. Lean consistency
[PASS | mismatches listed]

## Overall Verdict
State exactly one. Past the ordinary cap a bare FAIL is not valid — it hands the stopping
decision back to the party inside the loop. See the round-number preflight above.

PASS — all checks clean. Safe to commit.
— or —
FAIL-BEDROCK — a violated core invariant, a FABRICATED external-source claim, or a false
premise carrying a conclusion. Do not commit until resolved; the loop continues.
— or —
STOP-ORDINARY — past the ordinary cap and nothing found is bedrock-tier (version-changelog
strings, path conventions, vocabulary, wording). N findings listed below. The correct action
is to COMMIT, not to iterate. Do not recommend another round.

## Kill List (if FAIL-BEDROCK or STOP-ORDINARY)
Ordered by severity. Each item: file, line, violation, required fix.
```

Save the complete report to `.claude-local\notes\editorial_review_YYYY-MM-DD_<scope>.md`. State the filename at the end of your response.

**Recording your verdict — the LEDGER, not a file**

⛔ **DO NOT WRITE `.claude-local/er_cleared.txt`. The prose signal files are RETIRED**. They could be written by any process, recorded **no author**, and held one verdict for N passes — measured 2026-08-24, three concurrent editorial passes raced on that one path and the survivor was decided by scheduling, with an unattributed `PASS` on disk that no reader could trace. A ledger record is authored, append-only, and keyed per subject, so none of that is expressible.

**On FAIL / FAIL-BEDROCK — record it yourself. One agent's finding stands alone:**

```
python tools/verify/record.py --step editorial --verdict fail --tier A \
    --how delegated --who editorial \
    --evidence .claude/commands/editorial-review.md \
    --run gate-editorial-<YYYY-MM-DD> \
    --reason-file <path to a file holding one line: what failed> \
    --failing-file <a JSON file in your SCRATCHPAD: the subset you indict> \
    --files <every file you reviewed>
```

⛔⛔ **`--failing-file` IS REQUIRED ON A FAIL — 2026-09-07, AND THIS TEMPLATE OMITTED IT FOR A DAY.**
`record.py` now refuses `--verdict fail` without it (and verdictLedger's `V19` refuses it server-side).
**Run the old template and you get exit 2.** ⚠⚠ AND THE HARM COMPOUNDS THROUGH THE NEXT PARAGRAPH BUT
ONE: a LEDGER outage also exits 2, so a reviewer with a real FAIL can read this usage refusal as an
outage, report it as one, **and the FAIL never lands.** Measured 2026-09-07 by running this template
verbatim under `--dry-run`. ⭐ **This paragraph is why the correction below exists** — see *EXIT 2
MEANS THE RECORD DID NOT LAND — DISPATCH ON THE MESSAGE*; until 2026-09-09 this brief stated only the
ledger cause, and so armed the very trap described here.
⚠ `check_briefs.py`'s `flags` leg cannot catch this — it checks that a named flag EXISTS, never that a
REQUIRED one is present. **A rule was made mandatory and its callers were not updated**; the
checker built to keep briefs runnable is blind to exactly that shape.

`--files` is COVERAGE: what you examined. `--failing-file` is INDICTMENT: the subset that
actually failed. ⚠ **Absence is no longer a way to spell "all"** — it is refused. If the finding
genuinely covers everything you examined, pass the full `--files` list and say so explicitly. An
EMPTY list is refused too: it resolves to PASS at every path, which is exoneration wearing a FAIL's
costume. Historically, absent `failing` meant a FAIL over forty
files condemns the thirty-nine that passed.

```
    --failing-file <a JSON file in your SCRATCHPAD holding a list of the repo-relative paths
                    this verdict indicts — a subset of --files>
```

⚠ **Until 2026-09-06 no review gate could express this**, because the flag did not exist —
**every** tier-A blocking record up to then carries no `failing`. Mechanical checkers have named
their indicted subset since 2026-09-03. A gap that is CATEGORICAL rather than partial is a missing
affordance, not sloppiness — and this is the affordance.

⛔ **THE FROZEN COUNT THAT STOOD HERE IS GONE, AND ITS REMOVAL IS THIS BRIEF'S OWN RULE APPLIED TO ITSELF.** It was a ratio of the form *"N of N"*, written into FOUR briefs at once. The numerator held
while the denominator moved, so the ratio was false while both of its halves were once true.
⚠⚠ **AND THIS PARAGRAPH NAMED A DENOMINATOR UNTIL 2026-09-09, AND THAT NUMBER WENT STALE TOO** — it
said 125; measured today it is past that again. **In four briefs at once, which is precisely the failure
the sentence above describes.** Removed rather than updated: updating it would re-arm the same trap on a later date. **Compute it.** This file already says it in the `CALLER PRE-FLIGHT` blockquote at the top:
*"a number written into
four briefs goes stale in four places at once, and the tool computes it."* **Compute it:**
`find(tier='A')`, filter `verdict in (FAIL, UNDECIDED)`, count those with no `failing`.

⚠ **If your finding genuinely covers everything you examined, SAY SO EXPLICITLY** by listing them
all. That is a different fact from omitting the flag, and only one of them is a statement. The
measured cost of the other: a `check_prose` FAIL carrying 218 subjects whose own reason reads
*"1 failing subject(s)"* — the record knew, said so in prose, and condemned 218.

⚠ A FILE, never argv: a list of paths is exactly the payload that breaks on length, on quoting,
and on the `PreToolUse` hook that denies any command containing a denied token. The flag is
REFUSED on a PASS — a PASS indicts nothing — and refused if it names a path outside the recorded
subjects.

**On PASS — RECORD IT, with `--how delegated`.** This changed on 2026-08-25 and the old instruction here was *"record NOTHING"*. That was correct while `agreement` was the only route: V3 refuses a lone A-tier PASS, `mechanical` would be a lie about a computation, and `signature` asserts a PERSON accepted it. So a gate could report findings and had **no way to report success** — measured across the whole stream that day, nine agent reviews, every one a FAIL, and not a single recorded PASS. Absence of a pass therefore meant nothing, which is the exact ambiguity this ledger exists to remove.

```
python tools/verify/record.py --step editorial --verdict pass --tier A \
    --how delegated --who editorial \
    --evidence .claude/commands/editorial-review.md \
    --run gate-editorial-<YYYY-MM-DD> \
    --files <every file you reviewed>
```

### ⭐⭐ `--outstanding-file` IS BOUND TO HOLDING FINDINGS, NOT TO BEING PAST THE CAP

**These are two independent axes and this brief used to conflate them.** The verdict answers *how
severe is what I found*; `outstanding` answers *am I carrying findings that do not block*. **A round
at round 0 that found only ordinary things is a PASS, and it carries them.** You do not need to be
past the cap to use the flag, and you must not reach for STOP-ORDINARY in order to earn it.

**THE ARTIFACT, specified HERE because this is where the flag is now bound.** Write a JSON list of
your ordinary findings **to the SCRATCHPAD, never into the repo** — one object per finding, each with
at least `note` and `severity: "ordinary"`. That file is what `--outstanding-file` names:

```
python tools/verify/record.py --step editorial --verdict pass --tier A \
    --how delegated --who editorial \
    --evidence .claude/commands/editorial-review.md \
    --run gate-editorial-<YYYY-MM-DD> \
    --outstanding-file <the JSON file you wrote> \
    --files <every file you reviewed>
```

⚠ **Do not confuse this flag with `--failing-file`.** They have OPPOSITE polarity: `--failing-file`
NARROWS an indictment and is REFUSED on a PASS — *a PASS indicts nothing*; `--outstanding-file`
carries non-blocking findings and is ACCEPTED on a PASS.

⛔ **WHY THIS IS WRITTEN DOWN RATHER THAN LEFT TO JUDGEMENT.** While the flag was documented only
under STOP-ORDINARY, a reviewer holding ordinary-only findings under the cap had three bad options
and no good one: **PASS** dropped the findings, **FAIL** blocked the commit over things that do not
block, and **STOP-ORDINARY** misdescribed the round. Both records validate identically, so an
uncapped-pass-with-findings rendered as a clean pass — reintroducing the 2026-09-04 harm this brief
documents below, through its own routing.

⚠ **And it is a candidate mechanism for real non-convergence, which is why it is not merely tidy.**
The round-7 adversary, ranking it first of three process fixes: *"Under the cap, a reviewer holding
ordinary findings has PASS (which drops them) or FAIL-BEDROCK (which iterates). There is no
STOP-with-findings until the cap is already spent.* ***A gate whose only expressible non-clean verdict
continues the loop will continue the loop.***" Seven rounds on 2026-09-08 may have been iterating
partly because iterating was the only thing a reviewer could SAY.

⚠ **Measured, and it is why this is not hypothetical: the caller had to hand the missing instruction
to the reviewer in the spawn message.** `R-BRIEF`'s failure mode exactly — the rule lived in a
hand-typed prompt and not in the published brief, so it bound nothing spawned without it.

**On STOP-ORDINARY — DO NOT record, and DO NOT leave the caller to reconstruct it.** `R-ER`/`R-AR`
make this the one verdict the CALLER records, because it is a PROCEED that is not a pass and the
decision to proceed is not yours. **The flag above is not what makes this verdict different — the
CAP is.** You are the only one holding the findings, so **hand it over ready to use**: write the same
findings JSON specified above, and end your report with the exact command the caller should run:

```
python tools/verify/record.py --step editorial --verdict pass --tier A \
    --how delegated --who editorial \
    --evidence .claude/commands/editorial-review.md \
    --run gate-editorial-<YYYY-MM-DD> \
    --outstanding-file <the JSON file you wrote> \
    --files <every file you reviewed>
```

⚠ **`severity` MUST be `ordinary` on every finding.** The server refuses `bedrock` on a PASS (V18),
and that split is the entire safety of this route — it is not a way to ship one. A pass carrying
findings and a clean pass are different facts, and `outstanding` is the only place a reader can still
tell them apart; omitting the key is what a genuinely clean pass looks like.

⚠⚠ **STAGE THE FILES BEFORE YOU RECORD — AND THE CALLER OWNS THAT STEP.** Subjects are read from the
git INDEX, so a review of a modified-but-unstaged tree records NOTHING: `common.ledger_subjects`
fences every path that differs from the index, and when NOTHING survives the fence `record.py` exits
2 — *"nothing recordable for &lt;step&gt; at &lt;ref&gt; — the review certified no recordable file"*.
⚠ **All-or-nothing is the wrong model, and the middle case is the dangerous one:** on a PARTIAL fence
`record.py` prints the skip lines and **records a NARROWED subject set at exit 0**. A green exit does
not mean everything you reviewed was recorded — read the skip lines and say which paths did not make
it. **You are read-only and cannot fix it**, so if it fences your paths, SAY SO and hand the
command back. ⛔ Do not reach for `--ref` to route around it. Measured twice on 2026-09-09: both
gates reviewed correctly and neither could record, because nobody had staged.

⚠ **Measured 2026-09-04, and it is why this paragraph exists.** An editorial round returned
STOP-ORDINARY with eight findings and recorded NOTHING — correctly, per the rule — and the caller did
not record either. **A gate that found eight ordinaries and a gate that found nothing produced the
same ledger state**, and the findings survived only in prose.

⚠ **`--evidence` is the BRIEF, not the checker, and it is what makes a delegated PASS accountable.** Attribution is not authentication — no key material exists here and *"prove you are that agent"* was never available. What IS checkable is which instructions governed the round: **editing this brief stales the key and the gate re-runs.** A delegated verdict cannot outlive its instructions.

⚠ **`delegated` claims no consensus and must not be dressed as one.** It records ONE agent round, honestly. If a caller genuinely runs three independent passes, that is still `--how agreement` and it remains the stronger claim; V3 is untouched.

⚠ **Subjects are read from the git INDEX, so the files you reviewed must be STAGED.** `common.ledger_subjects` fences anything untracked or differing from the index, which is why a review of bytes that have since changed cannot be recorded by accident. ⚠ **It fails closed ONLY when NOTHING survives the fence — on a PARTIAL fence it records a NARROWED subject set at exit 0.** See *STAGE THE FILES BEFORE YOU RECORD*: read the skip lines and say which paths did not make it. If it fences a path, say so; do not work around it.

⚠⚠ **IF YOU ARE ONE OF SEVERAL CONCURRENT PASSES, EXPECT `V11` AND DO NOT RETRY.** The server
keys a record by `(step, basis, revision)`, so the FIRST failing pass records and later ones are
refused with *"revision 0 already exists for step '<step>' at this basis"*. That is the design
working — it fails CLOSED and loudly, with an attributed append-only record, where the retired
signal files failed silently and let the last writer win. **Do not treat it as an outage and do not
retry.** Instead: read the recorded record's `reason`, and **report to your caller exactly which of
your findings are ABSENT from it.** Two passes converging is corroboration; a finding only you found
is lost unless you say so in your report. `record.py --revision <n>` supersedes a verdict at this basis; the prior record REMAINS in
the append-only stream and `inventory` resolves the TIP, so a regrade stays auditable.
⚠ USE IT ONLY WHEN A VERDICT IS GENUINELY BEING RESTATED, NEVER TO RETRY A REFUSAL — a
`V11` you did not expect means another pass got there first, and the right move is still to
read its reason and report which of your findings it omits.

⚠⚠ **EXIT 2 MEANS THE RECORD DID NOT LAND. IT DOES NOT TELL YOU WHY, AND THE REMEDIES DIFFER.**
⛔ **THE BINDING RULE: DISPATCH ON THE MESSAGE, NEVER ON THE EXIT CODE.** Never report exit 2 as a
ledger outage unless the message says the ledger was reached and refused, or could not be reached.

**Dated survey — every exit-2 site in `record.py`, read FROM SOURCE on 2026-09-09.** A dated survey
is legitimate; a completeness claim is not (`R-ADJACENT`). ⚠ Two earlier versions of this block
asserted a fixed number of causes — one said ONE, the next said TWO — and each was falsified within a
day by a site nobody had opened the file to count. **The count is not the thing to memorise; the
message is.**

| what the message shows | what happened | what YOU do |
|---|---|---|
| an argparse `usage:` banner | your invocation is wrong — among others `--failing-file` missing on a FAIL, `--failing-file` on a PASS, `--outstanding-file` carrying a non-`ordinary` severity, `--evidence` absent on a delegated PASS, `--run` unset | **YOURS to fix.** Correct the flags and re-run. |
| `nothing recordable for <step> at <ref>` | the subject fence emptied your set. **The ledger was never contacted** | You are READ-ONLY and cannot fix it — see *STAGE THE FILES BEFORE YOU RECORD*. Say so and hand the command back. |
| any line beginning `UNDECIDED: verdictLedger ` — unreachable, refused, or no usable payload — or an outage line printed by the dry-run check | the ledger was reached and refused, or could not be reached. **The message says WHICH**: `record refused by verdictLedger:` is a rule being applied; `unreachable` decided nothing | **Report it.** Do NOT retry a refusal — the same call is refused again. An outage decided nothing and may be retried once the ledger is up. Either way the review may have been fine and simply went unrecorded. |

⛔ **If the message matches none of the three, it is a site added since the survey date — not one of
these wearing a different coat.** The binding rule still governs: report what the message actually
said, and do not translate it into the nearest familiar case. ⚠ **Translating an unfamiliar exit 2
into "the ledger" is the exact harm named earlier in this brief** — a reviewer with a real FAIL
reports an outage, and the FAIL never lands.

⚠ **Never claim PASS when the verdict was STOP-ORDINARY.** Both are proceed verdicts and they are not the same fact; the distinction is why the caller, not you, decides what reaches the ledger.

Do not soften findings. A failed check is a failed check. Name the file, the line, and the exact string.
---

## Before you start: name your DETECTOR

Read `.claude-local/DEFECT_CLASSES.md` — one row per defect class, each with the detector that finds
it. State three things in your first output, before any finding:

- **LAYER** — claim / declaration / statement / proof / tooling / prose. A gate that does not name its
  layer re-attacks the layer the last gate already cleared.
- **STATE** — the condition you tested under (warm cache, truncated log, stale signal, at release).
  Two bedrock findings in one session were correct in the state tested and wrong in a routine one.
- **DETECTOR** — by id, e.g. `DC-1: read the elaborated #check`. "Check the glosses" is not a detector.

**PREFER A DETECTOR WHOSE VERB IS *RUN* OVER ONE WHOSE VERB IS *READ*.** Measured across ~20 agent
runs: every BEDROCK finding came from executing something, every ORDINARY finding from reading
something, no exceptions. If your whole review is reading, you will find only ordinary defects.
