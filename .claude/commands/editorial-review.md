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


## HARD CONSTRAINTS ON THIS REVIEW — read before doing anything

**This review is READ-ONLY on the working tree.** Read, measure, report. Do NOT modify, create, or delete
any file under the repository, with exactly ONE exception: your findings note under
`.claude-local/notes/`. ⚠ **There is no signal file any more** — verdicts go to the ledger, and the
recording section below is the only place you write a verdict.

**NO SCRATCH FILES IN THE REPO.** If you need a probe, a temp script, or a measurement harness, write it
to the **session scratchpad directory** named in your environment — never under `ZeroParadox/` or
anywhere else in the working tree — run it there, and delete it when done. Measured 2026-07-19: a review
agent left a scratch probe (`ZZTestOrd.lean`, since deleted) in the source tree; the next commit swept it up, and a scratch
probe is now in the permanent history.

**Do not cite a private path in anything reader-facing.** `.claude-local/` is gitignored and unreachable
to an external reader; a tracked file must never point at it.

---

Spawn the Agent with this prompt (substitute ARGUMENTS_VALUE for the actual value of $ARGUMENTS):

---
You are a technical editor reviewing formal mathematical publication documents for internal consistency, editorial standards compliance, and prose precision. You have no prior knowledge of this project — read the relevant files first to build your understanding before running any checks.

Working directory: `C:\Workspace\ZeroParadox`. Private working files are in `.claude-local\`.

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

Run these checks on every in-scope file. They are pattern-based and should produce zero false negatives.

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
### Mode: [Pre-commit | Targeted | Full Scan]
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

Save the complete report to `.claude-local\notes\editorial_review_YYYY-MM-DD.md`. State the filename at the end of your response.

**Recording your verdict — the LEDGER, not a file**

⛔ **DO NOT WRITE `.claude-local/er_cleared.txt`. The prose signal files are RETIRED**. They could be written by any process, recorded **no author**, and held one verdict for N passes — measured 2026-08-24, three concurrent editorial passes raced on that one path and the survivor was decided by scheduling, with an unattributed `PASS` on disk that no reader could trace. A ledger record is authored, append-only, and keyed per subject, so none of that is expressible.

**On FAIL / FAIL-BEDROCK — record it yourself. One agent's finding stands alone:**

```
python tools/verify/record.py --step editorial --verdict fail --tier A \
    --how agreement --passes 1 --agreed 1 \
    --run gate-editorial-<YYYY-MM-DD> \
    --reason-file <path to a file holding one line: what failed> \
    --files <every file you reviewed>
```

**On PASS — record NOTHING, and report the verdict to your caller.** § 6a-i: *FAIL alone, PASS by unanimity or signature.* A lone A-tier PASS is absence-of-evidence wearing a clean bill, and `V3` rejects it at the server anyway. The caller either runs `policy.agreement.min_passes` independent passes and records the agreement, or takes a human signature. **Your job ends at reporting.**

⚠ **Subjects are read from the git INDEX, so the files you reviewed must be STAGED.** `common.ledger_subjects` fences anything untracked or differing from the index — it fails closed, which is why a review of bytes that have since changed cannot be recorded by accident. If it fences a path, say so; do not work around it.

⚠⚠ **IF YOU ARE ONE OF SEVERAL CONCURRENT PASSES, EXPECT `V11` AND DO NOT RETRY.** The server
keys a record by `(step, basis, revision)`, so the FIRST failing pass records and later ones are
refused with *"revision 0 already exists for step '<step>' at this basis"*. That is the design
working — it fails CLOSED and loudly, with an attributed append-only record, where the retired
signal files failed silently and let the last writer win. **Do not treat it as an outage and do not
retry.** Instead: read the recorded record's `reason`, and **report to your caller exactly which of
your findings are ABSENT from it.** Two passes converging is corroboration; a finding only you found
is lost unless you say so in your report. `record.py` exposes no `--revision`, so the supersede
chain is not reachable from here — that is a known gap, not something for you to work around.

⚠ **Exit 2 is NOT exit 1.** `record.py` exits 2 when the ledger could not be reached or refused the record — the review may have been fine and simply went unrecorded. Report that as a RECORDING failure, never as a finding about the corpus.

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
