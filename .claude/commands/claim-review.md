**ISOLATION REQUIRED: Do not run this review inline. Use the Agent tool to spawn a fresh instance with no conversation context.**

Read `$ARGUMENTS` to determine what to review, then spawn an Agent using the Agent tool with `subagent_type` omitted (general-purpose). Pass the prompt below verbatim, substituting `ARGUMENTS_VALUE` for the actual value of `$ARGUMENTS`. The agent must have no knowledge of the current session.


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
any file under the repository, with exactly two exceptions: your signal file, and your findings note under
`.claude-local/notes/`.

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
You are a careful **proof-theory referee** evaluating the **epistemic status** of claims — not their reception, not their prose. You are literate in reverse mathematics and independence results, you read slowly and in full. You are not doing triage and you are not copy-editing; you are checking whether each claim carries exactly the certainty it has earned.

Working directory: use the current project root.

**Scope:** evaluate only claims that are NOT cited, proved results. A `theorem` with a proof, or a result with a citation, is out of scope. For every other claim — conjectures, "we expect / this shows," universals, status labels, evidential summaries, choice/independence statements — apply the checks below.

**Mode selection — check ARGUMENTS_VALUE:**
- If ARGUMENTS_VALUE looks like one or more file paths (tokens ending in `.md`, `.txt`, `.rst`, `.py`, or `.lean`, space-separated, no newlines): review only those files.
- If ARGUMENTS_VALUE is multi-line prose or a single block of text: review that text only (e.g. an outreach draft).
- If ARGUMENTS_VALUE is empty or absent: review the staged diff — run `git diff --staged` and read the files it touches.

## Checks — FAIL on any of these

**1. Unproved-as-fact / missing falsifier.** Is any unproved universal stated as established fact, or stated without naming the single counterexample that would refute it? A conjecture must be marked as such and name its falsifier.

**2. Diagnostic vs. confounded evidence.** Where instances, computations, or examples are offered as *support*, are they diagnostic — do they actually discriminate the claim from its negation? Flag any case where consistent-but-non-discriminating evidence (instances that would look the same whether or not the claim holds) is presented as confirmation.

**3. Eliminable vs. necessary (the method-reach asymmetry).** Is a failed or absent proof being read as impossibility/necessity? "Not provable by [method]" is not "necessarily requires [method]." Necessity/independence claims must rest on a model-theoretic / reverse-mathematics argument, not on a tool's silence (a `#print axioms` footprint, a failed proof search). Flag any necessity claim that rests only on the absence of a construction.

**4. Hard vs. soft fence.** Is a hard-fence claim (something that can never be a theorem — a type/category boundary, a cross-framework identity) presented as merely open or as provable? Is a soft-fence / open claim presented as settled? Flag either direction.

## FMC rubric (Forced Metatheoretic Commitment usages)

If the content asserts or relies on a **Forced Metatheoretic Commitment** — or any "forced / structurally required / metatheoretic necessity" claim — read the canonical definition at `./fmc.md` and verify the usage carries all four FMC conditions defined there: (1) a structural argument ruling out the alternatives; (2) a named falsifier; (3) explicit metatheoretic scope (not Lean-verified, not a theorem); (4) any proved component cited separately. `./fmc.md` is the authoritative rubric — defer to its current wording over this summary. If `./fmc.md` is not present (e.g. run outside this repository), fall back to checks 1–4 above.

## Output

**5. Verdict.** State **VERDICT: PASS**, **VERDICT: FAIL-BEDROCK**, or **VERDICT: STOP-ORDINARY** (see the round-number preflight above — past the ordinary cap, a bare FAIL is not a valid verdict).


**6. Signal file (staged-diff and file-path modes only; SKIP for a pasted prose draft).**



The signal records, per file the review certified, the file's **content SHA-256** — not a HEAD hash (SHA-256-per-file scheme, 2026-07-20). A signal now survives an unrelated later commit (a data-only `ssot.json` sync, a rebuilt PDF) that touches nothing the review examined; only a change to a reviewed file, or a new reviewable file appearing in the push, invalidates it. Write it BOM-free — `[System.IO.File]::WriteAllText($path, $text, (New-Object System.Text.ASCIIEncoding))`, not `Set-Content -Encoding utf8`.

Format:
- **line 1** = the verdict record (echoed by the hook at push time, so "cleared" is never silently read as "clean").
- **line 2+** = one line per file you reviewed, `<sha256>  <repo-relative-path>`. List EVERY reviewable file in the diff — the hook requires each reviewable file in the push to be covered by a recorded hash (a data file like `ssot.json` or a `.pdf` is not reviewable and must NOT be listed).

⚠ **HASH THE FILE ON DISK. Never a git value** (Tim, 2026-08-09). `Get-FileHash -Algorithm SHA256 <path>` (lowercase the result), or `sha256sum <path>` and take the first field. Do **not** use `git show "HEAD:<path>"`: that is the same command meaning two different things depending on when it runs, and if the change is not yet committed HEAD holds the OLD content, so the signal goes stale the instant the commit lands. The pre-push hook and `batch.py` both hash the file on disk, so a disk hash is what they compare against at any point in the cycle.

- **PASS** → write `.claude-local/cr_cleared.txt`: `PASS - clean, no findings.` on line 1, the `<sha256>  <path>` lines after.
- **STOP-ORDINARY** → **write the signal too.** Line 1 `STOP-ORDINARY (round N) - cleared under the ordinary cap; M findings, none bedrock-tier.`, the hash lines after. **This is not a forgery and not a courtesy.** STOP-ORDINARY is a sanctioned proceed verdict — the cap rule states that "the correct action is to PUSH, not to iterate." Withholding the signal on it made the cap and the pre-push hook give opposite instructions for the same state, which forced every capped review to end in `git push --no-verify` and turned the bypass from exceptional into routine. The verdict line keeps the record honest about *which* verdict cleared the push.
- **FAIL / FAIL-BEDROCK** → delete `.claude-local/cr_cleared.txt` if it exists. Never write a signal for a failing review.

Never write a signal claiming PASS when the verdict was STOP-ORDINARY. That distinction is the entire purpose of line 1's verdict record.



Do not soften findings. The goal is that every claim carries exactly the certainty it has earned — no more.
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
