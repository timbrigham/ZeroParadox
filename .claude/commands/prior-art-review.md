**ISOLATION REQUIRED: Do not run this review inline. Use the Agent tool to spawn a fresh instance with no conversation context.**

Read `$ARGUMENTS` to determine what to review, then spawn an Agent using the Agent tool with `subagent_type` omitted (general-purpose). Pass the prompt below verbatim, substituting `ARGUMENTS_VALUE` for the actual value of `$ARGUMENTS`. The agent must have no knowledge of the current session.


## CALLER PRE-FLIGHT — round number and the cap (do this BEFORE spawning)

**CALLER ONLY: run `python tools/verify/gate_round.py bump` ONCE per round and put the number in the brief. The reviewer must NEVER bump — a spawned agent that bumps double-counts the round and burns the cap early (measured 2026-07-19). Reviewers may only `show`.**
A rule about a loop does not fire from inside the loop — on 2026-07-19 three rounds ran against a
2-round cap because the caller was fixing kills, not counting rounds. The reviewer stands outside the
loop, so it enforces the cap. Paste this into the brief with N substituted:

> This is **gate round N** against a cap of 2 (ORDINARY) / 5 (BEDROCK). Your verdict must be one of
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

## CALLER PRE-FLIGHT — attach the sources; this is your job, not the scout's

**Where the content under review already CITES a source, attach that source's text** (relevant pages, quotes, page numbers) under a `## Source material` heading in the brief. The scout's own rules already say a search summary is a lead and not a citation — but it can only act on that with the source in hand.

**The failure this prevents.** Without the source, a scout can report a citation as *unverified*. It cannot report it as *false*. On 2026-07-19 a docstring claimed a cited paper's "norm counts coefficients"; the claim was invented, the real definition is a finite-fibre condition, and this gate correctly returned "abstract-verified only" — the strongest verdict available to it. Three gates passed over the error for the same reason. Attaching the paper is what converts "unverified" into "wrong."

**Before concluding a source is unreadable**, try direct extraction — `pypdf` and `pdfminer` are installed (`.claude-local/extract_pdf_text.py`). `WebFetch`'s PDF converter has misreported a text-layer PDF as an unreadable scan. Do not record a tooling failure as a fact about the paper.

This is distinct from the scout's *search* job: it still hunts for prior art we have NOT cited. This pre-flight covers the other half — prior art we HAVE cited and may be describing wrongly.

---
Spawn the Agent with this prompt (substitute ARGUMENTS_VALUE for the actual value of $ARGUMENTS):

---
You are a **literature scout and prior-art referee** for a mathematical framework. Your job is to make sure each distinctive *synthesis* claim — a claim that unifies, connects, or identifies a structure across more than one field — is placed honestly against the prior art that already owns it, so the framework reads as an instance *joining* a recognized program rather than one reinventing it.

Working directory: use the current project root.

**Mode selection — check ARGUMENTS_VALUE:**
- File paths (tokens ending in `.md`, `.txt`, `.rst`, `.py`, or `.lean`, space-separated): review only those files.
- Empty or absent: review the staged diff — run `git diff --staged` and read the files it touches.
- A single block of prose: review that text only.

## Scope — what counts
Evaluate only **synthesis / bridge claims**: a distinctive claim that unifies or identifies a structure across more than one field or framework, or that sits in a specialist subfield the framework is not native to. **Out of scope:** a claim whose central content is a single named classical theorem the framework merely invokes (e.g. Ostrowski, Gentzen) — that is already anchored; and a claim already carrying a specific prior-art citation (verify the citation is real and correctly directed, then move on).

## Procedure — for each distinctive synthesis claim
1. **Check our own corpus FIRST (before any web search).** Grep the repo and `.claude-local` (notes, `external/`, outreach) for an existing reference to the claim/concept — much of this project's prior-art knowledge already lives there (citations inside `.lean` docstrings, vendored libraries, outreach drafts, research notes). Anything already cited there is NOT a gap; do not "rediscover" it. Only what is genuinely uncited in our own corpus proceeds to a web search.
2. **State the claim** in the target field's own terms.
3. **Identify the specialist branch** that would own it (the subfield and the kind of result).
3. **Search the literature** (web search), then **read the actual source** — do not stop at search summaries. To read a source: use WebFetch; if a domain is not reachable that way, download it via PowerShell `Invoke-WebRequest -Uri <url> -OutFile .claude-local/<name>.pdf` and open it with the Read tool (this works for any publisher — arXiv, Dagstuhl/LIPIcs, nLab, journal sites). **Draft from source, not from snippets:** a search summary is a lead, not a citation. If you genuinely cannot read the source, say so and treat the citation as unverified.
4. **Verdict for this claim:**
   - **Prior art exists and is already cited** in the content → OK (after confirming the citation is real and correctly directed).
   - **Prior art exists and is NOT cited** → FAIL for this claim: give the full citation (author, year, venue), state the claim's honest *delta* against it (what the framework genuinely adds), and the credit direction (framework is an instance joining the program, never subsuming it).
   - **A diligent search finds no closer specialist prior art** → OK, but record "searched [date], no closer prior art found" so the determination is on file.
5. **Citation-direction check:** for any prior art the content already cites, confirm it is cited in the correct direction (framework as instance/extension, not the prior work as an instance of the framework) and that the source actually says what the content claims it says.

## Output
**Verdict:** **VERDICT: PASS**, **VERDICT: FAIL-BEDROCK**, or **VERDICT: STOP-ORDINARY** — see the round-number preflight above; past the ordinary cap, a bare FAIL is not a valid verdict.

- **PASS** — every distinctive synthesis claim is either cited-and-verified, or searched-and-novel ("searched, none found" recorded explicitly).
- **FAIL-BEDROCK** — an uncited closest-prior-art that makes a distinctive claim look unaware, a FABRICATED claim about a source, or a false premise carrying a conclusion. The loop continues.
- **STOP-ORDINARY** — past the ordinary cap and nothing found is bedrock-tier: citation scope, a mischaracterized lemma, a stale paper title or lemma number, hedging a tier too strong. Report the findings, then state explicitly that the correct action is to PUSH, not to iterate.


Save the findings to `.claude-local/notes/prior_art_review_YYYY-MM-DD.md`, listing every source consulted and every PDF saved. State the filename at the end.

**Signal file (staged-diff and file-path modes only; SKIP for a pasted prose block):**


The signal records, per file the review certified, the file's **content SHA-256** — not a HEAD hash (SHA-256-per-file scheme, 2026-07-20). A signal now survives an unrelated later commit (a data-only `ssot.json` sync, a rebuilt PDF) that touches nothing the review examined; only a change to a reviewed file, or a new reviewable file appearing in the push, invalidates it. Write it BOM-free — `[System.IO.File]::WriteAllText($path, $text, (New-Object System.Text.ASCIIEncoding))`, not `Set-Content -Encoding utf8`.

Format:
- **line 1** = the verdict record (echoed by the hook at push time, so "cleared" is never silently read as "clean").
- **line 2+** = one line per file you reviewed, `<sha256>  <repo-relative-path>`. For a new `.lean` file this is normally the one file. List EVERY reviewable file in the diff — the hook requires each reviewable file in the push to be covered by a recorded hash (a data file like `ssot.json` or a `.pdf` is not reviewable and must NOT be listed).

⚠ **HASH THE FILE ON DISK. Never a git value** (Tim, 2026-08-09). `Get-FileHash -Algorithm SHA256 <path>` (lowercase the result), or `sha256sum <path>` and take the first field. Do **not** use `git show "HEAD:<path>"`: that is the same command meaning two different things depending on when it runs, and if the change is not yet committed HEAD holds the OLD content, so the signal goes stale the instant the commit lands. The pre-push hook and `batch.py` both hash the file on disk, so a disk hash is what they compare against at any point in the cycle.

- **PASS** → write `.claude-local/pa_cleared.txt`: `PASS - clean, no findings.` on line 1, the `<sha256>  <path>` lines after.
- **STOP-ORDINARY** → **write the signal too.** Line 1 `STOP-ORDINARY (round N) - cleared under the ordinary cap; M findings, none bedrock-tier.`, the hash lines after. **This is not a forgery and not a courtesy.** STOP-ORDINARY is a sanctioned proceed verdict — the cap rule states that "the correct action is to PUSH, not to iterate." Withholding the signal on it made the cap and the pre-push hook give opposite instructions for the same state, which forced every capped review to end in `git push --no-verify` and turned the bypass from exceptional into routine. The verdict line keeps the record honest about *which* verdict cleared the push.
- **FAIL / FAIL-BEDROCK** → delete `.claude-local/pa_cleared.txt` if it exists. Never write a signal for a failing review.

Never write a signal claiming PASS when the verdict was STOP-ORDINARY. That distinction is the entire purpose of line 1's verdict record.



Do not soften findings. The goal is that no distinctive synthesis claim ships without its closest prior art either cited or shown absent.
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
