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
any file under the repository, with exactly two exceptions: your findings note under
`.claude-local/notes/`, and **any source PDF you retrieve at rung D, filed into `.claude-local/papers/`**.
⚠ **The second is not a loophole, it is what makes rung A work.** Both live under `.claude-local/`,
which is gitignored — so none of them touches the tracked tree, and the read-only property this section
is protecting is unaffected. A scout that reads a source and files nothing leaves the library exactly as
poor as it found it, and the decay is invisible because it looks like restraint.

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
- Empty or absent: **STOP AND ERROR. Do not proceed, and do not fall back to a diff.** Report `SCOPE UNKNOWN — refusing to review` and record nothing. Direct version-control commands are denied to agents here (`MIG-3`, the OPEN entry about brief scope discovery — not the closed one about `common.py` mirrors, which shares the id). ⚠ **The denial itself is loud, not silent** — measured 2026-08-24 through both shells, it returns a ~25-line `BLOCKED:` message naming the command, the reason and the substitute. **What fails open is the BEHAVIOUR, not the call:** an agent told to review the staged diff, handed a refusal instead of a file list, has no instruction for that state and falls back to a scope of nothing — and every PASS condition below is **vacuously true of the empty set**, so the PASS writes the signal that clears the push. An empty scope is not an empty diff. If you need the staged list, the caller must pass it explicitly; `mcp__gitRobot__read(op='diff', args=['--staged','--name-only'])` is the only sanctioned way to obtain it, and it is the CALLER's job, not yours.
- A single block of prose: review that text only.

## Scope — what counts
Evaluate only **synthesis / bridge claims**: a distinctive claim that unifies or identifies a structure across more than one field or framework, or that sits in a specialist subfield the framework is not native to. **Out of scope:** a claim whose central content is a single named classical theorem the framework merely invokes (e.g. Ostrowski, Gentzen) — that is already anchored; and a claim already carrying a specific prior-art citation (verify the citation is real and correctly directed, then move on).

## Procedure — for each distinctive synthesis claim
1. **Check our own corpus FIRST (before any web search).** Grep the repo and `.claude-local` (notes, `external/`, outreach) for an existing reference to the claim/concept — much of this project's prior-art knowledge already lives there (citations inside `.lean` docstrings, vendored libraries, outreach drafts, research notes). Anything already cited there is NOT a gap; do not "rediscover" it. Only what is genuinely uncited in our own corpus proceeds to a web search.
2. **State the claim** in the target field's own terms.
3. **Identify the specialist branch** that would own it (the subfield and the kind of result).
4. **Search the literature — run the LADDER in order. Do not skip a rung, and do not stop early.**
   - **Rung A — `.claude-local/papers/`.** The downloaded-source library. **Grep loosely** (OCR'd scans carry intra-word spaces, so a tight-pattern miss is not absence).
   - **Rung B — `theoremsearch`** (MCP tool `mcp__theoremsearch__theorem_search`). Matches on the STATEMENT, not the title, so it reaches claims a title search cannot. Four rules, each measured:
     1. **THREE PHRASINGS MINIMUM.** Vary them along the four axes in CLAUDE.md § `R-NOTINLIB` (body: `tools/process/not-in-the-library.md`): **POLARITY** (how the corpus would say it if it DISAGREED with you), **PART OF SPEECH** (the verb that builds it, not the noun), **VOCABULARY** (the domain's words), **DISPLAY** (never conclude absence from TRUNCATED output). Measured 2026-08-23: the noun form put the right theorem at rank 1 and the **verb** form dropped it out of the top 5 entirely — same claim, same index. **A single-phrasing negative is worthless.**
     2. **DISPLAY is this rung's own exposure.** `theoremsearch` returns a capped list, so a scout who reads the cap and stops **has measured the cap, not the literature**. Re-run untruncated.
     3. **IGNORE the `similarity`/`score` field.** The 7-case calibration of 2026-08-23 found **no threshold that keeps the garbage out without discarding the find** — noise scored 0.69 while genuine prior art scored 0.61. ⚠ That is a claim about THRESHOLDS, **not** that the score runs backwards. Measured 2026-08-24 across two independent probes: exact statements of Lawvere's fixed-point theorem returned 0.676, 0.683 and 0.686, other exact hits 0.834 and 0.777, and relevant fixed-point theorems 0.732 and 0.728 against irrelevant ones at 0.687 and 0.680. **Rank by reading; never filter on the number.**
     4. ⚠ **`paper_filter` takes a TITLE, not an arXiv id.** Passing an id returns empty and reads exactly like absence.
   - **Rung C — the open web.** Run it when rung B returns no good match, **and also when rung B returns a neighbourhood hit whose real source still needs identifying**. Everything pre-arXiv lives here — Lawvere 1969, Aczel 1988, Ostrowski, Gentzen, Carlström. `theoremsearch` cannot return those as sources, only as work other people cite, **and the reason is the corpus boundary rather than a quirk: the index is built from arXiv, so a work published before it did not exists in the index only inside the reference lists of papers that cite it.** A Gentzen-1936 query returns modern arXiv papers citing Gentzen, never Gentzen.
   - **Rung D — RETRIEVE AND READ THE FULL SOURCE.** Use WebFetch; if a domain is not reachable that way, download it via PowerShell `Invoke-WebRequest -Uri <url> -OutFile .claude-local/papers/<author_topic_year[_id]>.pdf` and open it with the Read tool (this works for any publisher — arXiv, Dagstuhl/LIPIcs, nLab, journal sites). **Download straight into `.claude-local/papers/` under that name** — one destination, so filing is not a second step anyone can skip — and **validate before you rely on it** (a tiny PDF is an error page, not a paper). ⚠ **This is the one place the read-only rule yields, and it is deliberate**: filing the source is what feeds rung A for every later scout, so a review that reads a PDF and leaves nothing behind makes the library decay while looking like diligence.

   ⚠⚠ **RUNGS A–C ARE DISCOVERY. ONLY RUNG D IS VERIFICATION.** **Draft from source, not from snippets — and a `theoremsearch` theorem body is a snippet, not a passage in hand.** Measured 2026-08-23: a returned body read as our recorded citation renumbered for a journal version, and the PDF showed the two statements were different (connexity versus splitting). The returned `slogan` field is an **LLM paraphrase**, `label`/`link` come back **null**, and ambient hypotheses are inconsistently included. If you genuinely cannot read the source, say so and treat the citation as **unverified**.

   ⚠ **A NULL FROM RUNG B IS UNINFORMATIVE ON ITS OWN.** The index is coverage-bounded and the bound is invisible from the result — a paper this project holds on disk is verifiably absent from it. Never write "no prior art exists" from rung B, and do not record "none located as of &lt;date&gt;" until rung C has also run.
5. **Verdict for this claim:**
   - **Prior art exists and is already cited** in the content → OK (after confirming the citation is real and correctly directed).
   - **Prior art exists and is NOT cited** → FAIL for this claim: give the full citation (author, year, venue), state the claim's honest *delta* against it (what the framework genuinely adds), and the credit direction (framework is an instance joining the program, never subsuming it).
   - **A diligent search finds no closer specialist prior art** → OK, but record "searched [date], no closer prior art found" so the determination is on file.
6. **Citation-direction check:** for any prior art the content already cites, confirm it is cited in the correct direction (framework as instance/extension, not the prior work as an instance of the framework) and that the source actually says what the content claims it says.

## Output
**Verdict:** **VERDICT: PASS**, **VERDICT: FAIL-BEDROCK**, or **VERDICT: STOP-ORDINARY** — see the round-number preflight above; past the ordinary cap, a bare FAIL is not a valid verdict.

- **PASS** — every distinctive synthesis claim is either cited-and-verified, or searched-and-novel ("searched, none found" recorded explicitly).
- **FAIL-BEDROCK** — an uncited closest-prior-art that makes a distinctive claim look unaware, a FABRICATED claim about a source, or a false premise carrying a conclusion. The loop continues.
- **STOP-ORDINARY** — past the ordinary cap and nothing found is bedrock-tier: citation scope, a mischaracterized lemma, a stale paper title or lemma number, hedging a tier too strong. Report the findings, then state explicitly that the correct action is to PUSH, not to iterate.


Save the findings to `.claude-local/notes/prior_art_review_YYYY-MM-DD.md`, listing every source consulted and every PDF saved. State the filename at the end.

**Recording your verdict — the LEDGER, not a file** (file-path mode only; SKIP for a pasted prose block, and there is no staged-diff mode — see the mode selection above, where an empty scope is a refusal):


⛔ **DO NOT WRITE `.claude-local/pa_cleared.txt`. The prose signal files are RETIRED.** Nothing GATES on that path any more — `batch.py`'s review check asks the ledger, and `hooks.py` and `guards.py` never opened it. ⚠ One reader remains and it is informational only: `check_release_ready.py` prints whether the file is present and never blocks on it, so its absence costs a line of output, not a refusal. It could be written by any process, recorded **no author**, and held one verdict for N passes; measured 2026-08-24, three concurrent passes of a sibling gate raced on one such path and the survivor was decided by scheduling. A ledger record is authored, append-only and keyed per subject, so none of that is expressible.

**On FAIL / FAIL-BEDROCK — record it yourself. One agent's finding stands alone** (*FAIL alone, PASS by unanimity or signature*):

```
python tools/verify/record.py --step prior_art --verdict fail --tier A \
    --how agreement --passes 1 --agreed 1 \
    --run gate-prior-art-<YYYY-MM-DD> \
    --reason-file <path to a file holding one line: the uncited closest prior art> \
    --files <every file the CALLER handed you>
```

**On PASS — record NOTHING and report the verdict to your caller.** A lone A-tier PASS is absence-of-evidence wearing a clean bill, and the server's `V3` rejects it anyway. The caller either runs three independent passes and records the agreement, or takes a human signature.

⚠ **`--run` is REQUIRED, and `--reason-file` is not optional politeness.** `V9` refuses a record with no run id, and a spawned gate has no pipeline to inherit one from. The reason goes in a FILE because the PreToolUse hook denies any command containing the denied version-control token — arguments included — so an honest reason describing a scope-discovery defect blocks the very command that reports it. Measured three times on 2026-08-24, by three separate review agents.

⚠ **Subjects are read from the INDEX, so the files must be STAGED**, and `--ref` defaults to `INDEX` for exactly that reason. `common.ledger_subjects` fences anything untracked or differing from the index; it fails closed. ⚠⚠ **IF YOU ARE ONE OF SEVERAL CONCURRENT PASSES, EXPECT `V11` AND DO NOT RETRY.** The server
keys a record by `(step, basis, revision)`, so the FIRST failing pass records and later ones are
refused with *"revision 0 already exists for step '<step>' at this basis"*. That is the design
working — it fails CLOSED and loudly, with an attributed append-only record, where the retired
signal files failed silently and let the last writer win. **Do not treat it as an outage and do not
retry.** Instead: read the recorded record's `reason`, and **report to your caller exactly which of
your findings are ABSENT from it.** Two passes converging is corroboration; a finding only you found
is lost unless you say so in your report. `record.py` exposes no `--revision`, so the supersede
chain is not reachable from here — that is a known gap, not something for you to work around.

⚠ **Exit 2 is NOT exit 1** — it means the ledger was unreachable or refused the record, a RECORDING failure rather than a finding about the corpus.



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
