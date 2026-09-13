# The editorial and adversary gates — protocol, signal scheme, and what triggered them

**Body for `CLAUDE.md` §§ `R-ER` and `R-AR`.** The rules are there; the SHA-256-per-file
signal scheme, the hash-from-disk correction, the `MIG-3` fail-open, and the incident that
created each gate are here.

---

## Editorial Review Gate — Hard Rule

**Any commit touching document prose requires editorial review to have completed before the commit is made.** This applies to:

- Changes to any build script `body()`, `cbody()`, `sp()`, or box-helper string content
- Changes to README.md, GUIDE.md, RELEASES.md, or any `.md` file in the repo root (except `CLAUDE.md` — see the gate exemption above)
- Changes to any companion or formal document build script
- Changes to register.md

**The protocol:**
1. Before committing any of the above, run `/editorial-review` — ⚠ **and PASS IT THE FILE PATHS
   EXPLICITLY (Targeted mode) until `MIG-3` is fixed.** Pre-commit mode discovers its own scope with
   `git diff --staged`, which is now denied, and **the denial FAILS OPEN**: the empty result reads as
   *"nothing staged"*, the brief falls back to Full Scan, reviews a scope nobody asked for, and
   **still writes a signal** hashing whatever it opened. A gate certifying the wrong file set while
   reporting success. Same pattern in `/adversary-review` and `/claim-review`. Ticket:
   `.claude-local/queue/tooling-briefs-gitcall-migration.md`.
2. Wait for the editorial agent to return a verdict
3. If FAIL: resolve every item in the kill list before committing
4. The agent RECORDS ITS OWN VERDICT, FAIL and PASS alike (`record.py --step editorial --how delegated`) — on PASS, proceed with the commit. **STOP-ORDINARY is the one exception:** it is a PROCEED verdict that is not a pass, so it goes to the caller, who decides what reaches the ledger and carries the round's findings on the record as `outstanding`.

Same-session self-review does not satisfy this requirement. `/editorial-review` spawns a fresh agent with no conversation history.

⚠⚠ **THE PROSE SIGNAL FILES ARE RETIRED (2026-08-24), AND NOTHING READS THEM.** `batch.py`'s review check asks the **verdictLedger** — `record.stale_or_missing`, the single staleness predicate, server-side. Re-deriving freshness locally would be the mirror defect at exactly the point the split exists to protect: two implementations of *"is this verdict still good"*, disagreeing silently. An unreachable ledger returns `None`, and `None` is not an empty set, so the check fails **CLOSED**.

The per-subject principle SURVIVES the retirement and is now the ledger's, not a file's: a record is keyed to each subject's blob id, so a data-only commit (`ssot.json`, a rebuilt PDF) does not stale a review that never examined it — the failure mode of the older HEAD-equality scheme. What the ledger adds is what a file could never carry: **an author, append-only history, and one verdict per subject rather than one verdict per path.** Measured 2026-08-24 — three concurrent passes of one gate raced on a single signal path and the survivor was decided by scheduling, leaving an unattributed verdict no reader could trace.

If nothing reviewable changed, no review is required. If a step reads STALE it is because a reviewed file actually changed; re-run the gate and let it record.

⚠ **EVERY hash in this scheme is of the FILE ON DISK. Never a git value** (Tim, 2026-08-09). Not `git show "HEAD:<path>"`, not the index, not the blob — `Get-FileHash -Algorithm SHA256 <path>` or `sha256sum <path>`. **Why it is a rule and not a preference:** the four command files used to say *"compute each hash from the committed content … `git show "HEAD:<path>" | sha256sum`"*, and that is one command meaning two different things depending on when it runs. At push time HEAD is the new commit, so it matched and the instruction looked correct for months. But editorial and claim-review are **pre-commit** gates, so there HEAD holds the **OLD** content: the reviewer certifies the pre-edit file, the commit lands, and the hook compares against a hash of content that no longer exists. **Measured 2026-08-09** with both controls — on a clean tree the two forms agree (which is why nothing ever caught it), and on a dirty tree they diverge, with the `git show` form returning the hash of the *unmodified* file. Fixed in `.git/hooks/pre-push` and its staged copy (`file_hash` now hashes the path), and in all four command files. `batch.py check_signals` already hashed the file on disk, so all three components now agree. **CRLF is not a hazard here:** `.gitattributes` declares `* text=auto eol=lf`, which overrides `core.autocrlf`, so working files are LF on every clone. ⚠ Hooks live in `.git/` and are **not** version-controlled — re-install from `tools/verify/proposed_pre_push_hook.sh` per clone or this fix is absent.

## Adversary Review Gate — Hard Rule

**Any public-facing action requires adversary review to have completed before execution.** This is non-negotiable and applies to every action that puts content in front of an external reader:

- `git push` containing changes to prose in any tracked file (Lean source docstrings, build script `body()` calls, README.md, GUIDE.md, any companion script)
- Sending an email to any external party
- Posting or editing a GitHub Discussion body or follow-up comment
- Posting or editing a GitHub Issue
- Any other action that surfaces content outside this repository

**The protocol:**
1. Before executing any of the above, Claude must explicitly ask: "Adversary review complete for this content?"
2. Wait for Tim's confirmation before proceeding — do not self-assess whether review is needed
3. If review has not been run, offer to run `/adversary-review` on the relevant content first
4. The agent RECORDS ITS OWN VERDICT, FAIL and PASS alike (`record.py --step adversary --how delegated`). **STOP-ORDINARY is the one exception:** a PROCEED verdict that is not a pass, so it goes to the caller, who decides what reaches the ledger and carries the findings as `outstanding`.
5. Only after explicit confirmation may the public-facing action execute

Same-session self-review does not satisfy this requirement. The review must be a separate adversarial context (spawned Agent with no conversation history).

**What triggered this rule:** Lean docstring and build script prose changes were pushed on 2026-05-20 before adversary review ran. The review subsequently found two additional precision errors in the already-committed content.

⚠ **NO "MINOR FIX" EXCEPTION.** The gate applies to ALL `body()` changes — rendering fixes, character
substitutions, glyph corrections. The mathematical significance of the change is irrelevant; if a
`body()` call changed, adversary review is required. **Violated twice in one session (2026-05-24):**
the initial ZP-L push, and a CNF glyph fix pushed without review. The glyph fix introduced a
precision error — *"a positive natural number less than ω"* is redundant — plus a missing p-adic
convention note, caught only by a retroactive review. A change too small to review is still a change
to a published surface.

---

## Running the gates: the calibration a brief written from memory cannot carry

*Migrated from private memories, 2026-08-28. `CLAUDE.md` R-BRIEF: "Memory BODIES never arrive at all
— only the index." Everything below was recorded only in that invisible copy, which for material
about how to SPAWN a reviewer is the worst possible place for it.*

### Run gates FROM THE COMMAND FILES. Three separate agents. Never a hand-written brief.

Tim, 2026-08-06, on finding it had not been happening: *"you need to be doing the reviews using our
standard agents. that's a substantial f****** if that hasn't been happening."*

**The failure:** across an entire session every gate was run as ONE `general-purpose` agent with a
brief written from memory, and `.claude/commands/` was never opened. Five pushes went out that way.

1. **READ the command file** — `adversary-review.md`, `editorial-review.md`, `prior-art-review.md`
   (also `claim-review.md`, `experiment-review.md`, `tag-review.md` where they apply).
2. **Pass its brief VERBATIM** to a spawned agent. The file's own first line says *"Do not run this
   review inline. Use the Agent tool to spawn a fresh instance… Pass the prompt below verbatim."*
   **The `.md` is an instruction TO THE CALLER, not a doc to skim.**
3. **THREE SEPARATE AGENTS, one per gate.** Not one agent wearing three hats.
4. The caller bumps `gate_round.py` **once** per round and puts N in each brief; reviewers only `show`.

**Why, measured the same session — independence is the product, not ceremony.** The prior-art gate
found a published prior-art hit the adversary gate missed; the adversary gate found a vacuous theorem
prior-art missed; Tim found two things all of them missed. Collapsing three contexts into one
silently removes most of that. Separately, those command files hold **~580 lines of calibration**
accumulated from specific past failures — a brief written from memory loses all of it **and cannot
know what it lost.**

⚠ **AND IT CORRUPTS A PERMISSION.** Standing permission to push on green gates is licensed by *the
gates* passing. A consolidated review is not the gates, so pushing on it spends a permission never
granted for it. If the mechanism ever deviates, **say so before pushing** — the deviation is the
thing to surface, not the verdict.

**Tell:** if a gate brief is being composed in the message rather than read from a file, it is wrong.

### ⭐⭐ THE CARRIER MODEL — orchestration, worktrees as the RETURN CHANNEL, and why the gates parallelise

*Recorded 2026-09-12. Tim: **"your job should be orchestration much more than anything else for a
review like this"**, and — on the flow below being restated independently — **"this is the exact flow
that we've been trying to migrate towards for a while."** It lived in nobody's documentation until
then, which is the same defect the preamble to this section describes.*

**You are the CARRIER (`D3`), not the author.** `.claude/commands/copy-editor.md` already names the
role: *"You move work between agents and you write no content here."* The panel judges; you union,
you tally, you escalate.

⛔⛔ **AND ON A BEDROCK FINDING THE REVIEWER WRITES THE FIX — NOT YOU.** `adversary-review.md` settled
this on 2026-09-08 and states the cost: *"Do not apply the reviewer's findings by hand. That was the
standing practice until 2026-09-08 and it is the measured cause of this gate's non-convergence: across
three rounds in one day, **every hand-applied fix wrote the next round's bedrock finding**, because the
carrier was reconstructing someone else's intent from a note."* **The reviewer returns a worktree PATH
and a SHA; the carrier merges it.** ⚠ Remediation is the ADVERSARY's, in its own worktree — the
prior-art scout does not author fixes either (*"`D1` gives remediation to the ADVERSARY… You return
findings and filed sources"*). So a prior-art FAIL-BEDROCK routes: scout reports → carrier spawns an
adversary to author the fix in its own worktree → carrier merges the SHA → re-run the gate.

⚠⚠ **VIOLATED 2026-09-12, four days after it was written, and the near-miss is the lesson.** A
prior-art round returned FAIL-BEDROCK on `Algebra/Wheel.lean`; the carrier authored the fix by hand
from the reviewer's note, graded the severities itself, and carried the findings to Tim as prose.
Round 2 happened to PASS, so nothing bad landed — **which is exactly how a retired practice survives
retirement.** `R-LOOPCAP`'s cost line (*three of the last four bedrock findings were introduced by the
previous round's fix*) is the SAME measurement, and `D1`/`D3` is its fix. Quoting the cost while
skipping the remedy is the shape to watch for.

#### The `D`-scheme, and ⚠ it is defined NOWHERE as a set

Cited across **7 command files** (`adversary-review`, `copy-editor`, `editorial-review`,
`claim-review`, `prior-art-review`, `reconstruct`, `rely`) with in-situ glosses only; `pipeline.md`
mentions `D1` once in passing. **There is no definition list**, so a reader meeting `D5` mid-brief
cannot look it up. Assembled 2026-09-12 from the citations themselves — a dated survey, not a
completeness claim:

| id | stated as | stated in |
|---|---|---|
| `D1` | the REVIEWER (adversary) writes the fix, in its own worktree | `adversary-review.md`, `prior-art-review.md` |
| `D3` | the CARRIER moves work and authors nothing; risk is transport WITHOUT transformation | `copy-editor.md`, `adversary-review.md` |
| `D4` | escalation goes to the carrier, who carries it to the author; gates never report to the author directly | `copy-editor.md`, `adversary-review.md` |
| `D5` | the bedrock-clean state is a STATE, not a run — do not re-run to "confirm" it | `copy-editor.md` |
| `D6` | editorial gets its own branch, cut from that state | `copy-editor.md` |
| `D8` | the prior-art references that will be PUBLISHED (the expensive half) | `copy-editor.md` |
| `D9` | three copy editors, 2-of-3 to proceed | `copy-editor.md` |
| `D10` | findings UNION, only the verdict is VOTED | `copy-editor.md`, `adversary-review.md` |

⛔ **`D2` and `D7` were NOT LOCATED** — searched 2026-09-12 across `.claude/commands/*.md` and
`tools/process/`; `D7` appears once as a bare citation (`adversary-review.md`, beside `D4`) with no
gloss anywhere, and `D2` returns nothing at all. Do not invent them. Whoever knows the scheme owes
either the two rows or a correction to the citations.

⛔ **`D3`'s RISK IS TRANSPORT WITHOUT TRANSFORMATION.** *"Hand over the worktree and the diff, never a
summary of them… A carrier that paraphrases has rebuilt the translation step `D1` and `D3` exist to
delete."* Measured twice in one day: a claim gained confidence and changed units at each hop between
two agents while both cited their sources correctly. ⚠ **And measured again 2026-09-12 in the
caller**: two prior-art rounds were paraphrased to Tim in prose, their severities re-graded by the
carrier, and every fix authored by the carrier. All three of those are the author's job or the gate's.

#### The topology

    carrier ──worktree(action='add')──▶  wt₁ … wtₙ    each agent, in its OWN tree:
                                                       read · correct · build · run its gate ·
                                                       record its own verdict · COMMIT
            ◀────── commit SHA ───────   the return channel
            ──merge(branch=<sha>)──▶     fan-in, --no-ff, gated like any commit

**The worktree is a DATA CHANNEL, not a fence.** Write isolation is a side effect (Tim, 2026-09-12:
*"You are wrong about write contention. That's a side effect"*). What it is FOR is giving an agent a
place to do complete work and hand back a commit-ish. `merge` takes any commit-ish despite the
parameter being called `branch`; a worktree from `add` is DETACHED and has no branch name, so the SHA
is the handle.

#### Why the gates can run simultaneously — and why the fan-in does not destroy their verdicts

Two facts, both read from source rather than assumed, and they are what make this composable:

1. **A basis is a TREE.** `common.ledger_basis(INDEX)` runs `git write-tree` with `cwd` set to the
   repo it is invoked in, and `V11` keys a record `(step, basis, revision)`. ⚠ **So the question is
   not where the agent stands, it is what its index HOLDS.** Sibling worktrees sitting at the same
   commit share a tree and would collide; sibling worktrees that have each done their work and
   committed have **different trees, hence different bases, hence no collision.** The trees are
   honestly different rather than artificially separated, which is why this is not `ARC-1d`.
   ⛔ **The reasoning trap, committed 2026-09-12 and corrected by Tim:** reasoning about the worktree
   at CREATION time, when its tree is identical to HEAD, and concluding parallel gates must collide.
   A worktree is a workspace whose tree diverges; the basis is computed at RECORD time.
2. **A verdict binds `(step, path, git_blob_id)` — content, never position.** gitRobot states it:
   *"recording from a worktree is SUPPORTED and correct… where the agent stood when it looked is not
   part of the claim."* So the blob an agent's fix produced is the blob its verdict names, the merge
   carries that blob into trunk unchanged, and **the verdict still resolves after fan-in.**
   Content-keying is not merely an audit nicety — it is the property that makes parallel gate
   execution safe to merge at all.

#### The tally rules, which generalise from the panel to the fleet

- **Findings UNION. Only the VERDICT is voted** (`D10`). A lone reader who catches a meaning shift
  must not be outvoted; majority decides *"may this proceed"*, never *"did anyone find something"*.
- **DO NOT bump `gate_round.py` for parallel readers.** The counter counts LOOP iterations. `R-LOOPCAP`
  bounds SEQUENTIAL iteration because each fix writes the next round's defect; **parallel readers fix
  nothing and build on nothing, so there is no compounding to bound.** One worktree = one arc = one
  counter (Tim, 2026-09-02).
- Escalation goes to the CARRIER, who carries it to the author. Gates never report to the author
  directly.

#### ⚠ UNVERIFIED — settle with ONE worktree before running a fleet

Neither of these was executed as of 2026-09-12; both are reasoned, and reasoning is what the item
above got wrong.

- **That N parallel worktree gate runs genuinely do not collide.** The argument is sound and untested.
- **Where an agent's FINDINGS NOTE lands.** `.claude-local/` is gitignored and sits beside the MAIN
  checkout, so a worktree gets its own — `PUB-1` records the state writers dying with
  `FileNotFoundError` in a private-folder-free worktree until `write_text_lf` was taught to create the
  parent. A note written to `.claude-local/notes/` from inside a worktree therefore lands somewhere
  nothing commits. **The tracked return channel (the commit) is solid; the findings channel is not
  established.** Prove the loop once — one file, review-and-fix, own verdict, SHA returned, merged —
  before paying for it N times.

### Report which reviews are running, and their parameters

Name them as they launch, not only when verdicts return. Per review: the **command file** it came
from, that it is a **fresh isolated agent**, its **scope**, its **mode/arguments**, the **gate round
and cap**, the **verdicts it may return**, **what it is told to attack** this round, and any **source
material** attached.

**Why** (Tim, 2026-08-10, after several rounds that produced only an agent name and later a verdict):
a review is interpretable only if you know what it was pointed at. *"/rely passed"* means nothing
without its scope, and **a gate that ran on the wrong scope looks identical to one that ran on the
right scope and found nothing.** `batch.py prepush` now prints the same manifest, so the two agree
and neither depends on memory.

### Attach the SOURCE to any gate that will judge a citation

Include the actual pages or excerpts in the prompt. Do not rely on a summary.

**Why:** in the 2026-05-26 ZPJ docstring review the adversary reviewer found three real issues and
**hallucinated a fourth** — it claimed "ch. 1" was the wrong citation for AFA uniqueness, asserting
the formal statement appears in Chapter 3. It had been given the key quote and still constructed a
false account of the chapter structure. The reviewer's training data holds many plausible-sounding
descriptions of Aczel 1988; given a description, it compares against that prior instead of the quote.
**Primary source text in the prompt overrides that prior.**

⭐ **APPLIES TO PRIOR-ART REVIEW TOO (2026-07-19), and this is the sharpest form of it.** A prior-art
review was spawned on content citing Buchholz–Cichon–Weiermann *without* the paper attached. The
scout reached only metadata and correctly reported the claim as abstract-verified-only — and could
not tell it was in fact **false** (their norm is a finite-fibre condition, not a coefficient count).
**A gate without the source can flag "unverified"; it can never flag "wrong."**

**Tooling note from that incident:** two independent agents concluded the PDF had no text layer —
`WebFetch`'s converter called it a fax scan, and the scout hit the same wall. It was byte-identical
to a copy `pypdf` read in one call. **Do not record a fetch tool's failure as a fact about the
source** (this is R-NOTINLIB one layer over). Try `pypdf`/`pdfminer` before concluding a paper is
unreadable.

### `<details>` blocks are exempt from adversary kill recommendations

The adversary persona is a cold reader doing five-second triage, and **that persona never opens a
`<details>` block.** So collapsed content in a GitHub Discussion can freely carry internal ZP
notation, Lean encoding detail, supporting calculations and cross-references. When a review flags one
for cutting, treat it as a no-fix — confirmed by Tim on the ZP-C review, 2026-05-20, which
recommended cutting the block holding JSD = log 2 and the Lean encoding notes.

### Outreach ordering

After any substantive edit to outreach copy, the adversary gate runs **in the same session, before**
a test send is offered — not after. Measured failure: in a May 2026 session the review was skipped
until Tim asked for it, by which point the test email had already gone out. Draft → review → apply
fixes → *then* offer the send.

⚠ **STALE MECHANISM, RECORDED SO NOBODY GOES LOOKING.** An earlier version of this gate ran through a
`check_push_ar.ps1` `PreToolUse` hook plus a `.claude-local/ar_clearance.lock` file carrying the HEAD
hash. **Both are retired** — the prose signal files went in 2026-08-24 (see above) and direct `git`
is denied to agents entirely, so the push it hooked cannot be typed. The protocol above is the live
one.

---

## Cold review after every Lean cycle, and CONTEXT HYGIENE for the agent you spawn

*Migrated from private memories, 2026-08-28.*

**The cadence (Tim, 2026-06-29):** each completed Lean cycle gets a fresh deflation-first cold
reviewer **before it is called a result**. Set after two same-session deflations — the
"inversion = opposite" keystone came back LARGELY PROSE, and the verb-transport test came back
THIN-BUT-HONEST with an overstatement that had to be corrected.

**Why a build is not evidence:** a build succeeding means it type-checks. It does **not** mean the
theorem carries the content the docstring claims. **The warm, invested pass cannot tell its own
insight from its own confabulation — fluency and validity feel identical from the inside.** Only
externalising separates them, and the cold pass has caught the inflation every time.

Verdict scale: SOLID / THIN-BUT-HONEST / LARGELY PROSE (or GENUINE TRANSPORT /
DEFINITIONAL-OR-OVERCLAIMED at an edge). Act on the verdict before moving on.

### Context hygiene — the falsifier's entire value is COLD INDEPENDENCE

Tim, 2026-06-26: *"validate you're not including a bunch of extra context, just the papers and what
we're attempting to validate, so we're not risking polluting the falsifier."*

**SEND:** the neutral claim or plan under test; the PRIMARY SOURCES the agent reads itself; a neutral
checklist.

**SCRUB — anything that steers the verdict:** your own conclusions or expected answer; **the
framework's self-justifying language** ("the project's own convention says this is fine"); a prior
note's conclusions; "what I think the answer is."

**BACKGROUND IS FOR YOU, NOT THE FALSIFIER.** A note that LOCATES a source is gold for finding and
attaching the PDF — but its CONCLUSIONS stay out of the prompt. Attach Aczel; leave the note's
"DC-free / carefully scoped" verdict behind and let the agent read the source and judge.

**Provenance exception:** a fact verified by a PRIOR INDEPENDENT pass may be forwarded for efficiency,
labelled as such — but prefer letting each agent re-derive. Add to every falsifier prompt: *"reach
your verdict only from the primary sources; treat any framing here as the QUESTION, not the answer."*

**The logged slip:** AUDIT 02 (2026-06-26) forwarded *"the project's own convention states this
fence"* to the verdict agent. It did not change the PASS, but it was a process leak. This is the
complement of attaching sources: **attach the source TEXT, never the project's gloss on it.**

### Do not gate per-edit while a document is being polished

While Tim is iterating on a single document, make the local edits and hold. Each gate cycle spawns two
fresh agents (~120k tokens combined); running that after every small edit burns the billable window —
flagged 2026-07-14: *"you are burning through my token budget unnecessarily."* **Batch the gates and
one commit at the DOCUMENT BOUNDARY** — when Tim says the document is done, or when he switches
documents (at a switch, ask whether to gate and commit the finished one first). The hard gate rules
still apply to the eventual push; they run once before that batched commit, not per edit.
