# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

**Gate exemption — this file and operational meta.** `CLAUDE.md` itself (and other internal operating-instruction / meta files, as opposed to the mathematical publication content) is **exempt from the Editorial Review Gate and the Adversary Review Gate** below. The review gates are scoped to externally-facing publication prose — formal documents, companions, README.md/GUIDE.md, build-script prose. `CLAUDE.md` is the operating manual, not publication content, so it needs **version control only**: commit and push normally, and use `git push --no-verify` if the pre-push hook blocks on a stale review signal for a `CLAUDE.md`-only change.

**The exemption covers the VERIFICATION CODE (2026-08-15).** `tools/verify/**` is operating
machinery on the same argument: a checker makes no claim about the mathematics, so there is nothing
for an editorial or adversary gate to review. **`/rely` reviews that layer instead, and it BLOCKS** —
the two are a pair, so weakening the routing re-opens this exemption as a hole.

**AND IT COVERS `tools/process/**` — DECLARED, NOT DERIVED (2026-08-20).** That directory is **this
file's body**: `CLAUDE.md` is a routing table (a condition, the exact file to open, the cost of
skipping) and `tools/process/` holds what the routing points at. Same argument, same price —
operating instructions asserting nothing about the mathematics, so editorial and adversary have no
claim to review, and **`/rely` covers it and BLOCKS.** The carve is written here **because the
paragraph below forbids inferring it**; do not extend it to a further directory by analogy — write
the next one down too, or it is not exempt. **Fence: anything asserting mathematics belongs in the
corpus and is gated normally.** Criterion for what may live there, and the two sections that
deliberately may not: `tools/process/README.md`.

⚠ **IT DOES NOT COVER `.claude/commands/`, AND THE DISTINCTION IS THE POINT.** The gate briefs are
now published deliberately, as the artifact showing how this project reviews itself, so they are
**publication content and both gates fire on them** — `VERIFICATION_BUILDOUT.md` Phase 7 lists "the
gate command files" under publishing the method and calls the review non-discretionary. `CLAUDE.md`
is exempt because it is an internal manual that happens to live in a public repo; a gate brief is
being surfaced *on purpose*. **Published-and-exempt is not a category you may reason your way into
from "it is operating instructions" — CLAUDE.md is the exception, not the rule.** Same for
`DEFECT_CLASSES.md`, `vocabulary_reference.md` and the protocols, which is why those stayed private
when the code went public.

## ⭐⭐ DIRECT `git` AND `gh` ARE BLOCKED FOR AGENTS. USE `gitRobot`. (2026-08-22.)

**TRIGGER — an action, so there is nothing to adjudicate: you are about to type `git` or `gh`.** A
`PreToolUse` hook inspects the **whole command string** for a word-boundary `git` or `gh` and denies
it — bare, `cd`-chained, `&&`-chained, `git -C`, absolute `git.exe`, shelled out of Python. It
**fails closed**: empty or unparseable input denies.

**Why, measured the day it landed:** `illustrated` had **no branch protection at all**, `main`
required **zero status checks**, `.claude/settings.json` was `Bash(*)`/`PowerShell(*)` with no deny
rules, there are **two recorded bypass incidents**, and `reset --hard` / `checkout -- .` / `clean` /
`stash` **fire no hook at all** — which is how the most expensive incident here destroyed an
uncommitted edit and then correctly reported success.

| you want | use |
|---|---|
| status, unpushed count, **what would block a push** | `status()` — one call, more than `git status` + `git log ..HEAD` gave |
| any read — `log` `diff` `show` `ls-files` `rev-parse` `blame` `cat-file` | `read(op=..., args=[...])` — tier 3, no gate, no audit, always available |
| stage | `stage(paths=[...])` — **named paths only**; `-A` is refused on the main repo and permitted for `.claude-local` |
| commit | `commit(message_file=...)` — message from a FILE, never argv; runs `precommit` first |
| push | `preflight()` → poll `preflight_status()` → `push(branch, reason)` |
| sync before work | `fetch()` then `merge(branch, reason)` |
| a private checkout to mutate in | `worktree(action='add')` → path; `'remove'` tears it down |
| move HEAD, drop a branch, untrack a file, tag | `switch` · `branch_delete` (safe only) · `remove_files` (named, no `-f`) · `tag_create` (no deletion verb) |
| why was I refused | `explain(refusal_id)` · `history(limit)` for the audit log |
| a **release** | **Tim.** Releases mint permanent DOIs; that is not an agent decision |

⚠ **DO NOT WORK AROUND IT** — no aliases, no wrapper scripts, no shelling out from Python. If you
believe you genuinely need direct git, **say so and let Tim decide**.

⚠ **THE MATCHER SEES ARGUMENTS, NOT JUST COMMANDS.** A path containing the standalone token blocks
the whole command — a file named `...-direct-git-migration.md` cannot be passed to *any* shell
command, **including the one that would rename it**; the only escape is a glob avoiding the literal.
**Never put a bare `git` in a filename.** (Measured 2026-08-22, on a file this project created that
same day.)

⚠ **TOOLS THAT USE GIT INTERNALLY ARE UNAFFECTED.** The hook intercepts **agent tool calls**, not
subprocesses spawned by a Python process. `batch.py`, `hooks.py`, all 21 checkers that shell git,
`check_frozen.py`'s upstream-ref basis and every build script keep working untouched. **Do not
"migrate" them** — there is nothing wrong with them, and rewriting them onto an MCP server the
pipeline cannot depend on would break the gates.

⚠ **`gitRobot` IS LAYER 2 OF 3, AND LAYER 3 DOES NOT EXIST.** Local enforcement raises friction
against drift; it cannot bind an actor who controls the machine. **The only sound layer is remote
branch protection with required status checks, and it is still not configured.** Do not read this
section as the hole being closed.

📖 **What is denied, why, and what would REOPEN each item — `.claude-local/notes/access_controls_2026-08-22.md`.**
Several are provisional. **The server's own definition, including the tier model and the
absent-by-design parameters, is `C:\temp\gitRobot.md`.**

## ⭐⭐ WHERE THINGS LIVE. Three tiers, and the boundary is PUBLISHABILITY, not convenience. (2026-08-15.)

| tier | what | tracked? |
|---|---|---|
| **`tools/verify/`** | every checker, the pipeline (`batch.py`, `hooks.py`, `guards.py`, `report.py`, `vendored.py`), the **baselines**, the hook sources + `install_hooks.py` | **yes — public** |
| **`scripts/`** | every PDF build script, `zp_utils.py`, `scan_pdfs.py`, `PDF_Rendering_Standards.md` | **yes — public** |
| **`tools/process/`** | `CLAUDE.md`'s body — the argument behind each routed rule | **yes — public** |
| **`.claude/commands/`** | the review-gate definitions Claude Code reads | **yes — public** |
| **`.claude-local/`** | signals (`*_cleared.txt`), `gate.lock`, `batch_state.json`, `gate_round.json`, `DEFECTS.md`, `notes/`, `feedback/`, `outreach/`, `papers/` | **not tracked by THIS repo — it is its OWN repository**, with its own history, a `master` branch and a private remote (`ZeroParadoxLocal`). The parent additionally ignores the path |

**The line: artifacts of VERIFICATION are public; artifacts of PROCESS-IN-FLIGHT are private.**
A checker and its baseline are reproducible from the public corpus, so withholding them protected
nothing and only made the claims unauditable. A signal recording what this session reviewed is
per-push state that churns on every commit.

⚠ **THERE ARE NO MIRRORS ANY MORE, AND RE-CREATING ONE IS A DEFECT.** Three existed and **two had
silently drifted**: the build scripts, duplicated between `scripts/` and the private folder
(`scan_pdfs.py`, adrift three months), and the gate definitions, which existed in the user-level
Claude directory *and* as a private backup copy — 4 of the 8 had diverged. If something must exist in
two places, that is the signal to change the layout — **not** to add a copy step and a rule asking
someone to remember it. Every old path now holds a tombstone that **exits 2**, and
`python tools/verify/check_moved.py --block` fails if anything still points at a relocated path.

⚠ **A tool NEVER writes its own invocation path down.** Each derives `SELF` from `__file__` and
prints that, so usage text cannot go stale — a hardcoded `python <dir>/tool.py` in a docstring is a
COPY of the path and drifts exactly like a mirrored file. Baselines resolve relative to the checker
for the same reason, so they travel with it. **This file is the one place a literal path is
correct**, because a human reads it and nothing computes on their behalf.

⚠⚠ **NEVER PUT A NON-COMMAND `.md` FILE IN `.claude/commands/`.** Claude Code registers **every**
`.md` in that directory as a slash command, so a `README.md` there silently creates `/readme`. The
directory is an interface, not a folder — anything explaining it goes here instead. (Tim, 2026-08-15,
catching exactly that proposal.)

**What a public reader should know about the published gate briefs, since they cannot follow all of
it:** the 11 files in `.claude/commands/` are the real briefs, run verbatim, and the published
surface as a whole references a substantial number of artifacts inside `.claude-local/` —
measure it rather than quoting a figure; an earlier count here said 66 and an adversary pass
measured considerably more across the wider surface — the notes, the defect ledger, the papers library, the DeepSeek
screening scripts, and the per-push signal files. Those are deliberately private (see § *Private
Working Folder*), so a reader can see exactly what each gate is instructed to do and cannot open
every artifact it names. That is the honest position and it should be stated rather than discovered:
**the method is public; some of the material it operates on is not.**

## NARRATE THE MATH — in an engineer's register, every report. (Tim, 2026-08-12.)

> *"for future iterations I want you to narrate the math for me. and do it in terms fitting to an
> engineer that's not a mathematician by trade."*

**Every report touching mathematical content carries a plain-language pass on the MATHEMATICS, beside
the process summary — not instead of it, and not only when asked.** Long verification arcs drift into
reporting gate verdicts, defect ids, signal freshness and exit codes. That is scaffolding. *"The
prior-art gate verified AMM Thm 7.2 p. 27"* says a check passed; it does not say what the theorem
**states** or why its direction was load-bearing.

**Tim is this project's mathematician of record by decision, not by training. He cannot review what is
never explained, and his review is the control that has repeatedly caught what the gates did not.**

- **Use systems and programming analogies** — recursion and termination, type signatures,
  preconditions, interface vs implementation, invariants, null vs empty, cycles in a graph. Name the
  object before using its symbol.
- **Spell glyphs out in words at least once per paragraph** (bottom, epsilon-zero, infinity) — the
  standing mobile-readability rule.
- **Standard mathematical term first, ZP shorthand after.** Narration is never licence to lead with
  framework vocabulary; the § on language ordering still governs.
- **State which direction an implication runs, and why that matters.** The 2026-08-12 arc turned
  entirely on sufficiency versus necessity in a cited theorem, and *"the biconditional overstates the
  source"* is precisely the phrasing that hides the point from anyone not already holding it.
- **Do not soften the claim.** Precision is the deliverable; only the register changes. If a
  distinction is load-bearing, explain it rather than dropping it.

⚠ **This governs REPORTS TO Tim, not the corpus.** It is not licence to add prose to `.lean` files —
the prose cap, the `Statement:`/`Reading:` labels and *"anything convertible to Lean MUST be
converted"* are untouched. If narration reveals that a claim is only expressible in prose, that is a
finding about the claim, not a reason to write an essay into the source.

## ⭐⭐ `batch.py precommit` BEFORE EVERY COMMIT. `/batch` for any multi-site work. Not optional.

**The orchestrator is the default entry point, not a special mode.** `tools/verify/batch.py` owns
sequencing and mechanical preconditions; an agent owns judgement. It decides nothing — it refuses to
let a commit or push happen while a decidable obligation is unmet.

```
python tools/verify/batch.py precommit    # BEFORE EVERY COMMIT. Works with or without a batch.
python tools/verify/batch.py prepush      # before any push: which reviews are required, and are
                                           # the signals FRESH (hash + coverage, not existence)
```

**`precommit` runs the UNIVERSAL obligations on every commit** — build green, a `#print axioms` entry
for every added declaration, an `ssot.json` row for every added declaration, all checkers at zero new.
Those are the four things this project forgets most; each was forgotten again on 2026-08-09 with all
four rules known and written down.

**⭐⭐ DO NOT LOOK UP WHAT BLOCKS WHERE — THE PIPELINE ANNOUNCES ITSELF AT EVERY ENTRY POINT.** Before
any check runs, all four entry points print a manifest: what is about to run, in what order, which
checks BLOCK and which only warn, what scope, what is exempt, and what is deliberately NOT run.
`prepush` additionally prints **the recorded verdict line from each review signal**, so *"cleared"*
is never read as *"clean"*. **Run it; never maintain a prose copy of its answer** — one formatter
(`report.py`), so the four cannot drift.

⚠ **The purity/SSOT check is driven by an ON-DISK BASELINE (`tools/verify/decl_baseline.txt`), never
by git.** Computed against `HEAD` it is meaningful only *before* the commit, and run afterwards both
checks passed **vacuously**. A **stale baseline is safe** — it can only make more declarations look
new, so the check gets stricter, never blind. Re-seed:
`python tools/verify/batch.py decls --baseline`. Vendored backports are exempt structurally.

**⚠ ALL pipeline logic is `tools/verify/hooks.py`; the hooks are three-line shims. Edit `hooks.py`,
and the shim must never grow.** Two partial implementations measurably disagreed three ways while
checking disjoint things — that is what this replaced.

**Use `/batch <bucket>` for anything MULTI-SITE** — a debaselining bucket, a defect-class sweep, a
file-sized burn-down. It adds stage ordering (`ledger` → `screen` → `probe` → `judge`), a frozen
filter snapshot, and a recorded note per stage. **A single targeted fix with a named defect id does
not need a batch**; `precommit` alone covers it.

⚠ **Filters are frozen at `batch start`.** Editing a checker mid-batch means the work was done
against a moving target; the batch is invalid and must restart. Route filter defects to `DEFECTS.md`
and fix them in their own batch. (Violated by the author of the rule on the day it was written —
`PRC-1`.)

⚠ **If a stage BLOCKS, fix the cause.** Do not delete `batch_state.json`, do not `--no-verify`, do
not push a subset to dodge a signal. **This project has two recorded bypass incidents and both began
by treating a block as an obstacle.**

📖 **WHY THE PIPELINE IS SHAPED THIS WAY — `tools/process/pipeline.md`.** Which obligation gates at
commit versus push and why `lake build` deliberately gates neither; the three defects that stayed
invisible for a month because a gate did not declare its own enforcement mode; and the `REL-1`
ordering lesson, where delegating before fixing would have replaced a correct computation with a
vacuous one. **Read it before changing `hooks.py`, `batch.py` or `report.py`, or before arguing a
gate is in the wrong place.**

## ⭐ The defect register — `.claude-local/DEFECT_CLASSES.md`. Consult it by DEFAULT.

**One row per defect CLASS, each with its DETECTOR.** `DEFECTS.md` is open instances; the register is
kinds, and the detector column is the part that transfers to a question nobody has asked yet.

**Three triggers, and they are obligations, not suggestions:**
1. **Writing a gate brief or spawning any reviewing agent** — name the **LAYER** attacked, the
   **STATE** tested, and the **DETECTOR by id**. *"Check the glosses"* is not a detector; *"DC-1: read
   the elaborated `#check`"* is. A gate that does not name its layer re-attacks the one the last gate
   already cleared.
2. **Something looks wrong and you are choosing how to check it** — find the class first. The register
   is indexed by what you have in hand (a suspicious sentence), not by what you are asking.
3. **A defect recurs** — add or amend a row, in the same change. A one-off is an instance and belongs
   in `DEFECTS.md`; the *second* occurrence is a class.

**The one-line summary of everything measured so far: PREFER A DETECTOR WHOSE VERB IS *RUN* OVER ONE
WHOSE VERB IS *READ*.** Across ~20 agent runs, every BEDROCK finding came from an agent **executing**
something and every ORDINARY finding from an agent **reading** something, with no exceptions.

⚠ **Six of seventeen rows have a mechanical checker; eleven do not.** Those eleven rely on someone
remembering, which this file elsewhere records as failing by construction. That is visible debt, not a
solved problem — and this register is the **seventh** convention of this shape, the previous six having
all leaked.

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

## ⭐⭐⭐ WHEN A FAILURE RECURS: the rule is wrong, not the reader. Run this list. (Tim, 2026-08-15.)

**THE PRINCIPLE, and everything below follows from it: a failure that recurs is evidence about the
RULE, never about whoever tripped it.** The response is to change the rule's SHAPE. It is never to try
harder, and it is never to add a second rule saying the same thing louder — this file records **seven**
conventions that leaked, and every one leaked while being remembered by people who had read it.

**THE LIST. Run it in order; stop when a step resolves.**

0. **⭐⭐ RE-READ THIS FILE FROM DISK. YOUR COPY IS A SNAPSHOT AND IT IS PROBABLY STALE.** (Tim,
   2026-08-15 — a cache invalidation on the one path where the cache is guaranteed to be wrong.)
   **The `CLAUDE.md` in your context was injected at session start. Any rule written LATER in that
   session — including the fix for the failure you are recovering from — is absent from it.** Measured
   the same day: a control agent was handed the exact failing task, and the section that reverses that
   task **was not in its context**; it found the rule **by accident**, through an unrelated grep that
   happened to return a `CLAUDE.md` line.
   - **THE TRIGGER, and it is an action so it cannot be adjudicated away:** you are told you are in a
     failure condition, or this is a retry, or a gate returned FAIL, or **someone refers to a rule you
     do not recognise** — that last one is the tell that your copy is stale.
   - **DO IT CHEAPLY FIRST.** `grep -n "^## " CLAUDE.md` costs ~1k tokens, lists every section title,
     and a rule added this session shows up immediately as a heading you have never seen. **Read only
     the sections that scan relevant.** A full re-read is ~55k tokens — check the manifest before
     loading the payload.
   - **⚠ THIS APPLIES TO THE MAIN INSTANCE TOO, not only subagents.** If you edited this file earlier
     in your own session, **your injected copy still does not contain your own edit.** You know it only
     because you wrote it, which is not the same as having it.
   - **⚠ CALLER-SIDE COMPLEMENT, and it is not optional:** if you edit this file mid-session, **carry
     the new rule into every subsequent brief verbatim.** Briefs are the only thing a spawned agent
     reliably reads, and until it re-reads from disk the brief is the sole delivery path.

1. **CHECK `DEFECTS.md` AND `DEFECT_CLASSES.md` FIRST.** If the class is already there, **a rule
   already exists and did not fire** — which is a different and more useful problem than a novel
   failure. Skipping this step is itself one of the recorded recurrences.
   - ⭐ **AND YOU DO NOT HAVE TO REMEMBER 60+ LEDGER ROWS TO SPOT A RECURRENCE — `tools/verify/selfheal.py`
     COUNTS THEM.** It reports *"this shape has happened N times and has no class row"* and suggests;
     it never corrects, because deciding whether N rows are one phenomenon or N coincidences is
     judgement and auto-filing would produce a register nobody verified. **`batch.py prepush` now
     prints the top uncovered shapes on every run, blocked or clear.** ⚠ It used to run only from
     `/ship` — the release command, i.e. the rarest action — and this file did not mention it at all,
     so the one decidable input to this whole list surfaced almost never. Measured 2026-08-18: a
     session made the same control-subject error **three times** (`DC-25`), closing each instance with
     a local comment and never lifting it to a class, while the counter that would have said *"three"*
     sat unrun. **Its counts are a READING LIST, not a finding list** — read the rows before acting on
     a number.
2. **DIAGNOSE THE TRIGGER, NOT THE CONTENT.** A rule that exists and did not fire almost never has a
   content problem. Ask: **is the trigger an ACTION, or a CATEGORY you must adjudicate?** A category
   leaks, because the adjudication is where it gets talked past. Ask also: **how deep in this file does
   it sit?** ⭐ **Measured 2026-08-15: line 127 fired reliably all day; line 2135 did not fire once.**
3. **FIX AT THE HIGHEST LEVERAGE AVAILABLE.** In descending order of reliability:
   - a **MECHANICAL check** — a gate, a hook, a checker. Fires whether or not anyone remembers. *Always
     prefer this.*
   - a **TRIGGER + NAMED FILE in this file** — the `CannotBe` pattern. Fires when someone reads. Needs
     all four properties: unmissable trigger, exact path, stated consequence, target worth opening.
   - a **NOTE.** Fires only if someone chooses to read it. **~10% of notes are ever referenced again** —
     treat this as recording, not fixing.
4. **CONTROL-TEST THE FIX.** ⭐ **Tim's addition, and it is what turned this protocol from a checklist
   into something that works.** Give a **fresh agent the exact failing task**, read-only, **without
   telling it the answer** — not the counts, not the finding, not that a prior attempt failed. **Fix
   the scorecard BEFORE the result comes back.** A fix you have not tested is a hypothesis.
5. **TEST DELIVERY SEPARATELY FROM CORRECTNESS.** ⚠ They fail independently and the second is invisible.
   Measured the same day: the fix was correct and **did not reach the agents it was written for** — a
   mid-session `CLAUDE.md` edit is absent from the context of agents spawned afterward. **Ask: did it
   arrive?** separately from *did it work?*
6. **RECORD ALL THREE — the class, the TRIGGER diagnosis, and the test result including how it was
   compromised.** A control that passed for the wrong reason is worth more written down than a clean
   pass, because the next person will otherwise trust it.

**⚠ THE ESCALATION LADDER — the count is the signal, and this file's own history is the calibration:**

| occurrence | what it is | where it goes |
|---|---|---|
| **1st** | an instance | `DEFECTS.md` |
| **2nd** | a **class** | `DEFECT_CLASSES.md`, with a **detector** |
| **3rd** | the rule's **TRIGGER** is wrong | fix the trigger — do not restate the rule |
| **4th+** | **discipline will not work here** | build the mechanical check; stop writing prose about it |
| **the CHECK then fails 3×, OR THE LOOP NEVER CONVERGES** | **the check's SHAPE is wrong, not its patterns** | see rung 5 below — widening it again is the failure repeating, and **the gate DOWNGRADES TO A WARNING** |

**⭐⭐ RUNG 5 — WHEN THE MECHANICAL CHECK ITSELF FAILS THREE TIMES, STOP WIDENING IT AND PUT AN LLM ON
THAT LAYER. (Tim, 2026-08-19.)** Rung 4 says build the checker; it never said what to do when the
checker keeps missing. The tell is unmistakable and it is not "more patterns are needed": **each fix
closes the holes its author thought of, and the next reader finds different ones.** Measured
2026-08-19 on `check_paths.py --claim`, which failed three times in one session — first on markdown
emphasis, then on HTML entities and escaped apostrophes, then on line-start markers where five of ten
were blind and the sixth was covered *by accident*. A `/rely` pass watched the second fix land and
reported that both of its routes were **still** blind in the new version.

**⭐⭐ NON-CONVERGENCE IS A SECOND, INDEPENDENT TRIGGER — AND IT FIRES THE DOWNGRADE. (Tim,
2026-08-21: *"anytime a loop fails to converge stop attempting to write a script and use AI fuzzy
logic instead — treat as a warning instead of a hard gate."*)** Rung 5 above triggers on a check that
**misses** three times. This triggers on a **LOOP that never settles**, which is a different
observation and was measured separately: four `/rely` rounds on `tools/verify/` ran **10 → 4 → 6 → 9**
findings and never quiesced, because each round reviewed code written in response to the last. On
2026-08-21 the same layer deadlocked outright — a one-line, mechanically-verified, zero-judgement fix
demanded by `check_figures` re-staled the `/rely` signature and blocked the push it was made to
unblock. **A loop whose own repairs land inside its own scope cannot terminate, and no amount of
further script will make it.**

**THE TWO MOVES, and the second is the new one:**
1. **STOP WRITING SCRIPT.** Put an LLM screen on the layer, subject to every fence below.
2. **DOWNGRADE THE GATE TO A WARNING.** It reports, it does not block. Enforcement moves to the
   human read, which is where the judgement already was.

**⚠ WHAT MAY BE DOWNGRADED, AND WHAT MAY NOT — this is the whole safety of the rule.** The unit is
still the defect class (§ below), so ask what the gate DOES:
- **An ENUMERATION gate — "have all sites been enumerated / do all hashes match / is everything
  covered".** Its failure mode is *incompleteness*, it can never prove itself done, and its own
  repairs re-arm it. **→ DOWNGRADE. It becomes a warning and a reading list.**
- **A FAIL-OPEN gate — one that catches bad work getting THROUGH.** A check that can be walked past, a
  signal that can be forged, an exemption anything can grant itself, a gate reporting success it has
  not earned. **→ NEVER DOWNGRADE, no matter how many rounds it takes.** Non-convergence in an
  enumeration is a fact about the enumeration; a fail-open is a fact about the work. `guards.py`, the
  bedrock cap, the quarantine check and the hook-armed check are all this kind.

**⚠⚠ SPLIT AT THE LEG, NEVER AT THE CHECK — the first draft of this rule got that wrong and the
error was silent.** A single check routinely has legs of both kinds. The `/rely` routing check is the
worked example: *"a routed `.md` changed since the signature"* is enumeration and downgrades, while
*"a checker's executable LOGIC changed since the signature"* guards against unreviewed weakening of
the verification layer and **must keep blocking**. Downgrading the check wholesale carries the second
across with the first.

**⚠⚠ AND ASK WHAT THE DOWNGRADE UN-PRICES. AN EXEMPTION BOUGHT WITH A BLOCK IS UNPAID THE MOMENT THAT
BLOCK BECOMES A WARNING.** ⭐ **LANDED 2026-08-21, AND THE PRICE IS NOW SPLIT THE SAME WAY THE LEGS
ARE.** `tools/verify/**` and `tools/process/**` skip editorial and adversary, and what pays for that
depends on WHAT changed:

| what changed under the prefix | `/rely` routing | what pays for the exemption |
|---|---|---|
| **executable logic** (`.py`, hooks) | **BLOCKS** | `/rely` covers it and blocks. Unchanged. |
| **exemption switches** (baselines, whitelists, pins) | **BLOCKS** | as above — a fail-open surface, never downgradable |
| **routed prose** (`.md`) | **WARNS** | **no longer a block** — see the warrant below |

**The prose leg's warrant is now an ARGUMENT, not a gate, and it has to stand on its own.** It is
this: routed `.md` is operating instruction of the same kind as `CLAUDE.md`, which is exempt from
both prose gates **and routed nowhere at all, by design**. So advisory `/rely` coverage is strictly
*more* review than the parent file gets, not less. **The fence is what makes that hold — anything
asserting mathematics belongs in the corpus and is gated normally** (`tools/process/README.md` states
the criterion). If that fence ever slips, this warrant fails and the prose must go back to editorial
and adversary; that is the trigger to watch, and it is a content question, not a tooling one.

**⚠ THE MECHANICAL HALF IS BUILT AND CONTROLLED.** `guards.py` § *the router the exemption is priced
on still BLOCKS* walks five routes: the fail-open legs are declared blocking, `check_routing` emits
those flags, every consumer of it honours them, `routing_bad` computes correctly, and `cmd_prepush`
still calls it. Two probes in `.claude-local/tools_wip/` are its controls —
`probe_warrant_blocks.py` neuters enforcement three ways and requires `guards.py` to go red on each
(it does), and `probe_docs_only_clears.py` exercises both halves: a docs-only edit clears as a
warning, a checker edit still blocks.

**Why the guard had to exist first, in one line:** enforcement mode used to be a literal at one call
site (`bad += 0 if ran else 1`), so no control could read it — a probe measured `guards.py` printing
`ok` over a router that had stopped blocking, the **fifth** warrant-satisfied-while-empty in that same
code (rounds 1–4: sampling, narrowing, a three-probe set, unchecked regex flags). The warrant tested
COVERAGE and the exemption is priced on coverage **and** enforcement. The mode is now data
(`_LEG_BLOCKING`, `routing_bad`), which is the entire reason it is testable.

⚠ **The rule this instance satisfied, kept for the next one: before any downgrade lands, the guard
asserting what still BLOCKS lands with it — or the exemption it warrants is given up in the same
change.**

**⚠ NON-CONVERGENCE MUST BE MEASURED, NOT ASSERTED — or this rule becomes a licence to downgrade any
gate that is currently inconvenient.** Name the rounds and their finding counts, as the `10 → 4 → 6 →
9` above does. *"This keeps blocking"* is not evidence; it is usually the gate working. And this does
**not** touch § *If a stage BLOCKS, fix the cause* — downgrading a gate's declared enforcement mode,
deliberately and in writing, is a different act from `--no-verify`-ing past one that still blocks.
**This project has two recorded bypass incidents and neither would have been legitimised by this
paragraph.**

**⚠ AND A DOWNGRADED GATE MUST GET LOUDER, NOT QUIETER.** A warning nobody reads is strictly worse
than a block, because it manufactures the appearance of coverage — which is `RLY25-1` exactly: a
report publishing `pass` for a property it no longer checks. So a downgrade obliges the manifest to
say **WARN** at every entry point (`report.py` already formats this), and obliges the count to be
printed on every run, blocked or clear, the way `check_poles.py` prints its suppression count so
rubber-stamping shows up as a rising number instead of going quiet.

**⚠ THE DISCRIMINATOR — AND THE UNIT IS THE DEFECT CLASS, NEVER THE TOOL.** Both gates caught the
first draft on this: `--claim` is *itself mixed* — locating a phrase is enumeration, judging that the
located sentence misdescribes the section it cites is ground truth, and the second is what the fix
that triggered this rule actually turned on. Escalating "the tool" would carry the second across with
the first.

**THE TEST — name the ORACLE, not the failure type: does deciding ONE candidate site require opening
another artifact?**
- **NO — self-contained.** The sentence in front of you settles it. Formatting shapes, phrasing,
  fragments, "does this paragraph contradict the one above it". **→ AN LLM SCREEN IS THE RIGHT
  LAYER.** It reads the sentence and does not care whether the line began with `>`.
- **YES — you must go and read something else.** Does this citation say what we claim; does this
  locator resolve; what is this declaration's real footprint. **→ DO NOT ESCALATE.** `DC-17` measured
  it: 10/10 on the self-contained slice, **0/8** on the citation slice. Fix the tool, or hand it the
  source.
- **BOTH SURFACES AT ONCE — a THIRD category, and the first draft routed it wrongly.**
  Cross-surface consistency ("README under-names relative to CLAIMS") *reads* like enumeration and is
  not: deciding it means holding two artifacts simultaneously, and `DC-17` measured that context lines
  **hurt** here. **→ HUMAN OR GATE. Neither the checker nor the screen.**

**⚠⚠ THE SCREEN MAY REPLACE THE ENUMERATION. IT MAY NEVER REPLACE THE VERDICT.** `DC-17` measured
precision as *unstable* — 1, 4, 4, 3 false positives across four runs over the same twelve negatives —
and this file's own rule is that a false positive is the more expensive error, because it manufactures
work that looks urgent. So the screen widens the candidate set and a human or a gate adjudicates,
which is exactly what makes `fragment_screen.py` work. Two operational rules come with it, or it gets
run once and believed: **take sites flagged in ≥2 of 3 runs**, and **ignore self-reported confidence**
— `DC-17` measured `UNSURE` used **zero times** on the slice the screen got wrong.

**⚠ AND THE MISAPPLICATION FAILS SILENTLY, WHICH IS WHY THE FENCE MUST BE AN ARTIFACT.** Point a screen
at a ground-truth question and it does not refuse — it returns a confident PASS, because it accepts the
sentence's own label as its warrant. Prose cannot stop that, and prose is what this rung exists to stop
relying on. **Any screen must run `deepseek/pole_groundtruth.json` — the recorded slice it should get
wrong — and be disqualified mechanically when it scores well on it.** That is the `check_checkers.py`
move: the control is the deliverable.

⚠⚠ **AND RUNG 5 IS NOT "PREFER AN LLM".** Measured in the round that produced it: all three prose kills
came from *reading*, and the one finding neither gate's reading caught — a register fingerprint
attesting a hash that matched nothing — came from **running a two-line comparison**. No screen would
ever have caught it. **Where a mechanical check is possible at all, it still beats this rung.** Rung 5
is for where enumeration has been *demonstrated* unbounded, three times, not for where it is merely
tedious.

⚠ **The screen is a READING LIST, exactly as the mechanical version was** — it locates, a human or a
gate judges. And it is a SCREEN, not a replacement: keep the mechanical check for the shapes it does
catch, because it is free and it runs on every push. `.claude-local/deepseek/` is the existing bulk
tier (memory `feedback_llm_screen_for_grammar`, Tim 2026-08-02, where a whitespace rule corrupted 61
files and **the damage checker written to catch it had the identical bug**, so it certified the
damage). That memory has never bound anything, because memory bodies do not load — which is why the
rule is here.

**⚠⚠ DO NOT SKIP TO STEP 3 AND WRITE A NEW SECTION.** That is the reflex, it feels like progress, and it
is how this file grew past the point where its tail fires. A recurrence usually needs a **trigger
changed**, not a rule added.
If you are about to add a section, first find the one that already says it and ask why it did not fire.

## ⭐⭐ BEFORE YOU EDIT ANY `.lean` FILE: read `ZeroParadox/MANIFEST.md` AND grep the identifiers you are about to touch. Hard Rule. (Tim, 2026-08-15.)

**The trigger is an ACTION, not a category. If you are about to change a `.lean` file — one character, a
docstring, a comment — this fires.** No judgement call, nothing to classify, no exception for "it's only
prose".

1. **Read `ZeroParadox/MANIFEST.md`** — the by-folder index of the whole corpus, **~7k tokens**, cheaper
   than the Engineer's Takes and far cheaper than loading a folder. **104 `.lean` files already point at
   it**; until today this file mentioned it once.
2. **Grep the IDENTIFIER of every declaration you are touching**, not the wording of the claim. Then read
   the hits.

**⚠ WHY THIS EXISTS, AND IT IS A DIAGNOSIS RATHER THAN A RESOLUTION.** § *Development mode* below already
says to load the subsystem. **It did not fire on 2026-08-15 and the reason is its trigger:** *"before
fresh **mathematical development**"* is a **category that has to be adjudicated**, and the adjudication is
where it leaks — *"this is a docstring edit, not development"* is how the rule was talked past, in this
session, by someone who had read it. **Compare § *Core Objects* directly below, which binds reliably: its
trigger is an unmissable TOPIC and it NAMES THREE EXACT FILES.** A rule you must first decide applies is a
rule that does not.

**What it cost, measured the same day.** A `l_inf` docstring was rewritten after grepping three theorem
names. The wording survey found **4** citing sites; `grep -n "l_inf"` returns **9**. And the appended
paragraph re-committed an overclaim that had **already been made and corrected** — the correction sits on
`machine_trichotomy` (`ZeroParadox/Computability/Occurrence.lean` § II), which fences that the
function-vs-relation choice is not the ONLY encoding of the modality, in the very file the new text
cited and never opened. **FAIL-BEDROCK, reverted in
full.** Ledger: `PROC-2`, `OCC-2`.

⚠ **Searching the CLAIM is not the same as searching the NAME, and this file already says the first
half.** § *Review-Loop Cap* says *"grep the corpus for the CLAIM, not the named file"* — correct, and
**insufficient**: a paraphrase search misses every site that cites the identifier without repeating the
phrasing. **Do both. The identifier sweep is the mechanical one, so it is the one that cannot be talked
past.**

⚠⚠ **AND A RULE ADDED MID-SESSION DOES NOT REACH AGENTS SPAWNED LATER IN THAT SESSION.** Measured
2026-08-15, hours after this section was written: a read-only control agent was given the exact task
that had just failed. It performed the reconnaissance correctly and **reported that the `CLAUDE.md`
injected into its context did not contain this section** — its snapshot predates the edit. It found
the rule **by accident**, through an unrelated grep that happened to return a `CLAUDE.md` line. Had
its search been scoped to `ZeroParadox/` (this project's own stated convention for Lean searches) it
would never have seen it. **So an edit here binds FRESH sessions, which read this file from disk, and
silently does not bind the current one's subagents.** Two consequences: **carry a new rule into the
BRIEF explicitly** for the rest of the session in which it is written — briefs are the only thing a
spawned agent reliably reads — and **do not treat a same-session agent's compliance as evidence the
rule works**, because it may never have received it.

⚠ **This is the EIGHTH convention of this shape and the previous seven leaked**, which is the argument for
the narrow mechanical half over the broad remembered one. The durable fix is a tool that prints reverse
references at edit time (`refs.py`, wired into a `PreToolUse` hook and the `precommit` manifest) so it
fires whether or not anyone remembers — the `guards.py` pattern, where the registry is the deliverable and
the discipline is not. **Until that exists, this rule is remembered, and this file records that remembered
rules fail here by construction.**

## Core Objects — Read the Lean First (Hard Rule)

The framework has three core objects, each pinned by an authoritative Lean characterization. **Before writing ANY prose, figure, docstring, companion text, or claim about ⊥ (the bottom), the snap (⊥ → ε₀), or ε₀ — first READ that object's Lean source and ground every statement in a named theorem there.** Do NOT reconstruct these objects from working memory, from prose notes, or from this summary; the Lean is the ground truth. State the theorem, not a gloss. If this summary and the Lean ever appear to disagree, **the Lean wins — stop and ask Tim.**

**The three objects and their authoritative Lean files:**
- **⊥ (the bottom element)** — `ZeroParadox/BottomCannotBe.lean` (the `#check`-only "what ⊥ is / is not" index) + reader map `BOTTOMELEMENT.md`.
- **The snap (⊥ → ε₀)** — `ZeroParadox/Order/SnapCannotBe.lean` (the `#check`-only "what the snap is / is not" index) + home file `ZeroParadox/Order/Snap.lean` (T-SNAP, `t_snap_derived`) + reader map `SNAP.md`.
- **ε₀** — `ZeroParadox/Ordinal/Epsilon0CannotBe.lean` (the `#check`-only "what ε₀ is / is not" index) + `Epsilon0LeastFP.lean` / `Epsilon0MinMax.lean`.

The `CannotBe` indexes are `#check`-only — they create no declarations, so a line cannot point at a dead or renamed result; reading one shows what the object IS and IS NOT, each line a live theorem.

**⚠ The `#check` lines cannot overclaim. The `--` glosses beside them absolutely can, and have.** This file used to say the indexes "structurally cannot overclaim" full stop; that is true of the *declarations* and **false of the comments**, which are ordinary unverified prose sitting in a file whose stated premise is that it cannot overclaim. Measured 2026-07-26: two glosses in `DiagonalFixedPoint.lean` (`-- the Kleene quine IS ⊥`, a flat cross-type identity on a theorem stating `IsQuineAtom q → q = bot`) survived **four** adversary rounds inside that blind spot, and three more were found in `SnapCannotBe.lean`.

**The standing convention (Tim, 2026-07-26) — every gloss carries one of two labels, and there is no third option:**
- **`Statement:`** — an accurate restatement of what the declaration actually proves. Best form is an
  elaborating `example` (a wrong gloss then fails to compile); prose is acceptable where an `example`
  would be unwieldy, but it must be checkable by reading the statement.
- **`Reading:`** — the framework's interpretation, explicitly NOT a claim about what the theorem says.

**`Idiom:` (Tim, 2026-08-09) is NOT a third gloss label — the two-label rule above is untouched.** It
is for **running prose that NAMES a phenomenon** rather than describing any declaration: *"the 0=∞
inversion"*, *"the 0=∞ antipodality"*, *"the pole"*. A gloss says what a theorem proves or how the
framework reads it; an idiom is **vocabulary**, and neither existing label fits a handle. **The test
before applying it: does the sentence USE the equation, or does it NAME something?** *"the 0 = ∞
pole"* names. *"0 = ∞ under `rInv`"* asserts, and stays a defect no matter how it is labelled.

⚠ **It is a SUPPRESSION MECHANISM.** It sits in the source where a reader sees it, never in a
baseline file, and `check_poles.py` reports how many sites carry it on every run — so rubber-stamping
shows up as a rising number instead of going quiet. **Apply it only after verifying the site**; a
label applied in bulk is worth less than no label, because it launders the unread ones.

This is as much for a human reader as for a checker: the label tells you at a glance whether you are looking at mathematics or at interpretation. **The rule generalizes beyond the indexes** — the same defect class (prose asserting conjuncts the cited statement lacks) was found this session in ordinary docstrings, in `CLAIMS.md` rows, and in this file itself.

**Why the labels, and not another sweep.** Grepping for a claim's vocabulary cannot terminate — there is always another claim, and a sweep that greps `da1_closed_concrete` misses the site that says `da1_paths_unified`. Checking **witnesses against statements** is finite: bounded by the number of citations. `ZeroParadox/ClaimsMirror.lean` already proves the principle works — `claim_DA1` states the honest content precisely because it had to elaborate.

**The keystone index (the phenomenon the three objects share):** `ZeroParadox/DiagonalFixedPoint.lean` — the `#check`-only index routing every formalized face of **self-reference** (the diagonal fixed point) by the μ/ν fork: wall faces where self-reference cannot close (no fixed point — Cantor, Russell, Turing, Tarski, Curry) and floor faces where it closes and lands at ⊥ (the Quine atom, the Kleene quine, Löb/Gödel-2, Rice), all off Lawvere's engine. It is the direct route to self-reference the three object indexes point back toward. It states no new claim: the cross-face unification is Lawvere (1969) / Yanofsky (2003), cited prior art, and the cross-face identity across domains stays a **type boundary**, never a Lean `=`.

**The μ/ν fork and the HOST VERDICT — read before writing about the "one root or two" question, about
well-foundedness as a "second root," or about how many faces self-reference has. It is ALREADY BUILT — do
not build it again.** Authoritative sites, all pre-existing: `ZeroParadox/Settheory/LawvereBridge.lean` § V
("the whole μ/ν picture … one engine, two regimes, discriminated by the self-loop"), whose
`mu_nu_branch_exclusion` (`:124`) and `selfApp_lands_on_nu` (`:133`) are the theorems;
`ZeroParadox/Settheory/QuineHost.lean`, whose class is named for the host and already sorts three theories
by whether they permit the self-loop; `ZeroParadox/DiagonalFixedPoint.lean` § II/§ III, whose spine is the
wall/floor (μ/ν) carving; and the reframe section of `ZeroParadox/Settheory/Wall.md`.

The engine (`negation_no_fixedpoint` → `lawvere_fixedpoint`) forks: **μ** — the map is fixed-point-free, no
object forms; **ν** — a fixed point exists. The well-founded family then renders a **verdict on ν**: a
well-founded host refuses it (`no_quine_atom`), a host carrying it is thereby not well-founded
(`quineHost_not_wellFounded`, `floor_not_wellFounded`). Same theorem (`wf_no_selfloop`), two hosts — so
well-foundedness is **not a third root of self-reference; it is the axis of the host's verdict**.

**Use the STANDARD NAMES — all four are published and all four sources are in `.claude-local/papers/`:**
- the ν direction is **"the Diagonal Theorem"** (Lawvere & Schanuel, via Yanofsky 2003 p. 5 Remark 3,
  p. 14 Thm 3 — Yanofsky was already cited in `ZeroParadox/Settheory/Wall.md`; the names were not);
- a host permitting ν is **"degenerate"** (Yanofsky p. 3; nLab, *Lawvere's fixed point theorem*);
- in set theory the permit/refuse split **is** Foundation vs Anti-Foundation (Aczel 1988 **p. 6**);
- the general form is a **published theorem** — Adámek-Milius-Moss 2020 **Thm 7.6** p. 30, *"the only
  well-founded fixed point is the initial algebra"* — with the axis named the **well-founded part /
  coreflection into well-founded coalgebras** (their Def 5.1 p. 22, credited to Taylor). The corpus proves
  the **one-relation shadow** of Thm 7.6, never the coalgebraic theorem.

**Three fences.** (1) The narrow one-root question is still **NO** — `wf_no_selfloop` is proved by
accessibility, not by the engine; `selfloop_permitted` / `engine_is_wf_free` stand. (2) Scope: the
ν-refusal reading covers the **well-founded family only** — the ε₀ row (`ZPN.omegaPow_no_fixedpoint`) is
ordinal arithmetic, not a self-loop instance. (3) **No traversal** — nothing here says the object moves;
that stays the commitment (`l_inf`'s docstring).

**⚠ Prefer the STRONGER library forms; this family has been re-proving the weakest rung.**
`WellFounded.asymmetric` (`Mathlib/Order/RelClasses.lean:225`) beats `wf_no_selfloop` (forbids 2-cycles
between distinct points; `asymmetric₃` for 3-cycles); Mathlib's `WellFounded.irrefl` is **class-valued**
(`Std.Irrefl`, a class with a *field* — it does NOT "unfold to `¬ r x x`") with instances registered, so
`irrefl_of`/`asymm_of` fire free and `ZFSet` already carries the instance; and
**`wellFounded_iff_isEmpty_descending_chain`** (`Order/WellFounded.lean:51`) is a **biconditional** that
renders the ν-hosted side as *"the host contains an infinite ℕ-indexed descent"* — **the INFINITE pole the
Two-Pole rule demands, which the `r x x` form hides.**

**⚠ THAT ADOPTION IS DONE — do not build it again.** It landed 2026-07-29 (`27b1911`) at
`ZeroParadox/Multihomed/Boundary.lean` § I-b: `floor_descent_from_bot`, `bot_not_acc`,
`floor_not_wellFounded_via_descent`. `ZeroParadox/Settheory/Wall.md` already says "Now adopted."
**This line said "Adopting it is open work worth doing" until 2026-07-30 — while § "unstated adjacency"
BELOW, in this same file, already listed the descending-chain form among the CLOSED finds. One file,
two contradictory answers.** That is the exact trap that produced the `HostVerdict.lean`
Trigger-0 revert, and it was live in the manual meant to prevent it. Sweep this file too when a find closes.
- **Purity, measured not inferred:** citing the biconditional at all costs `Classical.choice` (its `mp`
  builds the chain with `.choose_spec`, and `#print axioms` follows the STATEMENT). So
  `floor_not_wellFounded_via_descent` carries `[propext, Classical.choice, Quot.sound]` while § I's
  `floor_not_wellFounded` stays axiom-free and remains load-bearing. `bot_not_acc` is axiom-free **only
  because it is proved by hand**; the one-line `not_acc_iff_exists_descending_chain.mpr` route measured
  choice. Same verdict as the `CovBy` precedent: keep the hand proof, cite the standard name.
- **Fence:** the witness is `fun _ => bot`, the **degenerate** (constant) descent. A genuine non-constant
  descent is strictly more and does **not** follow from a self-loop — still open.
- Correct neighbour names in the pin: `not_acc_iff_exists_descending_chain` (`:34`) and
  `RelEmbedding.wellFounded_iff_isEmpty` (`Order/OrderIsoNat.lean:71`). There is no
  `not_acc_iff` and no `RelEmbedding.wellFounded_iff_no_descending_seq`.

**Why this section exists (2026-07-29) — a measured Trigger-0 failure, and the most expensive one yet.**
A file `Settheory/HostVerdict.lean` was written to "consolidate" this carving **before any prior-art
search**. Its `nu_hosted_forces_non_wf` was **character-for-character** `mu_nu_branch_exclusion`, same proof
body; its `nu_hosted_face` was `selfApp_lands_on_nu`. The contraposition already existed **eight times
across six files**, the carving **three times**, and the standard names sat in a paper the file's own base
already cited. It was **reverted in full** (`7b997fa`, `4a56da4`). Step 1 of the three-step check —
`grep -rn "¬ WellFounded" ZeroParadox` — would have prevented the entire build. **The failure was ORDERING,
not effort:** the expensive corpus grep was done (it is what made the file possible) and the two cheap steps
were skipped, which is the worst split, because doing the expensive half *feels* like diligence. Full
findings: `.claude-local/notes/archive/gate-findings/prior_art_hostverdict_2026-07-29.md`; the
reframe itself (Tim's) is
`.claude-local/notes/future-research/wall_one_root_or_two_trinary_2026-07-29.md`.

**The choice index (NOT a fourth core object — read it before writing about choice or constructivity):** `ZeroParadox/Category/ChoiceCannotBe.lean` — the `#check`-only index of the framework's **relationship to `Classical.choice`**. `Classical.choice` is an ambient kernel axiom, **not** a framework object, so this index is scoped differently from the three above: where choice is provably not needed, what it must not be confused with, and what is actually established. **Read it before writing any prose, docstring, note, or outreach copy touching choice, constructivity, purity, axiom footprints, or the "choice = point of view / chart selection" reading.** Three standing traps it exists to stop:
- **The equivocation (hit four separate times on 2026-07-19).** The ordinary English "choice" — an act of picking, a point of view, a chart selection — is **not** the axiom `Classical.choice`. Every evocative "choice = which way you view the split" reading is a **model** of the choice-vs-no-choice distinction, never the axiom. State it as a model or not at all. **Attribution, stated precisely — an earlier version of this bullet had it wrong and seeded the error into five Lean files:** Diaconescu (1975) proves an **EQUIVALENCE** — a coequalizer of two nonintersecting monomorphisms has a section *iff* subobjects have complements (p. 176), the choice direction being his corollary (p. 178); in modern terms, choice for inhabited subobjects of a two-element object **IS** excluded middle. That **full** AC is strictly stronger is **Cohen 1963** / Fraenkel-Mostowski independence, **not** Diaconescu — never attribute strictness or a failing converse to him. That the restricted fragment nonetheless *appears* not to follow from excluded middle in Lean — the natural construction fails to elaborate and closes only under `classical`, which is **strong evidence, never a proof of unprovability** — looks like a fact about **Lean's `Prop`/`Type` stratification** (the fragment selects into `Bool`, making it data-valued excluded middle), which a topos lacks; that reconciliation is the framework's own finding. **Never state the Lean gap as a negative result**: a failed elaboration is not an independence theorem, and claiming one would need a metatheoretic argument outside Lean. Full statement: `ZeroParadox/Category/ChoiceCannotBe.lean`.
- **NO COUNT — measure on demand, never record one.** Do **not** write a figure for how many declarations carry `Classical.choice` into this file, into any `.lean` docstring, or into any note. `ZeroParadox/Category/ChoiceCannotBe.lean` deliberately records none and gives the three reasons: a corpus total mostly measures how classically **Mathlib** is built rather than anything about this framework (**mostly, not entirely — `Category/Lawvere.lean:70`'s bare `classical` is the framework's own and is ESSENTIAL**, so do not write "none of it is ours"); it reads as "most of this is non-constructive" when the load-bearing fact is that **T-SNAP is axiom-free**; and the number has already been wrong three times (once quoted rather than measured, once measured and gone stale inside a single session — this bullet itself carried the stale one). That index supplies the PowerShell to measure on demand. **The framework is not choice-free; the core is (`t_snap_derived`, no axioms at all); most examined footprints proved removable; and TWO ARE PROVABLY NOT** (§ IV of the choice index). **Date the claim** — see the lesson below.
  - **⚠ CORRECTED 2026-08-01. This line previously read "every examined footprint has been removable — that statement does not go stale, and it is the one to use." BOTH HALVES WERE FALSE**, and the second half is what made the first durable. The two **essential** cases were committed 2026-07-20, one day after the choice index was last touched: `em_of_wellOrder_comparable` (`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean` — comparability of well-orders implies excluded middle; prior art Kraus-Nordvall Forsberg-Xu arXiv:2104.02549 **Thm 38(d)**, there in the data form) and `wem_of_fixedPointFree` (`ZeroParadox/Category/LawvereTaboo.lean` — the general fixed-point-free principle implies **weak** excluded middle, and this one sits on the **keystone**, not on an imported order instance). Both are **taboo reductions**, not failed elaborations, so they clear this file's own bar for a negative result. **Fixed in `ZeroParadox/Category/ChoiceCannotBe.lean` § IV.**
  - **State the shape correctly or not at all.** Each theorem is itself a **choice-free reduction**: the classical content is entirely in the **hypothesis**. What is established is about the **PRINCIPLE** — re-proving it constructively would decide a taboo, so no choice-free re-proof exists — **not** about any particular proof, and **not** an independence result. `#print axioms` reports a proof's footprint and can never witness necessity; that is precisely why the essential side needs a **reduction** where the accidental side needs a **measurement**.
  - **The defect was bigger than this line and was fixed AS A CLASS (closed 2026-08-01).** `ZeroParadox/Category/ChoiceCannotBe.lean` — the index this file *mandates reading* before any prose about choice — had asserted at `:91` *"No essential case has ever been found"* and at `:142` *"**No essential case has been found anywhere in the framework**"* while referencing **neither** theorem (`#check` count: 0). Meanwhile `RELEASES.md:425`, the **published** record, already advertised that index as containing "the two essential cases". The index was written honest and went false **one day later**. **Now closed:** both universal negatives are gone from the corpus (grep the claim: 0 hits) and both witnesses are `#check`ed in § IV. **Residual debt, not yet swept:** several dated notes still repeat the claim — `notes/choice_essential_vs_accidental_2026-07-18.md:31,122,134` and `notes/future-research/roots_enumeration_category_2026-07-20.md:295`. Dated records are deliberately not rewritten (they cite the tree as it stood), so **verify at the artifact, never from a note** — which is this file's standing rule anyway.
  - **The lesson, which is this file's own warning arriving at full scale:** the `#check` lines cannot overclaim; the **prose** can, and here the overclaim is not a gloss on one theorem but a **global negative** ("nowhere in the framework") in an index whose stated premise is that it cannot overclaim. **A universal negative in a `CannotBe` index is the most dangerous sentence shape in this corpus — it is falsified by any single future commit and nothing mechanical notices.** Prefer "none located as of &lt;commit&gt;" over "none exists".
- **The instance hazard.** Choice often enters at the **instance** level, invisible in the lemma: `Prop.instBooleanAlgebra` carries `Classical.choice` while `Prop.instHeytingAlgebra` is `[propext]`. A `Prop`-scoped statement that does not PIN its instance silently acquires choice and every purity claim about it becomes vacuous. Measure the instance and the tactic, not just the lemma.
  - ⚠ **AND THE `PurityCheck` CONVENTION DOES NOT COVER INSTANCES.** It is a per-file section of `#print axioms` over *theorems*. Measured 2026-08-08: **52 of 73 named instances had no `#print axioms` anywhere**, and a further **57 instances are anonymous**, so they cannot be `#print axioms`'d by name at all. All three hand-built `ZPCategory` instances carry `Classical.choice` and none had ever been measured — the hazard this bullet names, live and unnoticed in the corpus that names it.
  - ✅ **USE `python .claude-local/axioms.py <pattern>` — DO NOT PROBE.** `ZeroParadox/Meta/Snapshot.lean` already runs `Lean.collectAxioms` over **every** declaration in every tracked module on each build — 2494 of them, anonymous instances included — and files them in `translation_matrix/golden_master.json`. **Nothing read it for months.** So "is X choice-free?" cost several `lake env lean` probes, and because it was expensive **it got assumed instead** — which is exactly how a wrong purity claim entered this session. `--instances` groups the whole instance surface by footprint; `--summary` gives corpus totals **computed now**, never recorded. ⚠ The snapshot only regenerates where `.claude-local/translation_matrix/` exists, so it does **not** regenerate in CI; the tool prints its own age for that reason. **An empty result is evidence about your pattern or a stale snapshot, never about the corpus.**

**The computation index (NOT a core object — read it before writing about the computational face):** `ZeroParadox/Computability/Kleene.lean`, specifically **§ II** (the `KleeneStructure` class), **§ III** (T-COMP and its fence), **§ VI** (the quine family), and the **axiom-footprint block** in its header. Also `ZeroParadox/Information/Surprisal.lean`'s `l_inf` docstring, which is the honest statement of where the argument stops. *(A dedicated `#check`-only `ComputationCannotBe` index is drafted at `.claude-local/lean_wip/DRAFT_ComputationCannotBe.lean` and will replace this pointer when it is promoted through the gates.)*

**Read it before writing any prose, docstring, companion text, figure, or outreach copy touching computation, execution, the Kleene quine, DA-1, or "the bottom runs itself."** Six standing traps, every one of them measured on 2026-07-26 and every one of them shipped in the corpus for months:

- **`da1_closed_concrete` proves `IsQuineAtom (bot : MachinePhase)` and NOTHING computational.** No `Code`, no execution. It is named as though it closes DA-1; it closes the structural half. **Never cite it for self-execution.**
- **T-COMP proves THREE characterisations equivalent, not four** (`t_comp` is literally `t_exec_triple_iff`). The computational face enters as the class field `botCode_is_quine` — an assumption, not a clause.
- **`da1_paths_unified` is a CONJUNCTION, not an identity.** "Both hold" is not "these are the same fact," and they cannot be equated: one is about an element of `L`, the other about a `Code`.
- **The quine family is witnessed by CONSTANT codes** (`hconst_quine`, inside `infinite_quine_family`). `IsComputationalQuine` is a *periodicity* condition, strictly weaker than self-reference — a constant satisfies it vacuously. So the family is broad, and it is **not** a padding orbit (padding gives many indices for the *same* function).
- **The set-theoretic bottom is UNIQUE; the computational fixed points are an INFINITE indexed family.** A point and a family are different shapes. No fix to the predicate changes that.
- **`#print axioms` follows the STATEMENT, not the proof.** `[KleeneStructure L]` in a statement reaches Mathlib's `eval` and puts `Classical.choice` in the footprint even when the hypothesis is inert in the proof. **Inert-in-the-proof and absent-from-the-footprint are different properties — never infer either from the other.** This figure has been wrong four times, always because it was quoted rather than measured. **Measure it.**

**The honest line, which `l_inf`'s own docstring already states:** L-INF supplies the formal premise (surprisal at ⊥ is unbounded); the step from that to *forced execution* is an ontological bridge, a named design principle, **not** a mathematical consequence. The framework commits that the snap fires; it does not prove it.

**The claims mirror (the claim graph made checkable — read/update it whenever a claim's STATUS is asserted or changed):** `ZeroParadox/ClaimsMirror.lean` — the machine-checked representation of the SSOT `claims` store. Each claim node the store marks `proved` / `corr` / `deep` is **restated exactly and discharged from the existing machinery**, so a claim's status is a **verified link to a green declaration, not a label**; the purity block prints each claim's honest axiom footprint (three faces axiom-free — `node-order`, `node-set-theory`, `T-SNAP`; the p-adic floor `[propext]`; the rest carry Mathlib choice). The three non-theorems are represented by their **deliberate absence**: the two `Lawvere-*` conjectures (one Set face provably *not* a Lawvere instance) and the retired `MC-1-identity` (ill-typed — `x = y` across distinct categories is not a well-formed proposition) carry **no theorem**, and that non-representation is itself the checked fact. **Why it exists (2026-07-21):** a `proved` label is only as good as the decl under it, and a false premise attached to a *true* conclusion is invisible from the outside — nothing downstream breaks, so being right about the conclusion hides a wrong reason (the ZP-A / ZP-E Foundation-squeeze false premise survived to high revision exactly this way). The mirror is the mechanical guard: the kernel re-derives each claim indifferent to how it was reached, so a status that is not actually backed shows up as a decl that will not elaborate. **The rule:** before asserting a claim is proved (in prose, a docstring, a companion, outreach), check it has a green entry here; and whenever a core claim is added, or a claim's status changes, update `ClaimsMirror.lean` and its SSOT `link_claim` in the **same** change — the same reflex as the purity check and the SJV sync.

**Bedrock invariants — machine-checked; never violate, always verify against the theorem (do not assume):**
- **ε₀ ≠ 0. Always. In any reading, carrier, or encoding.** (`epsilon0_ne_zero`.) Never "fence ε₀ = 0" or treat 0 as a candidate value for ε₀ — it is not a well-formed possibility.
- **ε₀ ≠ ⊥.** (`epsilon0_ne_bot`.) ⊥ = 0 is the *base* the ε₀-tower is seeded at; ε₀ is its *closure* — the base is never its own closure.
- **ε₀ is both min AND max at once** — least fixed point ≡ tower supremum (`epsilon0_min_eq_max`); direction-/instance-specific, never collapsed to one face.
- **ε₀ requires two conditions**: the ω-tower operator `α↦ω^α` AND the base ⊥ (`ε₀ = nfp(ω^·)⊥`, `epsilon0_eq_nfp_bot`; Mathlib `ε₀ = deriv(ω^·) 0`). It is the *minimum* step next to the pole (Veblen coords (1,0); the 1/∞ reading), never the pole.
- **⊥ = 0 = ∞ is the pole** — *stated*, not fenced (the framework's own identity). **It is a CHART claim, not a point identity:** the same object reads as the zero pole under one measurement and the infinity pole under another. The two halves have **different witnesses** — **coincidence**: `infinitude_forces_infinite_complexity` (`ZeroParadox/Valuation/InfinitudeFloor.lean`; the floor's complexity *is* `⊤`); **drift**: `pole_inversion` (same file; the members converge to the floor while their complexity ascends to `⊤` — two measures running opposite along **one sequence**); **inversion**: `rInv_swaps` (the antipodal exchange). ⚠ **CORRECTED 2026-08-06 — this line used to name `pole_inversion` as the COINCIDENCE witness, contradicting the KIND table below, which lists it under DRIFT.** The table is right: `pole_inversion`'s conclusion is two `Tendsto` conjuncts and contains no `cx floor = ⊤`. The coincidence on that carrier is a *separate* declaration, named above. (`pole_inversion`'s own docstring also claims the theorem holds "their coincidence" — the **typeclass** does, the **theorem** does not.) **Never cite `rInv_swaps` for the coincidence.** It proves `rInvHomeo (some 0) = ∞ ∧ rInvHomeo ∞ = some 0` — two points *exchanged*, and its own docstring calls this "the 0=∞ antipodality"; in that carrier `some 0` and `∞` are provably distinct, and if they were one point the swap would be trivial. (Corrected 2026-07-26: line had cited `rInv_swaps` for the identity for months. The computability face's version of the coincidence is `selfloop_is_zero_and_infinity` — a self-looping configuration yields nothing (zero pole, output chart) while never halting (infinity pole, step chart).) This is NOT ⊥ = ε₀ (which is false).
- The snap-arc **returns to a bottom, never to ε₀** (`epsilon0_ne_bot`). The framework reads that bottom as a **new** one — a successor null, the next instantiation. What is *proved* is the **role** half: anything playing the bottom role **is** the bottom (`t_iz_limit_is_new_null`, which is one direction of `da2_bottom_characterization` — its statement is `(∀ x, join terminal x = x) → terminal = bot`, with no chain, no limit and no novelty in it). The **novelty is a commitment, not a theorem**: within a single lattice `bot` is unique, so "a different bottom" is not expressible there, and in the 2-adic realization the arc reapproaches the *same* 0 (`snap_arc_z2_loop`). **Never cite `t_iz_limit_is_new_null` as a witness for novelty.** (Corrected 2026-07-26: it had been named here as the novelty witness for months. Found by an adversary gate probing a *second* claim after the ZP-K sweep closed — see the note on the witness-vs-statement defect class.)

**Why this rule exists (2026-07-17):** a run of prose/figure errors — fencing ε₀ = 0, "co-locating ⊥ and ε₀," flattening min≡max to one face, calling ε₀ "a large ordinal / ceiling" — all came from reconstructing these objects from working memory instead of reading the Lean. The fix is mechanical: read the `CannotBe` index first, cite the theorem, never gloss.

## Commitments Go In HYPOTHESES, Data Goes In BRACKETS — Default Method, Hard Rule

**A commitment encoded as a typeclass field reads as data, because brackets are where data lives.
That single fact produced every bedrock defect of 2026-07-26.** State commitments as explicit
hypotheses so the signature cannot be misread.

**The test — CAN IT BE FALSE?**
- **Data** (goes in brackets): the carrier either has it or does not. `[ZPSemilattice L]` — a join with
  laws. Cannot be "wrong"; inference on it is worth keeping.
- **Commitment** (goes in a hypothesis): the framework asserts it and reality might not comply.
  "Nothing external can execute ⊥." "The bottom departs." "States are discrete."

**NEVER BUNDLE ONE INTO THE OTHER.** If a class field asserts something the framework could be wrong
about, extract it as a hypothesis on the theorems that need it. `KleeneStructure` is the worked example
of the failure: it bundles a `Code` (data) with the assertion that the code names ⊥ (commitment), and the
bundling is precisely what let `da1_closed_concrete` read as establishing self-execution for months.
`AbstractSelfApp` has the same shape — which is why `trivialSelfApp` inhabits it, and why "L carries
`AbstractSelfApp`, therefore …" is vacuous.

**The canonical form** (`ZeroParadox/Computability/Occurrence.lean` § VI-b):

```lean
theorem execution_requires_branching (R : σ → σ → Prop) (s : σ)
    (hfix : R s s)                      -- COMMITMENT: the bottom is its own fixed point
    (hdep : ∃ t, R s t ∧ t ≠ s) :       -- COMMITMENT: execution occurs
    ∃ t u, R s t ∧ R s u ∧ t ≠ u        -- CONSEQUENCE, not a further assumption
```

**Why this is the default and not a preference.** It is the only defence found on 2026-07-26 that
**requires nobody to remember anything** — gloss labels need discipline, review rounds need reviewers, a
type signature simply is what it is. It makes the framework's assumption load **countable** (grep the
hypotheses) instead of recoverable only by reading prose. And it would have prevented **both** bedrock
findings that day: `da1_closed_concrete` could not have been cited for self-execution with execution
visible as a hypothesis, and `t_iz_limit_is_new_null` could not have been cited for novelty with novelty
visible as one.

**Three encodings, decreasing honesty — know which you are writing:**
1. **Baked into the carrier** — `ax_b1_distinct : nullState ≠ firstAtomicState := by decide`, where
   discreteness *is* the two-element type. Invisible at every use site. **Worst.**
2. **Hidden in a class** — `[QuineHost L]`, `[KleeneStructure L]`. Visible only if you know what the
   class carries.
3. **Explicit hypothesis.** Visible on the face of the statement. **Prefer this for anything that can be
   false.**

**Rollout — AS-TOUCHED, not a rewrite.** The corpus has ~1400 declarations on the class form and there is
no realistic big-bang migration. Every new or edited commitment uses the hypothesis form immediately;
where an existing class carries a commitment, add a **companion explicit-hypothesis theorem** rather than
refactoring the class. First candidates: `KleeneStructure`'s identification, and **AX-B1**, which is the
framework's one substantive modelling commitment and currently the least visible of the three (encoding 1).

## ⭐⭐ THE GATE-ENFORCED CONVENTIONS. Rules here; the ARGUMENT is `tools/verify/README.md`.

**TRIGGER — an action, so there is nothing to adjudicate: you are about to write a POV claim, declare
a requirements class, add a prose block or docstring, close a self-exemption hole, or WRITE ANY FILE
TO DISK.** Each rule below **BLOCKS at push**, so you find out either way; reading first is how you
avoid finding out the expensive way.

| rule | fires when | checker |
|---|---|---|
| **A point-of-view claim declares its KIND and its STATUS.** Five kinds — COINCIDENCE, INVERSION, DRIFT, CARRIER, INVARIANT — via the existing `Statement:` / `Reading:` labels. **There is no slot for DENYING a reading, by design.** | you write "chart", "frame", "point of view" | `check_pov.py` |
| **A requirements class is only informative if something FAILS to be a member.** Build the trivial witness or prove you cannot; both answers are worth having. | you declare a `class` or `structure` | `check_classes.py` |
| **Short header, statement per declaration; prose never exceeds code.** The Engineer's Take is exempt. | you add a header block or a docstring | `check_prose.py` |
| **A guard protects a PROPERTY, not a hole — enumerate EVERY route.** Closing one route and calling it fixed is this project's most repeated defect. | you close a self-exemption or bypass | `guards.py` |
| **⭐⭐ REMOVING A BASELINE ENTRY OWES A `/claim-review`. A baseline entry IS the record that a site was let through UNEXAMINED**, so deleting it retires the record without discharging the liability. **The checkers measure the SHAPE of prose — volume, vocabulary — and never whether a claim is TRUE**, so a block dropping under cap is not a block whose claims were checked. ⚠ **FAIL-CLOSED, because "the key stopped matching" is not enough:** a removal is either *content GONE* (nothing to review) or *content MOVED* — a path-keyed entry dying while the claim lives on elsewhere — and no checker can tell them apart. The only exemption is the FILE being gone; an entry naming `Foo.lean` also demands its `Foo.md` ride-along. **Removal is still always ALLOWED — it is the point of the freeze — it is just not FREE.** | you delete a line from any `*_baseline.txt` | `check_frozen.py` |
| **EVERY FILE WRITTEN TO DISK IS VERIFIED — `python tools/verify/check_encoding.py <path>`.** ⚠ **"Is it UTF-8?" is the WRONG QUESTION and returns PASS on this defect**: double-encoded text is valid UTF-8 at every byte, so a decodability test is green while the content is garbage. And the corruption usually enters at **script PARSE time, not write time** — PowerShell 5.1 reads a `.ps1` as the system codepage unless the script carries a BOM, so a correct writer faithfully writes an already-mangled string. **Prefer the `Write`/`Edit` tools; keep non-ASCII out of `.ps1` source.** ⚠ **TWO TIERS: BOM and undecodable BLOCK; suspected double-encoding WARNS** and is quieted only by `tools/verify/encoding_whitelist.txt` — **verified** exclusions each carrying a stated reason, because the round-trip test provably cannot separate mojibake from some genuine typography (`3 × 10²` encodes to valid UTF-8). An entry with no reason is ignored. Recipes and the repair procedure (a whole-file inverse DESTROYS a mixed file): `tools/process/file-encoding.md`. | you write any file | `check_encoding.py` |

**⭐ THE ONE-LINE WHY, and it is the same for all four: each was a CONVENTION that leaked before it
was a CHECKER.** This file records **seven** conventions that leaked while being remembered by people
who had read them; every one of these four is a rule that failed as discipline and works as a gate.
That is the argument for reading `tools/verify/README.md` before arguing with any of them.

**📖 THE FULL ARGUMENT — `tools/verify/README.md`.** What each checker detects, the measured defect
it exists to stop, the baseline policy, and the controls each was verified against.
**Read it before changing a checker, adding a baseline entry, or claiming a gate is wrong.**

⚠ **Why it is THERE and the rules are HERE.** The arguments are prose that every session and
every subagent used to pay for, and **the gate fires whether or not anyone read them** — measured
2026-08-15: line 127 of this file fired reliably all day, line 2135 did not fire once. A rule in the
tail is decorative. So the rule, the trigger and the consequence stay in the firing zone; the
justification moved to a file this line NAMES. Same mechanism as the `CannotBe` indexes — delivery
is a trigger naming a path, not injection.

⚠ **A baseline is DEBT, not a decision, and all four are baselined.** They block on NEW sites only.
**Shrink the baseline as files are touched; never grow it deliberately** — `debaseline.py` reports
what is outstanding.

## Every brief carries the CONTROL OBJECTS and "name your first unjustified step". Hard Rule.

⚠ **This section deliberately did NOT move to `tools/verify/README.md` with its four neighbours.
Nothing enforces it** — no checker fires when a brief omits the controls — and an unenforced rule
outside the firing zone is a rule that stops working. **Enforcement is the criterion for moving a
section out, never adjacency.**

**Adopted 2026-08-11 from the zeta-zeros paper** (`.claude-local/papers/claude_zeta_zeros_two_thirds_2026.pdf`,
§C.6 *Parallelism with controls*). Its twenty-three concurrent agents each received the **same control
objects** — Davenport-Heilbronn functions, Epstein zeta functions, planted-zero Beurling systems:
objects satisfying the same inputs **for which the conclusion is FALSE** — plus one standing
instruction, *name the first step that is not justified*. Reported outcome: *"Most lines died against
their controls. The one that survived did so precisely because the controls under-certified."*

**ZP already owns its controls and has never issued them as a standing set** — they get run when
someone remembers, which is exactly how five of seventeen requirements classes went degenerate
unnoticed. The § above enforces that the degeneracy question was *asked*; this makes the answer
*available* to whoever is asking.

**Put these in every brief that BUILDS or REVIEWS a class, a claim, or a construction.** Located and
verified at their definition sites 2026-08-11 — a dated survey, not a completeness claim:

| control | where | kills |
|---|---|---|
| `Unit` / `PUnit` | — | any algebraic signature; every theory has a one-element model |
| `Empty` | — | anything with a `bot : L` field — but see the trap below |
| `Bool`, `Fin 3`, `ℕ → ℕ` | — | "the class bites at two or more points" |
| `trivialZPSemilattice` | `Valuation/Scale.lean:99` | `ZPSemilattice` membership as an argument |
| `trivialSelfApp` | `Computability/SelfApp.lean:177` | *"L carries `AbstractSelfApp`, therefore…"* |
| `trivialValBridge` | `Valuation/ScaleBridge.lean:218` | `ValBridge` membership |
| `trivialValuationStructure` | `Valuation/Scale.lean:111` | `ValuationStructure` membership |
| the constant map `_ ↦ ⊥`, the always-true relation, a constant sequence | — | self-application, `SeparatedSuccession`, periodicity |
| **ℝ** — `f_snap_impossible`, `Computability/ComputationCannotBe.lean:152` | | any claim that the snap is available in a general ordered carrier |

⚠ **`Empty` is a two-sided trap.** *"The finite carriers are exactly the subsingletons"* shipped as a
bedrock defect because the true statement needed **inhabited** subsingletons. And K1 is the same trap
inverted — `Order/Lattice.lean` claimed non-members *"abound"* when **every inhabited carrier admits a
`ZPSemilattice`** and `Empty` is the only obstruction. Run it, and read which way it points.

⚠ **VERIFY A CONTROL EXISTS BEFORE NAMING IT.** Writing this table, one name recalled from a ledger
row (`scTriv`) **did not resolve anywhere in the corpus**. A brief citing a control that does not
exist is worse than a brief with no controls: the agent reports it could not build the witness, and
that reads as evidence the class has teeth.

## Rules That Must Reach Spawned Agents — Hard Rules

**Why this section exists (measured 2026-07-19).** A spawned agent receives, automatically: this file in
full, the user-level `CLAUDE.md`, the Lean `.claudecodes` block, the project-standards block — **and the
memory INDEX only, not memory file bodies.** So a rule whose content lives in a memory body reaches a
subagent as one line among ~100 in an index, competing for attention with ninety-nine others, firing at
no particular moment. That is not a control.

**The consequence, verified:** a subagent invented a factual detail about a cited paper while the line
*"Draft from source only — public math claims must trace to a specific source passage"* was sitting in
its index. The rule was visible and did not bind. **A rule that must not be violated belongs HERE or in
the task brief. Memory is for context, not enforcement.** When delegating, carry the relevant rules below
into the brief explicitly — the same way the encoding and glob warnings are already carried.

- **Draft from source.** Never describe the content of a source you have not read. Cite existence (title,
  venue, that it exists) freely; assert specific technical content **only with the passage in hand**. If
  you cannot read it, say so explicitly — do **not** soften a specific into a vaguer assertion about a
  paper nobody opened. Applies to Lean docstrings citing external papers, companion sections, discussion
  comments, and outreach. Before concluding a PDF is unreadable, try `pypdf`/`pdfminer` directly
  (`.claude-local/extract_pdf_text.py`); a fetch tool's failure is not a fact about the source.
- **Start new files from the templates.** Any new `.lean` file starts from `.claude-local/templates/`
  (`TEMPLATE_lean.lean`, `TEMPLATE_experimental_mapping.lean`) and its `README.md`. Note the template's
  namespace line is stale — namespaces are FLAT (`ZeroParadox`), not `ZeroParadox.ZPX`.
- **Never write a bare "bottom."** Always say which level: the structureless referent / a specific
  structured instance (a face) / the family-and-schema. The bare word sliding between senses is the
  project's longest-standing source of confusion. (`/remember-bottom` re-orients.)
- **The literal string `ε₀ = 0`** may appear ONLY as a guard or fence forbidding it, or as a theorem where
  ε₀ is an argument. Never a bare assertion, never in conversation — even to deny it. Canary:
  `epsilon0_ne_zero`.
- **Standard mathematical term first**, ZP term after as a declared shorthand — never the reverse. This is
  the defense against the "ontology built on an equivocation" reading.
- **Verify an API exists before naming it in a plan.** Grep the Mathlib pin; a plan citing a lemma that
  does not exist in the pinned version is worse than no plan.
- **Never delete a Lean file a subagent produced**, even a failed experiment — say so in the brief.
- **NO SCRATCH FILES IN THE REPO.** Any probe, temp script, or measurement file goes in the session
  scratchpad directory, never under `ZeroParadox/` or anywhere else in the working tree. A reviewer that
  needs to measure something writes it to the scratchpad, runs it, and deletes it. **Measured
  2026-07-19:** a review agent left a `ZZTestOrd.lean` probe in the source tree (since deleted, so the
  path no longer exists) and it was committed — a scratch probe is now in the permanent history. Put this
  line in every subagent brief.
- **Reviews are READ-ONLY on the working tree.** A gate reads, measures, and reports; it does not modify
  repo files. The only writes a gate may make are its signal file and its findings note under
  `.claude-local/notes/`.
- ⚠⚠ **AN AGENT THAT EXERCISES THE HOOKS MUST NEVER `git reset --hard`, `git checkout -- .`,
  `git clean`, OR `git stash` THE SHARED TREE — IT WILL DESTROY THE CALLER'S UNCOMMITTED WORK AND
  REPORT SUCCESS.** Measured 2026-08-10: a `/rely` run was told to exercise the commit and push
  gates and to leave the repository exactly as it found it. It made probe commits and reset
  **`--hard`** to the base three times. That is a *correct* reading of the instruction, and it
  **silently deleted an uncommitted `CLAUDE.md` edit** the caller was holding; the agent then
  verified *"tracked tree clean, HEAD unchanged"*, which was true — and was the destruction. It had
  even NOTICED the concurrency, reporting that two files *"were being edited by their author during
  the trial"*, and hard-reset anyway. **"Restore the tree" and "preserve the tree" are different
  instructions, and only the caller knows which is meant.**
  - **Rule for the BRIEF:** an agent needing to create commits works in a dedicated worktree —
    **`worktree(action='add')`**, which returns a detached checkout under a scratch area outside the
    repository — never in the shared checkout. It gets a private HEAD and index, so nothing it does
    can reach the caller's tree; cleanup is `worktree(action='remove')` with that path, and
    `action='prune'` drops records of worktrees whose directories are already gone. The `CAL-2`
    pipeline replay used exactly this and left the main tree untouched.
    ⚠ **CARRY THIS INTO THE BRIEF VERBATIM, because the command CHANGED.** The old
    `git worktree add --detach` is now denied like every other direct git call, and this is the
    sanctioned escape from the four destructive verbs — so a brief that still names the old form
    leaves its agent with a safety rule it cannot execute. Measured 2026-08-22: `rely.md`'s single
    git reference was exactly this line.
  - ⭐ **The four destructive verbs are now REFUSED, not merely banned** — the hook denies the
    command and gitRobot has no parameter that reaches `--force`, `--hard` or `-f`. This bullet is
    now a statement of *why*, kept because the reasoning is what transfers to the next verb nobody
    has classified yet.
  - **Rule for the CALLER:** commit or stash your own work **before** spawning any agent licensed to
    touch git state, and treat the tree as unstable until it returns. This file already warns that
    background agents run concurrently so the tree is not a stable snapshot; this is that hazard
    with a **destructive** edge rather than the merely additive one of the `git add -A` incident.
  - ⚠ **`.claude-local/` survived only because the parent ignores that path — do not read that as
    safety.** A `clean -xfd` would have taken the whole private working folder. ⚠ **It DOES have a
    remote now** (`ZeroParadoxLocal`, private) — this line said "no remote and is backed up by hand"
    until 2026-08-22, which was stale, **and believing it is what left three commits sitting on one
    disk that day.** Commit *and push* it; see the handoff's PART 0b step 4.
- **Engineer's Takes are Tim's voice.** Claude never drafts one. The only sanctioned assembly is
  restating Tim's own session statements as declaratives, grammar-cleaned, shown back for approval.
  **Fill the Take BEFORE running the review gates (Tim, 2026-07-20)** — it is public prose in the pushed
  file, so the reviews must cover it. Order: finish the work → insert Tim's Take (with approval) → run
  editorial/adversary/prior-art on the COMPLETE file → push. Gating first and adding the Take after
  leaves it unreviewed and (under the SHA-256-per-file signal scheme) stales every signal, forcing a
  needless re-run.

## Anything convertible from prose to Lean MUST be converted. (Tim, 2026-08-08.)

> *"anything that can be converted from prose to lean should be done, with a single line statement
> or read reference for it right there"*

**THE RULE.** If a sentence makes a claim a declaration could carry, **write the declaration** and
leave ONE line at the site — a `Statement:`/`Reading:` gloss, or a pointer. Prose is the fallback
for what cannot elaborate, never the default. This generalizes the § above: that one caps prose by
volume, this one removes the *reason* to write it.

**THREE TIERS, in order of preference. Reach for the lowest-numbered one that fits:**
1. **An `example` that fails to compile when the claim is wrong.** Already the stated best form for
   `Statement:`; **now required for `Reading:` too, wherever the reading is checkable.**
2. **Emitted output** — `#print axioms`, `#check`. The machine computes it, and the **public CI log
   already carries all of it**: measured 2026-08-08 on `lean_action_ci.yml`, 1,270 `info:` lines
   including every axiom footprint and all 72 `BottomCannotBe` signatures, file-and-line prefixed,
   no truncation, regenerated per run, **retained nowhere in the repo — and that is correct.** Do
   not commit build logs; point at the workflow, never at a run id (logs expire).
3. **Prose**, only for interpretation carrying no mathematical content ("the framework calls this
   concurrency"). Label it `Reading:` and leave it alone.

**⚠ THE TRAP: `IO.println` of hand-written English is tier 3 wearing tier 2's clothes.** Measured
2026-08-08 — `#eval IO.println "Reading: the two faces coincide as a bare point."` printed that
**false** sentence, exit 0, no complaint. The machine did not compute it; it echoed it. In a log
where every other line is elaborator-derived, a typed sentence inherits authority it never earned —
this file's own *"the `#check` lines cannot overclaim, the glosses beside them absolutely can"*,
amplified rather than fixed. **Never route a claim through stdout to make it look checked.**

**A READING IS CHECKABLE WHENEVER IT CLAIMS STRENGTH, SCOPE, OR GENERICITY** — and those are the
readings that go wrong. Worked example, the bedrock finding of 2026-08-08: a `Reading:` said
`faces_iso_unique` shows the two faces of ⊥ coincide as a bare point, and that an exclusion rests on
it. Three lines refute it — `example (α : Type) : Subsingleton (α ≃ PUnit) := inferInstance`
elaborates, so the theorem holds of `Bool` and says nothing about ⊥. **That reading had been
certified accurate by an editorial gate one round earlier.** A prose round could not catch it; an
`example` makes it unwriteable. Same shape for *"the finiteness hypothesis is load-bearing"* (exhibit
the counterexample without it) and *"not* the *period, merely* a *period"* (exhibit a constant code
with a second period).

**⚠ And the probe settles it EITHER WAY — a failing `example` is a finding, not a dead end.** For
*"definitionally `t3_unreachability`"* the natural probe is `example : @t4 = @t3 := rfl`; **measured
2026-08-08, it does NOT typecheck** — `t4_chains_forward_only` carries an extra unused binder, so the
two statements are not the same type and the word *"definitionally"* was wrong. The one-line-
consequence form does elaborate. **That is the rule working**, and it is why you run the probe
instead of picking the phrasing that sounds safest.

**This is the NO-GO gauge (`.claude-local/notes/nogo_gauges_2026-06-29.md`, discipline (b) — *name
the obstruction in advance*) pointed at readings for the first time.** It also lands on the right
side of the prose rule for free: an `example` counts as **code**, not comment.

⚠ **Placement: put the `example` AFTER the `#check` it qualifies, never between the gloss and the
`#check`.** `check_prose.py` looks immediately above a `#check` for its gloss, so an interposed
`example` reads as a missing gloss and fires. Measured 2026-08-08 on the first application of this
rule. Write "the `example` below" in the gloss.

⚠⚠ **AND THE `example` MUST NOT ITSELF BE GENERIC — that is the same defect one level up, and it
happened on the second application of this rule.** To witness *"monotonicity is not the obstruction
for `Ordinal`"* an `example : Ordinal.{0} →o Ordinal.{0} := OrderHom.id` was written. **`OrderHom.id`
inhabits `α →o α` for every preorder**, so it says nothing about `Ordinal` — exactly the
`Subsingleton (α ≃ PUnit)` failure this section exists to prevent, committed four lines from where
the same file correctly fences it. **The test is the one from § *A requirements class is only
informative if something FAILS*: ask what the `example` EXCLUDES.** If it would elaborate with the
subject swapped for an arbitrary carrier, it witnesses nothing. Here the honest witness is the
ω-tower map itself, `⟨fun a => ω ^ a, fun _ _ h => opow_le_opow_right omega0_pos h⟩`.

**⚠ THAT WARNING HAS A NULL CASE, and reading it absolutely gets the answer backwards.** Ask what
the `example` excludes **relative to the claim it witnesses**, not in the abstract. When the claim
IS a universal — *"every inhabited carrier can be equipped"*, *"nothing here excludes anything"* —
a **generic** witness is the exact refutation and a specific one would be weaker. Worked example,
K1 (2026-08-10): the corpus said non-members of `ZPSemilattice` *"abound"*; the witness that settles
it is `example (L : Type) [Nonempty L] : Nonempty (ZPSemilattice L)`, which is maximally generic on
purpose, paired with `example : IsEmpty (ZPSemilattice Empty)` to pin inhabitation as the sole
obstruction. **Genericity is a defect when it is accidental and the content when it is the claim.**
This is the same shape as INVARIANT being the ratified null case of the Two-Pole Test — a rule that
fires everywhere is the cry-wolf shape this file says to narrow rather than tolerate.

**PREFER AN ANONYMOUS `example` OVER A NAMED `def`/`theorem` FOR A WITNESS — measured 2026-08-10,
it declares nothing.** `batch.py decls_in` returns `[]` for the two examples above and `['realOne']`
for a `theorem` beside them, so a witness in `example` form owes **no `#print axioms` entry and no
`ssot.json` row**, while a named one owes both plus an SJV sync. Name it only when something else
must cite it. Nothing is lost: the kernel checks an `example` exactly as hard, which is the entire
point of tier 1.

## The recurring defect is UNSTATED ADJACENCY — the fix is a pointer, not a theorem

**This corpus's characteristic failure is not wrong theorems. It is true theorems whose reach nobody
recorded.** Measured four times on 2026-07-29/30, each time the honest finding was *"the mathematics is
already here, and nothing says so"*:

* **Oscillation.** Asked whether the framework excludes liar-type flip-flop. `wf_no_cycle` already proved
  it — its own docstring says *"this also rules out 2-cycles"* — and grepping the Lean for "oscillation"
  returned nothing. Fix: instantiate at the two ends + state the fence (the floor is non-well-founded, so
  the exclusion holds ABOVE it and fails AT it).
* **min≡max.** Related coincidences, never cross-linked, so the "both poles" and "both extremes" readings
  drifted as if separate. **NONE of them is a `fork_collapse_iff` instance** — corrected TWICE on
  2026-07-30, because the first fix relocated the error rather than removing it. `fork_collapse_iff` needs
  `[CompleteLattice α]` and a monotone `f : α →o α`; `Ordinal` with `α ↦ ω^α` has a proper class of fixed
  points (`omega0_opow_epsilon`, so nothing collapses), `ZPSemilattice` is a bare join-semilattice whose
  `selfApp` is not an `OrderHom`, and the categorical seam lives in `ModuleCat ℂ`. **They share a SHAPE,
  which across distinct structures is a type boundary, never a common theorem.** State the shape; never an
  instance-of relation.
* **Turing machines.** `Occurrence.lean`'s results are stated over `σ → Option σ`, which **is** Mathlib's
  `StateTransition`; `Turing.TM0/TM1/TM2.step` all have that exact type and Mathlib's TM development is
  *built on* it. So those results already cover every Mathlib Turing machine — and the corpus had never
  mentioned `Turing.*` once.
* **The descending-chain form.** The INFINITE-pole reading of the floor sat in a Mathlib biconditional
  (`wellFounded_iff_isEmpty_descending_chain`) that this family had never cited.

**The rule.** When a question arises and the answer turns out to be already proved, **the deliverable is a
POINTER, not a new declaration.** Adding an elementary instantiation is the failure mode the prior-art gate
keeps catching (see Trigger 0). Ask in order: is it proved here already? is it in Mathlib? is the gap only
that nobody wrote it where the question gets asked? If the last — write it *there*, at the site the reader
lands on, not five sections away.

**Two corollaries worth their own line.** (1) **Generality is why the results are weak, and also why they
are free** — a theorem over `σ → Option σ` is elementary *because* it covers everything, and covering
everything is the payoff; state both halves. (2) **Adjacency is not identity.** "Turing machines are
witnesses" is licensed; "the bottom is a Turing machine" is a cross-carrier identity and the same type
boundary as everywhere else. The `QuineHost` precedent is the model: never "we commit to AFA", always "here
are the requirements, and AFA is a witness meeting them."

### ⭐ THE TWO RULES ABOVE AND BELOW PULL OPPOSITE WAYS. The resolution: ONE LINE at the site, the FULL STATEMENT at the canonical home. (Tim, 2026-08-15.)

*"Write it **there**, at the site the reader lands on"* pushes toward restating it locally.
*"Never enumerate in prose what the artifact defines"* pushes toward a bare pointer. **Both are rules
on this page and they disagree.** The resolution is the shape the corpus already uses in its
`Statement:` / `Reading:` glosses:

- **ONE LINE of consequence at the site** — what a reader standing here needs in order to keep reading.
- **A POINTER to the canonical home** for the full statement.
- **NEVER a bare pointer** (*"see `l_inf`"* makes the site worse to read, which is what the
  write-it-there rule is protecting).
- **NEVER a paraphrase.** A paraphrase is a copy, and a copy goes stale the instant the original moves.

**⚠ THE TEST, and it is the operative part: WOULD THIS SENTENCE BECOME FALSE IF THE CANONICAL
STATEMENT CHANGED?** If yes, it is a copy — replace it with a line plus a pointer. If no, it is a
consequence and it belongs where it is.

**Measured 2026-08-15 — this is not hypothetical.** `l_inf`'s docstring is already canonical by
adoption: **25 sites depend on it**, six build-script changelogs call it *"the designated honest
stopping point"*, and four retraction commits were written against it as their anchor. **But 10 of the
25 PARAPHRASE it** — *"`l_inf`'s docstring states that the step … is an ontological bridge"* — and a
rewrite of the docstring **falsified four of them immediately**. Ledger: `BLAST-1`, `OCC-2`.

⚠ **A canonical statement can have a copy that can NEVER be updated, and that must be recorded rather
than discovered.** `scripts/build_zpc.py:142` reproduces this docstring's closing paragraph, rendered
into **ZP-C v1.21 — already deposited with a Zenodo DOI.** The build script can be converted so future
rebuilds point rather than copy; **the deposited PDF is frozen and always will be.** That is correct
behaviour for a snapshot, and it means *"one canonical definition everywhere"* has permanent
exceptions. Name them at the canonical site.

**Rollout is AS-TOUCHED, never big-bang** — the same model as the file-path citation convention. A
25-site conversion in one round is the shape that generates new defects; 2026-08-15 is the evidence.

### And the pointer must not become a COPY. Never enumerate in prose what the artifact defines.

**A pointer that re-lists its target's contents is a second copy of the definition, and a second copy
drifts.** This is the general form of a rule this file already states three times for three specific
figures — the choice-footprint count ("NO COUNT — measure on demand, never record one"), the
`papers/` file count, and the `LEAN_CUSTOM_REGISTRY` tally. It is one rule, so state it once:

**Do not write into prose any count, tally, field list, instance list, or "these are the N conditions"
enumeration of something a Lean file, a directory, or a data store already defines.** Point at it, name
the one or two members that are load-bearing for what you are saying, and let the reader open it.

**Measured 2026-08-04 — the same defect twice in two rounds, one level apart, in the same paragraph.**
A pointer block added to `ZeroParadox/Valuation/PoleCornersBridge.lean` said `InfinitudeFloor` had
**four** realizations (there are five — `boundaryFloor` was missed) and, after that was fixed, said the
class had **two** conditions and that this "is the whole requirement" (it has three, and the dropped
`cx_floor_eq_iSup` is the load-bearing one, the field the headline theorem rewrites with first). Both
are the same error: **a completeness claim about an artifact's contents, asserted in prose that cannot
check itself** — in a file whose entire job was to POINT AT that artifact.

**Why enumeration specifically, and not just counts.** A count at least looks like a figure and invites
the "measure it" reflex. A field list reads as *description* and invites nothing, which makes it the
more dangerous of the two. Both are completeness claims; neither is checkable from where it is written.

**What IS legitimate to write down:** a **dated survey result** — "realizations located as of
&lt;date&gt;: …" — because that is a measurement, not a re-copy, and the date says so. Same for
"none located as of &lt;date&gt;" over "none exists" (§ the choice index's universal-negative rule).
The distinguishing question: *would this sentence be wrong if someone added a field tomorrow, with
nothing mechanical noticing?* If yes, it is an enumeration — replace it with a pointer or a date.

## Determinism is the SINGLE recurring cost — name it, don't rediscover it

**Every "the bottom cannot move" result in this corpus is powered by SINGLE-VALUEDNESS, not by
self-reference.** This surfaced four separate ways in one session (2026-07-30) and was re-derived each
time, so it is written here rather than left to be found five sections into a file:

- `machine_snap_impossible` — nothing is both its own fixed point and departed from. `Occurrence.lean` § VI
  states the diagnosis: *"the obstruction of § III is the absence of fan-out, not the presence of a fixed
  point."*
- `deterministic_has_no_fanout` — a function `σ → Option σ` admits at most one successor. That is the
  whole obstruction.
- `nondeterministic_escapes_the_trap` — a **relation** can loop at `s` *and* reach elsewhere. That is the
  whole escape.
- `execution_requires_branching` — stated over a **relation** for exactly this reason.

**The consequence to carry into any prose about the trichotomy:** halted / self-looping / stepping-onward
are three distinct **states** under any dynamics, but under a **function** the first two share a **FATE** —
`loop_is_a_trap` and `eval_of_halted` each give a singleton reachable set. The trichotomy is genuinely
three-valued **only** in the non-deterministic setting; make the step single-valued and the self-loop is a
relabelled trap. So **"could it still move?" is a MODAL question, and the function-vs-relation choice is
how the framework encodes that modality WITHIN the trichotomy.**

⚠ **It is not the only encoding, and "nothing else" is too strong** — the corpus's own counterexample is
`carry` (§ VI-c, `ZeroParadox/Computability/Occurrence.lean`): a **function with no fixed point anywhere**
whose observable projection never changes. `LoopsInPlace` demands the state return to *itself*, so adding
any accumulating component leaves no fixed point at all and `machine_snap_impossible` does not apply —
yet nothing observable moves. The separation being made is **the state moving** versus **the observable
changing**, which is a question about a quotient rather than about determinism.

**Do not re-derive this, and do not attribute the obstruction to the fixed point.** The self-loop is not
what blocks departure; being a function is. Note also what it is NOT: this says nothing about whether the
bottom *does* move. Non-determinism buys the *possibility* and never the *occurrence* — see `l_inf`'s
docstring, and `tri_idle_never_starts`, where a perfectly well-formed third state sits inert forever.

## The Two-Pole Test — Hard Rule. Run BOTH readings of ⊥ concurrently, never one.

**⊥ = 0 = ∞ is the framework's own pole identity (`rInv_swaps`). So every face of ⊥ has TWO readings —
the EMPTY one and the INFINITE one — and a face that implements only one is half-built.** Build and check
both concurrently. Do not sequence them, and do not treat "which first?" as a real question: the poles are
one object seen from two ends, so picking one builds half and forces a later switch.

**The test, run on every new development and on any face that is stuck:**
- **Q1 — where is the zero that runs to infinity?** (valuation, frequency, surprisal, self-reference…)
- **Q2 — what is the one-way arrow, and what does it look like run backwards?** (reversal is the
  *inversion*, never a second construction.)

**If either has no answer, the piece is not part of the framework yet, or its floor has not been found.**
That is a finding, not a stall — record it.

**The measured case that made this a hard rule (2026-07-26).** ZP-K's computational bottom is
`MachinePhase.initial`, whose own comment reads *"machine exists; no instruction fetched"* — a pure EMPTY
reading, with no infinity in it. **Q1 has no answer there**, and the test was never run. The consequence
was not cosmetic: because a machine that has fetched nothing has no reason to fetch anything, the claim
that ⊥ *executes itself* needed an ontological bridge, and that bridge is a commitment rather than a
theorem (see `l_inf`'s docstring, which says so honestly). **The INFINITE reading of the computational
bottom is divergence — the non-terminating computation — which does not need starting because it is
already running.** The occurrence problem is an artifact of implementing one pole.

**The diagnostic value, stated generally:** when a claim will not close, or a face needs an extra
assumption to work, **first check whether only one pole has been built.** A missing pole shows up as a
bridge you cannot formalize.

### The test applies to METHOD, not only to objects (Tim, 2026-08-07)

**A search that implements one polarity is a half-built detector, for exactly the reason a face that
implements one pole is half-built.** Tim, on being shown that four of five false negatives in one
session were one grep away in the opposite polarity: *"that polarity is the nature of the project — I
feel like every instance we can have will have that structure."* He is right, and **Q2 above is already
that question**, asked of a construction rather than of a search: *what does the one-way arrow look like
run backwards?*

**So run the test on the METHOD:**
- **Q1-M — what would this claim look like stated from the other side?** *"Seed-independent"* and
  *"⊥ is **a** seed, not a distinguished one"* are one fact. *"Converges"* and *"diverges"*. *"Is
  used"* and *"has no call sites"*. **Search both, or you have searched half.**
- **Q2-M — if the corpus disagreed with me, what words would it use?** That phrasing is where a
  contradicting result is sitting, and it is the phrasing you will never reach from your own.

**Measured, same day:** `seed-independent` → 0 hits; the inverse `"a seed, not"` → the section that
already proved it, by Tim, eight days earlier. `atTop (nhds _)` → 13 convergent files; the inverse
`atTop atTop` → the divergences, in files the survey never saw. Both had already shipped into docstrings
as measured fact. See § *NOT IN THE LIBRARY IS A CLAIM* step (c) for the operational form.

**⚠ Where it STOPS, and the framework already names the exception.** *"Every instance"* is the right
instinct and needs one qualifier the corpus itself supplies: the fifth POV KIND, **INVARIANT** — *"the
quantity does not transform; flipping the chart gains nothing."* That is the ratified slot for polarity
**not** applying. Four of the five KINDs are two-sided (COINCIDENCE, INVERSION, DRIFT, CARRIER); the
fifth is the null case. **So: expect polarity, and when flipping genuinely gains nothing, say INVARIANT
rather than forcing a second pole.** A rule that fires everywhere is the cry-wolf shape this file
elsewhere says to narrow rather than tolerate.

**Why this is here and not only in memory.** It *was* only in memory
(`feedback_two_part_lens_call_out`), where the body does not load — only the one-line index entry does,
competing with ~100 others. It did not fire for months. Per this file's own rule: *memory is for context,
not enforcement.* The memory keeps the full lens (the which-first corollary, the external-evaluation
corollary, and the call-out protocol for where Tim's human read is load-bearing); **the binding
obligation is here.**

**Call-out protocol (retained from the memory, still required):** when development turns on this lens —
a floor to locate, a reversal to characterize, a 0↔∞ swap — say so explicitly and flag it as needing
Tim's read rather than guessing; and when his input on such a point proves load-bearing, name what it
changed instead of presenting the result as self-derived.

## Prose that resists correction is a CLAIM defect. Revalidate, don't redraft. Hard Rule.

**If a sentence has to be fixed three times, the sentence is not the problem.** Stop editing it and go
measure the claim underneath. This is gate-enforced: `gate_round.py` prints a MANDATORY CLAIM
REVALIDATION protocol at **round 3**, or as soon as the **same `--target` has been re-fixed 3 times**.

**Why, in one line: the gates check WORDING against SOURCES. They cannot see an unmeasured claim, and
they will keep passing one forever.** Measured 2026-08-03 — one ZP-P sentence was wrong in six
consecutive versions and four gate rounds passed it, because the citations were always correct and the
claim underneath had never been measured by anyone. Six rounds of prose editing could not find it. One
probe did, in a minute.

**⚠ MODAL CLAIMS ARE THE HIGH-RISK CLASS — and this corpus is full of them.** *"not a necessity"*,
*"an artifact"*, *"in principle"*, *"could be removed"*, *"eliminable"*, *"inherited from Mathlib"* are
claims about what **cannot be proved**, and a footprint measurement can never establish one:
- **ACCIDENTAL** is proved only by **EXHIBITING** the clean proof.
- **ESSENTIAL** is proved only by a **REDUCTION** to a taboo.
- **`#print axioms` follows the STATEMENT, not the proof.** A *type* can carry an axiom — then no
  proof is clean, and every "removable" claim about it is false. **Measure the type, not just the
  theorem.**

**The protocol, when the tripwire fires:** name the claim in one line without its framing → ask what
would settle it and whether anyone did that → probe it in the scratchpad (`lake env lean` on a
standalone file needs no repo write) → then either restate to exactly what was measured, or restate as
an explicit conjecture, **or delete the sentence**. **Deleting is legitimate and often correct**: if an
accurate statement already lives in a checkable file, published prose does not need to relitigate it —
that is how the ZP-P case was finally closed (v1.16, Tim: *"if the Lean is accurate, just delete the
problem sentence"*).

**Record what the MEASUREMENT showed, not that you re-worded something.** A changelog entry saying
"clarified" after a revalidation round is the failure repeating.

📖 **THE CASE, THE DETECTOR AND THE MEASURED FOOTPRINTS — `tools/process/claim-revalidation.md`.**
The ZP-P arc in full; `check_modal.py`'s three false-negative paths, **every one found by running a
probe rather than by reading the code**; and the axiom-footprint table that must be read whole (*"`PFunctor.M`
is axiom-free"* is true of the type former and false of its destructor, and that half-truth shipped to a
published PDF under the word *"Measured"*). **Read it before believing a checker's zero, and before
writing "removable" about anything.**

## "NOT IN THE LIBRARY" IS A CLAIM. Probe it before you believe it. Hard Rule.

**The characteristic error of 2026-08-04 was not a wrong theorem. It was three wrong NEGATIVES**, each
of the form *"X is not available"*, each recorded as measured, each false:

| the claim | what was actually there |
|---|---|
| *"`pole_inversion` is not available on `ℤ_[2]`"* | true of the class instance, **false of the content** — both halves of the drift were already proved (`towerCx_zero`/`towerCx_member`, `tower_converges_to_zero`); only the packaging was missing |
| *"`WellPowered (Type 0)` does not synthesize"* | `instance : WellPowered.{u} (Type u)` sits in a module **titled** *"`Type u` is well-powered"*; the probe failed on an unimported name and an **unresolved universe parameter** |
| *"AMM Def 2.14 clause (c) is not a Mathlib concept"* | **derivable in six lines** — `IsStableUnderColimitsOfShape.condition` already has that exact shape; instantiate its second diagram at the constant functor |

**A failed `#synth` is EVIDENCE ABOUT YOUR PROBE, not a fact about the library.** It has at least four
innocent causes, and all four were hit in one day:
1. **Not imported.** `unknown identifier` and `failed to synthesize` look alike in a hurried read, and
   `Mathlib.Tactic` does not reach most of `CategoryTheory`.
2. **Universe parameters.** `WellPowered (Type 0)` fails; `WellPowered.{u} (Type u)` succeeds. An
   unresolved metavariable in the goal is the tell — read it.
3. **A different name.** Grep the CONCEPT, never the name you would have chosen.
4. **Decomposed into parts.** The thing is not absent, it is *assembled from* pieces that are present —
   the clause-(c) case, where a three-clause definition had two clauses as instances and the third as a
   short derivation. **A definition can be available without any declaration bearing its name.**
5. **GENERATED BY AN ATTRIBUTE, so it has NO SOURCE LINE AT ALL.** Mathlib's `@[to_dual]`, `@[simps]`,
   `@[mk_iff]` and friends synthesise siblings that grep can never see. Measured 2026-08-08:
   `OrderDual.toDual_bot` appears in **no source line anywhere in Mathlib** — only its dual
   `toDual_top` is written out — and `#check @OrderDual.toDual_bot` resolves it instantly. It cost
   **three probes across two agents** before anyone got it. **grep is not the authority; `#check` is.**

**The rule.** Before writing *"not in Mathlib"*, *"the corpus does not have"*, *"no instance exists"*, or
any dated survey negative: **(a)** confirm the name is imported and elaborates at all, **(b)** re-run
with universes explicit, **(c)** **run THREE phrasings, and make one of them the INVERSE** (see below),
and **(d)** ask whether it decomposes. Then write **"not located as of &lt;date&gt;, searched as
follows"** — never *"absent"*.

### (c) in full — THREE PHRASINGS, AND THEY MUST VARY ALONG AXES, NOT BE SYNONYMS. Tim's rule, 2026-08-07, measured three times the same day.

*"Grep the concept in two vocabularies"* is the right principle and fails on its own, because it says
nothing about **which** — and three synonyms of one formulation are one search run three times.
**Vary along the axes below. Each has its own measured false negative from a single session.**

| axis | run BOTH ends | the failure it prevents |
|---|---|---|
| **1. POLARITY** | the claim / **its inverse** — how the corpus would say it if it *disagreed* with you | you find only the half stated your way |
| **2. PART OF SPEECH** | the **noun** (the object) / the **verb** (the operation that produces it) | you search for the *thing* and miss the *step that makes it* |
| **3. VOCABULARY** | your words / the **domain's** words | you find only what you would have named it |
| **4. DISPLAY** ⚠ | the full matched line / **what you actually printed** | the query was right, the match was there, and you **truncated it off the screen** |

⚠⚠ **AXIS 4 IS NOT ABOUT THE QUERY, WHICH IS WHY THE OTHER THREE CANNOT CATCH IT.** Axes 1-3 all
assume the failure is in what you *asked*. Here the query was correct, the pattern **did** include the
term, the file **was** in the result set — and the term sat past the character limit of the formatting
applied to the output. **Absence was read off a line that contained the thing.**
**Measured 2026-08-12**, and it produced a note, a handoff entry and a spoken claim all asserting a
gap that did not exist: a search for `Γ₀|Feferman|Schütte` matched `Ordinal/Epsilon0CannotBe.lean:79`,
whose gloss ends *"coords (1,0), the minimum closure, **below Γ₀**"* — at roughly character 110 of a
line printed to 90. `Ordinal/Epsilon0LeastFP.md` states the entire Veblen ladder up to Γ₀ and
`SnapNucleusConstructive.lean` references `epsilon_zero_lt_gamma`. **The corpus was ahead of the
search, and the deliverable dissolved.**
**THE RULE: never conclude absence from truncated output.** Re-run untruncated — or print
`file:line` only and open the hits — **before writing any negative.** This is § *NOT IN THE LIBRARY IS
A CLAIM* applied to your own terminal: **a formatting choice is a filter, and an unexamined filter is
a blind half.** ⚠ It compounds with `head_limit`/`-First N` caps, which drop whole *rows* the same way
this dropped whole *columns*.

**Measured, all on 2026-08-07, all having already shipped into docstrings as fact before a gate or Tim
caught them:**

| axis | the claim | what was run | what should have been run |
|---|---|---|---|
| POLARITY | *"the corpus never measured seed-independence"* | `seed-independent` → **0 hits** | `"a seed, not"` → lands directly on `Epsilon0MinMax.md`, which states the theorem, the proof route, and the verdict *"Elementary and not novel"* |
| POLARITY | *"every `Tendsto` in the corpus runs inward"* | `atTop (nhds _)` → 13 files, all convergent | `atTop atTop` → the divergences, immediately, in files the survey never saw |
| **PART OF SPEECH** | *"the succession of bottoms is not formalized"* | the NOUN — `family of bottom`, `botSeq`, `ℕ → .*Bot` → nothing | the VERB — `next bottom`, `re-seed`, `succ` → **`succession_succ`**, the n → n+1 re-seeding theorem, which had been there all along |

**⚠ The part-of-speech axis is the newest and was the most expensive**, because it produced a *published
note* asserting a formalization did not exist. Tim: *"you need to look closer at n and n+1 logic. we very
likely already have this belt."* **A corpus names an operation and a thing differently, and formal corpora
overwhelmingly declare the OPERATION** — `succession_succ`, `snapNucleus`, `nfp` — while prose about them
uses the noun. **If you are asking whether a structure exists, search for the step that builds it.**

**Why the inverse specifically.** A corpus records a fact in whichever polarity its author found natural,
and that is frequently the opposite of yours. *"Seed-independent"* and *"⊥ is **a** seed, not a
distinguished one"* are the same fact; only one of them is greppable from the other. Likewise
*"converges"* / *"diverges"*, *"is available"* / *"cannot be stated"*, *"is used"* / *"has no call
sites"*. **A single-polarity grep is a detector with a blind half**, and this file's own
*"VERIFY THE DETECTOR BEFORE BELIEVING A ZERO"* applies to it.

**A bonus worth expecting:** the inverse grep surfaces the corpus's *idioms*. `"a seed, not a
distinguished one"` also returned `Computability/Kleene.lean`'s *"computational quine, not a
distinguished one"* — the same sentence shape used for a different object. Finding the idiom is how you
find the other places the claim is made.

**The generalization, now that there are three axes:** a search is a **projection**, and a projection
loses whatever is orthogonal to it. Polarity, part of speech and vocabulary are the three projections
this corpus has actually been caught by; there is no reason to think they are the only three.
**When an absence matters, ask what dimension your query collapsed** — and note that this is the
Two-Pole Test again (§ above), which is itself a rule about never looking from only one end.

**Why this is its own section and not a footnote.** This file already says
*"VERIFY THE DETECTOR BEFORE BELIEVING A ZERO"* — but scoped to `check_modal.py`, so it did not fire for
`#synth`, and the identical failure recurred three times in one day. **The generalization is the point:
any tool that reports absence needs its absence-reporting verified before the absence is believed.**
It also compounds: each false negative was written into a docstring as a *measured* fact, which is the
`CannotBe`-index universal-negative hazard arriving through a new door.

**And the payoff for checking is real, not just defensive.** Correcting the three negatives above turned
"one of four hypotheses holds" into "three of four", and put an instance-of claim the corpus had twice
withheld back within reach. **Searching harder gets you MORE** — the same lesson as Trigger 0.

## Review-Loop Cap — Severity-Tiered, Hard Rule

**The gates will always find something. Stopping is a decision about SEVERITY, not a wait for silence.**

⚠ **THE NUMBERS BELOW ARE A HUMAN-READABLE ECHO. `tools/verify/gate_round.py` IS AUTHORITATIVE**
(`BEDROCK_CAP` / `ORDINARY_CAP`), and `gate_round.py show` prints the current round beside both caps.
**Change a cap THERE, in one place, and never here alone** — this paragraph is prose and cannot check
itself. The four gate briefs used to restate the figures too; as of 2026-08-15 they instruct the
reviewer to run `show` and obey it, so a cap change no longer has to be chased across five files.
**What stays written out everywhere is the SEVERITY TIERING below, because that is semantics a
reviewer must act on rather than a number that drifts.**

- **BEDROCK severity → up to 5 iterations.** A violated core invariant (`ε₀ ≠ 0`, `ε₀ ≠ ⊥`, min≡max
  flattened, the snap-arc returning to the same ⊥, a cross-type `=`), a **fabricated** claim about an
  external source, or a false premise carrying a conclusion. These must not ship — keep iterating.
- **ORDINARY severity → 2 iterations, then STOP and push normally.** Citation scope, a mischaracterized
  lemma, hedging a tier too strong, path-convention drift, wording. These never reach zero.

**The stopping question is "did this round find anything BEDROCK?" — if no, stop**, even on ten ordinary
findings. Ratified 2026-07-19 after three rounds; memory `feedback_er_ar_max_iterations` carries the
detail.

**⚠ NO `--no-verify` IS INVOLVED AT THE CAP.** A **STOP-ORDINARY reviewer WRITES ITS SIGNAL**, so the
hook clears **on its own merits** and there is nothing to bypass. Put it in the brief:
*withholding the signal on ordinary findings is not a valid outcome.*

**⭐ AND FIXING A FINDING RESTARTS THE OBLIGATION FOR THE TEXT YOU CHANGED.** The cap's licence assumes
the outstanding findings *stay outstanding*; once you have **acted** on them the push contains **new
unreviewed prose**, which is a different thing from known debt and warrants a gate rather than a flag.
**So: edit after a STOP-ORDINARY ⇒ re-sign. Do not want another round ⇒ do not edit** — record the
findings as next-touch debt and push what was actually certified. Measured 2026-08-01: four of the
next round's six editorial findings landed in the one file no gate had yet seen, which existed only
because it was edited after the gates finished.

### Prose about PREVIOUS STATES is redundant. Git holds it. (Tim, 2026-08-08.)

**This project already ratified the argument, for documents, and never applied it to prose.** The
`historical/` folder was retired because *"git history and each release's Zenodo snapshot are records
more complete and authoritative than a hand-maintained archive"* — the archive drifted a month out of
date; those do not. **A retraction record in a docstring is a hand-maintained archive of prior
states.** Same object, same failure mode.

**Measured 2026-08-08: 87 lines across 39 `.lean` files** carry prior-state prose (*"an earlier
draft"*, *"was FALSE"*, *"is retracted"*, *"previously read"*, *"until 2026-…"*). **The distribution
is the finding** — the top six are the files most recently through the gate loop. This prose is not
spread through the corpus; **it is what the review loop deposits**, and nothing prunes it.

**The cost is not tidiness.** In one three-round arc the correction layer grew to ~40% of a 96-line
section guarding **two** declarations, and **generated a new defect in every round** — including a
retraction that misdescribed its own subject, and a "corrected" claim (*"proved by `funext`, not
`rfl`"*) that a gate refuted by running it. **Records about records are unverifiable by construction
and nothing checks them.**

**THE RULE — apply the strip test.** Remove the *"an earlier draft said X, which was wrong"* framing
and read what is left:

* **Something remains, and it is MATHEMATICS** — then that is **content**, and its provenance in an
  error is irrelevant. **State it positively and delete the framing.** Worked examples from that arc,
  all worth keeping and none needing a retraction to say: *`deriv` is not `nfp`, and here is the
  counterexample*; *ε₁ is a fixed point, so it is the one seed that makes the wrong reading look
  supported*; *an all-zero prefix names the same end, so the discriminator is a nonzero digit.*
* **Nothing remains but history** — **delete it.** `read(op='log', args=['-p','--','<path>'])` has it, exactly, permanently, with
  provenance no docstring can match.

**Where history actually belongs:** `.claude-local/DEFECTS.md` while a defect is open, the
gate-findings archive once it is closed. Both are read when choosing work; a docstring is read when
doing mathematics. **The defects that recurred despite earlier fixes did not recur because a docstring
lacked a retraction — they recurred because the ledger was not consulted.**

**YES, THIS MEANS FIX IT SILENTLY — in the file** (Tim asked directly). **Delete the false claim,
state the true one, and let the COMMIT MESSAGE be the narrative.** That is its job, it is versioned,
and it is where a reader looking for history will actually go.

**The record is never lost, because it lives in three places that are not the docstring:** the commit
message, `.claude-local/DEFECTS.md` while the defect is open, and the session itself. **The only thing
being removed is a fourth copy — the one that cannot be checked, drifts, and accumulates.**

⚠ **The narrow thing that is NOT permitted:** letting a fix be invisible **everywhere**. Do not skip
the ledger on an open defect, do not bury a substantive correction under a vague commit subject, and do
not decline to surface it — cross-arc patterns are caught by the human, repeatedly and by measurement,
and he cannot catch what he is not told. **Silent in the artifact, recorded in the process.**

⚠ And this does not touch the dated-survey convention (*"none located as of &lt;date&gt;"*), which
records a **measurement**, not a prior state.

📖 **ROUND MECHANICS AND THE VERBATIM BRIEF BLOCK — `tools/process/review-loop-cap.md`.** Who bumps
the counter and who may only read it; `--target` slugs; and the block that goes into **every** review
brief with N substituted. **Open it before spawning any gate.** Why it matters: a rule about a loop
does not fire from inside the loop — on 2026-07-19 three rounds ran against a 2-round cap because
nobody was counting, and a reviewer that bumped the counter itself burned the cap a round early.

## NEVER truncate the output of a hook-running command, and NEVER write a `--no-verify` fallback. Hard Rules.

**TRIGGER — an action: you are about to put `| head`, `| grep -q`, `| grep -m`, `| sed q` or any
early-exiting consumer around a command that runs a git hook, or to write `|| git push --no-verify`.**

- **Redirect, do not truncate.** `python tools/verify/batch.py prepush > prepush.log 2>&1; echo $?`,
  then read the log. (`tail` reads to EOF and is safe; the rule covers everything anyway, because you
  should not have to remember which consumers exit early.)
- **`--no-verify` is a separately-typed decision, never a fallback and never chained with `||`.** The
  one documented case is a `CLAUDE.md`-only change against a stale signal.

⭐ **HALF OF THIS IS NOW STRUCTURAL, AND HALF IS NOT — KNOW WHICH.** Since 2026-08-22 a push goes
through `gitRobot`, which **never passes `--no-verify` and has no parameter that reaches it**, so the
second bullet can no longer be violated by an agent even deliberately. **The first bullet still binds
with full force**, because the commands you truncate now are `batch.py`, `lake build` and the
checkers — and `| Select-Object -First N` breaks a PowerShell pipe and reports a wrong exit code
exactly as `| head` did. **The SIGPIPE hazard moved; it did not go away.**

**⚠ THE COST, AND IT IS WHY THESE ARE HARD RULES: BOTH BYPASSES SUCCEED SILENTLY — THE PUSH LOOKS
GREEN.** Measured 2026-07-26: the identical push exited **1** (blocked) bare and **0** (pushed)
through `| head -5`, because `head` closed the pipe and the hook died of `SIGPIPE` before reaching
its `exit 1` — and the review-signal check runs **last**, so any truncation short enough to be
useful is long enough to skip it. A twelve-file push with a stale `pa_cleared.txt` reached `origin`
that way. The `||` fallback is the same failure written down on purpose. **If a push is blocked,
read the reason and fix it — the block is the control working.**

📖 **THE MEASUREMENTS, AND WHERE THE DEFENCE ACTUALLY LIVES — `tools/process/push-gate-bypass.md`.**
The immunity is in `tools/verify/hooks.py`, **not** a `trap '' PIPE` in `.git/hooks/pre-push` —
a reader who greps for `trap` will not find it and could conclude the defence was dropped. Install
per clone with `python tools/verify/install_hooks.py`; `--check` exits 1 when the gates are not
armed. **Read it before assuming the clone you are standing in is protected.**

## Staging — NAMED PATHS, never `-A`. ⭐ NOW MECHANICAL, not remembered. (2026-08-22.)

**Bulk staging takes whatever happens to be in the tree, including files this session did not create.**

**Measured 2026-07-19:** a background review agent wrote a scratch probe into `ZeroParadox/`, and the next
bulk add swept it into a commit unnoticed. It is in the permanent history now. Background agents run
*concurrently* with commits, so the working tree is not a stable snapshot of what you intended to change.

**The rule:** stage the specific paths you edited — `stage(paths=['a.lean','b.md'])`. Before committing,
`read(op='status', args=['--short'])` and confirm every staged path is one you meant to touch. If a path
appears that you did not edit, find out where it came from before committing it.

⭐ **THIS IS THE EIGHTH CONVENTION IN THIS FILE TO STOP BEING A DISCIPLINE AND START BEING A GATE, AND
IT IS THE ONE TO COPY.** `gitRobot.stage` has **no bulk form on the main repo** — `-A`, `.` and `-u` are
refused, with the reason and the alternative in the refusal text. There is nothing left to remember and
nothing to adjudicate. The old escape hatch (*"`-A` is acceptable when nothing has been spawned since the
last commit"*) is **gone**, and it should be: it was a judgement call at exactly the moment a session is
least able to make it.

⚠ **`.claude-local` is exempt and bulk staging is its documented flow** —
`stage(paths=['-A'], repo_mode='.claude-local')`. Different repo, different risk: nothing published, and
the failure mode there is losing notes rather than shipping a probe.

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
4. If PASS: the agent writes `.claude-local/er_cleared.txt` recording the SHA-256 of each reviewed file (see the SHA-256-per-file scheme below) — proceed with the commit

Same-session self-review does not satisfy this requirement. `/editorial-review` spawns a fresh agent with no conversation history.

The pre-push hook validates `.claude-local/er_cleared.txt` and `.claude-local/ar_cleared.txt` (and `pa_cleared.txt` on a `.lean` trigger) using the **SHA-256-per-file scheme** (2026-07-20): each signal records the content SHA-256 of every file the review certified (line 1 = verdict record; lines 2+ = `<sha256>  <path>`), and it is valid iff (a) every recorded file still hashes to its recorded value and (b) every *reviewable* file in the push is covered by a recorded hash. Reviewable = changed files minus pure data/binary (`ssot.json`, PDFs, images, lockfiles), so a data-only commit no longer stales a review — that was the old HEAD-equality scheme's failure mode. If nothing reviewable changed, no signal is required. `--no-verify` should now be genuinely rare; if a signal is stale it is because a reviewed file actually changed (re-run the review) or a new reviewable file is uncovered.

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
4. If PASS: the agent writes `.claude-local/ar_cleared.txt` recording the SHA-256 of each reviewed file (see the SHA-256-per-file scheme below)
5. Only after explicit confirmation may the public-facing action execute

Same-session self-review does not satisfy this requirement. The review must be a separate adversarial context (spawned Agent with no conversation history).

**What triggered this rule:** Lean docstring and build script prose changes were pushed on 2026-05-20 before adversary review ran. The review subsequently found two additional precision errors in the already-committed content.

## Prior-Art Search — Trigger Conditions and Gate

The framework's value is its *delta* against prior art, so an uncited closest-prior-art reads as "unaware" — the crank-triage failure mode. **It BLOCKS at push:** the adversary gate detects synthesis-layer content and withholds `ar_cleared.txt`, and the pre-push hook checks `pa_cleared.txt` directly on trigger 5.

### ⚠ TRIGGER 0 — SEARCH BEFORE YOU BUILD. Hard rule, and it is the cheapest one here.

**If you can state the claim in one sentence of standard mathematical English, search for it BEFORE
writing Lean.** Not after. The post-hoc gate still runs; this sits in front of it.

**⭐ THE POINT IS NOT EMBARRASSMENT-AVOIDANCE — SEARCHING FIRST GETS YOU MORE.** Measured 2026-07-27
across three findings in one day, it would have handed us a **stronger** theorem than our own claim
(a biconditional), a **purer** proof (function extensionality where ours took `Classical.choice`),
free analyticity lemmas, and the standard NAME for a thing described longhand.

**The three-step check, ~10 minutes:**
1. **Grep our own corpus.** The cheapest miss, and it happened three times in one day.
2. **Grep the pinned Mathlib for the CONCEPT, not the name you would have chosen — and ⚠⚠ IF THE
   CLAIM IS A LEAN STATEMENT, RUN `exact?`.** It beats grep and is the only step here whose verb is
   **RUN**: grep searches *names*, `exact?` searches *statement shape*, so it finds the lemma whose
   name you would never have guessed, and it reaches the attribute-generated siblings (`@[to_dual]`,
   `@[simps]`) that have **no source line to grep**.
3. **One literature search** if the object has a name. **`.claude-local/papers/` FIRST** — it is the
   downloaded-source library, and a scout once declared Aczel unobtainable while it sat on disk.

**⚠ AND WHEN YOU FETCH A SOURCE, FILE IT** — `.claude-local/papers/`, named
`author_topic_year[_id].pdf`. **Validate before filing** (a tiny PDF is an error page, not a paper).
**Never record a file count** — measure it. **Grep loosely**: scanned books are OCR'd with spurious
intra-word spaces, so a tight-pattern miss is not evidence of absence. **Carry both halves — check it
first AND file what you fetch — into every scout brief.**

**The exception, and it is real:** if you *cannot* yet state the claim in one sentence, building is
how you find the shape and searching returns noise. Build, then **search before promoting** — and
that second half is the one that gets skipped. **When a survey turns into a theorem, the prior-art
clock restarts**; the search that justified the investigation does not cover the mathematics that
came out of it.

**Standard framing, once found, is ADOPTED — not noted and worked around** (Tim, 2026-07-27:
*"anytime that we have official framing we need to make use of it"*). Keep the framework's own label
as the handle where one exists; take the library's lemmas. ⚠ **Check purity before swapping a
proof** — one adoption pushed a `[propext]` theorem to full choice, so the hand proof was kept and
the standard name cited instead.

**Trigger conditions:**
1. **A new synthesis/bridge layer is created** — prior-art search before its first push. (Highest yield; every gap found in the 2026-06-22 arc originated at layer creation.)
2. **A synthesis layer's central/distinctive claim is revised or strengthened** — re-run for that claim.
3. **A layer is prepared for outreach or arXiv** — prior-art search is part of the pre-flight, beside the adversary pre-flight.
4. **Reactive:** an external reviewer asks "have you seen X?" — search, then add the result to the CLAIMS "Convergence with established work" table with attribution.
5. **A new `.lean` file, or a large net addition to one** (≥50 net `.lean` lines) — a substantial original *construction* is in-scope even if it is not a cross-field synthesis claim. This is the mechanical complement to synthesis-detection, and what would have caught ZP-D's `T` (the van der Put / Kozyrev ball-indicator ONB).

**`/prior-art-review` is the deep gate**, a fresh-agent scout — same-session self-review does not
satisfy it. On PASS it writes `.claude-local/pa_cleared.txt`. **The record:** the CLAIMS "Convergence
with established work" table is the public ledger; `.claude-local/notes/prior_art_*` holds the
per-search findings.

📖 **THE MEASURED CASES, THE THREE STEPS IN FULL, AND HOW THE GATE RUNS — `tools/process/prior-art.md`.**
What each of the three 2026-07-27 findings cost, the `exact?` case that corrected the mathematics and
not just the line count, the 19 abandoned PDFs, the survey-became-a-theorem case, and the scope rule
that decides whether a layer triggers at all. **Read it before writing a scout brief or arguing that
a layer is out of scope.**

## Guiding Principles (from Project Instructions)

- **Logical Rigor First:** The primary goal is logical consistency and rigor. 
- **Prose Role:** Use prose only to restate mathematics into accessible language. 
- **Ontology Focus:** Finalized documents must be structured as an ontology. 
- **Persistence:** All completed work must be committed back to the repository immediately to prevent data loss.

## Repository Nature

This is a **mathematical publication repository** first. It is no longer true that there is "no build system, test suite, or source code" — there is a Lean 4 corpus with CI, and as of 2026-08-15 a tracked verification suite — but the PDFs and the Lean remain the point, and the tooling exists to keep them honest. The repository contains:

- PDF documents (the formal mathematical framework and illustrated companions)
- The Lean 4 corpus under `ZeroParadox/`, with `MANIFEST.md` as its by-folder index
- Markdown documentation (README.md, ABOUTME.md, this file)
- (superseded document versions are preserved in git history and per-release Zenodo snapshots; the `historical/` folder was retired in v3.0)
- `scripts/` — the PDF build tooling. Their only home since 2026-08-15, not a transparency mirror
- `tools/verify/` — the checkers, pipeline and baselines that gate every commit and push
- `tools/registry/`, `tools/render/` — the declaration extractor and the diagram generators

## Private Working Folder

A `.claude-local/` folder exists locally. **It is its OWN git repository** — its own history, a `master` branch, and a private remote (`ZeroParadoxLocal`) — and the public repo additionally ignores that path, so none of it appears here. This is intentional.

⚠ **"Gitignored" is the parent repo's view of it and is the wrong mental model to work from** (Tim, 2026-08-22). Ignored files are protected by nothing; a repository with a remote is protected by committing and pushing. Get this wrong and you conclude the only copy is on disk and that backing it up is someone else's problem — which is exactly what happened on 2026-08-22, when three commits sat unpushed while the `PostToolUse` robocopy that used to catch them had been dead since agents lost `git commit`. **Commit AND push it; the handoff's PART 0b step 4 is the procedure.** It serves as a private working space for the project's core collaborators during active development, before material is ready for public discourse. It contains:

- Reviewer feedback and correspondence (e.g. `feedback/`)
- In-progress build scripts and draft outputs
- Session notes and development artifacts

Transparency is a core value of this project. The existence of this private folder is acknowledged here precisely for that reason: readers of the public repo can see that private collaboration is occurring, understand its purpose, and know that the mathematical content and editorial decisions will be surfaced publicly as the work matures. Nothing in `.claude-local/` affects the formal mathematics — that lives entirely in the committed PDFs.

## Document Versioning Conventions

- Current documents live at the root with **flat (version-free) filenames**: `ZP-X_Title.pdf`
- Version numbers are tracked in `register.md` (Formal Version column) and in each PDF's title block — not in the filename
- Superseded versions are **not** archived to a folder (the `historical/` folder was retired in v3.0); the flat root PDF is overwritten in place, and git history + each release's Zenodo snapshot are the record
- README.md and GUIDE.md always link to the flat root filename

## GitHub Releases and Zenodo Snapshots

GitHub Releases trigger automatic Zenodo snapshots with permanent DOIs. `RELEASES.md` is the human-readable record of each release.

### Release naming

`v<major>.<minor>` - e.g. `v1.0`, `v1.1`, `v2.0`

### What triggers a release

- **Major version** (`v1.0 → v2.0`): a new formal layer added, or a theorem status changes (candidate → derived), or a significant structural revision to the framework
- **Minor version** (`v1.0 → v1.1`): a substantive reviewer feedback round addressed, or accumulated document/companion updates that represent a meaningful state of the framework

**Do not release on:** every individual PR. Releases should feel like milestones worth timestamping.

**Lean-only changes are an open question, not an automatic trigger (either way).** The release model is document-centric: `RELEASES.md` is built around a "Document versions" table, and the candidate→derived trigger above refers to *tracked, labeled* results in formal documents (carried in `register.md`), not to a placeholder proved only inside a `.lean` file. When a Lean milestone lands without accompanying formal prose (e.g. a conjecture proved only in Lean, no PDF document or companion moved), do not assume it warrants a release, and do not assume it doesn't - raise it as an explicit question for Tim. The two clean resolutions are: (a) bundle it into the next document release, or (b) write the result up as formal prose first, then release. Example: the wheel of fractions (§VIII conjecture → theorem, ZPJ_Wheel/ZPJ_WheelFrac) landed 2026-06-06 as a Lean-only change and was flagged, not auto-released.

### Release workflow

When Tim initiates a release: draft the `RELEASES.md` entry + `.zenodo.json` → PR → after merge, **run the Release-Readiness Gate (`check_release_ready.py <tag>` must exit 0) and confirm its judgment checklist** → draft the GitHub Release body → **wait for explicit approval** → execute:
```
gh release create <tag> --target main --title "<tag> - <title>" --notes-file ".claude-local\release_<tag>_body.md"
```
⚠ **THIS IS TIM'S COMMAND TO RUN, NOT AN AGENT'S — `gh` is denied for agents (2026-08-22).** That is
deliberate rather than incidental: `gh release create` mints a **permanent Zenodo DOI**, and a
permanent public act is not an agent decision. An agent's role ends at drafting the body and getting
the Release-Readiness Gate to exit 0. `gitRobot` can create the annotated tag (`tag_create`) but has
no way to push one and no release verb at all.
After release, confirm the Zenodo snapshot minted (query `https://zenodo.org/api/records/<conceptID>`). The README DOI badge is the **concept DOI** (`10.5281/zenodo.20060860`), which auto-resolves to the latest version — so **no per-release badge edit is needed** (confirmed v2.6, 2026-06-24). Only verify the snapshot exists; do not chase a badge update.

**Release-Readiness Gate — mandatory hard gate before drafting the release body / cutting any tag.** Run from the repo root:
```
python tools/verify/check_release_ready.py <tag>
```
It must **exit 0** before the release body is drafted. The script mechanically verifies the deterministic release preconditions and **exits 1 (NO-GO)** on any blocking failure: Engineer's Takes filled (no `TODO (Tim)` / `TODO: Engineer` / empty take section), build-script hash integrity vs `register.md`, the `LEAN_CUSTOM_REGISTRY` invariant (`### ` entries == `[ZP-CUSTOM]` tags), `.zenodo.json` valid JSON, no conflict markers in tracked files, a `## <tag>` entry present in `RELEASES.md`, and every README/GUIDE-linked PDF exists. It also prints WARN-level hygiene checks (register↔script VERSION, `scripts/` mirror currency, untracked root PDFs) and a **judgment checklist** of the non-mechanizable items (editorial/adversary/claim-review/prior-art ran on the PR; companion sync; major-vs-minor decision; release body approved). It **consolidates** the `.zenodo.json` and Engineer's-Take checks below (kept individually documented for context) and adds the rest. The gate cannot hook `gh release create` (no git event for tag creation), so enforcement is procedural: **the gate must exit 0 AND its judgment checklist must be confirmed before the release body is drafted.** Lives in `tools/verify/` — **TRACKED, alongside every other checker (2026-08-15).** This reverses the old rule that `check_*` dev tools stay gitignored and unmirrored: they are now tracked *in place*, which is not the same as mirroring them. There is one copy, it is the public one, and a checker edit is an ordinary reviewable diff instead of a change `git diff` could not see. Reuses `check_hashes.py` for register parsing. Spec: `.claude-local/notes/release_readiness_gate_2026-06-24.md`. (Added 2026-06-24 after `LEAN_CUSTOM_REGISTRY` went 18 days stale undetected at the v2.6 threshold — the scattered-checks model let it slip.)

**`.zenodo.json` check — mandatory before every release:** Read `.zenodo.json` and verify the `description` field accurately reflects the current layer count and layer list. Update it in the same PR as `RELEASES.md` if anything is stale. Zenodo reads this file at release creation time; it cannot be updated retroactively via the repo (only via the Zenodo web UI).

**Engineer's Take check — mandatory before every release (hard gate):** Before cutting any release, grep the Lean sources for outstanding Engineer's Take placeholders — at minimum `TODO (Tim)` and `TODO: Engineer's Take` across **`ZeroParadox/**/*.lean`** (also scan for any `## Engineer's Take` heading followed immediately by an empty section). **The glob MUST be recursive.** This instruction previously read `ZeroParadox/*.lean`, which post-reorg matches only 3 files out of 187 — a manual check run that way would pass silently on an unfilled Take in any subdirectory. `check_release_ready.py` already uses the recursive form and is correct; only this prose was wrong (fixed 2026-07-19). Every ZP-X Lean file included in the release must have its Engineer's Take filled in Tim's own voice. **A release is BLOCKED until all are filled.** Claude never writes these — they must be Tim's own language (see the Engineer's Take convention) — so this gate catches the omission, it does not fill it. Surface the list of unfilled takes to Tim and wait for his prose. (Added 2026-06-11 after the four ZP-H functor takes plus ZP-L's were almost missed at the v2.4 threshold.)

**RELEASES.md format:** `## vX.Y - YYYY-MM-DD` header, then **Why this release** (one sentence), **What changed** (bullets), **Document versions at this release** (table), **Next threshold**. Match existing entries in RELEASES.md for exact formatting.

## register.md — Canonical Version Registry

`register.md` is the authoritative source for all current document version numbers, filenames, and companion versions. It is committed to the public repository and reachable from the main index via the Claims Ledger (`CLAIMS.md`, which README links to register.md), so it no longer carries an unlinked-transparency notice (removed 2026-06-21).

**Schema:** One row per formal document:
`| Document | Formal Version | Filename | Companion Version | Notes |`

**Rule: update register.md first.** On any version bump — before touching README.md or a build script docstring — update register.md. **`register.md` is canonical and README.md's Framework table is the single derived copy; that is the whole propagation path.**

**On every version bump, in order:**
1. Update register.md (formal version, filename, companion version if changed)
2. Update README.md Framework table (verify against register.md)
3. Update build script docstring
4. Archive old version per archiving convention

⚠ **GUIDE.md IS DELIBERATELY NOT A STEP HERE, AND THE OLD STEP 3 WAS WORSE THAN VACUOUS.** It said to
verify GUIDE's Reading Paths against register.md — but **GUIDE.md carries no version numbers at all**
(measured 2026-08-19, `grep -c` = 0). A rule naming a surface that cannot go stale can only ever
report green, so an audit ticks a box for a check that never ran. **That GUIDE carries no versions is
a PROPERTY TO PRESERVE, not an omission to correct:** its Reading Paths link flat filenames and
delegate version state to README, and re-adding numbers would mint a *third* copy of every version —
against § *the pointer must not become a COPY* directly, and it would oblige the README↔register
comparator to grow a third arm to police the copy the decision created. **Reintroducing a version
number to GUIDE.md is a regression, not a helpful addition.**

## Companion Document Versioning

**TRIGGER — an action: a formal document was updated, or you are touching any rendered PDF text.**

- **Review its companion IN THE SAME SESSION**, and bump the companion's internal version in the
  **same commit**. Companion versions are independent of formal versions; what matters is that the
  companion is not materially **stale**, because a general reader meets the framework there and a
  stale key-result box misdescribes what is proved.
- **A document's OWN version appears in exactly ONE place in rendered content — the subtitle meta
  line.** No self-version changelogs, no `[new in v1.7]` provenance tags. **Editorial review kills
  these.** ⚠ **Cross-document citations are exempt** (*"T-SNAP derived in ZP-E v2.0"*) — that is a
  citation, not a self-changelog, and treating it as a violation is a false kill.

📖 **THE CHECKLISTS — `tools/process/document-workflow.md`.** The companion sync questions and
checklist, the full violation list to strip on discovery, and the **five prose-precision categories**
(precision error · invented terminology · directional ambiguity · context-free structural claim ·
scope overclaiming) that every companion section is drafted and reviewed against. **Open it before
writing companion prose** — those five are the errors that recur, and they are graded by an editorial
gate that will send them back.

## Vocabulary Reference Guide — Standing Update Rule

A vocabulary reference guide lives at `.claude-local/vocabulary_reference.md`. It is the authoritative list of:
- Terms to avoid or replace (technically loaded words used incorrectly, or invented ZP jargon)
- Terms requiring a plain-language gloss for non-specialist audiences
- ZP-internal vocabulary and how to describe it externally

**Standing rule:** Whenever a vocabulary problem is surfaced — by Dan, by an adversary review kill-list, or by any external reviewer — update `.claude-local/vocabulary_reference.md` in the same session before the session ends. Add a row to the Update Log with the date, source, and term. Do not leave vocabulary fixes as one-off edits without capturing the general rule.

This rule applies to both directions:
- A term flagged as wrong (e.g., "isolated," "membership status") → add to Section 1
- A term flagged as needing a gloss (e.g., "valuation," "clopen") → add or verify in Section 2

## Build Script Hash Integrity

`register.md` records a SHA-256 fingerprint (first 8 chars) of every formal and companion build script in the `formal:XXXXXXXX comp:XXXXXXXX` token embedded in each row's Notes field.

**Line endings are LF, enforced by `.gitattributes`.** Because the fingerprint is a hash of file *bytes*, line endings must be byte-stable across machines or the same script would hash differently (CRLF vs LF). `.gitattributes` declares `* text=auto eol=lf` (all text normalized to LF) and marks PDFs/images `binary` (never converted). Do not commit CRLF in tracked text files, and do not rely on `core.autocrlf` — the attributes override it. `check_hashes.py` hashes the active `.claude-local` scripts (LF); the `scripts/` mirror is the same content under the same LF policy. (Added 2026-06-21 after a CRLF/LF mismatch made the `scripts/` mirror hash differ from the active script for the same content.)

**Standing rule — any script change requires all four steps in the same commit:**
1. Make the change and bump the internal version number
2. Rebuild the PDF and archive the old version
3. Recompute the hash: `python -c "import hashlib; print(hashlib.sha256(open('scripts/build_<doc>.py','rb').read()).hexdigest()[:8])"`
4. Update the hash token in `register.md`

**Session start check:** Run `python tools/verify/check_hashes.py` at the start of any session that will touch build scripts. A mismatch means a script was modified without completing the full four-step workflow — version bump and PDF rebuild are overdue.

A hash mismatch is not just a "rebuild needed" signal — it means the version bump step was skipped. Do not rebuild without incrementing the version number.

## PDF Build Standards

**Before building any PDF in this project** — formal layer, companion, or otherwise — read `scripts/PDF_Rendering_Standards.md`. It is the single authoritative source for font stack, glyph rendering, table cell formatting, HTML entities, subscript/superscript rules, and pre-build verification. All rules there apply to every PDF build without exception.

## Companion PDF Diagram Layout Standards

These rules apply to every `Drawing` object in every companion build script. Violations cause diagram content to overflow the declared bounding box and render over surrounding text — a recurring issue that has required multiple retroactive fixes.

**Now build-enforced (automatic).** `zp_utils` validates every `Drawing` in the story at `doc.build()` time — no per-function `validate_drawing()` call required. It **hard-fails the build** when content escapes its box (`max_y > dh` or `min_y < 0`, the only case that overlaps surrounding text), and prints a **margin warning** when content is inside the box but within the 10pt-top / 5pt-bottom safety margin. The rules below are still the design discipline (write diagrams that fit), but a forgotten check can no longer ship an escape. The bounds gate cannot see the *internal-collision* class (two elements overlapping inside the box, e.g. a caption over a node box); for that, every build prints a **diagram-page report** (`[diagram pages — eyeball for internal overlaps: …]`) naming the pages to visually check. Eyeball those pages on any diagram-touching build before commit.

**Known deferred tripwire (2026-06-19):** `build_zpc_companion.py`'s surprisal diagram has a pre-existing ~2pt bottom escape (the amber origin marker) — sub-perceptible, no visible overlap. Left unfixed by decision; the gate will block that companion's next rebuild until the diagram's `dh` is bumped a few points. Fix it then, bundled with whatever change prompts the rebuild.

### Diagram height and cy rules

**Rule 1 — Never derive `cy` from `dh` when the diagram contains fixed-size elements (circles, boxes, labels at fixed offsets).** `cy = dh * fraction` is only safe when all content scales with `dh`. If any element has a fixed radius `r` or a fixed offset, use a fixed numeric `cy` instead.

**Rule 2 — Verify bounds before committing.** After placing all elements, check:
- `max_y = max content y` must satisfy `max_y < dh - 10`
- `min_y = min content y` must satisfy `min_y > 5`

The minimum margin is 10 pts top and 5 pts bottom. If either fails, increase `dh` or adjust `cy`.

**Rule 3 — Common overflow sources to check explicitly:**
- Labels below circles: `cy - r - label_offset` — goes negative when `cy` is too small
- Labels above circles: `cy + r + label_offset` — exceeds `dh` when `cy` is too large  
- Internal title strings at `dh - N` — conflict with top circle labels when both are near the top
- Caption strings at fixed `y=10` inside the drawing — safe, but check nothing else sits at the same y

**Rule 4 — Internal title strings are usually redundant.** Diagrams that have both a title string inside the `Drawing` and a `ccaption()` below it should drop the internal title. It adds clutter and occupies the same crowded top zone as circle labels.

### Pre-build checklist for new diagrams

- [ ] `cy` is a fixed value, not `dh * fraction` (unless all elements scale with `dh`)
- [ ] Calculated `max_y < dh - 10` and `min_y > 5` for all content
- [ ] No internal title string that duplicates the caption
- [ ] `dh` expressed in inches with comment: `# N * 72 = M pts; content top = X, content bottom = Y`

## scripts/ is the build scripts' ONLY home. There is no mirror to keep current. (2026-08-15.)

`scripts/build_*.py`, `zp_utils.py` and `scan_pdfs.py` are the working copies; the `.claude-local/`
originals of those were deleted. **Edit the file in `scripts/` and commit it like any other source
file — there is no copy step.**

⚠ **NOT every build script moved.** Five remain private-only: `build_bottom_matrix.py`,
`build_claim_map.py`, `build_padicbridge.py`,
`build_zp_reals_companion.py`, `build_zpj_bridge_companion.py`. **Measured 2026-08-15: none of
the five emits a TRACKED artifact**, so nothing published depends on an unpublished builder and
the transparency position holds — but `scripts/build_dictionary_map.py` *imports* the first of
them, which is why it cannot run from a public clone and now says so instead of raising
`ModuleNotFoundError`.

⚠ **WHY IT WAS RETIRED, and the failure is the general argument against mirrors.** The rule asked a
human to remember a copy step on every commit, and `register.md` fingerprinted only the PRIVATE
copy — so the PUBLISHED script sat outside the integrity check entirely. `scan_pdfs.py` drifted on
2026-05-20 and nothing noticed for three months. A mirror plus a discipline is strictly worse than
one file: it adds a way to be wrong and removes the way to detect it. `check_hashes.py` now
fingerprints `scripts/`, so **what `register.md` attests to is exactly what a reader can download.**

**The four-step rule for changing a build script is unchanged** — edit, bump the internal version,
rebuild the PDF, update the hash token in `register.md`. Only the copy step is gone.

✅ **The fonts are published too, so `scripts/` is RUNNABLE and not merely source-visible.** The
12 DejaVu + STIX Two TTFs live in `scripts/fonts/` (6.1 MB, measured 2026-08-16), which was the
last thing standing
between a clone and a working build — the code was public and its fonts were not.

⚠ **Both licences ship beside them and that is a requirement, not a courtesy.** The SIL OFL says
each copy must contain "the above copyright notice and this license"; redistributing the binaries bare
would violate it. `LICENSE-DejaVu.txt` is the Bitstream Vera text extracted from the font's own
`name` table (authoritative for these exact files, rather than assumed from the family name), and
`LICENSE-STIXTwo-OFL.txt` is the canonical upstream OFL 1.1. **If a font is ever added or replaced,
read its `name` table id 13 and ship whatever licence it declares.**

If a script is new, add a row for it to `scripts/README.md` in the same commit.

## Lean↔PDF Consistency — AI-Assisted Workflow

There is no automated tooling that verifies theorem status labels in PDF build scripts (e.g. "Status: DERIVED", "Candidate Theorem") match the actual Lean proof state. This is a known gap.

It is closed by the Claude-assisted session workflow instead. At every session where a Lean proof changes status or a new result is added, Claude cross-checks the corresponding PDF script and companion document as part of the same work. The companion sync checklist and README sync triggers (above) formalize this discipline.

This is a deliberate choice: the mapping between Lean theorem names and PDF prose descriptions is not machine-parseable without a maintained lookup table that would itself require discipline to keep current. The AI workflow catches the same class of errors more flexibly, with lower maintenance overhead, at the project's current scale.

If the framework grows significantly or external contributors join, a lightweight parseable-marker convention (`-- LEAN_STATUS: DERIVED` in Lean files, grepped against PDF scripts) would be worth adding. For now, the session discipline is the mechanism.

**Lean encoding descriptions can also go stale.** The gap above covers theorem *status* labels. A separate gap: prose descriptions of Lean *encodings* (type names, constructor names, how a concept is represented in code) can drift when the Lean source is refactored. Before stating any Lean encoding in a PDF, companion, README, or correspondence — verify it against the actual source file. Do not rely on memory or prior documentation. Example: `Fin 2` was replaced by `OntologicalStates` in ZPB.lean; stale references persisted in README.md, CLAUDE.md, and build scripts until caught by a reviewer question in May 2026.

### File-Reference Citation Convention (standing rule — Tim 2026-07-08, post-reorg)

References to Lean **files** in reviewer-facing / checkable surfaces must carry the **full repository path** (`ZeroParadox/<Domain>/<Name>.lean`), never a bare basename. A full path is grep-verifiable against the filesystem — it resolves or it does not — so a move/rename fails **loud**; a bare basename fails **silent** (plausible but pointing nowhere), which is exactly the stale-citation class the 2026-07-08 reorg sweep had to hunt down. For a "check it yourself" repo, loud is the point.

By reference kind and surface:
- **Declaration names** (`t_snap_derived`, `mc1_correspondence`): keep **bare** — a decl name is globally unique in the codebase and self-locating via `#print axioms ZeroParadox.<name>`. Never prefix a decl with a path or a (dead) per-layer namespace.
- **File references in checkable surfaces** — CLAIMS.md, BOTTOMELEMENT.md, README/GUIDE, and each formal document's "Lean source" box/footer: **full path**, as a markdown link href where the medium supports it. The markdown ledgers already do this; keep it uniform.
- **File references in flowing general-reader companion prose**: a bare basename is acceptable where a full path would clutter the sentence for a non-programmer — the checkable surfaces carry the path and the file is one grep away.

**Rollout is additive, not a big-bang rewrite.** Every new or edited reference uses a full path immediately. Existing formal-doc source boxes upgrade to full paths **as each document is next rebuilt** (the same as-touched model as the companion-sync and vocabulary conventions — do not burn a rebuild round retrofitting). The authoritative old→new file map is `ssot.json` (`new.file`).

**Enforcement:** a `check_paths.py`-style resolver (the one used in the 2026-07-08 sweep, in the scratch/`.claude-local` tooling) verifies every repo-relative file reference in tracked markdown resolves against the filesystem. Run it before any doc-touching commit; it should become a pre-push/CI check so a future reorg cannot silently rot the citation layer again.

## Transparency notices on unlinked files — RETIRED 2026-08-15 (Tim).

**The rule was: any tracked file unlinked from both README.md and GUIDE.md must carry a
transparency blockquote (or, for a PDF, an amber callout). It is gone.** It bound seven files
and exactly one honoured it, for months, with nothing noticing — which is past this file's own
*fix the trigger* rung and into *discipline will not work here*.

**Measured the day it was retired.** Unlinked from both indexes: `ABOUTME.md`,
`BOTTOMELEMENT_findings.md`, `CLAUDE.md`, `LEAN_CUSTOM_REGISTRY.md`, `RELEASES.md`,
`register.md`, `scripts/PDF_Rendering_Standards.md`. Only `ABOUTME.md` carried a notice. Its own
table named two files and one of them, `ZP_Gen2_Applications.pdf`, had been moved to the private
folder and was not tracked at all.

⚠ **THE TRIGGER WAS MEASURING THE WRONG THING, and that is the transferable part.** It asked
*is this linked?* when what anyone actually cared about is *would a reader be misled about why
this exists?* Those came apart twice: `register.md` is flagged unlinked while this same file
says it is deliberately reachable through the Claims Ledger, and an instruction file cannot
carry a header at all, because a notice prepended to a prompt **becomes part of the prompt**.
The exception carved for `.claude/commands/*.md` and `CLAUDE.md` was the tell that the trigger
was wrong, not that it needed one more exception.

**What replaces it: nothing mechanical, and that is deliberate.** Disclosure lives in
§ *WHERE THINGS LIVE* and § *Private Working Folder* — pages a human reads. Where a document's
STATUS could mislead (speculative, superseded, a development artifact), say so in its own
opening because it is true, not because a linkage rule fired. `ABOUTME.md` keeps its note on
exactly that basis.

**Also retired with it: § *README.md Link Restrictions*,** whose table named the same two files
and was stale the same way. Nothing is being *hidden* — if a file should not be in the index,
the reason belongs in a commit message or a defect row, not a standing table that outlives it.

## Development Environment

This project runs on **Windows 11**. Shell commands must use PowerShell syntax, not Unix/Bash.

- **File discovery:** Use the `Glob` tool — never `find` (hangs on this system) or `ls`
- **Shell commands:** Use the `PowerShell` tool — never `Bash` with Unix-style commands
- **Never prepend `cd`:** The working directory is always `C:\Workspace\ZeroParadox` at session start. 
- **Never prepend `cd C:\Workspace\ZeroParadox;` or `Set-Location` to any command — doing so creates command strings that don't match the allowlist and triggers unnecessary permission prompts.
- **File verification:** Use `Get-ChildItem *.pdf` not `ls *.pdf`
- **File moves:** Use `Move-Item` not `mv`
- **Path separators:** Backslash in PowerShell (`C:\Workspace\ZeroParadox`), forward slash in Lean/lake config

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

## Theorem/Proposition/Lemma Naming Convention

All formal ZP documents use the following hierarchy for naming results. Apply this consistently when drafting or editing any formal layer:

- **Theorem**: The primary result of a section — of major significance for the framework. Reserve for results that drive the dependency chain or that are the central claim of a layer (e.g., T3 Monotonicity, T-SNAP).
- **Proposition**: A derived result that is rigorously proved but subsidiary to the main theorems — true and important, but not the headline claim (e.g., T1 partial order, T2 clopen balls).
- **Lemma**: A technical helper result used as a stepping stone toward proving another result (e.g., L-RUN, T2 global minimum).
- **Corollary**: A result that follows immediately from a theorem, proposition, or lemma with no substantial additional work (e.g., C1, C2, C3, T1b). Mark with "Corollary" label.
- **Conditional Claim (CC)**: A result that holds only given an explicit modelling commitment not derivable from the axioms (e.g., CC-1: S₀ = ⊥).
- **Design Principle (DP)**: A design commitment — well-motivated and explicit — that is chosen rather than derived (e.g., DP-1: orthogonality).
- **Remark (R)**: An observation providing context or clarification; does not require proof.

When assigning a label, ask: "Is this result the central claim of its section, or is it infrastructure for something else?" Central claims are Theorems; infrastructure is Propositions or Lemmas.

### Readable Name Convention — CC-2 is "the Quine atom" (framework-wide, additive)

**Standing rule (Tim, 2026-06-09).** CC-2 (⊥ = {⊥}, the self-containing bottom) is the conceptual keystone of the framework — it is what forces ZF+AFA, makes ⊥ immune to external description, and is the single contact point between ZFC+Foundation and ZF+AFA. The bare label "CC-2" undersells it on two counts: it reads as a minor sequence code, and the "CC = Conditional Claim" prefix is now **stale** — CC-2 was upgraded to a Forced Metatheoretic Commitment (closed via ZP-J T-EXEC), so it is no longer a conditional claim. This is the same situation AX-1 was in before it became T-SNAP.

**The convention — ADDITIVE, never eliminative:**
- Present CC-2 with the readable name **"the Quine atom."** This is a recognized set-theory term (Quine, Aczel) — it carries real gravity and a literature anchor, and it is NOT ZP-invented jargon (avoid inventing a ZP-branded name — that would undo the de-jargoning work).
- **Keep "CC-2" as the formal handle and note it alongside** — e.g., "the Quine atom (CC-2)" on first/significant mention. Do NOT remove or rename the CC-2 identifier anywhere; every existing cross-reference stays valid.
- Gloss once per document as "the self-containing bottom, ⊥ = {⊥}."
- **⚠ SCOPE THE GLOSS — BANKED 2026-08-01 (Tim), NOT YET ROLLED OUT.** `⊥ = {⊥}` is well-formed and
  true **in the ZF+AFA metatheory** — that is anti-foundation's actual content and Aczel's Quine atom
  is a real object, so **do NOT retire it** (a flat retirement would deny a true theorem of a real set
  theory: the `snap_is_frameflip` over-correction pattern). But asserted of the **Lean carrier** it is
  a **cross-type `=`** — `bot : L` against `{bot} : Set L` — which is on this file's bedrock-violation
  list. **Carrier-level statements take the INSTANCE-OF-FAMILY form**, which the corpus already
  proves: `IsQuineAtom q := selfMem q ∧ ∀ x, selfMem x → x = q` (the family predicate),
  `da1_closed_concrete : IsQuineAtom (bot : MachinePhase)` (⊥ as an instance), and
  `selfMem_eq_singleton_bot : {x | selfMemDerived x} = {bot}` (a `Set L` equality, `[propext,
  Quot.sound]`). This is the **QuineHost pattern** — never "⊥ *is* {⊥}", always "here are the
  requirements, and ⊥ is a witness meeting them."
  - **Why it was missed, and it is a measurement error worth copying the lesson from.** The rollout
    note below says *"Lean is clean (CC-2 is never a Lean identifier — 0 occurrences)"*. True of the
    **label** and false of the **claim**: `ZeroParadox/Algebra/Wheel.lean` asserts the bare equation
    many times. **Grep the CLAIM, not the name** — the same rule this file states for
    kill-propagation, missed here at the measurement step. **No count and no line numbers are
    recorded here on purpose**: the figure once said "ten times" with ten line numbers, and both went
    stale as the file was edited. Measure it.
  - **⚠ AND THE ROLLOUT IS NOT A SWEEP — most occurrences are CORRECT.** All were re-read
    individually 2026-08-03: the governing scope note, the correction record, and every site that is
    explicitly ZF+AFA-scoped or hedged as a conjectured counterpart is **right as written**, because
    `⊥ = {⊥}` is a true theorem of a real set theory. Only a **carrier-level consequence** claim is a
    defect. Two have been found and fixed, both the same modality (`forced`, then `structurally
    requires`), and the second was left standing by the pass that fixed the first — which had
    recorded itself as fixing "the one" occurrence.
  - **Provenance, because it is easy to misremember (it was, this session):** the 2026-07-14 ratification
    retired **MC-1**'s identity and cites CC-2 only as the precedent for *keeping a label*. **CC-2's own
    identity was never reviewed.** And the two defects are NOT the same: MC-1's was **ill-typed**
    (cross-category, never a proposition); CC-2's is **well-typed in the metatheory and cross-type in
    the carrier**. Scope it; do not retire it.
- **Do not overclaim status.** It remains a Forced Metatheoretic Commitment, not a Lean theorem. The structural self-application fixed point is Lean-proved (ZP-J T-EXEC); the literal set-membership ⊥ ∈ ⊥ is metatheoretic (lives in the ZF+AFA framing, not the Lean kernel). The readable name conveys significance, not proof-status.

**Rollout (phased, not a 12-PDF marathon):**
- Reader-facing surfaces first: README.md, GUIDE.md, register.md.
- Then apply to each formal document/companion **as it is next revised** (the readable name leads CC-2's introduction). Footprint as of 2026-06-09: 12 build scripts carry CC-2 (build_zpe.py 27, build_zpa.py 13, build_zpc.py 8, etc.); Lean is clean (CC-2 is never a Lean identifier — 0 occurrences).
- **Do not touch** RELEASES.md (release record - never rewrite history).

### The keystone concept — "the diagonal fixed point" (confirmed name)

**Standing rule (Tim, 2026-06-10).** The Quine atom (CC-2) is only the *set-theoretic face* of the
framework's actual keystone: **⊥ is the same self-referential fixed point in every framework, and the
floor of each structure is its point of self-reference** (the Gödel inversion — self-reference located
at the floor, not the ceiling). The confirmed readable name for this keystone is **"the diagonal fixed
point."** This language has recurred across many sessions; it is the real central concept.

- The faces of the one diagonal fixed point: the Quine atom (set theory, CC-2), the Kleene quine
  (computability, ZP-K), v₂(0)=∞ (valuation, ZP-B), the unique fixed point of `selfApp`
  (ZP-J `AbstractSelfApp`), unbounded surprisal / no external description (ZP-C), the categorical
  initial object (ZP-G). MC-1 (the bottom family) is what identifies them as kin.
- **Name it to evoke the recognized phenomenon, do NOT claim the unification as proved.** "Diagonal"
  anchors it to the diagonal argument and Lawvere's fixed-point theorem (the recognized home for
  self-referential fixed points across Russell / Quine / Kleene / Gödel / Tarski / Cantor). What ZP has
  *formalized*: `AbstractSelfApp` + instances, T-COMP (Quine atom = Kleene fixed point = ⊥), ZP-M
  (Kleene quine ∧ ε₀ co-witnessed). That ZP's keystone *is* a manifestation of Lawvere's theorem is a
  CONNECTION / conjecture, not a ZP result — keep that fence.
- Full articulation, faces, and the formal-vs-conjectural split:
  `.claude-local/notes/keystone_self_referential_fixed_point_2026-06-10.md`.

### MC-1 status convention — RETIRED as a commitment; MC-1 = the bottom family (rolled out 2026-07-15)

**Standing rule (Tim, ratified 2026-07-14, rolled out 2026-07-15).** MC-1 no longer names a "modeling
commitment" to one object; it names the **bottom family**. The "MC = Modeling Commitment" prefix is stale
(the same arc as AX-1→T-SNAP and CC-2→FMC). The earlier "correspondence derived / identity a commitment"
split is superseded:

- **Correspondence half — now formally realized.** Each domain bottom is the categorical bottom
  (limit or initial object) of its own *real* Mathlib category: F_B `fB_functor : ℕᵒᵖ ⥤ TopCat`
  (⊥ = inverse limit `⋂ B(0,2⁻ⁿ) = {0}`), F_D `fD_functor : ℕ ⥤ ModuleCat ℂ` (⊥ = initial object
  `StateSpace 0`), F_C `fC_functor : ℕ ⥤ KleisliCat PMF` (⊥ = initial object `Fin 0`, with
  `fC_no_return` = AX-G2 as a theorem). Bundled witness: `mc1_correspondence` (`MC1Bridge.lean`).
  So the bare label "MC = Modeling Commitment" now **undersells** this half.
- **The family — membership proved.** Each domain's bottom satisfies a shared list of criteria (the slots
  in BOTTOMELEMENT); per-domain membership is proved, the choice of criteria a design principle.
- **Identity half — RETIRED as ill-typed.** That the four bottoms are *numerically one object* across
  distinct categories is NOT a commitment the framework holds — `x = y` across distinct categories is not a
  well-formed proposition, so it was never a claim. The members are provably distinct (the walls); the only
  oneness is the shared *shape* (the diagonal fixed point), apophatic, never a formal identity.

**The convention (ADDITIVE, never eliminative):**
- Keep **"MC-1"** as the formal handle everywhere; it now points at the **bottom family** (CC-2 precedent:
  keep the label, retire the framing). Do not rename it; `mc1_correspondence` is unchanged. **Never call the
  cross-category identity a "modeling commitment," "offered," or "one object we commit to"** — it is retired
  as ill-typed. Present the split: membership PROVED, criteria a design principle, identity RETIRED, members
  provably distinct.
- **No new readable name for MC-1.** Unlike CC-2 (which *is* an object = the Quine atom), MC-1 is the
  *identification*; its underlying object already has the confirmed readable name
  [[project_diagonal_fixed_point]] ("the diagonal fixed point"). Coining an MC-branded name would be
  the ZP-invented jargon the CC-2 convention warns against — do not.
- **Do not overclaim.** The real categories are not `ZPCategory` instances (they have terminal
  objects), so ⊥ is the *limit* in `TopCat` and the *initial object* in the other two; state that
  distinction honestly. The cross-category identity is never claimed as proved.
- Canonical definition lives in **BOTTOMELEMENT's opening** ("The family - MC-1"); everything references
  there (draft MC1.md folded in + archived to `.claude-local/notes/` 2026-07-15).
- **Rollout DONE (2026-07-15):** README, CLAIMS, SNAP + BOTTOMELEMENT via their generators. Do not touch RELEASES.md.

## GitHub Issues — Transparency and Engagement Policy

The Zero Paradox project treats GitHub Issues as a public transparency mechanism, consistent with the project's core transparency commitment. Issues are not just a bug tracker — they are the public record of what is open, contested, or unresolved in the framework.

### When to check

- At the start of any session where a PR is being created or merged
- At the start of any session where outreach responses are being processed
- Any time Tim asks about external engagement or project status

### When to file a public issue

- Framework open questions that are genuinely unresolved and would benefit from external input (e.g. OQ-E2 cardinality question, AFA/CH tractability)
- Substantive technical questions that arose in review and were not closed within the session
- Questions where the framework explicitly flags something as open and outside the authors' expertise

### When NOT to file

- Anything sourced from private correspondence (reviewer feedback, outreach responses, academic group correspondence)
- Reviewer identity or feedback details
- Outreach strategy, sending schedules, or draft emails
- Editorial or prose decisions
- Anything that belongs in `.claude-local/`

### Issue framing standard

Public issues should read as genuine open questions to the mathematical community — not as requests for validation. Frame them as specific, honest about uncertainty, and standalone without requiring knowledge of the full framework.

### Identifier tracking — standing requirement

Every outreach item must have its external identifier recorded in `.claude-local/outreach/tracker.md` at the time it is created or sent. No exceptions.

**What counts as an identifier:**
- GitHub Discussion: `#N` (e.g. `#77`)
- GitHub Issue: `#N`
- MathOverflow question: full URL
- Email thread: date sent + recipient (email threads have no stable ID — date + recipient is the key)
- Zulip post: stream + topic slug
- arXiv submission: arXiv ID

**When to record it:** At the moment the item is created or sent — not after the fact. If an identifier is missing from the tracker, add it before doing any other work in that outreach session.

---

## Framework Structure (for context)

The Zero Paradox is a multi-layer mathematical ontology proving the Binary Snap (⊥ → ε₀) as a theorem. The dependency order of the formal layers is:

**ZP-A** (lattice algebra) → **ZP-B** (p-adic topology) → **ZP-C** (information theory) → **ZP-D** (state layer) → **ZP-E** (DA-1/T-SNAP derivation)

**ZP-G** (category theory) → **ZP-H** (categorical bridge) — self-contained; depends on ZP-E conceptually but not formally.

Each formal document has a paired illustrated companion for general readers. AX-G1 and AX-G2 are the two structural commitments of ZP-G's categorical layer. Neither is a novel commitment: AX-G1 is grounded in ZP-A's bottom element ⊥; AX-G2 follows from ZP-A antisymmetry and ZP-B C3 (topological irreversibility). ZP-G is self-contained by design and states them explicitly within that layer. AX-B1 (binary/discrete existence) is the framework's **one substantive modeling commitment** (discrete Boolean existence, not a continuum of partial states) — do NOT call it "directly verifiable / not a novel commitment" (reclassified 2026-07-15): the `decide` proof (`ax_b1_distinct`) only checks the two states are distinct *given* the two-element type, not the choice of a discrete alphabet over a continuum. The ZP-C forcing lemmas (`pmf_subsingleton_isPure` / `binaryState_exhaustive`, `Information/Surprisal.lean`) discharge the no-half-state worry (leaving ⊥ needs a second outcome) but force only the ≥2-outcome lower bound; the residual substantive commitment is that the outcome space is DISCRETE, not a continuum - which those lemmas do not eliminate and which the reals lack (the snap fails there, `f_snap_impossible`). See the CLAIMS AX-B1 row. AX-1 (Binary Snap Causality) is now Theorem T-SNAP, derived in ZP-E — do not refer to it as an axiom.

## Four-Fingerprint Scan — Decision Log Requirement

When a four-fingerprint scan is conducted (see memory: `feedback_reader_orientation.md`), the session notes file in `.claude-local/notes/` must be updated before the session ends with:

1. **Each item reviewed** — the finding, the decision (FIXED / NO FIX / PENDING), and the version bump if fixed.
2. **Rationale for no-fix decisions** — e.g., "already addressed in vX.Y", "standard result in the relevant literature", "Lean scope already disclosed."
3. **Any technique notes** — e.g., "read the Lean file before fixing to confirm the actual proof argument."

This log is the authoritative record of what has been reviewed and why. Future sessions must read it before starting a new scan pass to avoid re-reviewing already-settled items.

**File convention:** `.claude-local/notes/framing_scan_YYYY-MM-DD.md` — one file per scan pass, named by the date the scan was run. The decision log lives at the bottom of that file under a `## Decision Log` header.

**Standing rule:** A scan pass is not complete until all reviewed items have a decision recorded. "PENDING" is a valid decision for items deferred to a future session.

## Communication Quality Feedback

During working sessions, apply the Communication Quality Rubric to evaluate Tim's statements about the framework in real time. Flag anything scoring **7 or below** on the composite scale (35% terminological accuracy, 35% structural accuracy, 15% consistency, 15% clarity). The full rubric with scoring tables and calibration notes lives at `.claude-local/communication_quality_rubric.md`. Key terms requiring extra care: ⊥ (three-way identification), T-SNAP (theorem, not axiom), DA-1 (derived proposition, conditional on DP-2), DP-2 (grounded in D7 — not freely chosen), CC-1/CC-2 (both now derived via ZP-J, not freestanding commitments).

## Session Handoff File

`.claude-local/handoff.md` is the standardized session state file. At the start of every session, read it first. At the end of every session (or before a planned context switch), overwrite it with the current state. It has **two parts, in order**: first, **keeping the conversation thread alive** — the live orientation a fresh session needs to resume mid-thought rather than cold-start; then the **factual ledger** — what was just done, the immediate next action, and anything deferred. The thread leads, the ledger follows; the components, structure, and rationale of the thread part are defined privately (memory `feedback_handoff_thread_first`). Always use this exact filename — one file, always current, always overwritten.

⭐ **"UPDATE THE HANDOFF" IS A COMPOUND ACTION, AND THE PROCEDURE IS DEFINED IN THE FILE ITSELF —
`.claude-local/handoff.md` PART 0b.** It closes finished tickets by MOVING them to `queue/done/`,
opens tickets for what was found, **commits the private repo**, and reports (never pushes) main-repo
state. **Do not restate the six steps here** — one definition, and it lives where it is read first.
⚠ It is loaded onto this phrase deliberately (Tim, 2026-08-20): the git hygiene this project keeps
failing at has no reliable trigger, and *"update the handoff"* is one that actually fires.
⚠ **Overwriting is safe ONLY because `.claude-local` is a git repo — and that is the step with the
measured failure history.** 2026-08-20: 120 uncommitted entries, 86 of them notes never once
committed, with 42- and 21-day gaps. An unstarted item vanished from this file for five revisions and
was recovered only because Tim remembered it existed.

## Development mode — LOAD THE SECTION BEFORE YOU WORK. (Tim, 2026-07-31.)

**Before fresh mathematical development, read the whole relevant subsystem. Do not start from
targeted search.** This is scoped to *development*; error-sweeps have their own discipline and a
different unit (see below).

```
python .claude-local/where.py "<Tim's phrasing, verbatim>"     # -> ranked folders + token cost
python .claude-local/where.py --files "<phrase>"               # + the file list
python .claude-local/where.py --spine                          # what the always-load spine costs
```

Then load: **the ~50k spine** (the five `#check`-only indexes — `BottomCannotBe`, `SnapCannotBe`,
`Epsilon0CannotBe`, `DiagonalFixedPoint`, `ChoiceCannotBe` — plus `MANIFEST.md`, `CLAIMS.md`,
`BOTTOMELEMENT.md`, `SNAP.md`) **plus the one or two folders it names.** Most subfolders are 5k–66k
tokens; the largest, `Valuation/`, is ~123k. Total lands at 80k–170k, comfortably resident.

**Why, and it is not about catching errors.** Every real finding of 2026-07-31 came from **colliding
two facts** — `selfApp` fixes ⊥ *and* `α ↦ ω^α` does not; ⊥'s down-set is empty *and* R1 forbids
subtraction; `nfp` is seed-independent *and* the corpus says "⊥ the seed". **You cannot collide facts
you are fetching one at a time.** Targeted search returns the fact you asked for and nothing adjacent,
which is precisely what a collision needs.

**Two honest limits.** (1) `where.py` scores term distinctiveness — it produces a *shortlist*, not an
answer, and on one of four test queries the right folder ranked third. Load two or three. (2) It
**cannot** route a genuinely new concept with no corpus vocabulary; fall back to `--spine`.

**Tim's Engineer's Takes are the bridge, and `where.py` reports them.** The Lean body says `cx`,
`member`, `infinitude`; Tim says *"bottom itself is infinitely complex."* The Takes are the only
corpus written in the register a question arrives in, they are attached to the file they describe, and
**all of them together are ~16k tokens — cheap enough to load wholesale.** Measured 2026-07-31: on four separate questions the answering
Take was found *after* the work, never before.

**Not this, for error-sweeps.** A claim-sweep's unit is the **rendered PDF text**, never the source —
a claim survived four vocabulary changes and one split across two Python string literals. See
`vocabulary_reference.md`.

## High-Value Insight Capture — Standing Rule

Any observation made during a session that could lead to a new theorem, new layer,
new conjecture, or significant axiom relationship must be written to `.claude-local/notes/`
immediately — without waiting to be asked. Do not defer to the end of the session.

**Triggers — capture automatically when any of these arise:**
- A structural connection between two existing layers that hasn't been formalized
- An identification of two mathematical objects as "the same fact in different languages"
- A conjecture about axiom derivability or necessity (e.g. deriving a class field from
  upstream structure)
- An argument that could become a new ZP layer or bridge layer
- A DC-free, choice-free, or purity result not yet in a Lean file
- A new justification for an existing axiom or design principle
- Any observation that directly answers or partially closes an open question in the framework

**What the note must contain:**
1. The insight in plain language (one paragraph — legible without session context)
2. The precise mathematical claim (what exactly is being asserted)
3. What is formal vs. what is still philosophical/conjectural
4. Status: open conjecture / partial proof / architecture clear but unbuilt / etc.
5. Connected notes (link to related `.claude-local/notes/` files)

**File naming:** `.claude-local/notes/<topic>_YYYY-MM-DD.md`

**The test:** Would a future session miss something important if this wasn't written down?
If yes, write it now.

### But the note is the DRAFT. The POINTER is the deliverable. (Measured 2026-07-31.)

**Writing the note is not the durable act; being pointed at from a read surface is.** Measured across
767 notes: **only ~10% were referenced from anywhere a future session actually reads** — `CLAUDE.md`,
`.claude-local/handoff.md`, a `.lean` docstring, or a memory file. The other ~90% were write-only. On
the same day, four separate findings were rediscovered the slow way while the relevant note sat
unread, and every piece of context that *did* reach the session came from a Lean docstring, this file,
or a memory — **not one came from a note.**

So the rule above is half a rule. After writing the note, **wire the finding to the artifact**, at the
site the reader lands on — which is what § "unstated adjacency" already demands of findings generally
(*"write it there, at the site the reader lands on, not five sections away"*). Applied to notes: put
the sentence in the `.lean` docstring / `CLAUDE.md` / the memory, and let the note hold the long form.

**⚠ AND A NOTE RECORDING PENDING WORK GOES FALSE THE MOMENT THE WORK IS DONE.** This is worse than
going unread: an unread note is inert, a stale one actively misleads. Measured 2026-07-31:
`zpa_launders_axb1_as_a_metric_result_2026-07-26.md` says **"Not yet fixed"** of a bedrock defect that
ZP-A **v1.21 struck days later** — and a triage pass nearly reopened it on that basis. Two sibling
notes say "pending" and "status at interruption" and are equally unverifiable. **Never act on a note's
self-reported status; verify at the artifact.** If a finding is a *defect*, its home is a gate finding
or a fix, never a note that cannot know when it stops being true.

**Folder layout (established 2026-07-31, 767 notes triaged):**
- `notes/` — **active only.** Live conventions, indexes, corrections that must not be re-introduced.
- `notes/future-research/` — **open work.** A stated conjecture, an identified gap with a route, an
  "architecture clear but unbuilt". The test: *could a future session do mathematics from this?*
  **Read this folder when choosing what to work on.**
- `notes/archive/{gate-findings,resolved,superseded}/` — historical. Gate reports are an audit trail:
  write them, never expect to read them.

When triaging, **prefer KEEP when torn** — this is a research record and over-archiving is the
costlier error.

## Reviewer Feedback Tracking

Reviewer feedback and correspondence are tracked in `.claude-local/feedback/reviewer_feedback_tracking.md`. That file is private and gitignored. Do not include reviewer names or feedback details in this file.

## License

CC BY-NC-ND 4.0 — share with attribution; no modifications; no commercial use.


# .claudecodes instructions for Lean 4 development
- Always run lake build as two separate PowerShell calls: first `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8`, then `Get-Content build.log | Select-Object -Last 1` (or with a `-match` filter). Never combine them with `;` in a single call.
- Ignore PDF rendering assets and website build artifacts in the root.
- Always check 'lake-manifest.json' for dependency updates before adding new imports.

- When searching for Lean source files in this project, always use the pattern ZeroParadox/**/*.lean, never **/*.lean. The .lake/ folder contains thousands of Mathlib library files that aren't mine."

# Zero Paradox Project Standards

## Development Branch

All work — Lean 4 proofs and PDF rendering — happens on the `illustrated` branch. This is the single active development branch. `main` is production/public. The `lake_testing` branch is retired; do not switch to it or push to it.

## Operational Rules
1. **Single branch:** All Lean and PDF work happens on `illustrated`. No branch switching required.
2. **Math Workflow:** Verify theorem changes with two separate calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` then `Get-Content build.log | Select-Object -Last 1`.
3. **PDF Workflow:** Use existing rendering scripts and strictly follow the document versioning and archiving conventions defined above.
4. **Transparency:** Maintain the `.claude-local/` folder for in-progress scripts and internal notes as a private "collaboration buffer."
5. **Sync before starting work:** At the start of any session, `fetch()` then `merge(branch='origin/main', reason=...)` before making any changes. Never make edits against a stale base. ⚠ `merge` is **refused while the tree is dirty** — that is deliberate, and the answer is to commit first or take a worktree, never to force it. (Until 2026-08-22 this step said `git fetch` / `git merge` and had been **unexecutable by agents** since direct git was denied.)
6. **Verify no conflict markers after any merge:** Before committing after a merge, run `read(op='diff', args=['--check'])` to confirm no conflict markers (`<<<<<<<`, `=======`, `>>>>>>>`) remain in any file. A file with unresolved markers will commit silently and corrupt the document. This has happened twice on this project.
7. **5-minute timeout on all external tool calls:** Every `PowerShell` or `Bash` call that invokes an external process (PDF build scripts, `lake build`, `python <script>`, long-running `git` or `gh` operations) must use `timeout: 300000` (5 minutes). If the command exceeds this limit, kill it and report back — never wait indefinitely. If it times out, diagnose the cause rather than retrying blindly.
⚠ **STANDARDS 8, 9 AND 10 ARE TIM'S TO RUN — `gh` IS DENIED FOR AGENTS (2026-08-22).** PR creation
and editing, and every GitHub Discussion mutation, reach outside the repository and are governed by
the Adversary Review Gate, which is Tim's decision by construction. **GitHub READS are untouched** —
all the `mcp__github__*` read tools still work, so an agent can still check PR status, read
discussion comments and verify a posted body. The `--body-file` / `-F body=@file` discipline below is
unchanged and still correct; it is the *transport* rule, and it matters exactly as much when Tim runs
the command.

8. **Pull request body — always use `--body-file`:** PowerShell cannot reliably pass multiline PR bodies inline (special characters, arrows, backticks, and asterisks all cause parse errors). Always write the body to `.claude-local\pr_body_<name>.md` first, then create the PR with:
   ```powershell
   gh pr create --title "..." --body-file ".claude-local\pr_body_<name>.md"
   ```

9. **Keep PR description current:** If additional commits are pushed to a branch after the PR is opened, update the PR body to reflect the new content. Update `.claude-local\pr_body_<name>.md` first, then run:
   ```powershell
   gh pr edit <number> --body-file ".claude-local\pr_body_<name>.md"
   ```

10. **GitHub Discussion body updates — always use `-F body=@file`:** Passing Unicode body content through PowerShell string interpolation (`$body = Get-Content -Raw; -F body="$body"`) corrupts multi-byte UTF-8 characters (arrows, subscripts, math symbols). Always write the body to `.claude-local\temp_body.md` first, then pass the file directly:
   ```powershell
   gh api graphql -F query=@.claude-local\mutation_update_discussion.graphql -F id="NODE_ID" -F body=@.claude-local\temp_body.md
   ```
   After every update, verify the live body via `mcp__github__get_discussion` before proceeding to the next thread. This issue was discovered 2026-05-23 when ZP-C (#69) was posted with garbled math.

## File Priority
- Both `.lean` files and PDF build scripts are first-class on `illustrated`.
- All other conventions (versioning, archiving, scripts/ sync) apply as documented above.

## Lean 4 Proof Development: Stub-First Protocol

As proofs grow more complex (ZP-D onward), always use a stub-first approach before writing full proofs. This prevents session hangs caused by heavy import chains and typeclass resolution.

**The workflow for every new ZP-X Lean file:**

1. **Symbol map** — before writing any Lean, map each PDF symbol to its Lean 4 / Mathlib equivalent. Identify which imports are required and which are dangerously heavy (p-adics + EuclideanSpace together, for example, can cause elaborator hangs).
2. **Stub file** — write the complete file with all definitions and theorem statements, but use `sorry` for every proof body. Add `set_option maxHeartbeats 400000` at the top. Do not write proof bodies during the planning or stub step — output the stub file and stop. Wait for a clean build before proceeding.
3. **Build the stub** — run `lake build` and confirm 0 errors on the skeleton. This validates that types elaborate correctly before any proof work begins.
4. **Commit the stub** — commit the sorry-stubbed file immediately after a clean build. This creates a rollback point before any proof work begins.
5. **Fill proofs incrementally** — prove one theorem at a time, building after each. Commit after each theorem is successfully proved. Do not attempt to write all proofs before checking.
6. **Final clean build** — once all `sorry`s are removed, run a final build to confirm 0 errors and 0 warnings, then proceed to the documentation workflow below.

**When to abstract away heavy dependencies:** If a layer imports both p-adic numbers and Hilbert space machinery, consider whether the cross-layer dependency can be replaced with an abstract typeclass or index type (e.g., `Fin (2^k)` instead of `ℚ_[2]`) for the purposes of the proof. Decoupling reduces elaboration load significantly.

## Proof Documentation Workflow

When a ZP-X document is successfully proved in Lean 4, the following steps are **mandatory** before the work is considered complete:

1. **Build clean** — run as two separate calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` then `Get-Content build.log | Select-Object -Last 1`. Confirm zero errors and zero warnings.
2. **Purity check** — add a `#print axioms` block at the bottom of every ZP-X Lean file (inside a `section PurityCheck ... end PurityCheck`), one call per proved theorem. The expected result is `'theorem_name' does not depend on any axioms`. Any kernel axiom that appears (`Classical.choice`, `propext`, `Quot.sound`) must be explicitly noted and justified in a comment in the Lean file.
3. **Update README.md** — add or update a row in the `### Formal Verification (Lean 4)` subsection of The Framework, and update the Question Register row for `Formal verification (Lean/Rocq)`.
4. **Sync the SJV registry (SSOT) — mandatory, see the standing rule below.**
5. **Commit all changes together** on `illustrated`.

### SJV Registry Sync — Standing Rule (mandatory on any Lean declaration change)

**Any change that adds, renames, removes, or splits Lean declarations at HEAD — including a new `.lean` file — must update the SJV `declarations` store and re-export `ssot.json` in the SAME change, never deferred.** The SSOT is only trustworthy if it tracks HEAD 1:1; every un-synced decl re-introduces registry drift (the recurring "SJV is a whole reorg behind" problem the ontology-revamp arc eliminated). Treat this as the same reflex as `lake build` and the purity check.

The sequence (via the SJV MCP; tools reload in any session started after the MCP loaded):
1. `migrate_batch` — `add_new` for new decls (`{qualified, file, namespace, short}`); `reconcile` for renames/moves (id-keyed `new.*` + `disposition`) with `remap_deps=true` (or an explicit `deps` list) so deps edges follow; drops for removed decls.
2. `annotate_many` — ontology tags on new/changed entries (no `domain=[]`; a `role:face` needs an `object`). Refine later via `/tag-review` if unsure.
3. `validate` + `verify_integrity` (both green).
4. `export_full(dest="C:/Workspace/ZeroParadox/ssot.json")` — ABSOLUTE path (a relative dest lands beside the MCP).
5. Confirm file paths resolve N/N, then commit `ssot.json` with the change.

Memory: `feedback_sjv_sync_on_lean_change`.
