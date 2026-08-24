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
| **`tools/verify/`** | every checker, the pipeline (`batch.py`, `hooks.py`, `guards.py`, `report.py`, `vendored.py`), the **baselines**, the **git** hook sources + `install_hooks.py` | **yes — public** |
| **`tools/verify/claude_hooks/`** | the **Claude Code** `PreToolUse` hooks — `block_git_gh.ps1` and its 24-case control, the two enforcement shims. Wired from the tracked `.claude/settings.json`, so a clone inherits the guards rather than an appearance of them (2026-08-23, `GUARD-1`) | **yes — public** |
| **`scripts/`** | every PDF build script, `zp_utils.py`, `scan_pdfs.py`, `PDF_Rendering_Standards.md` | **yes — public** |
| **`tools/process/`** | `CLAUDE.md`'s body — the argument behind each routed rule | **yes — public** |
| **`.claude/commands/`** | the review-gate definitions Claude Code reads | **yes — public** |
| **`.claude-local/`** | signals (`*_cleared.txt`), `batch_state.json`, `gate_round.json`, `DEFECTS.md`, `notes/`, `feedback/`, `outreach/`, `papers/` | **not tracked by THIS repo — it is its OWN repository**, with its own history, a `master` branch and a private remote (`ZeroParadoxLocal`). The parent additionally ignores the path |

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

## R-DEFECTS  A defect's home is the ledger. Read it before choosing work.
TRIGGER  you found a defect, you are choosing what to work on next, or you are about to
         cut a release.
RULE     record it in `.claude-local/DEFECTS.md` — never a note, a gate-findings archive,
         or a handoff line, and never a second copy. Verify every entry AT THE ARTIFACT
         before recording it open or closed. GREP LOOSELY. Burn down in FILE-SIZED
         BATCHES. NO RELEASE IS CUT WHILE THE LEDGER IS NON-EMPTY; release pressure never
         defers a finding to next-touch debt. The target is ZERO KNOWN defects, not zero.
COST     a DOI is permanent and four releases already carry latent flaws — a defect fixed
         before a release costs one gate round, one shipped inside a PDF is forever.
READ     tools/process/defect-ledger.md

## R-RECUR  A failure that recurs is evidence about the RULE, never about the reader.
TRIGGER  you are told you are in a failure condition, this is a retry, a gate returned
         FAIL, or someone refers to a rule you do not recognise.
RULE     re-read this file FROM DISK first — `grep -n "^## " CLAUDE.md` before any full
         read; your injected copy predates every rule written this session, your own edits
         included. Then, stopping at the first step that resolves: check `DEFECTS.md` and
         `DEFECT_CLASSES.md`; diagnose the TRIGGER, not the content (an ACTION binds, a
         CATEGORY leaks); fix at the highest leverage — checker > trigger-plus-path > note;
         control-test with a fresh agent, scorecard fixed BEFORE the result; test delivery
         separately from correctness. Escalate by COUNT: 1st an instance, 2nd a class with
         a detector, 3rd the trigger is wrong, 4th+ build the checker. Never add a second
         rule saying the same thing louder, and never skip to writing a new section.
COST     a mid-session edit never reaches agents spawned after it, so a correct fix can be
         unreachable; and a rule stated twice fires in neither place.
READ     tools/process/recurrence-protocol.md

## R-NOCONV  A check that misses 3x, or a loop that will not settle, changes SHAPE.
TRIGGER  a mechanical check has missed three times, or three or more rounds of fixes have
         not reduced findings — name the rounds and their counts, never assert it.
RULE     stop widening the script. Put an LLM screen on the layer as a READING LIST: it
         may replace the ENUMERATION, never the VERDICT — take sites flagged in >=2 of 3
         runs, ignore self-reported confidence, and ship the recorded slice it should get
         WRONG as its control. Downgrade ENUMERATION legs to WARN; FAIL-OPEN legs never
         downgrade, no matter how many rounds. SPLIT AT THE LEG, never at the check. The
         guard asserting what still BLOCKS lands in the same change, or the exemption that
         block paid for is given up with it. A downgraded gate prints its count every run.
COST     a downgraded fail-open leg is an unpriced exemption, and a warning nobody counts
         manufactures coverage that was never earned.
READ     tools/process/non-convergence.md

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

## R-COREOBJ  Read the Lean before writing about the bottom, the snap, or epsilon-zero.
TRIGGER  you are about to write any prose, figure, docstring, companion text, note or
         outreach copy naming the bottom, the snap, epsilon-zero, choice, or computation.
RULE     open that object's authoritative Lean file and ground every statement in a NAMED
         theorem there. Never reconstruct from memory, from notes, or from this file. If
         this file and the Lean disagree, THE LEAN WINS — stop and ask Tim.
           bottom  `ZeroParadox/BottomCannotBe.lean` + `BOTTOMELEMENT.md`
           snap    `ZeroParadox/Order/SnapCannotBe.lean` + `ZeroParadox/Order/Snap.lean`
           eps-0   `ZeroParadox/Ordinal/Epsilon0CannotBe.lean`
           also    `ZeroParadox/DiagonalFixedPoint.lean` (keystone) ·
                   `ZeroParadox/Category/ChoiceCannotBe.lean` (choice) ·
                   `ZeroParadox/Computability/Kleene.lean` (computation) ·
                   `ZeroParadox/ClaimsMirror.lean` (a claim's status)
         Every gloss carries `Statement:` (what it proves, best form an elaborating `example`)
         or `Reading:` (interpretation, NOT a claim about the theorem). No third option.
         `Idiom:` is vocabulary for a NAMED phenomenon, never a gloss, and it SUPPRESSES —
         apply it only after verifying the site.
COST     the `#check` lines cannot overclaim and the glosses beside them can: two false ones
         survived four adversary rounds inside a file whose stated premise is that it cannot.
READ     tools/process/core-objects.md

## R-BEDROCK  Machine-checked invariants. Never violate; verify at the theorem, never assume.
TRIGGER  you are about to state anything about epsilon-zero, the pole, or where the snap-arc
         returns.
RULE
- **ε₀ ≠ 0. Always. In any reading, carrier, or encoding.** (`epsilon0_ne_zero`.) Never "fence ε₀ = 0" or treat 0 as a candidate value — it is not a well-formed possibility.
- **ε₀ ≠ ⊥.** (`epsilon0_ne_bot`.) ⊥ = 0 is the *base* the ε₀-tower is seeded at; ε₀ is its *closure* — the base is never its own closure.
- **ε₀ is both min AND max at once** — least fixed point ≡ tower supremum (`epsilon0_min_eq_max`); direction-/instance-specific, never collapsed to one face.
- **ε₀ requires two conditions**: the ω-tower operator `α↦ω^α` AND the base ⊥ (`epsilon0_eq_nfp_bot`). It is the *minimum* step next to the pole, never the pole.
- **⊥ = 0 = ∞ is the pole** — *stated*, not fenced. **A CHART claim, not a point identity.** Three distinct witnesses: **coincidence** `infinitude_forces_infinite_complexity`; **drift** `pole_inversion`; **inversion** `rInv_swaps`. **Never cite `rInv_swaps` for the coincidence** — it proves two points *exchanged*, and there they are provably distinct. This is NOT ⊥ = ε₀, which is false.
- The snap-arc **returns to a bottom, never to ε₀** (`epsilon0_ne_bot`). Proved is the **role** half — anything playing the bottom role IS the bottom (`t_iz_limit_is_new_null`). The **novelty is a commitment, not a theorem**; in the 2-adic realization the arc reapproaches the *same* 0 (`snap_arc_z2_loop`). **Never cite `t_iz_limit_is_new_null` as a witness for novelty.**
COST     each of these was violated in shipped prose by reconstructing from memory; a wrong one
         inside a published PDF cannot be withdrawn.
READ     tools/process/core-objects.md

## R-COMMIT  Commitments go in HYPOTHESES; data goes in BRACKETS.
TRIGGER  you are about to add a field to a `class`/`structure`, or state a theorem whose
         premise the framework asserts rather than derives.
RULE     apply the test — CAN IT BE FALSE? If the carrier either has it or does not, it is
         DATA and belongs in brackets. If the framework asserts it and reality might not
         comply, it is a COMMITMENT and belongs in an explicit hypothesis on the theorems
         that need it. NEVER bundle a commitment into a class. Rollout is AS-TOUCHED: new
         and edited commitments use the hypothesis form now; where an existing class carries
         one, add a companion explicit-hypothesis theorem rather than refactoring.
COST     a commitment in brackets reads as data, which is how `da1_closed_concrete` was cited
         for self-execution for months. This is the only defence that requires nobody to
         remember anything — a signature simply is what it is.
READ     tools/process/commitments-in-hypotheses.md

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

## R-ADJACENT  When the answer is already proved, the deliverable is a POINTER, not a theorem.
TRIGGER  a question arose and you are about to write a new declaration to answer it.
RULE     ask in order: is it proved in this corpus already? is it in Mathlib? is the only
         gap that nobody wrote it where the question gets asked? If the last, write it
         THERE — ONE LINE of consequence at the site, plus a pointer to the canonical home.
         Never a bare pointer, and never a paraphrase. THE TEST: would this sentence become
         false if the canonical statement changed? If yes it is a copy — replace it with a
         line and a pointer. Never enumerate in prose what an artifact defines — counts,
         field lists, "the N conditions". Point, name the load-bearing member, stop. A
         DATED survey is legitimate; a completeness claim is not.
COST     adding an elementary instantiation is what the prior-art gate keeps catching, and a
         paraphrase goes stale the instant the original moves — 10 of 25 sites citing `l_inf`
         paraphrased it, and one rewrite falsified four of them immediately.
READ     tools/process/unstated-adjacency.md

## R-DETERMINISM  Single-valuedness is the obstruction, never the fixed point.
TRIGGER  you are about to write prose about why the bottom cannot move, or about the
         halted / self-looping / stepping-onward trichotomy.
RULE     attribute the obstruction to the step being a FUNCTION, not to the presence of a
         self-loop. A function admits at most one successor; a RELATION can loop at `s` and
         reach elsewhere. Under a function, halted and self-looping share a FATE, so the
         trichotomy is genuinely three-valued only in the non-deterministic setting — the
         function-vs-relation choice is how the framework encodes that modality. Say so.
         Non-determinism buys the POSSIBILITY, never the occurrence.
COST     this was re-derived four separate ways in one session; and "nothing else encodes the
         modality" is too strong — `carry` is a function with no fixed point anywhere whose
         observable projection never changes, which is a fact about a quotient, not determinism.
READ     tools/process/determinism.md

## R-TWOPOLE  Every face of the bottom has TWO readings. Build both, concurrently.
TRIGGER  you are starting fresh development, a face is stuck, or a claim needs an extra
         assumption to close.
RULE     run both, never in sequence: Q1 — where is the zero that runs to infinity? Q2 —
         what is the one-way arrow, and what does it look like run BACKWARDS? If either has
         no answer, the piece is not part of the framework yet; record that as a finding.
         Run it on METHOD too: state the claim from the other side, and ask what words the
         corpus would use if it DISAGREED with you — a single-polarity search has a blind
         half. When flipping genuinely gains nothing, say INVARIANT (the ratified null case)
         rather than forcing a second pole. Call out where Tim's read is load-bearing.
COST     a missing pole shows up as a bridge you cannot formalize — ZP-K implemented only the
         EMPTY reading, so the step to forced execution stayed a commitment rather than a theorem.
READ     tools/process/two-pole-test.md

## R-REVALIDATE  A sentence fixed three times is a CLAIM defect. Measure it; do not redraft.
TRIGGER  the same sentence or `--target` has been re-fixed three times, or the gate round
         reaches 3 — `gate_round.py` prints the protocol at that point.
RULE     stop editing. Name the claim in one line without its framing; ask what would settle
         it and whether anyone did that; probe it in the scratchpad; then restate to exactly
         what was measured, restate as an explicit conjecture, or DELETE the sentence —
         deleting is legitimate and often correct. Record what the MEASUREMENT showed, never
         that you re-worded something. MODAL claims are the high-risk class: ACCIDENTAL is
         proved only by exhibiting the clean proof, ESSENTIAL only by a reduction to a taboo,
         and `#print axioms` follows the STATEMENT, so measure the type, not just the theorem.
COST     the gates check WORDING against SOURCES — they cannot see an unmeasured claim and
         will pass one forever. Six versions and four gate rounds missed one; a probe found
         it in a minute.
READ     tools/process/claim-revalidation.md

## R-NOTINLIB  "Not in the library" is a CLAIM. Probe it before you believe it.
TRIGGER  you are about to write "not in Mathlib", "the corpus does not have", "no instance
         exists", or any dated survey negative.
RULE     a failed `#synth` or grep is evidence about YOUR PROBE, never about the library.
         Confirm the name imports and elaborates; re-run with universes explicit; ask whether
         it DECOMPOSES into pieces that are present; remember attribute-generated siblings
         have no source line, so `#check` is the authority and grep is not. Run THREE
         phrasings varied along axes, never synonyms: POLARITY (how the corpus would say it
         if it DISAGREED with you) · PART OF SPEECH (the verb that builds it, not the noun) ·
         VOCABULARY (the domain's words) · DISPLAY (never conclude absence from TRUNCATED
         output — re-run untruncated or print `file:line` and open the hits). Then write
         "not located as of &lt;date&gt;, searched as follows" — never "absent".
COST     three recorded negatives were false and had already shipped into docstrings as
         measured fact; and correcting them turned "one of four hypotheses holds" into three.
READ     tools/process/not-in-the-library.md

## R-LOOPCAP  Stopping is a decision about SEVERITY, never a wait for silence.
TRIGGER  a review gate has returned findings and you are deciding whether to iterate again.
RULE     ask only: did this round find anything BEDROCK? BEDROCK — a violated core invariant,
         a fabricated claim about a source, a false premise carrying a conclusion — gets up to
         5 rounds and must not ship. ORDINARY — citation scope, a mischaracterized lemma,
         hedging, wording — gets 2, then STOP and push normally. Run `gate_round.py show` for
         the live caps; never maintain a prose copy of them. A STOP-ORDINARY reviewer WRITES
         its signal, so nothing is bypassed. EDIT AFTER A STOP ⇒ RE-SIGN; do not want another
         round ⇒ do not edit. Prose about PREVIOUS STATES is redundant — apply the strip test,
         state the live rule positively, and let the commit message narrate.
COST     the cap's licence assumes findings stay outstanding; acting on them creates NEW
         unreviewed prose — four of one round's six findings landed in the one file no gate
         had seen, which existed only because it was edited after the gates finished.
READ     tools/process/review-loop-cap.md

## R-TRUNC  Never truncate a hook-running command; never write a `--no-verify` fallback.
TRIGGER  you are about to put `| head`, `| grep -q`, `| grep -m`, `| Select-Object -First N`
         or any early-exiting consumer around a command that runs a gate — or to chain
         `|| ... --no-verify`.
RULE     redirect to a file and read it: `python tools/verify/batch.py prepush > log 2>&1`,
         then open the log. `--no-verify` is a separately-typed decision, never a fallback and
         never chained. If a push is blocked, read the reason and fix it — the block is the
         control working.
COST     BOTH bypasses succeed SILENTLY and the push looks green: the identical push exited 1
         bare and 0 through `| head -5`, because the hook died of SIGPIPE before its `exit 1`,
         and the review-signal check runs LAST. A twelve-file push with a stale signal reached
         `origin` that way.
READ     tools/process/push-gate-bypass.md

## R-STAGE  Stage NAMED PATHS. Never `-A` on the main repo.
TRIGGER  you are about to stage anything.
RULE     `stage(paths=['a.lean','b.md'])` — the specific paths you edited. Then
         `read(op='status', args=['--short'])` and confirm every staged path is one you meant
         to touch; if an unexpected one appears, find out where it came from before committing.
         `.claude-local` is exempt and bulk staging is its documented flow.
COST     background agents write to this checkout concurrently, so the tree is not a stable
         snapshot — a review agent's scratch probe was swept into a commit that way and is in
         the permanent history. `gitRobot.stage` now refuses `-A` outright, so there is nothing
         left to remember.
READ     tools/process/staging.md

## R-ER  Editorial review completes BEFORE the commit that touches document prose.
TRIGGER  you are about to commit a change to a build script's prose, a README/GUIDE/RELEASES/
         register edit, or any root `.md` other than `CLAUDE.md`.
RULE     run `/editorial-review` in a FRESH agent — same-session self-review does not satisfy
         it — and PASS IT THE FILE PATHS EXPLICITLY. On FAIL, clear every kill-list item before
         committing. On PASS the agent writes `.claude-local/er_cleared.txt` recording the
         SHA-256 of each reviewed file, computed FROM THE FILE ON DISK, never from a git value.
COST     `MIG-3`: pre-commit mode discovers its own scope with a now-denied git call, and the
         denial FAILS OPEN — the empty result reads as "nothing staged", the brief falls back to
         Full Scan, and it still writes a signal hashing whatever it happened to open.
READ     tools/process/review-gates.md

## R-AR  Adversary review completes BEFORE anything reaches an external reader.
TRIGGER  you are about to push prose, send an email, post or edit a GitHub Discussion or Issue,
         or surface any content outside this repository.
RULE     ask Tim explicitly: "Adversary review complete for this content?" and WAIT for
         confirmation — never self-assess whether review is needed. If it has not run, offer
         `/adversary-review` first. It must be a separate adversarial context, never this one.
         On PASS the agent writes `.claude-local/ar_cleared.txt` with a SHA-256 per reviewed
         file. Only after explicit confirmation may the public-facing action execute.
COST     docstring and build-script prose was pushed before review ran, and the review then
         found two further precision errors in already-committed content.
READ     tools/process/review-gates.md

## R-PRIORART  Search BEFORE you build, and the gate runs after.
TRIGGER  you can state the claim in one sentence of standard mathematical English and are
         about to write Lean; or a synthesis layer is created, its central claim revised, a
         layer prepared for outreach, a reviewer asks "have you seen X?", or a new `.lean`
         file / >=50 net new lines lands.
RULE     three steps, ~10 minutes, BEFORE building. (1) grep our own corpus. (2) grep the
         pinned Mathlib for the CONCEPT — and if the claim is a Lean statement, RUN `exact?`;
         it searches statement SHAPE, not names, and reaches attribute-generated siblings
         that have no source line. (3) one literature search, run as the four-rung LADDER:
         `.claude-local/papers/` → `theoremsearch` → the open web → RETRIEVE THE FULL
         DOCUMENT. Three phrasings minimum at rung 2; ignore its similarity score; its null
         is UNINFORMATIVE. Rungs 1–3 are DISCOVERY, only rung 4 is VERIFICATION — a returned
         theorem body is not a passage in hand. Standard framing, once found, is ADOPTED, not
         noted and worked around; check purity before swapping a proof. `/prior-art-review`
         is the deep gate, a fresh agent, and on PASS it writes `.claude-local/pa_cleared.txt`.
         If you cannot yet state the claim, build first — then SEARCH BEFORE PROMOTING,
         because a survey that became a theorem restarts the clock.
COST     an uncited closest prior art reads as unaware — the crank-triage failure. And
         searching first gets you MORE: one round yielded a stronger theorem than our own
         claim, a purer proof, free lemmas, and the standard NAME for a thing described longhand.
READ     tools/process/prior-art.md

## R-CONTEXT  What this repository is, and where a file belongs.
TRIGGER  you are orienting in this repo, or deciding where a new file goes.
RULE     this is a mathematical PUBLICATION repository first: the PDFs and the Lean corpus
         under `ZeroParadox/` (indexed by `ZeroParadox/MANIFEST.md`) are the point, and the
         tooling exists to keep them honest. Formal documents live at the root under FLAT,
         version-free filenames — versions live in `register.md` and each PDF's title block,
         never in a filename. Superseded versions are NOT archived: overwrite the flat root
         PDF in place and let history plus each release's Zenodo snapshot be the record. Do
         not recreate `historical/`, and never rewrite history to purge old binaries —
         SHA-pinned permalinks and DOI-referenced commits depend on them. `.claude-local/` is
         its OWN repository with a private remote: commit AND PUSH it; the parent additionally
         ignores the path. Prose exists only to restate mathematics accessibly; finalized
         documents are structured as an ontology; completed work is committed immediately.
COST     `historical/` drifted a month stale while the snapshots did not; and reasoning from
         the ignore entry alone concludes the only copy is on disk, which is how three commits
         sat unpushed on one machine.
READ     tools/process/repository-layout.md

## R-RELEASE  A release is Tim's action. An agent's role ends at a green gate.
TRIGGER  Tim initiates a release, or you are about to draft a release body or a tag.
RULE     `python tools/verify/check_release_ready.py <tag>` must EXIT 0 and its judgement
         checklist must be confirmed BEFORE the release body is drafted. It verifies the
         deterministic preconditions — Engineer's Takes filled (recursive glob over
         `ZeroParadox/**/*.lean`), build-script hashes against `register.md`, the
         `LEAN_CUSTOM_REGISTRY` invariant, `.zenodo.json` valid and its description current,
         no conflict markers, a `## <tag>` entry in `RELEASES.md`, every linked PDF present.
         **NO RELEASE WHILE `DEFECTS.md` IS NON-EMPTY.** Then STOP: creating the release is
         Tim's command, never an agent's. Major = a new formal layer or a theorem status
         change; minor = a substantive feedback round or accumulated updates. Never release
         per-PR. A Lean-only milestone is an explicit QUESTION for Tim, not an automatic
         trigger either way.
COST     a release mints a PERMANENT Zenodo DOI and four already carry latent flaws that
         cannot be withdrawn. Deposited FILES are frozen; record METADATA can still be
         corrected in the Zenodo UI, so a wrong release description is fixable and a flaw
         inside a published PDF is not.
READ     tools/process/document-workflow.md

## R-REGISTER  `register.md` is canonical. Update it FIRST, then propagate.
TRIGGER  you are bumping any document or companion version, or editing a build script.
RULE     order matters: (1) `register.md` — formal version, filename, companion version;
         (2) README.md's Framework table, the single derived copy. That is the whole
         propagation path. GUIDE.md carries NO version numbers, deliberately — never "sync"
         one into it; that is a regression to revert. Any build-script change takes all four
         steps in ONE commit: edit, bump the internal version, rebuild the PDF, recompute the
         `formal:` / `comp:` hash token in `register.md`. A document's own version appears in
         exactly ONE rendered place, the subtitle meta line — no self-changelogs, no
         `[new in v1.7]` tags; cross-document citations are exempt.
COST     a hash mismatch does not mean "rebuild needed", it means the version bump was
         SKIPPED — do not rebuild without incrementing. `check_hashes.py` compares
         `register.md` against README on every run and found five stale rows on its first.
READ     tools/process/document-workflow.md

## R-DIAGRAM  Diagram bounds are build-enforced; internal collisions are not.
TRIGGER  you are adding or editing a `Drawing` in any companion build script.
RULE     never derive `cy` from `dh` when the diagram holds fixed-size elements — use a fixed
         numeric `cy`. Keep `max_y < dh - 10` and `min_y > 5`. Drop internal title strings
         that duplicate the caption. Express `dh` in inches with a comment giving content top
         and bottom. `zp_utils` validates every `Drawing` at `doc.build()` and HARD-FAILS on
         escape, so a forgotten check can no longer ship one.
COST     the bounds gate cannot see INTERNAL collisions — two elements overlapping inside the
         box. Every build prints a diagram-page report; eyeball those pages on any
         diagram-touching build before commit.
READ     tools/process/document-workflow.md

## R-COMPANION  A formal document and its companion move together.
TRIGGER  you updated a formal document, or you are touching any rendered PDF text.
RULE     review the companion IN THE SAME SESSION and bump its internal version in the SAME
         commit; companion versions are independent of formal versions, and what matters is
         that the companion is not materially stale. Read
         `scripts/PDF_Rendering_Standards.md` before building ANY PDF. When a vocabulary
         problem is surfaced by anyone, update `.claude-local/vocabulary_reference.md` in the
         same session and log the term — both directions, wrong-term and needs-a-gloss.
COST     a general reader meets the framework in the companion, so a stale key-result box
         misdescribes what is proved.
READ     tools/process/document-workflow.md

## R-SCRIPTS  `scripts/` is the build scripts' only home. There is no mirror.
TRIGGER  you are editing, adding, or looking for a PDF build script.
RULE     edit the file in `scripts/` and commit it like any other source file — there is no
         copy step. A new script gets a row in `scripts/README.md` in the same commit. The
         fonts ship beside them under `scripts/fonts/` with their licences, so a clone can
         actually build; if a font is added or replaced, read its `name` table id 13 and ship
         whatever licence it declares. Five scripts remain private-only and none emits a
         tracked artifact — `scripts/build_dictionary_map.py` imports one and says so rather
         than raising `ModuleNotFoundError`.
COST     the retired mirror asked a human to remember a copy step while `register.md`
         fingerprinted only the PRIVATE copy — so the PUBLISHED script sat outside the
         integrity check and drifted three months unnoticed. A mirror plus a discipline adds
         a way to be wrong and removes the way to detect it.
READ     tools/process/repository-layout.md

## R-LEANPDF  Verify a Lean encoding at the source before stating it anywhere.
TRIGGER  you are about to state a Lean type name, constructor, or theorem STATUS in a PDF,
         companion, README, or correspondence.
RULE     open the actual `.lean` file and check; never rely on memory or prior documentation.
         No automated checker covers status labels or encoding descriptions — the session
         workflow IS the mechanism, so cross-check the PDF script and companion in the same
         session as any Lean status change. File references in CHECKABLE surfaces carry the
         FULL repository path (`ZeroParadox/<Domain>/<Name>.lean`); declaration names stay
         BARE and unprefixed; flowing companion prose may use a bare basename. Rollout is
         as-touched, never a retrofit round.
COST     a full path fails LOUD when a file moves; a bare basename fails SILENT — plausible
         and pointing nowhere. `Fin 2` survived in three surfaces after the Lean moved to
         `OntologicalStates`, until a reviewer asked.
READ     tools/process/document-workflow.md

## R-SHELL  This is Windows. PowerShell syntax, and never prepend `cd`.
TRIGGER  you are about to run a shell command or search for a file.
RULE     use the `PowerShell` tool, not Bash with Unix commands. Use `Glob` for file discovery
         — never `find`, which hangs here. `Get-ChildItem` not `ls`; `Move-Item` not `mv`.
         Backslash paths in PowerShell, forward slash in Lean/lake config. The working
         directory is already the repo root: never prepend `cd` or `Set-Location`. Every call
         invoking an external process (a build script, `lake build`, `python <script>`) uses
         `timeout: 300000`; if it times out, diagnose rather than retry blindly.
COST     a prepended `cd` produces a command string that misses the allowlist and triggers an
         avoidable permission prompt.

## R-INDEXES  README is the formal index; GUIDE is the general-reader hub.
TRIGGER  a document is versioned up, an open question closes, a claim's status changes, or a
         document is added or archived.
RULE     audit BOTH files. Preserve the section order in each — do not add top-level
         sections, reorder, or drop terminal ones without agreement. `check_hashes.py`
         mechanically compares `register.md` against README's Framework table on every run,
         joined on the PDF FILENAME, never the `ZP-X` code (four register rows begin `ZP-J`).
         Check GUIDE's link TARGETS resolve, and never sync a version into it. Where a
         document's STATUS could mislead — speculative, superseded, a development artifact —
         say so in its own opening because it is TRUE, not because a linkage rule fired.
COST     the retired transparency-notice rule bound seven files and exactly one honoured it,
         because it measured "is this linked?" when what matters is "would a reader be misled
         about why this exists?" Those came apart twice.
READ     tools/process/indexes-and-superseding.md

## R-NAMING  Label a result by whether it is the section's central claim or its infrastructure.
TRIGGER  you are naming or relabelling a result in any formal ZP document.
RULE     ask: is this the CENTRAL claim of its section, or infrastructure for something else?
         **Theorem** — the primary result, driving the dependency chain (T3, T-SNAP).
         **Proposition** — rigorously proved but subsidiary. **Lemma** — a stepping stone.
         **Corollary** — follows immediately, no substantial work. **Conditional Claim (CC)** —
         holds only given an explicit modelling commitment. **Design Principle (DP)** — chosen,
         not derived. **Remark (R)** — context, no proof.
         Readable names are ADDITIVE, never eliminative: CC-2 is "the Quine atom (CC-2)",
         glossed once as the self-containing bottom; MC-1 is "the bottom family" and gets NO
         new readable name, because its object already has one — the diagonal fixed point.
         Keep every formal handle; never rename or remove an identifier. AX-1 is Theorem
         T-SNAP — never call it an axiom.
COST     the prefixes go stale as status changes and the label then misdescribes what is
         proved: CC-2's "Conditional Claim" outlived its own upgrade, and MC-1's numerical
         identity is RETIRED as ill-typed — `x = y` across distinct categories was never a
         well-formed proposition, so it was never a commitment either.
READ     tools/process/naming-and-labels.md

## R-ISSUES  Public issues are transparency, not a request for validation.
TRIGGER  you are about to file, or are being asked about, a public GitHub Issue or Discussion.
RULE     file genuinely unresolved framework open questions and substantive technical
         questions that review left open — framed as specific, honest about uncertainty, and
         standalone without requiring knowledge of the framework. NEVER file anything sourced
         from private correspondence, reviewer identity or feedback, outreach strategy or
         drafts, or editorial decisions; those belong in `.claude-local/`. Record every
         outreach item's external identifier in `.claude-local/outreach/tracker.md` AT THE
         MOMENT it is created or sent — a Discussion or Issue `#N`, a full URL, a date plus
         recipient for email, a stream and topic, an arXiv id. If an identifier is missing,
         add it before doing any other work in that session.
COST     issues are the public record of what is open or contested; an issue that reads as
         seeking validation converts a transparency mechanism into an outreach one.
READ     tools/process/naming-and-labels.md

## R-FRAMEWORK  The layer dependency order, and the one substantive commitment.
TRIGGER  you need the framework's shape, or are about to describe a layer's status.
RULE     dependency order: **ZP-A** (lattice) → **ZP-B** (p-adic) → **ZP-C** (information) →
         **ZP-D** (state) → **ZP-E** (DA-1 / T-SNAP). **ZP-G** (category) → **ZP-H** (bridge)
         is self-contained — conceptually downstream of ZP-E, formally independent. Each
         formal document has a paired illustrated companion. AX-G1 and AX-G2 are grounded,
         not novel. **AX-B1 is the framework's ONE substantive modelling commitment** —
         discrete Boolean existence, not a continuum of partial states — so never call it
         "directly verifiable" or "not a novel commitment"; the `decide` proof only checks
         the two states are distinct GIVEN the two-element type. AX-1 is Theorem T-SNAP.
COST     the ZP-C forcing lemmas discharge the no-half-state worry but force only the
         >=2-outcome lower bound; the residual commitment is DISCRETENESS, which they do not
         eliminate and which the reals lack — the snap fails there (`f_snap_impossible`).
READ     tools/process/repository-layout.md

## R-HANDOFF  "Update the handoff" is a compound action defined in the file itself.
TRIGGER  the session is ending, a context switch is planned, or someone says "update the handoff".
RULE     read `.claude-local/handoff.md` FIRST at session start; overwrite it at the end. Two
         parts in order: the THREAD (live orientation for resuming mid-thought), then the
         LEDGER (what was done, the next action, what was deferred). One file, always current.
         The full procedure is PART 0b of that file — do not restate it here; it closes finished
         tickets by MOVING them to `queue/done/`, opens tickets for what was found, COMMITS AND
         PUSHES the private repo, and reports main-repo state.
COST     overwriting is safe only because `.claude-local` is a repo, and that is the step with
         the measured failure history — 120 uncommitted entries, 86 notes never once committed,
         and an unstarted item that vanished for five revisions.

## R-CAPTURE  Capture a high-value insight immediately; the POINTER is the deliverable.
TRIGGER  a structural connection, a cross-domain identification, a derivability conjecture, a
         purity result, or anything that partially closes an open question surfaces.
RULE     write `.claude-local/notes/<topic>_YYYY-MM-DD.md` now, without being asked: the
         insight in plain language, the precise claim, what is formal versus conjectural, the
         status, and links to related notes. THEN WIRE IT to the artifact — a line in the
         `.lean` docstring, `CLAUDE.md`, or a memory — because the note is the draft and being
         pointed at from a read surface is the durable act. Active notes only in `notes/`; open
         work in `notes/future-research/`; history in `notes/archive/`. Prefer KEEP when torn.
COST     only ~10% of 767 notes were ever referenced again, and on one day four findings were
         rediscovered the slow way while the relevant note sat unread. Worse, a note recording
         PENDING work goes FALSE the moment the work is done — never act on a note's
         self-reported status; verify at the artifact.

## R-DEVMODE  Before fresh development, load the subsystem. Do not start from targeted search.
TRIGGER  you are beginning fresh mathematical development.
RULE     `python .claude-local/where.py "<Tim's phrasing, verbatim>"` for ranked folders and
         token cost, `--files` for the list, `--spine` for the always-load core. Then load the
         ~50k spine — the five `#check`-only indexes plus `MANIFEST.md`, `CLAIMS.md`,
         `BOTTOMELEMENT.md`, `SNAP.md` — plus the one or two folders it names. Load two or
         three; it produces a SHORTLIST, not an answer, and it cannot route a concept with no
         corpus vocabulary. Tim's Engineer's Takes are the bridge between his register and the
         Lean body, and all of them together are cheap enough to load wholesale.
COST     every real finding comes from COLLIDING two facts, and you cannot collide facts you
         are fetching one at a time. Not this for error-sweeps: a claim-sweep's unit is the
         RENDERED PDF text, never the source.

## R-LEANDEV  Stub first. Build, commit, then fill proofs one at a time.
TRIGGER  you are creating a new `.lean` file or starting a proof.
RULE     map each symbol to its Mathlib equivalent and identify heavy imports BEFORE writing
         Lean. Write the complete file with every proof `sorry`, `set_option maxHeartbeats
         400000`, and STOP — wait for a clean build. Commit the stub as a rollback point. Fill
         one theorem at a time, building and committing after each. Build as TWO separate
         calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8`, then read the
         log — never combined with `;`. When done: zero errors and warnings, a `#print axioms`
         block per proved theorem inside `section PurityCheck`, README updated, and the SJV
         registry synced (`migrate_batch` → `annotate_many` → `validate` + `verify_integrity`
         → `export_full` to an ABSOLUTE path) in the SAME change. Search Lean files as
         `ZeroParadox/**/*.lean`, never `**/*.lean` — `.lake/` holds thousands of Mathlib files.
COST     heavy import chains (p-adics plus Hilbert space) hang the elaborator, and an unsynced
         declaration re-introduces the registry drift the ontology revamp eliminated.
READ     tools/process/lean-development.md

## R-BRANCH  All work happens on `illustrated`. Sync before you start.
TRIGGER  you are starting a session, or about to make your first edit.
RULE     all Lean and PDF work happens on `illustrated`; `main` is production/public;
         `lake_testing` is RETIRED — never switch to it or push to it. At session start
         `fetch()` then `merge(branch='origin/main', ...)` before making any change, so you
         never edit against a stale base. `merge` is REFUSED while the tree is dirty — that is
         deliberate, and the answer is to commit first or take a worktree, never to force it.
         After ANY merge, `read(op='diff', args=['--check'])` to confirm no conflict markers
         survive. Both `.lean` files and PDF build scripts are first-class here.
COST     a file with unresolved conflict markers commits SILENTLY and corrupts the document.
         That has happened twice on this project.

## License

CC BY-NC-ND 4.0 — share with attribution; no modifications; no commercial use.

