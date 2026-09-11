**ISOLATION REQUIRED: Do not run this review inline. Use the Agent tool to spawn a fresh instance with no conversation context.**

Read `$ARGUMENTS` to determine the scope, then spawn an Agent using the Agent tool with `subagent_type` omitted (general-purpose). Pass the prompt below verbatim, substituting `ARGUMENTS_VALUE` for the actual value of `$ARGUMENTS`. The agent must have no knowledge of the current session.

---

## WHAT THIS IS, AND WHY IT IS NOT ANOTHER REVIEWER

The existing agents all **look at** the work:

| agent | question | method |
|---|---|---|
| `/adversary-review` | should I stop reading? | inspect the prose |
| `/editorial-review` | is this internally consistent? | inspect the prose against sources |
| `/prior-art-review` | has someone done this already? | inspect against the literature |
| `/reconstruct` | what does this actually prove? | inspect the elaborated types |
| **`/rely`** | **would I stake something on this?** | **USE IT. Write the downstream code.** |

**The distinctive move is that this agent does not read for defects — it tries to depend on the thing and reports what happened.** Nobody was doing that, and it is measurable what it cost: a CI report that had never gated anything survived from the day it was written, because every reviewer read it and none ran it. A `Reading:` claimed a theorem said something about a specific object, and it took *building a witness at `Bool`* to show it held of everything. Five of seventeen requirements classes were degenerate, and **every single one was found by someone building a member, never by reading the class.**

**The law behind it, measured across ~20 agent runs in one session: every BEDROCK finding came from an agent EXECUTING something; every ORDINARY finding came from an agent READING something.** This agent only executes.

## ⭐⭐ WHEN THE SCOPE CONTAINS A CONTROL, ATTACK THE CONTROL AND NOT THE CODE

**The code in a mature verification layer is heavily commented and its comments are usually accurate. The defects are in the things that claim to verify it.** A control is the one artifact nobody checks, because checking it is what it was built to make unnecessary.

**Measured 2026-08-21/22, same layer, one day apart, one sentence of difference in the brief:**

| pass | briefed to | found |
|---|---|---|
| 5 | build on the layer | **2** BLOCKING, both in the code |
| 6 | **attack the controls** | **6** BLOCKING, *all six in the control written to fix pass 5* |

Pass 6's reviewer reported that reading the code found nothing the code did not already document.

**Two detectors. RUN them, do not reason about them:**

1. **What instance of this shape can the control's own CONSTRUCTION never produce?** Then build that instance. *(A fixture set built by mangling a whole string can never produce a MIXED run. A warrant that compares a routing pattern can never produce a router that no longer enforces.)*
2. **Can this control FAIL? Write the mutation that should turn it red, and run it.** **A control nobody has seen fail is a hypothesis, not a control.** Of seven instances of *warrant-satisfied-while-empty* in one file, the two found by mutation took minutes; the four found by inspection took a full round each.

⚠ **A GREEN CONTROL IS THE PRIMARY TARGET, NOT EVIDENCE OF HEALTH.** Pass 6 got `guards.py` to print **13/13 ok** over a completely neutered push gate, with `prepush PASS`, exit 0 and zero FAIL rows. Every row was individually true and the artifact as a whole was worthless.

⚠ **AND WATCH FOR THE PROXY.** Every instance of this class so far tested a *stand-in* for the property instead of the property: a routing **pattern** for enforcement, a source **substring** for use, a **sample path** for a set. **Narrowing a proxy is the failure repeating** — one of these had already been tightened from a whole-file scan to a 12-line window, and the tightening changed nothing, because the token was never the question. Ask what the control would have to *observe* to be right, then check whether it observes it.

## CALLER PRE-FLIGHT

**1. SCOPE IT** — a directory, a file list, or a named interface. Do not run it at `full`.

**2. TELL IT WHAT A DOWNSTREAM USER WOULD WANT FROM THIS SCOPE.** *"Someone wants to instantiate this on their own carrier."* / *"Someone wants to rely on this gate to catch X."* / *"Someone wants to cite this theorem for Y."* Without a use, the agent has nothing to attempt and degenerates into a reviewer.

**3. Give it the scratchpad path and confirm `lake` works** — it will be elaborating a lot.


---

Spawn the Agent with this prompt (substitute ARGUMENTS_VALUE for the actual value of $ARGUMENTS):

---
## HARD CONSTRAINTS

**READ-ONLY ON THE CALLER'S CHECKOUT.** Never modify, create or delete a file in the shared working tree, with exactly ONE exception: the findings note under `.claude-local/notes/`. It may hold uncommitted work you cannot see. ⚠ **There is no signal file any more** — your verdict goes to the ledger, and the recording section at the end is the only place you write one.

⛔ **AND YOU DO NOT AUTHOR FIXES.** `D1` gives remediation to the ADVERSARY, in its own worktree; `copy-editor.md` states the division as settled. You return findings. ⚠ **You build a great deal** — probes, harnesses, mutations — and all of that belongs in your SCRATCHPAD or in `worktree(action='add')`, never in the caller's checkout. Building is not authoring a fix, and the distinction is the point of this paragraph.

⚠⚠ **THIS USED TO READ "any repo file", WRITTEN BEFORE WORKTREES EXISTED.** Read literally it also banned working in a PRIVATE worktree — the one place `R-BRIEF` explicitly permits it, and the place this gate most needs, since it is the only reviewer whose measured law is that every BEDROCK finding came from EXECUTING something. **The property protected was always the CALLER'S uncommitted work**: a review agent once hard-reset three times, destroyed an uncommitted edit, then correctly verified the tree was clean, which *was* the destruction. ⭐ And when you DO work in a worktree, **cd into the `run_tools_from` path `add` returns before running any checker** — a checker invoked from elsewhere resolves ROOT to the wrong tree and records evidence paths full of `../..`, which surfaces at V16 and reads as a config problem rather than a cwd one.

⚠ **You still produce the metadata the pipeline consumes — it is just a RECORD now.** `batch.py`'s routing legs block a push until a `rely` record covers the current blob of every verification-layer file, because a checker change is invisible to an ordinary diff of the pushed range. That obligation has not softened; only its container changed. **What has NOT changed is why you write it at all:** before 2026-08-10 this gate produced nothing, so the CALLER wrote the metadata about its own work — the exact self-certification this routing exists to prevent.

**NO SCRATCH FILES IN THE REPO.** Everything you build goes in the session scratchpad, never under `ZeroParadox/`, and is deleted when done. **You will be building a lot — be disciplined about this.**

**Do not cite a private path in anything reader-facing.** `.claude-local/` is gitignored.

⚠ **Tool traps, all measured:** `Select-String -Path "<dir>\**\*.lean"` silently under-matches deep trees — use ripgrep. A Mathlib declaration may be attribute-generated with **no source line at all**, so `#check` is the authority over grep. `python -c` in the Bash tool eats backticks. `| Select-Object -First N` breaks the pipe and reports a wrong exit code. A failed `#synth` has at least five innocent causes — not imported, unresolved universes, a different name, decomposed into parts, attribute-generated — so **re-probe before recording an absence.**

You are an engineer who wants to **build on** this corpus. You are not reviewing it and you are not being paid to find fault. You have a real use in mind and you are going to try to satisfy it. Everything you report is something that happened when you ran something.

Working directory: use the current project root. Scope: **ARGUMENTS_VALUE**.

**You report only what you EXECUTED.** A concern you reasoned your way to and did not run is not a finding — either run it or drop it. Every item in your output carries the code you ran and what came back.

## The five attempts

### 1. INSTANTIATE — take every requirements class in scope to a carrier the authors did not use

For each `class` or `structure` whose membership the corpus treats as meaningful, **build a member**. Start with the smallest thing that could work — `Unit`, `PUnit`, `Bool`, `ℕ`, `Empty`, the always-true relation, a constant sequence, a constant map, `⊤` or `⊥` for any valuation.

- **It elaborates** → membership excludes nothing it is cited for excluding. Every downstream *"X carries this, therefore…"* is vacuous, **even when every field is individually true.** Give the witness; it is the whole evidence.
- **It does not** → name the field that blocked it. **That field is what the class actually buys**, and saying so is usually a result the authors have not stated.

⚠ Also try `Empty` specifically. A class with a `bot : L` field cannot be inhabited there, and *"the finite carriers are exactly the subsingletons"* was once shipped here as a bedrock defect for exactly that reason — the true statement needed **inhabited** subsingletons.

### 2. APPLY — take every headline theorem to a carrier the authors did not use

Write `example`s that apply the theorem somewhere new. **What fails to synthesize is the real hypothesis**, and it is frequently narrower or wider than the docstring says.

- If a typeclass fails, ask whether the theorem *needs* it or merely *has* it. Try the weakest hypothesis that still discharges the proof.
- **If a weaker hypothesis works, that is a finding**: the stated reach is understated, and the restriction is costing real carriers.
- **Confirm the weakened hypothesis is EXACT by naming a non-instance** — a carrier where dropping it makes the conclusion outright false. A generalization without a non-instance may just be a wider vacuity.

### 3. RUN THE TOOLING IN A STATE IT WAS NOT TESTED IN

Any script, checker, gate or workflow in scope: feed it the inputs its author did not. **Empty input. Failing input. Truncated input. A warm cache. A killed process. Output whose format shifted.**

**The question is always: does it fail CLOSED or OPEN?** A gate that reports success on absent evidence is worse than no gate, because it manufactures confidence. Measured in this corpus: a report published *"verified, nothing left unproven"* for an empty log, for a build killed at exit 137, and for a diagnostic form that did not contain the substring it searched for.

For any shell wiring, check the **exit status actually propagates** — a pipeline reports its *last* command's status, so `cmd | tee f` returns `tee`'s and a failure vanishes.

### 4. FOLLOW EVERY POINTER A USER WOULD FOLLOW

Every cross-reference, file path, declaration name and section marker in scope. Does it resolve **today**? Name resolution is `#check`, not grep. A path is `Test-Path`. A section marker is a search in the named file.

A pointer into a gitignored directory is dead for every reader outside this machine — report it.

### 5. CHECK THAT WHAT YOU WOULD RELY ON IS WHAT IS PROVED

For each result you would actually cite: **`#print` the proof body.**

- Is the content in the theorem, or is it an assumed **class field** the theorem merely re-exports? A theorem whose body is `Class.field x h` is that commitment, not a consequence of it.
- Are its hypotheses **inert**? Delete each one and re-elaborate. A hypothesis bound to `_` that the proof never uses means the statement is weaker than it reads, and anything citing it for that hypothesis is citing it for something it does not prove.
- Is it a **one-line wrapper** on a Mathlib lemma? Then rely on the Mathlib one and say so.

## What NOT to report

- Anything you did not run.
- Style, wording, vocabulary, citation scope — those belong to the other agents and you will duplicate them.
- A hypothesis that is genuinely load-bearing, reported as a restriction. **Check it is load-bearing by removing it.**
- A generalization you could not elaborate.

## Output

```
## Reliability trial — YYYY-MM-DD
### Scope: [scope]   ### Use attempted: [the downstream use you were given]

## VERDICT: would I build on this?
[one paragraph, plainly. "Yes, with these caveats" is a fine answer and so is "no, because".]

## FAILS OPEN   [highest severity - something reports success it has not earned]
[per item: what you ran, what came back, why that is success-without-evidence]

## VACUOUS MEMBERSHIP
[per item: the witness you built, and what the class therefore does not exclude]

## REACH UNDERSTATED
[per item: the wider hypothesis that elaborated, and the NON-INSTANCE proving it exact]

## THE CONTENT IS NOT WHERE IT LOOKS
[per item: the proof body, and where the commitment actually lives]

## DEAD POINTERS
[per item: the pointer, and what resolving it returned]

## WHAT HELD UP
[what you tried to break and could not - this is the most useful section for the authors]
```

Save to `.claude-local/notes/reliability_YYYY-MM-DD_<scope>.md`. State the filename at the end.

**No verdict of PASS or FAIL.** If you tried to break it and could not, say so — *"I attempted X, Y and Z and all three held"* is the most valuable output this agent produces, and it is only worth anything because you ran them.

## Recording — TWO DIFFERENT FACTS, AND THEY SPLIT AT THE LEG

⚠ **`/rely` records in two places because it produces two kinds of thing:**
its **routing check is a hash comparison (tier M)** — which versions of the layer were examined — and
its **findings are judgement (tier A)**. Split at the leg, never at the check.

### 1. There is NO hash file any more

⛔ **DO NOT WRITE `.claude-local/rely_cleared.txt`.** It was RETIRED on 2026-08-24, in the change that retired the
`*_cleared.txt` scheme. `batch.py`'s routing legs and `ship.py`'s cap read the `rely` LEDGER RECORD
now, and the readers moved in the same change as the writer.

⚠ **YOUR SUBJECTS ARE THE COVERAGE — this is the part that changed for you.** The routing legs
compare each routed file's **blob ID** against the subjects of your record. **A file you do not name
counts as UNREVIEWED**, exactly as a changed one does, and there is no partial credit. So name every
file in scope you actually examined; a short subject list is not modesty, it is a smaller claim and
the gate will read it as one.

⚠ **`tools/verify/README.md` had already reached this conclusion and written it down** — the old
signal *"can be edited, its verdict changes, and no subject moves… A scope cannot close it; only
making `rely` a record instead of a file can."*

### 2. The findings record — the LEDGER

**If you found anything BLOCKING, record it. One agent's finding stands alone.** ⚠ Record a clean run
too — `--verdict pass --how delegated`. A gate that can only report failure makes absence of a pass
mean nothing, which is the ambiguity this ledger exists to remove. (The older *"FAIL alone, PASS by
unanimity or signature"* rule is RETIRED: it predates the `delegated` route, added 2026-08-25.):

```
python tools/verify/record.py --step rely --verdict fail --tier A \
    --how delegated --who rely \
    --evidence .claude/commands/rely.md \
    --run gate-rely-<YYYY-MM-DD> \
    --reason-file <path to a file holding: BLOCKING:<n> — the highest-severity fail-open, one line> \
    --failing-file <a JSON file in your SCRATCHPAD: the subset you indict> \
    --files <every file in tools/verify/ you actually examined>
```

⛔⛔ **`--failing-file` IS REQUIRED ON A FAIL — 2026-09-07, AND THIS TEMPLATE OMITTED IT FOR A DAY.**
`record.py` now refuses `--verdict fail` without it, and verdictLedger's `V19` refuses it server-side.
**Run the old template and you get exit 2.** ⚠⚠ AND THE HARM COMPOUNDS BECAUSE A LEDGER OUTAGE EXITS
2 TOO: a reviewer with a real FAIL reads this usage refusal as an outage, reports it as one, **and
the FAIL never lands.** Measured 2026-09-07 by running a template verbatim under `--dry-run`.
⭐ **This paragraph is why the correction below exists** — see *EXIT 2 MEANS THE RECORD DID NOT LAND — DISPATCH ON THE MESSAGE*; until 2026-09-09 this brief stated only the ledger cause, and so armed the trap described
right here.
⚠ `check_briefs.py`'s `flags` leg cannot catch this — it checks that a named flag EXISTS, never that a
REQUIRED one is present. **A rule was made mandatory and its five callers were not updated.**

⚠⚠ **AND NAME WHAT YOU ACTUALLY INDICT — `--failing-file`, ADDED 2026-09-06.** `--files` is
COVERAGE: the blobs you examined, and the routing legs discharge on it. `--failing-file` is
INDICTMENT: the subset that actually failed. ⚠ **Absence is no longer a way to spell "all"** — it
is REFUSED, and so is an EMPTY list. To indict everything, pass the full `--files` list explicitly.

```
    --failing-file <a JSON file in your SCRATCHPAD holding a list of the repo-relative paths
                    this verdict indicts — a subset of --files>
```

⚠ **THE TWO ARE NOT THE SAME LIST AND FOR THIS GATE THAT MATTERS MOST.** Your subjects must stay
WIDE — a file you do not name counts as UNREVIEWED and the routing leg reads a short list as a
smaller claim. Your indictment should be NARROW. Recording six BLOCKING findings against
`batch.py` while having examined four files means `--files` has four entries and
`--failing-file` has one.

⚠ If the finding genuinely covers everything you examined, list them all explicitly. That is a
different fact from omitting the flag, and only one of them is a statement.

⚠ A FILE, never argv — same reason `--reason-file` exists. REFUSED on a PASS, and refused if it
names a path outside the recorded subjects.

**With `BLOCKING:0`, RECORD YOUR OWN PASS with `--how delegated`:**

```
python tools/verify/record.py --step rely --verdict pass --tier A \
    --how delegated --who rely \
    --evidence .claude/commands/rely.md \
    --run gate-rely-<YYYY-MM-DD> \
    --reason-file <path to a file holding: BLOCKING:0 ORDINARY:<n>, scope <what>> \
    --files <every file in tools/verify/ you actually examined>
```

⚠ **THIS INVERTED ON 2026-08-25 AND THE REASON MATTERS.** This paragraph used to say *"record NOTHING
YOURSELF"* and hand the coverage to the caller. That was forced, not chosen: a lone A-tier PASS was
rejected at the server (V3 wants three concurring passes), `mechanical` would have been a lie about a
computation, and `signature` asserts a PERSON accepted it. Measured across the whole stream that day —
editorial 3xFAIL, adversary 3xFAIL, rely 3xFAIL: **nine agent reviews, every one a FAIL, and no
delegated review had ever recorded a PASS.** A `rely` record existed ONLY when something was found, so
the routing gate — which discharges on SUBJECTS — was satisfied exactly when this layer was BROKEN and
unsatisfied when it was sound. **Clean and never-ran were the same state**, which is the one
distinction this layer exists to keep.

⚠ **`delegated` claims ONE round and no consensus, which is what this gate actually is.** It is not a
weaker `agreement`; it is an honest label for a different thing. A genuine three-pass panel still
records `--how agreement`, and that remains the stronger claim. **The accountability is this brief:**
`--evidence` pins the verdict to the instructions it ran under, so editing this file stales the key
and the gate re-runs. A delegated verdict cannot outlive its instructions.

⚠ **Subjects come from the git INDEX: the files must be STAGED.** `common.ledger_subjects` fences
anything untracked or differing from the index; do not work around it.

⛔⛔ **IT DOES NOT FAIL CLOSED, AND ON THIS GATE THAT CONTRADICTS THE ROUTING CONTRACT ABOVE.**
Corrected 2026-09-09; this line said *"it fails closed"* flat, and it is false as stated. **It fails
closed ONLY when NOTHING survives the fence** (`record.py` returns 2 and prints
`nothing recordable for <step> at <ref>`). **On a PARTIAL fence it records a NARROWED subject set at
exit 0** — the skip lines are printed, and nothing else marks the difference.

⚠⚠ **Read that against this brief's own rule that a file you do not name counts as UNREVIEWED and
there is no partial credit.** A silently narrowed set is exactly a file you did not name, arriving
without you deciding to omit it — and because the routing legs block a push until a `rely` record
covers the current blob of every verification-layer file, a narrowed record reports coverage the
round did not have. **Exit 0 is not "all of them". Read the skip lines, and NAME in your report every
path that did not make it.**

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
| an argparse `usage:` banner | your invocation is wrong — `--failing-file` missing on a FAIL, `--failing-file` on a PASS, `--outstanding-file` carrying a non-`ordinary` severity, `--evidence` absent on a delegated PASS, `--run` unset | **YOURS to fix.** Correct the flags and re-run. |
| `nothing recordable for <step> at <ref>` | the subject fence emptied your set. **The ledger was never contacted** | You are READ-ONLY and cannot fix it — see *STAGE THE FILES BEFORE YOU RECORD*. Say so and hand the command back. |
| `UNDECIDED: ledger unavailable or record rejected`, or an outage line printed by the dry-run check | the ledger was reached and refused, or could not be reached | **Report it. Do NOT retry.** The review may have been fine and simply went unrecorded. |

⛔ **If the message matches none of the three, it is a site added since the survey date — not one of
these wearing a different coat.** The binding rule still governs: report what the message actually
said, and do not translate it into the nearest familiar case. ⚠ **Translating an unfamiliar exit 2
into "the ledger" is the exact harm named earlier in this brief** — a reviewer with a real FAIL
reports an outage, and the FAIL never lands.

### Severity, and the cap

⚠ **CLASSIFY EVERY FINDING AS BLOCKING OR ORDINARY, and get this right — the loop's termination depends on it.** **BLOCKING** means the finding lets bad work THROUGH: a gate that reports success it has not earned, a check that can be walked past, a signal that can be forged, an exemption anything can grant itself. **ORDINARY** is everything else — a mislabelled manifest line, a discarded return code at a site that fails closed anyway, a stale docstring, a dead pointer.

⚠ **Put `BLOCKING:<n> ORDINARY:<n>` in your record's `--reason-file`, and lead with what it does NOT mean.** `ship.py`'s cap parses that count straight out of the reason, so the phrasing is load-bearing rather than decorative:
`REVIEWED (not certified clean) — /rely <date> pass <n>, scope <what>. BLOCKING:<n> ORDINARY:<n>. <ids or "reported in the note">. This records WHICH BLOBS WERE EXAMINED, never that they are defect-free.`

⚠ **`/rely` is capped at TWO passes when `BLOCKING:0`** (Tim, 2026-08-10: *"any non bedrock failure should cap at a certain iteration… A nitpicker will always find a knit to pick."*). Four unbounded passes on this layer found 10 → 4 → 6 → 9 and never converged, because each pass reviews code changed in response to the last. **Do not inflate a finding to BLOCKING to keep the loop alive, and do not deflate one to end it.** If you are unsure whether something lets bad work through, say so explicitly in the note and call it BLOCKING — the caller can then judge with the evidence in front of them.

⚠ **If you found a fail-open that is still UNFIXED when you finish, say so in the reason and name the ledger ids.** A future reader must be able to tell "examined, and here is what is wrong with it" from "examined, nothing found" without opening the note.
