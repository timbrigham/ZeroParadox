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

## HARD CONSTRAINTS

**READ-ONLY on the working tree.** Do NOT modify, create, or delete any repo file, with exactly ONE exception: the findings note under `.claude-local/notes/`. ⚠ **There is no signal file any more** — your verdict goes to the ledger, and the recording section at the end is the only place you write one.

⚠ **You still produce the metadata the pipeline consumes — it is just a RECORD now.** `batch.py`'s routing legs block a push until a `rely` record covers the current blob of every verification-layer file, because a checker change is invisible to an ordinary diff of the pushed range. That obligation has not softened; only its container changed. **What has NOT changed is why you write it at all:** before 2026-08-10 this gate produced nothing, so the CALLER wrote the metadata about its own work — the exact self-certification this routing exists to prevent.

**NO SCRATCH FILES IN THE REPO.** Everything you build goes in the session scratchpad, never under `ZeroParadox/`, and is deleted when done. **You will be building a lot — be disciplined about this.**

**Do not cite a private path in anything reader-facing.** `.claude-local/` is gitignored.

⚠ **Tool traps, all measured:** `Select-String -Path "<dir>\**\*.lean"` silently under-matches deep trees — use ripgrep. A Mathlib declaration may be attribute-generated with **no source line at all**, so `#check` is the authority over grep. `python -c` in the Bash tool eats backticks. `| Select-Object -First N` breaks the pipe and reports a wrong exit code. A failed `#synth` has at least five innocent causes — not imported, unresolved universes, a different name, decomposed into parts, attribute-generated — so **re-probe before recording an absence.**

---

Spawn the Agent with this prompt (substitute ARGUMENTS_VALUE for the actual value of $ARGUMENTS):

---
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

⚠ **`/rely` records in two places because it produces two kinds of thing** (the recording contract § 6a-iv):
its **routing check is a hash comparison (tier M)** — which versions of the layer were examined — and
its **findings are judgement (tier A)**. Split at the leg, never at the check.

### 1. There is NO hash file any more

⛔ **DO NOT WRITE `.claude-local/rely_cleared.txt`.** It was RETIRED on 2026-08-24, the last of the
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

**If you found anything BLOCKING, record it. One agent's finding stands alone** (§ 6a-i: *FAIL alone,
PASS by unanimity or signature*):

```
python tools/verify/record.py --step rely --verdict fail --tier A \
    --how agreement --passes 1 --agreed 1 \
    --run gate-rely-<YYYY-MM-DD> \
    --reason-file <path to a file holding: BLOCKING:<n> — the highest-severity fail-open, one line> \
    --files <every file in tools/verify/ you actually examined>
```

**With `BLOCKING:0`, record NOTHING and report to your caller.** You issue no PASS — you never have —
and a lone A-tier PASS is rejected at the server anyway. The caller decides whether the round is a
signature or an agreement.

⚠ **Subjects come from the git INDEX: the files must be STAGED.** `common.ledger_subjects` fences
anything untracked or differing from the index. It fails closed; do not work around it.

⚠⚠ **IF YOU ARE ONE OF SEVERAL CONCURRENT PASSES, EXPECT `V11` AND DO NOT RETRY.** The server
keys a record by `(step, basis, revision)`, so the FIRST failing pass records and later ones are
refused with *"revision 0 already exists for step '<step>' at this basis"*. That is the design
working — it fails CLOSED and loudly, with an attributed append-only record, where the retired
signal files failed silently and let the last writer win. **Do not treat it as an outage and do not
retry.** Instead: read the recorded record's `reason`, and **report to your caller exactly which of
your findings are ABSENT from it.** Two passes converging is corroboration; a finding only you found
is lost unless you say so in your report. `record.py` exposes no `--revision`, so the supersede
chain is not reachable from here — that is a known gap, not something for you to work around.

⚠ **Exit 2 is NOT exit 1** — it means the ledger was unreachable or refused the record, which is a
RECORDING failure, not a finding about the layer.

### Severity, and the cap

⚠ **CLASSIFY EVERY FINDING AS BLOCKING OR ORDINARY, and get this right — the loop's termination depends on it.** **BLOCKING** means the finding lets bad work THROUGH: a gate that reports success it has not earned, a check that can be walked past, a signal that can be forged, an exemption anything can grant itself. **ORDINARY** is everything else — a mislabelled manifest line, a discarded return code at a site that fails closed anyway, a stale docstring, a dead pointer.

⚠ **Put `BLOCKING:<n> ORDINARY:<n>` in your record's `--reason-file`, and lead with what it does NOT mean.** `ship.py`'s cap parses that count straight out of the reason, so the phrasing is load-bearing rather than decorative:
`REVIEWED (not certified clean) — /rely <date> pass <n>, scope <what>. BLOCKING:<n> ORDINARY:<n>. <ids or "reported in the note">. This records WHICH BLOBS WERE EXAMINED, never that they are defect-free.`

⚠ **`/rely` is capped at TWO passes when `BLOCKING:0`** (Tim, 2026-08-10: *"any non bedrock failure should cap at a certain iteration… A nitpicker will always find a knit to pick."*). Four unbounded passes on this layer found 10 → 4 → 6 → 9 and never converged, because each pass reviews code changed in response to the last. **Do not inflate a finding to BLOCKING to keep the loop alive, and do not deflate one to end it.** If you are unsure whether something lets bad work through, say so explicitly in the note and call it BLOCKING — the caller can then judge with the evidence in front of them.

⚠ **If you found a fail-open that is still UNFIXED when you finish, say so in the reason and name the ledger ids.** A future reader must be able to tell "examined, and here is what is wrong with it" from "examined, nothing found" without opening the note.
