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

## CALLER PRE-FLIGHT

**1. SCOPE IT** — a directory, a file list, or a named interface. Do not run it at `full`.

**2. TELL IT WHAT A DOWNSTREAM USER WOULD WANT FROM THIS SCOPE.** *"Someone wants to instantiate this on their own carrier."* / *"Someone wants to rely on this gate to catch X."* / *"Someone wants to cite this theorem for Y."* Without a use, the agent has nothing to attempt and degenerates into a reviewer.

**3. Give it the scratchpad path and confirm `lake` works** — it will be elaborating a lot.

## HARD CONSTRAINTS

**READ-ONLY on the working tree.** Do NOT modify, create, or delete any repo file, with exactly two exceptions: the findings note under `.claude-local/notes/`, and the signal file described at the end.

⚠ **This section used to say "No signal file — this is not a gate and must not block a push." That became FALSE and stayed false** (corrected 2026-08-10). `batch.py`'s routing was added later and DOES block a push until `rely_cleared.txt` records the current hash of every verification-layer file — because a checker change is invisible to `git diff` (`.claude-local/` is gitignored), so the hash signal is the only way the pipeline can see it. The result was the one gate that did not produce the metadata the hook consumes, leaving **the caller to write it about its own work** — exactly the self-certification this routing exists to prevent. **You now write it.** See "Signal file" at the end.

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

## Signal file — `.claude-local/rely_cleared.txt`

**Write it whether you found things or not.** It is NOT a pass certificate; it records **which
versions of the verification layer were actually examined**, which is the only question the routing
asks. Withholding it does not make the layer safer — it just leaves the caller to write it about its
own work.

Format, matching what `batch.py` reads:
- **line 1** = the record, and it must NOT read as a clearance. It **must carry a severity split**:
  `REVIEWED (not certified clean) — /rely <date>, scope <what>. BLOCKING:<n> ORDINARY:<n>. <ids or "reported in the note">. This records WHICH HASHES WERE EXAMINED, never that they are defect-free.`

⚠ **CLASSIFY EVERY FINDING AS BLOCKING OR ORDINARY, and get this right — the loop's termination depends on it.** **BLOCKING** means the finding lets bad work THROUGH: a gate that reports success it has not earned, a check that can be walked past, a signal that can be forged, an exemption anything can grant itself. **ORDINARY** is everything else — a mislabelled manifest line, a discarded return code at a site that fails closed anyway, a stale docstring, a dead pointer.

⚠ **`/rely` is capped at TWO passes when `BLOCKING:0`** (Tim, 2026-08-10: *"any non bedrock failure should cap at a certain iteration… A nitpicker will always find a knit to pick."*). Four unbounded passes on this layer found 10 → 4 → 6 → 9 and never converged, because each pass reviews code changed in response to the last. **Do not inflate a finding to BLOCKING to keep the loop alive, and do not deflate one to end it.** If you are unsure whether something lets bad work through, say so explicitly in the note and call it BLOCKING — the caller can then judge with the evidence in front of them.
- **line 2+** = `<first-12-hex-of-sha256>  <filename>`, two spaces, **one per file in `batch.py`'s
  `CHECKERS` list**. Basename only, not a path. **Do not write the set down here** — it grows,
  and the enumeration that used to sit on this line went stale as soon as a checker was added.
  `batch.py` is authoritative and computes it:

  ```
  python -c "import sys;sys.path.insert(0,'tools/verify');import batch;[print(h,' ',c) for c,h in sorted(batch.checker_hashes().items())]"
  ```

  ⚠ **Both halves of that command were wrong until 2026-08-15, and the editorial gate proved
  it by RUNNING it:** the path said `.claude-local`, so it exited **2** and emitted zero hashes
  — while `batch.py prepush` still BLOCKED on the signal it was meant to produce. **The gate
  was unsatisfiable from its own documentation.** It failed closed, which is the right
  direction, but a reviewer following this file could not have cleared the push it blocked.

⚠ **Hash the FILE ON DISK.** Never a git value. Write BOM-free:
`[System.IO.File]::WriteAllText($p, $s, (New-Object System.Text.ASCIIEncoding))`.

⚠ **If you found a fail-open that is still UNFIXED when you finish, say so in line 1 and name the
ledger ids.** A future reader must be able to tell "examined, and here is what is wrong with it"
from "examined, nothing found" by reading one line.
