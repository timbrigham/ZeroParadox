**ISOLATION REQUIRED: Do not run this inline. Use the Agent tool to spawn a fresh instance with no conversation context.**

Read `$ARGUMENTS` for the question and the subject, then spawn an Agent using the Agent tool with `subagent_type` omitted (general-purpose). Pass the prompt below verbatim, substituting `ARGUMENTS_VALUE` for the actual value of `$ARGUMENTS`. The agent must have no knowledge of the current session.

---

## WHAT THIS COMMAND IS FOR, AND WHY IT IS NOT "WRITE ME A TEST"

**The agent is given a QUESTION. The only thing that answers it is a control that has been seen to fail. So the artifact IS the answer** — not a report about one.

⚠⚠ **WHY IT IS A SEPARATE AGENT, AND IT IS NOT A COURTESY.** `DC-26`, measured six-for-six across four rounds: **the fixer writes the fix's only control, so the control is built from the same materials as the fix and there is a whole family of instances its construction cannot produce.** The control passes, the gate reports clean, and the next reader finds the neighbouring instance in minutes.

⚠ **Measured again 2026-09-05, three instances in one session**, including a control whose two new cases could not distinguish the property being present from the property being **deleted outright** — five states through the harness returned byte-identical output. The author had run a different test, watched it pass, and recorded the control as verified.

⛔ **AND THE PART THAT MAKES THIS A COMMAND RATHER THAN A HABIT:** the same session's independent agent *did* construct the missing state, ran it, reported the numbers — and the harness died with its context. **It was rebuilt by hand an hour later.** The construction is the valuable object and a report throws it away.

---

## CALLER PRE-FLIGHT — you supply four things, and a missing one makes the answer meaningless

**1. THE QUESTION, in one line**, phrased so only a running artifact can answer it.
Good: *"Can `enforce_prepush_verdict` still refuse when a non-routing leg fails and someone has annihilated its recorded count?"*
Bad: *"Write tests for the verdict registry."* That is a chore, and a chore comes back as a chore.

**2. THE SUBJECT** — the exact file, function or property under control, and what it CLAIMS. Hand over the code, not a description of it.

**3. THE STATES, EXPRESSED FOR THIS SUBJECT.** You know the domain; the agent does not. Say what ABSENT, PASS and FAIL each mean here — and, if the control runs a PANEL, what a genuine SPLIT means — *"absent = `ssot.json` is not in the tree"*, *"fail = one leg reports a real violation"*.

**4. THE SHAPE OF REAL DATA.** Point at real inputs — an actual `ssot.json`, an actual failing log, an actual range. ⚠ **A control that only goes red in a state the system can never occupy is vacuous in the mirror direction**, and that is the failure mode this delegation introduces if nobody guards it.

⚠ **`R-BRIEF`:** carry any rule that must not be violated into the prompt VERBATIM. A spawned agent receives a possibly stale `CLAUDE.md` snapshot — measured 2026-08-27, an agent spawned after a committed edit got the pre-edit text and said so. Memory bodies never arrive at all.

---

Spawn the Agent with this prompt (substitute ARGUMENTS_VALUE for the actual value of $ARGUMENTS):

---

## HARD CONSTRAINTS — read before doing anything

- **READ-ONLY on the shared working tree.** Build everything in `worktree(action='add')` or your scratchpad. **Never mutate the caller's checkout** — it may hold uncommitted work, and a review agent once hard-reset three times, destroyed an uncommitted edit, then correctly verified the tree was clean, which *was* the destruction.
- **NEVER `reset --hard`, `checkout -- .`, `clean`, or `stash`.**
- **NO SCRATCH FILES IN THE REPO.** Scratchpad or worktree only.
- **Direct `git` and `gh` are BLOCKED.** A `PreToolUse` hook matches the whole command string — bare, `cd`-chained, `&&`-chained, `-C`, absolute path, shelled out of Python — and FAILS CLOSED. Use `mcp__gitRobot__*`.
- ⚠ **Never pipe anything that runs a `tools/verify` script through `head`, `tail`, `grep`, `Select-Object -First/-Last` or any early-exiting consumer.** SIGPIPE severs the exit status and a blocked gate reads as green. **Redirect to a file and read the file.** A hook enforces this.
- **This is Windows.** PowerShell, not Bash-with-Unix-commands. Glob, never `find`. Never prepend `cd`. External processes get `timeout: 300000`.
- **Never describe a source you have not opened.**

---

## YOUR ANSWER IS A CONTROL THAT HAS BEEN SEEN TO FAIL

A control nobody has watched go red is a **hypothesis**. You are not finished when the control is written; you are finished when it has been observed producing each outcome below that APPLIES TO IT, in states that could really occur.

**If you cannot construct a state where it goes red — that is the finding.** Say so plainly, name what you tried, and stop. **A non-answer reported as a non-answer is worth more than a control nobody has seen fail**, because the second one enters service and the first one does not.

## THE FOUR STATES, AND THEY MUST NOT COLLAPSE — THREE ARE EXITS, THE FOURTH IS A RECORD

The `0`/`2` split is the house convention and it is in force, stated in `tools/verify/check_paths.py` at the guard above `if not t:` — *"exit 2 says the question could not be asked, exit 0 with zero hits says it was asked and answered. Collapsing those two is what a fail-open IS."*

⚠⚠ **THAT CITATION COVERS TWO ROWS, AND THIS BLOCK SPENT IT ON FOUR.** Until 2026-09-08 the table gave *answer contested* **exit 3** under the preface *"this is the house convention and it is already in force"*, and neither half held. The cited comment names `0` and `2` and no third code. And **exit 3 is already taken, three incompatible ways, in the one namespace this table governs — a checker's own process exit.** Measured by importing the consumers and running their scoring predicates rather than reading them:

    check_paths    EXIT_SKIPPED = 3, "the scope could not be determined"
    ci_report      rc == 3 renders `**skipped**` and does NOT increment `failed`
    check_briefs   classify_record_failure(2, reachable) -> 3, the ledger REACHED and REFUSED,
                   returned as the checker's own exit and blocked on by `hooks.py`
    batch.py       special-cases `rc == 2` only, so 3 lands in the generic non-zero bucket

**So a control exiting 3 for a contested panel is scored by the CI reporter as *skipped* — exit 3 collapsing into exit 2, "I could not look".** That is this file's own cardinal rule inverted by the form the rule is printed on, one turn further round than the last time this file recorded that shape.

| state | exit | the sentence it makes | ledger |
|---|---|---|---|
| **PASS** | **0** | "I looked, and it is fine." | `PASS` record |
| **FAIL** | **1** | "I looked, and here is what is wrong." | `FAIL` record, `failing` naming the indicted subset |
| **ABSENT** | **2** — input absent, unreadable, dependency unreachable | "I could not look." **Never a finding about the subject.** | **NO RECORD AT ALL** + a typed `error_type` |
| **CONTESTED** | **1**, and it must SAY SO | "I looked, and we do not agree." | `UNDECIDED` record, `failing` narrowing it — **only if the subject already has a REGISTERED step; check before you promise one** |

⭐ **THE FOURTH STATE IS REAL; WHAT CARRIES IT IS THE VERDICT, NOT THE EXIT.** A panel that ran perfectly and split 2-1 has **answered** — it simply did not answer with one voice, and spelling that as *"could not ask"* throws away the fact that the work was done. The distinction was supplied by the verdictLedger session on 2026-09-05: *"UNDECIDED is a FOURTH state your three exits cannot express."* **That was right about the state, and this file drew the wrong conclusion from it.** A fourth integer does not express it either, because **nothing branches on one.** `R-ZERONULL` asks whether the extra branch returns a value a CONSUMER acts on — and in the ledger it does: `record.py --verdict undecided` exists, `schema.VERDICTS` admits it, `can_push` blocks on it, and `stale_or_missing` counts it among the steps owing a re-run. **The exit channel carries answerability; the ledger carries the verdict. Put the contest where something reads it.** ⚠⚠ **AND THAT IS TRUE OF THE LEDGER WITHOUT BEING TRUE OF EVERY GATE — THE NEXT-BUT-ONE BLOCK IS THE FENCE, AND IT IS NOT OPTIONAL READING.** Those four consumers all exist and all branch; whether *your* control can reach them depends on whether its subject has a registered step, and for this gate's own subject it does not.

⛔ **SO A CONTESTED CONTROL EXITS 1, AND IS NOT PERMITTED TO BE QUIET ABOUT IT.** Exit 1 is fail-CLOSED, which is the safe direction and the only one of the four integers that is: `0` would be a fail-open, `2` is the forbidden collapse, `3` is read three ways by three consumers on the push path. **Exit 1 ALONE under-reports** — it reads as a plain violation — so the distinction has to be carried somewhere else or it is lost exactly where it was lost before. **The carrier that is ALWAYS available is a line on stdout that only the contested path can emit** (the delivery contract below already requires one, and requires it to name the PROPERTY rather than the outcome). **The `UNDECIDED` record narrowed by `failing` is the stronger carrier and it is CONDITIONAL** — read the next block before you promise one.

⛔⛔ **AND THE RECORD IS NOT ALWAYS AVAILABLE. CHECK BEFORE YOU PROMISE ONE — MEASURED 2026-09-08.**
A verdict can only be recorded under a step that is REGISTERED in `tools/verify/required.v2.json`,
which today holds 29 of them. Under a registered step the fourth verdict lands cleanly; under
anything else the server refuses it outright, and `record.py` returns **exit 2** — *"UNDECIDED:
ledger unavailable or record rejected"* — which reads as an OUTAGE rather than as a design decision.
Both halves were run under `--dry-run`. Naming a REGISTERED step returned exit 0, *"the ledger WOULD
ACCEPT this record."* Naming this gate returned exit 1 and the server's own rule:

    V8: step 'control' is not registered in required.v2.json — an unregistered check
        cannot record, so it cannot silently not count

⚠ **THAT REFUSAL IS QUOTED IN THE LEDGER'S WORDS AND NOT AS A COMMAND LINE, DELIBERATELY.**
`check_briefs.py`'s `steps` leg BLOCKS on the flag form wherever it appears in a brief — it scans the
whole file, so it cannot tell an instruction from a counter-example. Writing the refused invocation
out in full would make this file fail the very checker that guards it. `experiment-review.md` quotes
its own refusal the same way, for the same reason.

⛔ **THERE IS NO `control` STEP, SO THIS GATE CANNOT RECORD ITS OWN VERDICT, AND YOU MUST NOT TRY.**
Neither can a control built over an unregistered subject — `hooks` is refused by name the same way,
and the worked question at the top of this file (`enforce_prepush_verdict`) lives in exactly that
class. **Do not reach for a neighbouring step to make the command run**: `batch.py` is the declared
module of `decls` and `pdf_coupling`, so a control over it *would* be accepted under either, and
filing a contest about one property under a step that asserts a different one is a false record that
every downstream reader will believe.

⭐ **SO STATE THE CONTEST IN YOUR REPORT AND HAND IT UP.** When no step exists, the contested-only
stdout line plus your report ARE the carrier, and saying that plainly is the honest result. This is
not a gap to paper over: `experiment-review.md` reached the same wall on 2026-08-24 and settled it
the same way — *"a record that cannot land is worse than none, because its exit 2 reads as an outage
rather than as a design decision"* — and it also names the ORDER, which is the part that binds here:
**registering the step comes FIRST, and the recording block comes with it.**

⚠ **REGISTERING ONE IS TIM'S DECISION, NOT AN AGENT'S, AND THE COST IS WHY.** `required.v2.json`
declares `"default": "REQUIRED_FOR_ALL_ACTIONS"` — *"A registered type binds on EVERY action unless
an entry says otherwise, and saying otherwise costs a stated `reason`."* A bare new entry therefore
blocks every commit, push and tag until a record exists for it. **Inclusion is free to write and
expensive to live with**, which is the same shape as minting a fourth exit integer below: the
blocker is never the token, it is everything downstream that has to be taught to read it.

⚠ **MINTING A FOURTH CHECKER EXIT IS NOT AN AGENT'S DECISION, AND IT IS THE DURABLE FIX.** A sweep of `sys.exit(N)` and `EXIT_* = N` under `tools/` on 2026-09-08 located no code above 3 — evidence about that probe, not a guarantee an integer is free. **The blocker is not the integer, it is that `ci_report`, `batch` and `hooks` would each have to be taught to read it.** When one of them is, the state moves back into the exit channel and this row changes with it; until then it lives in the verdict, and this is an interim guard rather than the design. Tim decides which.

⚠ **`UNDECIDED` BLOCKS ADMISSION, RANKS BETWEEN FAIL AND PASS, AND HAS NEVER ONCE BEEN RECORDED.** ⭐ **THE ZERO IS THE CLAIM; THE DENOMINATOR IS NOT** — it was 2,170 when this line was written, 2,267 on 2026-09-06, and 2,503 on 2026-09-08. **The stream grows and the zero has not moved.** Re-derive it with `find(verdict='undecided')` rather than trusting any figure here; a frozen denominator beside a live numerator is `DC-6` and this line carried one for two days (AR8-4). It is storable today — `schema.VERDICTS` is `{FAIL, PASS, UNDECIDED}`, the validator admits it, the resolver reads it, `can_push` blocks on it, and `pytest -k undecided` passes 15. **Its downstream has never executed on production data**, so the first real one is a first on the data, not a first through the code. Say so if you emit one — **and say so just as plainly if you could not, naming the step that was refused.** A gate that could not record is a fact the next reader needs; it is not the same fact as a gate that found nothing.

⭐ **AND `failing` IS WHAT KEEPS A NARROW DISPUTE NARROW.** It is admitted on `FAIL` and `UNDECIDED` and refused on `PASS`. **A 2-1 split over forty files is UNDECIDED about the one line they disagree on and perfectly decided about the other thirty-nine** — so name the contested subset rather than indicting the scope. Rows carry `narrowed_from` and the push path prints `⚠ NARROWED INDICTMENT`.

⛔ **THE VERDICT AND THE ANSWERABILITY ARE DIFFERENT PLANES.** `verdict` answers the question; `error_type` says whether a question was answerable at all. They are orthogonal by construction, which is why exit 2 produces **no record** rather than a record saying "unknown" — you cannot record that the recorder was unreachable. From `verdictLedger/core/errors.py`: *"If 'the ledger could not take it' and 'the ledger rejected it' look alike, a caller under pressure retries its way past a validation rule."*

⛔⛔ **COLLAPSING 2 INTO 0 IS THE DEFECT THIS WHOLE COMMAND EXISTS TO PREVENT** (`DC-45`, `CLAUDE.md` `R-ZERONULL`). *"Nothing wrong"* and *"nothing ran"* are different answers and a consumer branching on the value cannot tell them apart. Measured in this corpus: `check_ssot` returned `True, "no ssot.json in tree"` for months — **the more complete the coverage looked, the less had actually been read.**

⚠ **AND COLLAPSING 2 INTO 1 IS ALSO WRONG**, in the expensive direction: a recording failure read as a finding sends someone to fix a corpus that is fine. `record.py` says it outright — *"Exit 2 is NOT exit 1."*

⚠ **A CRASH IS NOT A STATUS.** An uncaught traceback exits 1 and is indistinguishable from an honest violation. Measured: `gate_round.py` returned 1 on a `UnicodeEncodeError` where 2 meant "past the bedrock cap", **and every caller read the crash as an ordinary failure.** Your control must make a crash distinguishable — catch it and exit 2, or emit a line only the real path can produce.

## THE DELIVERY CONTRACT — six runs minimum, EIGHT for a panel, and the transcript is half the deliverable

**Ship BOTH:**

**(1) THE CONTROL ITSELF**, committed in your worktree. Not pasted into a report — committed, so it survives your context.

**(2) THE MUTATED FORMS THAT PROVE EACH STATE**, and **at least TWO genuinely different variations per state**. ⚠ **Which states apply depends on the control.** A single check owes PASS, FAIL and ABSENT — six mutations minimum. **A control that runs a PANEL owes CONTESTED as well** — eight minimum — and must demonstrate a genuine split, not a simulated one. ⚠ CONTESTED is not proved by an exit code, because it shares one with FAIL: prove it with the contested-only line, and with the `UNDECIDED` record where the subject has a registered step to carry one. Two variations because one mutation proves the control noticed *that edit*; two proves it is watching the *property*. ⚠ **Make them different in KIND, not in spelling.** Deleting a call and renaming the same call are one variation. Deleting a call and making it return a plausible wrong value are two.

For each of them — **six, or eight if your control runs a panel** — give the caller what they need
to re-run it themselves:

```
STATE: <absent | pass | fail | undecided>   VARIATION: <what was changed, and why it is a different KIND>
COMMAND:  <the exact command, runnable as written>
EXIT:     <the code>
OUTPUT:   <the line(s) that make this exit attributable to the property, quoted verbatim>
```

⚠⚠ **FOUR TOKENS AND THREE EXITS — THE COUNTS DIFFER, AND THAT IS THE POINT.** `absent` is exit 2
(could not ask), `pass` is 0, `fail` is 1, and **`undecided` is asked-ran-to-completion-answer-
contested, which ALSO exits 1.** So on an `undecided` row the `EXIT:` field does not discriminate
and the `OUTPUT:` field is the whole evidence — quote the contested-only line, and name the
`UNDECIDED` record you emitted **or the step whose absence stopped you emitting one.** ⚠ **THE
OUTPUT LINE IS THE HALF YOU ALWAYS OWE**; the record is the half you owe when the subject has a
registered step, and "there was none" is a reportable answer rather than a missing deliverable.

⚠ **THIS TEMPLATE CARRIED THREE TOKENS UNTIL 2026-09-08 AND THEN FOUR MAPPED TO A FOURTH EXIT, AND
BOTH WERE WRONG IN THE SAME DIRECTION.** With three, an agent holding a genuine 2-1 split had to
spell it `absent`, literally *"I could not look."* With `undecided` mapped to exit 3, the CI reporter
scored it `**skipped**` — the same sentence, arrived at by a longer route. **The remedy being the
defect twice over**, which `copy-editor.md` names as the mark of a bedrock finding.

⭐ `undecided` is the ledger's word for the same state, not a coincidence and not a synonym: a
contested panel records `UNDECIDED` with `failing` narrowing it to the contested subset, wherever a
registered step exists to carry it. **One missing word, in the prose layer and the recording
layer.** Use the ledger's token here so the two cannot drift — **and note that the word is available
to you in the run table even when the record is not.** Naming the state is free; recording it is the
part that has a precondition.

⚠ **THE OUTPUT LINE MUST NAME THE PROPERTY, NOT JUST THE OUTCOME.** An exit code is over-determined — a crash, an unrelated failure and a real violation all exit non-zero. Quote the line that only the code under test can emit.

**(3) THE REAL-DATA CROSS-REFERENCE.** For each constructed state, say what real input it corresponds to and how you know the shape matches. *"`ssot.json` moved aside"* is real. *"a stubbed function returning None"* may not be — if nothing can produce that input in service, the control has never been tested against anything.

⚠ **State any variation you could NOT construct**, and why. That is a coverage gap in the control, and it is exactly what the next reader needs.

## Before you finish

- **Did any two of your runs — six, or eight for a panel — produce byte-identical output?** If so those two prove one thing, not two — and if a mutation's output matches the unmutated baseline, **that case proves nothing at all.** Say so rather than counting it.
- **What instance of this shape can your own construction never produce?** Build it if you can; name it if you cannot.
- **Name your FIRST UNJUSTIFIED STEP** — the first inference in your own reasoning you took without warrant. The answer is never "none".

## Report back

The question as you understood it · the control's path in your worktree · the run table (six, or eight for a panel) · the real-data cross-reference · anything you could not construct · your first unjustified step. **State plainly which exits the control has been observed producing, and which apply to it at all.** If it has not, the answer is "not yet", and that is a legitimate result.

⚠ **AND IF YOUR CONTROL HAS A CONTESTED STATE, SAY WHICH WAY THE RECORD WENT** — the record id you emitted, or the step name the ledger refused and the refusal it printed. **Do not report a record you did not land, and do not report the refusal as an outage**: `record.py` returns exit 2 for an unregistered step and for a dead server alike, and this file's own rule is that those are different answers.
