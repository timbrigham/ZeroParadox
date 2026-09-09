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

## THE STATES MUST NOT COLLAPSE — AND THIS FILE NO LONGER TELLS YOU WHAT THEY MEAN

⭐⭐ **DO NOT SUPPLY A MEANING FOR ANY OF THESE TOKENS YOURSELF.** `exit_code`, `row_status`,
`decision` and `error_type` each have a served definition — every value with its meaning, rendered
from the constants the servers import. **The rule you act on holds whatever those values turn out to
be: KEEP THE STATES APART.** Never fold an undetermined result into a pass or a fail, never fold a
crash into either, and for every state you report use the token that the thing you actually RAN
emitted, quoted. If a meaning is not visible in what you ran, report that you could not see it —
never reconstruct one from memory or from this file.

*(Provenance, for whoever audits this brief rather than executes it: `docs://gitrobot/vocabulary`.
Fetching it is not a step of this brief; the rule above is.)*

⛔ **DO NOT RESTATE THOSE DEFINITIONS HERE, IN YOUR REPORT, OR IN ANY OTHER BRIEF.** The resource
says why, and it is this file's own history in one line: *"If a document restates any of this, the
document is the copy that will be wrong."*

⚠ **WHAT USED TO STAND IN THIS SECTION, AND WHY IT IS GONE.** Twenty-seven exit-code assertions, a
four-state table, and a NO-STEP / WRONG-STEP table keyed on a check that does not exist. **Five
BEDROCK findings came out of that material in a single day; zero came out of the rest of this file.**
The last of them inverted a precondition — a rule about the STEP-NAME argument written up as a rule
about the SUBJECT argument — inside the same table where the previous round had already fixed the
identical mistake. Every assertion was true when written. **Correct was never the property that
mattered; not-being-a-copy is.**

⚠ **A retry note, measured 2026-09-08:** immediately after a server restart a call can come back
*"Connection closed"* against a surface that is plainly still being served. That is the transport,
not the surface, and one retry cleared it on both servers. **A named refusal is a fact about what is
served; "Connection closed" is a fact about the connection.** Do not report the second as the first.

### What this file still asserts, because it is about YOUR CONDUCT and not about a tool

⛔ **THE EXIT CHANNEL CARRIES ANSWERABILITY; THE LEDGER CARRIES THE VERDICT.** A panel that ran
perfectly and split 2-1 has **answered** — it simply did not answer with one voice, and spelling that
as *"could not ask"* throws away the fact that the work was done. Put the contest where something
reads it. **The exit channel alone cannot be that place: an integer names no property and no subset,
so it cannot say WHICH line the panel split over.**

⛔ **A CONTESTED CONTROL IS NOT PERMITTED TO BE QUIET ABOUT IT.** Fail CLOSED, and carry the
distinction somewhere that survives the exit code: **a line on stdout that only the contested path
can emit**, naming the PROPERTY rather than the outcome. An exit code is over-determined — a crash,
an unrelated failure and a real violation are not distinguishable by it.

⚠ **A CRASH IS NOT A STATUS.** An uncaught traceback is indistinguishable from an honest violation.
Measured 2026-09: a checker returned a failure code on a `UnicodeEncodeError` where that code meant
something specific, **and every caller read the crash as an ordinary failure.** Your control must
make a crash distinguishable — catch it, or emit a line only the real path can produce.

⛔⛔ **THE COLLAPSE THIS WHOLE COMMAND EXISTS TO PREVENT** (`DC-45`, `CLAUDE.md` `R-ZERONULL`):
*"nothing wrong"* and *"nothing ran"* are different answers, and a consumer branching on the value
cannot tell them apart. Measured in this corpus: `check_ssot` returned `True, "no ssot.json in tree"`
for months — **the more complete the coverage looked, the less had actually been read.** The mirror
error is as bad in the other direction: a recording failure read as a finding sends someone to fix a
corpus that is fine.

### Whether you can record a verdict at all — RUN IT, do not read it

⛔ **THERE IS NO `control` STEP, SO THIS GATE CANNOT RECORD ITS OWN VERDICT, AND YOU MUST NOT TRY.**

**Your SUBJECT is a separate question and this file does not answer it.** It once carried a table
predicting the answer; the table was wrong, in the fail-open direction, and that is the defect that
retired it. **Ask the ledger under `--dry-run` and believe what it says.** The registry tells you
what is REGISTERED; only the ledger tells you what it would ACCEPT.

⛔ **DO NOT REACH FOR A NEIGHBOURING STEP TO MAKE THE COMMAND RUN.** Filing a contest about one
property under a step that asserts a different one is a false record every downstream reader will
believe, and **nothing refuses it.** If the honest step does not exist, the honest answer is that it
does not exist.

⚠ **AND WHEN YOU REPORT A REFUSAL, GIVE IT IN THE LEDGER'S WORDS AND NEVER AS A COMMAND LINE.**
`tools/verify/check_briefs.py`'s `steps` leg BLOCKS on the flag form wherever it appears in a brief —
it scans the whole file, so it cannot tell an instruction from a counter-example. Writing the refused
invocation out in full would make this file fail the very checker that guards it.
`.claude/commands/experiment-review.md` quotes its own refusal in the ledger's words, for this
reason. **Verified by execution 2026-09-08**, and it is the one tool-behaviour claim kept here on
purpose: deleting it invites the next author to trip the checker it warns about.

⚠ **REGISTERING A STEP IS TIM'S DECISION, NOT AN AGENT'S.** It is free to write and expensive to
live with — **the blocker is never the token, it is everything downstream that has to be taught to
read it.** Report the need; do not satisfy it.

⭐ **AND NARROWING IS WHAT KEEPS A NARROW DISPUTE NARROW.** A 2-1 split over forty files is contested
about the one line they disagree on and perfectly decided about the other thirty-nine — so name the
contested subset rather than indicting the scope.

## THE DELIVERY CONTRACT — six runs minimum, EIGHT for a panel, and the transcript is half the deliverable

**Ship BOTH:**

**(1) THE CONTROL ITSELF**, committed in your worktree. Not pasted into a report — committed, so it survives your context.

**(2) THE MUTATED FORMS THAT PROVE EACH STATE**, and **at least TWO genuinely different variations per state**. ⚠ **Which states apply depends on the control.** A single check owes PASS, FAIL and ABSENT — six mutations minimum. **A control that runs a PANEL owes the `undecided` state as well** — eight minimum — and must demonstrate a genuine split, not a simulated one. Two variations because one mutation proves the control noticed *that edit*; two proves it is watching the *property*. ⚠ **Make them different in KIND, not in spelling.** Deleting a call and renaming the same call are one variation. Deleting a call and making it return a plausible wrong value are two.

For each of them — **six, or eight if your control runs a panel** — give the caller what they need
to re-run it themselves:

```
STATE: <absent | pass | fail | undecided>   VARIATION: <what was changed, and why it is a different KIND>
COMMAND:  <the exact command, runnable as written>
EXIT:     <the code>
OUTPUT:   <the line(s) that make this exit attributable to the property, quoted verbatim>
```

⚠⚠ **FOUR TOKENS, AND THEY DO NOT MAP ONE-TO-ONE ONTO EXITS.** Do not read a mapping off this file
and do not reconstruct one: record the exit you OBSERVED beside the output line that produced it, and
leave the mapping to the reader. **Whatever that mapping turns out to be, never rest a contested row
on its `EXIT:` field — quote the contested-only `OUTPUT:` line as the evidence, every time.** And
name the record you emitted **or the step whose absence stopped you emitting one.** The output line
is the half you always owe; the record is the half you owe when the subject has a step to carry it,
and *"there was none"* is a reportable answer rather than a missing deliverable.

⚠ **THIS TEMPLATE HAS BEEN WRONG TWICE, IN THE SAME DIRECTION.** With three tokens, an agent holding
a genuine 2-1 split had to spell it *"I could not look."* With four tokens mapped to a fourth exit,
a downstream reporter scored it *skipped* — the same sentence by a longer route. **The remedy being
the defect twice over**, which `.claude/commands/copy-editor.md` names as the mark of a bedrock
finding. That is the reason the mapping now lives in one served place and not in this file.

⭐ `undecided` is the ledger's word for the contested state, not a coincidence and not a synonym. Use
the ledger's token wherever you name the state so the two cannot drift — **and note that the word is
available to you in the run table even when the record is not.** Naming the state is free; recording
it is the part that has a precondition.

⚠ **THE OUTPUT LINE MUST NAME THE PROPERTY, NOT JUST THE OUTCOME.** Quote the line that only the code under test can emit.

**(3) THE REAL-DATA CROSS-REFERENCE.** For each constructed state, say what real input it corresponds to and how you know the shape matches. *"`ssot.json` moved aside"* is real. *"a stubbed function returning None"* may not be — if nothing can produce that input in service, the control has never been tested against anything.

⚠ **State any variation you could NOT construct**, and why. That is a coverage gap in the control, and it is exactly what the next reader needs.

## Before you finish

- **Did any two of your runs — six, or eight for a panel — produce byte-identical output?** If so those two prove one thing, not two — and if a mutation's output matches the unmutated baseline, **that case proves nothing at all.** Say so rather than counting it.
- **What instance of this shape can your own construction never produce?** Build it if you can; name it if you cannot.
- **Name your FIRST UNJUSTIFIED STEP** — the first inference in your own reasoning you took without warrant. The answer is never "none".

## Report back

The question as you understood it · the control's path in your worktree · the run table (six, or eight for a panel) · the real-data cross-reference · anything you could not construct · your first unjustified step. **State plainly which exits the control has been observed producing, and which apply to it at all.** If it has not, the answer is "not yet", and that is a legitimate result.

⚠ **AND IF YOUR CONTROL HAS A CONTESTED STATE, SAY WHAT THE LEDGER ACTUALLY ANSWERED** — the record
id you emitted, or the refusal it printed, quoted. **Report only what you ran.** Do not report a
refusal you never triggered, do not report a record you did not land, and do not report a refusal as
an outage: the exit code collapses those two and the OUTPUT does not — a refusal names the rule and
an outage names the transport. **Quote the line, not the code.**
