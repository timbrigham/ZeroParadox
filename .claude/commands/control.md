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

## THE FOUR STATES, AND THEY MUST NOT COLLAPSE

This is the house convention and it is already in force — stated at `tools/verify/check_paths.py:1501`: *"exit 2 says the question could not be asked, exit 0 with zero hits says it was asked."*

| exit | meaning | the sentence it makes | ledger |
|---|---|---|---|
| **0** | asked, and the property HOLDS | "I looked, and it is fine." | `PASS` record |
| **1** | asked, and the property is VIOLATED | "I looked, and here is what is wrong." | `FAIL` record, `failing` naming the indicted subset |
| **2** | **COULD NOT ASK** — input absent, unreadable, dependency unreachable | "I could not look." **Never a finding about the subject.** | **NO RECORD AT ALL** + a typed `error_type` |
| **3** | **ASKED, RAN TO COMPLETION, ANSWER CONTESTED** | "I looked, and we do not agree." | `UNDECIDED` record, `failing` narrowing it |

⚠⚠ **EXIT 3 IS NOT EXIT 2, AND COLLAPSING THEM IS THE SAME DEFECT ONE LEVEL DOWN.** A panel that ran perfectly and split 2-1 has **answered**; it simply did not answer with one voice. Spelling that as *"could not ask"* throws away the fact that the work was done — and sends someone to fix infrastructure that is fine. This distinction was supplied by the verdictLedger session on 2026-09-05 against an earlier draft of this brief that had only three exits: *"UNDECIDED is a FOURTH state your three exits cannot express... If `/control` ever runs a panel rather than a single check, it needs its own exit, or the panel split will get spelled as could-not-ask."*

⚠ **`UNDECIDED` BLOCKS ADMISSION, RANKS BETWEEN FAIL AND PASS, AND HAS 0 RECORDS OF 2,170.** It is storable today — `schema.VERDICTS` is `{FAIL, PASS, UNDECIDED}`, the validator admits it, the resolver reads it, `can_push` blocks on it, and `pytest -k undecided` passes 15. **Its downstream has never executed on production data**, so the first real one is a first on the data, not a first through the code. Say so if you emit one.

⭐ **AND `failing` IS WHAT KEEPS A NARROW DISPUTE NARROW.** It is admitted on `FAIL` and `UNDECIDED` and refused on `PASS`. **A 2-1 split over forty files is UNDECIDED about the one line they disagree on and perfectly decided about the other thirty-nine** — so name the contested subset rather than indicting the scope. Rows carry `narrowed_from` and the push path prints `⚠ NARROWED INDICTMENT`.

⛔ **THE VERDICT AND THE ANSWERABILITY ARE DIFFERENT PLANES.** `verdict` answers the question; `error_type` says whether a question was answerable at all. They are orthogonal by construction, which is why exit 2 produces **no record** rather than a record saying "unknown" — you cannot record that the recorder was unreachable. From `verdictLedger/core/errors.py`: *"If 'the ledger could not take it' and 'the ledger rejected it' look alike, a caller under pressure retries its way past a validation rule."*

⛔⛔ **COLLAPSING 2 INTO 0 IS THE DEFECT THIS WHOLE COMMAND EXISTS TO PREVENT** (`DC-45`, `CLAUDE.md` `R-ZERONULL`). *"Nothing wrong"* and *"nothing ran"* are different answers and a consumer branching on the value cannot tell them apart. Measured in this corpus: `check_ssot` returned `True, "no ssot.json in tree"` for months — **the more complete the coverage looked, the less had actually been read.**

⚠ **AND COLLAPSING 2 INTO 1 IS ALSO WRONG**, in the expensive direction: a recording failure read as a finding sends someone to fix a corpus that is fine. `record.py` says it outright — *"Exit 2 is NOT exit 1."*

⚠ **A CRASH IS NOT A STATUS.** An uncaught traceback exits 1 and is indistinguishable from an honest violation. Measured: `gate_round.py` returned 1 on a `UnicodeEncodeError` where 2 meant "past the bedrock cap", **and every caller read the crash as an ordinary failure.** Your control must make a crash distinguishable — catch it and exit 2, or emit a line only the real path can produce.

## THE DELIVERY CONTRACT — six runs minimum, and the transcript is half the deliverable

**Ship BOTH:**

**(1) THE CONTROL ITSELF**, committed in your worktree. Not pasted into a report — committed, so it survives your context.

**(2) THE MUTATED FORMS THAT PROVE EACH EXIT**, and **at least TWO genuinely different variations per state**. ⚠ **Which states apply depends on the control.** A single check owes exits 0, 1 and 2 — six mutations minimum. **A control that runs a PANEL owes exit 3 as well** — eight minimum — and must demonstrate a genuine split, not a simulated one. Two variations because one mutation proves the control noticed *that edit*; two proves it is watching the *property*. ⚠ **Make them different in KIND, not in spelling.** Deleting a call and renaming the same call are one variation. Deleting a call and making it return a plausible wrong value are two.

For each of the six, give the caller what they need to re-run it themselves:

```
STATE: <absent | pass | fail | undecided>   VARIATION: <what was changed, and why it is a different KIND>
COMMAND:  <the exact command, runnable as written>
EXIT:     <the code>
OUTPUT:   <the line(s) that make this exit attributable to the property, quoted verbatim>
```

⚠⚠ **FOUR TOKENS, BECAUSE THERE ARE FOUR EXITS.** `absent` is exit 2 (could not ask), `pass` is 0,
`fail` is 1, and **`undecided` is exit 3 — asked, ran to completion, answer contested.** This
template carried three tokens against the four-state table above until 2026-09-08, so an agent with
a genuine 2-1 split had to spell it `absent`, literally *"I could not look."* **That is the exact
collapse this file's own cardinal rule forbids, manufactured by the form the rule is printed on** —
the remedy being the defect, which `copy-editor.md` names as the mark of a bedrock finding.

⭐ `undecided` is the ledger's word for the same state, not a coincidence and not a synonym: a
contested panel records `UNDECIDED` with `failing` narrowing it to the contested subset. **One
missing word, in the prose layer and the recording layer.** Use the ledger's token here so the two
cannot drift.

⚠ **THE OUTPUT LINE MUST NAME THE PROPERTY, NOT JUST THE OUTCOME.** An exit code is over-determined — a crash, an unrelated failure and a real violation all exit non-zero. Quote the line that only the code under test can emit.

**(3) THE REAL-DATA CROSS-REFERENCE.** For each constructed state, say what real input it corresponds to and how you know the shape matches. *"`ssot.json` moved aside"* is real. *"a stubbed function returning None"* may not be — if nothing can produce that input in service, the control has never been tested against anything.

⚠ **State any variation you could NOT construct**, and why. That is a coverage gap in the control, and it is exactly what the next reader needs.

## Before you finish

- **Did any two of your six runs produce byte-identical output?** If so those two prove one thing, not two — and if a mutation's output matches the unmutated baseline, **that case proves nothing at all.** Say so rather than counting it.
- **What instance of this shape can your own construction never produce?** Build it if you can; name it if you cannot.
- **Name your FIRST UNJUSTIFIED STEP** — the first inference in your own reasoning you took without warrant. The answer is never "none".

## Report back

The question as you understood it · the control's path in your worktree · the six-run table · the real-data cross-reference · anything you could not construct · your first unjustified step. **State plainly which exits the control has been observed producing, and which apply to it at all.** If it has not, the answer is "not yet", and that is a legitimate result.
