# When a failure recurs — the list in full, and the escalation ladder

**Body for `CLAUDE.md` § `R-RECUR`.** The trigger and the ordered list are there; every
measurement, worked case and caller-side complement is here.

---

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
