# Maintaining CLAUDE.md: the shape contract, the intake gate, and the remediation program

**What this file is.** The protocol governing edits to `CLAUDE.md` itself: what shape a rule takes,
what an addition costs, where the argument goes, and how the file gets compressed without losing a
rule. `tools/verify/check_claude_md.py` and `tools/verify/hooks.py` both name this path, and the
checker prints it as `body` in the manifest banner (a default run and `--measure`; `--selftest` and
`--help` return before the banner is built) — so this is the file those pointers resolve
to. **`CLAUDE.md` does not yet carry a routing stanza pointing back here**, which means nothing
routes a reader to this protocol from the file it governs. That gap is real and is not closed by
this sentence; opening a stanza costs a removal under §3, so it is Tim's call and batched.

**Why it exists.** `CLAUDE.md` has measured its own failure mode twice over. Seven conventions
leaked while being remembered by people who had read them. And **measured 2026-08-15 at commit
`4363d24`, in a then-2438-line file: line 127 fired reliably all day and line 2135 fired zero
times.** ⚠ Attribute that figure to the dated measurement, never to the current text — the
compression sweep this file governs cut `CLAUDE.md` to under 700 lines, so neither line number
exists any more and grepping for them returns nothing. The conclusion survives the file it was
measured on: **rules do not fail because they are absent, they fail because they are buried.**
Prose added below the firing zone is not a rule, it is a memorial.

**Scope.** `CLAUDE.md` and `tools/process/**` — and this file lives at `tools/process/` precisely so
that its own scope sentence is true of it. Nothing here asserts mathematics, so under R-EXEMPT the
editorial and adversary gates have no claim on either. ⚠ **The two are exempt for the same reason
and covered differently:** R-EXEMPT routes `/rely` over `tools/verify/**` and `tools/process/**` —
*those two directories* — so this file is `/rely`'s, while **`CLAUDE.md` itself is exempt from all
three** and is covered by `check_claude_md.py` alone. Do not read "exempt" as "reviewed elsewhere"
for `CLAUDE.md`; the checker is the only thing looking at it. ⚠ **The carve is a property of the DIRECTORY, not of this document.** A copy of this file
placed anywhere else does not carry the exemption with it, and `.claude/commands/**` is the
directory R-EXEMPT marks explicitly non-exempt.

---

## 1. The shape contract

**`CLAUDE.md` is a ROUTING TABLE. It is not a manual, not a changelog, and not an incident
archive.** One entry per rule, and an entry has exactly four parts:

```
## <ID> <imperative title>
TRIGGER  an ACTION you are about to take. Never a category you must adjudicate.
RULE     what to do instead, in the imperative. No justification.
COST     what breaks if you skip it, in one clause. Measured, undated, no war story.
READ     one exact path, when there is a body. Omitted when there is not.
```

Hard limits, so that "is this entry too long" is never a judgement call:

| property | limit | enforcement |
|---|---|---|
| lines per entry | 12 | WARN |
| TRIGGER present, and phrased as an action | required | BLOCK |
| paths named in the entry resolve on disk | required | BLOCK |
| whole file, net lines added while over budget | 0 | BLOCK |

**Everything that is not TRIGGER / RULE / COST / READ goes to `tools/process/<slug>.md`.** That
includes the argument, the measurement, the incident, the date, the counter-example, the table of
what was tried. Those are worth keeping. They are not worth paying for at every session start and
in every subagent context.

**The four things that must never be written into `CLAUDE.md`, by class:**

1. **Justification.** The reason a rule exists belongs in the body. A reader who is about to violate
   a rule does not need to be convinced, they need to be stopped and given a path.
2. **Prior-state prose.** "This line used to say X, which was wrong." Apply the strip test the file
   already defines: if mathematics or a live rule remains after removing the framing, state it
   positively; if only history remains, delete it. Git holds it.
3. **Enumerations of what an artifact defines.** Counts, field lists, "the N conditions", file
   inventories. Point, name the one or two load-bearing members, stop.
4. **A second statement of a rule that already exists.** A recurrence means the existing trigger is
   wrong. Fix the trigger. A rule stated twice is a rule that fires in neither place, because each
   copy licenses skipping the other.

---

## 2. The intake gate: what to do when a new lesson arrives

**This is the moment of growth, so this is where the control sits.** Run it in order and stop at
the first match. The reflex being interrupted is "write a new section", which feels like progress
and is how the file got here.

**Step 0. Does a rule already cover this?**
`grep -n "^## " CLAUDE.md` first (cheap, and your injected copy is stale if anything landed this
session). Then check `DEFECT_CLASSES.md` and `DEFECTS.md`. If a rule exists and did not fire, this
is a **trigger defect**, not a missing rule. Go to the escalation ladder in `CLAUDE.md`; do not add
anything here.

**Step 1. Is it mechanically decidable?**
Then it is a checker, not a sentence. Write the check, add one table row naming the checker, and
write no prose about it beyond COST. A rule with a checker needs no persuasion in the file, because
it fires whether or not anyone reads.

**Step 2. Is it an argument, a measurement, or an incident?**
Then it is a body. `tools/process/<slug>.md`, and the routing entry gains at most a READ line. Test:
if the sentence would not change what someone about to act does in the next thirty seconds, it is a
body.

**Step 3. Is it prior-state prose?**
Strip test. State the live rule positively, delete the history, let the commit message narrate.

**Step 4. Is it a genuinely new rule, not mechanizable, that must fire at action time?**
Only now do you add an entry, in the four-part form, under the budget in §3, placed by §4.

**Step 5. None of the above?**
It is a note. `.claude-local/notes/`, and per the existing rule, the pointer is the deliverable, not
the note.

---

## 3. The budget: additions are paid for, not appended

**The file has a size cap and a slot count, and both are enforced against the diff, not against
anyone's intention.**

- **Over budget: a diff that adds net lines to `CLAUDE.md` is intended to BLOCK.** A diff that
  removes always passes. This is decidable, so it blocks rather than warns once it is armed.
  ⚠ **It is not armed yet.** The `budget` leg reports PENDING, because the cap is set BY
  MEASUREMENT after the Phase 1 sweep and no cap is set. Until then this is a rule people keep, not
  a rule anything enforces — check the leg table on a live run rather than trusting this bullet.
- **Payment is one of three moves, and the checker computes the receipt from the diff rather than
  trusting a typed claim:**
  1. **Mechanize:** replace an entry with a checker row. Frees the most.
  2. **Move:** relocate the argument to `tools/process/`, leaving TRIGGER / RULE / COST / READ.
  3. **Merge:** fold a recurrence into the entry it is a recurrence of, fixing that entry's trigger.
- **Deleting an entry outright is Tim's call, batched, one line of assent each.** Compressing,
  moving, and mechanizing are not: those preserve the rule and change only where its body lives.

**Set the cap by measurement, and record it in the checker, never in prose.** One place, so it
cannot drift. The right first cap is the current size after the Phase 1 sweep in §7, not a round
number picked now.

---

## 4. Placement: the firing zone is real estate, ordered by trigger frequency

Position is enforcement. Order entries by **how often the trigger fires**, highest first. Not by
topic, not by recency, not by importance-as-felt.

- **Frequency is derived, not asserted.** Give every entry a stable ID (`R-STAGE`, `R-ENC`,
  `R-TRUNC`). Gate briefs, defect rows and commit messages cite the ID. The checker then reports
  citations per ID over a window, which is the only honest measure of whether an entry is load
  bearing.
- **An entry nothing has cited in a long window is a candidate for demotion**, in this order:
  mechanize it, move it to a body, or accept that it is decorative and delete it. The report is a
  **reading list, never an auto-prune**: deciding whether zero citations means dead or means rarely
  and critically triggered is judgement.
- **Never reorder and rewrite in the same pass.** A reorder is verifiable by diffing the section
  title manifest; a rewrite is not. Mixed, neither is.

---

## 5. What may never be routed out

**Route out the argument. Never route out a rule whose violation is silent and irreversible.** For
those, the pointer is the hole: the cost of not opening it is paid before the reader learns there
was something to open.

The test: **if skipping the READ can destroy work, ship a permanent artifact, or produce a green
result that was never earned, the rule stays inline in full.** Current members of that class, by
kind rather than by name, so the criterion survives the next one nobody has classified yet:

- destructive tree operations, and anything that reports success after destroying state
- anything that makes a gate report `pass` for a property it did not check
- anything that mints a permanent public artifact (a DOI, a release, an external message)
- anything that can be walked past silently (truncation and broken pipes, bypass flags, bulk staging)

These entries may still lose their justification to a body. They may not lose their rule.

---

## 6. Defect classes in `CLAUDE.md`, with detectors

One row per class. The detector column is the part that transfers. Prefer a detector whose verb is
**run** over one whose verb is **read**.

| id | class | detector | verb |
|---|---|---|---|
| **CM-1** | Justification inline: an entry carrying its own argument | entry exceeds the line cap, or contains "why this exists", "measured", "what it cost" | run |
| **CM-2** | Prior-state prose | grep the correction idioms ("this line said", "used to read", "previously", "until 2026-", "was FALSE", "corrected") | run, then read each hit |
| **CM-3** | Duplicated enumeration | grep for digit-plus-noun counts and "the N conditions"; every hit is a completeness claim the file cannot check | run |
| **CM-4** | Cross-section contradiction | LLM screen over section pairs sharing a subject; take a flag appearing in at least 2 of 3 runs | screen, human verdict |
| **CM-5** | Dead tail: an entry below the firing zone | citation count per ID over the window, plus position | run |
| **CM-6** | Category trigger: a rule you must first decide applies | grep TRIGGER lines for nouns rather than verbs ("before fresh development", "any change touching") | run |
| **CM-7** | Restatement: one rule in two places | LLM screen for imperative overlap across entries | screen, human verdict |
| **CM-8** | Unenforced rule outside the firing zone | entry has no checker named and no BLOCK, and sits below the zone | run |
| **CM-9** | Stale pointer | resolve every path named in `CLAUDE.md` against the filesystem | run |
| **CM-10** | Rule that outlived its subject | named artifact, directory, or command no longer exists | run |

**The screen legs (CM-4, CM-7) are screens, not verdicts.** They widen the candidate set; a human
adjudicates. Ignore self-reported confidence. Keep a small recorded slice of entries the screen
should get **wrong** (a legitimate pair of similar-looking rules that are genuinely distinct) and
disqualify the screen mechanically when it scores well on it. The control is the deliverable.

---

## 7. The remediation program for the file as it stands today

**This is a batch, and it obeys batch discipline: the classification is frozen at start.** If the
shape contract changes mid-pass, the pass was run against a moving target and must restart.

**Phase 0. Measure, and record nothing in prose.**
Section title manifest, per-section line counts, total size, per-ID citation counts, and the CM-1
through CM-10 detector output. Everything goes into the pass note, never into `CLAUDE.md`.

**Phase 1. Classify every section into exactly one bucket.** No edits in this phase. Output is a
table of `section title -> bucket -> destination`.

| bucket | meaning | action later |
|---|---|---|
| **ROUTE** | live rule, fires at action time | compress to the four-part form |
| **MECHANIZE** | decidable, currently remembered | write the checker, replace with a table row |
| **MOVE** | argument, incident, measurement, worked case | to `tools/process/<slug>.md`, leave a READ |
| **MERGE** | a restatement of another entry | fold in, fix the surviving trigger |
| **DELETE** | prior-state prose, dead subject, self-contradiction resolved elsewhere | delete, commit message narrates |
| **ASK** | a rule Tim wrote in his own voice that looks dead | one batched list, one line of assent each |

**Phase 2. Execute in bucket order: MOVE, then MERGE, then ROUTE, then DELETE, then MECHANIZE.**
Moves are the cheapest and free the most space. Mechanize last, because a checker written against
prose that is about to be rewritten is a checker written against a moving target.

**Phase 3. One file-sized unit per pass.** The natural unit is a contiguous run of sections, not one
section at a time, and not the whole file. Compressing the whole file in one round is exactly the
shape that generates new defects; the 25-site conversion of 2026-08-15 is the evidence already on
record.

**Phase 4. Control-test each compressed entry.** Give a fresh agent the exact task the entry
governs, read only, without telling it the answer, and see whether the entry fires. **Fix the
scorecard before the result comes back.** A compression you have not tested is a hypothesis about
what a reader needed from the deleted words.

**Phase 5. Test delivery separately from correctness.** A mid-session edit does not reach agents
spawned afterward, so a compressed entry can be correct and unreachable. During a compression pass:
carry moved-entry pointers verbatim into every brief, and maintain `tools/process/MOVED.md` mapping
old section title to new home, so "someone refers to a rule you do not recognise" resolves in one
grep instead of an accidental one.

**Phase 6. Record the class, the trigger diagnosis, and the test result, including how the test was
compromised.** A control that passed for the wrong reason is worth more written down than a clean
pass.

**What this costs.** `CLAUDE.md` and `tools/process/**` are exempt from the editorial and adversary
gates, so moving an argument between them owes no prose review round.

⚠ **A pass that edits a brief under `.claude/commands/**` DOES owe both gates.** That directory is
the one R-EXEMPT marks explicitly non-exempt — *"published-and-exempt is not a category you may
reason your way into"* — and Phase 5 routinely edits briefs, so the exemption above does not travel
with the pass. Measured 2026-08-24: a compression pass **edited one brief in that directory and
created a second**, both gates were run on them, and they returned FAIL-BEDROCK and FAIL between
them — including against this file. **Budget for the round.** The other real risks are delivery (Phase 5) and losing a rule
inside a move (Phase 1 classification, which is why no edits happen there).

---

## 8. The checker

`tools/verify/check_claude_md.py`. Legs are split by kind, because the downgrade rule splits at the
leg and not at the check.

**DO NOT LOOK UP WHAT BLOCKS WHERE — RUN IT.** The checker prints its complete leg table first on
any run that judges the file: each leg, its enforcement mode, and the property it tests. Restating that table here puts
a second copy beside the one the tool computes, and the copy is the half that goes stale — which is
this file's own §6 defect class, committed in the section describing the checker that would catch it.

⚠ **Some legs are PENDING: declared, built no further, and NOT PASSING.** The banner says so in
those words, and it is the load-bearing sentence in the output: *"PENDING legs are NOT checked and
NOT passing. A clear run below is not evidence about them."* A PENDING leg is an unpriced exemption
until the Phase 1 sweep arms it. **Read the count off the run, never off this paragraph.**

**The counts print on every judging run, blocked or clear.** A downgraded gate must get louder, not quieter;
a warning nobody counts manufactures the appearance of coverage. Rising suppression counts are the
tell that the warn legs are being rubber-stamped.

**The manifest declares its own enforcement mode at every entry point**, so nobody has to look up
what blocks where.

---

## 9. Cadence

**Attach the audit to triggers that already fire, never to a calendar.**

- **Every push whose diff touches `CLAUDE.md`:** the checker runs, prints the budget delta and the
  receipt it computed. This is the one that matters, because it fires exactly when growth happens.
- **On the phrase "update the handoff":** the citation and CM report prints. That phrase is already
  the trigger this project loaded its git hygiene onto, and it fires.
- **When the escalation ladder reaches rung 3 for any rule:** run §2 step 0 against the whole file,
  not just against the rule in hand, because a trigger defect is rarely unique.
- **Never on a release.** Releases are the rarest action, which is where the self-heal counter was
  buried and stopped being read.

---

## 10. Division of labour

**Claude does, without asking:** classify, move bodies out, compress to the four-part form, merge
restatements, write checkers, fix stale pointers, delete prior-state prose, run and report the
control tests.

**Claude asks first:** deleting a rule (as opposed to its justification), changing a cap or a
budget, downgrading a leg from BLOCK to WARN, retiring a section written in Tim's voice.

**Claude never:** narrates a compression as a rewrite of Tim's intent, or lets a rule disappear
without it landing in a checker, a body, or an explicit assent line.

---

## 11. Worked example

**Before** (one real section, roughly ninety lines: rung 5 and non-convergence, with its two
triggers, its measured round counts, the leg table, the guard argument, the probes, the
discriminator, and four warnings).

**After:** the four-part entry `R-NOCONV` in `CLAUDE.md`, and the argument in
`tools/process/non-convergence.md`. **Read the entry there rather than here.**

⚠ **This section used to reproduce the entry inline, and the copy was wrong within nine days** —
it ran 12 lines against the real 14, and silently dropped *"never assert it"*, the whole
screen-may-replace-the-ENUMERATION-never-the-VERDICT clause with its `>=2 of 3` rule and its
control, and *"a downgraded gate prints its count every run"* — while captioned **"Nothing is
lost."** Found by the editorial gate, 2026-08-24. **That is §6's copy-that-drifted class, committed
by the worked example demonstrating how to avoid it**, and it is the reason the copy is now a
pointer: a reproduction here would become false the moment the entry moved, and R-ADJACENT's test
says a sentence with that property is a copy, not a citation.

**What the example is actually teaching is the SHAPE, and that is what to take from it:** roughly
ninety lines — two triggers, the measured round counts, a leg table, the guard argument, the probes,
the discriminator and four warnings — become a fourteen-line entry with a TRIGGER, a RULE, a COST
and a READ. Nothing is deleted; the argument moves to the body. What stops being paid for is the
eighty lines that every session and every subagent loaded in order to not hit this trigger.

---

## 12. This file is subject to its own contract

It will grow, by the same mechanism. So: it carries a cap, it is checked by the same checker, and an
addition to it is paid for the same way. If it ever needs a second file, that is the signal that a
section of it should have been a checker.

**And the one honest limit worth stating up front:** everything here except the BLOCK legs in §8 is
remembered rather than enforced, and this project's own record is that remembered rules fail by
construction. The BLOCK legs are the part that will still be working in six months. Build those
first, and treat the rest as scaffolding that buys time until they exist.
