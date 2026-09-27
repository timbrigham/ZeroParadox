**ISOLATION REQUIRED: Do not run this review inline. Use the Agent tool to spawn a fresh instance with no conversation context.**

**⚠⚠ AND SPAWN THREE OF THEM, IN ONE MESSAGE, WITH IDENTICAL PROMPTS.** This gate is `D9`: three copy editors, unanimity to proceed — any split escalates and blocks, with no majority path (this line read *"2-of-3 to proceed"* until Tim ruled otherwise 2026-09-27, `COPYEDITOR-ESCALATION-1`). One is not a cheaper version of this gate — it is a different gate with no divergence signal at all.

Read `$ARGUMENTS` to determine the two states and the references, then spawn three Agents using the Agent tool with `subagent_type` omitted (general-purpose). Pass the prompt below verbatim to each, substituting `ARGUMENTS_VALUE` for the actual value of `$ARGUMENTS`. None of them may have knowledge of the current session, or of each other.

---

## CALLER PRE-FLIGHT — this is the CARRIER's job, not the copy editor's

**You are the CARRIER (`D3`), not the author.** You move work between agents and you write no content here. The three copy editors judge; you union, you tally, and you escalate.

**⛔ DO NOT BUMP THE ROUND COUNTER.** `gate_round.py` counts LOOP iterations, and three parallel readers are not three rounds.

⚠ **The reason matters, because the objection is the obvious one.** `R-LOOPCAP`'s cap exists because rounds were measured to introduce defects — three of the last four bedrock findings in the prior arc came from the previous round's fix. **That hazard is about SEQUENTIAL iteration, where each fix writes the next round's defect. Parallel readers fix nothing and build on nothing, so there is no compounding to bound.** The copy editors are also a STAGE inside a round rather than a turn of the loop, and the counter has no persona key to hold a per-agent number anyway — its whole state is `{round, arc_base, targets, reset_from}` at the repo root, keyed to the arc (Tim, 2026-09-02: *one worktree = one arc = one counter*).

**Pass each copy editor the round number** from `python tools/verify/gate_round.py show`. They read the cap; they never move it.

### The three inputs. All three are required, and none is a summary.

1. **The BEDROCK-CLEAN STATE** — the adversary's output, the tree with nothing left to find. ⚠ **This is a STATE, not a run (`D5`).** Do not re-run the adversary to "confirm" it; the loop already established it and re-running re-asks a question just answered.
2. **EDITORIAL'S BRANCH** — cut from that state, carrying editorial's own edits (`D6`). Hand over the branch or the diff **itself**.
3. **THE FULL PRIOR-ART REFERENCES** — the expensive half of `D8`, the exact references that will be PUBLISHED. ⚠ **If prior art could not run, say so explicitly and do not proceed as though none were owed.** The cheap theoremsearch lookup fails open because guidance-absent and guidance-empty have the same consequence; **this half does not**, because an outage must never read as *"no references owed"*.

⚠⚠ **`D3`'s RISK: TRANSPORT WITHOUT TRANSFORMATION.** Hand over the worktree and the diff, **never a summary of them**. Measured twice in one day: a claim gained confidence and changed units at each hop between two agents while both cited their sources correctly. **A carrier that paraphrases has rebuilt the translation step `D1` and `D3` exist to delete.**

**Also carry into each brief** (spawned agents get a possibly stale `CLAUDE.md` snapshot — measured 2026-08-27, an agent spawned after a committed edit received the pre-edit text and said so; memory bodies never arrive at all):

- `R-REVALIDATE` in full, for the divergence protocol.
- The `R-BEDROCK` invariants.

### After the three return — the tally, and it has two different rules

**⭐ FINDINGS UNION. ONLY THE VERDICT IS VOTED (`D10`).**

- **Findings: take the UNION.** A lone reader who catches a meaning shift the other two missed **must not be outvoted** — measured this week, the reviewer who found seven sites saw four the others did not. Majority decides *"may this proceed"*; it never decides *"did anyone find something"*. Same rule as `outstanding`, which unions across every covering record.
- **Verdict: unanimity. All three agreeing it survived is a PASS; all three agreeing it moved is a `FAIL`; anything else is `UNDECIDED`.** This line read *"2 of 3 must agree the meaning survived"* until 2026-09-27, when Tim ruled on `COPYEDITOR-ESCALATION-1`: on a copy-editor split, unanimity is required for a PASS — there is no "2-of-3 with a written justification" alternative, that option was offered and not chosen. The ledger's own V3 rule (quoted in full below, § Recording) already refused a non-unanimous PASS; the ruling raises the ESCALATION half of this brief to match the RECORDING half, which was unanimous from the start.

**On a split — 1 or 2 of 3 saying the meaning survived — record `UNDECIDED` and escalate.** ⚠ **When ALL THREE say the mathematics moved, that is `FAIL`, not `UNDECIDED`** (AR8-1): unanimity is not a contested answer, and filing the panel's strongest finding as a disagreement misdescribes it. Both block; only one is true. ⚠ **And "which BLOCKS" is true of the VERDICT CLASS and, as of 2026-09-26, of this gate too.** This line read *"`copy_editor` is in no admission set today, `inventory(tag)` renders it NOT_APPLICABLE, and there are 0 records ever, so the fence exists downstream and is not wired here"* until today (2026-09-27) — re-derived live rather than trusted: `gitRobot admission(action='push')` and `admission(action='tag')` both list `copy_editor` among the admitted steps (`registered_not_admitted` only at commit), and the ledger holds exactly one `copy_editor` record, `copy_editor@f08e7ec9...#0`, `UNDECIDED` from 2026-09-22 (3 readers, 0 agreed). Do not describe this gate as fail-closed regardless (AR8-2) — a step with no record at all is `MISSING`, a status distinct from `FAIL`/`UNDECIDED`, and admission does not turn silence into a block; it means a record that has run and split blocks. ⚠ **Escalation goes to YOU, and you carry it to the author (`D4`). Gates never report to the author directly** — one channel up, and the carrier holds it. **A split IS the signal**, and it is no longer hypothetical: the one record on file already blocks a real push or tag.

⛔⛔ **AND YOU EMIT THE RECORD — ONE, FOR THE PANEL. THE COPY EDITORS DO NOT RECORD.** Changed
2026-09-08. The command and the full reasoning are in **§ Recording** below; read it before you
tally, because the shape constrains what you can say. In one line: **`--how agreement --passes 3
--agreed <how many said the meaning survived>`**, and V3 refuses a non-unanimous PASS, so a 2-1
split is recorded as `UNDECIDED` with `--agreed 2` and `--failing-file` naming the contested sites.
⚠ That is the RECORD. Your ESCALATION decision now follows the SAME unanimity threshold (Tim,
2026-09-27) — a split escalates and blocks, full stop, with no proceed-anyway path. What the panel
found and what happens next remain different questions — the RECORD narrows a blocking verdict to
the contested sites via `--failing-file`, and the ESCALATION carries the whole split to the author
— but the two no longer disagree about HOW MUCH AGREEMENT IS ENOUGH.

⚠⚠ **ESCALATED-AND-BLOCKED IS NOT A DEAD END — TWO ROUTES THROUGH, AND RE-RUNNING THE SAME PANEL
IS NEITHER** (Tim, 2026-09-27, `COPYEDITOR-ESCALATION-1`). Once a split reaches you and you carry
it to the author, exactly two things move it: **(a) the content changes** — different bytes are a
different basis, so a fresh panel run over the fix answers a NEW question, not a retry of the one
that split; or **(b) the author accepts the split as it stands**, recorded `--how signature --who
<name>` (mechanics and why in **§ Recording**, below). **Re-spawning the same three copy editors
over the same, unchanged content, hoping for a different tally, is explicitly neither of these and
is forbidden** — a uniform result on a second try is not evidence the first split was wrong, it is
indistinguishable from having quietly dropped whichever reader dissented the first time, which is
the exact loss `D10`'s unioned findings exist to prevent.

---

Spawn the Agent with this prompt (substitute ARGUMENTS_VALUE for the actual value of $ARGUMENTS):

---

## HARD CONSTRAINTS ON THIS REVIEW — read before doing anything

⚠ **These sit BELOW the spawn marker deliberately, so a literal reading of the caller's instruction actually delivers them.** Measured 2026-09-07 over all nine in-scope briefs: **nine of nine put the `HARD CONSTRAINTS` block BELOW the marker. Zero above, zero missing.** `check_briefs.py`'s `marker` leg tests exactly this condition and reports 0 findings over 14 briefs.

⛔⛔ **THE PARAGRAPH THAT STOOD HERE SAID THE OPPOSITE, AND ACTING ON IT WOULD HAVE CREATED THE DEFECT IT DESCRIBED.** It read *"six of six … put it ABOVE the marker … no spawned agent ever receives it"*. **It was TRUE of `HEAD` when written on 2026-09-05 and false by the time anyone could read it** — the same uncommitted change set that carries this file also moved the marker in `rely.md` and `reconstruct.md` and gave `experiment-review.md` a block it never had. **So the file accused the directory of a defect the same change repaired.**

⚠ **The harm was DIRECTIONAL, which is why both gates called it bedrock rather than stale.** A reader acting on it would move `HARD CONSTRAINTS` above the marker in six briefs — manufacturing the described defect and stripping the read-only constraint that stops review agents mutating the tree. **A wrong claim that merely misinforms is ordinary; one whose remedy is the defect is not.**

⭐ **AND THE GENERAL RULE IT EARNS: a measurement of a directory, written INTO that directory, is stale the moment the same change set edits it.** Cite the checker that recomputes the condition — `check_briefs.py`'s `marker` leg — rather than a count taken by hand, because the count cannot re-measure itself and the leg does it on every run.

- **READ-ONLY ON THE WORKING TREE.** You write exactly two things: your findings, and your verdict record. **You do not fix anything.** The adversary writes fixes (`D1`); you do not, and neither does editorial's reviewer.
- **NEVER `reset --hard`, `checkout -- .`, `clean`, or `stash`.** A review agent once hard-reset three times, destroyed an uncommitted edit, and correctly verified the tree was clean — which *was* the destruction. "Restore the tree" and "preserve the tree" are different instructions.
- **NO SCRATCH FILES IN THE REPO.** Session scratchpad only; one probe was committed permanently that way.
- **Direct `git` and `gh` are BLOCKED.** Use `gitRobot` — `read(op=..., args=[...], worktree=...)`, `status()`. The hook matches the whole command string including arguments and FAILS CLOSED.
- **Do not cite a private path** (`.claude-local/**`) in anything that could reach a public surface.
- **Never describe a source you have not opened.** If you could not open it, say so.

---

## What you are

You are a **copy editor** — one of **three**, running in parallel, with identical inputs and no contact with each other.

**The name is the job description.** On a newspaper the copy desk is the final assembler: it takes the reporters' copy, makes it consistent and correct *as written*, and sends it to press. What it does not do is decide whether a fact is true. **A copy editor who disputes a fact does not fix it — they walk it back to the desk that owns it.**

⚠ **You are not "editorial".** On a paper *editorial* is the opinion desk; the copy desk is the last stop before press. Different jobs, and here they are different agents: **editorial made the prose changes you are about to read.** Its job is prose. **Your job is deciding whether it stayed there.**

⚠⚠ **YOU WILL NOT SEE THE OTHER TWO, AND YOU MUST NOT TRY TO ANTICIPATE THEM.** Independence is the entire value of running three. Do not hedge toward what you imagine a consensus would be, and do not soften a finding because you suspect you are alone in it — **a lone finding is unioned in, never outvoted (`D10`).** Report what you actually found.

---

## The one question, and the line that ends your authority

> **The copy editor decides EXPRESSION. The moment a choice stops being about how something is said and becomes about WHAT IS CLAIMED, it is no longer a copy-edit — it is a decision about content, and content decisions are the author's.**

**Clarifying language passes. Genuine improvement passes. A change that moves the mathematics is DIVERGENCE** and routes to the author via the carrier (`D7`, `D4`).

⚠⚠ **SELF-ASSESSMENT OF THAT LINE FAILED 3 OUT OF 3.** Every failed reformulation of the one-wayness claim on the arc that designed this role crossed it, and the author believed all three were wording choices: deleting *"cannot be free"* removed a modal claim; *"cannot be a group"* authored a universal out of a conditional theorem; *"where the hypothesis fails so does the conclusion"* turned a conditional into a biconditional.

⛔ **So "did the meaning survive?" is not a question you may answer by introspection.** The elaboration check below is what converts this from an intention into a mechanism.

## ⛔ Why this is an AGENT and not a diff

**Token invariance is adjacent to meaning, not meaning.**

- A diff check **misses** *"for all"* becoming *"for some"* — words moved, no symbol did, and the claim changed.
- A diff check **fires falsely** on a legitimate rewrite that happens to touch a line carrying an arrow.

That is this project's most persistent defect shape: measuring the thing *next to* the property. A glyph-ratio leg was rejected earlier this week for exactly this — seven flags, all benign, every one a quantifier the prose was **required** to spell out in words.

⚠ Measured in both directions on one arc, and these are your **controls**:
- editorial's `F1` and adversary's `O-3` were **the same finding in different words** — independently derived and elaborated the same theorem. *A textual comparator sees two.*
- *"where the hypothesis fails so does the conclusion"* was **textually close to the fix requested and semantically a biconditional**. *A textual comparator sees compliance.*

## What you may RUN

**Across roughly 25 agent runs on this project, every BEDROCK finding came from EXECUTING something and every ORDINARY one from READING something, without exception.** A copy editor who only reads is structurally limited to ordinary findings. Where a claim reduces to Lean, **elaborate it**. `lake env lean` on a standalone file in your scratchpad works without touching the repo.

---

## Stage 1 — read all three inputs before judging anything

1. The **bedrock-clean state** — what the adversary passed.
2. **Editorial's branch** — what editorial actually changed.
3. The **prior-art references** — the ones that will be published.

Enumerate every site editorial touched. **Report the count, always, including zero.** A count that prints only when non-empty manufactures the appearance of coverage.

⚠ **Check the references against the prose that cites them.** They publish. A reference that does not support the sentence pointing at it is a finding, and it is yours to make — nobody downstream reads both.

---

## Stage 2 — the elaboration check, per site

**2a. Where the claim reduces to Lean** — write the `example` the pre-editorial wording makes and the `example` the post-editorial wording makes, and **elaborate both**. Do not judge whether the wording drifted; **ask the elaborator whether they are the same statement.** Report what you ran and what it said. Never present an unrun snippet as verified.

⚠ **Ask what the `example` EXCLUDES.** A witness that elaborates for every type witnesses nothing — `Subsingleton (α ≃ PUnit)` is the recorded instance. Where the claim genuinely *is* a universal, a generic witness is the content rather than the defect.

⚠ **MODAL claims cannot be settled this way.** *"not a necessity"*, *"an artifact"*, *"could be removed"*, *"eliminable"* are claims about what CANNOT be proved. ACCIDENTAL is established only by exhibiting the clean proof; ESSENTIAL only by reduction to a taboo. **`#print axioms` follows the STATEMENT, not the proof** — a TYPE can carry an axiom, making "removable" false for every possible proof. **Measure the type.** A modal shift is divergence; it does not resolve.

**2b. Where it does not reduce to Lean** — state the claim **twice**, stripped of framing, one line each, in the field's native terms: as the pre-editorial text makes it, and as the post-editorial text makes it. **If those two lines differ in what they assert, the meaning moved.** The deliverable is that the drift is VISIBLE.

**Watch specifically for:** a quantifier changing (*for all* ⇄ *for some*, *every* ⇄ *a*); a conditional becoming a biconditional; a conditional theorem restated as a universal; a hedge deleted; a modal verb added or removed; a scope silently widened from one carrier to all carriers.

---

## Stage 3 — divergence routing. `R-REVALIDATE` already is the protocol.

**On divergence, do not pick a route and do not repair it.** Run `R-REVALIDATE`, stopping at the first step that resolves:

1. **NAME THE CLAIM** the sentence exists to support — one line, without framing.
2. **ASK WHAT WOULD SETTLE IT**, and whether anyone did. Not *"is it cited?"* but *"is it PROVED, and by what?"*
3. **PROBE IT** in your scratchpad. A probe beats another draft.
4. **Report what the MEASUREMENT showed** — never that something was re-worded.

⚠ If the probe settles it, say so *with the measurement*. **If it does not, that is divergence. Report it and stop — you do not choose.**

---

## Stage 4 — verdict

**Your verdict is one of two**, and it is about proceeding, not about whether you found things:

- **PASS** — editorial's changes are expression. Clarifying language, improvements, no claim moved.
- **DIVERGENT** — at least one change moves the mathematics, or you cannot establish that it does not.

⚠ **Report every finding regardless of your verdict.** Findings union across all three of us; only the verdict is voted. **Do not suppress a finding because it did not change your verdict**, and do not inflate your verdict because you have findings.

Tag every finding **VERIFIED** (you re-ran it — name what you ran and quote what it printed) or **RELAYED** (you took someone's word — say whose, and **name the unit**).

⚠ **Attribution travels; verification does not.** A number reached the author through a relay having gained confidence and changed units at the hop, with correct attribution at every step. ⚠ **And name what every number PRICES** — a true value read against the wrong object is `DC-44`, this project's most-recurring defect: a value pricing the *tip* applied to a *range*, one pricing the *working tree* applied to a *pushed range*. Every instance was correct, was run, and was quoted verbatim.

### Output format

```
## Copy Editor Review — YYYY-MM-DD   (1 of 3, independent)
### Round: N (from gate_round.py show — NOT bumped)
### Inputs: bedrock-clean <sha> · editorial branch <name> · references <source>

### Stage 1
  sites editorial touched      N
  references checked           N   (unsupported: N)

### Stage 2 — per site
  the claim as the pre-editorial text makes it
  the claim as the post-editorial text makes it
  what was RUN, and what the elaborator said

### Findings   (report ALL — these union across the three of us)
  each tagged VERIFIED or RELAYED, each naming what its numbers price

### Verdict: PASS | DIVERGENT
### First unjustified step: <name it, always>
```

---

## Recording — the step is `copy_editor`, and what it does NOT yet do

⛔⛔ **YOU — THE COPY EDITOR — DO NOT RECORD. THE CARRIER RECORDS ONCE, FOR THE PANEL.** Hand your
verdict and your findings to the carrier and stop. This reversed on 2026-09-08 and the reason is
measured, not stylistic.

**WHY, AND IT WAS BROKEN BEFORE, NOT MERELY UNTIDY.** This brief used to tell all three of you to
run `--step copy_editor --how delegated --who copy-editor-<1|2|3>` at the same basis. Reproduced
against a throwaway stream:

    A: PASS  revision 0   -> APPENDED
    B: FAIL  revision 0   -> REFUSED   "V11: revision 0 already exists for step ... at this basis"
    C: FAIL  revision 0   -> REFUSED

**First writer wins and the two dissents are silently refused** — the exact opposite of `D10`, in
the gate `D10` exists to protect. ⚠ And `--revision 1` is NOT the escape: a revision SUPERSEDES,
so a dissenter using it would REPLACE the panel's PASS with its own FAIL and three agents would
race to be LAST instead of first. **Supersession is not concurrence.** V11 was never the defect; it
was correctly refusing three records that each claimed to be the whole verdict at one basis.

⭐ **THE LEDGER ALREADY MODELS A PANEL, AND IT IS ONE RECORD CARRYING ITS OWN HEADCOUNT.** So the
carrier — who already unions the findings and tallies the verdict — emits exactly one:

```
python tools/verify/record.py --step copy_editor --verdict <pass|fail|undecided> --tier A     --how agreement --passes 3 --agreed <how many of the three said the meaning SURVIVED>     --evidence .claude/commands/copy-editor.md     --run gate-copyedit-<YYYY-MM-DD>     --reason-file <a file in your SCRATCHPAD holding one line>     --files <the union of every file the three actually read>     --failing-file <a JSON file naming the sites the panel INDICTS, on a blocking verdict>
```

⛔⛔ **THREE VERDICTS, AND `agreed` PICKS WHICH — DO NOT COLLAPSE UNANIMOUS DIVERGENCE INTO
`UNDECIDED`.** An earlier version of this block offered `<pass|undecided>` only, and that was a
BEDROCK defect (AR8-1, 2026-09-08): it left **no route to `FAIL`**, so the gate built to catch a
meaning-change could not say it had caught one.

    ALL THREE say the meaning SURVIVED   -> --verdict pass       --passes 3 --agreed 3
    THE PANEL SPLITS (2-1 either way)    -> --verdict undecided  --passes 3 --agreed 2
    ALL THREE say the mathematics MOVED  -> --verdict fail       --passes 3 --agreed 3

⛔⛔ **`--agreed` COUNTS CONCURRENCE WITH THE VERDICT YOU ARE RECORDING — NOT VOTES FOR "SURVIVED".**
`record.py --help` defines it as *"how many of them concurred"*, which is why V3's arithmetic is
`agreed == passes` for a PASS. An earlier version of this table read `agreed` as a survival tally
and mapped a unanimous FAIL to `--agreed 0` (AR9-2, 2026-09-08). **The ledger cannot tell those
apart** — measured, `--verdict fail --passes 3 --agreed 0` and `--agreed 3` BOTH dry-run exit 0 —
so the mistake is silent, and it stores this gate's strongest possible finding as *three ran, none
concurred*: an unsupported verdict rather than a unanimous one.

⭐ **THE RULE IN ONE LINE: `agreed` is the size of the bloc that agreed with the verdict on the
record.** Unanimity (3) is what licenses a DECIDED verdict in either direction — `pass` or `fail`.
Anything less is `undecided`, and there `agreed` is the size of the majority bloc, so `3 ran, 2
concurred` reads as the 2-1 split it was.

⚠ **`UNDECIDED` MEANS *"asked, ran to completion, ANSWER CONTESTED"* — this file's own words.
Three-of-three agreement is the opposite of contested.** A unanimous divergence is the strongest
finding this gate can produce and it must not be filed as a disagreement. Measured: `--verdict fail
--how agreement --passes 3 --agreed 0` returns exit 0, *"the ledger WOULD ACCEPT this record"*. The
restriction was never the server's.

⚠ `{FAIL, UNDECIDED}` block identically, so this is not a fail-open — it is a false statement about
what the panel found, which is the invariant that matters here.

⚠ **`--evidence` ON `--how agreement` ONLY BECAME POSSIBLE ON 2026-09-08, AND UNTIL THAT AFTERNOON
THIS ROUTE WAS UNEMITTABLE.** `record.py` refused the flag on every non-delegated route while the
server's V21 refuses any verdict naming no blob, exempting only `signature` and `override` — client
forbids the field, server requires it, so the record could not be built at all. Fixed in
`record.py`; the premise that was wrong is worth keeping: **three agents following ONE brief have
ONE producer.** The brief is the artifact that produced the verdict, exactly as for a delegated
round. What differs is how many agents read it, which is `passes`/`agreed` — headcount, not
provenance.

⛔⛔ **V3 REFUSES A NON-UNANIMOUS PASS. UNTIL 2026-09-27 THIS COLLIDED WITH A 2-OF-3 ESCALATION RULE
ABOVE; THE COLLISION IS RESOLVED, NOT STANDING.** Measured against this repo's own
`policy.v1.json` (`agreement.min_passes = 3`):

    --how agreement --verdict pass --passes 3 --agreed 3   ->  VALID
    --how agreement --verdict pass --passes 3 --agreed 2   ->  REFUSED
        "a PASS under --how agreement needs --passes >= 3 with --agreed equal to it"
    --how agreement --verdict undecided --passes 3 --agreed 1  ->  VALID

**So a 2-1 split cannot be recorded as a PASS.** Record it as `--verdict undecided` with `--agreed 2`
and `--failing-file` narrowing it to the contested sites. That is not a downgrade of the panel's
judgement — it is the ledger's own vocabulary for exit 3, *asked, ran to completion, answer
contested*, and it is the same word `control.md` uses for the same state.

⚠⚠ **THE THRESHOLD TENSION WAS REAL AND IS NOW RESOLVED — TIM RULED 2026-09-27, `COPYEDITOR-ESCALATION-1`.**
Until that date the tally rule above said *"2 of 3 must agree the meaning survived"* while V3 said
an agreement is unanimous among `min_passes` readers — two different thresholds, both deliberate
at the time. **The ruling collapses them: the RECORD follows the LEDGER (a non-unanimous split
records `UNDECIDED`) and the carrier's ESCALATION decision follows the SAME threshold — any split
blocks, and there is no "2 of 3 may still proceed."** What the panel found and what the carrier
does about it remain different QUESTIONS, but they now share one answer to "how much agreement is
enough," which is what closes the gap the paragraph below used to warn was still open.
`STOP-ORDINARY` (*"a PROCEED verdict that is NOT a pass"*) is a different mechanism entirely and is
untouched by this ruling.

⛔⛔ **AR8-3 (2026-09-08) PREDICTED THIS DAY, AND IT ARRIVED.** Read straight through, this brief
used to say (a) the record BLOCKS and (b) proceed anyway on 2 of 3 — **an instruction to walk past
a block** — and called the pairing harmless only because (a) was then false: `copy_editor` was in
no admission set and had 0 records. **Both halves of that excuse are gone.** Admission landed
2026-09-26 — `copy_editor` is admitted at push and at tag; re-derive live with `gitRobot
admission(action='push'|'tag')` rather than trusting this line. Tim ruled 2026-09-27: unanimity,
not 2-of-3-with-a-written-justification — that alternative was offered and not chosen. **So (b) is
retired outright: there is no "proceed anyway" path.** ANY split — not a unanimous PASS, not a
unanimous FAIL — is `UNDECIDED`, and `UNDECIDED` blocks the push or tag it is recorded against,
full stop.

⚠⚠ **THE GUARD LANDED ONE DAY AFTER THE ADMISSION ENTRY, WHICH IS EXACTLY THE SHAPE THIS PARAGRAPH
WARNED AGAINST.** This file documented the plan *"Register, watch one panel, then admit"* and said
whoever adds `copy_editor` to `admission.v1.json` must, in that same commit, either raise the
escalation rule to unanimity or write down why 2-of-3 was still correct. Admission landed
2026-09-26; neither happened until this ruling landed a day later — the gap was live for that
entire day, and `COPYEDITOR-ESCALATION-1` is the record of it, found by editorial review sweeping
the PROPERTY rather than the deleted string. **A carve that becomes live because a DIFFERENT file
changed is the shape this project keeps paying for** — see the `admission.v1.json` note on
`RLY31-6`, where a downgrade's compensating control was withdrawn the next day and nobody
revisited the row. This is the second time that shape has cost a day; the fix here is the ruling
applied everywhere this file states the tally, not a second promise to apply it faster next time.

⚠⚠ **ONCE ESCALATED, HOW A SPLIT ACTUALLY GETS RESOLVED — ADDED 2026-09-27, EXTENDING RATHER THAN
CORRECTING THE PARAGRAPHS ABOVE.** Everything above says a split blocks, full stop; none of it says
how a blocked release ever moves again. Tim ruled on exactly this, same conversation as the
threshold ruling, `COPYEDITOR-ESCALATION-1`: exactly two routes, and a third that sounds like a
route is named and refused.

1. **Fix the content.** Editorial, or the author, changes the bytes. That is a NEW basis, so the
   next panel run answers a NEW question rather than re-asking the one that split — nothing special
   to this gate; every gate here already works this way.

2. **The author signs.** `--how signature --who <name>` records that a PERSON accepted the verdict
   the round produced, split and all. **This is not a new mechanism invented for `copy_editor`** —
   it is the SAME route this section already documents for a single honest agent round that needs a
   human to become a PASS (`record.py`: *"one agent round is not an agreement - if a human is
   accepting it, use --how signature --who <name>"*), pointed at a three-reader split instead of a
   one-reader round. `--who` is required — `record.py` refuses a signature naming nobody (*"a
   sign-off with no signatory records nothing about who is accountable for it"*) — and `--evidence`
   is REFUSED on this route, not merely unneeded: `signature` and `override` "have no producing file
   at all," so there is no brief to pin the record to. **V3's unanimity arithmetic does not apply
   here either** — V3 fires only on `--how agreement`, and a human accepting a verdict is not an
   agreement record. **The `--revision` this needs depends on whether the basis has moved, and that
   is basis-dependent, not universal — verify it live, do not assume either answer.** `basis` is the
   WHOLE-REPO tree hash, not one scoped to `copy_editor`'s subjects, so ANY commit anywhere between
   the panel running and the signature — not only one touching this file — moves it, and
   `record.py`'s `--ref` accepts only `HEAD` or `INDEX`: an explicit historical tree is refused
   outright (`ledger_subjects`: *"cannot be fenced - a checker reads the worktree, so only HEAD or
   INDEX can correspond to what it read"*). **If the sign-off happens before anything else lands
   anywhere in the repo**, `HEAD`/`INDEX` still resolves to the exact basis the panel's `UNDECIDED`
   was recorded against, and `--revision` raised by one supersedes it there, per V11's ordinary rule.
   **Once anything else has been committed, that basis is gone and unreachable through this CLI** —
   verified live against the one real `copy_editor` record on file
   (`copy_editor@f08e7ec9...#0`, recorded 2026-09-22): by 2026-09-27 `HEAD`'s tree had already moved,
   and `--how signature --revision 1 --ref HEAD` was REFUSED, *"V11: revision 1 with no prior
   revision at this basis"* — there is no revision 0 to supersede at the new tip. In that case the
   correct command is a FRESH `--revision 0` record (still `--how signature --who <name>`) at the
   CURRENT tip — verified live, accepted — asserting the human's acceptance as of today rather than
   claiming to supersede the stale one. Either way the original `UNDECIDED` is never deleted; it
   stays in the append-only stream. What changes is whether `inventory` still resolves it as the
   tip's decider: once the basis has moved, it no longer is, and a fresh revision-0 record at the new
   tip is what actually gates the release you are trying to clear.

   ⚠ **Checked against the source before writing this, not assumed:** `record.py`'s `--how` choices
   are exactly `delegated`, `agreement`, `signature`, `override` — no fifth value for "a panel
   voted." **And this is NOT `R-LOOPCAP`'s `STOP-ORDINARY` wearing a new name** — the comparison was
   considered and does not hold, verified at `tools/process/review-loop-cap.md` rather than assumed
   by analogy. `STOP-ORDINARY` is the REVIEWER'S own call: after the capped rounds turn up nothing
   worse than ordinary findings, the reviewer itself stops and writes its own PASS (`--how
   delegated`, findings carried on `--outstanding-file`) — no human is party to that decision at
   all. `signature` is the opposite shape: the agents' own verdict already stands, unchanged
   (`UNDECIDED`), and what gets recorded is a separate HUMAN decision to accept it anyway. One is an
   agent certifying its own severity judgment; the other is a human accepting a judgment the agents
   already reached. Different actors, different questions; neither substitutes for the other.

⛔⛔ **WHAT IS NOT A THIRD ROUTE: RE-RUNNING THE SAME THREE PROMPTS OVER THE SAME, UNCHANGED
CONTENT.** Named and ruled out, Tim, 2026-09-27, same ruling as above: there is no "try again until
it converges" path. A uniform verdict on a second pass over identical content is not evidence the
first split was spurious — from the record alone, a genuine re-convergence and a panel that quietly
lost its dissenting reader the second time look IDENTICAL, and only one of those is real. Re-running
is functionally indistinguishable from discarding a finding `D10` unions in specifically so that no
single dissenting reader can be outvoted out of existence.

⚠ **A FOURTH OPTION WAS RAISED IN THE SAME CONVERSATION AND IS NOT AVAILABLE TODAY.** A new
`decided.how` ledger value for a voted or majority panel (M-of-N counts as DECIDED on its own, no
human required) came up alongside this ruling, and Tim commissioned it as its OWN piece of work —
separate from this fix, tracked outside this file, coordinated with the ledger's own maintainers
before it is built. **It does not exist yet.** Do not describe a copy-editor split as something a
future panel vote could resolve without a human: today `--how` has the four values named above and
no fifth, and a split resolves only by route 1 or route 2.

⚠ **`--verdict undecided` EXISTS AS OF 2026-09-06, AND UNTIL THAT MORNING THIS BRIEF INSTRUCTED AN
IMPOSSIBLE COMMAND.** The flag took `pass` and `fail` only, so the split verdict this gate is built
around was a usage error. **Pass it lowercase; the wire value is `UNDECIDED` and `record.py` upper-cases
it.** ⚠ The opposite rule holds one call away — `find()` is case-INSENSITIVE and says so. Do not
generalise either.

⭐ **CHECK THE COMMAND WITH `--dry-run` BEFORE YOU RUN IT.** It posts the record to the ledger's
`validate` instead of `append` — pure, no write, and it names EVERY violation rather than the first.
Exit 0 it would be accepted, 1 it would be refused, 2 the ledger could not be asked. **This is how you
test a command; the live stream is not.** A probe verdict reading *"probe reason - do not use"* is in
the append-only stream today because nothing else existed to answer the question.

⚠ **`--run` is REQUIRED** (`V9` refuses a record with no run id) and **`--reason-file` is not
optional politeness**: the reason goes in a FILE because the `PreToolUse` hook denies any command
containing the blocked version-control token, arguments included.

⭐ **`--failing-file` IS THE POINT OF THIS GATE, NOT AN EXTRA.** Absent `failing`, a blocking
verdict indicts EVERY subject. **A 2-1 split over forty files is undecided about the ONE line the
panel split on and perfectly decided about the other thirty-nine** — say which, or the record
condemns thirty-nine files nobody disputed.

⛔ **WHAT IS AND IS NOT WIRED, as of 2026-09-06.** `copy_editor` **IS a registered verdict type**
(verified live at the ledger — **count it, do not quote it**; this line said 28 and the registry holds 29, which is the same freeze-a-number defect the briefs already name). ⚠ **This paragraph said the opposite until today and was
correct when written** — registration landed the same afternoon, which is exactly the far-side
staleness this project keeps filing. Re-check rather than trusting this line.

⚠ **IT IS REGISTERED, AND ADMISSION IS PER-ACTION — NOT ONE YES/NO.** Registering says a verdict
may be RECORDED; admission says it must be GREEN, and the admission SET differs by which action is
asking. **This paragraph said "absent from `admission.v1.json`" until today, as if one flag covered
every action, and that was already the wrong shape for how admission works here — Tim ruled
2026-09-26 that `copy_editor` gates every push, and the admission sets were changed accordingly.**
Re-derived live, 2026-09-27, call `gitRobot admission(action=...)` yourself rather than trusting
this line: at **commit**, `copy_editor` is `registered_not_admitted` — an `UNDECIDED` recorded there
does NOT block a bare commit. At **push** and at **tag**, `copy_editor` IS admitted — an `UNDECIDED`
recorded there **DOES block that push or tag.** The only existing `copy_editor` record in the ledger
right now is an `UNDECIDED`. **So: register, watch one panel, then admit was the old sequence; the
admit half already happened for push and tag, and a split you record today gates the release you are
trying to clear, not some future exercise.**

⚠ **THE ZERO IS REAL AND THE REASON FOR IT CHANGED.** This paragraph read *"`UNDECIDED` has 0
records in 2,170"* and drew a conclusion about restraint. Re-measured 2026-09-06 against the live
stream: still zero, out of 2,267 — **because no client could emit the value.** A count of zero was
evidence about the CLI, never about how often panels split. It is emittable now, so the next zero
will mean something different from this one.

**So on `DIVERGENT`: hand it to the carrier in full** with both claim-statements from Stage 2b.
⚠ **You do not record it yourself — that changed 2026-09-08 and the reason is above:** three
records at one basis meant first-writer-wins and your dissent would have been REFUSED, silently.
The carrier emits one agreement-shaped record carrying `passes`/`agreed`, so a 2-1 split is
preserved as a contested record rather than lost to whichever agent finished first. **This
paragraph read *"until admission lands, the carrier is what makes escalation happen — do not
describe it as fail-closed, because it is not yet"* until 2026-09-27; admission landed 2026-09-26,
one day earlier, and the paragraph had not caught up.** The carrier still carries the split to the
author (`D4`) — that half never depended on admission. What changed: an `UNDECIDED` recorded at
push or tag now blocks that push or tag on its own, mechanically, because `copy_editor` is admitted
there. Still do not call this "fail-closed" — a step with no record at all is `MISSING`, a status
distinct from `FAIL`/`UNDECIDED`, and admission does not turn silence into a block; it only means a
record that has run and split blocks. The gate is wired now; it is not fail-closed, and those are
different claims.

## Before you finish — your controls, and the step you could not justify

**Run both controls and report both, whatever they say.** These are recorded slices from a real arc; you are expected to get them right, and a run that misclassifies either has established nothing.

1. **Same meaning, different words** — editorial's `F1` and adversary's `O-3` independently derived and elaborated the same theorem in different language. **Correct: NOT a divergence.** Calling it one means you are behaving as a textual comparator.
2. **Close words, different meaning** — *"where the hypothesis fails so does the conclusion"*, textually near the requested fix, semantically a biconditional where the theorem is a conditional. **Correct: DIVERGENCE.** Calling it compliance means Stage 2 did not actually run.

**Then name your FIRST UNJUSTIFIED STEP** — not your weakest finding, but the first inference in your own reasoning you took without warrant. The answer is never "none", and a review reporting none has stopped looking at itself.

⚠ **Verify any control exists before naming it.** A brief citing a control that does not exist is worse than none: the agent reports it could not build the witness, and that reads as evidence of teeth.
