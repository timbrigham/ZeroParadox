**ISOLATION REQUIRED: Do not run this review inline. Use the Agent tool to spawn a fresh instance with no conversation context.**

Read `$ARGUMENTS` to determine the scope, then spawn an Agent using the Agent tool with `subagent_type` omitted (general-purpose). Pass the prompt below verbatim, substituting `ARGUMENTS_VALUE` for the actual value of `$ARGUMENTS`. The agent must have no knowledge of the current session.

---

## WHAT THIS IS, AND WHY IT IS NOT A GATE

`/editorial-review`, `/adversary-review` and `/prior-art-review` are all **CONFIRMATORY**: each takes a claim the framework already makes and tests it. That means **none of them can find a claim that was never made.**

Measured 2026-08-08:

```
1,338  theorems and lemmas in the corpus
   19  claims machine-mirrored in ClaimsMirror.lean
```

`ClaimsMirror.lean` runs claims → declarations. **Nothing runs declarations → claims.** A theorem that establishes something significant and was never written down is structurally invisible, and there are over thirteen hundred candidates. `tools/process/unstated-adjacency.md` names **unstated adjacency** — *"true theorems whose reach nobody recorded"* — as this corpus's characteristic defect, and its prescribed fix is *"the deliverable is a POINTER, not a new declaration."* (CLAUDE.md carries the rule as R-ADJACENT, wording the object "not a theorem".) This agent finds where those pointers are missing.

**It is GENERATIVE, not a gate.** It writes **no signal file**, returns **no PASS/FAIL**, and **blocks no push**. Its output is a ranked worklist. Do not wire it into `pre-push`.

## CALLER PRE-FLIGHT — do this BEFORE spawning; it is your job, not the agent's

**1. SCOPE IT. Never run this at `full` on a first outing.** 1,338 theorems will produce noise proportional to the ask. Pass a directory (`ZeroParadox/Valuation`), a file list, or a single `.lean` file. `python tools/verify/where.py "<topic>"` ranks folders by relevance and reports their token cost.

**2. GENERATE THE ELABORATED INPUT YOURSELF AND HAND IT OVER.** This is the load-bearing step and it is what makes the agent unprimed *structurally* rather than by instruction. For each module in scope:

```
lake env lean <path>.lean 2>&1 | Out-File -FilePath <scratch>\<name>.sig.txt -Encoding utf8
```

**Any DECLARATION** not `#check`ed emits nothing useful, so generate a probe that imports the module and `#check`s **every declaration in it**. ⚠ The unit is the DECLARATION, not the file: a module carrying one `#check` and eighteen bare declarations does not trigger a per-file test, and those eighteen are exactly the general lemmas this agent exists to find. ⚠⚠ `#print axioms` output from `build.log` is a **SUPPLEMENT, never a substitute** — it carries a name and a footprint and **no type at all**, and phase 1 clusters by TYPE, so a scope fed only from `build.log` reads as fully populated while containing nothing this agent can read. **Tell the agent which files you generated and where — AND hand it the LIST OF DECLARATION
NAMES you enumerated, never a count.**

⚠⚠ **A COUNT IS THE WRONG INSTRUMENT, MEASURED: three of them have failed here, each in a
different direction.** A module-level comparison was blind to a module delivered one declaration
deep. A denominator drawn from the same enumeration as the numerator could never differ from it. And
a regex denominator matched ordinary ENGLISH at the head of wrapped docstring lines — `theorem`,
`lemma`, `instance` and `axiom` are all English words — returning **12 for a module holding 9** and
**2 for a module holding none**, so a caller who delivered every declaration could trip a guard that
then announced the sample was incomplete.

**A NAME cannot do any of that.** A prose false positive shows up as a string a reader can see is not
an identifier; in a count it is an invisible +1. ⚠ **That defence is partial, so do not lean on it:**
`ZeroParadox.towerNONote._proof_2` is a well-formed, `#check`able identifier carrying nothing
claimable, so "the reader will see the garbage" filters PROSE noise and not GENERATED noise — and the
enumeration below **does not** remove the generated kind either. What it removes is the guesswork
about where the names came from.

**THE ENUMERATION METHOD — run this, do not hand-roll a regex.** Twelve lines, no source parse, and
it returns names AND types in one pass.

⚠⚠ **IT COMPUTES THE `NON_INTERNAL` COLUMN, NOT THE AUTHORED ONE.** Measured 2026-09-04 by running
it: `Kruskal` → **57**, `Gentzen` → **32** — the middle column below, not the authored 28 / 30.
`isInternalDetail` drops what Lean marks as an internal detail and **does not** drop the
auto-generated siblings: the `Gentzen` name list it prints still contains `NONote.oadd.congr_simp`
and `ZeroParadox.towerNONote.eq_def`. Reaching the authored column needs a further filter on those
suffixes, which this probe does not implement. **Hand over the non-internal reading and SAY SO.**

⚠ **CONTROL — run it on `Kruskal` and expect 57.** An earlier revision cited `Epsilon0MinMax → 2` as
its check; all three populations equal 2 there, so that control could never separate them and would
have passed whichever column the probe computed. Use a module where the columns differ, or you are
not testing the thing the label claims.

```lean
import <the module>            -- and Mathlib.Tactic
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modName : Name := `<the module>
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleFor? n == some modName && !n.isInternalDetail then
      names := names.push n
  logInfo m!"AUTHORED in {modName}: {names.size}"
  for n in names do
    match env.find? n with
    | some ci => logInfo m!"{n} : {ci.type}"
    | none    => pure ()
```

⚠⚠ **STATE WHICH POPULATION YOU HANDED OVER, because the defensible readings differ by up to 2.6x.**
Every-constant / non-internal / authored gave `Gentzen` 65 · 32 · 30 and `Kruskal` 74 · 57 · 28, with
nobody making an error. The probe above is the **non-internal** reading; dropping `!n.isInternalDetail`
gives every-constant (74 / 65). Whichever you run, **name it** — the label is the whole point of this
paragraph, and getting it wrong mislabels the sample by a factor of two.

If you did not enumerate by name, **say so plainly** — the agent's job is then to scope its answer,
not to guess a denominator.

**3. Do NOT hand it the docstrings, CLAIMS.md, the README, or the PDFs at the start.** It reads those only in phase 3, to compute the diff. Handing them over early makes it confirmatory again, which is the one thing this agent exists not to be.


---

Spawn the Agent with this prompt (substitute ARGUMENTS_VALUE for the actual value of $ARGUMENTS):

---
## HARD CONSTRAINTS

**READ-ONLY on the working tree.** Do NOT modify, create, or delete any repo file, with exactly one exception: the findings note under `.claude-local/notes/`. **No signal file** — this is not a gate.

**NO SCRATCH FILES IN THE REPO.** Probes go in the session scratchpad directory named in the environment, never under `ZeroParadox/`, and are deleted after.

**Do not cite a private path in anything reader-facing.** `.claude-local/` is gitignored.

⚠ **Tool traps, all measured:** `Select-String -Path "<dir>\**\*.lean"` silently under-matches deep trees — use ripgrep. A Mathlib declaration may be **generated by an attribute and have no source line at all**, so `#check` is the authority over grep. `python -c` in the Bash tool eats backticks. `| Select-Object -First N` breaks the pipe and reports a wrong exit code.

You are a mathematician who has just found this repository. You do not know the authors, you have not read their prose, and you have no reason to accept their account of what they have done. **You have been handed the elaborated Lean output and nothing else.** Your job is to work out what this corpus actually proves, in your own words, and then — only at the end — compare that against what its authors say it proves.

Working directory: use the current project root. Scope: **ARGUMENTS_VALUE**.

⚠⚠ **BEFORE ANYTHING ELSE, CHECK YOUR SAMPLE.** Your output is a NEGATIVE — a report that some set of declarations holds nothing further worth claiming — and **a negative is quantified over its SAMPLE, never over the scope you were asked about.** (The unscoped phrasings of that sentence are denylisted at the end of this brief; this one is written the way you are required to write yours.) Two states stop you before you begin, and they have different remedies:

- **Nothing reached you.** No signature files, or empty ones. **STOP AND ERROR**: report
  `NO SIGNATURES DELIVERED — refusing to reconstruct`, claim nothing, **write no note and save
  nothing**, and ask the caller to re-run pre-flight and name the files. (This agent records no
  verdict in any state, so the note is the only artifact there is to withhold.) An empty scope is
  not an empty corpus.
- **They reached you and carry no TYPES.** `#print axioms` output is a name and a footprint and
  no type; phase 1 clusters by type. **STOP AND ERROR**: report
  `SIGNATURES CARRY NO TYPES — refusing to reconstruct`, **write no note and save nothing** (as
  above, the note is the only artifact this agent has to withhold), and ask the caller for `#check`
  probes.

If they reached you and are merely SPARSE, proceed — the closing obligation of this brief is what
scopes the negative to what you actually received. It is unconditional wording, not a threshold.

## The one rule that makes this worth doing

**Phases 1 and 2 are conducted WITHOUT reading docstrings, comments, `CLAIMS.md`, `README.md`, `BOTTOMELEMENT.md`, `SNAP.md`, or any PDF or build script.** You have signature files; use those. If you read the framework's framing before forming your own, you will reconstruct their claims instead of the corpus's content, and the exercise is worthless. **Say explicitly in your report whether you held to this**, and name anything you read early and why.

You may read Mathlib freely — it is not the framework's account of itself.

## Phase 1 — read the mathematics

From the elaborated signatures alone:

1. **Group by what is actually being said**, not by file or directory. Elaborated types cluster by shape; let them.
2. **For each cluster, write one sentence** of standard mathematical English stating what is established. Use the target field's vocabulary, not any vocabulary you find in identifier names — an identifier is the authors' framing leaking in.
3. **Rank each result by generality.** A theorem over `σ → Option σ` covers every Mathlib Turing machine; a theorem over one concrete carrier covers one carrier. **Generality is the strongest signal that a result is under-claimed**, because a general theorem is usually stated for the one instance its author cared about.
4. **Note the axiom footprint** where you have it. Axiom-free and choice-free results are the corpus's headline property, so a choice-free result nobody has pointed at is a strong candidate.

## Phase 2 — find what is worth claiming, and try to kill each candidate

For every candidate result, **before it goes in the report**, apply these three gauges. A candidate that fails any of them is not a finding.

- **(a) THE DECORATIVE GAUGE.** Delete all framework-specific vocabulary from your sentence. If nothing specific is lost, it is a label, not a result. **REJECT.**
- **(b) NAME A NON-INSTANCE.** State something that does NOT satisfy the hypothesis, or an adjacent structure where the conclusion fails. *"If you cannot say what would break it, you do not understand the claim."* A candidate with no non-instance is either trivially true or you have not understood it. **REJECT or investigate.**
- **(c) SAY WHAT IT EXCLUDES.** A result that excludes nothing is vacuous even when every step is valid. If the statement holds of an arbitrary type, say so — **build the witness and run it**, do not reason about it. A statement true of `Bool` says nothing about any particular object.

⚠ **Gauge (c) has caught a BEDROCK defect in this corpus.** A `Reading:` claimed a theorem showed two faces of an object coincide; `example (α : Type) : Subsingleton (α ≃ PUnit) := inferInstance` elaborates, so the theorem holds of every type and said nothing. **Settle genericity by elaboration, never by argument.**

**Your own failure mode is OVER-claiming.** You will be tempted to report every theorem as a finding. Thirteen hundred findings is worse than none. Report what survives all three gauges, ranked, and say how many candidates you rejected and why — the rejection count is evidence you applied them.

## Phase 3 — NOW read their account, and diff

Only now read `CLAIMS.md`, `ZeroParadox/ClaimsMirror.lean`, the relevant docstrings, `BOTTOMELEMENT.md`, `SNAP.md` and the `CannotBe` index files. Produce three diffs:

**DIFF 1 — claimed but not backed.** A claim whose named declaration does not state it. `ClaimsMirror.lean` already covers 19 claims this way; you are checking the rest. *(Existing gates partly cover this. Report briefly.)*

**DIFF 2 — PROVED BUT NEVER CLAIMED. This is the point of the exercise.** A result that survived phase 2 and appears in no claim, no index, and no docstring that a reader would reach. For each: name the declaration, state the claim in the target field's terms, and say **where the pointer should go** — the site a reader lands on when they ask the question it answers, not five sections away.

**DIFF 3 — reach understated.** The declaration proves something strictly more general than anything anyone has written about it. Give the general statement, the narrower one currently recorded, and the delta. **This is the unstated-adjacency class and it is the corpus's named recurring defect.**

## What NOT to report

- A result the corpus already points at from a place a reader lands on. Check before reporting: `CLAIMS.md`, the `CannotBe` indexes, `BOTTOMELEMENT.md`, `SNAP.md`, and the declaring file's own header.
- An elementary instantiation of something already stated. `tools/process/prior-art.md` § "Trigger 0 — the measured cases" records that adding those is a recurring failure, not a contribution.
- Anything you cannot name a declaration for. **Every finding must be falsifiable by `#check <name>`.**
- Prior-art questions. If a result looks like it belongs to a known program, say so in one line and route it to `/prior-art-review`; do not search the literature yourself.

## Output

```
## Reconstruction — YYYY-MM-DD
### Scope: [what was in scope]
### Received: [N declarations across M modules — every one NAMED under "What reached me"]
### Population: [which enumeration you were handed — every-constant / non-internal / authored,
                 or "not stated"]
### Sample provenance: [the caller's own words for how the probe was enumerated, or "not stated"]
### Not received: [the set difference, if a declaration NAME LIST was supplied; else
                   "no name list supplied, so what is missing is unknown"]
### Modules in scope that sent nothing: [glob the scope, subtract the modules you received a
                 signature from, NAME the remainder; or "none — every module in scope reported"]
### Unprimed: [held / broken, and what you read early]

## What this corpus proves, in my words
[the clusters from phase 1, most general first, each one sentence]

## DIFF 2 — proved but never claimed   [THE HEADLINE]
[per finding: declaration · the claim in the field's terms · where the pointer belongs
 · the non-instance · what it excludes]

## DIFF 3 — reach understated
[per finding: declaration · what is proved · what is recorded · the delta]

## DIFF 1 — claimed but not backed
[brief]

## Rejected candidates
[how many, and the gauge each failed - this is evidence the gauges were applied]

## What reached me
[every declaration name you received a signature for, grouped by module. This is the
 evidence for the scoping sentence above, and it is not optional.]
```

Save to `.claude-local/notes/reconstruction_YYYY-MM-DD_<scope>.md`. State the filename at the end — **unless you stopped at one of the two refusals above, in which case save nothing.**

⚠⚠ **YOUR ANSWER IS A NEGATIVE, AND IT IS SCOPED TO WHAT YOU RECEIVED — ALWAYS, WITH NO THRESHOLD.** There is no count to compare and no fence to trip. Every numeric version of this guard failed: twice by staying silent when it should have fired, once by firing on a COMPLETE delivery and calling that a certainty. **So the obligation is unconditional, and it is about wording:**

- **NEVER write "in this scope", "nothing here is unclaimed", or "full coverage".** Write **"in the `N` declarations I received"** — and **LIST THEM BY NAME**. You hold the signatures, so the list is free and exact. ⚠ **What cannot be miscounted is the LIST, not `N`.** `N` is the size of whatever population the caller enumerated, and the defensible populations differ: measured over four modules, every-constant / non-internal / authored give `Gentzen` 65 · 32 · 30 and `Kruskal` 74 · 57 · 28, a factor of 2.6, with nobody making an error. **So state which population you received** (§2 names one), and let the names carry the scoping rather than the number.
- **Print the MODULE leg too.** *Modules in scope that sent nothing:* glob the scope, subtract the modules you received a signature from, and NAME the remainder. Like the declaration list this one is free and exact, it needs no denominator, no threshold and no caller cooperation — and it is the only thing that scopes the negative to the SCOPE rather than to the declarations you happened to be handed.
- **State where the sample came from**, in the caller's own words, or write *"not stated"*. That is not an apology — it is the reader's only handle on what the negative is worth.
- **If you were handed a declaration NAME LIST, print the SET DIFFERENCE**: received, and not received. A name diff cannot over- or under-count. ⚠ It is still not a licence to write "complete" — a list you were handed is the caller's claim, not your measurement. ⚠⚠ **A name that is not a well-formed identifier is a defect in the LIST, not a missing declaration — say so rather than reporting it as not received.** And a well-formed identifier is not automatically claimable content: `ZeroParadox.towerNONote._proof_2` `#check`s cleanly and carries nothing worth claiming, so "a reader can see it is garbage" is not a filter you may rely on.

**A negative over a small sample is not a defect; an UNSCOPED negative is.** *"Everything worth claiming in the `N` declarations I received, named below, is already claimed"* is a real result and a useful one. *"Everything worth claiming here is already claimed"* is the same sentence with the evidence deleted.

This agent gates nothing and writes no signal, so nothing is bypassed. The harm is a confident negative that sends the next person to scope elsewhere. ⚠ **Naming the declarations does not by itself prevent that**, and an earlier revision claimed it did: naming them pins the INNER coordinate — *scoped to these declarations* — while the `Scope:` header re-asserts the OUTER one at full width. The implication runs one way and the converse needs the MODULE set, which is why the module leg above is not optional.

**No signal file. No verdict.** If the honest answer is *"everything worth claiming in the `N` declarations I received, named below, is already claimed"*, say that plainly — with the `N` and with the names, exactly as modelled above — it is a real result, and naming what you did NOT see is what lets the next person scope the rest.
