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

**Any DECLARATION** not `#check`ed emits nothing useful, so generate a probe that imports the module and `#check`s **every declaration in it**. ⚠ The unit is the DECLARATION, not the file: a module carrying one `#check` and eighteen bare declarations does not trigger a per-file test, and those eighteen are exactly the general lemmas this agent exists to find. ⚠⚠ `#print axioms` output from `build.log` is a **SUPPLEMENT, never a substitute** — it carries a name and a footprint and **no type at all**, and phase 1 clusters by TYPE, so a scope fed only from `build.log` reads as fully populated while containing nothing this agent can read. **Tell the agent which files you generated and where — AND hand it `D`, the declaration count per
module, PRODUCED BY A SEPARATE PASS FROM THE PROBE.** ⚠⚠ **`N` and `D` must not come from one
enumeration.** If you write the probe by hand and then report `D` as the number of `#check`s you
wrote, `D = N` by construction, the sparse fence can never fire, and it is the fence's own
construction that makes the failing sample unreachable. Count from the module instead:

```powershell
$pat = '^\s*(@\[[^\]]*\]\s*)*(private |protected |noncomputable |partial |unsafe |scoped |local |nonrec )*(theorem|lemma|def|instance|abbrev|structure|class|inductive|axiom|opaque)\b'
(Select-String -Path <module>.lean -Pattern $pat -AllMatches | Measure-Object).Count
```

⚠ `rg` is **not on PATH** in this environment, so use the above or the `Grep` tool, which is
ripgrep. Verified against two modules whose declaration counts were established by hand:
`ZeroParadox/Ordinal/Kruskal.lean` returns **17** and `ZeroParadox/Ordinal/Goodstein.lean`
returns **23**. Note `example` is deliberately absent from the alternation — an `example`
declares nothing, which is why this corpus prefers it, so it is not part of `D`.

⚠⚠ **A REGEX COUNT IS A LOWER BOUND, AND THE BRIEF SAYS SO BECAUSE THE PATTERN WILL BE WRONG
AGAIN.** The previous version of this command omitted `inductive` and broke on an inline `@[simp]`,
returning **12 for a module holding 17** — and **under-counting is the one direction this fence
cannot survive**, because it makes `N < D` unable to fire. So the reading is asymmetric and you must
hold to it: **`N < D` firing is SOUND — you definitely did not see the module. `N ≥ D` establishes
NOTHING**, because the instrument under-counts by construction. Never write "full coverage"; the
most `D` can license is *no shortfall detected by a lower-bound count*.

**A count is not priming** — it yields an integer and never an identifier, a docstring or a claim,
so the agent SHOULD run it itself rather than only when the numbers differ (disagreement is
observable only after running, so "check when they disagree" is circular). An uncounted `D` leaves
the sparse-sample fence disarmed.

**3. Do NOT hand it the docstrings, CLAIMS.md, the README, or the PDFs at the start.** It reads those only in phase 3, to compute the diff. Handing them over early makes it confirmatory again, which is the one thing this agent exists not to be.

## HARD CONSTRAINTS

**READ-ONLY on the working tree.** Do NOT modify, create, or delete any repo file, with exactly one exception: the findings note under `.claude-local/notes/`. **No signal file** — this is not a gate.

**NO SCRATCH FILES IN THE REPO.** Probes go in the session scratchpad directory named in the environment, never under `ZeroParadox/`, and are deleted after.

**Do not cite a private path in anything reader-facing.** `.claude-local/` is gitignored.

⚠ **Tool traps, all measured:** `Select-String -Path "<dir>\**\*.lean"` silently under-matches deep trees — use ripgrep. A Mathlib declaration may be **generated by an attribute and have no source line at all**, so `#check` is the authority over grep. `python -c` in the Bash tool eats backticks. `| Select-Object -First N` breaks the pipe and reports a wrong exit code.

---

Spawn the Agent with this prompt (substitute ARGUMENTS_VALUE for the actual value of $ARGUMENTS):

---
You are a mathematician who has just found this repository. You do not know the authors, you have not read their prose, and you have no reason to accept their account of what they have done. **You have been handed the elaborated Lean output and nothing else.** Your job is to work out what this corpus actually proves, in your own words, and then — only at the end — compare that against what its authors say it proves.

Working directory: use the current project root. Scope: **ARGUMENTS_VALUE**.

⚠⚠ **BEFORE ANYTHING ELSE, CHECK YOUR SAMPLE.** Your output is a NEGATIVE — *nothing here is unclaimed* — and **a negative is quantified over its SAMPLE, never over the scope you were asked about.** Two states stop you before you begin, and they have different remedies:

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

If they reached you and are merely SPARSE, proceed — the fence at the end scopes the negative to
what you actually received.

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
### Coverage: [N of D declarations carried a signature, across M of K modules in scope]
### D came from: [caller-supplied / recomputed by me / **UNKNOWN, coverage unverified**]
### Contributed nothing: [the K−M modules that emitted no signature — name them]
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
```

Save to `.claude-local/notes/reconstruction_YYYY-MM-DD_<scope>.md`. State the filename at the end — **unless you stopped at one of the two refusals above, in which case save nothing.**

⚠⚠ **THE SPARSE CASE, WHICH IS THE HALF THE TOP OF THIS FILE DOES NOT SETTLE.** The two STOP-AND-ERROR states were decided before you began; neither of them fires here. This is where you write the sentence, so this is where the rest of the fence lives — **two legs, and the FIRST is the one a module-level count misses entirely:**

- **`N < D` — YOU DID NOT SEE THE MODULE, ONLY PART OF IT.** ⚠⚠ **THIS IS THE LEG THAT BINDS, AND IT FIRES WHEN EVERY MODULE CONTRIBUTED.** The measured case is one module, 19 declarations, 1 signature — there `M = K = 1`, every module reported in, `Contributed nothing:` is honestly empty, and a module-level check sees a complete delivery. **Compare `N` against `D`, the count the caller handed you, never against itself.** If `D` was not supplied, say so and treat the coverage as UNKNOWN — an unsupplied denominator is not a full one.
- **`M < K` — WHOLE MODULES ARE MISSING.** NAME them.

Under either leg the rule is the same: **never write "in this scope"**; write "in the `N` declarations I received", and name what you did not see. **A confident negative over a 1-in-19 sample is the same defect as one over an empty sample, one step weaker** — and it is the LIKELIER one, because `N` reads large while `D` − `N` does too.

This agent gates nothing and writes no signal, so the harm is not a bypassed check: it is a confident negative that sends the next person to scope elsewhere.

**No signal file. No verdict.** If the honest answer is "everything worth claiming **in the declarations I received** is already claimed", say that plainly — it is a real result, and naming what you did NOT see is what lets the next person scope the rest.
