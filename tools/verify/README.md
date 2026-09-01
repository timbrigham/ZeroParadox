# tools/verify — the verification suite, and what each checker enforces

The checkers in this repository that gate every commit and push. Like `tools/registry/` (the
declaration extractor), `tools/render/` (the diagram generators) and `scripts/` (the PDF build),
this folder exists so the provenance of a claim is inspectable — here, the claim is *"this corpus
was checked"*. You can read exactly what is checked, run it yourself, and see what is deliberately
**not** checked.

⚠ **Unlike its sibling folders, this is not a source-visibility COPY. It is the working code**,
tracked in place since 2026-08-15. There is no private original: the file you are reading is the
file that runs. That was the point of moving it — a gate whose source nobody can see is an
assertion rather than evidence, and a copy of a gate is a copy that can drift from the gate.

They are **blocking gates, not advice.** What follows is the argument behind each: what it detects,
the defect it exists to stop, and the measurement that justified building a checker rather than
writing another convention.

**Why this text is here and not in `CLAUDE.md`.** It was four sections of the operating manual,
injected into every session and every subagent. Each is already enforced by a checker that BLOCKS
at push — **the gate fires whether or not anyone reads the argument** — so the argument does not
need to be in context to work. `CLAUDE.md` keeps the rule, the trigger, a one-line *why* and a
pointer here. Same pattern as the `CannotBe` indexes: delivery is a trigger in the injected file
naming a specific path, not injection of the content.

⚠ **Only gate-enforced sections moved.** A neighbouring section on control objects stayed in
`CLAUDE.md` precisely because nothing enforces it — an unenforced rule outside the firing zone is a
rule that stops working. Enforcement is the criterion, not adjacency.

**Lifted from `CLAUDE.md` on 2026-08-15, near-verbatim.** These sections carry measured history
— dates, and the specific defect each rule was built against — which a summary would lose.

⚠ **The first version of this line said "nothing below was rewritten", and that was wrong
within hours.** Moving the text verbatim was meant to avoid drift; what it actually did was
import figures that had ALREADY drifted — a recorded baseline count here disagreed with the
baseline file in this same directory, and CI publishes both, one click apart. An adversary
pass caught it. The stale counts are now removed in favour of running the checker, or dated
where they are historical measurements. **Verbatim is not a defence against staleness when
the source was already stale.**

| checker | mode | enforces |
|---|---|---|
| `check_pov.py` | **BLOCK** at commit and at push | a POV claim declares its KIND and STATUS; a DENIAL is never allowed |
| `check_modal.py` | **BLOCK** at commit and at push | a modal claim carries a measurement or a reduction |
| `check_classes.py` | **BLOCK** at commit and at push | a new requirements class records a degeneracy verdict |
| `check_prose.py` | **BLOCK** at commit and at push | prose caps: block size, docstring vs declaration, gloss labels |
| `guards.py` | **BLOCK** at push | every enumerated ROUTE to a guarded property still behaves |

Each prints its own invocation path; run with no arguments for a report.

---

## The type registry and the policy live HERE, and the ledger reads them from here.

`required.v2.json` and `policy.v1.json` sit in this directory, and the verdict ledger LIVE-READS
both from the working tree — `ZPLEDGER_CONFIG` points at `tools/verify/`. Moved back 2026-08-25 by
Tim's decision: the bar belongs in the history it gates, where the prose gates and the checkers can
see it disagree with `CLAUDE.md`. While they lived in the ledger's own tree, nothing in this
repository could.

⚠ **THE RULE THAT SURVIVED THE MOVE IS "ONE COPY", NOT "NOT HERE".** Two copies make every
inventory wrong in the most convincing way available — both sides internally consistent,
disagreeing about what *complete* means. There is exactly one copy and it is this one.

⚠⚠ **EDIT THESE THE WAY YOU EDIT A LIVE GATE, BECAUSE THEY NOW ARE ONE.** There is no restart
between the edit and the gate using it. A malformed edit does not fail loudly at deploy — it makes
the config UNLOADABLE, and an unloadable config serves UNDECIDED and refuses every commit and push.
Load, modify and re-parse in one script rather than hand-editing JSON.

**It had already happened.** When the copies were removed the ledger served 24 types while the
local file carried 22, missing `rely` and `claim_review`; the served `policy_sha` (`8c85b6c0`)
matched neither the raw nor any canonical hash of the local policy. The drift arrived by
reconfiguration — nobody decided it — which is exactly why a mirror plus a discipline is worse
than one file.

- **Ask the ledger:** `requirements(action=...)` for the registry, `policy()` for the thresholds.
- **Review a change to the bar:** it is a tracked, public diff in the MCP server repository under
  `verdictLedger/config/`, each commit carrying its reason. What was lost here is *proximity*,
  never reviewability — and the fix for proximity is this pointer, not a second file.

`admission.v1.json` REMAINS, and it is a copy of neither: the registry says what may be
**recorded**, the admission set says what must be green to let an action **through**. Two facts,
two lifecycles — registering a type is free, promoting one to gate a push is deliberate.

---

## ⭐⭐ THE GATE CANNOT CERTIFY THE THING IT IS MADE OF. Three measured instances, 2026-08-23.

**A verification layer can check the corpus. It cannot cleanly check itself, and every attempt so
far has failed in a *different* way.** This is not a counsel of despair — each instance had an
honest resolution — but the shape recurs, and someone meeting it for the first time will reach for
the fix that makes it worse.

| # | the gate | what it could not certify | resolution |
|---|---|---|---|
| 1 | `guards` | **its own inputs.** Two of its seven live in `.claude-local`, a different repository, so they can never be subjects of a record here. `rely_cleared.txt` can be edited, its verdict changes, and no subject moves | left **unscoped and under-covered** — 4 of 477 — because under-covered-and-true beats fully-covered-and-false. A scope cannot close it; only making `rely` a record instead of a file can |
| 2 | `rely` | **anything, at the breadth its bar demanded.** Its brief forbids running at `full`; the admission set required exactly that breadth. The brief and the bar contradicted each other, so no amount of running it could ever have closed the key | scoped to `tools/verify/*`. **Unsatisfiable by construction** is its own class — a refusal no work can answer |
| 3 | the recording path | **the review that found its own defects.** `/rely` found two fail-opens *in the recording path*; fixing them changed `tools/verify`, and the fence then refused a record naming the tree the reviewer had read | none. **The round's verdict is unrecordable and `rely` stays MISSING** — see the ordering rule below |

⚠ **THE REFLEX TO RESIST, in each case, is the one that closes the hole by making the gate lie.**
Scoping `guards` to `tools/verify/**` would zero its `subjects_unexamined` by dropping the corpus
paths it plants violations in. A `--force-ref` escape would let instance 3 record — and would be the
one fail-open with a reviewer's signature on it. **Prefer a gate that is visibly short over one that
reads complete because it stopped asking.**

### RECORD, THEN FIX. The other order is not bad practice — it is unrepresentable.

**A review round's verdict must be recorded BEFORE its findings are fixed.** Run → record at HEAD
with the verdict as found → *then* fix, which correctly stales the record for exactly the files that
changed and leaves the rest covered.

**Why it is not a matter of discipline:** `common.ledger_subjects` refuses any basis it cannot fence
(only `HEAD` and the index can correspond to what a checker read from the worktree). Once the tree
moves, the bytes the reviewer examined exist nowhere the fence can reach, so the record cannot be
written at all. Measured 2026-08-23: `/rely` examined one commit, its fixes landed in the next, and
the verdict became unrecordable in between.

⚠ **And re-running is not a free repair when the fixes are inside the gate's own scope.** `CLAUDE.md`
measures four `/rely` passes on `tools/verify` at **10 → 4 → 6 → 9** findings, never quiescing,
because each pass reviews code written in response to the last. A second pass after a repair
measures **the repair**, not the layer.

### ⚠ A repair that satisfies the checker while deleting what the checker was protecting

**A distinct defect class, and the most dangerous kind found this session, because nothing is absent
and nothing is silent.** The checker runs, passes, and reports honestly — on a property that has
quietly become smaller.

**The measured near-miss:** six checkers already declared a *baseline* switch when the vendored
allowlist had to be added. Writing the allowlist **over** the baseline would have removed the
earlier protection while adding the new one — **and every record would still have validated**,
because the rule asserts that *declared* switches are *named by a record*; it says nothing about
whether a previously-declared switch still exists. Caught by appending rather than replacing, and
pinned by a test carrying the full map of every type's declarations.

**The general form: a validator that checks a set is COVERED cannot notice the set SHRINKING.**
Wherever a check is keyed to a declaration, the declaration itself needs a separate pin.

---

## Point-of-view claims: declare the KIND and the STATUS. Gate-enforced.

**"Point of view" / "chart" / "frame" was doing FIVE different jobs with one word.** The cost, measured
2026-07-30: a full day of gate rounds, two bedrock findings, and a correction that itself over-corrected
into *denying* the framework's own thesis. The sequence is worth keeping because both halves are traps:

1. `snap_is_frameflip` was cited as proving the snap **is** a change of frame. Its statement contains no
   snap. Witness-vs-statement defect.
2. The fix then wrote *"the POLE EXCHANGE (**NOT** of the snap)"* into a dozen sites — which **denies** a
   reading that is well-motivated and is ZP-Q's stated conjecture. Over-correction, and the same class as
   `feedback_triage_review_vs_grounded_figures`: a review pass gutting a grounded claim.

**Neither is possible if every POV claim declares WHICH KIND it is and WHETHER IT IS PROVED.**

**THE FIVE KINDS** — genuinely different phenomena, previously all called "chart":

| KIND | means | example witness |
|---|---|---|
| **COINCIDENCE** | both readings hold of ONE object **simultaneously** | `selfloop_is_zero_and_infinity`; `epsilon0_min_eq_max`; `catseam_is_frameflip` |
| **INVERSION** | a map **exchanges** the readings; always an involution | `rInv_swaps`, `swap_involutive`, `flipPoles_involutive` |
| **DRIFT** | two measures run **opposite** along one sequence | `pole_inversion` (element descends, complexity ascends) |
| **CARRIER** | the claim's **truth value** depends which carrier you are in | snap available in ℚ₂, impossible in ℝ — both completions of ℚ (Ostrowski) |
| **INVARIANT** | the quantity **does not transform**; flipping the chart gains nothing | measure-zero-ness, cardinality |

**THE STATUS — folded into the EXISTING `Statement:` / `Reading:` labels. This adds no new label:**
- **`Statement:` + KIND** — the theorem proves it. Name the witness.
- **`Reading:` + KIND** — the framework reads X as an instance of that kind. Conjectural.

**ONE THEOREM MAY CARRY TWO KINDS — write one `Statement:` line per KIND it actually proves.** A bundle
carrying two is the **normal case for a self-dual object**, not an exception. `catseam_is_frameflip` is the
worked example: (i) and (ii) say the seam is initial AND terminal — **COINCIDENCE** — while (iii) says `op`
exchanges those characterisations and fixes the seam — **INVERSION**. Being both is exactly what makes it
self-dual; either label alone is a mischaracterisation. **Measured 2026-07-30, one commit after this table
was written:** the gloss went in tagged INVERSION only, disagreeing with the COINCIDENCE entry in this very
table, and the prior-art gate caught it. The convention as first drafted implied one KIND per claim, and the
mislabel followed immediately.

**There is deliberately NO slot for denying a reading.** That is what makes trap 2 unwriteable. If a
theorem does not establish an identification, say `Reading:` and mark it conjectural — never "NOT the snap".

**And the DENIAL is checked directly, not inferred from a missing tag.** Measured 2026-07-30: the tag-check
passed at **zero** new untagged claims while **seven** denial sites sat live in the corpus, and the editorial
gate had to find four of them by eye. A denial is wrong regardless of how it is tagged, so `check_pov.py`
carries a `DENIAL` pattern checked **unconditionally and never baselined**. **The generalizable lesson, which
applies to every gate this project writes:** a convention with a *forbidden form* must detect the forbidden
form itself — detecting only the *absence of the required form* leaves the violation invisible.

**Enforcement is MECHANICAL, because this is the FOURTH convention of this shape and the previous three
all leak.** (`vocabulary_reference.md`: the bare-"bottom" rule, "iterative bottoms", standard-math-first.)
`feedback_jargon_blindspot` records why: Claude is embedded in the project's language and structurally
cannot self-detect vocabulary drift, so discipline-level rules fail here by construction.
- `python tools/verify/check_pov.py --block` — **BLOCKS AT BOTH STAGES.** `pre-commit` runs it
  (with the other three) via `hooks.py`, and `pre-push` § 3b runs it again. Install the hooks with
  `python tools/verify/install_hooks.py`; `--check` reports whether the gates are actually armed,
  which is a different question from whether the checks passed. **`hooks.py` is the authority on
  enforcement mode, not this file** — its `PRE_COMMIT_PLAN` is printed to the operator on every
  commit, so the mode is visible at the moment it applies and cannot drift from the code the way a
  sentence here can. ⚠ This paragraph described a warn-only commit gate until 2026-08-15, six days
  after the behaviour changed.
- Validated end-to-end, twice, by planting each checker's own must-fire text and running the real
  hook: commit → exit 1, `Commit blocked — NEW violations in: check_pov.py`; push → exit 1.
  ⚠ A hand-written violation is NOT a control — it is not a shape the checker detects, and two
  separate reviewers reached the opposite (wrong) conclusion from one before re-running with the
  checker's own text.
- **Baselined.** The corpus carries a baselined set of untagged sites; `check_pov.py` prints the current figure on every run. (A recorded count here disagreed with `pov_baseline.txt` beside it.) Demanding a tag on all of
  them is a migration, not a gate, and a gate that blocks everything on day one gets muted. So
  `tools/verify/pov_baseline.txt` grandfathers them and the gate blocks on **NEW** sites only —
  as-touched rollout, same as the file-path and CC-2 conventions. **Shrink the baseline as files are
  touched; never grow it deliberately.**

**Do not flag the intentional collisions.** `project_notation_notes`: the ⊥ / ε₀ / P₀ overloads are
deliberate. The checker allowlists them, and anything that starts crying wolf must be narrowed, not
tolerated — a muted gate is worse than none.

## A requirements class is only informative if something FAILS to be a member. Gate-enforced.

**Measured 2026-08-07: five of the seventeen requirements classes then in the corpus were degenerate or bundled a commitment as data. That is one
design habit, not five incidents** — writing a class without asking what it EXCLUDES:

| class | verdict |
|---|---|
| `WheelValuationStructure` | constant-`⊤` valuation satisfies every field on any commutative ring → `WVSNondegenerate` added |
| `AbstractSelfApp` | `trivialSelfApp` inhabits it, so *"L carries it, therefore…"* is vacuous |
| `InfinitudeFloor` | characterised 2026-08-07 as **exactly** `Infinite α` — nothing more |
| `SeparatedSuccession` | `Unit` + the always-true relation discharges every field (2026-08-07) |
| `KleeneStructure` | bundles a `Code` (data) with the assertion that it names ⊥ (commitment) |

**⚠ THIS IS NOT A NEW RULE — IT IS TIM'S OWN 2026-06-29 NO-GO GAUGES, FINALLY ENFORCED AND FINALLY
POINTED AT THE RIGHT OBJECT.** `.claude-local/notes/nogo_gauges_2026-06-29.md` already specifies
**gauge 1, the decorative check** (*"delete all framework vocabulary; if nothing specific is lost, the
entry is a label. REJECT"*), **gauge 4, the vacuity check** (*"if every confirmed edge is tier-1
generic, the dictionary is true-but-empty"*), and **discipline (b): NAME the obstruction in advance —
"if you can't say what would break it, you don't understand the claim."** That is *name a non-member*,
written 40 days before this section.

**Why it never fired:** the gauges were scoped to **dictionary transport edges**, nobody pointed them
at **requirements classes**, and they lived in a memory body plus a note rather than here — exactly the
failure this file names in its own words, *memory is for context, not enforcement*. Fifty files carry
NO-GO text, so it was applied wherever someone remembered. As of that same 2026-08-07 audit, most classes had never been asked the question at all. (The two counts in this section were taken on the same day and differ by one; both are dated rather than corrected, because a survey result is a measurement at a moment, not a standing claim.)

**The check is mechanical and cheap: BUILD THE TRIVIAL WITNESS, or prove you cannot.** Both answers are
worth having — a failed attempt is evidence the class has teeth. Do it **before** citing membership as
meaningful, because a vacuous class makes every downstream *"X carries this, therefore…"* empty.

**⚠ The failure is invisible from inside.** Every one of the five was found by someone building a
witness, never by reading the class. `SeparatedSuccession`'s `separated` field even carries the comment
*"the succession never repeats"* while admitting a **constant** sequence — the comment asserts what the
field does not enforce.

**Enforcement (2026-08-07, Tim's call — mechanical because this is the FIFTH convention of this shape
and the earlier four all leak).** `python tools/verify/check_classes.py --block` ENFORCES at commit AND at push. It cannot decide degeneracy (that needs a witness); it enforces that the
question was **asked** — a `NO-GO` section, a `Nondegenerate` predicate, or a named trivial witness in
the declaring file. Same design as `check_pov.py`: enforce that a convention was followed, never that a
claim is true. **Baselined; blocks on NEW classes only.** (For the current count run the checker — it prints `grandfathered` on every run. A number written here contradicted `class_baseline.txt` in the same directory, which is DC-6 inside the file that documents DC-6.) Shrink the baseline
as files are touched; `SeparatedSuccession` is first to remove (tracked as `SEP-1`).

**Detector verified before use**, per this file's own rule: it fires on `SeparatedSuccession` (the
known-degenerate case, found by hand the same day) and suppresses `InfinitudeFloor`,
`WheelValuationStructure` and `AbstractSelfApp` (where the question was asked). A checker with only a
must-fire control is half-tested.

## A guard protects a PROPERTY, not a hole. Enumerate every ROUTE — in `guards.py`. Gate-enforced.

**Fixing one route to a property and calling it closed is this project's most repeated defect, and
until 2026-08-10 nothing but memory stood against it.** Measured: *"a file cannot exempt itself from
the gating checkers"* was fixed **four** times — content marker → nested `Vendored/` path → the
`vendored_files.txt` allowlist → the four `*_baseline.txt` switches — and *"the bedrock cap cannot be
walked"* **three** times, each fix correct and each leaving another door open. The routes live in
different files, so *"enumerate them"* was a memory exercise performed by whoever had just forgotten
one. (Tim: *"I'm getting a little tired of that behavior."*)

**THE RULE — when you close a hole, name the PROPERTY, then add EVERY route to
`tools/verify/guards.py`.** Not a comment, not a note. The registry is the deliverable; the fix is
half of it. `python tools/verify/guards.py --list` prints the surface; it BLOCKS in `pre-push`,
ahead of the checkers it protects, because a green checker whose exemption surface has a new hole is
a **false zero**, and this file already records that a false zero costs more than a red one.

- **List permitted routes too**, with a `visible` predicate. Vendoring must keep working; the
  requirement on a legitimate exemption is not that it fails but that **it cannot happen quietly**.
- **Include the enumerator.** `guards.py` is in `CHECKERS`, because deleting a route from the
  registry would otherwise re-open it *and* remove the only thing that would say so — the **fifth**
  instance of the property, found while wiring the fix for the first four.
- **It found two live routes on its first run**, one of them (`P5-3`) already sitting open in the
  ledger. That is the argument for the mechanism over the discipline, in one measurement.

## Short header, statement per declaration. Prose never exceeds code. Gate-enforced.

**Tim, 2026-08-08, and it is a software-engineering norm, not a preference:**

> *"I'm not a big fan of having just a giant header block full of prose. Usually it's a short
> summary of what the file is supposed to be doing as a whole, no more than a few sentences, and
> only once you actually get into the individual lines, do you have a statement of what that exact
> line is supposed to be doing. Apart from the Engineer's Take, I don't think there should be more
> prose than code as a general rule, counted by line numbers."*

**THE SHAPE:**
1. **File header** — a few sentences on what the file does. **Not** an essay.
2. **Every declaration** — a docstring saying what **that declaration** does, no longer than the
   declaration itself.
3. **Long-form reasoning** — a note in `.claude-local/notes/`, with a pointer. Not the source file.
4. **The Engineer's Take is exempt.** It is Tim's voice and the only corpus written in the register
   a question arrives in — `where.py` reports Takes for exactly that reason.

**WHY IT IS A CORRECTNESS RULE AND NOT TIDINESS. Code is kernel-checked; prose is unchecked by
construction.** The prose:code ratio is the ratio of verified asset to unverified liability.
Measured across three gate rounds on 2026-08-08: **~12 findings, every one in prose, none in a
theorem statement** — and an 82-line cut then passed all three gates with nothing load-bearing lost,
one deletion being an outright *improvement* because the paragraph asserted a distinction the
artifact could not support. **The corpus's characteristic defect class is prose, and prose volume is
its carrier.**

**MEASURED, so the rule is calibrated and not guessed** (2026-08-08, whole corpus):
- prose **15,629** lines vs code **14,795** excluding Takes — ratio **1.06**, with **129 of 218
  files** already over.
- **The design is already the norm**: file-header blocks run **p50 = 1 line, p75 = 3, p90 = 7**;
  section blocks **p50 = 1, p75 = 6, p90 = 14**; and **85% of declarations already have a
  docstring**. This is **outlier control, not a migration** — the tail runs 121, 115, 100, 83 lines.
- **41% of all prose sits in detached header blocks** rather than attached to what it describes.
  The extreme is `ChoiceCannotBe.lean`: **302 prose lines, five blocks, zero docstrings** — and two
  false universal negatives lived in exactly that prose until 2026-08-01.

**⚠ THIRD-PARTY BACKPORTS ARE EXEMPT STRUCTURALLY, NOT BASELINED** (Tim, 2026-08-08: *"the vendored
bucket we shouldn't touch at all, that's a backport from an official source"*). A baseline entry
means *fix later*; this means **never**. Editing an Apache-2.0 backport's prose also destroys the
diff against upstream, which is the reason for vendoring it. `check_prose.py` skips any file under
`Vendored/` or carrying a provenance header (`VENDORED FROM`, `Apache-2.0`, `Upstream:`) and **names
the exempt files in its output**, so the exemption is visible rather than silent. Currently
`ZeroParadox/Vendored/NaturalOps.lean` (verbatim, Mathlib v4.28.0) and
`ZeroParadox/Ordinal/NaturalOpsPow.lean` (a port of Hernández's Combinatorial Games file) — verified
to match those two files and no others. When the exemption landed it removed **140 sites, measured 2026-08-08**,
of which **119 were undocumented declarations we did not author, measured the same day** — a
one-time delta, not a running total.

⚠ **The exemption has exactly ONE definition — `tools/verify/vendored.py`. Import it; never restate
it** (Tim, 2026-08-09: *"the vendor files should be exempt extremely. we already did it elsewhere"*).
It lived in `check_prose.py`, was re-implemented from memory in `batch.py`, and **the copy was
already wrong three ways after a single day**: `Apache-2\.0` missed the space form, an unanchored
`Upstream:` matched prose *about* upstream, and it scanned 4000 characters where the original scanned
30 lines. A duplicated exemption drifts, and a drifting one is worse than none — it exempts files
nobody meant to exempt. **All five checkers plus `batch.py decls` now import it**, which also closes
the hole this line used to record: `check_pov` / `check_modal` / `check_classes` previously had no
vendored handling at all. **Verified with matched pairs** — the same violations planted in a vendored
file report 0 from every checker, and fire from every checker in a non-vendored one. ⚠ The scan is
deliberately limited to the file HEAD; a whole-file search would exempt anything merely *mentioning*
Apache-2.0.

**AND AN INDEX LINE MUST JUSTIFY ITSELF** (Tim, same day): *"every one of those CannotBe line items
should be distinguishable from the others, and the statement for why the CannotBe is applicable
should be directly tied to the specific lines."* A `#check` index is nothing **but** line items, so
a justification sitting in the header leaves every line uncheckable and no two items
distinguishable. **Measured across the six index files:** 47 of 204 `#check`s carry **no gloss at
all** — `BottomCannotBe.lean` is 36 of 72 — while `ChoiceCannotBe.lean` carries **203 header lines
against 31 checks**, which is what "built after the fact" looks like. ⚠ **And the
`Statement:`/`Reading:` convention is applied to 13 of 151 glosses** — zero in four of the six
files. The mechanism meant to stop glosses overclaiming is, in the indexes whose premise is that
they cannot overclaim, essentially absent.

**ENFORCEMENT — mechanical, because this is the SIXTH convention of this shape and the previous
five all leaked.** `python tools/verify/check_prose.py --block` ENFORCES at commit and at push
(`pre-push` § 3b-e). **FOUR rules** (a fifth was retired 2026-08-08, below): a module-doc
block over **10 lines** (just above the p90 for file headers); a docstring longer than its
declaration; a `#check` with **no gloss**; and a gloss carrying **no `Statement:`/`Reading:`
label**. **Fires on NEW and EDITED prose only.**

⚠ **RETIRED — "a declaration with no docstring".** It was the only rule here that **demanded**
prose rather than capping it, and authoring is where this corpus's defects come from: measured
across one arc, roughly **one hand-written gloss in seven was false, while deletions produced
none**. What it demanded is also redundant now — the public CI run summary publishes every
declaration's axiom footprint and the build emits its elaborated signature, both regenerated per
run and neither hand-maintained, so a docstring restating a signature is a second copy that can
drift while the artifact cannot. Retiring it removed **119 sites, measured 2026-08-08, by
amending a rule rather than by writing anything** — the only category of burndown with a zero
error rate. **An
interpretive docstring is still welcome everywhere — it is simply no longer mandatory**, and the
caps on over-long ones are untouched.
- **The `bare` rule was deliberately NOT retired with it.** 17 of the 27 open bare-`#check` sites
  are inside `CannotBe` indexes, which are reader maps for people who do not read Lean signatures;
  a bare index line tells them nothing. Those stay real debt.
- **The baseline was PRUNED, not regenerated.** `--baseline` rebuilds from whatever violates today
  and can grandfather a site nobody has read, which would falsify the baseline's own premise that
  each entry was verified by reading it. Removing a subset cannot add anything: a strict subset of the previous keys,
  strict-subset assertion enforced in the pruning script. **Verified end-to-end**: a newly added
  undocumented declaration no longer blocks (exit 0) and a newly added bare `#check` still does
  (exit 1), with the working tree restored clean.
Blocks are keyed by a **content hash**, so editing a grandfathered block re-fires it: the
baseline-shrinking rule enforced rather than remembered. **Detector verified with six controls**
(must-fire on an oversized block, an oversized docstring, an undocumented declaration, a bare
`#check` and an unlabelled gloss; must-suppress on the Take, documented/attributed declarations,
`private`, `example`, and both label forms in same-line, line-above and bolded shapes), plus an
end-to-end control that `--block` exits 1 on a new site and 0 once baselined. ⚠ **The first
baseline silently under-covered by six sites** because a truncated key could end in whitespace,
which `.strip()` destroyed on read-back — a clean-looking zero that was wrong, and the reason the
end-to-end control exists.

⚠ **The failure mode to watch is mine, not the tool's.** Every gate round of that arc, I answered a
finding by *adding a paragraph*, and each new paragraph carried a new claim. **When a section will
not stabilise, cut the essay around the theorem — do not extend it.** That is the § *Prose that
resists correction* protocol arriving at file scale.
