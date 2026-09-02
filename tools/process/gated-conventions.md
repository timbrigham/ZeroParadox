# The gate-enforced conventions, the control objects, and the brief-delivery rule

**Body for `CLAUDE.md` §§ `R-GATED`, `R-CONTROLS` and `R-BRIEF`.** The rules are there;
the measured defect behind each checker, the control-object survey with its definition
sites, and the spawned-agent incidents are here.

---

## ⭐⭐ THE GATE-ENFORCED CONVENTIONS. Rules here; the ARGUMENT is `tools/verify/README.md`.

**TRIGGER — an action, so there is nothing to adjudicate: you are about to write a POV claim, declare
a requirements class, add a prose block or docstring, close a self-exemption hole, or WRITE ANY FILE
TO DISK.** Each rule below **BLOCKS at push**, so you find out either way; reading first is how you
avoid finding out the expensive way.

| rule | fires when | checker |
|---|---|---|
| **A point-of-view claim declares its KIND and its STATUS.** Five kinds — COINCIDENCE, INVERSION, DRIFT, CARRIER, INVARIANT — via the existing `Statement:` / `Reading:` labels. **There is no slot for DENYING a reading, by design.** | you write "chart", "frame", "point of view" | `check_pov.py` |
| **A requirements class is only informative if something FAILS to be a member.** Build the trivial witness or prove you cannot; both answers are worth having. | you declare a `class` or `structure` | `check_classes.py` |
| **Short header, statement per declaration; prose never exceeds code.** The Engineer's Take is exempt. | you add a header block or a docstring | `check_prose.py` |
| **A guard protects a PROPERTY, not a hole — enumerate EVERY route.** Closing one route and calling it fixed is this project's most repeated defect. | you close a self-exemption or bypass | `guards.py` |
| **⭐⭐ REMOVING A BASELINE ENTRY OWES A `/claim-review`. A baseline entry IS the record that a site was let through UNEXAMINED**, so deleting it retires the record without discharging the liability. **The checkers measure the SHAPE of prose — volume, vocabulary — and never whether a claim is TRUE**, so a block dropping under cap is not a block whose claims were checked. ⚠ **FAIL-CLOSED, because "the key stopped matching" is not enough:** a removal is either *content GONE* (nothing to review) or *content MOVED* — a path-keyed entry dying while the claim lives on elsewhere — and no checker can tell them apart. The only exemption is the FILE being gone; an entry naming `Foo.lean` also demands its `Foo.md` ride-along. **Removal is still always ALLOWED — it is the point of the freeze — it is just not FREE.** | you delete a line from any `*_baseline.txt` | `check_frozen.py` |
| **EVERY FILE WRITTEN TO DISK IS VERIFIED — `python tools/verify/check_encoding.py <path>`.** ⚠ **"Is it UTF-8?" is the WRONG QUESTION and returns PASS on this defect**: double-encoded text is valid UTF-8 at every byte, so a decodability test is green while the content is garbage. And the corruption usually enters at **script PARSE time, not write time** — PowerShell 5.1 reads a `.ps1` as the system codepage unless the script carries a BOM, so a correct writer faithfully writes an already-mangled string. **Prefer the `Write`/`Edit` tools; keep non-ASCII out of `.ps1` source.** ⚠ **TWO TIERS: BOM and undecodable BLOCK; suspected double-encoding WARNS** and is quieted only by `tools/verify/encoding_whitelist.txt` — **verified** exclusions each carrying a stated reason, because the round-trip test provably cannot separate mojibake from some genuine typography (`3 × 10²` encodes to valid UTF-8). An entry with no reason is ignored. Recipes and the repair procedure (a whole-file inverse DESTROYS a mixed file): `tools/process/file-encoding.md`. | you write any file | `check_encoding.py` |

**⭐ THE ONE-LINE WHY, and it is the same for all four: each was a CONVENTION that leaked before it
was a CHECKER.** This file records **seven** conventions that leaked while being remembered by people
who had read them; every one of these four is a rule that failed as discipline and works as a gate.
That is the argument for reading `tools/verify/README.md` before arguing with any of them.

**📖 THE FULL ARGUMENT — `tools/verify/README.md`.** What each checker detects, the measured defect
it exists to stop, the baseline policy, and the controls each was verified against.
**Read it before changing a checker, adding a baseline entry, or claiming a gate is wrong.**

⚠ **Why it is THERE and the rules are HERE.** The arguments are prose that every session and
every subagent used to pay for, and **the gate fires whether or not anyone read them** — measured
2026-08-15: line 127 of this file fired reliably all day, line 2135 did not fire once. A rule in the
tail is decorative. So the rule, the trigger and the consequence stay in the firing zone; the
justification moved to a file this line NAMES. Same mechanism as the `CannotBe` indexes — delivery
is a trigger naming a path, not injection.

⚠ **A baseline is DEBT, not a decision, and all four are baselined.** They block on NEW sites only.
**Shrink the baseline as files are touched; never grow it deliberately** — `debaseline.py` reports
what is outstanding.

## Every brief carries the CONTROL OBJECTS and "name your first unjustified step". Hard Rule.

⚠ **This section deliberately did NOT move to `tools/verify/README.md` with its four neighbours.
Nothing enforces it** — no checker fires when a brief omits the controls — and an unenforced rule
outside the firing zone is a rule that stops working. **Enforcement is the criterion for moving a
section out, never adjacency.**

**Adopted 2026-08-11 from the zeta-zeros paper** (`.claude-local/papers/claude_zeta_zeros_two_thirds_2026.pdf`,
§C.6 *Parallelism with controls*). Its twenty-three concurrent agents each received the **same control
objects** — Davenport-Heilbronn functions, Epstein zeta functions, planted-zero Beurling systems:
objects satisfying the same inputs **for which the conclusion is FALSE** — plus one standing
instruction, *name the first step that is not justified*. Reported outcome: *"Most lines died against
their controls. The one that survived did so precisely because the controls under-certified."*

**ZP already owns its controls and has never issued them as a standing set** — they get run when
someone remembers, which is exactly how five of seventeen requirements classes went degenerate
unnoticed. The § above enforces that the degeneracy question was *asked*; this makes the answer
*available* to whoever is asking.

**Put these in every brief that BUILDS or REVIEWS a class, a claim, or a construction.** Located and
verified at their definition sites 2026-08-11 — a dated survey, not a completeness claim:

| control | where | kills |
|---|---|---|
| `Unit` / `PUnit` | — | any algebraic signature; every theory has a one-element model |
| `Empty` | — | anything with a `bot : L` field — but see the trap below |
| `Bool`, `Fin 3`, `ℕ → ℕ` | — | "the class bites at two or more points" |
| `trivialZPSemilattice` | `ZeroParadox/Valuation/Scale.lean`, `def trivialZPSemilattice` | `ZPSemilattice` membership as an argument |
| `trivialSelfApp` | `ZeroParadox/Computability/SelfApp.lean`, `def trivialSelfApp` | *"L carries `AbstractSelfApp`, therefore…"* |
| `trivialValBridge` | `ZeroParadox/Valuation/ScaleBridge.lean`, `def trivialValBridge` | `ValBridge` membership |
| `trivialValuationStructure` | `ZeroParadox/Valuation/Scale.lean`, `def trivialValuationStructure` | `ValuationStructure` membership |
| the constant map `_ ↦ ⊥`, the always-true relation, a constant sequence | — | self-application, `SeparatedSuccession`, periodicity |
| **ℝ** — `f_snap_impossible`, `ZeroParadox/Reals/OrderedField.lean` (cited as `ComputationCannotBe.lean:152` until 2026-09-01 — WRONG FILE, and the line number happened to be right, which is why it read as precise) | | any claim that the snap is available in a general ordered carrier |

⚠ **`Empty` is a two-sided trap.** *"The finite carriers are exactly the subsingletons"* shipped as a
bedrock defect because the true statement needed **inhabited** subsingletons. And K1 is the same trap
inverted — `Order/Lattice.lean` claimed non-members *"abound"* when **every inhabited carrier admits a
`ZPSemilattice`** and `Empty` is the only obstruction. Run it, and read which way it points.

⚠ **VERIFY A CONTROL EXISTS BEFORE NAMING IT.** Writing this table, one name recalled from a ledger
row (`scTriv`) **did not resolve anywhere in the corpus**. A brief citing a control that does not
exist is worse than a brief with no controls: the agent reports it could not build the witness, and
that reads as evidence the class has teeth.

## Rules That Must Reach Spawned Agents — Hard Rules

**Why this section exists (measured 2026-07-19).** A spawned agent receives, automatically: this file in
full, the user-level `CLAUDE.md`, the Lean `.claudecodes` block, the project-standards block — **and the
memory INDEX only, not memory file bodies.** So a rule whose content lives in a memory body reaches a
subagent as one line among ~100 in an index, competing for attention with ninety-nine others, firing at
no particular moment. That is not a control.

**The consequence, verified:** a subagent invented a factual detail about a cited paper while the line
*"Draft from source only — public math claims must trace to a specific source passage"* was sitting in
its index. The rule was visible and did not bind. **A rule that must not be violated belongs HERE or in
the task brief. Memory is for context, not enforcement.** When delegating, carry the relevant rules below
into the brief explicitly — the same way the encoding and glob warnings are already carried.

- **Draft from source.** Never describe the content of a source you have not read. Cite existence (title,
  venue, that it exists) freely; assert specific technical content **only with the passage in hand**. If
  you cannot read it, say so explicitly — do **not** soften a specific into a vaguer assertion about a
  paper nobody opened. Applies to Lean docstrings citing external papers, companion sections, discussion
  comments, and outreach. Before concluding a PDF is unreadable, try `pypdf`/`pdfminer` directly
  (`.claude-local/extract_pdf_text.py`); a fetch tool's failure is not a fact about the source.
- **Start new files from the templates.** Any new `.lean` file starts from `.claude-local/templates/`
  (`TEMPLATE_lean.lean`, `TEMPLATE_experimental_mapping.lean`) and its `README.md`. Note the template's
  namespace line is stale — namespaces are FLAT (`ZeroParadox`), not `ZeroParadox.ZPX`.
- **Never write a bare "bottom."** Always say which level: the structureless referent / a specific
  structured instance (a face) / the family-and-schema. The bare word sliding between senses is the
  project's longest-standing source of confusion. (`/remember-bottom` re-orients.)
- **The literal string `ε₀ = 0`** may appear ONLY as a guard or fence forbidding it, or as a theorem where
  ε₀ is an argument. Never a bare assertion, never in conversation — even to deny it. Canary:
  `epsilon0_ne_zero`.
- **Standard mathematical term first**, ZP term after as a declared shorthand — never the reverse. This is
  the defense against the "ontology built on an equivocation" reading.
- **Verify an API exists before naming it in a plan.** Grep the Mathlib pin; a plan citing a lemma that
  does not exist in the pinned version is worse than no plan.
- **Never delete a Lean file a subagent produced**, even a failed experiment — say so in the brief.
- **NO SCRATCH FILES IN THE REPO.** Any probe, temp script, or measurement file goes in the session
  scratchpad directory, never under `ZeroParadox/` or anywhere else in the working tree. A reviewer that
  needs to measure something writes it to the scratchpad, runs it, and deletes it. **Measured
  2026-07-19:** a review agent left a `ZZTestOrd.lean` probe in the source tree (since deleted, so the
  path no longer exists) and it was committed — a scratch probe is now in the permanent history. Put this
  line in every subagent brief.
- **Reviews are READ-ONLY on the working tree.** A gate reads, measures, and reports; it does not modify
  repo files. The only writes a gate may make are its signal file and its findings note under
  `.claude-local/notes/`.
- ⚠⚠ **AN AGENT THAT EXERCISES THE HOOKS MUST NEVER `git reset --hard`, `git checkout -- .`,
  `git clean`, OR `git stash` THE SHARED TREE — IT WILL DESTROY THE CALLER'S UNCOMMITTED WORK AND
  REPORT SUCCESS.** Measured 2026-08-10: a `/rely` run was told to exercise the commit and push
  gates and to leave the repository exactly as it found it. It made probe commits and reset
  **`--hard`** to the base three times. That is a *correct* reading of the instruction, and it
  **silently deleted an uncommitted `CLAUDE.md` edit** the caller was holding; the agent then
  verified *"tracked tree clean, HEAD unchanged"*, which was true — and was the destruction. It had
  even NOTICED the concurrency, reporting that two files *"were being edited by their author during
  the trial"*, and hard-reset anyway. **"Restore the tree" and "preserve the tree" are different
  instructions, and only the caller knows which is meant.**
  - **Rule for the BRIEF:** an agent needing to create commits works in a dedicated worktree —
    **`worktree(action='add')`**, which returns a detached checkout under a scratch area outside the
    repository — never in the shared checkout. It gets a private HEAD and index, so nothing it does
    can reach the caller's tree; cleanup is `worktree(action='remove')` with that path, and
    `action='prune'` drops records of worktrees whose directories are already gone. The `CAL-2`
    pipeline replay used exactly this and left the main tree untouched.
    ⚠ **CARRY THIS INTO THE BRIEF VERBATIM, because the command CHANGED.** The old
    `git worktree add --detach` is now denied like every other direct git call, and this is the
    sanctioned escape from the four destructive verbs — so a brief that still names the old form
    leaves its agent with a safety rule it cannot execute. Measured 2026-08-22: `rely.md`'s single
    git reference was exactly this line.
  - ⭐ **The four destructive verbs are now REFUSED, not merely banned** — the hook denies the
    command and gitRobot has no parameter that reaches `--force`, `--hard` or `-f`. This bullet is
    now a statement of *why*, kept because the reasoning is what transfers to the next verb nobody
    has classified yet.
  - **Rule for the CALLER:** commit or stash your own work **before** spawning any agent licensed to
    touch git state, and treat the tree as unstable until it returns. This file already warns that
    background agents run concurrently so the tree is not a stable snapshot; this is that hazard
    with a **destructive** edge rather than the merely additive one of the `git add -A` incident.
  - ⚠ **`.claude-local/` survived only because the parent ignores that path — do not read that as
    safety.** A `clean -xfd` would have taken the whole private working folder. ⚠ **It DOES have a
    remote now** (`ZeroParadoxLocal`, private) — this line said "no remote and is backed up by hand"
    until 2026-08-22, which was stale, **and believing it is what left three commits sitting on one
    disk that day.** Commit *and push* it; see the handoff's PART 0b step 4.
- **Engineer's Takes are Tim's voice.** Claude never drafts one. The only sanctioned assembly is
  restating Tim's own session statements as declaratives, grammar-cleaned, shown back for approval.
  **Fill the Take BEFORE running the review gates (Tim, 2026-07-20)** — it is public prose in the pushed
  file, so the reviews must cover it. Order: finish the work → insert Tim's Take (with approval) → run
  editorial/adversary/prior-art on the COMPLETE file → push. Gating first and adding the Take after
  leaves it unreviewed and (under the SHA-256-per-file signal scheme) stales every signal, forcing a
  needless re-run.
