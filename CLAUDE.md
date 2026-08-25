# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.
## R-ROBOT  Direct `git` and `gh` are BLOCKED for agents. Use `gitRobot`.
TRIGGER  you are about to type `git` or `gh`.
RULE     a `PreToolUse` hook inspects the WHOLE command string for a word-boundary `git` or
         `gh` and denies it — bare, `cd`-chained, `&&`-chained, `-C`, absolute path, shelled
         out of Python. It FAILS CLOSED. Use instead:
           status, unpushed count, what would block a push  → `status()`
           any read (log diff show ls-files rev-parse blame) → `read(op=..., args=[...])`
           stage → `stage(paths=[...])` — NAMED PATHS; `-A` refused on the main repo
           commit → `commit(message_file=...)` — message from a FILE, never argv
           push → `preflight()` → `preflight_status()` → `push(branch, reason)`
           sync → `fetch()` then `merge(branch, reason)`
           a private checkout to mutate → `worktree(action='add')`
           why was I refused → `explain(refusal_id)` · `history(limit)`
           a RELEASE → Tim. Releases mint permanent DOIs; not an agent decision.
         DO NOT WORK AROUND IT — no aliases, no wrapper scripts, no shelling out. If you
         believe you need direct access, say so and let Tim decide.
COST     ⚠ the matcher sees ARGUMENTS: a path containing the standalone token blocks the whole
         command, so never put a bare `git` in a filename. Tools using it INTERNALLY are
         unaffected — `batch.py`, the checkers and the build scripts keep working; do not
         "migrate" them. This is layer 2 of 3 and layer 3 does not exist: only remote branch
         protection with required status checks is sound, and it is still not configured.
READ     .claude-local/notes/access_controls_2026-08-22.md

## R-EXEMPT  What is gate-exempt, and why you may not infer the next one.
TRIGGER  you are about to commit a file and are deciding whether the prose gates apply.
RULE     EXEMPT: `CLAUDE.md`, `tools/verify/**`, `tools/process/**` — operating machinery that
         asserts nothing about the mathematics, so editorial and adversary have no claim.
         `/rely` covers those two directories INSTEAD, and it BLOCKS on executable logic and
         exemption switches; routed `.md` only WARNS. NOT EXEMPT: `.claude/commands/**` — the
         gate briefs are published deliberately, as the artifact showing how this project
         reviews itself, so both gates fire on them. **Published-and-exempt is not a category
         you may reason your way into.** Each carve is WRITTEN DOWN; do not extend one to a
         further directory by analogy — write the next one, or it is not exempt. Fence:
         anything asserting mathematics belongs in the corpus and is gated normally.
COST     the exemption is PRICED on `/rely` still blocking. Weaken that routing and the
         exemption becomes a hole; a downgrade un-prices whatever the block paid for.
READ     tools/process/README.md

## R-NARRATE  Narrate the MATHEMATICS, in an engineer's register, in every report.
TRIGGER  you are writing any report that touches mathematical content.
RULE     carry a plain-language pass on the MATHEMATICS beside the process summary — not
         instead of it, and not only when asked. Gate verdicts, defect ids and exit codes are
         scaffolding. Use systems and programming analogies (recursion and termination, type
         signatures, preconditions, interface versus implementation, invariants, null versus
         empty, cycles in a graph) and name the object before using its symbol. Spell glyphs
         out in words at least once per paragraph — bottom, epsilon-zero, infinity. Standard
         mathematical term first, ZP shorthand after. STATE WHICH DIRECTION AN IMPLICATION
         RUNS and why that matters. Do not soften the claim: precision is the deliverable and
         only the register changes.
COST     Tim is this project's mathematician of record by decision, not by training; he cannot
         review what is never explained, and his review is the control that has repeatedly
         caught what the gates did not. This governs REPORTS, never the corpus — it is not
         licence to add prose to `.lean` files.

## R-PRECOMMIT  `batch.py precommit` before every commit. `/batch` for anything multi-site.
TRIGGER  you are about to commit, push, or start multi-site work.
RULE     `python tools/verify/batch.py precommit` before EVERY commit — it runs the four
         universal obligations (build green, a `#print axioms` entry and an `ssot.json` row
         per added declaration, all checkers at zero new). `python tools/verify/batch.py
         prepush` before any push: which reviews are required, whether the signals are FRESH
         by hash and coverage, and the recorded VERDICT line from each, so "cleared" is never
         read as "clean". DO NOT LOOK UP WHAT BLOCKS WHERE — all four entry points print a
         manifest first; run it, never maintain a prose copy. Use `/batch <bucket>` for
         multi-site work; filters FREEZE at `batch start`, so editing a checker mid-batch
         invalidates it. IF A STAGE BLOCKS, FIX THE CAUSE — never delete `batch_state.json`,
         never `--no-verify`, never push a subset to dodge a signal.
COST     the purity/SSOT check runs off an ON-DISK baseline, never git: computed against HEAD
         it passes VACUOUSLY after the commit. A stale baseline is safe — it only makes more
         declarations look new. This project has two recorded bypass incidents and both began
         by treating a block as an obstacle.
READ     tools/process/pipeline.md

## R-DEFECTCLASS  One row per defect CLASS, each with its DETECTOR.
TRIGGER  you are writing a gate brief or spawning a reviewing agent; something looks wrong and
         you are choosing how to check it; or a defect has recurred.
RULE     consult `.claude-local/DEFECT_CLASSES.md` by DEFAULT. In a brief, name the LAYER
         attacked, the STATE tested, and the DETECTOR BY ID — "check the glosses" is not a
         detector, "DC-1: read the elaborated `#check`" is. A gate that does not name its
         layer re-attacks the one the last gate cleared. A one-off is an instance and belongs
         in `DEFECTS.md`; the SECOND occurrence is a class and gets a row plus a detector, in
         the same change. `tools/verify/selfheal.py` counts recurrences and `batch.py prepush`
         prints the top uncovered shapes on every run — its counts are a READING LIST, never a
         finding list.
COST     PREFER A DETECTOR WHOSE VERB IS *RUN* OVER ONE WHOSE VERB IS *READ*: across ~20 agent
         runs every BEDROCK finding came from EXECUTING something and every ORDINARY one from
         READING something, without exception. Six of seventeen rows have a mechanical checker
         and eleven do not — that is visible debt, not a solved problem.

## R-DEFECTS  A defect's home is the ledger. Read it before choosing work.
TRIGGER  you found a defect, you are choosing what to work on next, or you are about to
         cut a release.
RULE     record it in `.claude-local/DEFECTS.md` — never a note, a gate-findings archive,
         or a handoff line, and never a second copy. Verify every entry AT THE ARTIFACT
         before recording it open or closed. GREP LOOSELY. Burn down in FILE-SIZED
         BATCHES. NO RELEASE IS CUT WHILE THE LEDGER IS NON-EMPTY; release pressure never
         defers a finding to next-touch debt. The target is ZERO KNOWN defects, not zero.
COST     a DOI is permanent and four releases already carry latent flaws — a defect fixed
         before a release costs one gate round, one shipped inside a PDF is forever.
READ     tools/process/defect-ledger.md

## R-RECUR  A failure that recurs is evidence about the RULE, never about the reader.
TRIGGER  you are told you are in a failure condition, this is a retry, a gate returned
         FAIL, or someone refers to a rule you do not recognise.
RULE     re-read this file FROM DISK first — `grep -n "^## " CLAUDE.md` before any full
         read; your injected copy predates every rule written this session, your own edits
         included. Then, stopping at the first step that resolves: check `DEFECTS.md` and
         `DEFECT_CLASSES.md`; diagnose the TRIGGER, not the content (an ACTION binds, a
         CATEGORY leaks); fix at the highest leverage — checker > trigger-plus-path > note;
         control-test with a fresh agent, scorecard fixed BEFORE the result; test delivery
         separately from correctness. Escalate by COUNT: 1st an instance, 2nd a class with
         a detector, 3rd the trigger is wrong, 4th+ build the checker. Never add a second
         rule saying the same thing louder, and never skip to writing a new section.
COST     a mid-session edit never reaches agents spawned after it, so a correct fix can be
         unreachable; and a rule stated twice fires in neither place.
READ     tools/process/recurrence-protocol.md

## R-NOCONV  A check that misses 3x, or a loop that will not settle, changes SHAPE.
TRIGGER  a mechanical check has missed three times, or three or more rounds of fixes have
         not reduced findings — name the rounds and their counts, never assert it.
RULE     stop widening the script. Put an LLM screen on the layer as a READING LIST: it
         may replace the ENUMERATION, never the VERDICT — take sites flagged in >=2 of 3
         runs, ignore self-reported confidence, and ship the recorded slice it should get
         WRONG as its control. Downgrade ENUMERATION legs to WARN; FAIL-OPEN legs never
         downgrade, no matter how many rounds. SPLIT AT THE LEG, never at the check. The
         guard asserting what still BLOCKS lands in the same change, or the exemption that
         block paid for is given up with it. A downgraded gate prints its count every run.
COST     a downgraded fail-open leg is an unpriced exemption, and a warning nobody counts
         manufactures coverage that was never earned.
READ     tools/process/non-convergence.md

## R-EDITLEAN  Before you edit ANY `.lean` file, read the manifest and grep the identifiers.
TRIGGER  you are about to change a `.lean` file — one character, a docstring, a comment.
         No judgement call, no exception for "it's only prose".
RULE     (1) read `ZeroParadox/MANIFEST.md`, the by-folder index of the whole corpus, ~7k
         tokens — cheaper than loading a folder, and 104 `.lean` files already point at it.
         (2) grep the IDENTIFIER of every declaration you are touching, not the wording of
         the claim, then READ THE HITS. Do BOTH: searching the CLAIM finds paraphrases,
         searching the NAME finds every citing site, and the identifier sweep is the
         mechanical one, so it is the one that cannot be talked past.
COST     measured on a docstring edit made after grepping three theorem names: the wording
         survey found 4 citing sites and `grep -n "l_inf"` returns 9, and the appended
         paragraph re-committed an overclaim that had ALREADY been corrected — in the very
         file the new text cited and never opened. Reverted in full. This is the eighth
         convention of this shape and the previous seven leaked; until `refs.py` prints
         reverse references at edit time, this one is remembered, and remembered rules fail
         here by construction.
READ     tools/process/core-objects.md

## R-COREOBJ  Read the Lean before writing about the bottom, the snap, or epsilon-zero.
TRIGGER  you are about to write any prose, figure, docstring, companion text, note or
         outreach copy naming the bottom, the snap, epsilon-zero, choice, or computation.
RULE     open that object's authoritative Lean file and ground every statement in a NAMED
         theorem there. Never reconstruct from memory, from notes, or from this file. If
         this file and the Lean disagree, THE LEAN WINS — stop and ask Tim.
           bottom  `ZeroParadox/BottomCannotBe.lean` + `BOTTOMELEMENT.md`
           snap    `ZeroParadox/Order/SnapCannotBe.lean` + `ZeroParadox/Order/Snap.lean`
           eps-0   `ZeroParadox/Ordinal/Epsilon0CannotBe.lean`
           also    `ZeroParadox/DiagonalFixedPoint.lean` (keystone) ·
                   `ZeroParadox/Category/ChoiceCannotBe.lean` (choice) ·
                   `ZeroParadox/Computability/Kleene.lean` (computation) ·
                   `ZeroParadox/ClaimsMirror.lean` (a claim's status)
         Every gloss carries `Statement:` (what it proves, best form an elaborating `example`)
         or `Reading:` (interpretation, NOT a claim about the theorem). No third option.
         `Idiom:` is vocabulary for a NAMED phenomenon, never a gloss, and it SUPPRESSES —
         apply it only after verifying the site.
COST     the `#check` lines cannot overclaim and the glosses beside them can: two false ones
         survived four adversary rounds inside a file whose stated premise is that it cannot.
READ     tools/process/core-objects.md

## R-BEDROCK  Machine-checked invariants. Never violate; verify at the theorem, never assume.
TRIGGER  you are about to state anything about epsilon-zero, the pole, or where the snap-arc
         returns.
RULE
- **ε₀ ≠ 0. Always. In any reading, carrier, or encoding.** (`epsilon0_ne_zero`.) Never "fence ε₀ = 0" or treat 0 as a candidate value — it is not a well-formed possibility.
- **ε₀ ≠ ⊥.** (`epsilon0_ne_bot`.) ⊥ = 0 is the *base* the ε₀-tower is seeded at; ε₀ is its *closure* — the base is never its own closure.
- **ε₀ is both min AND max at once** — least fixed point ≡ tower supremum (`epsilon0_min_eq_max`); direction-/instance-specific, never collapsed to one face.
- **ε₀ requires two conditions**: the ω-tower operator `α↦ω^α` AND the base ⊥ (`epsilon0_eq_nfp_bot`). It is the *minimum* step next to the pole, never the pole.
- **⊥ = 0 = ∞ is the pole** — *stated*, not fenced. **A CHART claim, not a point identity.** Three distinct witnesses: **coincidence** `infinitude_forces_infinite_complexity`; **drift** `pole_inversion`; **inversion** `rInv_swaps`. **Never cite `rInv_swaps` for the coincidence** — it proves two points *exchanged*, and there they are provably distinct. This is NOT ⊥ = ε₀, which is false.
- The snap-arc **returns to a bottom, never to ε₀** (`epsilon0_ne_bot`). Proved is the **role** half — anything playing the bottom role IS the bottom (`t_iz_limit_is_new_null`). The **novelty is a commitment, not a theorem**; in the 2-adic realization the arc reapproaches the *same* 0 (`snap_arc_z2_loop`). **Never cite `t_iz_limit_is_new_null` as a witness for novelty.**
COST     each of these was violated in shipped prose by reconstructing from memory; a wrong one
         inside a published PDF cannot be withdrawn.
READ     tools/process/core-objects.md

## R-COMMIT  Commitments go in HYPOTHESES; data goes in BRACKETS.
TRIGGER  you are about to add a field to a `class`/`structure`, or state a theorem whose
         premise the framework asserts rather than derives.
RULE     apply the test — CAN IT BE FALSE? If the carrier either has it or does not, it is
         DATA and belongs in brackets. If the framework asserts it and reality might not
         comply, it is a COMMITMENT and belongs in an explicit hypothesis on the theorems
         that need it. NEVER bundle a commitment into a class. Rollout is AS-TOUCHED: new
         and edited commitments use the hypothesis form now; where an existing class carries
         one, add a companion explicit-hypothesis theorem rather than refactoring.
COST     a commitment in brackets reads as data, which is how `da1_closed_concrete` was cited
         for self-execution for months. This is the only defence that requires nobody to
         remember anything — a signature simply is what it is.
READ     tools/process/commitments-in-hypotheses.md

## R-GATED  Five conventions are CHECKERS now. Each blocks at push.
TRIGGER  you are writing a POV claim, declaring a `class`/`structure`, adding a prose block or
         docstring, closing a self-exemption hole, deleting a `*_baseline.txt` line, or
         WRITING ANY FILE TO DISK.
RULE     a POV claim declares its KIND (COINCIDENCE · INVERSION · DRIFT · CARRIER · INVARIANT)
         and STATUS via `Statement:`/`Reading:` — there is no slot for DENYING a reading
         (`check_pov`). A requirements class is informative only if something FAILS to be a
         member: build the trivial witness or prove you cannot (`check_classes`). Short header,
         statement per declaration, prose never exceeds code (`check_prose`). A guard protects
         a PROPERTY, not a hole — enumerate EVERY route (`guards.py`). Removing a baseline
         entry owes a `/claim-review` and FAILS CLOSED, because no checker can tell content
         GONE from content MOVED (`check_frozen`). Verify every file written:
         `python tools/verify/check_encoding.py <path>` — "is it UTF-8?" is the WRONG question
         and returns PASS on double-encoding; prefer the Write/Edit tools and keep non-ASCII
         out of `.ps1` source.
COST     each was a CONVENTION that leaked before it was a checker. A baseline is DEBT, not a
         decision — shrink it as files are touched, never grow it deliberately.
READ     tools/verify/README.md

## R-CONTROLS  Every brief carries the control objects and "name your first unjustified step".
TRIGGER  you are writing a brief that BUILDS or REVIEWS a class, a claim, or a construction.
RULE     issue the controls as a standing set — objects satisfying the same inputs for which
         the conclusion is FALSE — plus the instruction to NAME THE FIRST STEP THAT IS NOT
         JUSTIFIED. `Unit`/`PUnit` kills any algebraic signature; `Empty` kills anything with
         a `bot` field; `Bool`, `Fin 3`, `ℕ → ℕ` kill "bites at two or more points"; the
         corpus's own `trivialZPSemilattice`, `trivialSelfApp`, `trivialValBridge`,
         `trivialValuationStructure` kill membership-as-an-argument; the constant map `_ ↦ ⊥`
         and the always-true relation kill self-application and periodicity; ℝ kills any claim
         the snap is available in a general ordered carrier. VERIFY A CONTROL EXISTS BEFORE
         NAMING IT.
COST     `Empty` is a two-sided trap — "the finite carriers are exactly the subsingletons"
         shipped as a bedrock defect because the true statement needed INHABITED subsingletons,
         and the inverse error claimed non-members "abound" when inhabitation is the sole
         obstruction. And a brief citing a control that does not exist is worse than none: the
         agent reports it could not build the witness, which reads as evidence of teeth.
READ     tools/process/gated-conventions.md

## R-BRIEF  A rule that must not be violated belongs in the BRIEF, never only in memory.
TRIGGER  you are delegating to a spawned agent.
RULE     carry the relevant rules into the brief VERBATIM — a spawned agent receives this file
         and the memory INDEX, but never memory BODIES, so a rule living in a memory body
         reaches it as one line among a hundred. Always include: draft from source, never
         describe a source you have not read; start new `.lean` files from
         `.claude-local/templates/`; never write a bare "bottom" — say which level; the literal
         `ε₀ = 0` only as a guard or a theorem argument; standard mathematical term first, ZP
         shorthand after; verify an API exists before naming it; never delete a Lean file a
         subagent produced; NO SCRATCH FILES IN THE REPO — the scratchpad, never the tree; and
         reviews are READ-ONLY on the working tree, writing only their signal and findings note.
         An agent needing commits works in `worktree(action='add')`, never the shared checkout.
COST     a subagent invented a detail about a cited paper while that exact rule sat in its
         memory index. And "restore the tree" and "preserve the tree" are different
         instructions: a review agent hard-reset three times, destroyed an uncommitted edit,
         and correctly verified the tree was clean — which WAS the destruction.
READ     tools/process/gated-conventions.md

## R-TOLEAN  Anything convertible from prose to Lean MUST be converted.
TRIGGER  you are about to write a sentence making a claim a declaration could carry.
RULE     write the declaration and leave ONE line at the site. Three tiers, lowest first:
         (1) an `example` that FAILS TO COMPILE when the claim is wrong — now required for
         `Reading:` too wherever the reading is checkable, and a reading is checkable whenever
         it claims STRENGTH, SCOPE or GENERICITY; (2) emitted output (`#print axioms`,
         `#check`); (3) prose, only for interpretation carrying no mathematical content.
         Prefer an anonymous `example` over a named decl — it declares nothing, so it owes no
         `#print axioms` entry, no `ssot.json` row and no SJV sync. Put the `example` AFTER
         the `#check` it qualifies, never between the gloss and the `#check`.
COST     `IO.println` of hand-written English is tier 3 wearing tier 2's clothes — the machine
         echoed a FALSE sentence, exit 0. And the `example` must not itself be generic: ask
         what it EXCLUDES relative to the claim. `Subsingleton (α ≃ PUnit)` elaborates for
         every type, so it witnessed nothing — but where the claim IS a universal, a generic
         witness is the content, not the defect.
READ     tools/process/prose-to-lean.md

## R-ADJACENT  When the answer is already proved, the deliverable is a POINTER, not a theorem.
TRIGGER  a question arose and you are about to write a new declaration to answer it.
RULE     ask in order: is it proved in this corpus already? is it in Mathlib? is the only
         gap that nobody wrote it where the question gets asked? If the last, write it
         THERE — ONE LINE of consequence at the site, plus a pointer to the canonical home.
         Never a bare pointer, and never a paraphrase. THE TEST: would this sentence become
         false if the canonical statement changed? If yes it is a copy — replace it with a
         line and a pointer. Never enumerate in prose what an artifact defines — counts,
         field lists, "the N conditions". Point, name the load-bearing member, stop. A
         DATED survey is legitimate; a completeness claim is not.
COST     adding an elementary instantiation is what the prior-art gate keeps catching, and a
         paraphrase goes stale the instant the original moves — 10 of 25 sites citing `l_inf`
         paraphrased it, and one rewrite falsified four of them immediately.
READ     tools/process/unstated-adjacency.md

## R-DETERMINISM  Single-valuedness is the obstruction, never the fixed point.
TRIGGER  you are about to write prose about why the bottom cannot move, or about the
         halted / self-looping / stepping-onward trichotomy.
RULE     attribute the obstruction to the step being a FUNCTION, not to the presence of a
         self-loop. A function admits at most one successor; a RELATION can loop at `s` and
         reach elsewhere. Under a function, halted and self-looping share a FATE, so the
         trichotomy is genuinely three-valued only in the non-deterministic setting — the
         function-vs-relation choice is how the framework encodes that modality. Say so.
         Non-determinism buys the POSSIBILITY, never the occurrence.
COST     this was re-derived four separate ways in one session; and "nothing else encodes the
         modality" is too strong — `carry` is a function with no fixed point anywhere whose
         observable projection never changes, which is a fact about a quotient, not determinism.
READ     tools/process/determinism.md

## R-TWOPOLE  Every face of the bottom has TWO readings. Build both, concurrently.
TRIGGER  you are starting fresh development, a face is stuck, or a claim needs an extra
         assumption to close.
RULE     run both, never in sequence: Q1 — where is the zero that runs to infinity? Q2 —
         what is the one-way arrow, and what does it look like run BACKWARDS? If either has
         no answer, the piece is not part of the framework yet; record that as a finding.
         Run it on METHOD too: state the claim from the other side, and ask what words the
         corpus would use if it DISAGREED with you — a single-polarity search has a blind
         half. When flipping genuinely gains nothing, say INVARIANT (the ratified null case)
         rather than forcing a second pole. Call out where Tim's read is load-bearing.
COST     a missing pole shows up as a bridge you cannot formalize — ZP-K implemented only the
         EMPTY reading, so the step to forced execution stayed a commitment rather than a theorem.
READ     tools/process/two-pole-test.md

## R-REVALIDATE  A sentence fixed three times is a CLAIM defect. Measure it; do not redraft.
TRIGGER  the same sentence or `--target` has been re-fixed three times, or the gate round
         reaches 3 — `gate_round.py` prints the protocol at that point.
RULE     stop editing. Name the claim in one line without its framing; ask what would settle
         it and whether anyone did that; probe it in the scratchpad; then restate to exactly
         what was measured, restate as an explicit conjecture, or DELETE the sentence —
         deleting is legitimate and often correct. Record what the MEASUREMENT showed, never
         that you re-worded something. MODAL claims are the high-risk class: ACCIDENTAL is
         proved only by exhibiting the clean proof, ESSENTIAL only by a reduction to a taboo,
         and `#print axioms` follows the STATEMENT, so measure the type, not just the theorem.
COST     the gates check WORDING against SOURCES — they cannot see an unmeasured claim and
         will pass one forever. Six versions and four gate rounds missed one; a probe found
         it in a minute.
READ     tools/process/claim-revalidation.md

## R-NOTINLIB  "Not in the library" is a CLAIM. Probe it before you believe it.
TRIGGER  you are about to write "not in Mathlib", "the corpus does not have", "no instance
         exists", or any dated survey negative.
RULE     a failed `#synth` or grep is evidence about YOUR PROBE, never about the library.
         Confirm the name imports and elaborates; re-run with universes explicit; ask whether
         it DECOMPOSES into pieces that are present; remember attribute-generated siblings
         have no source line, so `#check` is the authority and grep is not. Run THREE
         phrasings varied along axes, never synonyms: POLARITY (how the corpus would say it
         if it DISAGREED with you) · PART OF SPEECH (the verb that builds it, not the noun) ·
         VOCABULARY (the domain's words) · DISPLAY (never conclude absence from TRUNCATED
         output — re-run untruncated or print `file:line` and open the hits). Then write
         "not located as of &lt;date&gt;, searched as follows" — never "absent".
COST     three recorded negatives were false and had already shipped into docstrings as
         measured fact; and correcting them turned "one of four hypotheses holds" into three.
READ     tools/process/not-in-the-library.md

## R-LOOPCAP  Stopping is a decision about SEVERITY, never a wait for silence.
TRIGGER  a review gate has returned findings and you are deciding whether to iterate again.
RULE     ask only: did this round find anything BEDROCK? BEDROCK — a violated core invariant,
         a fabricated claim about a source, a false premise carrying a conclusion — gets up to
         5 rounds and must not ship. ORDINARY — citation scope, a mischaracterized lemma,
         hedging, wording — gets 2, then STOP and push normally. Run `gate_round.py show` for
         the live caps; never maintain a prose copy of them. A STOP-ORDINARY reviewer WRITES
         its signal, so nothing is bypassed. EDIT AFTER A STOP ⇒ RE-SIGN; do not want another
         round ⇒ do not edit. Prose about PREVIOUS STATES is redundant — apply the strip test,
         state the live rule positively, and let the commit message narrate.
COST     the cap's licence assumes findings stay outstanding; acting on them creates NEW
         unreviewed prose — four of one round's six findings landed in the one file no gate
         had seen, which existed only because it was edited after the gates finished.
READ     tools/process/review-loop-cap.md

## R-TRUNC  Never truncate a hook-running command; never write a `--no-verify` fallback.
TRIGGER  you are about to put `| head`, `| grep -q`, `| grep -m`, `| Select-Object -First N`
         or any early-exiting consumer around a command that runs a gate — or to chain
         `|| ... --no-verify`.
RULE     redirect to a file and read it: `python tools/verify/batch.py prepush > log 2>&1`,
         then open the log. `--no-verify` is a separately-typed decision, never a fallback and
         never chained. If a push is blocked, read the reason and fix it — the block is the
         control working.
COST     BOTH bypasses succeed SILENTLY and the push looks green: the identical push exited 1
         bare and 0 through `| head -5`, because the hook died of SIGPIPE before its `exit 1`,
         and the review-signal check runs LAST. A twelve-file push with a stale signal reached
         `origin` that way.
READ     tools/process/push-gate-bypass.md

## R-STAGE  Stage NAMED PATHS. Never `-A` on the main repo.
TRIGGER  you are about to stage anything.
RULE     `stage(paths=['a.lean','b.md'])` — the specific paths you edited. Then
         `read(op='status', args=['--short'])` and confirm every staged path is one you meant
         to touch; if an unexpected one appears, find out where it came from before committing.
         `.claude-local` is exempt and bulk staging is its documented flow.
COST     background agents write to this checkout concurrently, so the tree is not a stable
         snapshot — a review agent's scratch probe was swept into a commit that way and is in
         the permanent history. `gitRobot.stage` now refuses `-A` outright, so there is nothing
         left to remember.
READ     tools/process/staging.md

## R-ER  Editorial review completes BEFORE the commit that touches document prose.
TRIGGER  you are about to commit a change to a build script's prose, a README/GUIDE/RELEASES/
         register edit, or any root `.md` other than `CLAUDE.md`.
RULE     run `/editorial-review` in a FRESH agent — same-session self-review does not satisfy
         it — and PASS IT THE FILE PATHS EXPLICITLY. On FAIL, clear every kill-list item before
         committing. A FAIL the agent RECORDS ITSELF in the verdictLedger (`record.py --step
         editorial`); a PASS it reports to the CALLER, who records the agreement or takes a
         signature. The prose signal files are RETIRED — nothing reads them.
COST     `MIG-3`: pre-commit mode discovers its own scope with a now-denied git call, and the
         denial FAILS OPEN — the empty result reads as "nothing staged", the brief falls back to
         Full Scan, and it still writes a signal hashing whatever it happened to open.
READ     tools/process/review-gates.md

## R-AR  Adversary review completes BEFORE anything reaches an external reader.
TRIGGER  you are about to push prose, send an email, post or edit a GitHub Discussion or Issue,
         or surface any content outside this repository.
RULE     ask Tim explicitly: "Adversary review complete for this content?" and WAIT for
         confirmation — never self-assess whether review is needed. If it has not run, offer
         `/adversary-review` first. It must be a separate adversarial context, never this one.
         A FAIL the agent RECORDS ITSELF in the verdictLedger (`record.py --step adversary`);
         a PASS it reports to the CALLER. The prose signal files are RETIRED. Only after explicit confirmation may the public-facing action execute.
COST     docstring and build-script prose was pushed before review ran, and the review then
         found two further precision errors in already-committed content.
READ     tools/process/review-gates.md

## R-PRIORART  Search BEFORE you build, and the gate runs after.
TRIGGER  you can state the claim in one sentence of standard mathematical English and are
         about to write Lean; or a synthesis layer is created, its central claim revised, a
         layer prepared for outreach, a reviewer asks "have you seen X?", or a new `.lean`
         file / >=50 net new lines lands.
RULE     three steps, ~10 minutes, BEFORE building. (1) grep our own corpus. (2) grep the
         pinned Mathlib for the CONCEPT — and if the claim is a Lean statement, RUN `exact?`;
         it searches statement SHAPE, not names, and reaches attribute-generated siblings
         that have no source line. (3) one literature search, run as the four-rung LADDER:
         `.claude-local/papers/` → `theoremsearch` → the open web → RETRIEVE THE FULL
         DOCUMENT. Three phrasings minimum at rung 2; ignore its similarity score; its null
         is UNINFORMATIVE. Rungs 1–3 are DISCOVERY, only rung 4 is VERIFICATION — a returned
         theorem body is not a passage in hand. Standard framing, once found, is ADOPTED, not
         noted and worked around; check purity before swapping a proof. `/prior-art-review`
         is the deep gate, a fresh agent, and it records its verdict in the verdictLedger.
         If you cannot yet state the claim, build first — then SEARCH BEFORE PROMOTING,
         because a survey that became a theorem restarts the clock.
COST     an uncited closest prior art reads as unaware — the crank-triage failure. And
         searching first gets you MORE: one round yielded a stronger theorem than our own
         claim, a purer proof, free lemmas, and the standard NAME for a thing described longhand.
READ     tools/process/prior-art.md

## R-CONTEXT  What this repository is, and where a file belongs.
TRIGGER  you are orienting in this repo, or deciding where a new file goes.
RULE     this is a mathematical PUBLICATION repository first: the PDFs and the Lean corpus
         under `ZeroParadox/` (indexed by `ZeroParadox/MANIFEST.md`) are the point, and the
         tooling exists to keep them honest. Formal documents live at the root under FLAT,
         version-free filenames — versions live in `register.md` and each PDF's title block,
         never in a filename. Superseded versions are NOT archived: overwrite the flat root
         PDF in place and let history plus each release's Zenodo snapshot be the record. Do
         not recreate `historical/`, and never rewrite history to purge old binaries —
         SHA-pinned permalinks and DOI-referenced commits depend on them. `.claude-local/` is
         its OWN repository with a private remote: commit AND PUSH it; the parent additionally
         ignores the path. Prose exists only to restate mathematics accessibly; finalized
         documents are structured as an ontology; completed work is committed immediately.
COST     `historical/` drifted a month stale while the snapshots did not; and reasoning from
         the ignore entry alone concludes the only copy is on disk, which is how three commits
         sat unpushed on one machine.
READ     tools/process/repository-layout.md

## R-RELEASE  A release is Tim's action. An agent's role ends at a green gate.
TRIGGER  Tim initiates a release, or you are about to draft a release body or a tag.
RULE     `python tools/verify/check_release_ready.py <tag>` must EXIT 0 and its judgement
         checklist must be confirmed BEFORE the release body is drafted. It verifies the
         deterministic preconditions — Engineer's Takes filled (recursive glob over
         `ZeroParadox/**/*.lean`), build-script hashes against `register.md`, the
         `LEAN_CUSTOM_REGISTRY` invariant, `.zenodo.json` valid and its description current,
         no conflict markers, a `## <tag>` entry in `RELEASES.md`, every linked PDF present.
         **NO RELEASE WHILE `DEFECTS.md` IS NON-EMPTY.** Then STOP: creating the release is
         Tim's command, never an agent's. Major = a new formal layer or a theorem status
         change; minor = a substantive feedback round or accumulated updates. Never release
         per-PR. A Lean-only milestone is an explicit QUESTION for Tim, not an automatic
         trigger either way.
COST     a release mints a PERMANENT Zenodo DOI and four already carry latent flaws that
         cannot be withdrawn. Deposited FILES are frozen; record METADATA can still be
         corrected in the Zenodo UI, so a wrong release description is fixable and a flaw
         inside a published PDF is not.
READ     tools/process/document-workflow.md

## R-REGISTER  `register.md` is canonical. Update it FIRST, then propagate.
TRIGGER  you are bumping any document or companion version, or editing a build script.
RULE     order matters: (1) `register.md` — formal version, filename, companion version;
         (2) README.md's Framework table, the single derived copy. That is the whole
         propagation path. GUIDE.md carries NO version numbers, deliberately — never "sync"
         one into it; that is a regression to revert. Any build-script change takes all four
         steps in ONE commit: edit, bump the internal version, rebuild the PDF, recompute the
         `formal:` / `comp:` hash token in `register.md`. A document's own version appears in
         exactly ONE rendered place, the subtitle meta line — no self-changelogs, no
         `[new in v1.7]` tags; cross-document citations are exempt.
COST     a hash mismatch does not mean "rebuild needed", it means the version bump was
         SKIPPED — do not rebuild without incrementing. `check_hashes.py` compares
         `register.md` against README on every run and found five stale rows on its first.
READ     tools/process/document-workflow.md

## R-DIAGRAM  Diagram bounds are build-enforced; internal collisions are not.
TRIGGER  you are adding or editing a `Drawing` in any companion build script.
RULE     never derive `cy` from `dh` when the diagram holds fixed-size elements — use a fixed
         numeric `cy`. Keep `max_y < dh - 10` and `min_y > 5`. Drop internal title strings
         that duplicate the caption. Express `dh` in inches with a comment giving content top
         and bottom. `zp_utils` validates every `Drawing` at `doc.build()` and HARD-FAILS on
         escape, so a forgotten check can no longer ship one.
COST     the bounds gate cannot see INTERNAL collisions — two elements overlapping inside the
         box. Every build prints a diagram-page report; eyeball those pages on any
         diagram-touching build before commit.
READ     tools/process/document-workflow.md

## R-COMPANION  A formal document and its companion move together.
TRIGGER  you updated a formal document, or you are touching any rendered PDF text.
RULE     review the companion IN THE SAME SESSION and bump its internal version in the SAME
         commit; companion versions are independent of formal versions, and what matters is
         that the companion is not materially stale. Read
         `scripts/PDF_Rendering_Standards.md` before building ANY PDF. When a vocabulary
         problem is surfaced by anyone, update `.claude-local/vocabulary_reference.md` in the
         same session and log the term — both directions, wrong-term and needs-a-gloss.
COST     a general reader meets the framework in the companion, so a stale key-result box
         misdescribes what is proved.
READ     tools/process/document-workflow.md

## R-SCRIPTS  `scripts/` is the build scripts' only home. There is no mirror.
TRIGGER  you are editing, adding, or looking for a PDF build script.
RULE     edit the file in `scripts/` and commit it like any other source file — there is no
         copy step. A new script gets a row in `scripts/README.md` in the same commit. The
         fonts ship beside them under `scripts/fonts/` with their licences, so a clone can
         actually build; if a font is added or replaced, read its `name` table id 13 and ship
         whatever licence it declares. Five scripts remain private-only and none emits a
         tracked artifact — `scripts/build_dictionary_map.py` imports one and says so rather
         than raising `ModuleNotFoundError`.
COST     the retired mirror asked a human to remember a copy step while `register.md`
         fingerprinted only the PRIVATE copy — so the PUBLISHED script sat outside the
         integrity check and drifted three months unnoticed. A mirror plus a discipline adds
         a way to be wrong and removes the way to detect it.
READ     tools/process/repository-layout.md

## R-LEANPDF  Verify a Lean encoding at the source before stating it anywhere.
TRIGGER  you are about to state a Lean type name, constructor, or theorem STATUS in a PDF,
         companion, README, or correspondence.
RULE     open the actual `.lean` file and check; never rely on memory or prior documentation.
         No automated checker covers status labels or encoding descriptions — the session
         workflow IS the mechanism, so cross-check the PDF script and companion in the same
         session as any Lean status change. File references in CHECKABLE surfaces carry the
         FULL repository path (`ZeroParadox/<Domain>/<Name>.lean`); declaration names stay
         BARE and unprefixed; flowing companion prose may use a bare basename. Rollout is
         as-touched, never a retrofit round.
COST     a full path fails LOUD when a file moves; a bare basename fails SILENT — plausible
         and pointing nowhere. `Fin 2` survived in three surfaces after the Lean moved to
         `OntologicalStates`, until a reviewer asked.
READ     tools/process/document-workflow.md

## R-SHELL  This is Windows. PowerShell syntax, and never prepend `cd`.
TRIGGER  you are about to run a shell command or search for a file.
RULE     use the `PowerShell` tool, not Bash with Unix commands. Use `Glob` for file discovery
         — never `find`, which hangs here. `Get-ChildItem` not `ls`; `Move-Item` not `mv`.
         Backslash paths in PowerShell, forward slash in Lean/lake config. The working
         directory is already the repo root: never prepend `cd` or `Set-Location`. Every call
         invoking an external process (a build script, `lake build`, `python <script>`) uses
         `timeout: 300000`; if it times out, diagnose rather than retry blindly.
COST     a prepended `cd` produces a command string that misses the allowlist and triggers an
         avoidable permission prompt.

## R-INDEXES  README is the formal index; GUIDE is the general-reader hub.
TRIGGER  a document is versioned up, an open question closes, a claim's status changes, or a
         document is added or archived.
RULE     audit BOTH files. Preserve the section order in each — do not add top-level
         sections, reorder, or drop terminal ones without agreement. `check_hashes.py`
         mechanically compares `register.md` against README's Framework table on every run,
         joined on the PDF FILENAME, never the `ZP-X` code (four register rows begin `ZP-J`).
         Check GUIDE's link TARGETS resolve, and never sync a version into it. Where a
         document's STATUS could mislead — speculative, superseded, a development artifact —
         say so in its own opening because it is TRUE, not because a linkage rule fired.
COST     the retired transparency-notice rule bound seven files and exactly one honoured it,
         because it measured "is this linked?" when what matters is "would a reader be misled
         about why this exists?" Those came apart twice.
READ     tools/process/indexes-and-superseding.md

## R-NAMING  Label a result by whether it is the section's central claim or its infrastructure.
TRIGGER  you are naming or relabelling a result in any formal ZP document.
RULE     ask: is this the CENTRAL claim of its section, or infrastructure for something else?
         **Theorem** — the primary result, driving the dependency chain (T3, T-SNAP).
         **Proposition** — rigorously proved but subsidiary. **Lemma** — a stepping stone.
         **Corollary** — follows immediately, no substantial work. **Conditional Claim (CC)** —
         holds only given an explicit modelling commitment. **Design Principle (DP)** — chosen,
         not derived. **Remark (R)** — context, no proof.
         Readable names are ADDITIVE, never eliminative: CC-2 is "the Quine atom (CC-2)",
         glossed once as the self-containing bottom; MC-1 is "the bottom family" and gets NO
         new readable name, because its object already has one — the diagonal fixed point.
         Keep every formal handle; never rename or remove an identifier. AX-1 is Theorem
         T-SNAP — never call it an axiom.
COST     the prefixes go stale as status changes and the label then misdescribes what is
         proved: CC-2's "Conditional Claim" outlived its own upgrade, and MC-1's numerical
         identity is RETIRED as ill-typed — `x = y` across distinct categories was never a
         well-formed proposition, so it was never a commitment either.
READ     tools/process/naming-and-labels.md

## R-ISSUES  Public issues are transparency, not a request for validation.
TRIGGER  you are about to file, or are being asked about, a public GitHub Issue or Discussion.
RULE     file genuinely unresolved framework open questions and substantive technical
         questions that review left open — framed as specific, honest about uncertainty, and
         standalone without requiring knowledge of the framework. NEVER file anything sourced
         from private correspondence, reviewer identity or feedback, outreach strategy or
         drafts, or editorial decisions; those belong in `.claude-local/`. Record every
         outreach item's external identifier in `.claude-local/outreach/tracker.md` AT THE
         MOMENT it is created or sent — a Discussion or Issue `#N`, a full URL, a date plus
         recipient for email, a stream and topic, an arXiv id. If an identifier is missing,
         add it before doing any other work in that session.
COST     issues are the public record of what is open or contested; an issue that reads as
         seeking validation converts a transparency mechanism into an outreach one.
READ     tools/process/naming-and-labels.md

## R-FRAMEWORK  The layer dependency order, and the one substantive commitment.
TRIGGER  you need the framework's shape, or are about to describe a layer's status.
RULE     dependency order: **ZP-A** (lattice) → **ZP-B** (p-adic) → **ZP-C** (information) →
         **ZP-D** (state) → **ZP-E** (DA-1 / T-SNAP). **ZP-G** (category) → **ZP-H** (bridge)
         is self-contained — conceptually downstream of ZP-E, formally independent. Each
         formal document has a paired illustrated companion. AX-G1 and AX-G2 are grounded,
         not novel. **AX-B1 is the framework's ONE substantive modelling commitment** —
         discrete Boolean existence, not a continuum of partial states — so never call it
         "directly verifiable" or "not a novel commitment"; the `decide` proof only checks
         the two states are distinct GIVEN the two-element type. AX-1 is Theorem T-SNAP.
COST     the ZP-C forcing lemmas discharge the no-half-state worry but force only the
         >=2-outcome lower bound; the residual commitment is DISCRETENESS, which they do not
         eliminate and which the reals lack — the snap fails there (`f_snap_impossible`).
READ     tools/process/repository-layout.md

## R-HANDOFF  "Update the handoff" is a compound action defined in the file itself.
TRIGGER  the session is ending, a context switch is planned, or someone says "update the handoff".
RULE     read `.claude-local/handoff.md` FIRST at session start; overwrite it at the end. Two
         parts in order: the THREAD (live orientation for resuming mid-thought), then the
         LEDGER (what was done, the next action, what was deferred). One file, always current.
         The full procedure is PART 0b of that file — do not restate it here; it closes finished
         tickets by MOVING them to `queue/done/`, opens tickets for what was found, COMMITS AND
         PUSHES the private repo, and reports main-repo state.
COST     overwriting is safe only because `.claude-local` is a repo, and that is the step with
         the measured failure history — 120 uncommitted entries, 86 notes never once committed,
         and an unstarted item that vanished for five revisions.

## R-CAPTURE  Capture a high-value insight immediately; the POINTER is the deliverable.
TRIGGER  a structural connection, a cross-domain identification, a derivability conjecture, a
         purity result, or anything that partially closes an open question surfaces.
RULE     write `.claude-local/notes/<topic>_YYYY-MM-DD.md` now, without being asked: the
         insight in plain language, the precise claim, what is formal versus conjectural, the
         status, and links to related notes. THEN WIRE IT to the artifact — a line in the
         `.lean` docstring, `CLAUDE.md`, or a memory — because the note is the draft and being
         pointed at from a read surface is the durable act. Active notes only in `notes/`; open
         work in `notes/future-research/`; history in `notes/archive/`. Prefer KEEP when torn.
COST     only ~10% of 767 notes were ever referenced again, and on one day four findings were
         rediscovered the slow way while the relevant note sat unread. Worse, a note recording
         PENDING work goes FALSE the moment the work is done — never act on a note's
         self-reported status; verify at the artifact.

## R-DEVMODE  Before fresh development, load the subsystem. Do not start from targeted search.
TRIGGER  you are beginning fresh mathematical development.
RULE     `python .claude-local/where.py "<Tim's phrasing, verbatim>"` for ranked folders and
         token cost, `--files` for the list, `--spine` for the always-load core. Then load the
         ~50k spine — the five `#check`-only indexes plus `MANIFEST.md`, `CLAIMS.md`,
         `BOTTOMELEMENT.md`, `SNAP.md` — plus the one or two folders it names. Load two or
         three; it produces a SHORTLIST, not an answer, and it cannot route a concept with no
         corpus vocabulary. Tim's Engineer's Takes are the bridge between his register and the
         Lean body, and all of them together are cheap enough to load wholesale.
COST     every real finding comes from COLLIDING two facts, and you cannot collide facts you
         are fetching one at a time. Not this for error-sweeps: a claim-sweep's unit is the
         RENDERED PDF text, never the source.

## R-LEANDEV  Stub first. Build, commit, then fill proofs one at a time.
TRIGGER  you are creating a new `.lean` file or starting a proof.
RULE     map each symbol to its Mathlib equivalent and identify heavy imports BEFORE writing
         Lean. Write the complete file with every proof `sorry`, `set_option maxHeartbeats
         400000`, and STOP — wait for a clean build. Commit the stub as a rollback point. Fill
         one theorem at a time, building and committing after each. Build as TWO separate
         calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8`, then read the
         log — never combined with `;`. When done: zero errors and warnings, a `#print axioms`
         block per proved theorem inside `section PurityCheck`, README updated, and the SJV
         registry synced (`migrate_batch` → `annotate_many` → `validate` + `verify_integrity`
         → `export_full` to an ABSOLUTE path) in the SAME change. Search Lean files as
         `ZeroParadox/**/*.lean`, never `**/*.lean` — `.lake/` holds thousands of Mathlib files.
COST     heavy import chains (p-adics plus Hilbert space) hang the elaborator, and an unsynced
         declaration re-introduces the registry drift the ontology revamp eliminated.
READ     tools/process/lean-development.md

## R-BRANCH  All work happens on `illustrated`. Sync before you start.
TRIGGER  you are starting a session, or about to make your first edit.
RULE     all Lean and PDF work happens on `illustrated`; `main` is production/public;
         `lake_testing` is RETIRED — never switch to it or push to it. At session start
         `fetch()` then `merge(branch='origin/main', ...)` before making any change, so you
         never edit against a stale base. `merge` is REFUSED while the tree is dirty — that is
         deliberate, and the answer is to commit first or take a worktree, never to force it.
         After ANY merge, `read(op='diff', args=['--check'])` to confirm no conflict markers
         survive. Both `.lean` files and PDF build scripts are first-class here.
COST     a file with unresolved conflict markers commits SILENTLY and corrupts the document.
         That has happened twice on this project.

## License

CC BY-NC-ND 4.0 — share with attribution; no modifications; no commercial use.

