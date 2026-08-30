# Lean development, the session handoff, insight capture, and development mode

**Body for `CLAUDE.md` §§ `R-FRAMEWORK`, `R-HANDOFF`, `R-CAPTURE` and `R-LEANDEV`.**
⛔ **`R-DEVMODE` was RETIRED on 2026-08-27** (Tim: *"it's never fired right"*). The development-mode
section below is KEPT, because the content was never the problem — the trigger was. It now hangs off
`R-EDITLEAN` step 3, which calls `where.py` on a concrete action, and off `R-COREOBJ`, which says load
the subject's whole row rather than one file. The rules are there; the framework structure, the four-fingerprint scan
log requirement, the communication-quality rubric pointer, the notes-folder layout, the
stub-first rationale and the full SJV sync sequence are here.

---

## Framework Structure (for context)

The Zero Paradox is a multi-layer mathematical ontology proving the Binary Snap (⊥ → ε₀) as a theorem. The dependency order of the formal layers is:

**ZP-A** (lattice algebra) → **ZP-B** (p-adic topology) → **ZP-C** (information theory) → **ZP-D** (state layer) → **ZP-E** (DA-1/T-SNAP derivation)

**ZP-G** (category theory) → **ZP-H** (categorical bridge) — self-contained; depends on ZP-E conceptually but not formally.

Each formal document has a paired illustrated companion for general readers. AX-G1 and AX-G2 are the two structural commitments of ZP-G's categorical layer. Neither is a novel commitment: AX-G1 is grounded in ZP-A's bottom element ⊥; AX-G2 follows from ZP-A antisymmetry and ZP-B C3 (topological irreversibility). ZP-G is self-contained by design and states them explicitly within that layer. AX-B1 (binary/discrete existence) is the framework's **one substantive modeling commitment** (discrete Boolean existence, not a continuum of partial states) — do NOT call it "directly verifiable / not a novel commitment" (reclassified 2026-07-15): the `decide` proof (`ax_b1_distinct`) only checks the two states are distinct *given* the two-element type, not the choice of a discrete alphabet over a continuum. The ZP-C forcing lemmas (`pmf_subsingleton_isPure` / `binaryState_exhaustive`, `Information/Surprisal.lean`) discharge the no-half-state worry (leaving ⊥ needs a second outcome) but force only the ≥2-outcome lower bound; the residual substantive commitment is that the outcome space is DISCRETE, not a continuum - which those lemmas do not eliminate and which the reals lack (the snap fails there, `f_snap_impossible`). See the CLAIMS AX-B1 row. AX-1 (Binary Snap Causality) is now Theorem T-SNAP, derived in ZP-E — do not refer to it as an axiom.

## Four-Fingerprint Scan — Decision Log Requirement

When a four-fingerprint scan is conducted (see memory: `feedback_reader_orientation.md`), the session notes file in `.claude-local/notes/` must be updated before the session ends with:

1. **Each item reviewed** — the finding, the decision (FIXED / NO FIX / PENDING), and the version bump if fixed.
2. **Rationale for no-fix decisions** — e.g., "already addressed in vX.Y", "standard result in the relevant literature", "Lean scope already disclosed."
3. **Any technique notes** — e.g., "read the Lean file before fixing to confirm the actual proof argument."

This log is the authoritative record of what has been reviewed and why. Future sessions must read it before starting a new scan pass to avoid re-reviewing already-settled items.

**File convention:** `.claude-local/notes/framing_scan_YYYY-MM-DD.md` — one file per scan pass, named by the date the scan was run. The decision log lives at the bottom of that file under a `## Decision Log` header.

**Standing rule:** A scan pass is not complete until all reviewed items have a decision recorded. "PENDING" is a valid decision for items deferred to a future session.

## Communication Quality Feedback

During working sessions, apply the Communication Quality Rubric to evaluate Tim's statements about the framework in real time. Flag anything scoring **7 or below** on the composite scale (35% terminological accuracy, 35% structural accuracy, 15% consistency, 15% clarity). The full rubric with scoring tables and calibration notes lives at `.claude-local/communication_quality_rubric.md`. Key terms requiring extra care: ⊥ (three-way identification), T-SNAP (theorem, not axiom), DA-1 (derived proposition, conditional on DP-2), DP-2 (grounded in D7 — not freely chosen), CC-1/CC-2 (both now derived via ZP-J, not freestanding commitments).

## Session Handoff File

`.claude-local/handoff.md` is the standardized session state file. At the start of every session, read it first. At the end of every session (or before a planned context switch), overwrite it with the current state. It has **two parts, in order**: first, **keeping the conversation thread alive** — the live orientation a fresh session needs to resume mid-thought rather than cold-start; then the **factual ledger** — what was just done, the immediate next action, and anything deferred. The thread leads, the ledger follows; the components, structure, and rationale of the thread part are defined privately (memory `feedback_handoff_thread_first`). Always use this exact filename — one file, always current, always overwritten.

⭐ **"UPDATE THE HANDOFF" IS A COMPOUND ACTION, AND THE PROCEDURE IS DEFINED IN THE FILE ITSELF —
`.claude-local/handoff.md` PART 0b.** It closes finished tickets by MOVING them to `queue/done/`,
opens tickets for what was found, **commits the private repo**, and reports (never pushes) main-repo
state. **Do not restate the six steps here** — one definition, and it lives where it is read first.
⚠ It is loaded onto this phrase deliberately (Tim, 2026-08-20): the git hygiene this project keeps
failing at has no reliable trigger, and *"update the handoff"* is one that actually fires.
⚠ **Overwriting is safe ONLY because `.claude-local` is a git repo — and that is the step with the
measured failure history.** 2026-08-20: 120 uncommitted entries, 86 of them notes never once
committed, with 42- and 21-day gaps. An unstarted item vanished from this file for five revisions and
was recovered only because Tim remembered it existed.

## Load the whole subsystem before fresh development. (Tim, 2026-07-31.)

⛔ This was `R-DEVMODE`, **retired 2026-08-27** as a rule because its trigger never fired. Everything
below stands as GUIDANCE, reached from `R-EDITLEAN` step 3 and `R-COREOBJ`.

**Before fresh mathematical development, read the whole relevant subsystem. Do not start from
targeted search.** This is scoped to *development*; error-sweeps have their own discipline and a
different unit — for prose that ships, the sweep unit is the RENDERED PDF text, never the source
(`R-DEFECTCLASS` carries that now).

```
python .claude-local/where.py "<Tim's phrasing, verbatim>"     # -> ranked folders + token cost
python .claude-local/where.py --files "<phrase>"               # + the file list
python .claude-local/where.py --spine                          # what the always-load spine costs
```

Then load: **the ~50k spine** (the five `#check`-only indexes — `BottomCannotBe`, `SnapCannotBe`,
`Epsilon0CannotBe`, `DiagonalFixedPoint`, `ChoiceCannotBe` — plus `MANIFEST.md`, `CLAIMS.md`,
`BOTTOMELEMENT.md`, `SNAP.md`) **plus the one or two folders it names.** Most subfolders are 5k–66k
tokens; the largest, `Valuation/`, is ~123k. Total lands at 80k–170k, comfortably resident.

**Why, and it is not about catching errors.** Every real finding of 2026-07-31 came from **colliding
two facts** — `selfApp` fixes ⊥ *and* `α ↦ ω^α` does not; ⊥'s down-set is empty *and* R1 forbids
subtraction; `nfp` is seed-independent *and* the corpus says "⊥ the seed". **You cannot collide facts
you are fetching one at a time.** Targeted search returns the fact you asked for and nothing adjacent,
which is precisely what a collision needs.

**Two honest limits.** (1) `where.py` scores term distinctiveness — it produces a *shortlist*, not an
answer, and on one of four test queries the right folder ranked third. Load two or three. (2) It
**cannot** route a genuinely new concept with no corpus vocabulary; fall back to `--spine`.

**Tim's Engineer's Takes are the bridge, and `where.py` reports them.** The Lean body says `cx`,
`member`, `infinitude`; Tim says *"bottom itself is infinitely complex."* The Takes are the only
corpus written in the register a question arrives in, they are attached to the file they describe, and
**all of them together are ~16k tokens — cheap enough to load wholesale.** Measured 2026-07-31: on four separate questions the answering
Take was found *after* the work, never before.

**Not this, for error-sweeps.** A claim-sweep's unit is the **rendered PDF text**, never the source —
a claim survived four vocabulary changes and one split across two Python string literals. See
`vocabulary_reference.md`.

## High-Value Insight Capture — Standing Rule

Any observation made during a session that could lead to a new theorem, new layer,
new conjecture, or significant axiom relationship must be written to `.claude-local/notes/`
immediately — without waiting to be asked. Do not defer to the end of the session.

**Triggers — capture automatically when any of these arise:**
- A structural connection between two existing layers that hasn't been formalized
- An identification of two mathematical objects as "the same fact in different languages"
- A conjecture about axiom derivability or necessity (e.g. deriving a class field from
  upstream structure)
- An argument that could become a new ZP layer or bridge layer
- A DC-free, choice-free, or purity result not yet in a Lean file
- A new justification for an existing axiom or design principle
- Any observation that directly answers or partially closes an open question in the framework

**What the note must contain:**
1. The insight in plain language (one paragraph — legible without session context)
2. The precise mathematical claim (what exactly is being asserted)
3. What is formal vs. what is still philosophical/conjectural
4. Status: open conjecture / partial proof / architecture clear but unbuilt / etc.
5. Connected notes (link to related `.claude-local/notes/` files)

**File naming:** `.claude-local/notes/<topic>_YYYY-MM-DD.md`

**The test:** Would a future session miss something important if this wasn't written down?
If yes, write it now.

### But the note is the DRAFT. The POINTER is the deliverable. (Measured 2026-07-31.)

**Writing the note is not the durable act; being pointed at from a read surface is.** Measured across
767 notes: **only ~10% were referenced from anywhere a future session actually reads** — `CLAUDE.md`,
`.claude-local/handoff.md`, a `.lean` docstring, or a memory file. The other ~90% were write-only. On
the same day, four separate findings were rediscovered the slow way while the relevant note sat
unread, and every piece of context that *did* reach the session came from a Lean docstring, this file,
or a memory — **not one came from a note.**

So the rule above is half a rule. After writing the note, **wire the finding to the artifact**, at the
site the reader lands on — which is what § "unstated adjacency" already demands of findings generally
(*"write it there, at the site the reader lands on, not five sections away"*). Applied to notes: put
the sentence in the `.lean` docstring / `CLAUDE.md` / the memory, and let the note hold the long form.

**⚠ AND A NOTE RECORDING PENDING WORK GOES FALSE THE MOMENT THE WORK IS DONE.** This is worse than
going unread: an unread note is inert, a stale one actively misleads. Measured 2026-07-31:
`zpa_launders_axb1_as_a_metric_result_2026-07-26.md` says **"Not yet fixed"** of a bedrock defect that
ZP-A **v1.21 struck days later** — and a triage pass nearly reopened it on that basis. Two sibling
notes say "pending" and "status at interruption" and are equally unverifiable. **Never act on a note's
self-reported status; verify at the artifact.** If a finding is a *defect*, its home is a gate finding
or a fix, never a note that cannot know when it stops being true.

**Folder layout (established 2026-07-31, 767 notes triaged):**
- `notes/` — **active only.** Live conventions, indexes, corrections that must not be re-introduced.
- `notes/future-research/` — **open work.** A stated conjecture, an identified gap with a route, an
  "architecture clear but unbuilt". The test: *could a future session do mathematics from this?*
  **Read this folder when choosing what to work on.**
- `notes/archive/{gate-findings,resolved,superseded}/` — historical. Gate reports are an audit trail:
  write them, never expect to read them.

When triaging, **prefer KEEP when torn** — this is a research record and over-archiving is the
costlier error.

## Reviewer Feedback Tracking

Reviewer feedback and correspondence are tracked in `.claude-local/feedback/reviewer_feedback_tracking.md`. That file is private and gitignored. Do not include reviewer names or feedback details in this file.

## License

CC BY-NC-ND 4.0 — share with attribution; no modifications; no commercial use.


# .claudecodes instructions for Lean 4 development
- Always run lake build as two separate PowerShell calls: first `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8`, then `Get-Content build.log | Select-Object -Last 1` (or with a `-match` filter). Never combine them with `;` in a single call.
- Ignore PDF rendering assets and website build artifacts in the root.
- Always check 'lake-manifest.json' for dependency updates before adding new imports.

- When searching for Lean source files in this project, always use the pattern ZeroParadox/**/*.lean, never **/*.lean. The .lake/ folder contains thousands of Mathlib library files that aren't mine."

# Zero Paradox Project Standards

## Development Branch

All work — Lean 4 proofs and PDF rendering — happens on the `illustrated` branch. This is the single active development branch. `main` is production/public. The `lake_testing` branch is retired; do not switch to it or push to it.

## Operational Rules
1. **Single branch:** All Lean and PDF work happens on `illustrated`. No branch switching required.
2. **Math Workflow:** Verify theorem changes with two separate calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` then `Get-Content build.log | Select-Object -Last 1`.
3. **PDF Workflow:** Use existing rendering scripts and strictly follow the document versioning and archiving conventions defined above.
4. **Transparency:** Maintain the `.claude-local/` folder for in-progress scripts and internal notes as a private "collaboration buffer."
5. **Sync before starting work:** At the start of any session, `fetch()` then `merge(branch='origin/main', reason=...)` before making any changes. Never make edits against a stale base. ⚠ `merge` is **refused while the tree is dirty** — that is deliberate, and the answer is to commit first or take a worktree, never to force it. (Until 2026-08-22 this step said `git fetch` / `git merge` and had been **unexecutable by agents** since direct git was denied.)
6. **Verify no conflict markers after any merge:** Before committing after a merge, run `read(op='diff', args=['--check'])` to confirm no conflict markers (`<<<<<<<`, `=======`, `>>>>>>>`) remain in any file. A file with unresolved markers will commit silently and corrupt the document. This has happened twice on this project.
7. **5-minute timeout on all external tool calls:** Every `PowerShell` or `Bash` call that invokes an external process (PDF build scripts, `lake build`, `python <script>`, long-running `git` or `gh` operations) must use `timeout: 300000` (5 minutes). If the command exceeds this limit, kill it and report back — never wait indefinitely. If it times out, diagnose the cause rather than retrying blindly.
⚠ **STANDARDS 8, 9 AND 10 ARE TIM'S TO RUN — `gh` IS DENIED FOR AGENTS (2026-08-22).** PR creation
and editing, and every GitHub Discussion mutation, reach outside the repository and are governed by
the Adversary Review Gate, which is Tim's decision by construction. **GitHub READS are untouched** —
all the `mcp__github__*` read tools still work, so an agent can still check PR status, read
discussion comments and verify a posted body. The `--body-file` / `-F body=@file` discipline below is
unchanged and still correct; it is the *transport* rule, and it matters exactly as much when Tim runs
the command.

8. **Pull request body — always use `--body-file`:** PowerShell cannot reliably pass multiline PR bodies inline (special characters, arrows, backticks, and asterisks all cause parse errors). Always write the body to `.claude-local\pr_body_<name>.md` first, then create the PR with:
   ```powershell
   gh pr create --title "..." --body-file ".claude-local\pr_body_<name>.md"
   ```

9. **Keep PR description current:** If additional commits are pushed to a branch after the PR is opened, update the PR body to reflect the new content. Update `.claude-local\pr_body_<name>.md` first, then run:
   ```powershell
   gh pr edit <number> --body-file ".claude-local\pr_body_<name>.md"
   ```

10. **GitHub Discussion body updates — always use `-F body=@file`:** Passing Unicode body content through PowerShell string interpolation (`$body = Get-Content -Raw; -F body="$body"`) corrupts multi-byte UTF-8 characters (arrows, subscripts, math symbols). Always write the body to `.claude-local\temp_body.md` first, then pass the file directly:
   ```powershell
   gh api graphql -F query=@.claude-local\mutation_update_discussion.graphql -F id="NODE_ID" -F body=@.claude-local\temp_body.md
   ```
   After every update, verify the live body via `mcp__github__get_discussion` before proceeding to the next thread. This issue was discovered 2026-05-23 when ZP-C (#69) was posted with garbled math.

## File Priority
- Both `.lean` files and PDF build scripts are first-class on `illustrated`.
- All other conventions (versioning, archiving, scripts/ sync) apply as documented above.

## Lean 4 Proof Development: Stub-First Protocol

As proofs grow more complex (ZP-D onward), always use a stub-first approach before writing full proofs. This prevents session hangs caused by heavy import chains and typeclass resolution.

**The workflow for every new ZP-X Lean file:**

1. **Symbol map** — before writing any Lean, map each PDF symbol to its Lean 4 / Mathlib equivalent. Identify which imports are required and which are dangerously heavy (p-adics + EuclideanSpace together, for example, can cause elaborator hangs).
2. **Stub file** — write the complete file with all definitions and theorem statements, but use `sorry` for every proof body. Add `set_option maxHeartbeats 400000` at the top. Do not write proof bodies during the planning or stub step — output the stub file and stop. Wait for a clean build before proceeding.
3. **Build the stub** — run `lake build` and confirm 0 errors on the skeleton. This validates that types elaborate correctly before any proof work begins.
4. **Commit the stub** — commit the sorry-stubbed file immediately after a clean build. This creates a rollback point before any proof work begins.
5. **Fill proofs incrementally** — prove one theorem at a time, building after each. Commit after each theorem is successfully proved. Do not attempt to write all proofs before checking.
6. **Final clean build** — once all `sorry`s are removed, run a final build to confirm 0 errors and 0 warnings, then proceed to the documentation workflow below.

**When to abstract away heavy dependencies:** If a layer imports both p-adic numbers and Hilbert space machinery, consider whether the cross-layer dependency can be replaced with an abstract typeclass or index type (e.g., `Fin (2^k)` instead of `ℚ_[2]`) for the purposes of the proof. Decoupling reduces elaboration load significantly.

## Proof Documentation Workflow

When a ZP-X document is successfully proved in Lean 4, the following steps are **mandatory** before the work is considered complete:

1. **Build clean** — run as two separate calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` then `Get-Content build.log | Select-Object -Last 1`. Confirm zero errors and zero warnings.
2. **Purity check** — add a `#print axioms` block at the bottom of every ZP-X Lean file (inside a `section PurityCheck ... end PurityCheck`), one call per proved theorem. The expected result is `'theorem_name' does not depend on any axioms`. Any kernel axiom that appears (`Classical.choice`, `propext`, `Quot.sound`) must be explicitly noted and justified in a comment in the Lean file.
3. **Update README.md** — add or update a row in the `### Formal Verification (Lean 4)` subsection of The Framework, and update the Question Register row for `Formal verification (Lean/Rocq)`.
4. **Sync the SJV registry (SSOT) — mandatory, see the standing rule below.**
5. **Commit all changes together** on `illustrated`.

### SJV Registry Sync — Standing Rule (mandatory on any Lean declaration change)

**Any change that adds, renames, removes, or splits Lean declarations at HEAD — including a new `.lean` file — must update the SJV `declarations` store and re-export `ssot.json` in the SAME change, never deferred.** The SSOT is only trustworthy if it tracks HEAD 1:1; every un-synced decl re-introduces registry drift (the recurring "SJV is a whole reorg behind" problem the ontology-revamp arc eliminated). Treat this as the same reflex as `lake build` and the purity check.

The sequence (via the SJV MCP; tools reload in any session started after the MCP loaded):
1. `migrate_batch` — `add_new` for new decls (`{qualified, file, namespace, short}`); `reconcile` for renames/moves (id-keyed `new.*` + `disposition`) with `remap_deps=true` (or an explicit `deps` list) so deps edges follow; drops for removed decls.
2. `annotate_many` — ontology tags on new/changed entries (no `domain=[]`; a `role:face` needs an `object`). Refine later via `/tag-review` if unsure.
3. `validate` + `verify_integrity` (both green).
4. `export_full(dest="C:/Workspace/ZeroParadox/ssot.json")` — ABSOLUTE path (a relative dest lands beside the MCP).
5. Confirm file paths resolve N/N, then commit `ssot.json` with the change.

Memory: `feedback_sjv_sync_on_lean_change`.
