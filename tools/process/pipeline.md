# The verification pipeline — why it is shaped this way

**Opens when:** a gate blocked and you want to know what it was protecting, you are changing
`hooks.py` / `batch.py` / `report.py`, or you are asking why an obligation is enforced at commit
rather than at push.

`CLAUDE.md` carries the commands and the rules. This is the argument, and every part of it is a
measured failure rather than a design preference.

## 1. Do not copy the enforcement map — the tool prints it

**Before any check runs, `hooks.py pre_commit`, `hooks.py pre_push`, `batch.py precommit` and
`batch.py prepush` each print a manifest**: what is about to run, in what order, which checks BLOCK
and which only warn, what scope they apply to, what is exempt, and what is deliberately NOT run.
`prepush` additionally names each required review — its purpose, its trigger, and **what the
verdictLedger records for it at the bytes in hand**, so *"cleared"* is never read as *"clean"*.

One formatter, `tools/verify/report.py`, so the four entry points cannot drift into describing
themselves differently. **Run the command; do not maintain a second copy of its answer in prose.**

**⭐ Tim, 2026-08-10: *"update the process so that when we run the pipeline in the future this is the
default behavior."*** It is not cosmetic — it is how three defects stayed invisible for a month:

| defect | what was invisible |
|---|---|
| `HK-1` | `check_modal --block` had never blocked a push, and the output looked identical either way |
| `REL-3` | `check_poles` sat in the checker list gating nothing, while `precommit` printed `suite ok` |
| `RLY2-1` | three checkers silently skipped a file they judged vendored — how a self-exemption hole went unnoticed |

**A gate that does not declare its own scope and enforcement mode cannot be audited by reading its
output.**

⚠ **Two output bugs found while building it, both of which would have shipped looking correct.**
Python's stdout is block-buffered while child processes write straight to the terminal fd, so the
manifest printed *after* everything it announced, and section headers landed under the wrong
sections. Fixed with `line_buffering=True` alongside `encoding="utf-8"` — the Windows console
otherwise mangles an em-dash. Both live in `report.py`, so every entry point inherits them.

## 2. Where each obligation gates — ask the services

**What must be green for an action is served, not written here.** `gitRobot admission(action='commit')`
and `gitRobot admission(action='push')` return the admission set, which is what the gate reads;
`gitRobot requirements(action=...)` carries why each excluded step is excluded. `verdictLedger
requirements(action=...)` is a different object, the type registry: what may be RECORDED, not what
must be GREEN. The local hooks' own legs, with their BLOCK/WARN modes, are in the manifests of § 1.
None of these answers is copied into this file, because each moves.

**One argument the tools do not print: moving a check earlier must not break stub-first.** Stub-first
development commits `sorry`-stubbed files deliberately as rollback points
(`tools/process/lean-development.md`). A check may block at commit without conflicting with that only
if what it inspects is something a correct stub commit already satisfies. Settle that for the specific
check, by running it on a stub commit, before moving it earlier.

## 3. The hooks are three-line shims, and that was not free

Tim, 2026-08-10: *"the shell variants are legacy and should be retired... just the python version
should remain."* There were **two partial implementations** — a ~300-line shell hook and `batch.py`
— and they measurably disagreed three ways (what counts as reviewable; whether signals are required
when nothing reviewable changed; whether a gate-exempt file can stale a signal) while checking
**disjoint** things: the `/rely` routing only in `batch.py`, the four checkers and the path resolver
only in the hook. Neither was the pipeline. Shell and Python cannot share a module, so the shell
went. **Edit `hooks.py`; the shim must never grow.**

⚠ **The ORDERING was load-bearing, and this is how `REL-1` got fixed.** The hook knows the refs being
pushed; `batch.py` alone did not, so it computed "what changed" from the working tree and went
**vacuous the moment a commit landed**. `hooks.py` parses stdin and passes the ranges in. Measured on
`7d25a46..e15b222`: the working tree reports **0 reviewable, trigger 5 not firing**; the same range
reports **22 reviewable, 346 insertions, trigger 5 FIRES**. **Delegating before fixing this would
have replaced a correct computation with a vacuous one.**

`batch.py prepush` and the hook now run the same code — the hook passing `--ranges`, a manual run
reading the working tree. One definition, two entry points.

## 4. The declaration baseline is on disk, never computed from git

`tools/verify/decl_baseline.txt`. It used to compute "added" against `HEAD`, which is meaningful only
*before* the commit; run afterwards it returned nothing and both the purity and SSOT checks passed
**vacuously**.

A **stale baseline is safe** — it can only make more declarations look new, so the check gets
stricter, never blind. Re-seed with `python tools/verify/batch.py decls --baseline`. Vendored
backports are exempt structurally, as in `check_prose.py`.

## 5. Why `/batch` has stages

**`ledger` and `screen` are the two that got skipped.** Consulting `DEFECTS.md` first is a discipline
that failed three times in one session — three "findings" duplicated rows already in the ledger.
**A step that is not a stage is a step that can be forgotten.**

⚠ **Filters are frozen at `batch start`.** Editing a checker mid-batch means the work was done
against a moving target; the batch is invalid and must restart. Route filter defects to `DEFECTS.md`
and fix them in their own batch. (Violated by the author of the rule on the day it was written — see
`PRC-1`.)

⚠ **If a stage BLOCKS, fix the cause.** Do not delete `batch_state.json`, do not `--no-verify`, do
not push a subset to dodge a signal. This project has **two recorded bypass incidents and both began
by treating a block as an obstacle** — see `tools/process/push-gate-bypass.md`.

---

## Ask the ledger first: it is a state engine, not an archive (Tim, 2026-09-09)

**Tim, verbatim:** *"the verdict ledger is supposed to be more or less a state engine.. you should be
checking it before you do a damn thing.. this was one specific example, but checking first needs to
be the default."*

And the instance that prompted it: *"if we already have a passing verdict for this blob, why are you
even reattempting anything here?? once it's passed it's passed. sounds like a workflow problem to me.
not a data problem."*

### The control flow this replaces

The habit is **ACT → GET REFUSED → READ THE REFUSAL → ADJUST**. The refusals on this project are
good: they name the sanctioned alternative, so acting-then-reading converges. It is still the
expensive path, and it manufactures work that then fails.

The rule is **ASK → DO ONLY WHAT IS OWED.**

### Why it is not merely cheaper — a verdict is about BYTES

A verdict binds `(step, path, git_blob_id)`. It is a fact about content, not about occasions. So
"this step already PASSES for the bytes in hand" is a **complete answer**, and re-deriving it is not
diligence — it is work with no question behind it. Every gate re-run over unchanged content is
either wasted or, worse, actively harmful: the second append collides with the first.

### The measurement, 2026-09-09

A `D1` remediation merge was blocked. Diagnosing it by ACTING took roughly an hour: a refused
commit, a refused merge, a checker source read, two ledger lookups and a parent/tree walk.

One call answers it in about 4 KB:

    progress(action='push', ref='<the fix commit>', admission=[...])

      17/19 satisfied
      adversary  STALE  covered 73/74  owes_a_pass 1  remedy: run the step and record
      editorial  STALE  covered 74/75  owes_a_pass 1  remedy: run the step and record
      green: check_encoding, check_paths, check_pov, check_prose, decls, guards, ... (17)

**`check_encoding` was already green at that tree.** The merge's pipeline re-derived seventeen
recorded, passing verdicts and then blocked on the one it could not re-append. The block was
manufactured entirely by work that had no reason to happen, and the real remaining work was never
mechanical at all — two review records over one path each.

### ⚠ The contract already said this, which is why it is a rule and not a feature request

    gitRobot        "START HERE: admission(action='push') - ~665 bytes, and it is what
                     verdictLedger's progress(), coverage_gap() and can_push() refuse without."
    verdictLedger   "START HERE: status() ... then progress(...) which answers 'can I proceed'
                     in ~4KB."
    admission()     "measured over one night, progress 6 calls against 60 for inventory and status"

The tools were built for this flow and published with it. The 6-against-60 is the server author's
own measurement of exactly this failure. **The gap is behavioural, not technical.**

### The order

1. `gitRobot admission(action=...)` — the set of steps that must be green. ~665 bytes.
2. `verdictLedger progress(action=..., ref=..., admission=[...])` — what is unsatisfied, the remedy
   per step, and what is already green. ~4 KB.
3. Do only what step 2 named. Run no gate whose verdict is already recorded and passing for the
   content in hand.

⚠ `status().would_block_push` is TIP-SCOPED and is not the range answer; `can_push(rev_range=...)`
is. Reading the tip field as the push answer is a recorded trap.

⛔ The narrow half of this is mechanizable and is filed as `D1M-1`: the append path should consult
the basis before appending. **The hazard is the narrowing** — "already recorded" must mean *this
step, this basis, verdict PASS* and nothing wider, or the fix turns every genuine `V`-rule rejection
green on the push path.
