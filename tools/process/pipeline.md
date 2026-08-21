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
`prepush` additionally names each required review — its purpose, its trigger, its signal file, and
**the recorded verdict line from that signal**, so *"cleared"* is never read as *"clean"*.

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

## 2. Why each obligation gates where it does

`precommit` is a **manual** command, so until 2026-08-09 three of the four universal obligations
could be skipped simply by not running it. Tim's call that day moved them onto the hooks:

- **The four checkers BLOCK AT COMMIT.** `pre-commit` runs each with `--block`; it previously ran
  them and then `exit 0`'d unconditionally. **This does not reopen the 2026-07-30 warn-only
  decision** — that argument protects **build state**, because stub-first commits `sorry`-stubbed
  files deliberately, and none of the four checkers looks at `sorry`, the build, or completeness.
  They are baselined, sit at zero new, and **already blocked at push**, so nothing newly unpushable
  became uncommittable. The identical failure just arrives earlier, where the fix is cheap.
- **Purity and SSOT BLOCK AT PUSH** (`pre-push` § 3b-f, via `batch.py decls --block`). Before this
  they were the only two obligations with **no automatic enforcement anywhere**.
- **`lake build` deliberately gates NEITHER.** It is the one genuinely in tension with stub-first.
  CI at the PR to `main` is its backstop.

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
