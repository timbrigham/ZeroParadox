

---

## Routed from `CLAUDE.md`, 2026-08-23

## NEVER truncate the output of a hook-running command, and NEVER write a `--no-verify` fallback. Hard Rules.

**TRIGGER — an action: you are about to put `| head`, `| grep -q`, `| grep -m`, `| sed q` or any
early-exiting consumer around a command that runs a git hook, or to write `|| git push --no-verify`.**

- **Redirect, do not truncate.** `python tools/verify/batch.py prepush > prepush.log 2>&1; echo $?`,
  then read the log. (`tail` reads to EOF and is safe; the rule covers everything anyway, because you
  should not have to remember which consumers exit early.)
- **`--no-verify` is a separately-typed decision, never a fallback and never chained with `||`.** The
  one documented case is a `CLAUDE.md`-only change against a stale signal.

⭐ **HALF OF THIS IS NOW STRUCTURAL, AND HALF IS NOT — KNOW WHICH.** Since 2026-08-22 a push goes
through `gitRobot`, which **never passes `--no-verify` and has no parameter that reaches it**, so the
second bullet can no longer be violated by an agent even deliberately. **The first bullet still binds
with full force**, because the commands you truncate now are `batch.py`, `lake build` and the
checkers — and `| Select-Object -First N` breaks a PowerShell pipe and reports a wrong exit code
exactly as `| head` did. **The SIGPIPE hazard moved; it did not go away.**

**⚠ THE COST, AND IT IS WHY THESE ARE HARD RULES: BOTH BYPASSES SUCCEED SILENTLY — THE PUSH LOOKS
GREEN.** Measured 2026-07-26: the identical push exited **1** (blocked) bare and **0** (pushed)
through `| head -5`, because `head` closed the pipe and the hook died of `SIGPIPE` before reaching
its `exit 1` — and the review-signal check runs **last**, so any truncation short enough to be
useful is long enough to skip it. A twelve-file push with a stale `pa_cleared.txt` reached `origin`
that way. The `||` fallback is the same failure written down on purpose. **If a push is blocked,
read the reason and fix it — the block is the control working.**

📖 **THE MEASUREMENTS, AND WHERE THE DEFENCE ACTUALLY LIVES — `tools/process/push-gate-bypass.md`.**
The immunity is in `tools/verify/hooks.py`, **not** a `trap '' PIPE` in `.git/hooks/pre-push` —
a reader who greps for `trap` will not find it and could conclude the defence was dropped. Install
per clone with `python tools/verify/install_hooks.py`; `--check` exits 1 when the gates are not
armed. **Read it before assuming the clone you are standing in is protected.**
