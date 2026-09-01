

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

---

## The same rule one layer over: READ THE CHECKER OUTPUT WHOLE, on a PASS as much as on a BLOCK

*Migrated from a private memory, 2026-08-28. It was recorded twice — here in outline and in a memory
body no spawned agent can see (`CLAUDE.md` R-BRIEF: "Memory BODIES never arrive at all"), which is
`R-RECUR`'s "a rule stated twice fires in neither place". The measurements below are the half that
was only ever in the invisible copy.*

Tim, 2026-08-26: *"all of our checkers should be read in their entirety. that's true, just as much
for success conditions."*

⚠ **OBEYING THE RULE ABOVE AND THEN GREPPING THE LOG NARROWLY REINTRODUCES THE TRUNCATION AT THE READ
STEP** — letter obeyed, spirit broken. "Redirect to a file" is only half the instruction; the other
half is opening the file.

**Measured 2026-08-26, in both directions:**

- **On a BLOCK.** `check_prose` printed its migration remedy — *"Long-form reasoning… goes in the
  RIDE-ALONG: Foo.md beside Foo.lean"* — three lines below the line count. Read through
  `Select-String -Pattern "lines \(cap"`, the count showed and the remedy did not. Result: **26 lines
  of fences DELETED instead of migrated**, plus a confident report that "there is no standing
  instruction" when the instruction was inside output already on screen.
- **On a PASS.** `check_claude_md` printed, on 2026-08-26, `cap WARN 36/45 entries over the 12-line cap`. Every
  applicable run said so. It was seen once — the run that was unfiltered. Exit code 0 throughout.

**The checkers are DESIGNED for a whole read and say so in their own banners.** `check_claude_md`:
*"PENDING legs are NOT checked and NOT passing. A clear run below is not a pass."* `check_negatives`:
*"A hit is a PROMPT TO READ, never a verdict. Read hits; do not count them."*

**So: no `| head`, no `-Tail N`, no `Select-String` for the symptom, no grepping for `FAIL`.** The
WARN counts, the PENDING legs and the remedy are exactly the part a pattern chosen in advance can
never match — **you cannot grep for advice you have not read yet.**

⚠ **Corollary for REPORTING: a green exit is not "clean". Say what the WARN counts were.**

**Structural since 2026-08-28 — `tools/verify/claude_hooks/block_checker_truncation.ps1`.** A
`PreToolUse` hook now DENIES any command that runs something under `tools/verify` and pipes it into
`head`, `tail`, `grep`, `Select-String`, `findstr`, `Select-Object -First/-Last`, `-Tail` or
`-TotalCount`. Registered on both the Bash and PowerShell matchers, fails closed, 32 controls.
**Why it exists rather than a fourth restatement:** R-TRUNC was keyed to *"a command that runs a
GATE"*, a one-file `check_encoding` run did not feel like a gate, and `| Select-Object -Last 2` hid
four warnings an hour after the rule had been quoted. A CATEGORY leaks; **a pipe after a path** binds.
It tests INVOCATION, so grepping checker SOURCE stays free. **NOT a seal:** run-then-grep across two
separate tool calls each presents a clean command string, and `--no-verify` is unhooked.

📖 **THE MEASUREMENTS, AND WHERE THE DEFENCE ACTUALLY LIVES — `tools/process/push-gate-bypass.md`.**
The immunity is in `tools/verify/hooks.py`, **not** a `trap '' PIPE` in `.git/hooks/pre-push` —
a reader who greps for `trap` will not find it and could conclude the defence was dropped. Install
per clone with `python tools/verify/install_hooks.py`; `--check` exits 1 when the gates are not
armed. **Read it before assuming the clone you are standing in is protected.**
