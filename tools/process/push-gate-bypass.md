# The push-gate bypasses — the pipe, and the `--no-verify` fallback

**Opens when:** you are about to truncate the output of a command that runs a git hook, or you are
about to write a fallback into a push command. Both have bypassed this project's push gate for real,
in the same session, and both failed *silently* — the push looked green.

`CLAUDE.md` carries the two rules. This is the measurement behind them and where the defence
actually lives now.

## 1. The pipe bypass — measured and reproduced 2026-07-26

Same push, same repository state, same signals:

```
git push --dry-run origin <ref>                    → exit 1   (blocked, correctly)
git push --dry-run origin <ref> 2>&1 | head -5     → exit 0   (SUCCEEDS — gate bypassed)
```

**Mechanism.** `head` exits after N lines and closes the pipe. The hook is still writing — file
reference resolver, invariants, hash check, font checks, then the review-signal check **last**. It
died of `SIGPIPE` **before reaching its `exit 1`**, and git proceeded with the push. The review gate
never ran, and because its output is at the END, *any truncation short enough to be useful is long
enough to skip it.*

**It actually happened.** A twelve-file push whose `pa_cleared.txt` was stale was blocked on the
first attempt, then reached `origin` on a second attempt run as `git push … 2>&1 | head -40` —
issued only to read the hook's output. Nothing else changed.

**Scope of the hazard, measured after the fix.** `head`, `grep -q`, `grep -m`, `sed q` and any other
consumer that exits before EOF sever the pipe early. `tail` does not, because it reads to EOF.

## 2. Where the immunity lives — verified 2026-08-20

**In `tools/verify/hooks.py`, not in a shell `trap`.** It sets `signal.SIGPIPE` to `SIG_IGN` where
the signal exists (POSIX only) and catches `BrokenPipeError` around its own output everywhere;
`report.py` does the same for the manifest writer. Grep `SIGPIPE|BrokenPipeError` under
`tools/verify/` to see all three sites — **do not cite line numbers for them**, they drift.

⚠ **A reader looking for `trap '' PIPE` in `.git/hooks/pre-push` will not find it and could
reasonably conclude the defence was dropped.** It was there until the shell hooks became three-line
shims in August 2026; the protection moved with the logic and nothing was lost. `CLAUDE.md` carried
both the old location and its correction, eighteen lines apart, for months — one file, two answers,
which is the trap this project keeps re-entering.

**The installed hook is still not version-controlled** — git has no mechanism for that. What is
tracked is the SOURCE (`tools/verify/proposed_pre_*_hook.sh`) and the installer:

```
python tools/verify/install_hooks.py            # install
python tools/verify/install_hooks.py --check    # exits 1 when the gates are not armed
```

So the per-clone copy step no longer depends on someone having been handed the file out of band.

**The rule stands regardless of the protection.** Do not rely on immunity being installed in the
clone you are standing in, and never truncate the output of a hook-running command. Redirect and
read the file:

```
git push origin <branch> > push.log 2>&1; echo $?
```

## 3. The `--no-verify` fallback — measured 2026-07-26, self-inflicted, same session

A command of this shape was written to "handle" a possible block:

```
git push origin <branch> ... || git push --no-verify origin <branch> ...
```

**That is an unconditional, silent gate bypass.** If the gate fires, the fallback pushes anyway and
the transcript shows a successful push. It did not fire that time only because the push was
`CLAUDE.md`-only and therefore gate-exempt. It would have bypassed a real block.

`--no-verify` is legitimate **only** as a deliberate, separately-typed decision for a known-good
reason — the documented case is a `CLAUDE.md`-only change against a stale signal. Never as an
automatic fallback, never chained with `||`.

## 4. Why these are hard rules and not footnotes

A gate that can be cleared by re-running the command with a pipe is not a gate. Anything reaching a
public remote must pass on its own merits, not because a reader closed the pipe early. **If a push
is blocked, read the reason and fix it — the block is the control working.**
