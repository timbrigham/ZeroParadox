**`/ship` — the single command for production work.** Three actions, in order. Two are script calls;
the middle one spawns the agents, because a Python script cannot create an agent.

---

## 1. Run the script. It does ALL the mechanical work.

```
python tools/verify/ship.py pre --target <stable-slug>
```
(add `--ranges <base>..<tip>` when shipping something already committed)

One call performs: `batch.py precommit` (build green · `#print axioms` per new declaration ·
`ssot.json` row per new declaration · four gating checkers at zero new), the gate-round bump, and
the plan. **Non-zero exit means STOP** — never spend a gate round reviewing a tree that cannot commit.

It also runs the **standing self-improvement pass** (`selfheal.py`) and prints a one-line summary.
That pass **suggests and never corrects**: it counts recurring PROCESS and AGENT-BEHAVIOUR shapes
across `DEFECTS.md` and flags any at 3+ occurrences that still has no class row in
`DEFECT_CLASSES.md`. **If it flags something, raise it with Tim as a proposed process change** —
do not silently file a class row, and do not silently ignore it. Full output:
`python tools/verify/selfheal.py`. ⚠ Its counts are a **reading list, not a finding list**; two
matches may be one incident described twice.

It ends with three machine-readable lines. **Use them; do not re-derive them by eye:**
```
SHIP_SCOPE=<comma-separated reviewable files>
SHIP_GATES=<comma-separated gate keys that are OWED>
SHIP_ROUND=<n>
```

⚠ **DO NOT EDIT ANYTHING IN `SHIP_SCOPE` WHILE THE GATES ARE READING IT.** Nothing stops you at
the keystroke any more — the read-only freeze was retired 2026-08-23, because git unlinks and
recreates rather than opening for write, so `checkout` and `reset --hard` silently un-froze a
locked path. **What catches it instead is the per-file SHA-256:** an edited file stops matching
what the signal recorded, so `prepush` refuses and names it. The round is then wasted rather than
corrupted — which is the right failure, and still a wasted round.

## 2. Spawn exactly the gates in `SHIP_GATES` — one Agent call each, all in one message.

For each gate: **read its command file** (`.claude/commands/<gate>.md`) and pass the prompt
**verbatim** from after the "Spawn the Agent with this prompt" marker — never a hand-written brief.
Substitute `ARGUMENTS_VALUE` with `SHIP_SCOPE` (or the gate's own mode, e.g. `crank`). Add the
caller pre-flight: `SHIP_ROUND` and the cap, the permitted verdicts, and the three warnings below.

**Tell Tim which gates are running and their parameters before they start** — command file, scope,
mode, round, permitted verdicts, signal written, what this round must attack.

**Three warnings every brief must carry:**
1. **Hash the FILE ON DISK for any signal, never `git show "HEAD:<path>"`** — that means different
   things before and after a commit and yields a signal stale the instant the commit lands.
2. **Never `reset --hard` / `checkout -- .` / `clean` / `stash` the shared tree.** Assume the caller
   holds uncommitted work. Needs commits? `git worktree add --detach`. A run destroyed the caller's
   uncommitted file this way and reported success.
3. **Sources are on disk in `.claude-local/papers/`** — check before calling one unobtainable; never
   record a fetch failure as a fact about a source.

⚠ **Adversary's crank mode routes off `pa_cleared.txt`.** Tell it prior-art is running concurrently
and to check that signal at the END of its run, or it raises a routing kill for a gate beside it.

⚠ **Reviewers may only `gate_round.py show`.** A reviewer that bumps burns the cap.

## 3. Run the script again. It validates everything.

```
python tools/verify/ship.py post
```
Echoes each signal's recorded **verdict line**, so *"cleared"* is never read as *"clean"*. Exit 0
means safe to commit and push.

Then:
```
git add <named paths>          # NEVER -A; agents may have written to the tree
git status --short             # every staged path must be one you meant
git commit -F <message-file>   # BOM-free: [System.IO.File]::WriteAllText(p, s, UTF8Encoding($false))
git push origin illustrated > <scratchpad>/push.log 2>&1 ; echo $?
python tools/verify/batch.py close      # if a batch was open
```
⚠ **Never pipe a push through `head`/`grep -q`, and never write a `|| git push --no-verify`
fallback.** If the hook blocks, read it and fix the cause.

---

**Verdicts.** FAIL-BEDROCK → fix, bump, return to 2 (cap 5). STOP-ORDINARY → the gate writes its
signal; the correct action is to PUSH, not iterate (cap 2). ⚠ **Editing after a STOP-ORDINARY stales
every signal and restarts the obligation** — either re-run the gates or push what was certified and
ledger the rest. Not both. **Ledger every finding** in `.claude-local/DEFECTS.md`, fixed or not.

**Not wired into the git hook, deliberately.** A gate run is 15-25 minutes; four in a pre-push hook
would hang git for over an hour and be disabled within a day. **`/ship` produces the signatures; the
hook refuses work that lacks them.** Without the hook `/ship` is optional; without `/ship` the hook
is a wall with no door.
