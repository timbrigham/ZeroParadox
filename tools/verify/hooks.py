"""THE hook pipeline. The shell hooks are three-line shims that call in here.

WHY (Tim, 2026-08-10): *"the shell variants are legacy and should be retired... just the python
version should remain."* The pipeline had TWO partial implementations — a shell hook and
`batch.py` — and they measurably disagreed three ways (PIPE-1): what counts as reviewable
(`CLAUDE.md`), whether signals are required when nothing reviewable changed, and whether a
gate-exempt file recorded in a signal can stale it. They also checked disjoint things: the `/rely`
routing existed only in `batch.py`, the four checkers and the path resolver only in the hook.
Neither was the pipeline.

Shell and Python cannot share a module, so the only way to have one definition is for one of them
to go. The shell went. Everything it orchestrated was already Python (`check_paths`,
`check_invariants`, the four checkers, `check_hashes`, `scan_pdfs`); the shell was sequencing, and
sequencing is what drifted.

⚠ THIS FIXES REL-1 AS A SIDE EFFECT, AND THAT IS THE POINT OF DOING IT THIS WAY ROUND. The hook
knows the refs being pushed; `batch.py` alone did not, so it computed "what changed" from the
working tree and went vacuous the moment a commit landed. `pre_push` parses stdin and hands the
ranges to `batch.cmd_prepush`, so the shared code is correct at the only moment that matters.

Install (hooks live in .git/ and are still NOT version-controlled — per clone). The hook SOURCES
now are tracked, which is the half that used to be missing:
    python tools/verify/install_hooks.py
"""
import os
import subprocess
import sys

# TWO roots, and keeping them apart is the point of the 2026-08-15 move. `BASE` used to be
# `.claude-local` and served both purposes at once, which is why publishing the bundle was not a
# copy: HERE is the tracked, public tool bundle; PRIV is per-push private state (signals, locks,
# batch state) that deliberately did NOT move and MAY BE ABSENT ENTIRELY in a public clone.
# Roots come from `common` — ONE derivation for the whole bundle (`DEFECTS.md` MIG-3). SELF is
# derived from `__file__`, never written down: a hardcoded invocation path is a copy of the path and
# drifts exactly like a mirrored file does.
#
# ⚠ COERCED TO `str`, not re-derived. This module speaks `os.path`; `common` speaks `pathlib`. A
# line of type conversion is not a second definition — change the layout and there is still exactly
# one place to edit.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402

HERE = str(common.HERE)
REPO = str(common.REPO)
PRIV = str(common.PRIV)
SELF = common.self_rel(__file__)
BASE = HERE   # retained: existing call sites below mean "where the tools live"

if HERE not in sys.path:
    sys.path.insert(0, HERE)

import report      # noqa: E402  the one formatter every entry point announces itself with
import vendored    # noqa: E402  the one exemption definition

EMPTY_TREE = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"
ZERO = "0" * 40

# SIGPIPE immunity. CLAUDE.md records `git push ... | head` bypassing the gate: head closed the
# pipe and the shell hook died before reaching its `exit 1`. Python raises BrokenPipeError in the
# same situation, so both ends are handled — the signal where it exists, the exception always.
try:
    import signal
    signal.signal(signal.SIGPIPE, signal.SIG_IGN)   # POSIX only
except (ImportError, AttributeError, ValueError):
    pass


def run(*cmd):
    """Run a child, streaming its output, and return its exit code.

    ⚠ Never captures. The whole point of a gate is that the operator SEES why it fired, and a
    captured-then-reprinted stream loses interleaving with anything else that writes.

    ⚠ CONCURRENT MODE KEEPS THAT PROPERTY RATHER THAN BREAKING IT (`ZP_HOOK_JOBS`, 2026-10-04). A
    leg launched ahead of its turn writes stdout+stderr to its OWN file, and the file is replayed
    WHOLE, byte for byte, HERE — at the moment this sequential call site is reached, in manifest
    order. Nothing else writes into a leg's file, so there is no interleaving to lose; and because
    the replay happens where the stream would have been, the hook's own lines land between legs
    exactly where they land today. Partial output of a leg that died, timed out or crashed is
    replayed too. See `_Scheduler`."""
    sched = _SCHED
    if sched is not None:
        job = sched.take(cmd)
        if job is not None:
            return _consume(cmd, job)
    try:
        rc = _child(cmd)
    except OSError as e:
        print("  hook: could not run %s (%s)" % (" ".join(cmd), e))
        return 1
    # ⚠⚠ RECORDED HERE, AFTER THE CHILD HAS ACTUALLY RUN, AND NOWHERE ELSE. `/rely` R3-1: the
    # previous version appended in `py()` on the line BEFORE the call, which records the INTENT to
    # launch rather than the launch -- "a receipt vs an invoice, and reconcile audits invoices".
    # Three one-line mutations went green against it: deleting the `run(... scan_pdfs)` call while
    # leaving its hand-written append (20 of 20, rc 0), and stubbing this function to `return 0`
    # (0 children, still 11 of 11 and 20 of 20, rc 0). Both are impossible from here: no
    # `subprocess.call` return, no entry. An OSError returns above without recording, because a
    # child that could not start did not run.
    EXECUTED.append((_invocation(cmd), rc))
    return rc


def _invocation(cmd):
    """Normalise a launched argv to (script basename, *args) — what the manifest names.

    `cmd` is (python, /abs/path/to/script.py, *args); the manifest speaks in basenames.
    """
    parts = list(cmd)
    for i, p in enumerate(parts):
        if str(p).endswith(".py") and i > 0:
            return (os.path.basename(str(p)),) + tuple(str(x) for x in parts[i + 1:])
    return tuple(str(x) for x in parts)


# ⚠⚠ WHAT ACTUALLY RAN, IN ORDER. `/rely` R2-1 measured why a generated manifest is not enough:
# generating the plan from the same TABLE the loop iterates still leaves the LOOP a separate
# statement, so replacing its iterable with `[]` printed `11 check(s): 11 BLOCK`, named all eleven
# rows, ran nothing and exited 0. Deriving one hand-written list from another moves the divergence;
# it does not remove it. The only thing that cannot be faked is an observation of the invocation
# itself, so every child this process launches appends here and `reconcile()` compares the manifest
# against THIS, not against the table it was printed from.
EXECUTED = []

# Every ref name seen on stdin this run, recorded where they are PARSED rather than where they are
# judged — see `reconcile`'s independent quarantine re-test (R4-2).
REFS_SEEN = []

# The exact (local_ref, local_sha, remote_ref, remote_sha) tuples git fed THIS process on stdin —
# the advisory-skip receipt's match key. Recorded beside `REFS_SEEN`, where the line is parsed, so
# the key can only ever come from git's own stdin (ticket fence 1), never from a caller's claim.
REF_TUPLES = []


def py(script, *args):
    # ⚠ No recording here — `run()` records, and only after the child actually returns (R3-1).
    return run(sys.executable, os.path.join(BASE, script), *args)


def _found(expect):
    """The (invocation, rc) whose argv starts with `expect`, or None. Prefix, so flags may vary."""
    n = len(expect)
    for inv, rc in EXECUTED:
        if tuple(inv[:n]) == tuple(expect):
            return inv, rc
    return None


def reconcile(phase, expected, refs=(), skipped=None):
    """Block unless every advertised check LAUNCHED and its exit code was ACCEPTABLE.

    `expected` is [(label, argv_prefix_or_None, ok_codes)]. `ok_codes` of None tolerates any code
    (a WARN row). A None argv marks a row handled inline; those are re-tested here INDEPENDENTLY
    where that is possible, and reported as unverified where it is not.

    ⚠⚠ THE SECOND HALF IS THE POINT, AND IT IS WHY THE DECISION LIVES HERE RATHER THAN BESIDE THE
    LOOP. `/rely` R4-1: `pre_commit` was two statements — launch, then score — and `reconcile`
    observed only the first. Replacing the scoring block with `if False: pass` and forcing
    `check_pov` to exit 1 gave: the finding printed, `11 of 11` reconciled, and the commit MADE.
    Round 2's `_mode` closes a different route (widening `ok_codes`) and cannot see the scoring
    deleted, because it computes `BLOCK` correctly over a column nothing reads. So the verdict is
    now DERIVED from the recorded exit codes: delete the scoring and the block still happens,
    because there is no longer a second place where the decision lives.
    """
    missing, bad, inline = [], [], []
    for label, argv, ok_codes in expected:
        if not argv:
            inline.append(label)
            continue
        hit = _found(argv)
        if hit is None:
            missing.append(label)
            continue
        _inv, rc = hit
        if ok_codes is not None and rc not in ok_codes:
            bad.append("%s (exit %d)" % (label, rc))

    named = sum(1 for _l, argv, _o in expected if argv)
    print("")
    print("  manifest reconciliation: %d of %d advertised check(s) launched; %d bad exit(s)%s"
          % (named - len(missing), named, len(bad),
             ("; %d inline row(s): %s" % (len(inline), ", ".join(inline))) if inline else ""))

    # ⚠ R4-2: `quarantine` was the only push row with NO observer — deleting its inline branch let
    #   a `private/*` ref push green while the manifest printed the row's name. Re-tested here
    #   INDEPENDENTLY rather than observed, because a second enforcement survives deleting the
    #   first and an observer of a deleted branch sees nothing.
    # Both shapes `parse_refs` refuses: a quarantined LOCAL branch, and any REMOTE ref under
    # a `private/` path. Matching one and not the other would re-open half the hole.
    # ⚠⚠ FENCE 3 (`R-NOCONV`): THE GUARD ASSERTING WHAT STILL BLOCKS LANDS WITH THE SKIP. Printed on
    #   EVERY push run, matched or not, so a skip can never be the reason a BLOCK row went quiet:
    #   every BLOCK row named here must have launched, and no skipped label may be a BLOCK row of
    #   EITHER manifest. `skipped is None` is the commit phase, which has no skip at all.
    if skipped is not None:
        _block = [label for label, argv, ok in expected
                  if argv and ok is not None and 1 not in ok]
        _launched = [label for label in _block if label not in missing]
        print("  BLOCK rows launched: %d of %d; advisory leg(s) skipped: %s"
              % (len(_launched), len(_block), ", ".join(skipped) or "none"))
        if skipped:
            _never = {label for label, argv, ok in expected
                      if not argv or (ok is not None and 1 not in ok)}
            _brows = _batch_rows()
            if _brows is None:
                print("%s BLOCKED — a leg was skipped and batch.py's manifest, which it must be "
                      "checked against, could not be read." % phase.upper())
                return 1
            _never |= {label for label, mode, _e in _brows if mode != "WARN"}
            _known = {label for label, _a, _o in expected} | {label for label, _m, _e in _brows}
            _bad_skip = sorted(set(skipped) & _never) + sorted(set(skipped) - _known)
            if _bad_skip:
                print("")
                print("%s BLOCKED — a skipped leg is a BLOCK row, or names no row at all: %s"
                      % (phase.upper(), ", ".join(_bad_skip)))
                print("Only a derivably ADVISORY leg may ever be skipped. This is the second of two")
                print("checks on that property (batch.py refuses first); reaching it is a defect.")
                return 1

    leaked = sorted({r for r in refs
                     if r.startswith("refs/heads/private/") or "/private/" in r})
    if leaked:
        print("")
        print("%s BLOCKED — a private/* ref reached the push: %s" % (phase.upper(), ", ".join(leaked)))
        print("These branches never leave this machine. This is the second of two checks on that")
        print("property; if the first did not fire, that is itself a defect to report.")
        return 1

    if missing or bad:
        print("")
        if missing:
            print("%s BLOCKED — the manifest advertised %d check(s) that never ran: %s"
                  % (phase.upper(), len(missing), ", ".join(missing)))
            print("This is the gate lying about itself, which is worse than any finding it could")
            print("report. Do not bypass: fix the wiring so the advertised check executes.")
        if bad:
            print("%s BLOCKED — %d advertised check(s) exited badly: %s"
                  % (phase.upper(), len(bad), ", ".join(bad)))
            print("Derived from the recorded exit codes, not from a second list beside the loop,")
            print("so deleting the scoring does not delete the block.")
        return 1
    return 0


def recorded(script, *args):
    """Run a push-time checker WITH `--record`, and keep exit 2 distinct from exit 1.

    ⚠ EXIT 2 IS NOT EXIT 1. A checker that PASSED but could not write its verdict leaves the key
    MISSING, so the ledger refuses the push with nothing local explaining why — while the operator
    has just watched every check go green. Collapsing the two prints "the check failed" over a
    check that did not fail, which is the shape that trains the `--no-verify` reflex.

    ⚠ WHY THE PUSH PATH RECORDS AT ALL. `--record` was wired into `pre_commit` and not here, so the
    nine checkers that run only at push earned keys ONLY when someone ran them by hand. They went
    STALE at every commit and stayed that way, which meant the skip helped exactly the five that
    needed it least and the gate was satisfiable only after a manual sweep. Measured 2026-08-23:
    15 of 24 steps needed a re-run on a tree whose checks had all just passed.
    """
    rc = py(script, *(args + ("--record",)))
    if rc == 2:
        print("\n⚠ %s ran but its verdict was NOT RECORDED." % script)
        print("  The ledger will report this step MISSING and refuse the push. This is a RECORDING")
        print("  failure, not a check failure — the check itself may have passed. Fix the ledger")
        print("  connection; do not go looking for a defect in the corpus.")
    return rc


def git_out(*args):
    try:
        r = subprocess.run(["git"] + list(args), cwd=REPO, capture_output=True,
                           text=True, encoding="utf-8", errors="replace")
        return r.returncode, (r.stdout or "")
    except OSError:
        return 1, ""


# ------------------------------------------------------------------ concurrent legs
#
# ⭐ TIM, 2026-10-04: *"Tooling speed concurrent checks."* Measured that day, a pre-push ran its legs
# strictly one after another for 842.9 s, of which the routing control alone was 595.4 s.
#
# ⚠⚠ THE DECISION CODE IS UNCHANGED, AND THAT IS THE DESIGN. `pre_push` / `pre_commit` still run top
# to bottom, call `py()` / `run()` in manifest order and decide from each exit code exactly as before.
# The scheduler only LAUNCHES legs early; `run()` then waits for the leg it was going to start,
# replays its output whole and returns its exit code. So every exit code, every `EXECUTED` entry (it
# is appended at CONSUMPTION, after the child finished — R3-1 unchanged), every BLOCK message and the
# reconcile result come from the same statements as at `ZP_HOOK_JOBS=1`, which does not create a
# scheduler at all and is today's code path byte for byte.
#
# ⚠⚠ THE DEPENDENCY GRAPH (derived from the legs' source 2026-10-04; each edge names its evidence).
#   MUTATORS — they rewrite shared files in THIS checkout and restore them, so nothing that reads
#   the tree may overlap them, and they may not overlap each other:
#     guards           appends to / rewrites ZeroParadox/Order/Snap.lean, vendored_files.txt,
#                      pov_baseline.txt, prose_baseline.txt, gate_round.json, a probe under
#                      ZeroParadox/Order/Vendored/, .claude/commands/tag-review.md, and
#                      tools/verify/record.py + check_briefs.py themselves (guards.py:83-136,
#                      1589-1905, 2232-2293, 2345-2378). record.py is imported by every --record leg.
#     check_checkers   runs EVERY checker's --selftest with cwd=REPO (check_checkers.py:118-128, 267),
#                      among them `guards.py --selftest`, which appends to Snap.lean
#                      (guards.py:2665-2690), and check_claude_md's, which creates
#                      tools/verify/check_synthetic_withdrawn.py (check_claude_md.py:329-335).
#   ORDER  guards -> check_checkers: guards runs before the checkers it protects (the false-zero
#          argument at its call site below), and check_checkers records a checker verdict.
#   ORDER  the receipt key (`push_key`: tools/verify bytes + HEAD tree, push_key/tools_digest above)
#          is computed BEFORE any mutator launches — it reads the files guards rewrites.
#   PURE   `hooks.py selftest` reads this file, batch.py and required.v2.json (none of which a
#          mutator writes) plus temp dirs, so it may overlap the mutators. Its verdict still gates
#          the skip decision, which stays where it is in `pre_push`.
#          `probe_routing_behavioural.py --selftest` reads its own source (`_mutant`) and works only
#          in temp dirs: stub worktrees, a stubbed `main()` whose git seam is replaced (`_NoGit`),
#          and `_tree_state` on scratch trees with git location variables removed. Measured
#          2026-10-04: a whole-tree hash before and after a run is identical. It records nothing.
#   READERS every other leg reads the tree and records a DISTINCT ledger step at the same basis
#          (no two legs record one step; the routing control's nested runs record nothing: no
#          `--record`, and the agent gate forced off by the `ZP_AGENT_GATE=0` override in the
#          probe's `_run_prepush`), so they run together once the mutators and the pure legs are
#          done. The routing control reads tools/verify only while seeding its own worktree (the
#          probe's `_seed`) and runs everything else inside that worktree, so it is a reader.
#   batch prepush  needs the skip decision (receipt consulted after the selftest passed; its
#          env switch, `pre_push` below), and reads the tree (agent gate re-runs three checkers):
#          submitted at the decision point, after the mutators. Its verdict reads only the review
#          steps, rely and prior_art (batch.py:2483-2583, 1947), which no leg records.
#   PRE-COMMIT  the eleven legs are all readers recording distinct steps, with no mutator: all run
#          together.
#
# ⚠ R-ZERONULL: a leg that could not start, raised inside the scheduler, or timed out is its own
#   OUTCOME and is never read as a pass — see `_consume`.

JOBS_ENV = "ZP_HOOK_JOBS"
LEG_TIMEOUT_ENV = "ZP_HOOK_LEG_TIMEOUT"
DEFAULT_JOBS = 8
TIMEOUT_RC = 124

LEG_EXITED = "EXITED"
LEG_NOSTART = "NOSTART"
LEG_TIMEOUT = "TIMEOUT"
LEG_ERROR = "ERROR"

_QUEUED, _RUNNING, _DONE, _CANCELLED = "QUEUED", "RUNNING", "DONE", "CANCELLED"

# The ledger environment each phase gives its recording legs. ONE definition: `pre_push` /
# `pre_commit` assign it and the scheduler launches with it, and `_consume` refuses any leg whose
# launch environment differs from the one the sequential call would have passed.
_PUSH_LEDGER_ENV = {"ZPLEDGER_BASIS": "HEAD", "ZPLEDGER_RUN": "pre-push"}
_COMMIT_LEDGER_ENV = {"ZPLEDGER_BASIS": "INDEX", "ZPLEDGER_RUN": "pre-commit"}

# Push rows by role, in the order they must run. See the graph above for the evidence.
_PUSH_PURE = ("advisory-skip controls", "routing control selftest")
_PUSH_MUTATORS = ("guards", "check_checkers")
_PUSH_FIRST = ("routing control", "batch prepush")      # longest legs launch first among readers

_SCHED = None


class _LegTimeout(Exception):
    pass


def hook_jobs(environ=None):
    """(jobs, note). 1 means sequential: no scheduler, today's path. `note` is None when there is
    nothing to say; an unreadable value falls back to the sequential path and SAYS so."""
    env = os.environ if environ is None else environ
    raw = env.get(JOBS_ENV)
    if raw is None or not raw.strip():
        return DEFAULT_JOBS, None
    try:
        n = int(raw.strip())
    except ValueError:
        return 1, "%s=%r is not an integer; running SEQUENTIALLY" % (JOBS_ENV, raw)
    if n < 1:
        return 1, "%s=%r is below 1; running SEQUENTIALLY" % (JOBS_ENV, raw)
    return n, None


def leg_timeout(environ=None):
    """(seconds or None, note). Unset means no timeout, as in the sequential path."""
    env = os.environ if environ is None else environ
    raw = env.get(LEG_TIMEOUT_ENV)
    if raw is None or not raw.strip():
        return None, None
    try:
        t = float(raw.strip())
    except ValueError:
        return None, "%s=%r is not a number; no per-leg timeout" % (LEG_TIMEOUT_ENV, raw)
    if t <= 0:
        return None, "%s=%r is not positive; no per-leg timeout" % (LEG_TIMEOUT_ENV, raw)
    return t, None


def _kill_tree(p):
    """Kill a timed-out leg AND its children (the routing control spawns nested runs)."""
    if os.name == "nt":
        subprocess.run(["taskkill", "/T", "/F", "/PID", str(p.pid)], capture_output=True)
    try:
        p.kill()
    except OSError:
        pass


def _child(cmd, env=None, out=None, timeout=None):
    """THE one process launch. Returns the exit code; raises OSError when it cannot start and
    `_LegTimeout` when it outlives `timeout` (the tree is killed first).

    With no `env`, `out` or `timeout` this is exactly the sequential call: the child inherits this
    process's environment and streams to its stdout."""
    if env is None and out is None and timeout is None:
        return subprocess.call(list(cmd), cwd=REPO)
    p = subprocess.Popen(list(cmd), cwd=REPO, env=env, stdout=out,
                         stderr=subprocess.STDOUT if out is not None else None)
    try:
        return p.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        _kill_tree(p)
        p.wait()
        raise _LegTimeout(timeout)


def _leg_cmd(argv):
    """The exact argv `py()` / `run()` passes for a manifest row's argv."""
    script = argv[0]
    path = os.path.join(BASE, script)
    if not os.path.exists(path) and os.path.exists(os.path.join(REPO, "scripts", script)):
        path = os.path.join(REPO, "scripts", script)
    return (sys.executable, path) + tuple(argv[1:])


class _Job(object):
    def __init__(self, cmd, env, label, pos, ok_codes, after, prio):
        self.cmd, self.env, self.label, self.pos = tuple(cmd), env, label, pos
        self.ok_codes, self.after, self.prio = ok_codes, tuple(after), prio
        self.state, self.outcome, self.rc, self.error = _QUEUED, None, None, None
        self.out_path, self.started, self.finished = None, None, None
        self.consumed = self.replayed = self.lost = False


class _Scheduler(object):
    """Launches submitted legs once their dependencies are DONE, at most `n` at a time.

    `stop_on_red`: a leg is not LAUNCHED once a leg earlier in manifest order finished red, because
    the sequential path would have returned before reaching it. That only saves work — a leg the
    decision code still reaches is then run inline, sequentially, by `run()`."""

    def __init__(self, phase, n, timeout, stop_on_red):
        import tempfile
        import threading
        self.phase, self.n, self.timeout, self.stop_on_red = phase, n, timeout, stop_on_red
        self.cv = threading.Condition()
        self.by_cmd, self.by_label, self.all = {}, {}, []
        self.running = 0
        self.early_key = None
        self.t0 = _clock()
        self.tmp = tempfile.mkdtemp(prefix="zp_hooks_legs_")

    def submit(self, cmd, env, label, pos, ok_codes=(0,), after=(), prio=1):
        with self.cv:
            cmd = tuple(cmd)
            if cmd in self.by_cmd or label in self.by_label:
                raise ValueError("leg %r submitted twice" % (label,))
            missing = [a for a in after if a not in self.by_label]
            if missing:
                # A dependency must be submitted first, which also makes a cycle impossible.
                raise ValueError("leg %r depends on unsubmitted %s" % (label, missing))
            job = _Job(cmd, dict(env), label, pos, ok_codes, after, prio)
            job.out_path = os.path.join(self.tmp, "%02d.out" % len(self.all))
            self.by_cmd[cmd] = job
            self.by_label[label] = job
            self.all.append(job)
            self._pump()

    def _red(self, job):
        if job.state == _CANCELLED:
            return True
        if job.state != _DONE:
            return False
        if job.outcome != LEG_EXITED:
            return True
        return job.ok_codes is not None and job.rc not in job.ok_codes

    def _pump(self):
        """Launch every ready leg. Called with `cv` held, on every submit and every completion."""
        import threading
        changed = True
        while changed:
            changed = False
            for job in sorted((j for j in self.all if j.state == _QUEUED),
                              key=lambda j: (j.prio, j.pos)):
                deps = [self.by_label[a] for a in job.after]
                if any(d.state == _CANCELLED for d in deps) or (
                        self.stop_on_red
                        and any(self._red(o) for o in self.all if o.pos < job.pos)):
                    job.state = _CANCELLED
                    changed = True
                    continue
                if any(d.state != _DONE for d in deps) or self.running >= self.n:
                    continue
                job.state = _RUNNING
                self.running += 1
                job.started = _clock()
                threading.Thread(target=self._work, args=(job,), daemon=True).start()
        self.cv.notify_all()

    def _work(self, job):
        fh = None
        try:
            try:
                fh = open(job.out_path, "wb")
            except OSError as e:
                raise RuntimeError("the leg's capture file could not be opened: %s" % (e,))
            rc = _child(job.cmd, job.env, fh, self.timeout)
            job.rc = rc
            job.outcome = LEG_EXITED
        except _LegTimeout:
            job.outcome, job.rc, job.error = LEG_TIMEOUT, TIMEOUT_RC, self.timeout
        except OSError as e:
            job.outcome, job.error = LEG_NOSTART, e
        except BaseException as e:                          # noqa: BLE001 — never a pass
            job.outcome, job.error = LEG_ERROR, e
        finally:
            if fh is not None:
                fh.close()
            with self.cv:
                job.finished = _clock()
                job.state = _DONE
                self.running -= 1
                self._pump()

    def take(self, cmd):
        """The leg this exact argv names, once it has finished; None to run it inline instead."""
        with self.cv:
            job = self.by_cmd.get(tuple(cmd))
            if job is None or job.consumed:
                return None
            job.consumed = True
            while job.state in (_QUEUED, _RUNNING):
                self.cv.wait(5.0)
            return None if job.state == _CANCELLED else job

    def finish(self, rc):
        """End of the run: launch nothing more, wait for every running leg, replay WHOLE the output
        of every leg the decision code never reached, and refuse a green run that launched one."""
        import shutil
        with self.cv:
            for job in self.all:
                if job.state == _QUEUED:
                    job.state = _CANCELLED
            while self.running:
                self.cv.wait(5.0)
        try:
            unread = [j for j in sorted(self.all, key=lambda j: j.pos) if not j.consumed]
            ran = [j for j in unread if j.state == _DONE]
            if ran:
                print("\n=== concurrent leg(s) this run did not reach — output replayed whole, "
                      "NOT scored (the run had already decided) ===")
                for job in ran:
                    print("--- %s: %s%s ---" % (job.label, job.outcome,
                                               "" if job.rc is None else " exit %d" % job.rc))
                    _replay_job(job)
            never = [j.label for j in unread if j.state == _CANCELLED]
            if never:
                print("  concurrency: not launched (an earlier leg was red, or the run had "
                      "decided): %s" % ", ".join(never))
            if rc == 0 and unread:
                print("\n%s BLOCKED — %d concurrent leg(s) were launched or queued that the "
                      "sequential path never consumed: %s" % (self.phase.upper(), len(unread),
                                                              ", ".join(j.label for j in unread)))
                print("The prefetch list and the decision code disagree. That is a wiring defect;")
                print("it fails CLOSED, because a green run must have read every leg it launched.")
                rc = 1
            print("  concurrency: %d leg(s), %d slot(s), wall %.1fs"
                  % (len(self.all), self.n, _clock() - self.t0))
        finally:
            shutil.rmtree(self.tmp, ignore_errors=True)
        return rc


def _clock():
    import time
    return time.perf_counter()


def _replay_job(job):
    """Write the leg's captured stdout+stderr to this process's stdout, WHOLE and once."""
    if job.replayed:
        return
    job.replayed = True
    try:
        with open(job.out_path, "rb") as fh:
            data = fh.read()
    except OSError as e:
        job.lost = True
        print("  hook: the captured output of %s could not be read back (%s); the leg is "
              "counted as FAILED, never a pass." % (job.label, e))
        return
    sys.stdout.flush()
    buf = getattr(sys.stdout, "buffer", None)
    if buf is not None:
        buf.write(data)
        buf.flush()
    else:
        sys.stdout.write(data.decode("utf-8", "replace"))


def _consume(cmd, job):
    """The sequential call site's result for a leg that ran early. Every non-EXITED outcome is a
    failure with its own message, never a pass (R-ZERONULL)."""
    _replay_job(job)
    if job.env != dict(os.environ):
        diff = sorted(k for k in set(job.env) | set(os.environ)
                      if job.env.get(k) != os.environ.get(k))
        print("  hook: concurrent leg %s ran with an environment that differs from the one the "
              "sequential call passes (keys: %s); its result is REFUSED — counted as FAILED."
              % (job.label, ", ".join(diff)))
        return 1
    if job.lost:
        return 1
    if job.outcome == LEG_NOSTART:
        print("  hook: could not run %s (%s)" % (" ".join(cmd), job.error))
        return 1
    if job.outcome == LEG_ERROR:
        print("  hook: concurrent leg %s failed inside the scheduler (%r); counted as FAILED, "
              "never a pass." % (job.label, job.error))
        return 1
    if job.outcome == LEG_TIMEOUT:
        print("  hook: %s TIMED OUT after %ss and was killed; the output above is all it wrote. "
              "Counted as exit %d — a failure, never a pass." % (job.label, job.error, TIMEOUT_RC))
        EXECUTED.append((_invocation(cmd), TIMEOUT_RC))
        return TIMEOUT_RC
    EXECUTED.append((_invocation(cmd), job.rc))
    return job.rc


def _start_prefetch(phase, n, timeout, timeout_note):
    global _SCHED
    _SCHED = _Scheduler(phase, n, timeout, stop_on_red=(phase == "push"))
    print("  concurrency: %s=%d — legs run in parallel, output replayed whole in manifest order; "
          "per-leg timeout %s%s" % (JOBS_ENV, n, "%ss" % timeout if timeout else "none",
                                    (" (%s)" % timeout_note) if timeout_note else ""))
    return _SCHED


def _start_push_prefetch(n, timeout, timeout_note):
    """Submit every push leg except `batch prepush` (that one waits for the skip decision)."""
    sched = _start_prefetch("push", n, timeout, timeout_note)
    # The receipt key reads tools/verify, which guards rewrites: computed BEFORE anything launches.
    sched.early_key = push_key(REF_TUPLES)
    base_env = dict(os.environ)
    led_env = dict(base_env)
    led_env.update(_PUSH_LEDGER_ENV)
    rows = [(i, label, argv, ok) for i, (label, argv, ok) in enumerate(PRE_PUSH_EXPECT)
            if argv and label != "batch prepush"]
    for i, label, argv, ok in rows:
        if label in _PUSH_PURE:
            sched.submit(_leg_cmd(argv), base_env, label, i, ok, after=(), prio=0)
    for i, label, argv, ok in rows:
        if label in _PUSH_MUTATORS:
            chain = _PUSH_MUTATORS[:_PUSH_MUTATORS.index(label)]
            sched.submit(_leg_cmd(argv), led_env, label, i, ok, after=chain, prio=0)
    for i, label, argv, ok in rows:
        if label not in _PUSH_PURE and label not in _PUSH_MUTATORS:
            readers_after = _PUSH_MUTATORS + _PUSH_PURE
            sched.submit(_leg_cmd(argv), led_env, label, i, ok, after=readers_after,
                         prio=0 if label in _PUSH_FIRST else 1)


def _submit_batch_prepush(ranges, skip):
    """Launch `batch prepush` the moment the skip decision exists, with the environment its
    sequential call site will give it: the push ledger env plus the skip's own switches."""
    env = dict(os.environ)
    env.update(_PUSH_LEDGER_ENV)
    for leg in skip:
        var, val = SKIP_SWITCHES[leg]
        env[var] = val
    pos = [label for label, _a, _o in PRE_PUSH_EXPECT].index("batch prepush")
    bp_after = _PUSH_MUTATORS + _PUSH_PURE
    _SCHED.submit((sys.executable, os.path.join(BASE, "batch.py"), "prepush", "--ranges",
                   ",".join(ranges)), env, "batch prepush", pos, (0,), after=bp_after, prio=0)


def _start_commit_prefetch(n, timeout, timeout_note):
    sched = _start_prefetch("commit", n, timeout, timeout_note)
    env = dict(os.environ)
    for i, (label, argv, ok, _d) in enumerate(PRE_COMMIT_CHECKS):
        sched.submit(_leg_cmd(tuple(argv) + ("--block", "--record")), env, label, i, ok)


def _with_scheduler(body, *args):
    """Run a phase body; whatever it returns or raises, close the scheduler it may have started."""
    global _SCHED
    try:
        rc = body(*args)
    except BaseException:
        sched, _SCHED = _SCHED, None
        if sched is not None:
            sched.finish(1)
        raise
    sched, _SCHED = _SCHED, None
    if sched is not None:
        rc = sched.finish(rc)
    return rc


# ------------------------------------------------------------------ advisory skip
#
# ⭐ TIM'S RULING, 2026-09-30 (ticket `tooling-prepush-pipeline-rerun-necessity`): *"advisory legs
# only; blocking legs and scope derivation from git's stdin refs stay untouched (fences 1 and 2);
# the skip must be control-tested (a mutation that should turn the hook red still does)."*
# Receipts are SINGLE-USE and expire after 24h.
#
# WHAT IT IS: `preflight()` runs this hook to green and `push()` then runs it again on the same
# HEAD and refs. The second run may skip ONLY the legs `advisory_skip_set()` derives as advisory —
# WARN mode AND an emitter that records no gating step. Today that is `agent gate`, the leg that
# makes paid model calls. Every BLOCK leg, the routing probe included, runs on every push.
#
# ⛔ WHAT IT IS NOT: a ledger lookup standing in for a check (fence 2), or trust in a caller's
# claim about scope (fence 1). The match key is the tuple set THIS process read from git's stdin,
# plus a digest of `tools/verify/**` and the HEAD tree; `GITROBOT_RUN_ID` / `GITROBOT_OP` are
# PROVENANCE printed on the SKIPPED line and are never part of the key, because anyone can set an
# environment variable.
#
# ⚠ THE RECEIPT LIVES IN THE GIT COMMON DIRECTORY, beside the installed hooks. `.claude-local` is
# its own repository whose documented flow is bulk staging, so a state file there would be
# committed and pushed; nothing under the common dir is tracked by either repository.

RECEIPT_NAME = "zp_prepush_green.json"
RECEIPT_SCHEMA = "zp.prepush_green.v1"
RECEIPT_MAX_AGE = 24 * 3600
ENV_RUN_ID = "GITROBOT_RUN_ID"
ENV_OP = "GITROBOT_OP"

# `R-ZERONULL`: one VALUE per state, and only MATCHED skips anything. "No receipt" and "could not
# read the receipt" are different answers and must not share a value with each other or with a match.
MATCHED = "MATCHED"
NO_RECEIPT = "NO_RECEIPT"
UNREADABLE = "UNREADABLE"
NOT_TERMINAL = "NOT_TERMINAL"
CONSUMED = "CONSUMED"
STALE = "STALE"
MISMATCH = "MISMATCH"
UNKEYABLE = "UNKEYABLE"
UNCONSUMABLE = "UNCONSUMABLE"

_RECEIPT_PATH_OVERRIDE = None     # controls only; production resolves the common dir


def _now():
    import datetime
    return datetime.datetime.now(datetime.timezone.utc)


def receipt_path():
    """Absolute path of the receipt, or None when the git common directory cannot be resolved."""
    if _RECEIPT_PATH_OVERRIDE:
        return _RECEIPT_PATH_OVERRIDE
    rc, out = git_out("rev-parse", "--git-common-dir")
    if rc != 0 or not out.strip():
        return None
    d = out.strip()
    if not os.path.isabs(d):
        d = os.path.join(REPO, d)
    return os.path.join(d, RECEIPT_NAME)


def tools_digest():
    """sha256 over (path, sha256 of on-disk bytes) for every TRACKED file under tools/verify, or None.

    On-disk bytes because those are what ran. A tracked file missing from disk hashes as ABSENT
    rather than being dropped, so deleting a checker moves the digest."""
    import hashlib
    rc, out = git_out("ls-files", "-z", "--", "tools/verify")
    if rc != 0:
        return None
    paths = sorted(p for p in out.split("\0") if p)
    if not paths:
        return None
    h = hashlib.sha256()
    for rel in paths:
        try:
            with open(os.path.join(REPO, rel), "rb") as fh:
                inner = hashlib.sha256(fh.read()).hexdigest()
        except OSError:
            inner = "ABSENT"
        h.update(("%s\0%s\n" % (rel, inner)).encode("utf-8"))
    return h.hexdigest()


def head_tree():
    rc, out = git_out("rev-parse", "HEAD^{tree}")
    return out.strip() if rc == 0 and out.strip() else None


def push_key(ref_tuples):
    """(key, None) or (None, why). The key is everything a receipt must equal to be used."""
    refs = sorted(tuple(t) for t in ref_tuples)
    if not refs:
        return None, "no ref lines on stdin, so there is nothing to key a receipt on"
    digest = tools_digest()
    if not digest:
        return None, "the tools/verify digest could not be computed"
    tree = head_tree()
    if not tree:
        return None, "HEAD's tree could not be resolved"
    return {"refs": [list(r) for r in refs], "tools_verify_digest": digest,
            "head_tree": tree}, None


def _provenance():
    return os.environ.get(ENV_RUN_ID) or None, os.environ.get(ENV_OP) or None


def _write_json_atomic(path, obj):
    import json
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(obj, fh, indent=2, sort_keys=True)
        fh.write("\n")
    os.replace(tmp, path)


def consult_receipt(key):
    """(status, receipt or None, why). Consumes the receipt on MATCHED — single-use.

    Every branch that is not a full match returns a status other than MATCHED, and the caller
    skips nothing on any of them: no receipt, unreadable, not a terminal pass, already consumed,
    older than 24h or dated in the future, any component of the key unequal."""
    import datetime
    import json
    if key is None:
        return UNKEYABLE, None, "this run could not establish its own match key"
    path = receipt_path()
    if path is None:
        return UNREADABLE, None, "the git common directory could not be resolved"
    if not os.path.exists(path):
        return NO_RECEIPT, None, "no green receipt on disk"
    try:
        with open(path, encoding="utf-8") as fh:
            rec = json.load(fh)
    except (OSError, ValueError) as e:
        return UNREADABLE, None, "receipt is not valid JSON or could not be read (%s)" % (e,)
    if not isinstance(rec, dict) or rec.get("schema") != RECEIPT_SCHEMA:
        return UNREADABLE, None, "receipt has no %s schema marker" % RECEIPT_SCHEMA
    if rec.get("terminal") != "PASS" or rec.get("skipped") != []:
        return NOT_TERMINAL, rec, ("receipt is not from a fully-green run that skipped nothing "
                                   "(terminal=%r, skipped=%r)" % (rec.get("terminal"),
                                                                  rec.get("skipped")))
    if rec.get("consumed_at"):
        return CONSUMED, rec, "receipt was already used at %sZ" % rec.get("consumed_at")
    try:
        ts = datetime.datetime.strptime(rec.get("ts_utc") or "", "%Y-%m-%dT%H:%M:%S").replace(
            tzinfo=datetime.timezone.utc)
    except (TypeError, ValueError):
        return UNREADABLE, rec, "receipt timestamp %r is not parseable" % (rec.get("ts_utc"),)
    age = (_now() - ts).total_seconds()
    if age < 0 or age > RECEIPT_MAX_AGE:
        return STALE, rec, "receipt is %ds old; the window is 0..%ds" % (age, RECEIPT_MAX_AGE)
    for part in ("refs", "tools_verify_digest", "head_tree"):
        if rec.get(part) != key[part]:
            return MISMATCH, rec, "receipt %s differs from this push's" % part
    run_id, op = _provenance()
    rec["consumed_at"] = _now().strftime("%Y-%m-%dT%H:%M:%S")
    rec["consumed_by"] = {"gitrobot_run_id": run_id, "gitrobot_op": op}
    try:
        _write_json_atomic(path, rec)
    except OSError as e:
        return UNCONSUMABLE, rec, "receipt matched but could not be marked used (%s)" % (e,)
    return MATCHED, rec, "matched"


# `R-ZERONULL` on the WRITER side: one value per outcome, every one printed. Only WRITTEN leaves a
# receipt behind; each NOT_WRITTEN_* is a different reason, so "the child ran with agent gate off"
# never shares a value with "the disk refused" or with "this run was red".
RECEIPT_WRITTEN = "WRITTEN"
NOT_WRITTEN_SKIPPED = "NOT_WRITTEN_SKIPPED"
NOT_WRITTEN_OPTED_OUT = "NOT_WRITTEN_OPTED_OUT"
NOT_WRITTEN_UNKNOWN = "NOT_WRITTEN_UNKNOWN"
NOT_WRITTEN_NO_KEY = "NOT_WRITTEN_NO_KEY"
NOT_WRITTEN_KEY_MOVED = "NOT_WRITTEN_KEY_MOVED"
NOT_WRITTEN_NO_PATH = "NOT_WRITTEN_NO_PATH"
NOT_WRITTEN_IO = "NOT_WRITTEN_IO"
NOT_WRITTEN_RED = "NOT_WRITTEN_RED"


def _receipt_state(state, detail):
    print("  green receipt: %s — %s" % (state, detail))
    return state


def write_green_receipt(key, skipped, child_off):
    """Write the receipt for THIS run; return one of the RECEIPT_* / NOT_WRITTEN_* states.

    `child_off` is the legs switched OFF in the environment the `batch.py prepush` child was launched
    with: the hook's own skip AND any opt-out inherited from the caller. A receipt asserts a run in
    which every leg ran, so it is keyed on what the child SAW, never on `skipped` alone. ORDINARY-1
    (2026-09-30): keyed on `skipped`, a caller-exported ZP_AGENT_GATE=0 minted `"skipped": []` and
    the next run skipped on it, so agent gate ran on neither. Now neither a skipped run nor an
    opted-out one can mint the receipt the next run would skip on. `None` (not known) refuses too."""
    if skipped:
        return _receipt_state(NOT_WRITTEN_SKIPPED, "this run skipped %s, and skips must not chain"
                              % ", ".join(skipped))
    if child_off is None:
        return _receipt_state(NOT_WRITTEN_UNKNOWN, "what the batch.py child ran with is not known")
    if child_off:
        return _receipt_state(NOT_WRITTEN_OPTED_OUT,
                              "%s did NOT run in the child (switched off in the environment it "
                              "inherited); a receipt asserts a run in which every leg ran"
                              % ", ".join(child_off))
    if key is None:
        return _receipt_state(NOT_WRITTEN_NO_KEY, "this run had no match key")
    end_key, why = push_key([tuple(r) for r in key["refs"]])
    if end_key != key:
        return _receipt_state(NOT_WRITTEN_KEY_MOVED,
                              why or "tools/verify or HEAD moved during the run")
    path = receipt_path()
    if path is None:
        return _receipt_state(NOT_WRITTEN_NO_PATH, "the git common directory could not be resolved")
    run_id, op = _provenance()
    rec = dict(key)
    rec.update({"schema": RECEIPT_SCHEMA, "terminal": "PASS", "skipped": [],
                "ts_utc": _now().strftime("%Y-%m-%dT%H:%M:%S"),
                "gitrobot_run_id": run_id, "gitrobot_op": op})
    try:
        _write_json_atomic(path, rec)
    except OSError as e:
        return _receipt_state(NOT_WRITTEN_IO, "%s" % (e,))
    return _receipt_state(RECEIPT_WRITTEN, "%s, run %s: single-use, valid 24h, for these exact refs"
                          % (RECEIPT_NAME, run_id or "no gitRobot provenance"))


# ------------------------------------------------------------------ pre-commit pass-cache
#
# ⭐ TIM'S RULING R10, 2026-10-03 (ticket `tooling-precommit-pass-cache-attestation`): gitRobot keeps
# an in-memory attestation of the pre-commit gate it just ran; the hook asks `attest()`; a single-use
# yes skips the hook's pre-commit legs; ANYTHING ELSE runs the full pipeline. Measured before
# building: gitRobot commit run 3ce8b497bf7a (2026-10-04) took 400.4s end to end, of which its own
# gate phase was 212.2s — the hook's second run inside `git commit` was the other ~188s.
#
# ⛔ WHAT IT IS NOT: trust in a caller's claim (ticket fence). `GITROBOT_RUN_ID` only says WHICH
# attestation to ask about; anyone can export it, and a forged one is answered `attested: false` by
# gitRobot, which alone decides — keyed on the tree the HOOK computes, never one it was handed. That
# holds only because the answerer's address is a constant (`ATTEST_URL`), never the environment's.
# ⚠ `attest()` IS NOT READ-ONLY: a yes CONSUMES the attestation and every answer is audited, so it
#   is called at most once per hook run, never without a run id, and never from a control.
#
# `R-ZERONULL`: one VALUE per state, and only ATTEST_YES skips. "Nobody answered" (UNREACHABLE),
# "answered too slowly" (TIMEOUT), "answered no" (DENIED), "answered with an error" (REFUSED /
# NOT_OK), "answered something unreadable" (MALFORMED) and "answered yes about a different tree"
# (TREE_ECHO_MISMATCH) are different answers, and none of them shares a value with the match.
ATTEST_YES = "ATTESTED"
ATTEST_NO_RUN_ID = "NO_RUN_ID"
ATTEST_NO_TREE = "NO_TREE"
ATTEST_DENIED = "DENIED"
ATTEST_REFUSED = "REFUSED"
ATTEST_NOT_OK = "NOT_OK"
ATTEST_MALFORMED = "MALFORMED"
ATTEST_TREE_ECHO = "TREE_ECHO_MISMATCH"
ATTEST_UNREACHABLE = "UNREACHABLE"
ATTEST_TIMEOUT = "TIMEOUT"
ATTEST_ERROR = "ERROR"
ATTEST_RPC_ID = "RPC_ID_MISMATCH"
ATTEST_RUN_ECHO = "RUN_ID_ECHO_MISMATCH"
ATTEST_STATUSES = (ATTEST_YES, ATTEST_NO_RUN_ID, ATTEST_NO_TREE, ATTEST_DENIED, ATTEST_REFUSED,
                   ATTEST_NOT_OK, ATTEST_MALFORMED, ATTEST_TREE_ECHO, ATTEST_UNREACHABLE,
                   ATTEST_TIMEOUT, ATTEST_ERROR, ATTEST_RPC_ID, ATTEST_RUN_ECHO)

# Transport, from the served readme (`GITROBOT_HOST` / `GITROBOT_PORT` = 127.0.0.1 / 8010, "No key,
# no token, no shared secret") and a parent-session probe 2026-10-04: streamable-HTTP MCP at /mcp,
# the same handshake `record.py` uses for the ledger. Not imported from `record.py`: that module
# binds its URL and reconfigures stdout at import, and the hook needs neither.
# ⛔ THE ADDRESS IS A CONSTANT. No environment variable and no argv can choose who answers: an
#   env override let anyone who runs `git commit` point the hook at a stub that says yes, which
#   skipped every BLOCK leg and printed a gitRobot provenance it never had (`/rely` 2026-10-03,
#   BLOCKING-1). The selftest substitutes the transport through `_ATTEST_URL_SEAM`, a module
#   attribute only in-process code can set.
ATTEST_URL = "http://127.0.0.1:8010/mcp"
ATTEST_TIMEOUT_S = 4.0            # per request; an answer slower than this is TIMEOUT -> full run
_ATTEST_TIMEOUT_OVERRIDE = None   # controls only
_ATTEST_URL_SEAM = None           # controls only; in-process, never read from the environment


def _attest_url():
    return _ATTEST_URL_SEAM or ATTEST_URL


def index_tree():
    """The tree the pending commit will carry: `git write-tree` over the index git prepared.

    Runs with cwd=REPO, which `common` derives from THIS file's location; the installed shim runs
    the committing checkout's own copy, so in a worktree commit this is that worktree's index
    (git's exported GIT_INDEX_FILE is inherited too). Never resolved against the main checkout."""
    rc, out = git_out("write-tree")
    tree = out.strip()
    return tree if rc == 0 and tree else None


def _sse_json(body):
    """The JSON-RPC message in a response body, SSE-framed (`data:` line) or bare."""
    import json
    for line in body.splitlines():
        if line.startswith("data:"):
            return json.loads(line[5:].strip())
    return json.loads(body)


def _attest_call(run_id, tree):
    """One MCP round trip to gitRobot's `attest`. Returns `(request_id, parsed JSON-RPC response)`;
    RAISES on any transport or parse failure, which `consult_attest` classifies. No proxy: loopback
    only. The request id travels back so the judge can refuse an answer to some other request."""
    import json
    import urllib.request
    import uuid
    url = _attest_url()
    timeout = _ATTEST_TIMEOUT_OVERRIDE or ATTEST_TIMEOUT_S
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    headers = {"Content-Type": "application/json",
               "Accept": "application/json, text/event-stream"}

    def post(payload, session=None):
        h = dict(headers)
        if session:
            h["Mcp-Session-Id"] = session
        req = urllib.request.Request(url, data=json.dumps(payload).encode("utf-8"),
                                     headers=h, method="POST")
        with opener.open(req, timeout=timeout) as resp:
            return resp.headers.get("Mcp-Session-Id"), resp.read().decode("utf-8")

    sid, _body = post({"jsonrpc": "2.0", "id": str(uuid.uuid4()), "method": "initialize",
                       "params": {"protocolVersion": "2025-06-18", "capabilities": {},
                                  "clientInfo": {"name": "zp-hooks-attest", "version": "1"}}})
    post({"jsonrpc": "2.0", "method": "notifications/initialized"}, session=sid)
    call_id = str(uuid.uuid4())
    _sid, body = post({"jsonrpc": "2.0", "id": call_id, "method": "tools/call",
                       "params": {"name": "attest",
                                  "arguments": {"run_id": run_id, "tree": tree}}}, session=sid)
    return call_id, _sse_json(body)


def _classify_attest_exception(e):
    """Exception -> status. Timeout is told apart from refusal-to-connect; neither is ever a yes."""
    import socket
    import urllib.error
    if isinstance(e, (socket.timeout, TimeoutError)):
        return ATTEST_TIMEOUT
    if isinstance(e, urllib.error.HTTPError):
        return ATTEST_REFUSED
    if isinstance(e, urllib.error.URLError):
        if isinstance(e.reason, (socket.timeout, TimeoutError)):
            return ATTEST_TIMEOUT
        return ATTEST_UNREACHABLE
    if isinstance(e, ValueError):
        return ATTEST_MALFORMED
    if isinstance(e, (ConnectionError, OSError)):
        return ATTEST_UNREACHABLE
    return ATTEST_ERROR


def _judge_attest(res, tree, run_id, call_id):
    """(status, detail) from a parsed JSON-RPC response. ATTEST_YES only when ALL hold: the
    response `id` is the request id this hook sent; it carries no `error`; `isError` is absent or
    the boolean False; `ok` is exactly True; `attested` is exactly True; and the echoed `run_id`
    and `tree` both equal the ones this hook sent."""
    if not isinstance(res, dict):
        return ATTEST_MALFORMED, "the response is not a JSON object"
    if res.get("id") != call_id:
        return ATTEST_RPC_ID, "the response id %r is not this hook's request id %r" % (
            res.get("id"), call_id)
    if "error" in res:
        return ATTEST_REFUSED, "JSON-RPC error (a result beside it is ignored): %s" % (
            res.get("error"),)
    if "result" not in res:
        return ATTEST_MALFORMED, "the response carries no result"
    result = res["result"]
    if not isinstance(result, dict):
        return ATTEST_MALFORMED, "the result is not an object"
    if "isError" in result and result["isError"] is not False:
        content = result.get("content") or [{}]
        text = content[0].get("text") if isinstance(content[0], dict) else content[0]
        return ATTEST_REFUSED, "the server answered isError: %s" % (text,)
    sc = result.get("structuredContent")
    if not isinstance(sc, dict):
        return ATTEST_MALFORMED, "no structuredContent object in the result"
    if sc.get("ok") is not True:
        return ATTEST_NOT_OK, "ok=%r, why=%r" % (sc.get("ok"), sc.get("why"))
    if sc.get("attested") is False:
        return ATTEST_DENIED, "attested: false, why: %s" % (sc.get("why"),)
    if sc.get("attested") is not True:
        return ATTEST_MALFORMED, "attested=%r is not the boolean true" % (sc.get("attested"),)
    if sc.get("tree") != tree:
        return ATTEST_TREE_ECHO, "attested a tree %r, but this hook asked about %r" % (
            sc.get("tree"), tree)
    if sc.get("run_id") != run_id:
        return ATTEST_RUN_ECHO, "attested run %r, but this hook asked about run %r" % (
            sc.get("run_id"), run_id)
    return ATTEST_YES, "attested"


def consult_attest():
    """(status, run_id, tree, detail). Every path but a full yes returns a status other than
    ATTEST_YES, and the caller then runs every leg."""
    run_id, _op = _provenance()
    if not run_id:
        return ATTEST_NO_RUN_ID, None, None, "no %s in the environment (a hand-run commit)" % ENV_RUN_ID
    tree = index_tree()
    if not tree:
        return ATTEST_NO_TREE, run_id, None, "git write-tree failed, so there is no tree to ask about"
    try:
        call_id, res = _attest_call(run_id, tree)
    except Exception as e:                       # noqa: BLE001 — every failure is a full run
        return _classify_attest_exception(e), run_id, tree, "%s: %s" % (type(e).__name__, e)
    try:
        status, detail = _judge_attest(res, tree, run_id, call_id)
    except Exception as e:                       # noqa: BLE001 — a judge that crashes is no yes
        return ATTEST_ERROR, run_id, tree, "judging the answer raised %s: %s" % (type(e).__name__, e)
    return status, run_id, tree, detail


def _emitter_of(argv):
    """Repo-relative module a push row's child records from, or None for an inline row."""
    if not argv:
        return None
    if os.path.exists(os.path.join(HERE, argv[0])):
        return "tools/verify/%s" % argv[0]
    if os.path.exists(os.path.join(REPO, "scripts", argv[0])):
        return "scripts/%s" % argv[0]
    return None


def _hook_rows():
    """(label, derived mode, emitter) for every row of THIS hook's push manifest."""
    argv = {label: a for label, a, _ok in PRE_PUSH_EXPECT}
    return [(label, mode, _emitter_of(argv.get(label)))
            for label, mode, _desc in _bind_push_modes(PRE_PUSH_PLAN, PRE_PUSH_EXPECT)]


REGISTRY = os.path.join(HERE, "required.v2.json")
BATCH_SRC = os.path.join(HERE, "batch.py")


def _registry_types(path=None):
    """The registry's `types` mapping, or None if it cannot be read."""
    import json
    try:
        with open(path or REGISTRY, encoding="utf-8") as fh:
            types = json.load(fh)["types"]
        return types if isinstance(types, dict) else None
    except (OSError, ValueError, KeyError, TypeError):
        return None


def gating_emitters(path=None):
    """Repo-relative modules that emit a record for a step that GATES some action, or None.

    A step gates unless the registry declares `actions: []` EXPLICITLY. An ABSENT `actions` key
    means the registry `default`, `REQUIRED_FOR_ALL_ACTIONS` — `claim_review` is the live instance,
    emitted by `check_frozen.py` with no `actions` key and admitted at push. Reading absence as
    "gates nothing" would make `check_frozen` skippable and starve `claim_review`.

    ⚠ `R-ZERONULL`: `None` (could not read the registry) is DISTINCT from an empty set (read it,
    nothing gates). Every consumer treats `None` as "nothing is skippable"."""
    types = _registry_types(path)
    if types is None:
        return None
    out = set()
    for _name, spec in types.items():
        if not isinstance(spec, dict) or not spec.get("module"):
            continue
        if "actions" not in spec or spec["actions"]:
            out.add(spec["module"])
    return out


def _batch_rows(src_path=None, types=None):
    """(label, mode, emitter) for every row of `batch.py prepush`'s manifest, or None.

    READ FROM THE SOURCE, not imported and not copied: the rows are the literal list passed to
    `report.plan(...)` inside `cmd_prepush`, which is exactly the manifest that command prints.
    `batch.py` is a PINNED producer (`decls`, `pdf_coupling`), and the ledger reads the pin from
    the main checkout's registry, so this change could not edit it from a worktree — measured: the
    commit was refused by V16c naming the unapproved blob. Reading its manifest needs no edit.

    The EMITTER of a row is the registry step whose name is the label with spaces as underscores
    when that step declares a `module` (`agent gate` -> `agent_gate` -> `tools/verify/agent_gate.py`);
    otherwise the row is computed inside `batch.py` and its emitter is `batch.py`, which records
    the gating `decls` and `pdf_coupling` — so no such row can ever be skippable."""
    import ast
    try:
        with open(src_path or BATCH_SRC, encoding="utf-8") as fh:
            tree = ast.parse(fh.read())
    except (OSError, SyntaxError, ValueError):
        return None
    types = _registry_types() if types is None else types
    if types is None:
        return None
    plans = []
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == "cmd_prepush":
            for sub in ast.walk(node):
                if (isinstance(sub, ast.Call) and isinstance(sub.func, ast.Attribute)
                        and sub.func.attr == "plan" and sub.args):
                    try:
                        plans.append(ast.literal_eval(sub.args[0]))
                    except (ValueError, TypeError, SyntaxError):
                        return None
    if len(plans) != 1:
        return None                     # zero or two manifests: refuse to guess which one ran
    rows = []
    for row in plans[0]:
        if not (isinstance(row, tuple) and len(row) == 3):
            return None
        label, mode, _desc = row
        spec = types.get(label.replace(" ", "_"))
        emitter = spec.get("module") if isinstance(spec, dict) else None
        rows.append((label, mode, emitter or "tools/verify/batch.py"))
    return rows


def advisory_skippable(rows, gating=False):
    """The labels in `rows` [(label, mode, emitter)] whose mode is exactly WARN AND whose emitter
    records no gating step. `None` in, or an unreadable registry, gives `None` — never an empty
    set a caller could not tell from "read it, nothing qualifies"."""
    if gating is False:
        gating = gating_emitters()
    if gating is None or rows is None:
        return None
    return frozenset(label for label, mode, emitter in rows
                     if mode == "WARN" and emitter and emitter not in gating)


# How each skippable leg is actually switched off in the `batch.py prepush` child. `agent_gate.py`
# already reads `ZP_AGENT_GATE` at import and prints `skip` when it is not "1" (an opt-out that
# predates this change), so the skip needs no edit to the pinned `batch.py`. A derivably advisory
# leg with NO entry here is simply not skipped: it runs, and the hook says so.
SKIP_SWITCHES = {"agent gate": ("ZP_AGENT_GATE", "0")}

# The value at which each switched leg RUNS, mirroring the leg's own reader: `agent_gate.py` sets
# `ENABLED = os.environ.get("ZP_AGENT_GATE", "1") == "1"`, so ANY other value switches it off, not
# only "0". The receipt writer keys on this, never on the hook's own skip list (ORDINARY-1).
SWITCH_ON = {"ZP_AGENT_GATE": "1"}


def legs_disabled(environ=None):
    """Sorted switched legs that a child launched with `environ` (default: this process's, which is
    what `run()` passes on) would NOT run. A switch with no known run-value counts as off: what the
    child would do cannot be told, and a receipt may only assert a run in which every leg ran."""
    env = os.environ if environ is None else environ
    out = []
    for leg, (var, _off) in SKIP_SWITCHES.items():
        on = SWITCH_ON.get(var)
        if on is None or env.get(var, on) != on:
            out.append(leg)
    return sorted(out)


def advisory_skip_set():
    """THE ONE SET of legs a matched green receipt may skip, or None when it cannot be derived.

    DERIVED, never listed: `advisory_skippable` over this hook's manifest (modes derived by
    `_bind_push_modes` from the same `ok_codes` `reconcile` enforces) and over `batch.py`'s
    manifest, against the registry's gating emitters. `check_frozen` is WARN here and is excluded
    because its module also emits `claim_review`, which gates."""
    try:
        hook = advisory_skippable(_hook_rows())
        bat = advisory_skippable(_batch_rows())
    except Exception as e:                                  # noqa: BLE001 — nothing skips on error
        print("  advisory skip: derivation errored (%r); nothing is skippable." % (e,))
        return None
    if hook is None or bat is None:
        return None
    return hook | bat


def skip_set_violations(skippable):
    """Every way `skippable` breaks the invariant: a BLOCK row, or a gating emitter, in it."""
    gating = gating_emitters()
    rows = _batch_rows()
    if gating is None or rows is None:
        return ["the registry or batch.py's manifest is unreadable; the invariant cannot be checked"]
    out = []
    rows = _hook_rows() + rows
    for label, mode, emitter in rows:
        if label not in (skippable or ()):
            continue
        if mode != "WARN":
            out.append("%s is a %s row" % (label, mode))
        if emitter in gating or not emitter:
            out.append("%s's emitter %s records a gating step (or is unknown)" % (label, emitter))
    return out


# ------------------------------------------------------------------ pre-commit

# ⚠⚠ ONE TABLE DRIVES BOTH THE MANIFEST AND THE LOOP, AND THAT IS THE WHOLE POINT OF ITS SHAPE.
# Until 2026-08-30 the printed plan was a hand-written SECOND COPY of the execution list, and
# `/rely` RLY27-1 measured what that buys: with the entire checker loop DELETED, this hook still
# printed `plan 11 check(s): 11 BLOCK, 0 advisory`, listed all eleven rows by name, ran nothing,
# and exited 0 -- and `check_checkers --block` reported `violations: 0` over that neutered gate,
# because its "is invoked" property is satisfied by the pre-push call site and cannot see a
# commit-time call disappear. The realistic variant reproduced too: dropping one entry from the
# tuple while leaving its manifest row gave eleven advertised, ten executed, exit 0.
# A manifest that CAN disagree with the loop is a claim about the loop, not a description of it.
#
# Each row is (label, argv, ok_codes, description). `ok_codes` is the exit codes that are NOT a
# finding -- see check_paths below for the one entry that needs more than (0,).
PRE_COMMIT_CHECKS = [
    ("check_pov", ("check_pov.py",), (0,),
     "POV claims declare a KIND; DENIALs never allowed"),
    ("check_modal", ("check_modal.py",), (0,),
     "modal claims carry a measurement or a reduction"),
    ("check_classes", ("check_classes.py",), (0,),
     "a new requirements class records a degeneracy verdict"),
    ("check_prose", ("check_prose.py",), (0,),
     "prose caps: block size, docstring vs decl, gloss labels"),
    # ⚠ AT COMMIT, NOT ONLY AT PUSH, AND FOR A REASON THE OTHER FOUR DO NOT SHARE. Double-encoded
    # text is valid UTF-8, so it survives every other check, renders plausibly in a diff, and the
    # window in which the author still knows which write did it is minutes long.
    ("check_encoding", ("check_encoding.py",), (0,),
     "BOM + undecodable BLOCK; suspected double-encoding WARNS"),
    # ⚠⚠ THE SIX BELOW WERE PUSH-ONLY UNTIL 2026-08-30, AND THAT WAS A HOLE, NOT A SAVING.
    # gitRobot admits 20 keys for a push and 18 for a commit; this hook emits 11. The other six ran
    # only in `pre_push`, against the TIP -- so a second commit silently invalidated the first, and
    # no intermediate commit could EVER reach the bar through ordinary work. Measured: a 2-commit
    # range read 11/19 with both commits made through the full pipeline, hook green each time.
    # The remedy on offer was `squash`, i.e. rewriting history on every push to satisfy a rule
    # that exists BECAUSE intermediate commits are fetchable, bisectable and citable forever.
    # ⚠ They already BLOCK at push, so this adds NO new failure class -- same argument
    # `pre_commit` makes for the original five, one paragraph down. Cost 16.1s (~5.9s -> ~22s).
    # ⚠ NOT the whole gap: `build`, `check_checkers`, `check_claude_md`, `check_hashes`,
    # `claim_review`, `guards` and `pdf_coupling` still have no pre-commit producer. Narrowed, not
    # closed (RLY27-5).
    #
    # ⚠⚠ EXIT 3 IS "SKIPPED PART OF MY SCOPE", NOT A FINDING -- `check_paths.EXIT_SKIPPED`, and
    # `pre_push` has always allowed it (see the File-reference check below). When these six were
    # added here on 2026-08-30 the loop treated every non-zero as a violation, so in any clone or
    # worktree WITHOUT a built `.lake` the pinned Mathlib is absent, `check_paths` returns 3, and
    # every commit was refused naming a defect that does not exist -- with `--no-verify`, which
    # skips all eleven, as the only escape. Measured by `/rely` RLY27-7 in a fresh worktree.
    # ⚠ SCOPE IS MARKDOWN + LEAN, AND SAYING MORE IS THE WORSE ERROR. Round 1 (RLY27-4) found this
    # row UNDERSTATED its scope; the repair overshot and claimed `scripts/**.py` too, which round 2
    # (R2-3) measured false: the only `scan()` calls that can set `failed` are markdown and Lean,
    # `tracked_scripts()` is reached from the selftest pin and `--claim` alone, the build-script
    # block prints "INFORMATIONAL: does not fail the run", and the ledger subject list is
    # `tracked_markdown() + tracked_lean()`. Live: 10 hits under `scripts/`, exit 0. An overstated
    # manifest is worse than an understated one -- it is a claim of coverage nobody has.
    ("check_paths", ("check_paths.py",), (0, 3),
     "every repo-relative reference in tracked markdown and Lean resolves "
     "(3 = scope skipped for want of a built .lake, not a finding; scripts/ scanned INFORMATIONALLY)"),
    ("check_moved", ("check_moved.py",), (0,),
     "nothing points at a path that was relocated"),
    ("check_negatives", ("check_negatives.py",), (0,),
     "a universal negative carries a date or a search record"),
    ("check_figures", ("check_figures.py",), (0,),
     "an artifact count carries a date, or is measured on demand"),
    ("check_invariants", ("check_invariants.py",), (0,),
     "Engineer's Takes filled; LEAN_CUSTOM_REGISTRY count matches"),
    # ⚠ `decls` lives in `batch.py` behind a subcommand rather than being a `check_*.py`, which is
    #   the only reason its argv has two elements. Same handling in every other respect.
    ("decls", ("batch.py", "decls"), (0,),
     "every new declaration has #print axioms + an ssot.json row"),
]

# ⚠ THE MODE COLUMN IS DERIVED, NOT ASSERTED. `/rely` R2-2: it was the literal "BLOCK" on every
# row, so widening an entry's `ok_codes` to swallow exit 1 left all eleven rows still advertising
# BLOCK while nothing could block. A row blocks exactly when the universal failure code is not
# tolerated, so that is what the column now computes.
def _mode(ok_codes):
    return "BLOCK" if 1 not in ok_codes else "WARN"


# The manifest is GENERATED from the table above -- but see `reconcile()`: generation alone only
# moves the divergence from "two lists" to "a list and a loop". The manifest is BINDING because
# every advertised row is checked against what actually launched.
PRE_COMMIT_PLAN = [(label, _mode(ok), desc) for label, _argv, ok, desc in PRE_COMMIT_CHECKS]

PRE_PUSH_PLAN = [
    ("hooks armed", "BLOCK", "the installed hooks match their tracked sources"),
    ("quarantine", "BLOCK", "private/* branches never reach a remote"),
    ("advisory-skip controls", "BLOCK", "the green-receipt match that may skip an ADVISORY leg is "
                                        "run against a mutant per control, in a child, before any "
                                        "receipt is read; its own output prints the count"),
    ("routing control selftest", "BLOCK", "the routing control's OWN controls (probe --selftest): "
                                          "its pool, retry, observable, clean-phase and vacuity "
                                          "machinery, each run against a mutant; 28 probe controls, "
                                          "pinned (the probe refuses if its list disagrees)"),
    ("guards", "BLOCK", "every enumerated ROUTE to a guarded property still behaves"),
    ("routing control", "BLOCK", "the behavioural mutation probe: mutations of the routing and "
                                 "enforcement routes, each required to turn its named ROW red, move "
                                 "the prepush EXIT CODE, or reach a named REFUSAL; "
                                 "23 probe mutation rows, pinned (fails CLOSED on a moved anchor or "
                                 "a changed count). "
                                 "RLY28-1 IS covered. The recorded VALUE of the four inline "
                                 "non-routing legs is covered through the agreement check, observed "
                                 "at ROUTING 0 (RLYB4-1/1b with meta-controls deleting or weakening "
                                 "that check); the two review-signal legs' site is NOT"),
    ("check_paths", "BLOCK", "every repo-relative reference in tracked markdown resolves"),
    ("check_claude_md", "BLOCK", "CLAUDE.md shape contract: rooted paths resolve, named checkers exist "
                                 "(3 legs still PENDING — it says so on every run)"),
    ("check_briefs", "BLOCK", "a gate brief instructs a command that WORKS: every --flag exists, "
                              "every --step is REGISTERED in the ledger, every cited path resolves. "
                              "2 WARN legs print their count every run"),
    ("check_moved", "BLOCK", "nothing points at a path that was relocated"),
    ("check_negatives", "BLOCK", "a universal negative carries a date or a search record"),
    ("check_figures", "BLOCK", "an artifact count carries a date, or is measured on demand"),
    # ⚠ WARN, NOT BLOCK, AND THE RETIREMENT IS THE REASON (Tim, 2026-08-23). The freeze comparison
    # is from the topology that preceded the independent-git-spaces rewrite, so its snapshot cannot
    # correspond to anything now and it fails PERMANENTLY — measured, 5 failing subjects on a clean
    # tree. The ledger retired it as a gate the same day (`actions: []`, stated reason) while keeping
    # it REGISTERED so it still records. This row said BLOCK for eight commits after that, so the
    # hook refused every push the ledger was willing to allow: a manifest telling the truth about a
    # gate the server had already stood down.
    # ⚠ It still RUNS and still RECORDS. What is retired is the freeze comparison's authority to
    # stop a push, never the emitter — `claim_review` is emitted by this file alone, and killing the
    # run would leave that key permanently MISSING and block every push forever, which is strictly
    # worse than the failure being removed.
    ("check_frozen", "WARN", "RETIRED as a gate (dead topology) — still runs, still records; "
                             "claim_review rides on it and must keep being emitted"),
    ("check_checkers", "BLOCK", "every checker has passing controls, and something invokes it"),
    ("check_invariants", "BLOCK", "Engineer's Takes filled; LEAN_CUSTOM_REGISTRY count matches"),
    ("check_pov", "BLOCK", "POV claims declare a KIND; DENIALs never allowed"),
    ("check_modal", "BLOCK", "modal claims carry a measurement or a reduction"),
    ("check_classes", "BLOCK", "a new requirements class records a degeneracy verdict"),
    ("check_prose", "BLOCK", "prose caps, baselined; NEW sites only"),
    ("check_encoding", "BLOCK", "BOM + undecodable BLOCK; suspected double-encoding WARNS"),
    ("decls", "BLOCK", "every new declaration has #print axioms + an ssot.json row"),
    ("check_hashes", "BLOCK", "build-script fingerprints match register.md"),
    # ⚠ NOT advisory: scan_pdfs' exit code IS the hook's when everything else passes, so it
    # can block a push on its own. Calling it "report" while it did exactly that is a
    # manifest that lies, which is worse than no manifest (/rely pass 3 and 4).
    ("scan_pdfs", "BLOCK", "PDF asset scan — its exit code becomes the hook's"),
    # ⚠ "/rely routing" is no longer one mode: the logic and exemption-switch legs BLOCK, the
    # routed-prose leg WARNS (downgraded 2026-08-21, rung 5). Said here too, because a manifest that
    # over-states at ONE entry point is the same defect as over-stating at all four.
    ("batch prepush", "BLOCK", "trigger 5, the three review signals, and /rely routing — logic and "
                               "exemption switches BLOCK, routed prose WARNS"),
]


def _bind_push_modes(plan, expect):
    """Replace each push row's asserted mode with the one its tolerances actually imply.

    ⚠⚠ R3-2, closed here rather than by editing twenty strings. The column was 20 literal
    "BLOCK"s, so deleting a single `return 1` left a row advertising a block it no longer
    performed — measured three times, once against the row whose own text reads "its exit code
    becomes the hook's". Now the same `ok_codes` that `reconcile` enforces also decides what the
    row is allowed to CLAIM, so the manifest and the enforcement cannot disagree: there is one
    fact and two readers of it.
    """
    # ⚠⚠ ONLY ROWS THAT LAUNCH A CHILD GET A DERIVED MODE. Caught in the receipt of the first
    # preflight after this function landed: `quarantine` printed WARN over a property that is
    # ENFORCED TWICE — once inline and once by `reconcile`'s independent re-test. Its `ok_codes` is
    # None because it launches nothing to have an exit code, and None was being read as "tolerates
    # any failure". Two different facts sharing one encoding, in the function written to stop a row
    # advertising a mode nothing enforces. An inline row keeps the mode the plan ASSERTS, because
    # there is no exit code to derive one from and inventing WARN is worse than trusting the author.
    tol = {label: ok for label, argv, ok in expect if argv}
    inline = {label for label, argv, _ok in expect if not argv}
    out = []
    for label, asserted, desc in plan:
        if label in inline:
            out.append((label, asserted, desc))
            continue
        ok = tol.get(label, (0,))
        out.append((label, "WARN" if ok is None or 1 in ok else "BLOCK", desc))
    return out

# ⚠⚠ WHAT EACH PUSH ROW MUST ACTUALLY LAUNCH. `/rely` R2-4: the commit manifest was made binding
# and this one was left a hand-written second copy -- the same defect fixed at ONE of its TWO
# sites, which is the recurring shape (`SH-3`) this project keeps paying for. Deleting the
# `check_hashes` call site, and separately `guards.py`'s, left the manifest printing every row it
# prints today (measured 2026-08-30) and naming both, exit 0. `guards.py` is the exemption-surface
# control that runs FIRST precisely
# because a green checker over a holed surface is a false zero -- so its silent disappearance is
# the worst single case in the file.
#
# `None` marks a row handled INLINE with no child process. `reconcile` reports those as unverifiable
# rather than counting them as satisfied: an honest gap beats a false tick.
# ⚠⚠ THE FLAGS ARE PART OF THE EXPECTATION, NOT DECORATION. `/rely` R3-3: matching on the script
# name alone let a four-character edit disable the check while reconciliation still reported
# success -- strip `--block` from the commit loop and eleven children launch, findings print, and
# the run exits 0. That was measured on real violations, not hypothetically: a BOM in `GUIDE.md`
# gives `check_encoding` exit 0 without `--block` and exit 1 with it; a theorem with no
# `#print axioms` entry gives `batch.py decls` exit 0 without and exit 1 with. The flag IS the
# enforcement, so an expectation that ignores it is checking the wrong thing.
# Third element is `ok_codes`: the exit codes that are NOT a finding. `None` means "any code
# tolerated" and is reserved for the one row the manifest itself declares WARN. Everything else
# names its tolerances explicitly, so the push verdict is derived from recorded exit codes rather
# than from twenty hand-written `return 1` statements (R4-1 at the push site; R3-2's real fix).
PRE_PUSH_EXPECT = [
    ("hooks armed", ("install_hooks.py", "--check"), (0,)),
    # ⚠ Launches nothing — but NOT unobserved any more: `reconcile` re-tests the property itself
    #   from `REFS_SEEN`. R4-2 measured the hole: delete the inline branch and a `private/*` ref
    #   pushed green while the manifest printed this row's name.
    ("quarantine", None, None),
    ("advisory-skip controls", ("hooks.py", "selftest"), (0,)),
    # ⚠ BOTH probe rows name their argument: `_found` matches by PREFIX, so a bare
    #   `("probe_routing_behavioural.py",)` would be satisfied by the `--selftest` launch alone.
    ("routing control selftest", ("probe_routing_behavioural.py", "--selftest"), (0,)),
    ("guards", ("guards.py", "--record"), (0,)),
    ("routing control", ("probe_routing_behavioural.py", "--mutations"), (0,)),
    # ⚠ 3 = scope skipped for want of a built .lake, tolerated at both phases (RLY27-7).
    ("check_paths", ("check_paths.py", "--all", "--warn-private", "--record"), (0, 3)),
    ("check_claude_md", ("check_claude_md.py", "--record"), (0,)),
    ("check_briefs", ("check_briefs.py", "--record"), (0,)),
    ("check_moved", ("check_moved.py", "--block", "--record"), (0,)),
    ("check_negatives", ("check_negatives.py", "--block", "--record"), (0,)),
    ("check_figures", ("check_figures.py", "--block", "--record"), (0,)),
    # ⚠ The manifest says WARN and means it: RETIRED as a gate (dead topology), still runs, still
    #   records, because `claim_review` rides on its emitter. Any exit is tolerated HERE, and that
    #   is the one row where `None` is correct rather than lazy.
    ("check_frozen", ("check_frozen.py", "--record"), None),
    ("check_checkers", ("check_checkers.py", "--block", "--record"), (0,)),
    ("check_invariants", ("check_invariants.py", "--record"), (0,)),
    ("check_pov", ("check_pov.py", "--block", "--record"), (0,)),
    ("check_modal", ("check_modal.py", "--block", "--record"), (0,)),
    ("check_classes", ("check_classes.py", "--block", "--record"), (0,)),
    ("check_prose", ("check_prose.py", "--block", "--record"), (0,)),
    ("check_encoding", ("check_encoding.py", "--block", "--record"), (0,)),
    ("decls", ("batch.py", "decls", "--block", "--record"), (0,)),
    ("check_hashes", ("check_hashes.py", "--record"), (0,)),
    ("scan_pdfs", ("scan_pdfs.py",), (0,)),
    ("batch prepush", ("batch.py", "prepush"), (0,)),
]


def pre_commit():
    """The pre-commit phase. The body is `_pre_commit`; this closes any scheduler it started."""
    return _with_scheduler(_pre_commit)


def _pre_commit():
    """The eleven checkers BLOCK; nothing here warns.

    The stub-first protocol commits `sorry`-stubbed files on purpose, so BUILD state must never
    gate here — and none of these reads `sorry`, the build, or completeness. They are
    baselined, sit at zero new, and already block at push, so blocking here adds no new failure
    class; it moves an identical, already-mandatory failure earlier, where the fix is cheap.

    ⚠⚠ SIX WERE ADDED 2026-08-30 SO THAT EVERY COMMIT EARNS ITS OWN ADMISSION KEYS. Recording
    them only in `pre_push` meant they were keyed to the TIP, so an intermediate commit could
    never satisfy the commit bar and `can_push` refused every multi-commit range. The fix is
    HERE rather than in `batch.py precommit` for the reason the comment below already gives:
    that command is MANUAL, and the path that fires on every commit is this hook."""
    report.banner("pre-commit pipeline", [
        ("entry", ".git/hooks/pre-commit -> hooks.py pre_commit"),
        ("scope", "the WORKING TREE as it stands (checkers scan the corpus on disk)"),
        ("exempt", "vendored: %s" % (", ".join(sorted(vendored.allowlist())) or "(allowlist empty)")
                   + " + anything under Vendored/"),
        ("not run", "lake build / purity / ssot — stub-first commits incomplete work on purpose"),
    ])
    report.plan(PRE_COMMIT_PLAN)

    # ⚠⚠ THE PASS-CACHE. The ONLY branch that skips is an exact `ATTEST_YES`; every other status —
    #   no run id, no tree, denied, refused, not ok, malformed, echoed tree or run id differs,
    #   response id differs, unreachable, timeout, error — falls through to the full pipeline below. The skip records nothing and
    #   writes nothing: gitRobot's gate already ran THIS function on THIS tree and recorded its
    #   verdicts. `R-NOCONV`: what still BLOCKS is printed on every run, matched or not.
    status, run_id, tree, detail = consult_attest()
    if status == ATTEST_YES:
        print("SKIPPED pre-commit: gitRobot gate %s passed for tree %s" % (run_id, tree))
        print("  (single-use attestation; that gate ran these %d legs on this exact tree in this run)"
              % len(PRE_COMMIT_CHECKS))
        print("  BLOCK rows launched: 0 of %d; skipped on attestation %s"
              % (len(PRE_COMMIT_CHECKS), ATTEST_YES))
        return 0
    print("  pass-cache: none — %s: %s; every leg runs." % (status, detail))

    failed = []
    # ⚠⚠ RECORDING BELONGS HERE, NOT IN `batch.py precommit` — measured 2026-08-23 and it was a
    # silent miss. `batch.py precommit` is a MANUAL command; the path that actually fires on every
    # commit is this hook. Wiring `--record` there meant every ledger record came from someone
    # typing the command, never from a commit — so the recorded basis was an index tree that no
    # commit ever had (`cbac5acb` recorded, `HEAD^{tree}` = `292ac861`), and six to fifteen paths
    # per step read STALE for content nobody had changed. Caught by mcp-mayhem, REQ-1.
    #
    # ⚠ INDEX, NOT HEAD. Git has already prepared the index by the time this hook runs, so the
    # staged tree IS the tree the pending commit will carry. HEAD is still the PARENT here.
    # ⚠⚠ ASSIGNMENT, NOT `setdefault` — changed 2026-08-30, `/rely` RLY27-3. `setdefault` let the
    # CALLER'S environment win: exporting `ZPLEDGER_RUN=whatever-i-say` and `ZPLEDGER_BASIS=HEAD`
    # both reached every checker unchanged, which defeats V9's run-id provenance at the commit gate
    # and, under `HEAD`, makes `ledger_subjects` drop exactly the paths just staged — the ledger
    # then reports narrowed coverage WITHOUT blocking. `pre_push` has always used assignment, for
    # the reason stated at its own call site: the environment here could only ever be wrong.
    os.environ.update(_COMMIT_LEDGER_ENV)
    # ⚠ CONCURRENT LAUNCH, SEQUENTIAL DECISION. Every leg here only READS the tree and records its
    #   own distinct step, so all eleven may start now; the loop below still consumes them one by
    #   one, in this order, through `py()`. `ZP_HOOK_JOBS=1` creates no scheduler at all.
    _jobs, _note = hook_jobs()
    if _note:
        print("  concurrency: %s" % _note)
    if _jobs > 1:
        _t, _tnote = leg_timeout()
        _start_commit_prefetch(_jobs, _t, _tnote)
    for label, argv, ok_codes, _desc in PRE_COMMIT_CHECKS:
        rc = py(*argv, "--block", "--record")
        # ⚠ EXIT 2 IS "COULD NOT BE RECORDED", NOT "FAILED". A checker that ran and could not reach
        # the ledger produced no key, so the commit must not proceed as though it had — but the
        # reader needs the outage named, not a phantom finding.
        # ⚠ A checker MISSING FROM DISK also surfaces as 2 today and is reported with the same
        #   wording, which fails closed but diagnoses wrong (RLY27-6, ledgered, not fixed here).
        if rc == 2:
            failed.append("%s (ran; verdict NOT RECORDED — no key exists for this content)"
                          % label)
        elif rc not in ok_codes:
            failed.append("%s (exit %d)" % (label, rc))

    # ⚠⚠ THE MANIFEST IS BINDING. Every row above named a child; this is where we confirm each one
    # actually launched. Run BEFORE the findings report, because "the gate did not run" outranks
    # "the gate found nothing" -- a neutered loop produces an empty `failed` list, which is exactly
    # what a clean run produces.
    # ⚠ The expectation carries `--block --record`, not just the script name (R3-3): those flags
    #   ARE the enforcement, and a name-only match passes a run that launched every child with the
    #   teeth removed.
    # ⚠ `ok_codes` travels with the row, so the accept/reject decision is made from the RECORDED
    #   exit code. Exit 2 stays distinguishable: it is not in any row's `ok_codes`, so it blocks
    #   here too, and the loop above has already named it as a recording failure rather than a
    #   finding.
    if reconcile("commit",
                 [(label, tuple(argv) + ("--block", "--record"), ok)
                  for label, argv, ok, _d in PRE_COMMIT_CHECKS]):
        return 1

    if failed:
        print("")
        print("Commit blocked — NEW violations in: " + " ".join(failed))
        print("These are baselined checkers, so a hit is a genuinely new site, and each one")
        print("already blocks at push. Fix it now — ⚠ writing it into .claude-local/DEFECTS.md")
        print("clears nothing here: nothing reads that file, and every leg above recomputes.")
        print("Bypassing here only defers the identical block to the push.")
        return 1
    return 0


# ------------------------------------------------------------------ pre-push

def parse_refs(stream):
    """git feeds '<local_ref> <local_sha> <remote_ref> <remote_sha>' per ref on stdin.

    Returns (ranges, quarantined). `private/*` branches are permanently local and must never reach
    any remote, in either the local or the remote ref position."""
    ranges, quarantined, malformed = [], [], []
    for line in stream:
        if not line.strip():
            continue
        parts = line.split()
        if len(parts) != 4:
            # ⚠ FAIL CLOSED. This used to `continue`, so a ref line git fed us in a shape we did not
            # expect vanished — and a push whose every line was dropped got an EMPTY range set,
            # which reads downstream as "no reviewable change, signals not required". A parse we do
            # not understand is not permission to skip the review (measured, /rely pass 4).
            malformed.append(line.rstrip())
            continue
        local_ref, local_sha, remote_ref, remote_sha = parts
        # ⚠ Recorded BEFORE and INDEPENDENTLY of the quarantine test below, so `reconcile`'s
        #   second check on the same property survives that branch being deleted (R4-2).
        REFS_SEEN.append(local_ref)
        REFS_SEEN.append(remote_ref)
        REF_TUPLES.append((local_ref, local_sha, remote_ref, remote_sha))
        if local_ref.startswith("refs/heads/private/"):
            quarantined.append("BLOCKED: '%s' is a quarantined branch — never push it." % local_ref)
        if "/private/" in remote_ref:
            quarantined.append("BLOCKED: refusing to push to quarantined remote ref '%s'."
                               % remote_ref)
        if local_sha == ZERO:
            continue                                  # branch deletion: nothing to inspect
        if remote_sha == ZERO:                        # new ref on the remote
            base = ""
            for cand in ("origin/main", "main"):
                rc, out = git_out("rev-parse", "--verify", "--quiet", cand)
                if rc == 0 and out.strip():
                    base = out.strip()
                    break
            ranges.append("%s..%s" % (base or EMPTY_TREE, local_sha))
        else:
            ranges.append("%s..%s" % (remote_sha, local_sha))
    if malformed:
        quarantined.append(
            "BLOCKED: %d unparseable ref line(s) on stdin; refusing to infer a push scope from a "
            "format this hook does not understand:\n    %s"
            % (len(malformed), "\n    ".join(malformed[:3])))
    return ranges, quarantined


def pre_push(stream):
    """The pre-push phase. The body is `_pre_push`; this closes any scheduler it started."""
    return _with_scheduler(_pre_push, stream)


def _pre_push(stream):
    ranges, quarantined = parse_refs(stream)
    if quarantined:
        for m in quarantined:
            print(m)
        print("Quarantine guard: push aborted. private/* is intentionally local-only.")
        return 1

    rc0, branch = git_out("rev-parse", "--abbrev-ref", "HEAD")
    report.banner("pre-push pipeline", [
        ("entry", ".git/hooks/pre-push -> hooks.py pre_push"),
        ("branch", branch.strip() or "(unknown)"),
        ("scope", ["%d ref(s) being pushed" % len(ranges)] + ["range %s" % r for r in ranges]
                  or ["nothing to push"]),
        ("basis", "the PUSHED RANGES, not the working tree — see REL-1"),
        ("exempt", "vendored: %s" % (", ".join(sorted(vendored.allowlist())) or "(allowlist empty)")
                   + " + anything under Vendored/"),
        ("not run", "lake build — CI at the PR owns build state (stub-first pushes stubs)"),
    ])
    report.plan(_bind_push_modes(PRE_PUSH_PLAN, PRE_PUSH_EXPECT))

    # ⚠ CONCURRENT LAUNCH, SEQUENTIAL DECISION — see the dependency graph above `JOBS_ENV`. Every leg
    #   below is still consumed at its own call site, in this order; `ZP_HOOK_JOBS=1` creates no
    #   scheduler and is today's path.
    _jobs, _note = hook_jobs()
    if _note:
        print("  concurrency: %s" % _note)
    if _jobs > 1:
        _t, _tnote = leg_timeout()
        _start_push_prefetch(_jobs, _t, _tnote)

    # ⚠⚠ THE SKIP'S OWN CONTROLS RUN FIRST, IN A CHILD, BEFORE ANY RECEIPT IS READ. A child, so no
    #   control's stubbing can leak into this process; first, so a skip is never decided by
    #   machinery whose controls did not pass on this very run.
    print("\n=== Advisory-skip controls ===")
    if py("hooks.py", "selftest") != 0:
        print("\nPush blocked: the advisory-skip controls did not behave as required.")
        print("Each FAIL row above names the control and the mutant it had to catch. Fix the")
        print("cause; never skip the controls to get the skip.")
        return 1

    # ⚠⚠ THE ROUTING CONTROL'S OWN CONTROLS (RELY-CC-5, 2026-10-04). `--selftest` drives the probe's
    #   pool, retry and observable machinery against a mutant per control; until this line it had
    #   no caller, so a defect in the machinery that decides whether a probe verdict may be trusted
    #   was found only when a human ran it. PURE (temp dirs only), so it runs beside the selftest
    #   above, BEFORE the ledger environment is set — the environment its concurrent launch carries.
    print("\n=== Routing control's own controls (probe --selftest) ===")
    if py("probe_routing_behavioural.py", "--selftest") != 0:
        print("\nPush blocked: the routing control's own controls did not behave as required.")
        print("Each FAIL row above names the control and the mutant it had to catch. A probe whose")
        print("pool or retry cannot be trusted cannot certify the routes; fix the probe, never skip it.")
        return 1

    # The decision. Scope is NOT touched by any of this: `ranges` above came from git's stdin and
    # every BLOCK leg below runs whatever the receipt says. Only the derived advisory set can shrink.
    skip = []
    skippable = advisory_skip_set()
    # ⚠ In concurrent mode the key was taken before any leg launched, because guards rewrites files
    #   under tools/verify and the key hashes them; sequentially nothing has run yet at this point.
    key, _why = _SCHED.early_key if _SCHED is not None else push_key(REF_TUPLES)
    if not skippable:
        print("  advisory skip: none — %s; every leg runs."
              % ("the skippable set could not be derived" if skippable is None
                 else "no leg is derivably advisory"))
    else:
        status, rec, detail = consult_receipt(key)
        if status == MATCHED:
            _batch_labels = {label for label, _m, _e in (_batch_rows() or [])}
            skip = sorted(skippable & _batch_labels & set(SKIP_SWITCHES))
            for leg in sorted(skippable - set(skip)):
                print("  advisory skip: %s is derivably advisory but has no skip switch; it RUNS."
                      % leg)
            _refs = "; ".join("%s@%s -> %s@%s" % (lr, ls[:12], rr, rs[:12])
                              for lr, ls, rr, rs in rec.get("refs", []))
            for leg in skip:
                print("SKIPPED %s: matched green run %s at %sZ, refs %s"
                      % (leg, rec.get("gitrobot_run_id") or "no gitRobot provenance",
                         rec.get("ts_utc"), _refs))
        else:
            print("  advisory skip: none — %s: %s; every leg runs."
                  % (status, detail if key is not None else _why))
    # ⚠ An opt-out exported by the CALLER predates this change and is not this skip; say so, so a
    #   "nothing skipped" line is never read over an agent gate that will not run anyway.
    for leg in legs_disabled():
        if leg not in skip:
            var = SKIP_SWITCHES[leg][0]
            print("  note: %s=%s was inherited from the caller, so `%s` will not run — a "
                  "pre-existing opt-out, not a receipt match; this run writes no green receipt."
                  % (var, os.environ.get(var), leg))
    # The skip decision now exists, so `batch prepush` can launch; it is still READ at its own call
    # site at the end, where `_consume` refuses it unless its launch env equals the one passed there.
    if _SCHED is not None:
        _submit_batch_prepush(ranges, skip)

    # ⚠ `gatelock` RETIRED 2026-08-23 — deliberately, not dropped. It froze reviewed paths with the
    # read-only bit while a gate round ran. Three reasons it went: the worktree rule makes the
    # shared-tree concurrent-edit hazard structural rather than policed; its own header recorded the
    # bypass it could not close (git unlinks and recreates, so `checkout`/`reset --hard` silently
    # un-froze a locked path, measured); and the harm it aimed at is already DETECTED downstream,
    # because editing a reviewed file changes its SHA-256 and stales the signal at this very gate.
    # Prevention by an advisory attribute, replaced by detection that cannot be walked past.

    # ⚠ THE CHECKERS BELOW ARE ONLY WORTH THEIR EXIT CODES IF THEY CANNOT BE WALKED AROUND.
    # `guards.py` plants a known violation and then tries EVERY enumerated route to suppressing it.
    # It runs here, before the checkers it protects, because a green checker whose exemption surface
    # has a new hole is a false zero — and this project's own record is that a false zero costs more
    # than a red one. ~10s, once per push.
    # ⚠ SET, NOT `setdefault`, AND THE DIFFERENCE IS A WRONG-TREE RECORD. At push the basis is
    # unambiguous — the tip being pushed, which is HEAD — so a value inherited from the caller's
    # environment could only be wrong, and would attach every verdict on this run to a tree nobody
    # examined. `run.id` comes from the pipeline by V9 and is refused if absent; pre_commit sets
    # both and pre_push set neither, so every push-time record was refused with
    # "run.id is required ... not the caller's imagination" and the whole point of wiring
    # `--record` here was lost at the first checker.
    os.environ.update(_PUSH_LEDGER_ENV)

    print("\n=== Property guards (exemption surface) ===")
    _rc_guards = recorded("guards.py")
    if _rc_guards == 2:
        return 1                      # `recorded` already said why; do not also blame the guard
    if _rc_guards != 0:
        print("\nPush blocked: a guarded property can be walked, or a guard left files mutated.")
        print("Read the FAIL lines above — each names the ROUTE. Fix the route, do not skip the run.")
        return 1

    # ⚠⚠ THE CONTROL FOR THE TWO ROUTES ABOVE, AND UNTIL NOW NOTHING RAN IT. `guards.py` green is
    # not evidence: ROUTE 3 and ROUTE 5 have been defeated FOUR times (whole-file substring →
    # windowed substring → AST shape → AST name), and each repair moved the hole rather than
    # closing it, because every attempt asked "does the consumer's SOURCE look like it honours the
    # flag?" — a static approximation with an escape every time. `probe_routing_behavioural.py`
    # asks the behavioural question instead: it drives the consumer with synthetic rows in its own
    # detached worktree and requires the named ROW to go red. It was written, it works, and it had
    # ZERO automatic callers — so the one artifact that can falsify the guard ran only when a human
    # remembered. Measured 2026-08-24 by `/rely`: 9 of 9, 225s, and it was the only thing in the
    # layer that reacted to a live neuter of `cmd_prepush`.
    #
    # ⚠ IT ASSERTS THE ROW, NOT THE EXIT CODE, and it fails CLOSED — a mutation whose anchor has
    # moved reports `MUTATION DID NOT APPLY` rather than passing, so a refactor that slides the
    # anchor blocks the push instead of silently retiring the control.
    #
    # ⚠ `RLY28-1` IS CLOSED AT THE SHAPE, NOT HERE. The router's producer now records its own count
    # in `batch`'s verdict registry and the push verdict is read from that, so multiplying the
    # returned count by zero at the call site — the neuter that took the gate from exit 1 to exit 0
    # on 2026-08-23 while three FAIL rows sat on screen — is now INERT rather than merely
    # detectable. Two mutations here pin both directions: annihilating the return must stay GREEN,
    # and deleting the producer's record must go RED. What THIS wiring closes is `RLY29-1`: the
    # control had no caller, so nothing ever ran the one artifact that can falsify the guard.
    print("\n=== Routing control (behavioural mutation probe) ===")
    _rc_probe = py("probe_routing_behavioural.py", "--mutations")
    if _rc_probe != 0:
        print("\nPush blocked: the routing control did not behave as required.")
        print("Each row above names the mutation and the ROW that had to go red. A row reading")
        print("MUTATION DID NOT APPLY means the anchor moved — the control is no longer testing")
        print("what it claims, which is a fail-open in the making. Fix the control, never skip it.")
        return 1

    print("\n=== File-reference check ===")
    # ⚠ 3 means "skipped part of my scope", not failure — see check_paths.EXIT_SKIPPED.
    # Locally the pinned Mathlib checkout is present, so this is normally 0; the branch
    # exists so a developer without a built .lake is not blocked by an unrunnable check.
    _rc_paths = recorded("check_paths.py", "--all", "--warn-private")
    if _rc_paths not in (0, 3):
        print("\nPush blocked: a repo-relative reference in TRACKED markdown does not resolve.")
        print("Fix the path, or word the line so the resolver skips it (e.g. 'no longer exists').")
        print("⚠ Writing it into .claude-local/DEFECTS.md does NOT clear this gate: nothing reads")
        print("  that file, and this leg recomputes from the checker on every run.")
        return 1
    print("===========================")

    print("\n=== CLAUDE.md shape contract ===")
    # ⚠ THE COMMENT HERE SAID "CALLED WITHOUT `--record`, DELIBERATELY" WHILE THE LINE BELOW PASSED
    # `--record` AND THE KEY EXISTED IN THE LEDGER. Corrected 2026-08-30, `/rely` RLY27-9: the
    # ledger support was added and the comment describing its absence was left behind. It IS
    # recorded and it IS audited. Kept as a warning rather than deleted, because a comment that
    # outlived its subject is how "wiring it in is the follow-up" reads as still-open work.
    # ⚠ Its manifest declares 3 PENDING legs on every run. A clear result here is evidence
    # about two legs, never about the shape contract as a whole.
    if py("check_claude_md.py", "--record") != 0:
        print("\nPush blocked: CLAUDE.md names a path or a checker that does not exist.")
        print("Fix the pointer. Body: tools/process/claude-md-maintenance.md.")
        return 1
    # ⚠ Keep a class id away from a following noun: `check_figures` reads a number next
    # to a countable word as an undated artifact count, and blocked this commit twice — the
    # second time on the comment written to explain the first. Writing ABOUT a pattern trips
    # it, exactly as `R-TRUNC` records for its own matcher.
    _cb = py("check_briefs.py", "--record")
    # ⚠⚠ FOUR CODES, BECAUSE THERE ARE FOUR FACTS -- AND UNTIL 2026-09-06 TWO OF THEM SHARED A
    # LINE. `record.emit` returns None for a ledger REFUSAL and for an OUTAGE alike, so both
    # arrived here as exit 2 and this printed "unreachable" for both. Measured that day (`B4`):
    # the step was not registered, the ledger ANSWERED naming exactly that rule, and the operator
    # was told the ledger was down. **A decision rendered as an absence** -- the one collapse the
    # exit-2 design exists to prevent, arriving inside the checker built to catch it one layer
    # down. `check_briefs.classify_record_failure` splits them and the remedies differ.
    # ⚠ THE REFUSAL CODE IS 4, NOT 3. `3` is UNDETERMINED in the fleet vocabulary and is also
    # `ci_report.SKIPPED_RC`, where it renders **skipped** -- a non-failure. Read the live values
    # from the server (`vocabulary(name='exit_code')`), never from this comment.
    if _cb == 4:
        print("")
        print("Push blocked: the ledger REACHED and REFUSED check_briefs' record.")
        print("That is a DECISION, not an outage. The rule it named is in the output above --")
        print("an unregistered step, a conflicting revision at this basis, a malformed subject.")
        print("Do not retry it: a validation refusal is terminal and re-sending only masks it.")
        return 1
    if _cb == 2:
        print("")
        print("Push blocked: check_briefs COULD NOT ASK (ledger or record.py unreachable).")
        print("This is a read failure, not a finding about the briefs. Fix the reachability.")
        return 1
    if _cb != 0:
        print("")
        print("Push blocked: a gate brief names a flag, step or path that does not exist.")
        print("A brief instructing a command that does not work is found by a confused agent")
        print("mid-round, which is the most expensive place to find it.")
        return 1
    print("================================")

    # ⚠ WIRED IN 2026-08-15, AFTER BEING BUILT AND LEFT UNCONNECTED FOR A DAY. `check_moved.py` is
    # the control that proves the tools/verify migration is complete — a tombstone only helps a
    # human browsing the folder, while this fails when ANY file still points at a relocated path.
    # It was written, tested, given controls, and run only by hand and in CI: the exact "fires only
    # if someone remembers" shape it exists to eliminate, in the tool built to eliminate it.
    # REL10-4. `install_hooks --check` asks "are the gates actually armed?" — a question its own
    # docstring said had NEVER been asked mechanically. It still had not: nothing invoked it.
    #
    # ⚠ A hook cannot detect its own absence — if it is not installed, none of this runs. What it
    # CAN detect is DRIFT: an installed hook that no longer matches its tracked source, which is a
    # hand-edited or half-updated gate. That is the catchable half, and it is worth catching here
    # because everything downstream assumes the shim it was invoked through is the current one.
    if py("install_hooks.py", "--check") != 0:
        print("\nPush blocked: the installed hooks do not match their tracked sources.")
        print("Run: python tools/verify/install_hooks.py --force")
        return 1

    if recorded("check_moved.py", "--block") != 0:
        print("\nPush blocked: something still points at a relocated path.")
        print("Update the reference, or record the file as a dated record in check_moved.py.")
        print("⚠ Writing it into .claude-local/DEFECTS.md does NOT clear this gate: nothing reads")
        print("  that file, and this leg recomputes from the checker on every run.")
        return 1

    if recorded("check_negatives.py", "--block") != 0:
        print("\nPush blocked: an undated universal negative.")
        print("Write 'none located as of <date>, searched as follows' — a universal negative")
        print("is falsified by any single future commit and nothing mechanical notices.")
        print("⚠ Writing it into .claude-local/DEFECTS.md does NOT clear this gate: nothing reads")
        print("  that file, and this leg recomputes from the checker on every run.")
        return 1

    if recorded("check_figures.py", "--block") != 0:
        print("\nPush blocked: an artifact count recorded in prose with no date.")
        print("Prefer measuring on demand. If it must be written down, date it -")
        print("the papers count went stale by 15 in a day, and nothing noticed.")
        return 1

    # ⚠ THE ACCEPTED-DEFECT BASELINES ARE FROZEN (2026-08-22). The ordinary path already refuses —
    # `--baseline` on any of the six exits 2 with an explanation — so this is the backstop for a
    # HAND EDIT, which no refusal can intercept. It prints the backlog total on every run, clear or
    # not, because a debt figure that surfaces only on failure cannot show progress.
    # ⚠ RUN AND RECORD, DO NOT BLOCK — see the manifest row. `--block` is deliberately NOT passed:
    # the freeze comparison is retired (dead topology), and the run is kept because `claim_review`
    # is emitted here and nowhere else. A downgraded gate must get LOUDER rather than quieter, so
    # the outcome is printed on EVERY push, clear or not, instead of surfacing only on failure.
    _rc_frozen = py("check_frozen.py", "--record")
    if _rc_frozen == 2:
        print("\n⚠ check_frozen ran but its verdict was NOT RECORDED — claim_review is emitted")
        print("  here and nowhere else, so a missing record blocks the push at the ledger.")
        return 1
    print("  check_frozen: WARN-only (retired 2026-08-23, dead topology). Ran and recorded;")
    print("  claim_review emitted. A finding here is a reading list, not a block.")

    if recorded("check_checkers.py", "--block") != 0:
        print("\nPush blocked: a checker cannot fail, or nothing runs it.")
        print("This suite's characteristic defect is a check that could not have failed;")
        print("every instance so far was found by probing, never by reading.")
        return 1

    if recorded("check_invariants.py") != 0:
        return 1

    # The gating checkers. Each exit code captured on its own line — HK-1 was a `$?` read one call
    # too late, which meant check_modal had never blocked a push in its life.
    # ⚠ COUNT THE TUPLE, DO NOT TRUST A WORD. This comment said "The four checkers" and the tuple
    # held four; adding `check_encoding` made the sentence false in the same edit that would have
    # left it. A number written in prose beside the list it describes is a second copy.
    checker_fail = False
    for script in ("check_pov.py", "check_modal.py", "check_classes.py", "check_prose.py",
                   "check_encoding.py"):
        if recorded(script, "--block") != 0:
            checker_fail = True
    if checker_fail:
        return 1

    # Purity + SSOT. Safe at push in a way `lake build` is not: neither touches `sorry`, so neither
    # conflicts with stub-first. Build state stays CI's job at the PR.
    if py("batch.py", "decls", "--block", "--record") != 0:
        print("\nPush blocked: a declaration is missing its #print axioms entry or its ssot.json row.")
        print("Add the purity line, run the SJV sync, then re-push.")
        print("If the baseline is merely stale: python %s/batch.py decls --baseline"
              % os.path.dirname(SELF))
        return 1

    if recorded("check_hashes.py") != 0:
        print("\nPush blocked: build-script hash mismatch vs register.md.")
        print("A script changed without completing the four-step workflow")
        print("(change + version bump + PDF rebuild + hash update).")
        print("⚠ Writing it into .claude-local/DEFECTS.md does NOT clear this gate: nothing reads")
        print("  that file, and this leg recomputes from the checker on every run.")
        return 1

    # ⚠ scan_pdfs lives in `scripts/`, NOT in this bundle. It is a BUILD-side tool (it checks
    # PDF assets and font registrations), and it moved with the build scripts on 2026-08-15
    # while this call kept looking here. Measured by /rely: `py("scan_pdfs.py") -> 2`, and
    # `pre_push` returns that, so EVERY push exited 2 with a bare [Errno 2] at the end of an
    # otherwise-green run. It failed CLOSED, which is why it is ordinary rather than bedrock —
    # but an unexplained exit 2 on a green run is precisely the shape that trains the
    # `--no-verify` reflex, which this project has already had fire twice.
    # ⚠ No hand-written append: `run()` records it, like every other child. The hand-patch that
    #   used to sit here was exactly the R3-1 defect -- delete the call below and the append
    #   claimed the row anyway.
    scan_exit = run(sys.executable, os.path.join(REPO, "scripts", "scan_pdfs.py"))

    # Routing + review signals, computed from the RANGES BEING PUSHED. This is the one call that
    # `batch.py` could not make correctly on its own (REL-1): it had only the working tree, which
    # is empty post-commit, so coverage was vacuous exactly at push time.
    # ⚠ The skip reaches the child ONLY as the leg's own switch, set for this one launch and put back
    #   afterwards; the argv is unchanged, so `reconcile`'s expectation for this row is unchanged.
    _saved_switch = {}
    for leg in skip:
        var, val = SKIP_SWITCHES[leg]
        _saved_switch[var] = os.environ.get(var)
        os.environ[var] = val
    # ⚠ ORDINARY-1: snapshot what the child will SEE, after the hook's own switches are applied, so
    #   the receipt writer keys on the child's environment rather than on `skip`.
    child_off = legs_disabled()
    try:
        rc = py("batch.py", "prepush", "--ranges", ",".join(ranges))
    finally:
        for var, old in _saved_switch.items():
            if old is None:
                os.environ.pop(var, None)
            else:
                os.environ[var] = old
    if rc != 0:
        print("\nPush blocked: the pre-push pipeline reported a failure above.")
        # ⚠⚠ EXACTLY ONE LEG HAS A HUMAN-ACCEPT ROUTE, AND NAMING MORE WOULD BE THE DEFECT THIS
        # LINE WAS JUST FIXED FOR. Being a registered ledger step is NECESSARY but NOT SUFFICIENT:
        # the leg must also CONSULT the ledger before blocking, and only `pdf coupling` does
        # (`batch.pdf_coupling_accepts`, step `pdf_coupling_in_push`). `check_paths`, `check_moved`,
        # `check_negatives` and `check_hashes` are registered and admitted and still recompute from
        # their checker every run, so a signature against them changes nothing at this gate.
        # `purity`, `ssot`, `routing` and `prior_art_attrib` are not registered steps at all.
        print("The ONLY leg here with a human-accept route is `pdf coupling`: an accepted FAIL")
        print("recorded as `pdf_coupling_in_push` over those exact (path, blob) pairs is not a")
        print("block. Every other leg above must be FIXED — a signature does not reach them, and")
        print("⚠ writing any of them into .claude-local/DEFECTS.md clears nothing.")
        # ⚠ This line used to read "This gate is mirrored in CI: a local bypass only defers the
        # block to the PR." That is FALSE and was measured false 2026-08-10: grepping all four
        # workflows for any checker returns nothing — CI runs `lake build`. Telling the operator a
        # backstop exists when it does not is the worst possible failure mode for a deterrent, and
        # the true statement deters harder.
        print("⚠ CI re-runs these checkers on `main` (.github/workflows/verify.yml) but")
        print("  REPORT-ONLY — it publishes findings and does not fail the run. This hook is")
        print("  the last check that STOPS a change; bypassing it ships the change unchecked.")
        return 1

    # ⚠⚠ LAST, AND ONLY ON THE OTHERWISE-GREEN PATH. Every branch above returns 1 before reaching
    # here, so a short run is a REPORTED failure, not a silent one; reconciling early would report
    # rows "missing" that were simply never reached. What this catches is the dangerous case: a
    # green run whose manifest advertised a check that no longer launches.
    if reconcile("push", PRE_PUSH_EXPECT, refs=REFS_SEEN, skipped=skip):
        return 1

    if scan_exit == 0:
        write_green_receipt(key, skip, child_off)
    else:
        _receipt_state(NOT_WRITTEN_RED, "scan_pdfs exited %d, so this run was not green" % scan_exit)
    return scan_exit


# ------------------------------------------------------------------ advisory-skip controls
#
# ⚠⚠ EACH CONTROL IS RUN TWICE: against THIS module, where it must PASS, and against a MUTANT of
# this file's (or batch.py's) source with the one protection it exists for removed, where it must
# FAIL. A control that also passes on its mutant cannot fail, which is a check in name only. A
# mutant whose anchor is missing is reported `MUTATION DID NOT APPLY` and fails the suite — fail
# CLOSED, so a refactor that slides an anchor blocks the push instead of retiring the control
# silently (the `probe_routing_behavioural.py` precedent).
#
# Simulated runs drive `pre_push` in-process with every child process stubbed: `run` records the
# launch and returns a scripted exit code, `tools_digest` / `head_tree` return fixed values, and the
# receipt lives in a temporary directory outside the repository. Nothing here launches a checker,
# touches the real receipt, or writes into the tree.
#
# ⚠ ORDINARY-2 (2026-09-30): because `_simulate` stubs `tools_digest` / `head_tree`, no control could
#   see a mutation INSIDE them — seven mutants survived all sixteen controls. The `_ScratchRepo`
#   controls run the REAL pair against a throwaway repository in the system temp dir (never this
#   checkout), and the receipt-validation branches each have a control of their own.

_CONTROLS_MARK = "# " + "-" * 66 + " advisory-skip controls"
_SHA_A = "a" * 40
_SHA_B = "b" * 40
_REFS = "refs/heads/illustrated %s refs/heads/illustrated %s\n" % (_SHA_A, _SHA_B)
_DIGEST = "d" * 64
_TREE = "e" * 40


def _ts(seconds_ago):
    import datetime
    return (_now() - datetime.timedelta(seconds=seconds_ago)).strftime("%Y-%m-%dT%H:%M:%S")


def _good_receipt(**over):
    rec = {"schema": RECEIPT_SCHEMA, "terminal": "PASS", "skipped": [],
           "refs": [["refs/heads/illustrated", _SHA_A, "refs/heads/illustrated", _SHA_B]],
           "tools_verify_digest": _DIGEST, "head_tree": _TREE, "ts_utc": _ts(600),
           "gitrobot_run_id": "ctl-preflight-1", "gitrobot_op": "preflight"}
    rec.update(over)
    return rec


def _simulate(m, stdin=_REFS, receipt=None, raw=None, env=None, red=(), digest=_DIGEST,
              keep_dir=None):
    """Run `m.pre_push` with every child stubbed. Returns a dict describing what happened."""
    import io as _io
    import json
    import shutil
    import tempfile
    tmp = keep_dir or tempfile.mkdtemp(prefix="zp_hooks_ctl_")
    path = os.path.join(tmp, m.RECEIPT_NAME)
    if receipt is not None:
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(receipt, fh)
    if raw is not None:
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(raw)
    names = ("run", "tools_digest", "head_tree", "git_out", "_RECEIPT_PATH_OVERRIDE")
    saved = {n: getattr(m, n) for n in names}
    switch_vars = sorted({var for var, _val in SKIP_SWITCHES.values()})
    env_keys = (ENV_RUN_ID, ENV_OP, "ZPLEDGER_BASIS", "ZPLEDGER_RUN", JOBS_ENV) + tuple(switch_vars)
    saved_env = {k: os.environ.get(k) for k in env_keys}
    launched, child_env = [], {}

    def fake_run(*cmd):
        inv = m._invocation(cmd)
        rc = 1 if any(tuple(inv[:len(r)]) == tuple(r) for r in red) else 0
        launched.append(inv)
        if tuple(inv[:2]) == ("batch.py", "prepush"):
            # What the CHILD would have seen: the switch values at the moment of launch.
            child_env.update({v: os.environ.get(v) for v in switch_vars})
        m.EXECUTED.append((inv, rc))
        return rc

    m.run = fake_run
    m.tools_digest = digest if callable(digest) else (lambda: digest)
    m.head_tree = lambda: _TREE
    m.git_out = lambda *a: (0, "illustrated\n")
    m._RECEIPT_PATH_OVERRIDE = path
    for k in (ENV_RUN_ID, ENV_OP) + tuple(switch_vars):
        os.environ.pop(k, None)
    # ⚠ SEQUENTIAL, ALWAYS: these controls stub `run`, and only the sequential path goes through
    #   it for every launch. The concurrent path has its own simulator (`_simulate_conc`).
    os.environ[JOBS_ENV] = "1"
    for k, v in (env or {}).items():
        os.environ[k] = v
    del m.EXECUTED[:], m.REFS_SEEN[:], m.REF_TUPLES[:]
    buf, real = _io.StringIO(), sys.stdout
    try:
        sys.stdout = buf
        rc = m.pre_push(_io.StringIO(stdin))
        post_env = {v: os.environ.get(v) for v in switch_vars}
    finally:
        sys.stdout = real
        for n, v in saved.items():
            setattr(m, n, v)
        for k, v in saved_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        del m.EXECUTED[:], m.REFS_SEEN[:], m.REF_TUPLES[:]
    after = None
    if os.path.exists(path):
        try:
            with open(path, encoding="utf-8") as fh:
                after = json.load(fh)
        except (OSError, ValueError):
            after = "unreadable"
    if keep_dir is None:
        shutil.rmtree(tmp, ignore_errors=True)
    skipped = sorted(leg for leg, (var, val) in SKIP_SWITCHES.items()
                     if child_env.get(var) == val)
    # A switch still set in THIS process after `pre_push` returned would leak into anything it
    # launches later; every switch was cleared before the run, so any value here is a leak.
    leaked = sorted(v for v in switch_vars if post_env.get(v) is not None)
    return {"rc": rc, "out": buf.getvalue(), "skipped": skipped, "after": after,
            "launched": launched, "leaked": leaked}


_POV_RED = (("check_pov.py",),)
_BATCH_RED = (("batch.py", "prepush"),)


def _ctl_positive(m):
    r = _simulate(m, receipt=_good_receipt())
    ok = (r["rc"] == 0 and r["skipped"] == ["agent gate"] and not r["leaked"]
          and "SKIPPED agent gate: matched green run ctl-preflight-1" in r["out"])
    return ok, "rc=%s skipped=%s switch leaked past the launch=%s" % (
        r["rc"], r["skipped"], r["leaked"] or "no")


def _ctl_switch_restored(m):
    r = _simulate(m, receipt=_good_receipt())
    ok = r["skipped"] == ["agent gate"] and not r["leaked"]
    return ok, "skipped=%s; switch still set after the batch launch: %s" % (
        r["skipped"], r["leaked"] or "none")


def _ctl_a_block_red(m):
    r1 = _simulate(m, receipt=_good_receipt(), red=_POV_RED)
    r2 = _simulate(m, receipt=_good_receipt(), red=_BATCH_RED)
    matched = "SKIPPED agent gate" in r1["out"] and "SKIPPED agent gate" in r2["out"]
    ok = matched and r1["rc"] != 0 and r2["rc"] != 0
    return ok, "receipt matched=%s; check_pov red -> rc=%s; batch prepush red -> rc=%s" % (
        matched, r1["rc"], r2["rc"])


def _ctl_b_sha_changed(m):
    stdin = _REFS.replace(_SHA_A, "c" * 40)
    if stdin == _REFS:
        return False, "input mutation did not apply"
    r = _simulate(m, stdin=stdin, receipt=_good_receipt())
    return r["skipped"] == [] and r["rc"] == 0, "one local sha changed -> skipped=%s" % r["skipped"]


def _ctl_c_env_no_receipt(m):
    r = _simulate(m, env={ENV_RUN_ID: "forged-run", ENV_OP: "push"})
    ok = r["skipped"] == [] and "NO_RECEIPT" in r["out"]
    return ok, "GITROBOT_RUN_ID set by hand, no receipt -> skipped=%s" % r["skipped"]


def _ctl_d_skipping_receipt(m):
    r1 = _simulate(m, receipt=_good_receipt(skipped=["agent gate"]))
    # And the writer half: a run that skipped must not leave a fresh, usable receipt behind.
    r2 = _simulate(m, receipt=_good_receipt())
    after = r2["after"] if isinstance(r2["after"], dict) else {}
    chained = bool(after) and not after.get("consumed_at")
    ok = r1["skipped"] == [] and r2["skipped"] == ["agent gate"] and not chained
    return ok, ("receipt marked skipped -> skipped=%s; after a skipping run the receipt is %s"
                % (r1["skipped"], "FRESH (chains!)" if chained else "consumed"))


def _ctl_e_digest(m):
    r = _simulate(m, receipt=_good_receipt(), digest="f" * 64)
    return r["skipped"] == [], "receipt digest != this run's digest -> skipped=%s" % r["skipped"]


def _ctl_h_inherited_optout(m):
    """ORDINARY-1: a caller-exported opt-out must not mint a receipt the next run skips on."""
    import shutil
    import tempfile
    seen = []
    for val in ("0", "off"):                     # agent_gate runs only on "1": any other value is off
        d = tempfile.mkdtemp(prefix="zp_hooks_ctl_")
        try:
            r1 = _simulate(m, env={"ZP_AGENT_GATE": val}, keep_dir=d)
            r2 = _simulate(m, keep_dir=d)
        finally:
            shutil.rmtree(d, ignore_errors=True)
        state = NOT_WRITTEN_OPTED_OUT in r1["out"]
        seen.append((val, r1["rc"], r1["after"] is None, state, r2["skipped"]))
    ok = all(rc == 0 and none and state and nxt == [] for _v, rc, none, state, nxt in seen)
    return ok, "; ".join("ZP_AGENT_GATE=%s inherited -> rc=%s, receipt %s, %s printed=%s; next run "
                         "skipped=%s" % (v, rc, "absent" if none else "WRITTEN", NOT_WRITTEN_OPTED_OUT,
                                         st, nxt) for v, rc, none, st, nxt in seen)


def _ctl_i_future(m):
    r = _simulate(m, receipt=_good_receipt(ts_utc=_ts(-3600)))
    ok = r["skipped"] == [] and "none — %s:" % STALE in r["out"]
    return ok, "receipt dated 1h in the future -> skipped=%s, STALE reported=%s" % (
        r["skipped"], "none — %s:" % STALE in r["out"])


def _ctl_j_schema(m):
    wrong = _good_receipt(schema="zp.prepush_green.v0")
    absent = _good_receipt()
    del absent["schema"]
    rs = [_simulate(m, receipt=wrong), _simulate(m, receipt=absent)]
    ok = all(r["skipped"] == [] and "none — %s:" % UNREADABLE in r["out"] for r in rs)
    return ok, "wrong schema -> skipped=%s; no schema -> skipped=%s" % (
        rs[0]["skipped"], rs[1]["skipped"])


def _ctl_k_terminal(m):
    failed = _good_receipt(terminal="FAIL")
    absent = _good_receipt()
    del absent["terminal"]
    rs = [_simulate(m, receipt=failed), _simulate(m, receipt=absent)]
    ok = all(r["skipped"] == [] and "none — %s:" % NOT_TERMINAL in r["out"] for r in rs)
    return ok, "terminal=FAIL -> skipped=%s; no terminal -> skipped=%s" % (
        rs[0]["skipped"], rs[1]["skipped"])


def _ctl_l_end_key(m):
    calls = []

    def moving():
        calls.append(1)
        return _DIGEST if len(calls) == 1 else "f" * 64
    r = _simulate(m, digest=moving)
    ok = r["rc"] == 0 and r["after"] is None and NOT_WRITTEN_KEY_MOVED in r["out"]
    return ok, "tools/verify moved between key and write (%d digest call(s)) -> receipt %s" % (
        len(calls), "absent" if r["after"] is None else "WRITTEN")


# Repository-locating variables git may export into a running hook; any of them would point the
# scratch repository's git calls back at the REAL one, so they are removed for its lifetime.
_GIT_LOCATION_VARS = ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
                      "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
                      "GIT_NAMESPACE", "GIT_PREFIX")


class _ScratchRepo(object):
    """A throwaway repository in the system temp dir, with `m.REPO` pointed at it, so a control runs
    the REAL `tools_digest` / `head_tree`. Plumbing only — init, add, rm --cached, write-tree,
    hash-object, and HEAD written as a file — so no hook, signing or identity setting fires."""

    def __init__(self, m):
        self.m = m

    def _git(self, *args, **kw):
        # ⚠ BYTES, not text: text-mode stdin on Windows writes CRLF, and a commit body with a `\r`
        #   in its tree line is refused by hash-object's fsck.
        data = kw.get("stdin")
        r = subprocess.run(["git"] + list(args), cwd=self.dir, capture_output=True,
                           input=data.encode("utf-8") if data is not None else None)
        if r.returncode != 0:
            raise RuntimeError("scratch repo: %s exited %d: %s" % (
                args[0], r.returncode, r.stderr.decode("utf-8", "replace").strip()))
        return r.stdout.decode("utf-8", "replace").strip()

    def __enter__(self):
        import tempfile
        self.saved_env = {k: os.environ.pop(k) for k in _GIT_LOCATION_VARS if k in os.environ}
        self.saved_repo = self.m.REPO
        self.dir = tempfile.mkdtemp(prefix="zp_hooks_ctl_repo_")
        self.m.REPO = self.dir
        self._git("init", "-q")
        return self

    def __exit__(self, *exc):
        import shutil
        self.m.REPO = self.saved_repo
        os.environ.update(self.saved_env)
        shutil.rmtree(self.dir, ignore_errors=True)
        return False

    def put(self, rel, data):
        p = os.path.join(self.dir, *rel.split("/"))
        if not os.path.isdir(os.path.dirname(p)):
            os.makedirs(os.path.dirname(p))
        with open(p, "wb") as fh:
            fh.write(data)

    def remove(self, rel):
        os.remove(os.path.join(self.dir, *rel.split("/")))

    def track(self, *rels):
        self._git("add", "--", *rels)

    def untrack(self, rel):
        self._git("rm", "-q", "--cached", "--", rel)

    def commit(self):
        """Commit the index as a detached HEAD; return its tree id, computed independently."""
        tree = self._git("write-tree")
        body = ("tree %s\nauthor ctl <ctl@invalid> 0 +0000\ncommitter ctl <ctl@invalid> 0 +0000\n"
                "\nctl\n" % tree)
        sha = self._git("hash-object", "-t", "commit", "-w", "--stdin", stdin=body)
        with open(os.path.join(self.dir, ".git", "HEAD"), "w", encoding="ascii", newline="\n") as fh:
            fh.write(sha + "\n")
        return tree


def _ctl_m_digest_content(m):
    with _ScratchRepo(m) as s:
        s.put("tools/verify/a.py", b"print(1)\n")
        s.put("tools/verify/b.py", b"x = 1\n")
        s.track("tools/verify")
        d1 = m.tools_digest()
        s.put("tools/verify/a.py", b"print(2)\n")         # same tracked set, one byte of content
        d2 = m.tools_digest()
    ok = bool(d1) and bool(d2) and d1 != d2
    return ok, "REAL tools_digest, scratch repo: a content edit moved the digest=%s" % (
        bool(d1) and d1 != d2)


def _ctl_n_digest_absent(m):
    with _ScratchRepo(m) as s:
        s.put("tools/verify/a.py", b"print(1)\n")
        s.put("tools/verify/b.py", b"x = 1\n")
        s.track("tools/verify")
        full = m.tools_digest()
        s.remove("tools/verify/b.py")
        absent = m.tools_digest()                         # tracked, missing from disk
        s.untrack("tools/verify/b.py")
        untracked = m.tools_digest()                      # no longer tracked at all
    ok = bool(full and absent and untracked) and absent != full and absent != untracked
    return ok, ("REAL tools_digest: deleted-but-tracked differs from intact=%s and from "
                "never-tracked=%s" % (absent != full, absent != untracked))


def _ctl_o_head_tree(m):
    with _ScratchRepo(m) as s:
        s.put("tools/verify/a.py", b"print(1)\n")
        s.track("tools/verify")
        t1 = s.commit()
        h1 = m.head_tree()
        s.put("tools/verify/a.py", b"print(2)\n")
        s.track("tools/verify")
        t2 = s.commit()
        h2 = m.head_tree()
    ok = t1 != t2 and h1 == t1 and h2 == t2
    return ok, "REAL head_tree, scratch repo: tracks commit 1=%s, tracks commit 2=%s" % (
        h1 == t1, h2 == t2)


def _ctl_f_single_use(m):
    import tempfile
    import shutil
    d = tempfile.mkdtemp(prefix="zp_hooks_ctl_")
    try:
        r1 = _simulate(m, receipt=_good_receipt(), keep_dir=d)
        r2 = _simulate(m, keep_dir=d)
    finally:
        shutil.rmtree(d, ignore_errors=True)
    ok = r1["skipped"] == ["agent gate"] and r2["skipped"] == []
    return ok, "first use skipped=%s; second use skipped=%s" % (r1["skipped"], r2["skipped"])


def _ctl_g_stale(m):
    r = _simulate(m, receipt=_good_receipt(ts_utc=_ts(25 * 3600)))
    return r["skipped"] == [], "receipt 25h old -> skipped=%s" % r["skipped"]


def _ctl_unreadable(m):
    r = _simulate(m, raw="{ not json")
    seen = [s for s in (UNREADABLE, NO_RECEIPT, MATCHED) if "none — %s:" % s in r["out"]]
    ok = r["skipped"] == [] and seen == [UNREADABLE]
    return ok, "garbage receipt -> skipped=%s, status reported %s (must be UNREADABLE, never " \
               "NO_RECEIPT)" % (r["skipped"], seen or "none")


def _ctl_writes(m):
    r = _simulate(m, env={ENV_RUN_ID: "ctl-run-9", ENV_OP: "preflight"})
    a = r["after"] if isinstance(r["after"], dict) else {}
    ok = (r["rc"] == 0 and a.get("terminal") == "PASS" and a.get("skipped") == []
          and a.get("gitrobot_run_id") == "ctl-run-9" and not a.get("consumed_at"))
    return ok, "green unskipped run -> receipt terminal=%s run_id=%s" % (
        a.get("terminal"), a.get("gitrobot_run_id"))


def _ctl_reconcile(m):
    import io as _io
    buf, real = _io.StringIO(), sys.stdout
    try:
        sys.stdout = buf
        rc = m.reconcile("push", [("guards", None, None)], skipped=["guards"])
    finally:
        sys.stdout = real
    return rc == 1, "reconcile with a BLOCK row in the skipped list -> rc=%s" % rc


def _ctl_invariant(m):
    s = m.advisory_skip_set()
    v = m.skip_set_violations(s) if s is not None else ["the set could not be derived"]
    return not v, "derived set %s; violations: %s" % (sorted(s or ()), "; ".join(v) or "none")


# ⚠ INDEPENDENTLY WRITTEN, NOT DERIVED: a control that re-derives its expectation from the producer
# agrees by construction (`guards.py`'s own finding). If a legitimate change grows the set, this row
# goes red and the literal is updated deliberately, in the same commit.
_EXPECTED_SKIPPABLE = {"agent gate"}


def _ctl_literal(m):
    s = m.advisory_skip_set()
    return s == _EXPECTED_SKIPPABLE, "derived %s, expected %s" % (
        sorted(s or ()), sorted(_EXPECTED_SKIPPABLE))


# ------------------------------------------------------------------ pass-cache controls
#
# `R-NOCONV`: the guard asserting what still BLOCKS lands with the skip. Each control drives the REAL
# `pre_commit` with every child stubbed and the attest transport STUBBED — never the live gitRobot,
# whose `attest()` consumes and audits. Only an exact yes about the hook's own tree may skip; every
# other answer must launch all eleven legs. The `_StubGitRobot` rows run the REAL `_attest_call`
# against a throwaway loopback server, so a mutation inside the transport is visible too.

_RUN = "ctl-run-attest"


_ECHO = object()      # echo exactly what the hook asked
_ABSENT = object()    # leave the key out of the answer altogether
_CTL_ID = "ctl"       # the request id the stubbed transport reports having sent
_FORGE_VAR = "GITROBOT_URL"   # the env override `/rely` forged with; it must reach nothing now


def _attest_answer(attested=True, tree=_ECHO, ok=True, why=None, is_error=False, structured=True,
                   run_id=_ECHO, rpc_id=_ECHO, error=None):
    """A JSON-RPC response shaped like gitRobot's AttestResult. `_ECHO` (the default) echoes what was
    asked, `_ABSENT` omits the key, any other value is sent as given — so a control can build a yes
    with NO tree or run id echo, which the earlier `tree=None`-means-echo helper could not."""
    def answer(asked_run, asked_tree, call_id=_CTL_ID):
        import json
        sc = {"ok": ok, "op": "attest", "attested": attested, "why": why}
        for key, val, asked in (("run_id", run_id, asked_run), ("tree", tree, asked_tree)):
            if val is _ECHO:
                sc[key] = asked
            elif val is not _ABSENT:
                sc[key] = val
        result = {"content": [{"type": "text", "text": json.dumps(sc)}]}
        if is_error is not _ABSENT:
            result["isError"] = is_error
        if structured:
            result["structuredContent"] = sc
        resp = {"jsonrpc": "2.0", "id": call_id if rpc_id is _ECHO else rpc_id, "result": result}
        if error is not None:
            resp["error"] = error
        return resp
    return answer


def _dead_url():
    """A loopback URL nothing listens on."""
    import socket
    sock = socket.socket()
    sock.bind(("127.0.0.1", 0))
    port = sock.getsockname()[1]
    sock.close()
    return "http://127.0.0.1:%d/mcp" % port


def _simulate_commit(m, env=None, answer=None, raises=None, tree=_TREE, real=False, url=None):
    """Run `m.pre_commit` with every child stubbed. `answer(run_id, tree)` or `raises` stands in for
    the transport unless `real`; then `m._attest_call` runs against `url`, set through the
    in-process seam `m._ATTEST_URL_SEAM`. A real run with no `url` is refused: it would reach the
    live gitRobot, whose `attest()` consumes and audits."""
    import io as _io
    if real and not url:
        raise ValueError("a real-transport control must name its loopback url")
    names = ("run", "index_tree", "_attest_call", "_ATTEST_URL_SEAM")
    saved = {n: getattr(m, n) for n in names}
    env_keys = (ENV_RUN_ID, ENV_OP, _FORGE_VAR, "ZPLEDGER_BASIS", "ZPLEDGER_RUN", JOBS_ENV)
    saved_env = {k: os.environ.get(k) for k in env_keys}
    launched, calls = [], []

    def fake_run(*cmd):
        inv = m._invocation(cmd)
        launched.append(inv)
        m.EXECUTED.append((inv, 0))
        return 0

    def fake_call(run_id, asked_tree):
        calls.append((run_id, asked_tree))
        if raises is not None:
            raise raises
        return _CTL_ID, answer(run_id, asked_tree)

    m.run = fake_run
    m.index_tree = lambda: tree
    if real:
        m._ATTEST_URL_SEAM = url
    else:
        m._attest_call = fake_call
    for k in (ENV_RUN_ID, ENV_OP, _FORGE_VAR):
        os.environ.pop(k, None)
    os.environ[JOBS_ENV] = "1"          # sequential, always: see `_simulate`
    for k, v in (env or {}).items():
        os.environ[k] = v
    del m.EXECUTED[:]
    buf, real_out = _io.StringIO(), sys.stdout
    try:
        sys.stdout = buf
        rc = m.pre_commit()
    finally:
        sys.stdout = real_out
        for n, v in saved.items():
            setattr(m, n, v)
        for k, v in saved_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        del m.EXECUTED[:]
    return {"rc": rc, "out": buf.getvalue(), "launched": launched, "calls": calls}


def _full(m, r, status):
    """True when the run launched every leg, exited 0 and reported exactly `status`."""
    return (r["rc"] == 0 and len(r["launched"]) == len(m.PRE_COMMIT_CHECKS)
            and "pass-cache: none — %s:" % status in r["out"] and "SKIPPED" not in r["out"])


def _say(r, status):
    return "rc=%s, %d of %d leg(s) launched, %s reported=%s, attest calls=%d" % (
        r["rc"], len(r["launched"]), len(PRE_COMMIT_CHECKS), status,
        "none — %s:" % status in r["out"], len(r["calls"]))


def _ctl_attest_yes(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN, ENV_OP: "commit"}, answer=_attest_answer())
    ok = (r["rc"] == 0 and r["launched"] == [] and r["calls"] == [(_RUN, _TREE)]
          and "SKIPPED pre-commit: gitRobot gate %s passed for tree %s" % (_RUN, _TREE)
          in r["out"] and "BLOCK rows launched: 0 of 11" in r["out"])
    return ok, "stubbed attested:true for this tree -> rc=%s, %d leg(s) launched, calls=%s" % (
        r["rc"], len(r["launched"]), r["calls"])


def _ctl_attest_denied(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN},
                         answer=_attest_answer(attested=False, why="ctl-why: tree differs"))
    ok = _full(m, r, ATTEST_DENIED) and "ctl-why: tree differs" in r["out"]
    return ok, "attested:false -> " + _say(r, ATTEST_DENIED) + ", why printed=%s" % (
        "ctl-why" in r["out"])


def _ctl_attest_unreachable(m):
    import urllib.error
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN},
                         raises=urllib.error.URLError(ConnectionRefusedError(10061, "refused")))
    return _full(m, r, ATTEST_UNREACHABLE), "connection refused -> " + _say(r, ATTEST_UNREACHABLE)


def _ctl_attest_timeout(m):
    import socket
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, raises=socket.timeout("timed out"))
    distinct = len(set(m.ATTEST_STATUSES)) == len(m.ATTEST_STATUSES)
    return (_full(m, r, ATTEST_TIMEOUT) and distinct,
            "socket timeout -> " + _say(r, ATTEST_TIMEOUT) + ", every status distinct=%s" % distinct)


def _ctl_attest_no_env(m):
    r = _simulate_commit(m, answer=_attest_answer())
    ok = _full(m, r, ATTEST_NO_RUN_ID) and r["calls"] == []
    return ok, "no GITROBOT_RUN_ID (stub would say yes) -> " + _say(r, ATTEST_NO_RUN_ID)


def _ctl_attest_no_tree(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(), tree=None)
    ok = _full(m, r, ATTEST_NO_TREE) and r["calls"] == []
    return ok, "write-tree failed (stub would say yes) -> " + _say(r, ATTEST_NO_TREE)


def _ctl_attest_bad_json(m):
    import json
    try:
        json.loads("{ not json")
        return False, "the malformed-JSON input parsed"
    except ValueError as e:
        err = e
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, raises=err)
    return _full(m, r, ATTEST_MALFORMED), "unparsable body -> " + _say(r, ATTEST_MALFORMED)


def _ctl_attest_not_bool(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(attested="true"))
    return _full(m, r, ATTEST_MALFORMED), 'attested:"true" (a string) -> ' + _say(r, ATTEST_MALFORMED)


def _ctl_attest_no_structured(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(structured=False))
    return (_full(m, r, ATTEST_MALFORMED),
            "yes in the text content only, no structuredContent -> " + _say(r, ATTEST_MALFORMED))


def _ctl_attest_is_error(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(is_error=True))
    return _full(m, r, ATTEST_REFUSED), "isError:true (body says yes) -> " + _say(r, ATTEST_REFUSED)


def _ctl_attest_not_ok(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(ok=False))
    return _full(m, r, ATTEST_NOT_OK), "ok:false (attested says yes) -> " + _say(r, ATTEST_NOT_OK)


def _ctl_attest_tree_echo(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(tree="f" * 40))
    return (_full(m, r, ATTEST_TREE_ECHO) and r["calls"] == [(_RUN, _TREE)],
            "yes about a different tree -> " + _say(r, ATTEST_TREE_ECHO))


def _ctl_attest_error(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, raises=RuntimeError("ctl boom"))
    return _full(m, r, ATTEST_ERROR), "an unclassified exception -> " + _say(r, ATTEST_ERROR)


class _ExplodingResponse(dict):
    """A response the judge cannot read: it raises the moment its keys are inspected."""

    def __contains__(self, key):
        raise RuntimeError("ctl: unreadable response")

    def get(self, *a):
        raise RuntimeError("ctl: unreadable response")

    def __getitem__(self, key):
        raise RuntimeError("ctl: unreadable response")


def _ctl_attest_judge_raises(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=lambda run_id, t: _ExplodingResponse())
    return _full(m, r, ATTEST_ERROR), "the judge raised -> " + _say(r, ATTEST_ERROR)


# ⚠ The eight below close the 2026-10-03 `/rely` round (BLOCKING-1, ORDINARY-1, ORDINARY-2): the
#   env-chosen answerer, and the protections that had no control firing when they were removed.

def _ctl_attest_no_tree_echo(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(tree=_ABSENT))
    return (_full(m, r, ATTEST_TREE_ECHO),
            "a yes with NO tree echo -> " + _say(r, ATTEST_TREE_ECHO))


def _ctl_attest_ok_truthy(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(ok="yes"))
    return _full(m, r, ATTEST_NOT_OK), 'ok:"yes" (truthy, not the boolean) -> ' + _say(r, ATTEST_NOT_OK)


def _ctl_attest_is_error_truthy(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(is_error="false"))
    return (_full(m, r, ATTEST_REFUSED),
            'isError:"false" (a truthy string) -> ' + _say(r, ATTEST_REFUSED))


def _ctl_attest_timeout_constant(m):
    """Tests the PRODUCTION constant, which the real-transport timeout control overrides."""
    t = m.ATTEST_TIMEOUT_S
    ok = (isinstance(t, (int, float)) and not isinstance(t, bool) and 0 < t <= 10
          and m._ATTEST_TIMEOUT_OVERRIDE is None)
    return ok, "ATTEST_TIMEOUT_S=%r (bound 10s), override at rest=%r" % (t, m._ATTEST_TIMEOUT_OVERRIDE)


def _ctl_attest_run_echo(m):
    r1 = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(run_id="someone-else"))
    r2 = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(run_id=_ABSENT))
    return (_full(m, r1, ATTEST_RUN_ECHO) and _full(m, r2, ATTEST_RUN_ECHO),
            "a yes for another run -> " + _say(r1, ATTEST_RUN_ECHO)
            + "; a yes with no run echo -> " + _say(r2, ATTEST_RUN_ECHO))


def _ctl_attest_error_and_result(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN},
                         answer=_attest_answer(error={"code": -32000, "message": "ctl"}))
    return (_full(m, r, ATTEST_REFUSED),
            "error AND a yes result -> " + _say(r, ATTEST_REFUSED))


def _ctl_attest_rpc_id(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(rpc_id="replayed"))
    return (_full(m, r, ATTEST_RPC_ID),
            "a yes answering some other request id -> " + _say(r, ATTEST_RPC_ID))


# ⚠ The eight below close the 2026-10-04 `/rely` round 2 (ORDINARY-1, now a CLASS: a fail-closed
#   protection in the attest transport/judge with no control that fails when it is removed; and
#   ORDINARY-2, `isError` falsy-but-not-False). `_sweep_attest` below is the class's detector.

def _ctl_attest_http_error(m):
    import io as _io
    import urllib.error
    e = urllib.error.HTTPError("http://ctl/mcp", 500, "ctl", {}, _io.BytesIO(b""))
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, raises=e)
    return _full(m, r, ATTEST_REFUSED), "HTTP 500 from the transport -> " + _say(r, ATTEST_REFUSED)


def _ctl_attest_urlerror_timeout(m):
    import socket
    import urllib.error
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN},
                         raises=urllib.error.URLError(socket.timeout("timed out")))
    return (_full(m, r, ATTEST_TIMEOUT),
            "URLError wrapping a timeout -> " + _say(r, ATTEST_TIMEOUT))


def _ctl_attest_bare_oserror(m):
    r1 = _simulate_commit(m, env={ENV_RUN_ID: _RUN},
                          raises=ConnectionResetError(10054, "ctl: reset"))
    r2 = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, raises=OSError(5, "ctl: io"))
    return (_full(m, r1, ATTEST_UNREACHABLE) and _full(m, r2, ATTEST_UNREACHABLE),
            "bare ConnectionResetError -> " + _say(r1, ATTEST_UNREACHABLE)
            + "; bare OSError -> " + _say(r2, ATTEST_UNREACHABLE))


def _ctl_attest_non_dict(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=lambda run_id, t: [1])
    return _full(m, r, ATTEST_MALFORMED), "a JSON array, not an object -> " + _say(r, ATTEST_MALFORMED)


def _ctl_attest_no_result(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN},
                         answer=lambda run_id, t: {"jsonrpc": "2.0", "id": _CTL_ID})
    return _full(m, r, ATTEST_MALFORMED), "no `result`, no `error` -> " + _say(r, ATTEST_MALFORMED)


def _ctl_attest_result_not_object(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN},
                         answer=lambda run_id, t: {"jsonrpc": "2.0", "id": _CTL_ID, "result": []})
    return _full(m, r, ATTEST_MALFORMED), "`result` is a list -> " + _say(r, ATTEST_MALFORMED)


def _ctl_attest_is_error_falsy(m):
    """Only an ABSENT `isError` or the boolean False may pass; None, 0, "", [] and {} are refused."""
    outs = []
    for v in (None, 0, "", [], {}):
        r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(is_error=v))
        outs.append((v, _full(m, r, ATTEST_REFUSED)))
    r_absent = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, answer=_attest_answer(is_error=_ABSENT))
    absent_skips = r_absent["launched"] == [] and "SKIPPED pre-commit" in r_absent["out"]
    ok = all(o for _v, o in outs) and absent_skips
    return ok, "isError %s refused; isError absent still skips=%s" % (
        ", ".join("%r:%s" % (v, "yes" if o else "NO") for v, o in outs), absent_skips)


_PROXY_VARS = ("HTTP_PROXY", "http_proxy", "HTTPS_PROXY", "https_proxy", "ALL_PROXY", "all_proxy",
               "NO_PROXY", "no_proxy")


def _ctl_attest_proxy_env(m):
    """`/rely` round 2's forge by a second variable: HTTP_PROXY / ALL_PROXY name a loopback stub that
    says yes. The REAL transport, its seam aimed at a dead port, must not route through the proxy:
    every leg runs, UNREACHABLE, and the stub sees nothing. NO_PROXY is cleared so the bypass list
    cannot mask a removed `ProxyHandler({})`."""
    saved = {k: os.environ.get(k) for k in _PROXY_VARS}
    try:
        with _StubGitRobot() as s:
            for k in _PROXY_VARS:
                os.environ.pop(k, None)
            for k in ("HTTP_PROXY", "http_proxy", "ALL_PROXY", "all_proxy"):
                os.environ[k] = s.url.rsplit("/mcp", 1)[0]
            r = _simulate_commit(m, env={ENV_RUN_ID: "forged-by-anyone"}, real=True, url=_dead_url())
            calls = list(s.calls)
    finally:
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
    return (_full(m, r, ATTEST_UNREACHABLE) and calls == [],
            "HTTP_PROXY/ALL_PROXY=<yes stub> -> " + _say(r, ATTEST_UNREACHABLE) + ", stub saw %s" % calls)


def _ctl_attest_index_tree(m):
    with _ScratchRepo(m) as s:
        s.put("tools/verify/a.py", b"print(1)\n")
        s.track("tools/verify")
        t1 = m.index_tree()
        s.put("tools/verify/a.py", b"print(2)\n")
        s.track("tools/verify")
        t2 = m.index_tree()
        want = s._git("write-tree")
    ok = bool(t1) and t1 != t2 and t2 == want
    return ok, "REAL index_tree, scratch repo: follows the staged index=%s" % (
        bool(t1) and t1 != t2 and t2 == want)


class _StubGitRobot(object):
    """A throwaway loopback streamable-HTTP MCP server answering `attest` yes for whatever it is
    asked, SSE-framed, refusing any request after `initialize` that lacks its session id. Never the
    real gitRobot: the real `attest()` consumes and audits."""

    def __init__(self, delay=0.0):
        self.delay = delay
        self.calls = []

    def __enter__(self):
        import http.server
        import json
        import threading
        import time
        outer = self

        class Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self, *a):
                pass

            def _send(self, code, obj, sid=None):
                try:
                    body = b"" if obj is None else (
                        "event: message\ndata: %s\n\n" % json.dumps(obj)).encode("utf-8")
                    self.send_response(code)
                    self.send_header("Content-Type", "text/event-stream")
                    if sid:
                        self.send_header("Mcp-Session-Id", sid)
                    self.send_header("Content-Length", str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                except OSError:
                    pass

            def do_POST(self):
                n = int(self.headers.get("Content-Length") or 0)
                msg = json.loads(self.rfile.read(n).decode("utf-8"))
                method = msg.get("method")
                if method == "initialize":
                    return self._send(200, {"jsonrpc": "2.0", "id": msg.get("id"), "result": {
                        "protocolVersion": "2025-06-18", "capabilities": {},
                        "serverInfo": {"name": "ctl-stub", "version": "0"}}}, sid="ctl-session")
                if self.headers.get("Mcp-Session-Id") != "ctl-session":
                    return self._send(400, None)
                if method == "notifications/initialized":
                    return self._send(202, None)
                args = (msg.get("params") or {}).get("arguments") or {}
                outer.calls.append((args.get("run_id"), args.get("tree")))
                if outer.delay:
                    time.sleep(outer.delay)
                return self._send(200, _attest_answer()(args.get("run_id"), args.get("tree"),
                                                        msg.get("id")))

        self.server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = True
        self.server.block_on_close = False
        self.server.handle_error = lambda *a: None
        self.url = "http://127.0.0.1:%d/mcp" % self.server.server_address[1]
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        return self

    def __exit__(self, *exc):
        self.server.shutdown()
        self.server.server_close()
        return False


def _ctl_attest_real_yes(m):
    with _StubGitRobot() as s:
        r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, real=True, url=s.url)
    ok = r["rc"] == 0 and r["launched"] == [] and s.calls == [(_RUN, _TREE)]
    return ok, "REAL transport, SSE-framed yes from a loopback stub -> rc=%s, %d leg(s) launched, " \
               "stub saw %s" % (r["rc"], len(r["launched"]), s.calls)


def _ctl_attest_real_timeout(m):
    saved = m._ATTEST_TIMEOUT_OVERRIDE
    m._ATTEST_TIMEOUT_OVERRIDE = 0.3
    try:
        with _StubGitRobot(delay=1.5) as s:
            r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, real=True, url=s.url)
    finally:
        m._ATTEST_TIMEOUT_OVERRIDE = saved
    return (_full(m, r, ATTEST_TIMEOUT),
            "REAL transport, stub answers yes after 1.5s, timeout 0.3s -> " + _say(r, ATTEST_TIMEOUT))


def _ctl_attest_real_refused(m):
    r = _simulate_commit(m, env={ENV_RUN_ID: _RUN}, real=True, url=_dead_url())
    return (_full(m, r, ATTEST_UNREACHABLE),
            "REAL transport, closed loopback port -> " + _say(r, ATTEST_UNREACHABLE))


def _ctl_attest_env_forge(m):
    """The `/rely` forge: GITROBOT_URL in the environment names a loopback stub that says yes. The
    answerer must stay the constant. Two legs, neither touching the live gitRobot: (1) with the
    seam at rest `_attest_url()` returns the literal production address despite the variable;
    (2) the whole REAL hook, its seam aimed at a dead port, runs every leg and the stub named in
    the environment is never called."""
    with _StubGitRobot() as s:
        saved = os.environ.get(_FORGE_VAR)
        os.environ[_FORGE_VAR] = s.url
        try:
            seam_at_rest = m._ATTEST_URL_SEAM
            chosen = m._attest_url()
        finally:
            if saved is None:
                os.environ.pop(_FORGE_VAR, None)
            else:
                os.environ[_FORGE_VAR] = saved
        r = _simulate_commit(m, env={ENV_RUN_ID: "forged-by-anyone", _FORGE_VAR: s.url},
                             real=True, url=_dead_url())
    ok = (seam_at_rest is None and chosen == "http://127.0.0.1:8010/mcp"
          and _full(m, r, ATTEST_UNREACHABLE) and s.calls == [])
    return ok, "%s=<yes stub>: answerer=%s; hook -> %s, stub saw %s" % (
        _FORGE_VAR, chosen, _say(r, ATTEST_UNREACHABLE), s.calls)


# ------------------------------------------------------------------ concurrency (cc) controls
#
# Each drives the REAL `pre_push` / `pre_commit`, the REAL `run()` and the REAL scheduler, with only
# the process seam `_child` stubbed — so what is tested is the decision code consuming legs that ran
# early, exactly as production does. Nothing here launches a checker. Event order is read from a log
# appended under a lock, never from clocks, so no control depends on timer resolution.

def _cc_label(inv, phase):
    rows = ([(label, tuple(argv)) for label, argv, _ok in PRE_PUSH_EXPECT if argv]
            if phase == "push" else
            [(label, tuple(argv) + ("--block", "--record")) for label, argv, _ok, _d
             in PRE_COMMIT_CHECKS])
    for label, argv in rows:
        if tuple(inv[:len(argv)]) == argv:
            return label
    return inv[0] if inv else "?"


def _cc_script(red=(), raises=(), partial=(), error=(), sleeps=None):
    """A stub leg: `(rc, text, sleep)` per label. `error` legs write and then RAISE (a scheduler-side
    failure), `partial` legs write a line with no newline and die with a crash code."""
    def script(lab):
        sl = (sleeps or {}).get(lab, 0)
        if lab in raises:
            raise OSError(2, "ctl: cannot start %s" % lab)
        if lab in error:
            return "RAISE", "PARTIAL-ERROR-%s" % lab, sl
        if lab in partial:
            return 3221225477, "PARTIAL-OUTPUT-%s" % lab, sl
        return (1 if lab in red else 0), "OUT %s\n  detail of %s\n" % (lab, lab), sl
    return script


def _simulate_conc(m, jobs, phase="push", script=None, stdin=_REFS, receipt=None, digest_seq=None):
    """Run `m.pre_push` / `m.pre_commit` with `ZP_HOOK_JOBS=jobs` and only `_child` stubbed.
    `receipt` is written where the hook reads it; `digest_seq(n)` is the tools/verify digest the
    n-th read returns (default: always `_DIGEST`)."""
    import io as _io
    import json
    import shutil
    import tempfile
    import threading
    import time
    script = script or _cc_script()
    tmp = tempfile.mkdtemp(prefix="zp_hooks_cc_")
    names = ("_child", "tools_digest", "head_tree", "git_out", "_RECEIPT_PATH_OVERRIDE")
    saved = {n: getattr(m, n) for n in names}
    switch_vars = sorted({var for var, _val in SKIP_SWITCHES.values()})
    env_keys = (ENV_RUN_ID, ENV_OP, "ZPLEDGER_BASIS", "ZPLEDGER_RUN", JOBS_ENV,
                LEG_TIMEOUT_ENV) + tuple(switch_vars)
    saved_env = {k: os.environ.get(k) for k in env_keys}
    events, streamed, sched_seen = [], [], []
    lock = threading.Lock()

    def fake_child(cmd, env=None, out=None, timeout=None):
        lab = _cc_label(m._invocation(cmd), phase)
        with lock:
            events.append(("start", lab))
            streamed.append(out is None)
            sched_seen.append(m._SCHED is not None)
        try:
            rc, text, sl = script(lab)
            if sl:
                time.sleep(sl)
            if out is None:
                sys.stdout.write(text)
            else:
                out.write(text.encode("utf-8"))
                out.flush()
            if rc == "RAISE":
                raise RuntimeError("ctl: the leg's worker raised after writing")
            return rc
        finally:
            with lock:
                events.append(("end", lab))

    def digest():
        with lock:
            events.append(("digest", None))
            n = sum(1 for kind, _l in events if kind == "digest")
        return digest_seq(n) if digest_seq else _DIGEST

    m._child = fake_child
    m.tools_digest = digest
    m.head_tree = lambda: _TREE
    m.git_out = lambda *a: (0, "illustrated\n")
    m._RECEIPT_PATH_OVERRIDE = os.path.join(tmp, m.RECEIPT_NAME)
    if receipt is not None:
        with open(m._RECEIPT_PATH_OVERRIDE, "w", encoding="utf-8") as fh:
            json.dump(receipt, fh)
    for k in env_keys:
        os.environ.pop(k, None)
    os.environ[JOBS_ENV] = str(jobs)
    del m.EXECUTED[:], m.REFS_SEEN[:], m.REF_TUPLES[:]
    buf, real = _io.StringIO(), sys.stdout
    try:
        sys.stdout = buf
        rc = m.pre_push(_io.StringIO(stdin)) if phase == "push" else m.pre_commit()
        executed = list(m.EXECUTED)
        leaked = m._SCHED is not None
    finally:
        sys.stdout = real
        for n, v in saved.items():
            setattr(m, n, v)
        for k, v in saved_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        del m.EXECUTED[:], m.REFS_SEEN[:], m.REF_TUPLES[:]
        m._SCHED = None
        shutil.rmtree(tmp, ignore_errors=True)
    return {"rc": rc, "out": buf.getvalue(), "executed": executed, "events": events,
            "streamed": streamed, "sched_seen": sched_seen, "leaked": leaked}


_CC_DRAIN = "=== concurrent leg(s) this run did not reach"


def _cc_lines(out):
    """The output as the operator reads it, minus the scheduler's own `concurrency:` lines and minus
    the drained-leg block that only a concurrent RED run can print after its decision."""
    lines = out.splitlines()
    for i, line in enumerate(lines):
        if line.startswith(_CC_DRAIN):
            lines = lines[:i]
            break
    lines = [ln for ln in lines if not ln.startswith("  concurrency:")]
    while lines and not lines[-1].strip():
        lines.pop()
    return lines


def _cc_fixtures():
    return [("push green", "push", _cc_script()),
            ("push one BLOCK red", "push", _cc_script(red=("check_pov",))),
            ("push one leg cannot start", "push", _cc_script(raises=("check_moved",))),
            ("commit green", "commit", _cc_script()),
            ("commit one BLOCK red", "commit", _cc_script(red=("check_pov",))),
            ("commit one leg cannot start", "commit", _cc_script(raises=("check_modal",)))]


def _ctl_cc_equivalence(m):
    """jobs=4 must equal jobs=1: exit code, EXECUTED (what reconcile reads), and every line printed
    up to the decision, on green, one-red-BLOCK and one-leg-cannot-start, at both phases."""
    bad = []
    for name, phase, script in _cc_fixtures():
        s = _simulate_conc(m, 1, phase, script)
        c = _simulate_conc(m, 4, phase, script)
        same = (s["rc"] == c["rc"] and s["executed"] == c["executed"]
                and _cc_lines(s["out"]) == _cc_lines(c["out"]) and not c["leaked"]
                and all(s["streamed"]) and not all(c["streamed"]))
        if not same:
            bad.append("%s (rc %s vs %s, executed equal=%s, output equal=%s)" % (
                name, s["rc"], c["rc"], s["executed"] == c["executed"],
                _cc_lines(s["out"]) == _cc_lines(c["out"])))
    return not bad, "%d fixture(s); differing: %s" % (len(_cc_fixtures()), "; ".join(bad) or "none")


def _ctl_cc_order(m):
    """Legs that FINISH in reverse body order are still printed in body order."""
    body = [label for label, argv, _o in PRE_PUSH_EXPECT if argv and label not in
            _PUSH_PURE + _PUSH_MUTATORS + ("batch prepush",)]
    sleeps = {label: 0.004 * (len(body) - i) for i, label in enumerate(body)}
    s = _simulate_conc(m, 1, "push", _cc_script(sleeps=sleeps))
    c = _simulate_conc(m, 32, "push", _cc_script(sleeps=sleeps))
    ends = [lab for kind, lab in c["events"] if kind == "end" and lab in body]
    reversed_finish = ends != [lab for lab in body if lab in ends]
    marks = lambda out: [ln[4:] for ln in out.splitlines() if ln.startswith("OUT ")]
    ok = reversed_finish and marks(c["out"]) == marks(s["out"]) and c["rc"] == s["rc"] == 0
    return ok, "legs finished out of body order=%s; printed order equals jobs=1=%s" % (
        reversed_finish, marks(c["out"]) == marks(s["out"]))


def _ctl_cc_dependency(m):
    """No reader (batch prepush included) starts before the mutators and the selftest END; the
    second mutator starts after the first ends; the receipt key is taken before any mutator."""
    sleeps = {"advisory-skip controls": 0.03, "guards": 0.05, "check_checkers": 0.15}
    c = _simulate_conc(m, 32, "push", _cc_script(sleeps=sleeps))
    ev = c["events"]
    idx = lambda kind, lab: ev.index((kind, lab)) if (kind, lab) in ev else None
    viol = []
    prereq = _PUSH_PURE + _PUSH_MUTATORS
    for kind, lab in ev:
        if kind != "start" or lab in prereq:
            continue
        for p in prereq:
            if idx("end", p) is None or idx("end", p) > idx("start", lab):
                viol.append("%s started before %s ended" % (lab, p))
    if idx("end", "guards") is None or idx("end", "guards") > idx("start", "check_checkers"):
        viol.append("check_checkers started before guards ended")
    d = idx("digest", None)
    if d is None or d > idx("start", "guards"):
        viol.append("the receipt key was not taken before guards started")
    started = sum(1 for kind, _l in ev if kind == "start")
    return (not viol and c["rc"] == 0 and started == len([a for _l, a, _o in PRE_PUSH_EXPECT if a]),
            "%d leg(s) launched, rc=%s; edge violations: %s" % (started, c["rc"],
                                                                  "; ".join(viol[:3]) or "none"))


def _ctl_cc_fail(m):
    """A red BLOCK leg that ran concurrently still exits 1 — a reader, a mutator, and at commit."""
    r1 = _simulate_conc(m, 8, "push", _cc_script(red=("check_pov",)))
    r2 = _simulate_conc(m, 8, "push", _cc_script(red=("guards",)))
    r3 = _simulate_conc(m, 8, "commit", _cc_script(red=("check_pov",)))
    ok = r1["rc"] == 1 and r2["rc"] == 1 and r3["rc"] == 1
    return ok, "check_pov red at push -> rc=%s; guards red -> rc=%s; check_pov red at commit -> rc=%s" % (
        r1["rc"], r2["rc"], r3["rc"])


def _ctl_cc_no_loss(m):
    """A leg that dies mid-output, one whose worker raises, and every leg launched past an early
    return all have their output on screen; the dying and raising legs count as failed."""
    r1 = _simulate_conc(m, 8, "push", _cc_script(partial=("check_pov",)))
    r2 = _simulate_conc(m, 8, "commit", _cc_script(error=("check_modal",)))
    r3 = _simulate_conc(m, 32, "push", _cc_script(red=("check_paths",)))
    started = sorted({lab for kind, lab in r3["events"] if kind == "start"})
    lost = [lab for lab in started if "OUT %s" % lab not in r3["out"]]
    # ⚠ AND `_consume` ITSELF, not only the run's exit code: `reconcile` also blocks a leg that never
    #   reached EXECUTED, so a run-level check alone cannot see this first protection removed.
    import io as _io
    import shutil
    import tempfile
    d = tempfile.mkdtemp(prefix="zp_hooks_cc_")
    path = os.path.join(d, "leg.out")
    with open(path, "wb") as fh:
        fh.write(b"PARTIAL-ERROR-unit")
    job = m._Job(("x.py",), dict(os.environ), "ctl-leg", 0, (0,), (), 1)
    job.state, job.outcome, job.error, job.out_path = _DONE, LEG_ERROR, RuntimeError("ctl"), path
    saved_exec = list(m.EXECUTED)
    buf, real = _io.StringIO(), sys.stdout
    try:
        sys.stdout = buf
        unit_rc = m._consume(("x.py",), job)
        unit_rec = m.EXECUTED[len(saved_exec):]
    finally:
        sys.stdout = real
        m.EXECUTED[:] = saved_exec
        shutil.rmtree(d, ignore_errors=True)
    unit_ok = unit_rc == 1 and not unit_rec and "PARTIAL-ERROR-unit" in buf.getvalue()
    ok = (r1["rc"] == 1 and "PARTIAL-OUTPUT-check_pov" in r1["out"]
          and r2["rc"] == 1 and "PARTIAL-ERROR-check_modal" in r2["out"]
          and r3["rc"] == 1 and not lost and len(started) > 6 and unit_ok)
    return ok, ("crash mid-line -> rc=%s, partial shown=%s; worker raised -> rc=%s, partial shown=%s; "
                "red at check_paths: %d launched, output missing for %s; _consume(ERROR) -> rc=%s, "
                "recorded as launched=%s" % (
                    r1["rc"], "PARTIAL-OUTPUT-check_pov" in r1["out"], r2["rc"],
                    "PARTIAL-ERROR-check_modal" in r2["out"], len(started), lost or "none",
                    unit_rc, bool(unit_rec)))


def _ctl_cc_timeout(m):
    """The REAL `_child` kills a leg that outlives its timeout, keeps what it wrote, and `_consume`
    turns that into exit 124 — recorded as launched, never a pass."""
    import io as _io
    import shutil
    import tempfile
    import time
    d = tempfile.mkdtemp(prefix="zp_hooks_cc_")
    path = os.path.join(d, "leg.out")
    cmd = [sys.executable, "-c", "import sys,time; sys.stdout.write('TIMEOUT-PARTIAL'); "
           "sys.stdout.flush(); time.sleep(2.5)"]
    t0 = time.time()
    raised = False
    try:
        with open(path, "wb") as fh:
            try:
                m._child(cmd, None, fh, 0.4)
            except m._LegTimeout:
                raised = True
        elapsed = time.time() - t0
        with open(path, "rb") as fh:
            kept = b"TIMEOUT-PARTIAL" in fh.read()
        job = m._Job(cmd, dict(os.environ), "ctl-leg", 0, (0,), (), 1)
        job.state, job.outcome, job.rc, job.error, job.out_path = (
            _DONE, LEG_TIMEOUT, TIMEOUT_RC, 0.4, path)
        saved_exec = list(m.EXECUTED)
        buf, real = _io.StringIO(), sys.stdout
        try:
            sys.stdout = buf
            rc = m._consume(tuple(cmd), job)
            recorded = m.EXECUTED[len(saved_exec):]
        finally:
            sys.stdout = real
            m.EXECUTED[:] = saved_exec
    finally:
        shutil.rmtree(d, ignore_errors=True)
    ok = raised and elapsed < 2.2 and kept and rc == TIMEOUT_RC and recorded and \
        recorded[0][1] == TIMEOUT_RC and "TIMEOUT-PARTIAL" in buf.getvalue()
    return ok, "killed after %.1fs=%s, partial kept=%s; consumed -> rc=%s, recorded=%s" % (
        elapsed, raised, kept, rc, recorded)


def _ctl_cc_env_refused(m):
    """A leg whose launch environment differs from the sequential call's is refused, not read."""
    import io as _io
    import shutil
    import tempfile
    d = tempfile.mkdtemp(prefix="zp_hooks_cc_")
    path = os.path.join(d, "leg.out")
    with open(path, "wb") as fh:
        fh.write(b"ctl output\n")
    env = dict(os.environ)
    env["ZPLEDGER_BASIS"] = "ctl-a-basis-nobody-set"
    job = m._Job(("x.py",), env, "ctl-leg", 0, (0,), (), 1)
    job.state, job.outcome, job.rc, job.out_path = _DONE, LEG_EXITED, 0, path
    saved_exec = list(m.EXECUTED)
    buf, real = _io.StringIO(), sys.stdout
    try:
        sys.stdout = buf
        rc = m._consume(("x.py",), job)
    finally:
        sys.stdout = real
        m.EXECUTED[:] = saved_exec
        shutil.rmtree(d, ignore_errors=True)
    ok = rc == 1 and "REFUSED" in buf.getvalue() and "ctl output" in buf.getvalue()
    return ok, "a green leg launched under another ZPLEDGER_BASIS -> rc=%s, refused=%s" % (
        rc, "REFUSED" in buf.getvalue())


def _ctl_cc_unread(m):
    """A green run that launched a leg its decision code never read is refused."""
    import io as _io
    saved = m._child
    m._child = lambda cmd, env=None, out=None, timeout=None: 0
    buf, real = _io.StringIO(), sys.stdout
    try:
        sys.stdout = buf
        s = m._Scheduler("push", 2, None, stop_on_red=True)
        s.submit(("ctl-orphan.py",), dict(os.environ), "ctl orphan", 0)
        rc = s.finish(0)
    finally:
        sys.stdout = real
        m._child = saved
    return rc == 1, "green body, one launched leg never consumed -> rc=%s" % rc


def _ctl_cc_jobs_one(m):
    """ZP_HOOK_JOBS=1 creates no scheduler and streams every leg — today's path — at both phases;
    an unreadable value falls back to it."""
    p = _simulate_conc(m, 1, "push")
    c = _simulate_conc(m, 1, "commit")
    seq = all(p["streamed"] + c["streamed"]) and not any(p["sched_seen"] + c["sched_seen"])
    parse = (m.hook_jobs({JOBS_ENV: "many"})[0] == 1 and m.hook_jobs({JOBS_ENV: "0"})[0] == 1
             and m.hook_jobs({JOBS_ENV: "1"})[0] == 1 and m.hook_jobs({})[0] == m.DEFAULT_JOBS)
    return seq and parse and p["rc"] == c["rc"] == 0, (
        "jobs=1: %d+%d launch(es), all streamed with no scheduler=%s; unreadable/0 -> 1=%s" % (
            len(p["streamed"]), len(c["streamed"]), seq, parse))


def _ctl_cc_lost(m):
    """RELY-CC-3 M3: a leg whose captured output cannot be read back is FAILED even though it exited
    0, and is NOT recorded as launched — its output is missing, so its exit code proves nothing."""
    import io as _io
    import shutil
    import tempfile
    d = tempfile.mkdtemp(prefix="zp_hooks_cc_")
    job = m._Job(("x.py",), dict(os.environ), "ctl-leg", 0, (0,), (), 1)
    job.state, job.outcome, job.rc = _DONE, LEG_EXITED, 0
    job.out_path = os.path.join(d, "never-written", "leg.out")
    saved_exec = list(m.EXECUTED)
    buf, real = _io.StringIO(), sys.stdout
    try:
        sys.stdout = buf
        rc = m._consume(("x.py",), job)
        rec = m.EXECUTED[len(saved_exec):]
    finally:
        sys.stdout = real
        m.EXECUTED[:] = saved_exec
        shutil.rmtree(d, ignore_errors=True)
    ok = rc == 1 and not rec and job.lost and "could not be read back" in buf.getvalue()
    return ok, "exit 0, capture unreadable -> rc=%s, lost=%s, recorded as launched=%s" % (
        rc, job.lost, bool(rec))


def _ctl_cc_early_key_used(m):
    """RELY-CC-3 M6: the skip decision USES the key taken before any leg launched. The tools/verify
    digest moves after its first read (guards rewrites files there), so a receipt matching the EARLY
    digest matches only if the early key is the one consulted — the key USED, not merely the first
    digest call, which `_ctl_cc_dependency` already pins."""
    c = _simulate_conc(m, 8, "push", receipt=_good_receipt(),
                       digest_seq=lambda n: _DIGEST if n == 1 else "f" * 64)
    reads = sum(1 for kind, _l in c["events"] if kind == "digest")
    ok = c["rc"] == 0 and "SKIPPED agent gate: matched green run ctl-preflight-1" in c["out"]
    return ok, "digest moved after read 1 of %d; receipt for the early key -> rc=%s, matched=%s" % (
        reads, c["rc"], "SKIPPED agent gate" in c["out"])


def _ctl_probe_selftest_blocks(m):
    """RELY-CC-5: a red `probe_routing_behavioural.py --selftest` blocks the push at ITS OWN call
    site, before the probe itself is launched."""
    st = ("probe_routing_behavioural.py", "--selftest")
    r = _simulate(m, red=(st,))
    launched = lambda argv: any(tuple(inv[:len(argv)]) == argv for inv in r["launched"])
    probe = launched(("probe_routing_behavioural.py", "--mutations"))
    ok = (r["rc"] == 1 and launched(st) and not probe
          and "Push blocked: the routing control's own controls" in r["out"])
    return ok, "probe --selftest exits 1 -> rc=%s, selftest launched=%s, probe launched=%s" % (
        r["rc"], launched(st), probe)


def _ctl_probe_rows_distinct(m):
    """RELY-CC-5: each probe row is satisfied ONLY by its own launch. `_found` matches by prefix, so
    with every advertised child recorded except one probe row's, `reconcile` must refuse and name
    THAT row — measured before the explicit flags: a bare `probe_routing_behavioural.py` expectation
    was satisfied by the `--selftest` launch, and deleting the probe's call reconciled 23 of 23."""
    import io as _io
    named = []
    for gone in ("routing control", "routing control selftest"):
        saved = list(m.EXECUTED)
        buf, real = _io.StringIO(), sys.stdout
        try:
            del m.EXECUTED[:]
            for label, argv, _ok in m.PRE_PUSH_EXPECT:
                if argv and label != gone:
                    m.EXECUTED.append((tuple(argv), 0))
            sys.stdout = buf
            rc = m.reconcile("push", m.PRE_PUSH_EXPECT)
        finally:
            sys.stdout = real
            m.EXECUTED[:] = saved
        hit = any(ln.strip().endswith("never ran: %s" % gone) for ln in buf.getvalue().splitlines())
        named.append((gone, rc, hit))
    return all(rc == 1 and hit for _g, rc, hit in named), "; ".join(
        "%s not launched -> rc=%s, named=%s" % n for n in named)


# (label, control, anchor, replacement). The replacement removes exactly the protection the
# control exists for; the control must PASS on the real module and FAIL on the mutant.
_CONTROLS = [
    # ⚠ CONCURRENT LEGS (`ZP_HOOK_JOBS`, 2026-10-04). Each mutant removes one property of the
    #   scheduler: an equivalence, the replay order, a dependency edge, failure propagation, an
    #   output path, the timeout, the env fence, the unread-leg refusal, the jobs=1 switch.
    ("cc  equivalence: NOSTART read as a pass", _ctl_cc_equivalence,
     '        print("  hook: could not run %s (%s)" % (" ".join(cmd), job.error))\n        return 1',
     '        print("  hook: could not run %s (%s)" % (" ".join(cmd), job.error))\n        return 0'),
    ("cc  equivalence: consumed leg never recorded", _ctl_cc_equivalence,
     "    EXECUTED.append((_invocation(cmd), job.rc))\n    return job.rc",
     "    return job.rc"),
    ("cc  order: replayed at completion, not at turn", _ctl_cc_order,
     "                job.state = _DONE\n",
     "                job.state = _DONE\n                _replay_job(job)\n"),
    ("cc  dependency: reader edges dropped", _ctl_cc_dependency,
     "            readers_after = _PUSH_MUTATORS + _PUSH_PURE",
     "            readers_after = ()"),
    ("cc  dependency: batch prepush edges dropped", _ctl_cc_dependency,
     "    bp_after = _PUSH_MUTATORS + _PUSH_PURE",
     "    bp_after = ()"),
    ("cc  dependency: mutator chain dropped", _ctl_cc_dependency,
     "            chain = _PUSH_MUTATORS[:_PUSH_MUTATORS.index(label)]",
     "            chain = ()"),
    ("cc  dependency: receipt key taken after launch", _ctl_cc_dependency,
     "    sched.early_key = push_key(REF_TUPLES)",
     "    sched.early_key = (None, \"ctl: deferred\")"),
    ("cc  fail: a red leg's exit code lost", _ctl_cc_fail,
     "            job.rc = rc\n",
     "            job.rc = 0\n"),
    ("cc  no loss: captured output not replayed", _ctl_cc_no_loss,
     "            data = fh.read()",
     '            data = b""'),
    ("cc  no loss: a raising worker read as a pass", _ctl_cc_no_loss,
     '              "never a pass." % (job.label, job.error))\n        return 1',
     '              "never a pass." % (job.label, job.error))\n        return 0'),
    ("cc  no loss: legs past an early return dropped", _ctl_cc_no_loss,
     "                    _replay_job(job)\n            never =",
     "                    pass\n            never ="),
    ("cc  timeout: the wait has no timeout", _ctl_cc_timeout,
     "        return p.wait(timeout=timeout)",
     "        return p.wait()"),
    ("cc  timeout: a timed-out leg read as a pass", _ctl_cc_timeout,
     "        return TIMEOUT_RC",
     "        return 0"),
    ("cc  env: a leg launched under another env is read", _ctl_cc_env_refused,
     "    if job.env != dict(os.environ):",
     "    if False:"),
    ("cc  unread: a green run that launched an unread leg", _ctl_cc_unread,
     "            if rc == 0 and unread:",
     "            if False:"),
    # ⚠ RELY-CC-3 (2026-10-04): the two scheduler properties no cc control observed (M3, M6).
    ("cc  lost: an unreadable capture read as its exit code", _ctl_cc_lost,
     "    if job.lost:\n        return 1",
     "    if job.lost:\n        pass"),
    ("cc  key: the decision recomputes the receipt key", _ctl_cc_early_key_used,
     "    key, _why = _SCHED.early_key if _SCHED is not None else push_key(REF_TUPLES)",
     "    key, _why = push_key(REF_TUPLES)"),
    # ⚠ RELY-CC-5: the probe's own controls are a BLOCK leg; a red one stops the push at its site.
    ("wiring  a red probe --selftest blocks the push", _ctl_probe_selftest_blocks,
     '    if py("probe_routing_behavioural.py", "--selftest") != 0:',
     "    if False:"),
    ("wiring  the probe run is not satisfied by --selftest", _ctl_probe_rows_distinct,
     '    ("routing control", ("probe_routing_behavioural.py", "--mutations"), (0,)),',
     '    ("routing control", ("probe_routing_behavioural.py",), (0,)),'),
    ("wiring  --selftest is not satisfied by the probe run", _ctl_probe_rows_distinct,
     '    ("routing control selftest", ("probe_routing_behavioural.py", "--selftest"), (0,)),',
     '    ("routing control selftest", ("probe_routing_behavioural.py",), (0,)),'),
    ("cc  jobs=1 (push) still schedules", _ctl_cc_jobs_one,
     "    if _jobs > 1:\n        _t, _tnote = leg_timeout()\n        _start_push_prefetch",
     "    if _jobs >= 1:\n        _t, _tnote = leg_timeout()\n        _start_push_prefetch"),
    ("cc  jobs=1 (commit) still schedules", _ctl_cc_jobs_one,
     "    if _jobs > 1:\n        _t, _tnote = leg_timeout()\n        _start_commit_prefetch",
     "    if _jobs >= 1:\n        _t, _tnote = leg_timeout()\n        _start_commit_prefetch"),
    ("cc  an unreadable ZP_HOOK_JOBS is not the default", _ctl_cc_jobs_one,
     '        return 1, "%s=%r is not an integer; running SEQUENTIALLY" % (JOBS_ENV, raw)',
     '        return DEFAULT_JOBS, "%s=%r is not an integer; running SEQUENTIALLY" % (JOBS_ENV, raw)'),
    ("positive  a matching receipt skips agent gate", _ctl_positive,
     "        os.environ[var] = val",
     "        pass"),
    ("switch    the skip does not outlive its launch", _ctl_switch_restored,
     "        for var, old in _saved_switch.items():",
     "        for var, old in []:"),
    ("(a) BLOCK leg red under a matched receipt", _ctl_a_block_red,
     "        if status == MATCHED:\n            _batch_labels =",
     "        if status == MATCHED:\n            return 0\n            _batch_labels ="),
    ("(b) one stdin sha changed", _ctl_b_sha_changed,
     '        if rec.get(part) != key[part]:',
     '        if part != "refs" and rec.get(part) != key[part]:'),
    ("(c) GITROBOT_RUN_ID by hand, no receipt", _ctl_c_env_no_receipt,
     "    path = receipt_path()\n    if path is None:\n        return UNREADABLE",
     "    if os.environ.get(ENV_RUN_ID):\n        return MATCHED, {\"gitrobot_run_id\": "
     "os.environ.get(ENV_RUN_ID), \"ts_utc\": \"env\", \"refs\": []}, \"env\"\n"
     "    path = receipt_path()\n    if path is None:\n        return UNREADABLE"),
    ("(d) a skipping run's receipt never qualifies", _ctl_d_skipping_receipt,
     '    if rec.get("terminal") != "PASS" or rec.get("skipped") != []:',
     '    if rec.get("terminal") != "PASS":'),
    ("(e) a receipt whose digest differs is refused", _ctl_e_digest,
     '    for part in ("refs", "tools_verify_digest", "head_tree"):',
     '    for part in ("refs", "head_tree"):'),
    ("(f) a consumed receipt does not match twice", _ctl_f_single_use,
     '    if rec.get("consumed_at"):',
     '    if False:'),
    ("(g) a receipt older than 24h does not match", _ctl_g_stale,
     "    if age < 0 or age > RECEIPT_MAX_AGE:",
     "    if age < 0:"),
    ("R-ZERONULL unreadable is not NO_RECEIPT", _ctl_unreadable,
     '        return UNREADABLE, None, "receipt is not valid JSON',
     '        return NO_RECEIPT, None, "receipt is not valid JSON'),
    ("writer  a green unskipped run mints a receipt", _ctl_writes,
     "    if scan_exit == 0:\n        write_green_receipt(key, skip, child_off)",
     "    if False:\n        write_green_receipt(key, skip, child_off)"),
    # ⚠ The eight below close ORDINARY-1 and ORDINARY-2 of the 2026-09-30 `/rely` round; each
    #   mutant is the reviewer's own (M1, M2, M3, M4, M6, M8, M12) or, for (h), the inherited opt-out.
    ("(h) an inherited opt-out mints no receipt", _ctl_h_inherited_optout,
     "    child_off = legs_disabled()",
     "    child_off = list(skip)"),
    ("(i) M3 a future-dated receipt does not match", _ctl_i_future,
     "    if age < 0 or age > RECEIPT_MAX_AGE:",
     "    if age > RECEIPT_MAX_AGE:"),
    ("(j) M6 a receipt without the schema is refused", _ctl_j_schema,
     '    if not isinstance(rec, dict) or rec.get("schema") != RECEIPT_SCHEMA:',
     '    if not isinstance(rec, dict):'),
    ("(k) M12 a non-PASS receipt is refused", _ctl_k_terminal,
     '    if rec.get("terminal") != "PASS" or rec.get("skipped") != []:',
     '    if rec.get("skipped") != []:'),
    ("(l) M4 the end-of-run key re-check holds", _ctl_l_end_key,
     "    if end_key != key:",
     "    if False:"),
    ("(m) M1 REAL digest moves on a content edit", _ctl_m_digest_content,
     "                inner = hashlib.sha256(fh.read()).hexdigest()",
     '                inner = "same"'),
    ("(n) M8 REAL digest hashes a deleted file ABSENT", _ctl_n_digest_absent,
     '        except OSError:\n            inner = "ABSENT"',
     "        except OSError:\n            continue"),
    ("(o) M2 REAL head_tree follows HEAD", _ctl_o_head_tree,
     "    return out.strip() if rc == 0 and out.strip() else None",
     '    return "e" * 40'),
    ("fence 3 reconcile refuses a skipped BLOCK row", _ctl_reconcile,
     "            _bad_skip = sorted(set(skipped) & _never) + sorted(set(skipped) - _known)",
     "            _bad_skip = []"),
    ("invariant no BLOCK row in the set (mode)", _ctl_invariant,
     '                     if mode == "WARN" and emitter and emitter not in gating)',
     '                     if emitter and emitter not in gating)'),
    ("invariant no gating emitter in the set", _ctl_invariant,
     '                     if mode == "WARN" and emitter and emitter not in gating)',
     '                     if mode == "WARN" and emitter)'),
    ("literal  absent `actions` still gates", _ctl_literal,
     '        if "actions" not in spec or spec["actions"]:',
     '        if spec.get("actions"):'),
    ("literal  a batch.py-computed row stays unskippable", _ctl_literal,
     '        rows.append((label, mode, emitter or "tools/verify/batch.py"))',
     '        rows.append((label, mode, emitter or "tools/verify/report.py"))'),
    # ⚠ PRE-COMMIT PASS-CACHE (Tim's R10, 2026-10-03). MUST SKIP on a stubbed yes for this tree;
    #   MUST RUN ALL ELEVEN LEGS on every other answer. Each mutant turns one non-yes into a skip.
    ("pc  attested:true for this tree skips", _ctl_attest_yes,
     '    if status == ATTEST_YES:\n        print("SKIPPED pre-commit',
     '    if False:\n        print("SKIPPED pre-commit'),
    # mcp-mayhem's two named mutants: (1) skip on an exception from the transport/parse path,
    # (2) skip without checking `attested` (on any ok:true response, or on any response at all).
    ("pc  M-gr1 skip on a transport exception", _ctl_attest_error,
     "        return _classify_attest_exception(e), run_id, tree,",
     "        return ATTEST_YES, run_id, tree,"),
    ("pc  M-gr1 skip on an exception while judging", _ctl_attest_judge_raises,
     '        return ATTEST_ERROR, run_id, tree, "judging',
     '        return ATTEST_YES, run_id, tree, "judging'),
    ("pc  M-gr2 skip on ok:true without `attested`", _ctl_attest_denied,
     '    if sc.get("attested") is False:\n'
     '        return ATTEST_DENIED, "attested: false, why: %s" % (sc.get("why"),)\n'
     '    if sc.get("attested") is not True:\n'
     '        return ATTEST_MALFORMED, "attested=%r is not the boolean true" % '
     '(sc.get("attested"),)\n',
     ''),
    ("pc  M-gr2 skip on any response at all", _ctl_attest_denied,
     "        status, detail = _judge_attest(res, tree, run_id, call_id)",
     '        status, detail = ATTEST_YES, "any response"'),
    ("pc  worktree: write-tree follows the invoking checkout", _ctl_attest_index_tree,
     '    rc, out = git_out("write-tree")',
     '    rc, out = git_out("-C", os.path.dirname(REPO), "write-tree")'),
    ("pc  attested:false runs in full, prints why", _ctl_attest_denied,
     '        return ATTEST_DENIED, "attested: false',
     '        return ATTEST_YES, "attested: false'),
    ("pc  unreachable runs in full", _ctl_attest_unreachable,
     "        return ATTEST_UNREACHABLE\n    if isinstance(e, ValueError):",
     "        return ATTEST_YES\n    if isinstance(e, ValueError):"),
    ("pc  timeout runs in full", _ctl_attest_timeout,
     "    if isinstance(e, (socket.timeout, TimeoutError)):\n        return ATTEST_TIMEOUT",
     "    if isinstance(e, (socket.timeout, TimeoutError)):\n        return ATTEST_YES"),
    ("pc  R-ZERONULL timeout is not UNREACHABLE", _ctl_attest_timeout,
     'ATTEST_TIMEOUT = "TIMEOUT"',
     'ATTEST_TIMEOUT = "UNREACHABLE"'),
    ("pc  no GITROBOT_RUN_ID runs in full, no call", _ctl_attest_no_env,
     "    if not run_id:\n        return ATTEST_NO_RUN_ID",
     "    if False:\n        return ATTEST_NO_RUN_ID"),
    ("pc  no write-tree runs in full, no call", _ctl_attest_no_tree,
     "    if not tree:\n        return ATTEST_NO_TREE",
     "    if False:\n        return ATTEST_NO_TREE"),
    ("pc  malformed JSON runs in full", _ctl_attest_bad_json,
     "    if isinstance(e, ValueError):\n        return ATTEST_MALFORMED",
     "    if isinstance(e, ValueError):\n        return ATTEST_YES"),
    ("pc  attested not the boolean true runs in full", _ctl_attest_not_bool,
     '    if sc.get("attested") is not True:',
     '    if not sc.get("attested"):'),
    ("pc  no structuredContent runs in full", _ctl_attest_no_structured,
     '    sc = result.get("structuredContent")',
     '    sc = result.get("structuredContent") or '
     '__import__("json").loads(result["content"][0]["text"])'),
    ("pc  isError:true runs in full", _ctl_attest_is_error,
     '    if "isError" in result and result["isError"] is not False:',
     '    if False:'),
    ("pc  ok:false runs in full", _ctl_attest_not_ok,
     '    if sc.get("ok") is not True:',
     '    if False:'),
    ("pc  a yes about another tree runs in full", _ctl_attest_tree_echo,
     '    if sc.get("tree") != tree:',
     '    if False:'),
    ("pc  any other exception runs in full", _ctl_attest_error,
     "    return ATTEST_ERROR\n\n\ndef _judge_attest",
     "    return ATTEST_YES\n\n\ndef _judge_attest"),
    ("pc  REAL index_tree follows the staged index", _ctl_attest_index_tree,
     "    return tree if rc == 0 and tree else None",
     '    return "e" * 40'),
    ("pc  REAL transport parses an SSE yes", _ctl_attest_real_yes,
     '        if line.startswith("data:"):',
     '        if False:'),
    ("pc  REAL transport times out short", _ctl_attest_real_timeout,
     "        with opener.open(req, timeout=timeout) as resp:",
     "        with opener.open(req) as resp:"),
    ("pc  REAL transport, closed port runs in full", _ctl_attest_real_refused,
     "        return ATTEST_UNREACHABLE\n    if isinstance(e, ValueError):",
     "        return ATTEST_YES\n    if isinstance(e, ValueError):"),
    # ⚠ `/rely` 2026-10-03. (i) is BLOCKING-1's forge; (ii)-(v) are ORDINARY-1's four uncontrolled
    #   mutants, verbatim; (vi)-(viii) are ORDINARY-2 and the unchecked response id.
    ("pc  (i) GITROBOT_URL in the env chooses nothing", _ctl_attest_env_forge,
     "    return _ATTEST_URL_SEAM or ATTEST_URL",
     '    return os.environ.get("GITROBOT_URL") or _ATTEST_URL_SEAM or ATTEST_URL'),
    ("pc  (ii) a yes with no tree echo runs in full", _ctl_attest_no_tree_echo,
     '    if sc.get("tree") != tree:',
     '    if sc.get("tree") is not None and sc.get("tree") != tree:'),
    ("pc  (iii) ok truthy but not True runs in full", _ctl_attest_ok_truthy,
     '    if sc.get("ok") is not True:',
     '    if not sc.get("ok"):'),
    ("pc  (iv) isError any truthy value runs in full", _ctl_attest_is_error_truthy,
     '    if "isError" in result and result["isError"] is not False:',
     '    if result.get("isError") is True:'),
    ("pc  (v) production timeout constant <= 10s", _ctl_attest_timeout_constant,
     "ATTEST_TIMEOUT_S = 4.0",
     "ATTEST_TIMEOUT_S = 600.0"),
    ("pc  (vi) run_id echo mismatch runs in full", _ctl_attest_run_echo,
     '    if sc.get("run_id") != run_id:',
     '    if False:'),
    ("pc  (vii) error beside a result runs in full", _ctl_attest_error_and_result,
     '    if "error" in res:\n        return ATTEST_REFUSED',
     '    if "error" in res and "result" not in res:\n        return ATTEST_REFUSED'),
    ("pc  (viii) response id mismatch runs in full", _ctl_attest_rpc_id,
     "    if res.get(\"id\") != call_id:",
     "    if False:"),
    # ⚠ `/rely` 2026-10-04 round 2: ORDINARY-1's seven uncontrolled mutants, verbatim from the
    #   reviewer's probe_mut.py, then ORDINARY-2 (isError falsy-but-not-False).
    ("pc  (ix) HTTP_PROXY/ALL_PROXY choose nothing", _ctl_attest_proxy_env,
     "    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))",
     "    opener = urllib.request.build_opener()"),
    ("pc  (x) an HTTPError runs in full", _ctl_attest_http_error,
     "    if isinstance(e, urllib.error.HTTPError):\n        return ATTEST_REFUSED",
     "    if isinstance(e, urllib.error.HTTPError):\n        return ATTEST_YES"),
    ("pc  (xi) a URLError wrapping a timeout runs in full", _ctl_attest_urlerror_timeout,
     "        if isinstance(e.reason, (socket.timeout, TimeoutError)):\n            return ATTEST_TIMEOUT",
     "        if isinstance(e.reason, (socket.timeout, TimeoutError)):\n            return ATTEST_YES"),
    ("pc  (xii) a bare OSError runs in full", _ctl_attest_bare_oserror,
     "    if isinstance(e, (ConnectionError, OSError)):\n        return ATTEST_UNREACHABLE",
     "    if isinstance(e, (ConnectionError, OSError)):\n        return ATTEST_YES"),
    ("pc  (xiii) a non-object response runs in full", _ctl_attest_non_dict,
     "    if not isinstance(res, dict):\n        return ATTEST_MALFORMED",
     "    if not isinstance(res, dict):\n        return ATTEST_YES"),
    ("pc  (xiv) a response with no result runs in full", _ctl_attest_no_result,
     '        return ATTEST_MALFORMED, "the response carries no result"',
     '        return ATTEST_YES, "the response carries no result"'),
    ("pc  (xv) a non-object result runs in full", _ctl_attest_result_not_object,
     '        return ATTEST_MALFORMED, "the result is not an object"',
     '        return ATTEST_YES, "the result is not an object"'),
    ("pc  (xvi) isError None/0/\"\"/[]/{} runs in full", _ctl_attest_is_error_falsy,
     '    if "isError" in result and result["isError"] is not False:',
     '    if result.get("isError"):'),
]


# ------------------------------------------------------------------ class detector (DC: uncontrolled
# fail-closed protection in the attest path). Its verb is RUN: it mutates every protection and asks
# whether ANY `pc` control fails, so a protection added later without a control is caught here even
# though no row above names it.
#
#   GENERIC  every `return ATTEST_<anything but YES>` inside the functions in `_SWEEP_FUNCS` is
#            turned, one at a time, into `return ATTEST_YES`. A new fail-closed return lands in the
#            sweep with no edit to this table.
#   EXPLICIT protections that are not a non-yes return (a handler, a keyword argument, a stricter
#            comparison), as a table; a NEW protection of that shape still needs a row here, which
#            is the sweep's stated limit.
_SWEEP_FUNCS = ("_attest_url", "_attest_call", "_classify_attest_exception", "_judge_attest",
                "consult_attest")
_SWEEP_EXPLICIT = [
    ("ProxyHandler({}) removed",
     "    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))",
     "    opener = urllib.request.build_opener()"),
    ("request timeout dropped",
     "        with opener.open(req, timeout=timeout) as resp:",
     "        with opener.open(req) as resp:"),
    ("production timeout constant raised",
     "ATTEST_TIMEOUT_S = 4.0", "ATTEST_TIMEOUT_S = 600.0"),
    ("answerer read from the environment",
     "    return _ATTEST_URL_SEAM or ATTEST_URL",
     '    return os.environ.get("GITROBOT_URL") or os.environ.get("HTTP_PROXY") '
     'or _ATTEST_URL_SEAM or ATTEST_URL'),
    ("transport exception classified as a yes",
     "        return _classify_attest_exception(e), run_id, tree,",
     "        return ATTEST_YES, run_id, tree,"),
    ("isError: falsy accepted",
     '    if "isError" in result and result["isError"] is not False:',
     '    if result.get("isError"):'),
    ("isError: only True refused",
     '    if "isError" in result and result["isError"] is not False:',
     '    if result.get("isError") is True:'),
    ("ok: truthy accepted",
     '    if sc.get("ok") is not True:', '    if not sc.get("ok"):'),
    ("attested: truthy accepted",
     '    if sc.get("attested") is not True:', '    if not sc.get("attested"):'),
    ("tree echo: absent accepted",
     '    if sc.get("tree") != tree:', '    if sc.get("tree") is not None and sc.get("tree") != tree:'),
    ("run echo: absent accepted",
     '    if sc.get("run_id") != run_id:',
     '    if sc.get("run_id") is not None and sc.get("run_id") != run_id:'),
    ("error beside a result accepted",
     '    if "error" in res:\n        return ATTEST_REFUSED',
     '    if "error" in res and "result" not in res:\n        return ATTEST_REFUSED'),
]


def _sweep_mutants():
    """[(name, mutated source or None, why)] — every protection mutant the class detector runs."""
    import ast
    import re
    src_path = os.path.abspath(__file__)
    if src_path.endswith(".pyc"):
        src_path = src_path[:-1]
    with open(src_path, encoding="utf-8") as fh:
        src = fh.read()
    head, sep, tail = src.partition(_CONTROLS_MARK)
    out = []
    spans = {n.name: (n.lineno, n.end_lineno) for n in ast.parse(head).body
             if isinstance(n, ast.FunctionDef) and n.name in _SWEEP_FUNCS}
    for fn in _SWEEP_FUNCS:
        if fn not in spans:
            out.append(("%s: function not found" % fn, None, "SWEEP SCOPE MISSING"))
    lines = head.split("\n")
    pat = re.compile(r"^(\s*return\s+)(ATTEST_(?!YES\b)[A-Z_]+)\b")
    for fn, (lo, hi) in sorted(spans.items(), key=lambda kv: kv[1]):
        for i in range(lo - 1, hi):
            mt = pat.match(lines[i])
            if mt:
                new = lines[:i] + [pat.sub(r"\1ATTEST_YES", lines[i], count=1)] + lines[i + 1:]
                out.append(("%s:%d %s -> ATTEST_YES" % (fn, i + 1, mt.group(2)),
                            "\n".join(new) + sep + tail, None))
    for name, anchor, repl in _SWEEP_EXPLICIT:
        if head.count(anchor) != 1:
            out.append((name, None, "MUTATION DID NOT APPLY — anchor found %d time(s)"
                        % head.count(anchor)))
        else:
            out.append((name, head.replace(anchor, repl, 1) + sep + tail, None))
    return out


_SLOW = ("_real_", "index_tree", "env_forge", "proxy_env")   # loopback servers, scratch repos


def _pc_controls(exclude=()):
    """The distinct `pc` controls, cheap stubbed ones first, so a sweep stops early."""
    out = []
    for label, ctl, _a, _r in _CONTROLS:
        if label.startswith("pc") and ctl not in out and ctl not in exclude:
            out.append(ctl)
    return sorted(out, key=lambda c: any(s in c.__name__ for s in _SLOW))


def _sweep_attest(controls=None, verbose=True, only=None):
    """Run every protection mutant (or those whose name contains `only`) against the `pc`
    controls. Returns (mutants, survivors): a survivor is a mutant on which NO control failed (or
    one that did not apply). A control that raises on a mutant is not counted as catching it, as
    in `selftest`."""
    if controls is None:
        controls = _pc_controls()
    mutants = [mu for mu in _sweep_mutants() if only is None or only in mu[0]]
    survivors = []
    for name, msrc, err in mutants:
        if msrc is None:
            survivors.append((name, err))
            continue
        mod, merr = _mutant_from_source(msrc)
        if mod is None:
            survivors.append((name, merr))
            continue
        caught = None
        for ctl in controls:
            try:
                ok, _why = ctl(mod)
            except Exception:                               # noqa: BLE001 — a crash is not a catch
                continue
            if not ok:
                caught = ctl.__name__
                break
        if caught is None:
            survivors.append((name, "no pc control failed"))
        if verbose:
            print("       sweep %-58s %s" % (name, ("caught by " + caught) if caught else "SURVIVED"))
    return len(mutants), survivors


def _mutant(anchor, repl):
    """(module, None) built from this file's source with ONE anchor replaced, or (None, why).

    Asserts the text actually changed and that the mutant compiles; either failure is reported as
    `MUTATION DID NOT APPLY`, which fails the suite rather than retiring the control."""
    import types
    src_path = os.path.abspath(__file__)
    if src_path.endswith(".pyc"):
        src_path = src_path[:-1]
    with open(src_path, encoding="utf-8") as fh:
        src = fh.read()
    # ⚠ Anchors are searched ABOVE this controls section only: the table above quotes every anchor
    #   as a literal, so a whole-file search would find each one twice and could mutate the quote.
    head, sep, tail = src.partition(_CONTROLS_MARK)
    if head.count(anchor) != 1:
        return None, "MUTATION DID NOT APPLY — anchor found %d time(s)" % head.count(anchor)
    mutated = head.replace(anchor, repl, 1) + sep + tail
    if mutated == src:
        return None, "MUTATION DID NOT APPLY — text unchanged"
    return _mutant_from_source(mutated)


def _mutant_from_source(mutated):
    """(module, None) compiled from a mutated copy of this file's source, or (None, why)."""
    import types
    src_path = os.path.abspath(__file__)
    if src_path.endswith(".pyc"):
        src_path = src_path[:-1]
    try:
        code = compile(mutated, src_path + ".mutant", "exec")
    except SyntaxError as e:
        return None, "MUTATION DID NOT APPLY — mutant does not compile: %s" % (e,)
    mod = types.ModuleType("zp_hooks_mutant")
    mod.__file__ = src_path
    exec(code, mod.__dict__)
    return mod, None


def selftest():
    """Every advisory-skip control, each seen to pass on this module and to FAIL on its mutant."""
    me = sys.modules[__name__]
    print("advisory-skip and pre-commit pass-cache (pc) controls "
          "(each: MUST PASS on the live code, MUST FIRE on its mutant)")
    total = bad = 0
    for label, ctl, anchor, repl in _CONTROLS:
        total += 1
        try:
            ok_live, why_live = ctl(me)
        except Exception as e:                              # noqa: BLE001 — a raise is a failure
            ok_live, why_live = False, "raised %r" % (e,)
        mod, err = _mutant(anchor, repl)
        if mod is None:
            ok_mut, why_mut = True, err                     # True = the mutant "passed" = FAIL
        else:
            try:
                ok_mut, why_mut = ctl(mod)
            except Exception as e:                          # noqa: BLE001 — a crash is not a catch
                ok_mut, why_mut = True, "mutant raised %r, which proves nothing" % (e,)
        good = ok_live and not ok_mut
        bad += 0 if good else 1
        print("  %-4s %-46s live: %s" % ("ok" if good else "FAIL", label, why_live))
        print("       %-46s mutant fired: %s — %s" % ("", "yes" if not ok_mut else "NO", why_mut))
    # The class detector: every attest-path protection mutant must be caught by SOME pc control.
    print("\nclass detector: attest-path protection sweep (each mutant MUST be caught by a pc control)")
    n_mut, survivors = _sweep_attest()
    total += 1
    sweep_ok = n_mut > 0 and not survivors
    bad += 0 if sweep_ok else 1
    print("  %-4s sweep: %d mutant(s), %d survived%s" % (
        "ok" if sweep_ok else "FAIL", n_mut, len(survivors),
        "".join("\n         SURVIVOR %s — %s" % s for s in survivors)))
    # ...and the detector's own control: with the one control for the response-id check withheld,
    # the sweep MUST report that check's mutant as a survivor. A sweep that cannot fail is no detector.
    n2, surv2 = _sweep_attest(controls=_pc_controls(exclude=(_ctl_attest_rpc_id,)), verbose=False,
                              only="ATTEST_RPC_ID")
    total += 1
    det_ok = n2 == 1 and any("RPC_ID" in name for name, _w in surv2)
    bad += 0 if det_ok else 1
    print("  %-4s detector control: _ctl_attest_rpc_id withheld -> survivors %s"
          % ("ok" if det_ok else "FAIL", [name for name, _w in surv2]))
    print("\nhooks advisory-skip selftest: %s (%d/%d control(s))"
          % ("PASS" if not bad else "FAIL", total - bad, total))
    return 1 if bad else 0


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else ""
    try:
        if what == "selftest":
            return selftest()
        if what == "pre-commit":
            return pre_commit()
        if what == "pre-push":
            return pre_push(sys.stdin)
        print("hooks.py: expected 'pre-commit' or 'pre-push', got %r" % what)
        return 1
    except BrokenPipeError:
        # Output was truncated (`git push | head`). The GATE still decides; a closed pipe must
        # never be able to turn a block into a pass.
        try:
            sys.stdout.close()
        except Exception:
            pass
        return 1


if __name__ == "__main__":
    sys.exit(main())
