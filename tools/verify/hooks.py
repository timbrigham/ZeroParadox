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
    captured-then-reprinted stream loses interleaving with anything else that writes."""
    try:
        return subprocess.call(list(cmd), cwd=REPO)
    except OSError as e:
        print("  hook: could not run %s (%s)" % (" ".join(cmd), e))
        return 1


def py(script, *args):
    return run(sys.executable, os.path.join(BASE, script), *args)


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


# ------------------------------------------------------------------ pre-commit

PRE_COMMIT_PLAN = [
    ("check_pov", "BLOCK", "POV claims declare a KIND; DENIALs never allowed"),
    ("check_modal", "BLOCK", "modal claims carry a measurement or a reduction"),
    ("check_classes", "BLOCK", "a new requirements class records a degeneracy verdict"),
    ("check_prose", "BLOCK", "prose caps: block size, docstring vs decl, gloss labels"),
    # ⚠ AT COMMIT, NOT ONLY AT PUSH, AND FOR A REASON THE OTHER FOUR DO NOT SHARE. Double-encoded
    # text is valid UTF-8, so it survives every other check, renders plausibly in a diff, and the
    # window in which the author still knows which write did it is minutes long.
    ("check_encoding", "BLOCK", "BOM + undecodable BLOCK; suspected double-encoding WARNS"),
    # ⚠⚠ THE SIX BELOW WERE PUSH-ONLY UNTIL 2026-08-30, AND THAT WAS A HOLE, NOT A SAVING.
    # gitRobot admits 19 keys for a push; this hook recorded 11. The other six ran only in
    # `pre_push`, against the TIP -- so a second commit silently invalidated the first, and no
    # intermediate commit could EVER reach the bar through ordinary work. Measured: a 2-commit
    # range read 11/19 with both commits made through the full pipeline, hook green each time.
    # The remedy on offer was `squash`, i.e. rewriting history on every push to satisfy a rule
    # that exists BECAUSE intermediate commits are fetchable, bisectable and citable forever.
    # ⚠ They already BLOCK at push, so this adds NO new failure class -- same argument
    # `pre_commit` makes for the original five, one paragraph down. Cost 16.1s (~5.9s -> ~22s).
    ("check_paths", "BLOCK", "every repo-relative reference in tracked markdown resolves"),
    ("check_moved", "BLOCK", "nothing points at a path that was relocated"),
    ("check_negatives", "BLOCK", "a universal negative carries a date or a search record"),
    ("check_figures", "BLOCK", "an artifact count carries a date, or is measured on demand"),
    ("check_invariants", "BLOCK", "Engineer's Takes filled; LEAN_CUSTOM_REGISTRY count matches"),
    ("decls", "BLOCK", "every new declaration has #print axioms + an ssot.json row"),
]

PRE_PUSH_PLAN = [
    ("hooks armed", "BLOCK", "the installed hooks match their tracked sources"),
    ("quarantine", "BLOCK", "private/* branches never reach a remote"),
    ("guards", "BLOCK", "every enumerated ROUTE to a guarded property still behaves"),
    ("routing control", "BLOCK", "the behavioural mutation probe: 9 neuters of the routing routes, "
                                 "each required to turn its named ROW red (~225s; fails CLOSED on a "
                                 "moved anchor). Does NOT yet cover RLY28-1 — a tenth mutation is owed"),
    ("check_paths", "BLOCK", "every repo-relative reference in tracked markdown resolves"),
    ("check_claude_md", "BLOCK", "CLAUDE.md shape contract: rooted paths resolve, named checkers exist "
                                 "(3 legs still PENDING — it says so on every run)"),
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


def pre_commit():
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
    os.environ.setdefault("ZPLEDGER_BASIS", "INDEX")
    os.environ.setdefault("ZPLEDGER_RUN", "pre-commit")
    for script in ("check_pov.py", "check_modal.py", "check_classes.py", "check_prose.py",
                   "check_encoding.py",
                   # the six that were push-only until 2026-08-30 — see PRE_COMMIT_PLAN
                   "check_paths.py", "check_moved.py", "check_negatives.py",
                   "check_figures.py", "check_invariants.py"):
        rc = py(script, "--block", "--record")
        # ⚠ EXIT 2 IS "COULD NOT BE RECORDED", NOT "FAILED". A checker that ran and could not reach
        # the ledger produced no key, so the commit must not proceed as though it had — but the
        # reader needs the outage named, not a phantom finding.
        if rc == 2:
            failed.append("%s (ran; verdict NOT RECORDED — no key exists for this content)"
                          % script)
        elif rc != 0:
            failed.append(script)

    # ⚠ `decls` is the sixth of the six, and it is driven separately because it lives in
    #   `batch.py` behind a subcommand rather than being a `check_*.py`. Same exit-2 handling:
    #   "could not be recorded" is not "failed", and neither may be read as the other.
    _rc_decls = py("batch.py", "decls", "--block", "--record")
    if _rc_decls == 2:
        failed.append("decls (ran; verdict NOT RECORDED — no key exists for this content)")
    elif _rc_decls != 0:
        failed.append("decls")

    if failed:
        print("")
        print("Commit blocked — NEW violations in: " + " ".join(failed))
        print("These are baselined checkers, so a hit is a genuinely new site, and each one")
        print("already blocks at push. Fix it now, or ledger it in .claude-local/DEFECTS.md.")
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
    report.plan(PRE_PUSH_PLAN)

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
    os.environ["ZPLEDGER_BASIS"] = "HEAD"
    os.environ["ZPLEDGER_RUN"] = "pre-push"

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
    _rc_probe = py("probe_routing_behavioural.py")
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
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1
    print("===========================")

    print("\n=== CLAUDE.md shape contract ===")
    # ⚠ CALLED WITHOUT `--record`, DELIBERATELY, AND THIS IS DEBT rather than a design choice.
    # The checker has no ledger support yet, and a `--record` flag that accepted the argument
    # while writing nothing would publish a verdict it never earned — the exact shape this
    # pipeline exists to refuse. So it BLOCKS locally and is NOT audited; wiring it into
    # `recorded()` is the follow-up, and until then its verdict leaves no key.
    # ⚠ Its manifest declares 3 PENDING legs on every run. A clear result here is evidence
    # about two legs, never about the shape contract as a whole.
    if py("check_claude_md.py", "--record") != 0:
        print("\nPush blocked: CLAUDE.md names a path or a checker that does not exist.")
        print("Fix the pointer. Body: tools/process/claude-md-maintenance.md.")
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
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1

    if recorded("check_negatives.py", "--block") != 0:
        print("\nPush blocked: an undated universal negative.")
        print("Write 'none located as of <date>, searched as follows' — a universal negative")
        print("is falsified by any single future commit and nothing mechanical notices.")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
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
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1

    # ⚠ scan_pdfs lives in `scripts/`, NOT in this bundle. It is a BUILD-side tool (it checks
    # PDF assets and font registrations), and it moved with the build scripts on 2026-08-15
    # while this call kept looking here. Measured by /rely: `py("scan_pdfs.py") -> 2`, and
    # `pre_push` returns that, so EVERY push exited 2 with a bare [Errno 2] at the end of an
    # otherwise-green run. It failed CLOSED, which is why it is ordinary rather than bedrock —
    # but an unexplained exit 2 on a green run is precisely the shape that trains the
    # `--no-verify` reflex, which this project has already had fire twice.
    scan_exit = run(sys.executable, os.path.join(REPO, "scripts", "scan_pdfs.py"))

    # Routing + review signals, computed from the RANGES BEING PUSHED. This is the one call that
    # `batch.py` could not make correctly on its own (REL-1): it had only the working tree, which
    # is empty post-commit, so coverage was vacuous exactly at push time.
    rc = py("batch.py", "prepush", "--ranges", ",".join(ranges))
    if rc != 0:
        print("\nPush blocked: the pre-push pipeline reported a failure above.")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        # ⚠ This line used to read "This gate is mirrored in CI: a local bypass only defers the
        # block to the PR." That is FALSE and was measured false 2026-08-10: grepping all four
        # workflows for any checker returns nothing — CI runs `lake build`. Telling the operator a
        # backstop exists when it does not is the worst possible failure mode for a deterrent, and
        # the true statement deters harder.
        print("⚠ CI re-runs these checkers on `main` (.github/workflows/verify.yml) but")
        print("  REPORT-ONLY — it publishes findings and does not fail the run. This hook is")
        print("  the last check that STOPS a change; bypassing it ships the change unchecked.")
        return 1

    return scan_exit


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else ""
    try:
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
