"""Install the tracked hook shims into .git/hooks/.

WHY THIS EXISTS. Git hooks live in `.git/hooks/`, which git does not and cannot version, so every
clone starts with no gates at all. Until 2026-08-15 the hook SOURCES were also untracked — they sat
in gitignored `.claude-local/` — so "reinstall per clone" meant copying a file that a fresh clone
did not have. CLAUDE.md flags that hazard in three separate places, and a missing reinstall is
silent: pushes simply stop being checked, and nothing says so.

Tracking the sources fixes the half that can be fixed. This script is the other half.

    python tools/verify/install_hooks.py            # install (refuses to clobber a modified hook)
    python tools/verify/install_hooks.py --force    # overwrite whatever is there
    python tools/verify/install_hooks.py --check    # report only; exit 1 if not correctly installed
    python tools/verify/install_hooks.py --selftest # controls, both directions

`--check` is the useful one for a pipeline manifest: it answers "are the gates actually armed?",
which is not the same question as "did the checks pass?".

ARMED MEANS THREE THINGS, AND EQUALITY IS ONLY ONE (HOOK-R5-1). Byte-equality with the tracked
source cannot see a GUTTED source: replace both shims with `exit 0`, install, and the copies still
match. So `--check` also asserts, of the installed body AND of the tracked source, that the shim's
only executable line is `exec python tools/verify/hooks.py <its own phase>`, and that `hooks.py`
exists for it to reach. The install refuses to copy a source that fails that test. What this file
does NOT check: the Claude Code PreToolUse registration in `.claude/settings.json` - a different
mechanism with its own owner; `claude_hooks/test_block_git_gh.ps1` measures that registration.
"""
import os
import re
import shutil
import tempfile
import subprocess
import sys

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
SELF = common.self_rel(__file__)

HOOKS = {
    "pre-commit": "proposed_pre_commit_hook.sh",
    "pre-push": "proposed_pre_push_hook.sh",
}

# The shim's one executable line. Comments and the shebang are not code; anything else is.
ARM_LINE = re.compile(r'^exec\s+python3?\s+tools/verify/hooks\.py\s+(?P<phase>[\w-]+)(?:\s+"\$@")?\s*$')


def not_armed(body, phase):
    """Why `body` does not arm `phase`, or None when it does.

    The shim is exactly one `exec python tools/verify/hooks.py <phase>` and nothing else - its own
    header says it "must never grow" - so ANY second executable line is a reason, not a tolerance:
    an `exit 0` above the exec arms nothing while still containing the right words."""
    code = [ln.strip() for ln in body.splitlines()]
    code = [ln for ln in code if ln and not ln.startswith("#")]
    if not code:
        return "no executable line"
    if len(code) != 1:
        return "%d executable lines (the shim is exactly one exec); first is %r" % (len(code), code[0][:60])
    m = ARM_LINE.match(code[0])
    if not m:
        return "its executable line does not exec hooks.py: %r" % code[0][:60]
    if m.group("phase") != phase:
        return "it runs hooks.py %s, not %s" % (m.group("phase"), phase)
    if not os.path.isfile(os.path.join(HERE, "hooks.py")):
        return "tools/verify/hooks.py, which it execs, does not exist"
    return None


def hook_dir():
    """Resolve the directory git ACTUALLY runs hooks from.

    ⚠⚠ `core.hooksPath` FIRST, AND IT IS CONFIGURED IN THIS REPO. Until 2026-08-30 this resolved
    `.git/hooks` unconditionally and never consulted it, which made `--check` a proxy for "are the
    gates armed" rather than a measurement of it. `/rely` RLY27-2 built the tree: both correct
    shims in the DEFAULT hook directory, `hooksPath` pointed at an EMPTY directory, and `--check`
    printed `pre-commit ok / pre-push ok`, exit 0, over a repository where no hook could fire.
    The reachable fail-open is worse than the demo: point `hooksPath` at a directory holding a
    correct `pre-push` and no `pre-commit`, and the push gate runs, this row passes, and every
    commit is ungated. Ask git where it looks; do not assume the default.
    """
    out = subprocess.run(['git', 'config', '--get', 'core.hooksPath'], cwd=str(REPO),
                         capture_output=True, text=True)
    if out.returncode == 0 and out.stdout.strip():
        hp = out.stdout.strip()
        return hp if os.path.isabs(hp) else os.path.normpath(os.path.join(REPO, hp))
    # No override configured: resolve .git/hooks, honouring a worktree (.git is a FILE there).
    dotgit = os.path.join(REPO, ".git")
    if os.path.isfile(dotgit):
        with open(dotgit, encoding="utf-8") as f:
            for line in f:
                if line.startswith("gitdir:"):
                    gitdir = line.split(":", 1)[1].strip()
                    if not os.path.isabs(gitdir):
                        gitdir = os.path.normpath(os.path.join(REPO, gitdir))
                    # A worktree's gitdir points at .git/worktrees/<name>; hooks are shared
                    # from the main .git, so walk back up to it.
                    parts = gitdir.replace("\\", "/").split("/")
                    if "worktrees" in parts:
                        gitdir = "/".join(parts[:parts.index("worktrees")])
                    return os.path.join(gitdir, "hooks")
    return os.path.join(dotgit, "hooks")


def main(argv, hd=None, src_dir=None):
    force = "--force" in argv
    check = "--check" in argv
    hd = hd or hook_dir()
    src_dir = src_dir or HERE
    if not os.path.isdir(hd):
        if check:
            print("NOT INSTALLED: no hook directory at %s" % hd)
            return 1
        os.makedirs(hd)

    problems = 0
    for name, src_name in sorted(HOOKS.items()):
        src = os.path.join(src_dir, src_name)
        dst = os.path.join(hd, name)
        want = open(src, encoding="utf-8").read()
        have = open(dst, encoding="utf-8").read() if os.path.exists(dst) else None
        src_why = not_armed(want, name)

        if check:
            if have is None:
                print("  %-12s NOT INSTALLED" % name)
                problems += 1
            elif have != want:
                print("  %-12s DIFFERS from the tracked source" % name)
                problems += 1
            have_why = not_armed(have, name) if have is not None else None
            if have_why:
                print("  %-12s NOT ARMED (installed): %s" % (name, have_why))
                problems += 1
            if src_why:
                print("  %-12s NOT ARMED (tracked source %s): %s" % (name, src_name, src_why))
                problems += 1
            if have is not None and have == want and not have_why and not src_why:
                print("  %-12s ok" % name)
            continue

        if src_why:
            # Installing a gutted source would report "installed" over a hook that does nothing.
            print("  %-12s NOT INSTALLED - the tracked source does not arm it: %s" % (name, src_why))
            problems += 1
            continue
        if have == want:
            print("  %-12s already current" % name)
            continue
        if have is not None and not force:
            # Refuse rather than clobber: a hand-modified hook may be someone's deliberate local
            # change, and silently replacing it is the same class of harm as a silent gate bypass.
            print("  %-12s EXISTS and differs - not overwriting. Re-run with --force to replace."
                  % name)
            problems += 1
            continue
        shutil.copyfile(src, dst)
        # chmod is a no-op on Windows and required everywhere else.
        try:
            os.chmod(dst, 0o755)
        except OSError:
            pass
        print("  %-12s installed" % name)

    if check and problems:
        print("\nThe gates are NOT armed. Install with:  python %s" % SELF)
    return 1 if problems else 0


def selftest():
    """Controls, both directions. Must FIRE on a disarmed tree that `--check` used to pass; must
    SUPPRESS on the tracked shims installed as-is. Runs in a temp directory - never .git/hooks."""
    import contextlib
    import io
    fired = suppressed = failed = 0

    def run_check(src_bodies, installed_bodies):
        with tempfile.TemporaryDirectory() as tmp:
            sd, hd = os.path.join(tmp, "src"), os.path.join(tmp, "hooks")
            os.makedirs(sd)
            os.makedirs(hd)
            for name, src_name in HOOKS.items():
                with open(os.path.join(sd, src_name), "w", encoding="utf-8") as f:
                    f.write(src_bodies[name])
                if installed_bodies.get(name) is not None:
                    with open(os.path.join(hd, name), "w", encoding="utf-8") as f:
                        f.write(installed_bodies[name])
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = main(["--check"], hd=hd, src_dir=sd)
            return rc, buf.getvalue()

    real = {n: open(os.path.join(HERE, s), encoding="utf-8").read() for n, s in HOOKS.items()}
    gutted = {n: "#!/bin/sh\nexit 0\n" for n in HOOKS}
    exit_first = {n: "#!/bin/sh\nexit 0\nexec python tools/verify/hooks.py %s\n" % n for n in HOOKS}
    swapped = {"pre-commit": real["pre-push"], "pre-push": real["pre-commit"]}

    cases = [
        # (label, sources, installed, want_rc, message the guard must print)
        ("HOOK-R5-1 repro: both gutted, both equal", gutted, gutted, 1, "NOT ARMED (installed)"),
        ("gutted source, gutted install: source named", gutted, gutted, 1, "NOT ARMED (tracked source"),
        ("exit 0 above the exec", exit_first, exit_first, 1, "2 executable lines"),
        ("phases swapped", swapped, swapped, 1, "runs hooks.py pre-push, not pre-commit"),
        ("real sources, nothing installed", real, {}, 1, "NOT INSTALLED"),
        ("real sources installed as-is", real, real, 0, "ok"),
    ]
    for label, srcs, inst, want_rc, msg in cases:
        rc, out = run_check(srcs, inst)
        ok = rc == want_rc and msg in out
        if want_rc == 0:
            ok = ok and "NOT" not in out
            suppressed += ok
        else:
            fired += ok
        failed += not ok
        print("    %-46s %s" % (label, "ok" if ok else "*** WRONG *** rc=%d\n%s" % (rc, out)))
    # The unit itself, on the tracked shims: each arms its own phase and not the other one.
    for name in HOOKS:
        ok = not_armed(real[name], name) is None
        other = [p for p in HOOKS if p != name][0]
        ok2 = not_armed(real[name], other) is not None
        suppressed += ok
        fired += ok2
        failed += (not ok) + (not ok2)
        print("    %-46s %s" % ("tracked %s arms %s, not %s" % (name, name, other),
                                  "ok" if ok and ok2 else "*** WRONG ***"))
    print("selftest: %s (fires on %d, suppresses %d)" % ("PASS" if not failed else "FAIL", fired, suppressed))
    return 0 if not failed else 1


if __name__ == "__main__":
    if "--selftest" in sys.argv[1:]:
        sys.exit(selftest())
    print("hook install target: %s" % hook_dir())
    sys.exit(main(sys.argv[1:]))
