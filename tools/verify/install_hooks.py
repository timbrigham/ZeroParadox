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

`--check` is the useful one for a pipeline manifest: it answers "are the gates actually armed?",
which is not the same question as "did the checks pass?" and has never been asked mechanically.
"""
import os
import shutil
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
SELF = os.path.relpath(os.path.abspath(__file__), REPO).replace("\\", "/")

HOOKS = {
    "pre-commit": "proposed_pre_commit_hook.sh",
    "pre-push": "proposed_pre_push_hook.sh",
}


def hook_dir():
    """Resolve .git/hooks, honouring a worktree (.git is a FILE there, not a directory)."""
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


def main(argv):
    force = "--force" in argv
    check = "--check" in argv
    hd = hook_dir()
    if not os.path.isdir(hd):
        if check:
            print("NOT INSTALLED: no hook directory at %s" % hd)
            return 1
        os.makedirs(hd)

    problems = 0
    for name, src_name in sorted(HOOKS.items()):
        src = os.path.join(HERE, src_name)
        dst = os.path.join(hd, name)
        want = open(src, encoding="utf-8").read()
        have = open(dst, encoding="utf-8").read() if os.path.exists(dst) else None

        if check:
            if have is None:
                print("  %-12s NOT INSTALLED" % name)
                problems += 1
            elif have != want:
                print("  %-12s DIFFERS from the tracked source" % name)
                problems += 1
            else:
                print("  %-12s ok" % name)
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


if __name__ == "__main__":
    print("hook install target: %s" % hook_dir())
    sys.exit(main(sys.argv[1:]))
