#!/bin/sh
# THIN SHIM — no pipeline logic lives here.
#
# The shell hooks were retired 2026-08-10 (Tim: "the shell variants are legacy and should be
# retired... just the python version should remain"). There were TWO partial implementations of
# the pipeline, shell and Python, and they measurably disagreed three ways while checking
# disjoint things (PIPE-1). Shell and Python cannot share a module, so one had to go.
#
# Everything lives in tools/verify/hooks.py. Edit THAT; this file must never grow.
#
# The hook SOURCE is now tracked (it moved out of gitignored .claude-local/ on 2026-08-15), so a
# fresh clone can install it without being handed a copy out of band:
#     python tools/verify/install_hooks.py
# The installed hook itself still lives in .git/hooks/ and is still not version-controlled — git
# has no mechanism for that, which is exactly why the installer is the tracked half.
#
# ⚠ Do NOT add `| head`, `| tee` or any early-exiting consumer around this. `git push … | head`
# once bypassed this gate outright: head closed the pipe and the hook died before reaching its
# exit 1. hooks.py ignores SIGPIPE and handles BrokenPipeError for that reason.
exec python tools/verify/hooks.py pre-push
