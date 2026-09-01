"""How the pipeline ANNOUNCES ITSELF. One formatter, used by every entry point.

WHY (Tim, 2026-08-10): *"update the process so that when we run the pipeline in the future this is
the default behavior."* Every entry point must state, before it does anything, **what it is about to
run and with what parameters** — which checks, in what order, which of them BLOCK and which only
warn, and what scope they are being applied to.

**This is not cosmetic.** Three defects this month were invisible precisely because the pipeline did
not say what it was doing:
  * `check_modal --block` had never blocked a push — the output looked identical either way, because
    nothing announced which checks were load-bearing (HK-1);
  * `check_poles` sat in the checker list gating nothing, while `precommit` printed `suite ok`, so
    "all five checkers at zero new" was a claim only four could make (REL-3);
  * three checkers silently skipped a file they judged vendored, and `check_prose` was the only one
    that named its exemptions — which is how a self-exemption hole went unnoticed (RLY2-1).

A gate that does not declare its own scope and enforcement mode cannot be audited by reading its
output, and this project's measured lesson is that **anything not declared is eventually assumed.**

Used by `hooks.py` (pre-commit, pre-push) and `batch.py` (precommit, prepush). One definition, so
the four cannot drift into describing themselves differently.
"""
import sys

# The Windows console defaults to a legacy code page, so an em-dash arrives as a replacement
# character. `batch.py` already did this for itself; `hooks.py` did not, and the mangling showed up
# the first time the banners ran. Doing it HERE means every entry point inherits it by importing the
# formatter — one more thing that cannot drift between them.
try:
    # line_buffering is as load-bearing as the encoding. These entry points interleave their own
    # output with child processes that write straight to the terminal fd; block-buffered Python
    # output therefore arrives AFTER children that ran later, so the log reads in the wrong order
    # and a section header lands under the section below it. Measured both ways here.
    sys.stdout.reconfigure(encoding="utf-8", line_buffering=True)
except Exception:
    pass

W = 78


def _w(s=""):
    """Write AND FLUSH.

    ⚠ The flush is load-bearing, not tidiness. These entry points spawn child processes that write
    straight to the terminal fd, while Python's own stdout is block-buffered when piped — so without
    an explicit flush the banner announcing what is about to run appears AFTER everything it
    announced. Measured the first time this ran: the pre-commit manifest was nowhere in the first 22
    lines of output."""
    try:
        sys.stdout.write(s + "\n")
        sys.stdout.flush()
    except BrokenPipeError:
        raise
    except Exception:
        pass


def banner(title, meta):
    """Header: what is running, and the parameters it is running under.

    `meta` is a list of (label, value); a value may be a list, printed one per line."""
    _w("")
    _w("=" * W)
    _w("  %s" % title.upper())
    _w("=" * W)
    for label, value in meta:
        if isinstance(value, (list, tuple)):
            if not value:
                _w("  %-10s (none)" % label)
                continue
            _w("  %-10s %s" % (label, value[0]))
            for extra in value[1:]:
                _w("  %-10s %s" % ("", extra))
        else:
            _w("  %-10s %s" % (label, value))


def plan(stages):
    """The ordered list of checks, each with its ENFORCEMENT MODE and what it enforces.

    `stages` is a list of (name, mode, what). `mode` is 'BLOCK', 'warn' or 'report' — stating it per
    stage is the point: a reader must never have to infer whether a check can actually stop them."""
    blocking = sum(1 for _n, m, _w2 in stages if m == "BLOCK")
    _w("  %-10s %d check(s): %d BLOCK, %d advisory"
       % ("plan", len(stages), blocking, len(stages) - blocking))
    for i, (name, mode, what) in enumerate(stages, 1):
        _w("     %2d. %-22s %-6s %s" % (i, name, mode, what))
    _w("=" * W)


def done(title, ok, detail=""):
    _w("")
    _w("%s  %s%s" % ("=" * 4, title.upper(), (" — " + detail) if detail else ""))
    _w("  %s" % ("PASS" if ok else "BLOCKED"))
    _w("=" * W)
