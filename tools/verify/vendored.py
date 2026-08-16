"""THE definition of the vendored exemption. Import it; never re-implement it.

Third-party code is EXEMPT **STRUCTURALLY, NOT BASELINED**. A baseline entry means "fix later";
this means "never". Tim, 2026-08-08: *"the vendored bucket we shouldn't touch at all, that's a
backport from an official source."* Editing an Apache-2.0 backport's prose also destroys the diff
against upstream, which is the entire point of vendoring it.

TWO signals, and CONTENT IS NOT ONE OF THEM:
  1. the file lives under a `Vendored/` directory;
  2. the file is listed in `vendored_files.txt`.

⚠⚠ **CONTENT SNIFFING WAS REMOVED 2026-08-10 BECAUSE IT WAS A SELF-EXEMPTION HOLE.** A file used to
become exempt by CONTAINING `VENDORED FROM`, `Apache-2.0` or `Upstream:` in its first 30 lines.
Measured by `/rely`, and reproduced: adding one prose line mentioning `Apache-2.0` at the top of
`ZeroParadox/Order/Snap.lean` took a **POV DENIAL** — the one class documented as never baselined —
from `check_pov --block` exit 1 (blocked) to exit 0, and `git commit` then SUCCEEDED. Any file could
opt itself out of all four checkers by mentioning a licence in prose.

The hole was LATENT while only `check_prose` consulted this, and the 2026-08-09 unification across
all five checkers is what made it live. That is the lesson worth keeping: **unifying a rule
propagates its weaknesses as fast as its strengths.** Sharing one definition was still right; the
definition had to be one that cannot be self-asserted.

Only two files were ever exempt — `Vendored/NaturalOps.lean` by directory and
`Ordinal/NaturalOpsPow.lean` by marker — so the entire content mechanism was replaced by one line in
an allowlist.

⚠ Callers should NAME their exempt files in output. `check_prose.py` does. A silent exemption is how
this went unnoticed: three checkers were skipping a file and saying nothing.
"""
import io
import os

BASE = os.path.dirname(os.path.abspath(__file__))
ALLOWLIST = os.path.join(BASE, "vendored_files.txt")

# The ONE vendored directory, anchored at the repository root. Not "any directory called Vendored".
VENDOR_DIR = "zeroparadox/vendored/"


def _allowlist():
    if not os.path.exists(ALLOWLIST):
        return set()
    out = set()
    for line in io.open(ALLOWLIST, encoding="utf-8-sig").read().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            out.add(line.replace("\\", "/").lstrip("./").lower())
    return out


_CACHE = None


def allowlist():
    global _CACHE
    if _CACHE is None:
        _CACHE = _allowlist()
    return _CACHE


def is_vendored(path, rel=None):
    """True when `path` is third-party and must never be edited to satisfy a checker.

    `rel` is the repo-relative path; when omitted, `path` is used. Content is never consulted."""
    rel = str(path) if rel is None else str(rel)
    norm = rel.replace("\\", "/").lstrip("./")
    # ⚠ ANCHORED. `"/Vendored/" in "/" + norm` matched the directory at ANY depth, so creating
    # `ZeroParadox/Order/Vendored/Probe.lean` exempted a file from all four checkers — a POV DENIAL
    # there passed at exit 0 while the identical file in an ordinary directory exited 1. That is the
    # same self-exemption as the content marker (RLY2-1), reached through the path instead, and it
    # survived the first fix. Found by /rely pass 2. Only the one canonical directory counts;
    # anything else needs an explicit allowlist line, which is a reviewable act.
    if norm.lower().startswith(VENDOR_DIR.lower()):
        return True
    return norm.lower() in allowlist()


# --------------------------------------------------------------------------- controls
# ⚠ **THIS MODULE WAS AUDITED BY NOTHING** (`VEND-1`, `/rely` round 4): no `--selftest`, not matched
# by the `check_*.py` glob, absent from `check_checkers.ALSO_AUDITED` and from
# `ci_report.SELFTESTS`. It is the SINGLE DEFINITION of the exemption surface that all four gating
# checkers import — precisely the trigger `check_checkers.py`'s own header states, *"add a module the
# moment other gates depend on it, whatever its filename"*.
#
# ⚠ Third instance of the `COM-1` / `DEB-1` class, and the one that shows why a roster reconciliation
# is not enough: `roster_agrees()` is STRUCTURALLY BLIND here, because both rosters omit this file
# identically and agreeing on an omission is still agreement.
#
# The PROPERTY was defended even while the module was unaudited — mutating `is_vendored` to exempt
# every `.lean` file is caught independently by `check_checkers --block` and by `guards --block`.
# What was missing is the demonstration that this file itself can fail.
MUST_FIRE = [                       # these MUST be reported vendored
    ("the canonical directory", "ZeroParadox/Vendored/NaturalOps.lean"),
    ("windows separators", r"ZeroParadox\Vendored\NaturalOps.lean"),
    ("a leading ./", "./ZeroParadox/Vendored/NaturalOps.lean"),
    ("case-insensitively", "zeroparadox/vendored/naturalops.lean"),
    ("an explicit allowlist line", "ZeroParadox/Ordinal/NaturalOpsPow.lean"),
]
MUST_SUPPRESS = [                   # these must NOT be exempt
    ("an ordinary corpus file", "ZeroParadox/Order/Snap.lean"),
    # ⚠ THE ANCHORING REGRESSION. A nested `Vendored/` exempted a file from all four checkers and
    # survived the first fix (RLY2-1's sibling, found by /rely pass 2). If someone un-anchors the
    # test, this control fails rather than the hole silently reopening.
    ("a NESTED Vendored directory", "ZeroParadox/Order/Vendored/Probe.lean"),
    ("a checker itself", "tools/verify/check_pov.py"),
    # ⚠ CONTENT IS NEVER CONSULTED. Until 2026-08-10 a file exempted itself by CONTAINING
    # `Apache-2.0` or `VENDORED FROM` in its head — RLY2-1, logged BEDROCK. This control is what
    # stops that being reintroduced as a convenience.
    ("a file merely NAMING a licence", "ZeroParadox/Order/Apache-2.0-notes.lean"),
]


def selftest():
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import common
    bad = common.fire_suppress(MUST_FIRE, MUST_SUPPRESS,
                               lambda rel: is_vendored(rel), 'a vendored exemption', width=34)
    print('PATTERNS')
    bad += common.check_vocabulary('vendored', globals())
    if bad:
        print('\nselftest: FAIL (%d)' % bad)
    return 1 if bad else 0


if __name__ == '__main__':
    import sys
    if '--selftest' in sys.argv:
        sys.exit(selftest())
    print('%s — THE definition of the vendored exemption. Import it; never re-implement it.'
          % os.path.relpath(os.path.abspath(__file__),
                            os.path.dirname(os.path.dirname(os.path.dirname(
                                os.path.abspath(__file__))))).replace('\\', '/'))
    print('  exempt directory : %s' % VENDOR_DIR)
    print('  allowlist        : %s' % (', '.join(sorted(allowlist())) or '(empty)'))
    print('\n  --selftest   run this module\'s own controls')
