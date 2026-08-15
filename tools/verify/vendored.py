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
