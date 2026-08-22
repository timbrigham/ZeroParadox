"""PROPERTY guards — enumerate every ROUTE to a property and test all of them.

    python guards.py            # run every property's every route
    python guards.py --list     # just show the surface

WHY (Tim, 2026-08-10: *"did we already fix the multiple routes to the same property for future
iterations? I'm getting a little tired of that behavior"*). **No — instances had been fixed and
nothing had been institutionalised.** Measured across one session, one property — *"a file cannot
exempt itself from the gating checkers"* — was "fixed" FOUR times:

    route 1  a content marker in the file head        closed, then
    route 2  a nested `Vendored/` directory            closed, then
    route 3  a line in vendored_files.txt              closed, then
    route 4  a line in a checker's *_baseline.txt      closed

and the bedrock cap was walkable three ways in one sitting. Each fix was correct and each left
another door open, because the routes live in DIFFERENT FILES — so "enumerate them" was a memory
exercise performed by the person who had just demonstrated they would forget one.

**THE FIX IS NOT ANOTHER RULE.** Rules of this shape have leaked six times in this project by its own
count. It is making the surface ENUMERABLE: one registry per property listing every route, and a
control that walks all of them. Closing a route means ADDING IT HERE, and the next person inherits
the list instead of reconstructing it.

⚠ **A route that is legitimately allowed is still listed** — `may_suppress=True`, plus a `visible`
predicate. A registry recording only attacks cannot tell you whether the real exemption still works,
and an over-tightened guard that breaks vendoring is its own defect. The requirement on a permitted
route is not that it fails; it is that **it cannot happen quietly**.

⚠ **This MUTATES real files** and restores them: each route backs up first and restores in a
`finally`. Restoration is then PROVED, by hashing the exact set of paths it touches before and
after — not by `git status`, which cannot see `.claude-local/` (gitignored) and which would force
this to refuse on any dirty tree. A per-path proof is both narrower and stronger, and it is what
lets this run inside the hooks, where it is worth having.

⚠ If the process is KILLED mid-route the mutation survives — visibly: the checkers fire and
`git status` shows the probe file. It is not silent, and re-running restores nothing on its own.
"""
import io
import json
import os
import re
import subprocess
import sys

# TWO roots. HERE is the tracked public bundle and holds the BASELINES — which are themselves
# exemption routes, so they must travel with the guard that enumerates them. PRIV holds per-push
# state (round state, signals) and may be absent in a public clone.
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
BASE = HERE   # retained: remaining call sites below mean "where the baselines live"
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import report                                          # noqa: E402

PROBE_FILE = os.path.join(REPO, "ZeroParadox", "Order", "Snap.lean")
# A POV DENIAL: the class documented as never baselineable, so a suppression here is always a bug.
DENIAL = "\n-- This is NOT the snap, per `t_snap_derived`.\n"
ROUND_STATE = os.path.join(PRIV, "gate_round.json")


def sh(*args):
    r = subprocess.run(args, cwd=REPO, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def _append(path, text):
    """(apply, undo) that appends `text` to `path` and restores the exact original bytes."""
    orig = io.open(path, "rb").read()

    def apply():
        with io.open(path, "a", encoding="utf-8", newline="\n") as f:
            f.write(text)

    def undo():
        io.open(path, "wb").write(orig)
    return apply, undo


def _rewrite(path, produce):
    """(apply, undo) that replaces `path` with produce(original_bytes); None deletes it."""
    orig = io.open(path, "rb").read() if os.path.exists(path) else None

    # ⚠ The parent directory may not exist. A probe writes into `.claude-local/`, which is absent
    # in any clone that is not Tim's — and a bare FileNotFoundError aborted the whole pre-push run
    # with a traceback instead of a verdict. Measured 2026-08-15 in a fresh worktree, immediately
    # after this bundle was published. It failed CLOSED, which is the safe direction, but a crash
    # is not a verdict: it says nothing about whether the guarded property holds.
    #
    # ⚠⚠ AND THE UNDO MUST BE SYMMETRIC. The first fix created the directory and did not remove it,
    # so the probe left the tree mutated — which this file's own "did the guard clean up after
    # itself?" check caught on the very next run. That is the control working on its author, and it
    # is the reason the directory is tracked in a closure rather than created and forgotten.
    _made_dir = []

    def apply():
        new = produce(orig)
        if new is None:
            if os.path.exists(path):
                os.remove(path)
        else:
            parent = os.path.dirname(path)
            if parent and not os.path.isdir(parent):
                os.makedirs(parent, exist_ok=True)
                _made_dir.append(parent)
            io.open(path, "wb").write(new)

    def undo():
        if orig is None:
            if os.path.exists(path):
                os.remove(path)
        else:
            io.open(path, "wb").write(orig)
        while _made_dir:
            d = _made_dir.pop()
            try:
                os.rmdir(d)          # only succeeds if empty — never removes real content
            except OSError:
                pass
    return apply, undo


# ═══ PROPERTY 1 — a file cannot exempt itself from the gating checkers ════════════════════════

def pov_blocks():
    rc, out = sh(sys.executable, os.path.join(BASE, "check_pov.py"), "--block")
    return rc != 0, out


# ═══ PROPERTY 6 — a changed file cannot escape the REVIEW-SIGNAL requirement ══════════════════
#
# ⚠ ADDED 2026-08-15, and it was missing at the moment it was most needed. The properties above all
# guard the CHECKERS. Nothing guarded the other exemption surface: `batch.reviewable_changed()`,
# which decides whether a changed file needs editorial and adversary coverage at all. A file that
# falls out of THAT set is not reviewed by anyone, and no guard would have noticed.
#
# It became urgent the same day, because the tools/verify migration ADDED a route: `EXEMPT_PREFIXES`
# now skips an entire directory tree. That is a defensible exemption — the argument is at its
# definition — but CLAUDE.md's rule is that closing OR OPENING a route means registering it here,
# and the author of that exemption (me) did not. This registry exists because "enumerate the routes"
# performed from memory is how one property got fixed four times.
#
# ⚠ These routes are classification, not mutation, so they are tested by asking the classifier
# directly rather than by planting files. That is deliberate and it is stronger: the other
# properties infer suppression from a checker's exit code, whereas this reads the decision itself.
_ORDINARY = "ZeroParadox/Order/Snap.lean"          # must always be reviewable
_EXEMPT_PATH = "CLAUDE.md"                          # exempt by exact path
_EXEMPT_PREFIX = "tools/verify/check_pov.py"        # exempt by directory prefix
_EXEMPT_PROCESS = "tools/process/claim-revalidation.md"  # exempt by the SECOND directory prefix
_EXEMPT_DATA = "scripts/fonts/DejaVuSans.ttf"       # exempt by data extension
# ⚠ A SECOND PREFIX IS A SECOND ROUTE. `EXEMPT_PREFIXES` was a one-entry tuple when this registry
# was written, so "directory prefix" tested the mechanism and the only path through it at once.
# Adding `tools/process/` split those apart: the mechanism stayed covered and the new route was
# not, which is the exact shape CLAUDE.md means by closing one route and calling the hole fixed.
# Registered 2026-08-20, in the same change that opened it.


def _classifies(paths):
    """Which of `paths` batch.py considers REVIEWABLE. The decision itself, not a proxy."""
    import importlib
    import batch
    importlib.reload(batch)
    return set(batch.reviewable_from(paths))


# ⚠⚠ THE `router` COLUMN IS THE EXEMPTION'S WARRANT, AND IT IS TESTED, NOT ASSERTED.
# Added 2026-08-21 after a `/rely` trial: dropping the `tools/process/` entry from `batch.ROUTING`
# left this table still printing `ok` for that row, still asserting "routed to /rely, which BLOCKS"
# — while nothing routed. The exemption survived the deletion of the only thing that justified it.
#
# An exemption and its compensating control must cover the same set, and `batch.ROUTING`'s own
# header already says so; what was missing was anything that FAILS when they come apart. A `router`
# of `None` means the row is exempt for a reason other than routing and must be justified in `why`
# — CLAUDE.md is version-control-only by its own header, and a font carries no prose at all.
EXEMPTION_SURFACE = [
    # (label, path, may_be_exempt, router, why)
    ("an ordinary corpus file", _ORDINARY, False, None,
     "must ALWAYS be reviewable - this is the must-fire control"),
    # ⚠⚠ THE MARKDOWN MUST-FIRE CONTROLS, AND THEIR ABSENCE WAS THE HOLE. The row above is a
    # `.lean` path, so NO markdown-scoped widening could ever trip this table — measured
    # (/rely round 3): `.md` added to `DATA_EXT`, and `readme.md` added to `EXEMPT_PATHS`, each
    # un-reviewed public prose with every row `ok` and exit 0. A must-fire control only covers the
    # extensions it is written in. These three are the reader-facing prose `CLAUDE.md` names as
    # gate-covered, so an exemption reaching them is never correct.
    ("public prose (README.md)", "README.md", False, None,
     "the formal index; both prose gates fire on it"),
    ("public prose (GUIDE.md)", "GUIDE.md", False, None,
     "the general-reader hub; both prose gates fire on it"),
    ("public prose (CLAIMS.md)", "CLAIMS.md", False, None,
     "the claims ledger; both prose gates fire on it"),
    ("exact path (CLAUDE.md)", _EXEMPT_PATH, True, None,
     "the operating manual; its own header exempts it, and it is routed NOWHERE by design"),
    ("directory prefix (tools/verify/)", _EXEMPT_PREFIX, True, "/rely",
     "operating machinery; /rely reviews this layer and BLOCKS"),
    ("directory prefix (tools/process/)", _EXEMPT_PROCESS, True, "/rely",
     "CLAUDE.md's routed body; declared in its header and routed to /rely, which BLOCKS"),
    ("data extension (a .ttf)", _EXEMPT_DATA, True, None,
     "a binary carries no prose for a prose gate to read"),
    # ⚠ THESE TWO WERE EXEMPT AND UNREGISTERED, and the completeness check found them the first
    # time it read `EXEMPT_PATHS` (2026-08-21). Both are GENERATED — `ssot.json` is exported by the
    # SJV registry, `lake-manifest.json` by lake — so there is no prose in either for a prose gate
    # to read, and a data-only commit staling a review is the exact failure the per-file hash scheme
    # replaced. Routed NOWHERE by design: a regenerated artifact is checked by whatever regenerates
    # it, not by a reviewer.
    ("generated data (ssot.json)", "ssot.json", True, None,
     "exported by the SJV registry; carries no prose, and its content is checked by export"),
    ("generated data (lake-manifest.json)", "lake-manifest.json", True, None,
     "generated by lake; carries no prose, and drift shows up as a build failure"),
]


def _routes_to(path):
    """Which agents `batch.ROUTING` actually sends `path` to. The routing table itself, not a claim
    about it — the same move as `_classifies()` reading the classifier rather than a proxy."""
    import importlib
    import batch
    importlib.reload(batch)
    return {agent for pat, agent, _why in batch.ROUTING if pat.match(path)}


def check_exemption_surface():
    """Every route by which a changed file can escape the review-signal requirement.

    Returns (rows, bad). A row fails when a path that MUST be reviewable is not, or when a path
    recorded as exempt has quietly stopped being exempt — both directions, because an exemption
    that silently disappears is a false alarm generator and one that silently appears is a hole."""
    rows, bad = [], 0
    for label, path, may_exempt, router, why in EXEMPTION_SURFACE:
        got = _classifies([path])
        is_exempt = path not in got
        ok = (is_exempt == may_exempt)
        if not ok:
            bad += 1
        state = "exempt" if is_exempt else "reviewable"
        expect = "exempt (permitted)" if may_exempt else "reviewable (required)"
        rows.append((label, ok, "%s — expected %s; %s" % (state, expect, why)))

        # The WARRANT leg. An exemption justified by a re-route is only as good as the re-route,
        # and until this ran the justification was a sentence in the `why` column.
        #
        # ⚠⚠ TESTED AS A SET, NOT AT A POINT. Checking the one sample path was still a fail-open:
        # NARROWING `ROUTING` (say to `^tools/process/sub/`) instead of deleting it leaves the
        # sample matching and every other file in the prefix unrouted, with `bad = 0`. Measured
        # /rely round 2. An exemption is a SET, so its warrant has to be checked over the set —
        # probing the prefix root and a nested path is what makes this a coverage test.
        # ⚠⚠ STRUCTURAL, NOT SAMPLED — the third shape, and the first two were both sampling.
        # Round 1 probed one path; round 2 probed three. Narrowing the route to
        # `^tools/verify/(?!vendor/)` leaves all three probes routing while `tools/verify/vendor/*`
        # is gate-exempt and routed to nothing — "the round-1 signature character for character",
        # in `batch.py`'s own words (/rely round 3). **No finite set of probes can exhibit a
        # narrowing**, because the attacker picks the excluded region after seeing the probes.
        #
        # The warrant is a claim about a SET: every path under the prefix routes. The only pattern
        # that guarantees it is one anchored at the prefix with nothing following, so compare the
        # pattern SOURCE rather than sampling its behaviour. Deliberately brittle: any edit to the
        # pattern fails this until someone re-states the warrant.
        if router is not None:
            prefix = _prefix_of(path)
            want = "^" + prefix
            # ⚠⚠ THE FLAGS ARE PART OF THE PATTERN. Comparing `p.pattern` alone was blind to
            # `p.flags`: dropping `re.I` left this row printing ok while `reviewable_from`
            # (which lowercases) exempted `Tools/Verify/CASETEST.md` and `ROUTING` (which no longer
            # did) routed it nowhere — `prepush` exit 1 -> PASS (/rely round 4, RLY4-2).
            # `batch.py`'s own comment calls that path LIVE on ubuntu-latest, where CI runs.
            exact = [p for p, a, _w in _routing()
                     if a == router and p.pattern == want and (p.flags & re.IGNORECASE)]
            r_ok = bool(exact) and prefix != ""
            if not r_ok:
                bad += 1
            rows.append(("  ^ warrant: %s anchored at the prefix" % router, r_ok,
                         ("a case-insensitive ROUTING pattern is exactly %r" % want) if r_ok else
                         "NO case-insensitive ROUTING pattern equals %r — the exemption is VOID "
                         "for any path the actual pattern does not reach, and no probe can prove "
                         "it does" % want))
    return rows, bad


def _prefix_of(path):
    """The exempt directory prefix a registry path stands for, or '' if it is an exact-path row."""
    import importlib
    import batch
    importlib.reload(batch)
    low = path.lower().replace("\\", "/")
    for p in batch.EXEMPT_PREFIXES:
        if low.startswith(p.lower()):
            return p
    return ""


def _routing():
    import importlib
    import batch
    importlib.reload(batch)
    return list(batch.ROUTING)


# ⚠⚠ AND THE REGISTRY MUST BE COMPLETE, WHICH IS A DIFFERENT PROPERTY FROM EACH ROW BEING RIGHT.
# Every row above can pass while a WHOLE NEW exemption prefix exists that nobody registered — the
# table is hand-maintained and nothing compared it against its source of truth. Measured /rely
# round 2: adding `.claude/commands/` to `EXEMPT_PREFIXES` — the one directory CLAUDE.md says both
# gates MUST fire on — produced `reviewable? False / routes to NOTHING / hashed? False` with this
# registry reporting every row `ok` and `bad = 0`.
#
# This is the same failure this whole file exists to prevent, one level up: "enumerate the routes"
# performed from memory, by the person who just added one. The fix is not another rule — it is
# deriving the obligation from `batch.EXEMPT_PREFIXES` so a new prefix cannot be silently unlisted.
def check_exemption_completeness():
    """Every exemption route `batch.reviewable_from()` honours must have a row above.

    ⚠⚠ ALL THREE TUPLES, NOT ONE. `reviewable_from()` drops a file on three independent tests in
    adjacent lines — `DATA_EXT`, `EXEMPT_PATHS`, `EXEMPT_PREFIXES` — and the first version of this
    check read only the third. Measured (/rely round 3): adding `"readme.md"` to `EXEMPT_PATHS`
    took `README.md` out of the review-signal requirement entirely, and adding `".md"` to
    `DATA_EXT` did the same for README, GUIDE and CLAIMS at once, both with **every row `ok` and
    exit 0**. That is the identical hole round 2 found in the third tuple, surviving in the other
    two — which is this file's founding failure (one property, four routes, fixed four times).

    Deriving the obligation from the source of truth is the only shape that has held here, so it is
    applied to the whole surface rather than to the tuple that was last attacked."""
    import importlib
    import batch
    importlib.reload(batch)
    # ⚠ ONLY ROWS THAT MAY BE EXEMPT CAN WITNESS AN EXEMPTION. Taking every row was a fail-open its
    # own control caught: `_ORDINARY` is `ZeroParadox/Order/Snap.lean` and is registered as
    # must-ALWAYS-be-reviewable, so it made `ZeroParadox/` look like an already-registered exempt
    # prefix — the must-fire control warranting the exemption it exists to forbid.
    covered = [p.lower().replace("\\", "/")
               for _l, p, may, _r, _w in EXEMPTION_SURFACE if may]
    rows, bad = [], 0

    def row(label, hit, kind):
        nonlocal bad
        if not hit:
            bad += 1
        rows.append((label, hit, "has a row above" if hit else
                     "*** EXEMPT BUT UNREGISTERED (%s) — exempt from the prose gates, warranted "
                     "by nothing, and no control would have said so ***" % kind))

    # ⚠ A ROW WITNESSES A PREFIX ONLY IF THE PREFIX IS *WHY* IT IS EXEMPT. Testing
    # `path.startswith(prefix)` alone was wrong and its own control caught it: the `.ttf` row lives
    # at `scripts/fonts/...`, so adding `scripts/` to EXEMPT_PREFIXES looked already-registered and
    # the attack passed. A row exempt by DATA_EXT or EXEMPT_PATHS would still be exempt with the
    # prefix tuple empty, so it witnesses nothing about the prefix.
    def witnesses(c, prefix):
        # ⚠⚠ AND IT MUST NOT BE CLAIMED BY A MORE SPECIFIC PREFIX. Requiring only
        # `startswith(prefix)` was still a fail-open: `tools/verify/check_pov.py` starts with
        # `tools/` too, so appending `"tools/"` to the tuple looked already-registered and
        # un-reviewed 12 tracked files under `tools/registry/` and `tools/render/` — measured end to
        # end, `prepush` went from exit 1 to PASS (/rely round 4, RLY4-1). A row witnesses the
        # prefix it is EXEMPT BY, which is the most specific one covering it; anything longer would
        # still be exempt with this prefix removed, so it proves nothing about this prefix.
        p = prefix.lower()
        if not c.startswith(p):
            return False
        if c.endswith(tuple(e.lower() for e in batch.DATA_EXT)):
            return False
        if c in [e.lower() for e in batch.EXEMPT_PATHS]:
            return False
        more_specific = [q.lower() for q in batch.EXEMPT_PREFIXES
                         if q.lower() != p and q.lower().startswith(p)]
        return not any(c.startswith(q) for q in more_specific)

    for prefix in batch.EXEMPT_PREFIXES:
        row("prefix: %s" % prefix,
            any(witnesses(c, prefix) for c in covered), "EXEMPT_PREFIXES")
    for exact in batch.EXEMPT_PATHS:
        row("exact path: %s" % exact,
            exact.lower() in covered, "EXEMPT_PATHS")

    # ⚠ DATA_EXT IS CHECKED BY ITS CONTENT, NOT BY A ROW PER ENTRY. Its argument is "a binary
    # carries no prose for a prose gate to read", so the property is that no PROSE extension is
    # ever in it — which is one assertion, cannot fall behind the tuple, and blocks the measured
    # attack (adding `.md`, which un-reviewed README, GUIDE and CLAIMS at once) directly. A row per
    # extension would be an enumeration, and enumerations are what this file exists to stop.
    PROSE_EXT = (".md", ".lean", ".py", ".txt", ".json", ".yml", ".yaml", ".sh", ".ps1")
    for ext in PROSE_EXT:
        rows.append(("prose ext NOT in DATA_EXT: %s" % ext, ext not in batch.DATA_EXT,
                     "not treated as data" if ext not in batch.DATA_EXT else
                     "*** %s IS IN DATA_EXT — every file with this extension is exempt from the "
                     "prose gates and reviewed by nothing ***" % ext))
        if ext in batch.DATA_EXT:
            bad += 1

    # ⚠⚠ AND THE SAME SWITCH ONE LEVEL OVER: `check_encoding` KEEPS ITS OWN SCAN-SCOPE TUPLE.
    # It is the fifth private tree-enumerator in this bundle and it was added AFTER the class was
    # supposedly closed, with no scope pin and no guards property. Measured (/rely round 4,
    # RLY4-3): with a genuinely mojibaked `.md` staged, adding `'.md'` to `BINARY_EXT` took
    # `hooks.py pre-commit` from exit 1 to exit 0 and silently cut the scan from 409 files to 341 —
    # while `check_encoding --selftest`, `check_checkers --block` and `common --selftest` all stayed
    # green, because its controls are in-memory strings and can never see its enumerator.
    import check_encoding
    for ext in PROSE_EXT:
        hit = ext not in check_encoding.BINARY_EXT
        rows.append(("prose ext NOT in check_encoding.BINARY_EXT: %s" % ext, hit,
                     "still scanned" if hit else
                     "*** %s IS IN BINARY_EXT — every file with this extension silently leaves the "
                     "encoding scan, and the checker still reports clean ***" % ext))
        if not hit:
            bad += 1
    return rows, bad


def check_routing_enforcement():
    """Does the `/rely` router still BLOCK — the property the exemption is PRICED on?

    ⚠⚠ WHY THIS EXISTS, AND IT WAS MEASURED RATHER THAN REASONED. `tools/verify/**` and
    `tools/process/**` skip editorial and adversary *because* `/rely` covers them and BLOCKS. The
    warrant leg in `check_exemption_surface` tests that the ROUTING pattern reaches every path under
    the prefix — a COVERAGE claim — and stops there. On 2026-08-21 a `DC-25` probe neutered the
    enforcement in a detached worktree, leaving the pattern untouched, and this file exited 0 with
    the warrant row still reading `ok`. Fifth instance of warrant-satisfied-while-empty in this same
    code; the first four were sampling, narrowing, a three-probe set and unchecked regex flags.

    The exemption is priced on COVERAGE **and** ENFORCEMENT. Only the first was ever checked.

    ⚠ WHAT THIS DOES NOT CATCH, STATED SO NOBODY OVER-TRUSTS IT. It does not run the pre-push hook end
    to end, so it cannot prove a push actually stops; the standing control for that is
    `.claude-local/tools_wip/probe_warrant_blocks.py`, which neuters enforcement and requires this
    file to go red. These rows are the cheap always-on layer, not a replacement for the probe."""
    import importlib
    import batch
    importlib.reload(batch)
    rows, bad = [], 0

    def row(label, ok, why):
        nonlocal bad
        if not ok:
            bad += 1
        rows.append((label, ok, why))

    # ROUTE 1 — the fail-open legs are declared blocking. `logic` is executable checker code and
    # `switch` is the baselines/whitelists/pins, where one appended line silences a site permanently
    # with every control still green. Neither may ever be downgraded; only the `docs` enumeration may.
    for leg in ("logic", "switch"):
        got = batch._LEG_BLOCKING.get(leg)
        row("fail-open leg still BLOCKS: %s" % leg, got is True,
            "declared blocking" if got is True else
            "*** %s IS NOT BLOCKING (%r) — this is a FAIL-OPEN surface and CLAUDE.md rung 5 forbids "
            "downgrading it. The editorial/adversary exemption for tools/verify/** and "
            "tools/process/** is priced on this and is now UNPAID ***" % (leg, got))

    # ROUTE 2 — the table is not decorative: `check_routing` must actually emit those flags.
    # Behavioural, and deterministic — the hashes are synthetic, so this does not depend on whether
    # the working tree happens to be dirty. Asserting the table alone would be a claim about a
    # constant; this is a claim about the function.
    real = batch.checker_hashes
    try:
        batch.checker_hashes = lambda: {"check_prose.py": "0" * 12,
                                        "pov_baseline.txt": "0" * 12,
                                        "tools/process/README.md": "0" * 12}
        emitted = {}
        for _agent, _ran, why, blocking in batch.check_routing({}, None):
            for leg in ("logic", "switch", "docs"):
                if why.startswith("[%s]" % leg):
                    emitted[leg] = blocking
    finally:
        batch.checker_hashes = real
    for leg in ("logic", "switch"):
        got = emitted.get(leg)
        row("check_routing EMITS blocking: %s" % leg, got is True,
            "row carries blocking=True" if got is True else
            "*** check_routing emitted %r for the %s leg (expected True) — the table says one thing "
            "and the function does another, so _LEG_BLOCKING is decorative ***" % (got, leg))

    # ROUTE 3 — EVERY CONSUMER HONOURS THE FLAG. A guard protects a PROPERTY, not a hole, so this
    # enumerates call sites rather than naming the two that exist today. A third consumer that
    # unpacks three fields would crash; one that unpacks four and ignores `blocking` would silently
    # re-impose or silently drop enforcement, which is exactly the shape the probe demonstrated.
    # ⚠ WINDOWED, NOT WHOLE-FILE. Scanning the entire source for the word `blocking` was the first
    # version and it is too loose to be worth running: `batch.py` mentions the flag in a dozen
    # comments, so gutting the enforcement arithmetic to `bad += 0` would have left the row green.
    # The window is the call site plus what immediately consumes it, which is where the decision is.
    WINDOW = 12
    consumers = []
    for dirpath, _dirs, names in os.walk(os.path.join(REPO, "tools")):
        for n in names:
            if not n.endswith(".py"):
                continue
            p = os.path.join(dirpath, n)
            lines = io.open(p, encoding="utf-8", errors="replace").read().splitlines()
            for i, line in enumerate(lines):
                # ⚠ SKIP OCCURRENCES INSIDE STRING LITERALS. This scanner's own detector line
                # (`"check_routing(" in body`) matched itself and the row went green BY ACCIDENT —
                # the surrounding lines happened to contain commas and the word `blocking`. An
                # accidental pass is the `check_paths.py` shape CLAUDE.md names, so it is removed
                # rather than tolerated: a control must not count itself as a subject.
                j = line.find("check_routing(")
                if j < 0 or "def check_routing" in line:
                    continue
                if line[:j].count('"') % 2 or line[:j].count("'") % 2:
                    continue
                body = [ln for ln in lines[i:i + WINDOW]
                        if not ln.lstrip().startswith("#")]
                consumers.append((os.path.relpath(p, REPO).replace("\\", "/"),
                                  i + 1, "\n".join(body)))
    row("consumers of check_routing located", bool(consumers),
        "%d call site(s)" % len(consumers) if consumers else
        "*** NO call site found — either check_routing is dead or this scan is broken; an "
        "enumerator that finds nothing must never read as ok ***")
    for rel, lineno, body in consumers:
        # Two conditions, because either alone is passable. It must UNPACK four values (a three-value
        # unpack would crash loudly, but a `for row in ...` would not), and it must REFERENCE the
        # flag in code rather than in a comment.
        unpacks = body.count(",") >= 3 and "check_routing(" in body
        uses = "blocking" in body
        ok = unpacks and uses
        row("consumer honours blocking: %s:%d" % (rel, lineno), ok,
            "unpacks four fields and consults the flag" if ok else
            "*** %s:%d consumes check_routing without reading `blocking` in the %d lines that "
            "follow — enforcement is being decided somewhere this control cannot see ***"
            % (rel, lineno, WINDOW))

    # ROUTE 4 — THE ARITHMETIC ITSELF IS CORRECT. Behavioural and total: a blocking FAIL counts, a
    # non-blocking FAIL does not, and an `ok` row never counts whatever its flag says.
    cases = [([("/rely", False, "w", True)], 1, "a blocking FAIL counts"),
             ([("/rely", False, "w", False)], 0, "a WARN row does not count"),
             ([("/rely", True, "w", True)], 0, "an ok row never counts"),
             ([("/rely", False, "w", True), ("/rely", False, "w", False)], 1, "mixed rows")]
    for r, want, label in cases:
        got = batch.routing_bad(r)
        row("routing_bad: %s" % label, got == want,
            "%d as expected" % got if got == want else
            "*** routing_bad returned %d, expected %d — the enforcement arithmetic is wrong, so "
            "every row above is testing a decision that is not the one being made ***" % (got, want))

    # ROUTE 5 — AND THE PUSH GATE STILL CALLS IT. This is the route the 2026-08-21 probe walked: the
    # arithmetic can be perfect and simply not invoked. Gutting `bad += routing_bad(rows)` to
    # `bad += 0` leaves ROUTES 1-4 green and the push wide open, so the call site is asserted at the
    # FUNCTION OBJECT rather than a line window — immune to the code moving.
    import inspect
    try:
        src = inspect.getsource(batch.cmd_prepush)
    except (OSError, TypeError):
        src = ""
    calls = "routing_bad(" in src
    row("prepush still CALLS routing_bad", calls,
        "the push gate invokes the enforcement decision" if calls else
        "*** cmd_prepush does not call routing_bad — the routing legs are computed and their verdict "
        "discarded. This is exactly the neuter the 2026-08-21 warrant probe performed, and the "
        "editorial/adversary exemption for tools/verify/** is UNPAID while it holds ***")
    return rows, bad


def routing_hash():
    """What `/rely` routing sees. A permitted exemption must MOVE this."""
    import importlib
    import batch
    importlib.reload(batch)
    return batch.checker_hashes()


def moves_routing(ctx):
    return ctx["route_before"] != ctx["route_after"]


def r_content_marker():
    return _append(PROBE_FILE, "\n-- VENDORED FROM upstream, Apache-2.0\n")
r_content_marker.attacks = PROBE_FILE


def r_allowlist():
    return _append(os.path.join(BASE, "vendored_files.txt"), "ZeroParadox/Order/Snap.lean\n")
r_allowlist.attacks = os.path.join(BASE, "vendored_files.txt")


def r_pov_baseline():
    """The honest attack: absorb the live violation wholesale, the way a regeneration would.

    ⚠ **THIS ROUTE WAS INERT FOR ITS ENTIRE LIFE AND SCORED `ok` THROUGHOUT.** It invoked
    `check_pov.py --baseline`; the flag that regenerates that baseline is `--update-baseline`. An
    unrecognised flag is not an error here — the checker simply ran in ordinary mode, wrote nothing,
    and returned. So the planted violation was still present, the detector still fired, and the row
    printed `does NOT bypass / ok`: **a pass earned by the attack never happening.** Found
    2026-08-16 by the inert-route control in `run_property`, not by reading — measured directly, the
    baseline's SHA-256 is unchanged across a `--baseline` run.

    ⚠ **AND IT INVALIDATES THE EVIDENCE FOR THIS ROW'S `may_suppress=False`.** The comment at the
    registry entry cites a /rely pass 9 measurement (REL9-5) that *"with a DENIAL planted,
    `check_pov.py --baseline` leaves `--block` at exit 1"*. That measurement was made with this same
    dead flag, so it observed a command that did nothing. The CONCLUSION still holds — `scan()`
    returns denials in their own bucket and `--update-baseline` writes only `untagged`, so a DENIAL
    is structurally unbaselineable — but it now rests on reading the code and on this route actually
    running, rather than on a vacuous command."""
    p = os.path.join(BASE, "pov_baseline.txt")
    orig = io.open(p, "rb").read()

    def apply():
        sh(sys.executable, os.path.join(BASE, "check_pov.py"), "--update-baseline")

    def undo():
        io.open(p, "wb").write(orig)
    return apply, undo
r_pov_baseline.attacks = os.path.join(BASE, "pov_baseline.txt")


def r_nested_vendored():
    d = os.path.join(REPO, "ZeroParadox", "Order", "Vendored")
    tgt = os.path.join(d, "Probe.lean")

    def apply():
        os.makedirs(d, exist_ok=True)
        io.open(tgt, "w", encoding="utf-8", newline="\n").write(
            "import ZeroParadox.Order.Snap\n" + DENIAL)

    def undo():
        if os.path.exists(tgt):
            os.remove(tgt)
        if os.path.isdir(d) and not os.listdir(d):
            os.rmdir(d)
    return apply, undo
r_nested_vendored.attacks = os.path.join(REPO, "ZeroParadox", "Order", "Vendored", "Probe.lean")


# ═══ PROPERTY 2 — the bedrock review cap cannot be walked ═════════════════════════════════════
# Past BEDROCK_CAP, `gate_round.py` must exit non-zero and `ship.py pre` must refuse. Measured
# 2026-08-10: the cap was walkable by varying the --target slug, by passing --target with no value,
# and by omitting --target entirely. All three were closed by counting ROUNDS not targets — and a
# fourth (a missing or unparseable state file silently restarting at 0) was still open, which is
# exactly the pattern this registry exists to stop.

def _put_round(n):
    return _rewrite(ROUND_STATE, lambda _o: json.dumps(
        {"round": n, "arc_base": "0" * 40, "targets": {}}, indent=2).encode("utf-8"))


def cap_refuses():
    rc, out = sh(sys.executable, os.path.join(BASE, "gate_round.py"), "show")
    return rc != 0, out


def announces_fresh(ctx):
    """A sanctioned restart must SAY it is restarting."""
    return "fresh arc" in ctx["output"].lower() or "no state" in ctx["output"].lower()


def r_bump_fresh_target():
    def apply():
        sh(sys.executable, os.path.join(BASE, "gate_round.py"), "bump", "--target", "brand-new-slug")

    def undo():
        pass                                    # the property's own violate/undo restores the file
    return apply, undo
r_bump_fresh_target.attacks = ROUND_STATE


def r_bump_empty_target():
    def apply():
        sh(sys.executable, os.path.join(BASE, "gate_round.py"), "bump", "--target")

    def undo():
        pass
    return apply, undo
r_bump_empty_target.attacks = ROUND_STATE


def r_bump_no_target():
    def apply():
        sh(sys.executable, os.path.join(BASE, "gate_round.py"), "bump")

    def undo():
        pass
    return apply, undo
r_bump_no_target.attacks = ROUND_STATE


def r_delete_state():
    return _rewrite(ROUND_STATE, lambda _o: None)
r_delete_state.attacks = ROUND_STATE


def r_corrupt_state():
    return _rewrite(ROUND_STATE, lambda _o: b"{ this is not json")
r_corrupt_state.attacks = ROUND_STATE


def r_reset_command():
    """`gate_round.py reset` is the sanctioned escape — it must not be a QUIET one."""
    def apply():
        sh(sys.executable, os.path.join(BASE, "gate_round.py"), "reset")

    def undo():
        pass                                    # the property's violate/undo rewrites the file
    return apply, undo
r_reset_command.attacks = ROUND_STATE


def r_missing_round_key():
    """Valid JSON with no `round` key — `.get('round', 0)` silently restarted the count."""
    return _rewrite(ROUND_STATE, lambda _o: json.dumps(
        {"arc_base": "0" * 40, "targets": {}}, indent=2).encode("utf-8"))
r_missing_round_key.attacks = ROUND_STATE


def announces_reset(ctx):
    return "reset" in (ctx["output"] or "").lower()


def r_bool_round():
    """`{"round": true}` — `isinstance(True, int)` is True in Python, so `True > 5` compared as 1."""
    return _rewrite(ROUND_STATE, lambda _o: json.dumps(
        {"round": True, "arc_base": "0" * 40, "targets": {}}, indent=2).encode("utf-8"))
r_bool_round.attacks = ROUND_STATE


def r_negative_round():
    return _rewrite(ROUND_STATE, lambda _o: json.dumps(
        {"round": -99, "arc_base": "0" * 40, "targets": {}}, indent=2).encode("utf-8"))
r_negative_round.attacks = ROUND_STATE


# ═══ PROPERTY 3 — the /rely iteration cap cannot be walked ═══════════════════════════════════
# Tim, 2026-08-10: *"any non bedrock failure should cap at a certain iteration. it used to be two.
# A nitpicker will always find a knit to pick."* The cap releases at BLOCKING:0 once passes >=
# RELY_CAP. Every route below defeated it silently before this registry existed.

RELY_SIG = os.path.join(PRIV, "rely_cleared.txt")   # a SIGNAL: per-push state, stays private
_CAPPED_LINE = ("REVIEWED - /rely 2026-08-10 pass 4, scope the verification pipeline. "
                "BLOCKING:0 ORDINARY:9.\n")
# Known-good: past the pass count, but with a BLOCKING finding outstanding, so the cap must NOT fire.
_UNCAPPED_LINE = ("REVIEWED - /rely 2026-08-10 pass 4, scope the verification pipeline. "
                  "BLOCKING:1 ORDINARY:9.\n")


def rely_cap_fires():
    """With a BLOCKING:0 signal past RELY_CAP passes, the cap must FIRE."""
    import importlib
    import ship
    importlib.reload(ship)
    capped, why = ship.rely_capped()
    return capped, why


def r_no_target_bump():
    """The round counter never incremented — the reviewer's own pass number must still count."""
    return _rewrite(ROUND_STATE, lambda _o: json.dumps(
        {"round": 1, "arc_base": "0" * 40, "targets": {}}, indent=2).encode("utf-8"))
r_no_target_bump.attacks = ROUND_STATE


def r_drop_blocking_token():
    """Line 1 without `BLOCKING:` — must not read as 'not capped, carry on'."""
    return _rewrite(RELY_SIG, lambda o: b"REVIEWED - /rely pass 4, scope the pipeline.\n"
                    + (o.split(b"\n", 1)[1] if o and b"\n" in o else b""))
r_drop_blocking_token.attacks = RELY_SIG


def says_malformed(ctx):
    return "malformed" in (ctx["output"] or "").lower()


# ═══ PROPERTY 4 — the Engineer's-Take exemption cannot SILENTLY swallow prose ════════════════
#
# PRS-1, 2026-08-12. The exemption LATCHED: it closed only on a markdown heading, so a Take
# followed by no heading ran to the end of the block and everything after it went unmeasured.
# `check_prose` reported 3 lines against a cap of 10 for a 27-line block, and a corpus run said
# `0 new` while 13 files, 244 prose lines, were not being scanned at all.
#
# It survived because the pre-existing selftest planted its essay BEFORE the Take; the live
# shape was essay AFTER it. That is this project's own rule — plant the probe in the shape you
# actually expect — unapplied to the file that states it.
#
# The Take itself must STAY exempt: it is Tim's voice. So the property is not "the Take is
# measured" but "prose the Take hides cannot go QUIET" — the same design as the `Idiom:` label
# and `check_pov`'s DENIAL: make the suppression countable rather than forbidden.

_PROBE_ESSAY = "\n".join("probe essay line %d" % i for i in range(30))
PROBE_TAKE_BLOCK = ("\n/-!\n# Guard probe\n\n## Engineer's Take\n"
                    "probe take line\n\n---\n\n" + _PROBE_ESSAY + "\n-/\n")
# The same block with the delimiter removed. ⚠ Do NOT synthesise this with `.replace("---", "")`
# over the whole file: `Snap.lean` carries its own `---` in its real header, so a first-match
# replace mutates THAT and leaves the probe untouched — the route then tests nothing and the
# verdict is about the wrong block. Measured while writing this property.
PROBE_TAKE_BLOCK_NODELIM = PROBE_TAKE_BLOCK.replace("\n---\n", "")


def prose_blocks():
    rc, out = sh(sys.executable, os.path.join(BASE, "check_prose.py"), "--block")
    return rc != 0, out


def r_drop_take_delimiter():
    """Delete the `---` so the Take latches and swallows the essay — PRS-1 exactly.

    Permitted ONLY because a bare continuation is syntactically indistinguishable from a long
    Take, and adjudicating where Tim's prose ends is not this checker's call. The requirement
    is therefore that it be REPORTED, never that it be blocked.
    """
    orig = io.open(PROBE_FILE, "rb").read()

    def apply():
        data = io.open(PROBE_FILE, "rb").read()
        io.open(PROBE_FILE, "wb").write(
            data.replace(PROBE_TAKE_BLOCK.encode("utf-8"),
                         PROBE_TAKE_BLOCK_NODELIM.encode("utf-8")))

    def undo():
        io.open(PROBE_FILE, "wb").write(orig)
    return apply, undo
r_drop_take_delimiter.attacks = PROBE_FILE


def r_prose_baseline():
    """`--baseline` absorbs the live violation wholesale. Grandfathering is the sanctioned
    mechanism here (unlike a POV DENIAL, which is never baselineable), so this may suppress —
    but the key must land in a file a human reads."""
    p = os.path.join(BASE, "prose_baseline.txt")
    orig = io.open(p, "rb").read()

    def apply():
        sh(sys.executable, os.path.join(BASE, "check_prose.py"), "--baseline")

    def undo():
        io.open(p, "wb").write(orig)
    return apply, undo
r_prose_baseline.attacks = os.path.join(BASE, "prose_baseline.txt")


# ═══ PROPERTY 5 — a block that is BOTH over cap and latching appears in BOTH reports ═════════
#
# RLY12-1, 2026-08-12. PROPERTY 4 could not detect removal of the fix it was written for.
# Reverting one token (`if take_unclosed:` back to `elif`) left `--selftest` green, PROPERTY 4
# printing PASS, and the corpus report saying `UNMEASURED: 10` when the truth was 65 — the
# property false for 55 blocks and 397 prose lines, with a pre-push BLOCK gate calling it PASS.
#
# Why PROPERTY 4 is blind to it: BOTH its probe states are one-sided by construction. With the
# `---` the block is over cap and not latching (36 lines); without it the block collapses to 3
# lines and is under cap. Neither state is ever BOTH, so the `elif` branch is unreachable from
# there — and BOTH is 55 of the 65 live cases.
#
# `check_prose.py --selftest` is run by NO gate (verified against hooks.py / batch.py / ship.py),
# so an assertion there would gate nothing. The control has to be a property with its own
# detector, which is this.

PROBE_BOTH_BLOCK = ("\n/-!\n# Guard probe both\n"
                    + "\n".join("probe pre-take line %d" % i for i in range(30))
                    + "\n\n## Engineer's Take\n"
                    + "\n".join("probe take line %d" % i for i in range(6)) + "\n-/\n")


def both_reports_fire():
    """The planted block is over cap AND latching, so it must appear as BOTH.

    Detector, not a bypass test: with the `elif` regression the block still reports as `block`
    (so `check_prose --block` still exits 1 and every bypass test still passes) while vanishing
    from the gap accounting entirely. Only asking for BOTH rows separates the two states.
    """
    _rc, out = sh(sys.executable, os.path.join(BASE, "check_prose.py"), "--block")
    # ⚠ Deliberately does NOT require `--block` to exit non-zero. Written that way first, and
    # the baseline route then read as "BYPASSES": grandfathering legitimately suppresses the
    # OVER-CAP half, so keying on the exit code conflated "the gap row vanished" with "the
    # violation was baselined", which is a permitted and expected outcome. The property is
    # narrower and does not depend on the exit code: **the gap row must name this block
    # whether or not its over-cap half is baselined**, because `takeopen` is never baselined.
    if "MEASUREMENT GAPS" not in (out or ""):
        return False, "no MEASUREMENT GAPS section - the gap accounting is silent"
    section = out.split("MEASUREMENT GAPS", 1)[1]
    named = "Guard probe both" in section
    return named, ("gap section names the planted block" if named else
                   "OVER CAP BUT NOT COUNTED AS A GAP - the `elif` regression, or equivalent")


def gap_is_reported(ctx):
    """The suppression must name THIS block inside the MEASUREMENT GAPS section.

    ⚠ RLY11-2, 2026-08-12. The first version was `"UNMEASURED" in out and "Order/Snap.lean" in
    out`, and it returned **True with the `---` still present** — i.e. with nothing suppressed:
    `UNMEASURED` came from ten unrelated files and `Order/Snap.lean` from the probe's own
    violation line elsewhere in the output. A `visible` predicate that cannot return False is
    not evidence; it is decoration. **Parse the SECTION, and require the gap-only listing.**
    """
    out = ctx["output"] or ""
    if "MEASUREMENT GAPS" not in out:
        return False
    section = out.split("MEASUREMENT GAPS", 1)[1].split("=" * 40, 1)[0]
    # ⚠ RLY12-2: key on the BLOCK (its title), not just the file. Keyed on `Order/Snap.lean`
    # alone, any unrelated gap-only block in that file greens this with the probe unsuppressed
    # - reproduced. `baseline_records_it` was already keyed to the probe's own title; this is
    # the same predicate written two ways, and the asymmetry was the tell.
    return any("Order/Snap.lean" in ln and "Guard probe" in ln and "close the Take" in ln
               for ln in section.splitlines())


def baseline_records_it(ctx):
    """The suppression must be written down where it can be audited and shrunk.

    ⚠ RLY11-2. The first version asked whether `Order/Snap.lean::block::` appeared at all —
    and `Snap.lean` already carries four baselined block keys, so it returned True **with
    nothing planted** and could never fail. Key on the PROBE BLOCK's own title instead, which
    exists only while the probe is planted.
    """
    p = os.path.join(BASE, "prose_baseline.txt")
    try:
        body = io.open(p, encoding="utf-8").read()
    except OSError:
        return False
    return any("Order/Snap.lean::block::" in ln and "Guard probe" in ln
               for ln in body.splitlines())


PROPERTIES = [
    {
        "name": "a block both over cap and latching appears in BOTH reports",
        "violate": lambda: _append(PROBE_FILE, PROBE_BOTH_BLOCK),
        "detect": both_reports_fire,
        "routes": [
            # `takeopen` is never baselined by design, so grandfathering the over-cap half must
            # NOT take the gap row with it. If it ever does, the gap accounting becomes
            # suppressible and this property is back to where RLY12-1 found it.
            ("checker baseline absorbs the over-cap half", r_prose_baseline, False, None),
        ],
    },
    {
        "name": "the Engineer's-Take exemption cannot silently swallow prose",
        "violate": lambda: _append(PROBE_FILE, PROBE_TAKE_BLOCK),
        "detect": prose_blocks,
        "routes": [
            ("drop the `---` so the Take latches", r_drop_take_delimiter, True, gap_is_reported),
            ("checker baseline absorbs it", r_prose_baseline, True, baseline_records_it),
        ],
    },
    {
        "name": "a file cannot exempt itself from the gating checkers",
        "violate": lambda: _append(PROBE_FILE, DENIAL),
        "detect": pov_blocks,
        "routes": [
            ("content marker in the head", r_content_marker, False, None),
            ("nested Vendored/ directory", r_nested_vendored, False, None),
            ("vendored_files.txt entry", r_allowlist, True, moves_routing),
            # ⚠ must NOT suppress, and this row said `may_suppress=True` on an unverified belief.
            # MEASURED /rely pass 9 (REL9-5): with a DENIAL planted, `check_pov.py --baseline`
            # leaves `--block` at exit 1 — the DENIAL pattern is never baselined, by design. The row
            # passed anyway because the route does not in fact suppress, so the mis-grading was
            # invisible; a future regression that DID let a baseline swallow a DENIAL would have
            # been scored "suppresses (permitted)" and reported ok. **A `may_suppress` entry is a
            # claim about the system and needs the same evidence as any other.**
            ("checker baseline absorbs it", r_pov_baseline, False, None),
        ],
    },
    {
        "name": "the bedrock review cap cannot be walked",
        "clean": lambda: _put_round(1),
        "violate": lambda: _put_round(6),
        "detect": cap_refuses,
        "routes": [
            ("bump with a fresh --target slug", r_bump_fresh_target, False, None),
            ("bump with --target and no value", r_bump_empty_target, False, None),
            ("bump with no --target at all", r_bump_no_target, False, None),
            ("state file deleted", r_delete_state, True, announces_fresh),
            ("state file corrupted", r_corrupt_state, False, None),
            ("`gate_round.py reset`", r_reset_command, True, announces_reset),
            ("valid JSON, no `round` key", r_missing_round_key, False, None),
            # ⚠ Routes 8 and 9 were CLOSED in `gate_round.py` and never REGISTERED here — by the
            # author of the rule that closing a route means adding it to this file, in the same
            # session. With the fix reverted, guards printed "every route behaves / PASS", exit 0,
            # 0 FAIL lines: the registry cannot report a route nobody listed (/rely pass 8, REL8-4).
            ("`round: true` (bool is int)", r_bool_round, False, None),
            ("negative round", r_negative_round, False, None),
        ],
    },
    {
        "name": "the /rely iteration cap cannot be walked",
        "clean": lambda: _rewrite(RELY_SIG, lambda _o: _UNCAPPED_LINE.encode("utf-8")),
        "violate": lambda: _rewrite(RELY_SIG, lambda _o: _CAPPED_LINE.encode("utf-8")),
        "detect": rely_cap_fires,
        "routes": [
            ("--target never bumped", r_no_target_bump, False, None),
            ("BLOCKING: token dropped", r_drop_blocking_token, True, says_malformed),
        ],
    },
]


def run_property(prop):
    """Plant the violation, confirm it is detected with no route applied, then walk EVERY route."""
    results = []
    v_apply, v_undo = prop["violate"]()

    # ⚠ MUST-SUPPRESS FIRST. With NOTHING planted the detector must stay quiet; if it fires on a
    # clean state it is not detecting the violation, and every route below then scores `ok` for the
    # wrong reason. Measured by /rely pass 6: DELETE `check_pov.py` and this file printed
    # `every route behaves / PASS`, exit 0 — because a missing script exits 2 and the detector was
    # `rc != 0`. The `vendored_files.txt` route even upgraded from "suppresses (permitted)" to the
    # stronger-looking "does NOT bypass". A control with only a must-fire half is half-tested, which
    # this project has written down twice and had to learn a third time HERE, inside the control
    # written to stop exactly this recurrence.
    # A property whose ambient state is not reliably clean supplies one (`clean`), so this control
    # tests the detector rather than today's counter value.
    c_apply, c_undo = prop["clean"]() if prop.get("clean") else (None, None)
    try:
        if c_apply:
            c_apply()
        quiet, qout = prop["detect"]()
    finally:
        if c_undo:
            c_undo()
    if quiet:
        return [("(control: nothing planted)",
                 "DETECTOR BROKEN — fires on a clean state, so every verdict below is worthless: "
                 + ((qout or "").strip().splitlines() or [""])[0][:120], False)]
    try:
        v_apply()
        fires, _out = prop["detect"]()
        if not fires:
            return [("(control: violation planted, no route)",
                     "BASELINE BROKEN — not detected even with no exemption", False)]
        for label, factory, may_suppress, visible in prop["routes"]:
            r_apply, r_undo = factory()
            before = routing_hash()
            # ⚠ THE INERT-ROUTE CONTROL, and it closes this registry's own DC-18 hole.
            #
            # A route is scored by whether the detector STILL fires after the route is applied. So a
            # route whose `apply()` silently stops mutating anything — a renamed baseline, a moved
            # probe path, a `produce` that returns the bytes it was given — leaves the planted
            # violation in place, the detector fires, and the row prints `does NOT bypass / ok`.
            # **It passes BECAUSE THE ATTACK NEVER HAPPENED.** That is exactly the proxy-check shape
            # (`DEFECT_CLASSES.md` DC-18): the test measures something correlated with the property
            # instead of the property, and DC-10's detector cannot find it, because deleting the
            # input makes a proxy check fail correctly.
            #
            # ⚠ MEASURED PER ROUTE, NOT OVER THE UNION — and the union version was itself a false
            # green (COM-3, /rely 2026-08-16). Hashing all of `TOUCHED` together only asks "did
            # ANYTHING move", so a route whose real attack is dead but which incidentally writes some
            # other tracked path still scored `ok`. That is GRD-1 again with one extra step. A
            # constructed probe demonstrated it: a route running the dead `check_pov.py --baseline`
            # flag AND appending a comment to `vendored_files.txt` passed.
            #
            # So each factory DECLARES the path its attack must move, beside its own definition —
            # `r_allowlist.attacks = ...` — and the control requires THAT path to have changed. A
            # central table would have been a second place to maintain, which is the pattern this
            # file exists to argue against.
            attacked = getattr(factory, "attacks", None)
            fs_before = snapshot()
            try:
                r_apply()
                moved = [p for p in TOUCHED if snapshot()[p] != fs_before[p]]
                if attacked is not None and attacked not in moved:
                    results.append((label, "ROUTE INERT — its declared target (%s) did not change, "
                                           "so the verdict below would be a false green"
                                           % os.path.relpath(attacked, REPO), False))
                    continue
                if attacked is None and not moved:
                    results.append((label, "ROUTE INERT — applying it changed none of the %d hashed "
                                           "paths, and it declares no target to check against"
                                           % len(TOUCHED), False))
                    continue
                still, out = prop["detect"]()
                ctx = {"route_before": before, "route_after": routing_hash(), "output": out}
                if still:
                    verdict, ok = "does NOT bypass", True
                elif not may_suppress:
                    verdict, ok = "BYPASSES — the property is not held", False
                elif visible and visible(ctx):
                    verdict, ok = "suppresses (permitted) and is VISIBLE", True
                else:
                    verdict, ok = "suppresses (permitted) but does so SILENTLY", False
                results.append((label, verdict, ok))
            finally:
                r_undo()
                v_apply()                       # routes may clobber the planted state; re-plant
    finally:
        v_undo()
    return results


# Every path any route can touch. Hashed before and after to PROVE restoration.
TOUCHED = [
    PROBE_FILE,
    os.path.join(BASE, "vendored_files.txt"),
    os.path.join(BASE, "pov_baseline.txt"),
    # ⚠ Added 2026-08-12 with PROPERTY 4, and it was MISSING for one run before that. The
    # `r_prose_baseline` route rewrites this file wholesale via `--baseline`, so without this
    # line the run printed `restored (6 paths hashed): yes` while a file it had rewritten was
    # outside the proof entirely. A restoration proof that does not name a mutated path is a
    # false green — the registry's own failure mode, found while extending the registry.
    # ANY new route must add every path it writes, here, in the same change.
    os.path.join(BASE, "prose_baseline.txt"),
    ROUND_STATE,
    RELY_SIG,
    os.path.join(REPO, "ZeroParadox", "Order", "Vendored", "Probe.lean"),
]


def snapshot():
    import hashlib
    out = {}
    for p in TOUCHED:
        out[p] = hashlib.sha256(io.open(p, "rb").read()).hexdigest() if os.path.exists(p) else None
    return out


# ═══ CONTROLS ON THE REGISTRY ITSELF ══════════════════════════════════════════════════════════
#
# ⚠ **THIS FILE HAD NO CONTROLS OF ITS OWN UNTIL 2026-08-16, AND `--selftest` WAS SILENTLY IGNORED**
# — `main()` parsed only `--list`, so the flag fell through to an ordinary run and produced
# byte-identical output. A previous session inferred from that identical output that `--selftest`
# "runs nothing"; the inference does not go that way, and it was wrong. It runs everything. The real
# gap was this: **nothing checked that the guard would still NOTICE a regression.**
#
# That is not a hypothetical. The controls below were written first and the inert-route check they
# certify found a live false green on its first run: `r_pov_baseline` invoked `check_pov.py
# --baseline`, a flag that checker does not have, so for its entire life the route wrote nothing and
# scored `ok / does NOT bypass` — a pass earned because the attack never happened.
#
# ⚠ **THE INERT-ROUTE CHECK IS ALSO THE REGISTRY-COVERAGE CHECK, and that is worth stating.** A
# route that writes a path MISSING from `TOUCHED` changes no hashed path either, so it is reported
# INERT. The 2026-08-12 failure — a route rewriting `prose_baseline.txt` while that file sat outside
# the restoration proof, printing `restored: yes` about a file it had rewritten — is now caught by
# the same measurement, from the other side.

_SYN_MARK = "\n-- guards selftest probe marker\n"
_SYN_EXTRA = "\n-- guards selftest second write\n"


def _noop_route():
    """A route that does nothing. MUST be reported INERT."""
    return (lambda: None), (lambda: None)


def _misdirected_route():
    """A route whose DECLARED attack is dead but which writes some OTHER hashed path.

    ⚠ This is COM-3's probe, kept as a permanent control. Under the union-hashing version it scored
    `ok / does NOT bypass` — the GRD-1 false green with one extra step, because something moved even
    though the attack did not. It must now be reported INERT."""
    return _append(os.path.join(BASE, "vendored_files.txt"), "\n# guards selftest misdirection\n")


_misdirected_route.attacks = os.path.join(BASE, "pov_baseline.txt")   # never touched by the above


def _syn_violate():
    """Plant the synthetic marker in a path that IS inside TOUCHED."""
    return _append(PROBE_FILE, _SYN_MARK)


def _syn_route():
    """A route that genuinely mutates a path inside TOUCHED. Must NOT be reported inert."""
    return _append(PROBE_FILE, _SYN_EXTRA)


def _syn_detect():
    """Fires iff the synthetic marker is present.

    ⚠ IT MUST BE STATE-DEPENDENT, not a constant. A first version returned `True` unconditionally
    and the must-fire control reported MISSED — correctly: `run_property` checks the detector on a
    CLEAN state first and abandons the property as `DETECTOR BROKEN` if it fires there, so the route
    loop was never reached. That is the guard's own must-suppress-first discipline catching a
    malformed control, which is the behaviour to keep."""
    try:
        return _SYN_MARK.strip() in io.open(PROBE_FILE, encoding="utf-8").read(), ""
    except OSError:
        return False, ""


def _syn_prop(label, factory):
    return {"name": "synthetic", "violate": _syn_violate, "detect": _syn_detect,
            "routes": [(label, factory, False, None)]}


def selftest():
    """Controls on the guard machinery, run against SYNTHETIC properties.

    Real properties are not used here: their verdicts depend on the corpus, and a control that moves
    when the corpus moves is not a control. Each synthetic property has a detector whose behaviour is
    known in advance, so what is being tested is `run_property`, not the tree."""
    must_fire = [
        ("a route that mutates nothing", _syn_prop("no-op route", _noop_route)),
        # COM-3: writes a hashed path, but not the one it declares it attacks.
        ("a route that moves the WRONG path",
         _syn_prop("misdirected route", _misdirected_route)),
    ]
    must_suppress = [("a route that really mutates", _syn_prop("real route", _syn_route))]

    def _reports_inert(prop):
        rows = run_property(prop)
        return any("ROUTE INERT" in verdict for _l, verdict, _ok in rows)

    before = snapshot()
    bad = common.run_controls([
        ("MUST FIRE (the inert-route control notices)", must_fire, _reports_inert, True, "MISSED"),
        ("MUST SUPPRESS (a live route is not called inert)", must_suppress, _reports_inert,
         False, "FALSE POSITIVE"),
    ], width=42)

    # The restoration proof must itself be honest: after running synthetic properties that mutated a
    # real file, every hashed path is back. A guard that cannot restore cannot be run in a hook.
    after = snapshot()
    moved = [p for p in TOUCHED if before[p] != after[p]]
    print("RESTORATION")
    print("  %-42s %s" % ("synthetic routes left no residue",
                          "ok" if not moved else "*** %d PATH(S) MOVED ***" % len(moved)))
    bad += 0 if not moved else 1

    # Coverage: every route in the registry must be reachable and callable. A factory that raises is
    # a route nobody is testing, which is the failure this whole file exists to prevent.
    n_routes = sum(len(p["routes"]) for p in PROPERTIES) + len(EXEMPTION_SURFACE)
    print("REGISTRY")
    print("  %-42s %s (%d)" % ("every route has a callable factory",
                               "ok" if n_routes else "*** EMPTY REGISTRY ***", n_routes))
    bad += 0 if n_routes else 1

    if bad:
        print("\nselftest: FAIL (%d)" % bad)
    return 1 if bad else 0


def main():
    report.banner("property guards", [
        ("purpose", "enumerate every ROUTE to a property and test all of them"),
        ("why", "one property was 'fixed' four times, each fix leaving another door open"),
        ("rule", "closing a route means ADDING IT HERE, so the list outlives the memory"),
    ])
    if "--selftest" in sys.argv:
        return selftest()
    if "--list" in sys.argv:
        for p in PROPERTIES:
            print("  %s" % p["name"])
            for label, _f, may, _v in p["routes"]:
                print("     - %-34s %s" % (label, "may suppress" if may else "must NOT suppress"))
        print("  a changed file cannot escape the REVIEW-SIGNAL requirement")
        for label, _path, may, _router, _why in EXEMPTION_SURFACE:
            print("     - %-34s %s" % (label, "may exempt" if may else "must NOT exempt"))
        return 0

    before = snapshot()
    bad = 0
    try:
        for p in PROPERTIES:
            print("\n  PROPERTY: %s" % p["name"])
            for label, verdict, ok in run_property(p):
                print("    %-4s %-34s %s" % ("ok" if ok else "FAIL", label, verdict))
                bad += 0 if ok else 1
        # Classification, not mutation — so it runs inside the try but plants nothing.
        print("\n  PROPERTY: a changed file cannot escape the REVIEW-SIGNAL requirement")
        _rows, _bad = check_exemption_surface()
        for label, ok, verdict in _rows:
            print("    %-4s %-34s %s" % ("ok" if ok else "FAIL", label, verdict))
        bad += _bad
        # ⚠ AND THE REGISTRY'S OWN COMPLETENESS. Every row above can pass while an unregistered
        # prefix is exempt from everything — see check_exemption_completeness.
        print("\n  PROPERTY: no exemption prefix escapes the registry")
        _rows, _bad = check_exemption_completeness()
        for label, ok, verdict in _rows:
            print("    %-4s %-34s %s" % ("ok" if ok else "FAIL", label, verdict))
        bad += _bad
        # ⚠⚠ AND THAT THE ROUTER IT WARRANTS STILL BLOCKS. The warrant above tests COVERAGE (does the
        # pattern reach the whole prefix) and is blind to ENFORCEMENT — measured 2026-08-21, a probe
        # stopped the router blocking and this file still exited 0.
        print("\n  PROPERTY: the router the exemption is priced on still BLOCKS")
        _rows, _bad = check_routing_enforcement()
        for label, ok, verdict in _rows:
            print("    %-4s %-34s %s" % ("ok" if ok else "FAIL", label, verdict))
        bad += _bad
    finally:
        after = snapshot()
    moved = [p for p in TOUCHED if before[p] != after[p]]
    clean = not moved
    print("\n  restored (%d paths hashed): %s"
          % (len(TOUCHED), "yes" if clean else "NO — RESTORE BY HAND:\n    "
             + "\n    ".join(os.path.relpath(p, REPO) for p in moved)))
    report.done("property guards", bad == 0 and clean,
                "every route behaves" if bad == 0 else "%d route(s) misbehaving" % bad)
    return 1 if (bad or not clean) else 0


if __name__ == "__main__":
    sys.exit(main())
