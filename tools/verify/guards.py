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
import subprocess
import sys

# TWO roots. HERE is the tracked public bundle and holds the BASELINES — which are themselves
# exemption routes, so they must travel with the guard that enumerates them. PRIV holds per-push
# state (round state, signals) and may be absent in a public clone.
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
PRIV = os.path.join(REPO, ".claude-local")
SELF = os.path.relpath(os.path.abspath(__file__), REPO).replace("\\", "/")
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


def r_allowlist():
    return _append(os.path.join(BASE, "vendored_files.txt"), "ZeroParadox/Order/Snap.lean\n")


def r_pov_baseline():
    # The honest attack: absorb the live violation wholesale, the way `--baseline` would.
    def _apply_undo():
        p = os.path.join(BASE, "pov_baseline.txt")
        orig = io.open(p, "rb").read()

        def apply():
            sh(sys.executable, os.path.join(BASE, "check_pov.py"), "--baseline")

        def undo():
            io.open(p, "wb").write(orig)
        return apply, undo
    return _apply_undo()


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


def r_bump_empty_target():
    def apply():
        sh(sys.executable, os.path.join(BASE, "gate_round.py"), "bump", "--target")

    def undo():
        pass
    return apply, undo


def r_bump_no_target():
    def apply():
        sh(sys.executable, os.path.join(BASE, "gate_round.py"), "bump")

    def undo():
        pass
    return apply, undo


def r_delete_state():
    return _rewrite(ROUND_STATE, lambda _o: None)


def r_corrupt_state():
    return _rewrite(ROUND_STATE, lambda _o: b"{ this is not json")


def r_reset_command():
    """`gate_round.py reset` is the sanctioned escape — it must not be a QUIET one."""
    def apply():
        sh(sys.executable, os.path.join(BASE, "gate_round.py"), "reset")

    def undo():
        pass                                    # the property's violate/undo rewrites the file
    return apply, undo


def r_missing_round_key():
    """Valid JSON with no `round` key — `.get('round', 0)` silently restarted the count."""
    return _rewrite(ROUND_STATE, lambda _o: json.dumps(
        {"arc_base": "0" * 40, "targets": {}}, indent=2).encode("utf-8"))


def announces_reset(ctx):
    return "reset" in (ctx["output"] or "").lower()


def r_bool_round():
    """`{"round": true}` — `isinstance(True, int)` is True in Python, so `True > 5` compared as 1."""
    return _rewrite(ROUND_STATE, lambda _o: json.dumps(
        {"round": True, "arc_base": "0" * 40, "targets": {}}, indent=2).encode("utf-8"))


def r_negative_round():
    return _rewrite(ROUND_STATE, lambda _o: json.dumps(
        {"round": -99, "arc_base": "0" * 40, "targets": {}}, indent=2).encode("utf-8"))


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


def r_drop_blocking_token():
    """Line 1 without `BLOCKING:` — must not read as 'not capped, carry on'."""
    return _rewrite(RELY_SIG, lambda o: b"REVIEWED - /rely pass 4, scope the pipeline.\n"
                    + (o.split(b"\n", 1)[1] if o and b"\n" in o else b""))


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
            try:
                r_apply()
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


def main():
    report.banner("property guards", [
        ("purpose", "enumerate every ROUTE to a property and test all of them"),
        ("why", "one property was 'fixed' four times, each fix leaving another door open"),
        ("rule", "closing a route means ADDING IT HERE, so the list outlives the memory"),
    ])
    if "--list" in sys.argv:
        for p in PROPERTIES:
            print("  %s" % p["name"])
            for label, _f, may, _v in p["routes"]:
                print("     - %-34s %s" % (label, "may suppress" if may else "must NOT suppress"))
        return 0

    before = snapshot()
    bad = 0
    try:
        for p in PROPERTIES:
            print("\n  PROPERTY: %s" % p["name"])
            for label, verdict, ok in run_property(p):
                print("    %-4s %-34s %s" % ("ok" if ok else "FAIL", label, verdict))
                bad += 0 if ok else 1
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
