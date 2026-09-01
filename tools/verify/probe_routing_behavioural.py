# -*- coding: utf-8 -*-
"""MUTATION CONTROL for the behavioural routing routes in `guards.py` (ROUTE 3 and ROUTE 5).

⭐ THE CONTROL IS THE DELIVERABLE, NOT THE GUARD. A guard that is green on a clean tree has
demonstrated nothing whatsoever; the only evidence it works is that it goes RED when the property it
claims to protect is actually broken. This file breaks it, nine ways, and requires the predicted row
to fail each time.

⚠ IT ASSERTS THE ROW, NOT THE EXIT CODE. `guards.py` walks many routes and others may be failing for
unrelated reasons, so "exit 1" would pass this control for the wrong reason — the classic
warrant-satisfied-while-empty shape this whole layer keeps producing. Each mutation below names the
row that must go red.

⚠ TWO OF THE NINE REQUIRE THE GUARD TO STAY **GREEN**, AND THEY ARE NOT PADDING. `RLY27-1` (one
space before an argument list) and `RLY27-3` (a `list(...)` wrapper) each defeated the previous
AST-based version while changing NOTHING about behaviour. A behavioural control must be indifferent
to them. If a future version of this control starts requiring red on those two, someone has
reintroduced a syntax test.

**Provenance.** The nine are the six escapes `/rely` pass 6 executed against attempt 3 (`RLY27-1..6`),
plus the three classic neuters (`if False:` at the release gate, dropping `and blocking`, and
downgrading the `logic` leg). Written up in full in
`.claude-local/notes/reliability_2026-08-22_rely-routing-c01c0e3.md`.

**It runs in its own detached worktree and removes it.** ⚠⚠ NEVER point it at the shared checkout:
it edits `ship.py` and `batch.py` in place, and `CLAUDE.md`'s hardest rule is that an agent
exercising the gates must not touch the caller's tree. Self-provisioning is not convenience here, it
is the safety property.

    python tools/verify/probe_routing_behavioural.py
"""
import io
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                                    # noqa: E402

common.utf8_stdout()
SELF = common.self_rel(__file__)
REPO = str(common.REPO)

# ⚠ A SENTINEL, NOT A ROW LABEL. A mutation carrying this instead of a `guards.py` row is judged by
# running `batch.py prepush` and reading its EXIT CODE — see `_prepush_exit`.
EXIT_NEEDLE = "__prepush_exit__"

SHIP_ANCHOR = '        if agent == "/rely" and not ran and blocking:'
SHIP_LOOP = "    for agent, ran, why, blocking in batch.check_routing({}, ranges):"


def _read(p):
    return io.open(p, encoding="utf-8").read()


def _write(p, s):
    io.open(p, "w", encoding="utf-8", newline="\n").write(s)


def _guards_rows(wt):
    """Run guards.py inside the worktree and return {row label: ok|FAIL}."""
    p = subprocess.run([sys.executable, os.path.join(wt, "tools", "verify", "guards.py")],
                       capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=wt)
    rows = {}
    for line in (p.stdout + p.stderr).splitlines():
        m = re.match(r"\s+(ok|FAIL)\s+(.*)", line)
        if m:
            rows[m.group(2).strip()[:70]] = m.group(1)
    return p.returncode, rows


def _prepush_exit(wt):
    """Run `batch.py prepush` inside the worktree and return its EXIT CODE.

    ⚠⚠ THE OBSERVABLE THE FIRST FIVE CONTROLS LACKED. Every earlier attempt read a `guards.py` ROW,
    and a row is computed by calling the verdict functions in `guards`' own frame — where the
    property still holds however thoroughly `cmd_prepush` discards the answer. Measured 2026-08-24:
    one added line (`_routing_bad, _missing = 0, ()`) took prepush to exit 0 with `prepush PASS`
    printed under live FAIL rows, while guards reported 81/81 ok and this probe reported 11 of 11.

    **An exit code cannot be faked by rebinding a name.** It is the thing the hook actually consumes,
    so it is the thing the control must observe.

    ⚠⚠ `--ranges` IS LOAD-BEARING, AND ITS ABSENCE DEFEATED THIS CONTROL COMPLETELY (found by
    /rely, 2026-08-25). With no ranges and a clean worktree, `cmd_prepush` prints
    `CANNOT JUDGE: no --ranges given` and takes `sys.exit(1)` — BEFORE `routing_verdict` and
    `enforce_prepush_verdict` ever run. So the baseline's exit 1 came from the argument parser,
    not from the enforcement, and every mutation was compared against a run that never reached
    the code under test. The control reported 13 of 13 while observing nothing.

    That is `DC-22` — a control passing for the wrong reason — landing on the control built to
    close `RLY28-1`. The docstring above promised *"if that ever stops holding, this control has
    lost its teeth and must say so rather than pass"*; it could not say so, because nothing looked.
    `_assert_reached` is that check, and it fails LOUD rather than returning a code.

    ⚠⚠ IT RETURNS THE **ROUTING COUNT**, NOT THE EXIT CODE, AND THAT IS THE THIRD ATTEMPT AT THIS
    OBSERVABLE. The exit code is OVER-DETERMINED: `prepush` exits non-zero for review signals, the
    pushed-tip leg, a crash, or routing, so `exit != 0` cannot distinguish an ENFORCING router from
    an ABSENT one. Measured by /rely 2026-08-26 twice over:

      · `check_routing` replaced with `return []` -> "0 routing, 2 other", exit 1. The old probe
        read BLOCKS and every mutation still passed. The router was GONE and the control was green.
      · a fail-open planted in the copied `record.py` took prepush from 4 routing failures to 2 —
        `[logic]`, `[switch]` and both review-signal legs cleared — and the probe printed 13 of 13.

    Widening what the probe COPIED (the previous fix) changed what it could SEE and not what it
    LOOKED AT. `enforce_prepush_verdict` already prints the routing count separately — "%d push
    check(s) failed — %d routing, %d other" — so the number that answers the question is right
    there in the output the enforcement itself emits. A router that stops enforcing drives it to
    zero; nothing else does."""
    p = subprocess.run([sys.executable, os.path.join(wt, "tools", "verify", "batch.py"),
                        "prepush", "--ranges", "HEAD~1..HEAD"],
                       capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=wt)
    out = p.stdout + p.stderr
    _assert_reached(out)
    m = re.search(r"push check\(s\) failed\s*[—-]\s*(\d+)\s+routing", out)
    if m:
        return int(m.group(1)), p.returncode
    # `prepush PASS` means the enforcement ran and found nothing: zero routing failures, honestly.
    if _ENFORCE_OK in out:
        return 0, p.returncode
    raise SystemExit(
        "probe could not read a ROUTING COUNT from prepush, and must not fall back to the exit\n"
        "  code alone — that is the over-determined observable this leg exists to stop using.")


def _prepush_blocks(wt):
    """True only when the router BOTH said it refused AND the process actually refused.

    ⚠⚠ FOURTH ATTEMPT AT THIS OBSERVABLE, AND THE DEFECT EACH TIME WAS **SUBSTITUTION**. Enforcement
    has two halves — *say it* (the routing count in `enforce_prepush_verdict`'s own message) and
    *do it* (the process exit code `hooks.py pre_push` actually consumes). Every previous version
    watched exactly one half and dropped the other, so each fix moved the blindness rather than
    removing it:

      · attempts 1-2 read a `guards.py` ROW — computed in guards' own frame, true however
        thoroughly `cmd_prepush` discards the answer.
      · attempt 3 read the EXIT CODE alone — over-determined, so `check_routing` replaced with
        `return []` still gave exit 1 and the probe printed 13 of 13 with the router GONE.
      · attempt 4 read the ROUTING COUNT alone and stopped reading `p.returncode` at all. /rely
        round 6 broke the *doing* half twice — `try/except SystemExit: pass` around
        `enforce_prepush_verdict`, and `die`'s `sys.exit(1)` changed to `sys.exit(0)` — and got,
        verbatim: `BLOCKED: 6 push check(s) failed — 4 routing, 2 other` followed by
        `prepush PASS`, `prepush exit=0`, `guards exit=0`, `RESULT: 13 of 13 behaved as required`.
        A green local push gate printing four routing failures directly above itself.

    Attempt 3's own docstring had the argument right — *"an exit code cannot be faked by rebinding
    a name; it is the thing the hook actually consumes, so it is the thing the control must
    observe"* — and attempt 4 then removed the exit code. **That is why this is a CONJUNCTION and
    not a better single signal.** Neither half is the property; the property is that they agree.
    Narrowing a proxy is the failure repeating, and swapping one proxy for another is the same move
    wearing a fix's clothes.

    ⚠ The two halves fail in OPPOSITE directions, which is what makes the conjunction total: the
    count goes to zero when the router stops enforcing and the exit code stays non-zero for four
    unrelated reasons; the exit code goes to zero when the refusal is swallowed and the count stays
    high because the message was already printed. Requiring both is the only reading under which
    each mutation above is visible."""
    routing, returncode = _prepush_exit(wt)
    return routing > 0 and returncode != 0


# ⚠⚠ THE OBSERVABLE MUST NAME THE ENFORCEMENT ITSELF. These are `enforce_prepush_verdict`'s own
# `die()` strings and `cmd_prepush`'s success line — the only outputs that exist BECAUSE the
# enforcement ran. Anything printed earlier proves nothing about it.
_ENFORCE_DIE = ("push check(s) failed", "push verdict incomplete")
# ⚠ `prepush PASS` IS *NOT* ENFORCEMENT-EXCLUSIVE, and saying so would be the same mistake this
# check exists to catch. Measured by /rely 2026-08-25: it is printed four lines AFTER
# `enforce_prepush_verdict` returns, so with the enforcement call deleted `_assert_reached` does
# NOT fire — the exit-code leg is what catches that case. Kept because a genuine pass must still
# be accepted, but it carries no proof on its own; the die-strings above are the exclusive ones.
_ENFORCE_OK = "prepush PASS"


def _assert_reached(out):
    """Raise unless the run actually reached `enforce_prepush_verdict`.

    ⚠⚠ THE FIRST VERSION OF THIS CHECK WAS ITSELF DEFEATED, WHICH IS THE WHOLE LESSON. It looked
    for `"routing:"` / `"/rely"` — both printed by `report.plan()` BEFORE any routing happens — so
    it could only ever fire on an import crash. Measured by /rely 2026-08-25: with
    `enforce_prepush_verdict(bad)` DELETED FROM THE PROGRAM, `_prepush_exit` still reported BLOCKS
    and the probe still printed `13 of 13`, because an unguarded `reviewed.get` raised
    `AttributeError` and the traceback exited 1 — the SAME code the enforcement exits.

    **An exit code cannot distinguish a gate that blocked from a gate that DIED.** That is `DC-22`
    landing on the control built to close `DC-22`, twice in two rounds. So the needles below are
    the enforcement's own words, and a traceback is now an explicit failure rather than a pass."""
    if "Traceback (most recent call last)" in out:
        raise SystemExit(
            "probe baseline CRASHED. Its exit 1 is a traceback, not the enforcement — every\n"
            "  mutation would be compared against a run that died before the code under test.\n"
            "  Fix the crash; do NOT relax this assertion.")
    if "CANNOT JUDGE" in out:
        raise SystemExit(
            "probe baseline never reached the enforcement: prepush exited at 'CANNOT JUDGE'.\n"
            "  Fix the invocation; do NOT relax this assertion.")
    if not (any(n in out for n in _ENFORCE_DIE) or _ENFORCE_OK in out):
        raise SystemExit(
            "probe baseline produced NO output that only `enforce_prepush_verdict` can emit.\n"
            "  Expected one of %r (it refused) or %r (it passed). Seeing neither means the run\n"
            "  ended before the enforcement, however plausible its exit code looks."
            % (_ENFORCE_DIE, _ENFORCE_OK))


def _row_state(rows, needle):
    hits = [v for k, v in rows.items() if needle in k]
    if not hits:
        return "ABSENT"
    return "FAIL" if "FAIL" in hits else "ok"


# -- ⭐⭐ RLY41-1: the failing baseline is CONSTRUCTED, never inherited -------------------
#
# ⚠⚠ THIS CONTROL PREVIOUSLY GOT ITS RED BASELINE BY ACCIDENT, AND THE ACCIDENT WAS REPAIRED
# OUT FROM UNDER IT. The old comment said it plainly: the worktree "supplies the failing state
# for free — it is detached at HEAD and `.claude-local/` is gitignored, so the `/rely` signal is
# absent there and the routing legs FAIL. If that ever stops holding, this control has lost its
# teeth and must say so rather than pass." Review signals then moved from `*_cleared.txt` files
# to LEDGER RECORDS keyed on `(step, path, blob)` — service-side, so a detached worktree with the
# same tree now gets the SAME answers as the main checkout. The blind spot the baseline stood on
# was a real defect and removing it was correct; standing on it undeclared was this file's defect,
# not the migration's. 2026-08-29: the control did the one thing `RLY31-8` gave it the ability to
# do, and refused to certify a tree it could not judge.
#
# ⭐ SO: a MUST-FIRE / MUST-SUPPRESS PAIR, which is this bundle's house style and which this probe
# has never had. Not a before/after delta.
#
#     A  perturb a ROUTED subject    -> MUST FIRE     (routing > 0, exit != 0)
#     B  perturb an UNROUTED subject -> MUST SUPPRESS (routing == 0, exit == 0)
#
# Both runs sit at the SAME HEAD, so `--ranges HEAD~1..HEAD` resolves identically; both are
# index-dirty; both are single-file. **The only free variable is routing membership**, which is
# the property under test. B is the half that was missing: if perturbing an UNROUTED file turns
# the routing legs red, the routing SCOPE is wrong, and nothing here would have caught it.
#
# ⚠⚠ STAGED, NOT COMMITTED, AND NOT LEFT IN THE WORKING TREE.
#
# ⚠⚠ THE FIRST VERSION OF THIS BLOCK STATED A FALSE PREMISE, AND IT IS CORRECTED HERE RATHER THAN
# QUIETLY REWRITTEN, because this block is the durable record and a wrong reason in it outlives a
# wrong line of code. It said: "unstaged edit -> index unchanged -> `moved` does NOT fire". That is
# WRONG. `moved` DOES fire on an unstaged edit — `ledger_subjects(rels, INDEX)` DROPS paths that are
# worktree-modified (skip reason: "modified in the worktree since it was staged"), so
# `checker_blobs()` returns `<ABSENT>` for them, and `<ABSENT>` is in no record and counts as moved.
# Measured: the HEAD blob `761cf303` IS covered by four `rely` records, and the unstaged edit still
# produced a red. Neither session opened `ledger_subjects` before asserting this.
#
#     unstaged edit  -> path DROPPED from the index read -> `<ABSENT>` -> red BY ABSENCE
#     STAGED edit    -> index blob genuinely differs      -> red BY MISMATCH
#     committed      -> also red, but MOVES HEAD
#
# ⭐ SO STAGING IS STILL RIGHT, FOR A DIFFERENT REASON THAN THE ONE ORIGINALLY RECORDED: it makes
# the baseline red because a blob DISAGREES with the record, not because a path went missing from
# the comparison. Red-by-absence and red-by-mismatch are the same colour and different facts, and a
# control that constructs the first while claiming the second is exactly the "red for the wrong
# reason" defect (`RLY31-8`) it exists to prevent. The sentinel path would also go green the moment
# `ledger_subjects` changed how it reports skips — a dependency on an error channel rather than on
# the property.
#
# `batch.py` has two routing legs, not one. `_stale_at_tip` reads the PUSHED TIP; `moved` /
# `_moved_blocking` reads the INDEX — `checker_blobs()` is `ledger_subjects(rels, common.INDEX)`
# and says "from the INDEX" in its own docstring. Committing is not merely overkill: it moves HEAD,
# so `HEAD~1..HEAD` would resolve to the perturbation commit in one run and to the whole prior
# range in the other — two SCOPES compared as though only content differed, which is exactly the
# confound this pair exists to remove.
#
# ⭐ This is the same fact that built `unstage`: on this pipeline STAGING IS THE VERIFICATION STEP,
# because the ledger keys on the index.
#
# ⚠ THE FILENAME IS A DIAGNOSTIC AND NEVER A PASS CRITERION. The first draft of this asserted that
# the refusal NAMES the perturbed file. That is attempt 5 of the defect this file already died of
# four times: the filename appears in the routing FAIL row, which is printed BEFORE
# `enforce_prepush_verdict` runs, and `_ENFORCE_DIE`'s comment says "Anything printed earlier proves
# nothing about it." `_assert_reached`'s own first version died this way, grepping strings
# `report.plan()` prints before any routing happens. A grep for the filename is that same string one
# round later — satisfied by a run that printed the row and then had the enforcement deleted,
# swallowed or `sys.exit(0)`-ed. A named red ASSERTED on the wrong string is worse than an unnamed
# red, because it reads as more rigorous. Print it; do not assert it.

# ⚠ A: ROUTED (`^tools/verify/`) and a `CHECKERS` entry, because `moved` is computed over CHECKERS.
#     `_leg_of` -> "logic", and `_LEG_BLOCKING["logic"] is True`, so it blocks. Verified both.
_A_SUBJECT = "tools/verify/check_moved.py"
# ⚠ B: UNROUTED — outside `^tools/verify/`, `^tools/process/` and `^.github/workflows/`. MEASURED
#     to trip nothing rather than reasoned into; see `_require_suppressed`, which reads the ROWS and
#     not merely the tuple, because "(0, 0)" is also what "something fired and something else
#     cancelled" looks like. Do NOT weaken this to fit a subject: pick another subject.
_B_SUBJECT = "scripts/fonts/DejaVuSans.ttf"
# ⚠ INERT BY CONSTRUCTION: a trailing comment in a `.py`, trailing junk in a binary nothing parses
#     at push time. The perturbation must change the BLOB without changing BEHAVIOUR, or A's red
#     could come from the file breaking rather than from the routing leg.
_PERTURBATION = b"\n# probe: staged perturbation (RLY41-1)\n"


def _cannot_judge(msg):
    """Abort with exit 2 — "the control could not look", never "a mutation escaped".

    ⚠⚠ THE FIRST VERSION OF THESE HELPERS USED BARE `raise SystemExit(msg)`, WHICH EXITS 1 — the
    MUTATION-FAILURE code. So four of the seven "cannot judge" paths were indistinguishable from a
    real fail-open finding, in the same change that added an explicit zero-point refusal returning
    2. Caught by `/rely` 2026-08-29.

    ⚠ This is the `died`/`failed` distinction that `preflight` exists to preserve — "it failed" and
    "it never ran" are different facts, and only one means the gate actually judged your tree —
    leaking out of the control that was arguing for it. `hooks.py:347` then collapses 2 into 1
    anyway (`RLY41-2`, and `:318` already has the `== 2` pattern to match), but that is a separate
    defect: this side must emit the distinction before the reader's side can be blamed for erasing
    it."""
    print(msg)
    raise SystemExit(2)


def _staged_paths(wt):
    """Exactly what is in the worktree's index, as repo-relative paths."""
    p = subprocess.run(["git", "diff", "--cached", "--name-only"], cwd=wt,
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    return sorted(x for x in p.stdout.split() if x)


def _perturb_and_stage(wt, rel):
    """Perturb ONE named path in the worktree and stage it BY NAME. Returns (abspath, original).

    ⚠⚠ NAMED PATH, NEVER A BULK ADD, AND THE PROBE ASSERTS IT STAGED EXACTLY ONE THING. The
    worktree is seeded with ~63 working-tree copies from `tools/verify/` that are deliberately
    UNSTAGED — which is why `moved` compares HEAD blobs and the unperturbed run reads green. An
    `add -A` / `add .` / `add -u` would sweep all of them into the index.

    ⚠ AND THE TRAP IS CONDITIONAL, WHICH IS WHY THIS IS AN ASSERTION AND NOT JUST CARE. While the
    INVOKING checkout is clean the seeded bytes equal HEAD, so a bulk add moves no blob and the
    damage is invisible. The moment the invoking checkout is DIRTY, seeded bytes differ from HEAD,
    `moved` fires across the whole bundle, and BOTH A and B go red — B red for a reason that has
    nothing to do with its subject, which is `RLY31-8` (red for the wrong reason) landing on the
    control built to replace it. A bulk add would silently couple this probe's verdict to the
    cleanliness of whatever checkout invoked it. Checking is a property of the probe; being careful
    is only a property of whoever edits it next."""
    p = os.path.join(wt, *rel.split("/"))
    if not os.path.exists(p):
        _cannot_judge(
            "probe cannot perturb %r — it is not in the worktree. The subject must be a tracked\n"
            "  path; do NOT substitute a different one to make this run." % rel)
    before = _staged_paths(wt)
    if before:
        _cannot_judge(
            "probe expected a CLEAN index before perturbing, found staged: %s\n"
            "  A previous perturbation was not restored; the two would compound." % before)
    with io.open(p, "rb") as fh:
        original = fh.read()
    with io.open(p, "wb") as fh:
        fh.write(original + _PERTURBATION)
    add = subprocess.run(["git", "add", "--", rel], cwd=wt,
                         capture_output=True, text=True, encoding="utf-8", errors="replace")
    if add.returncode != 0:
        _cannot_judge("probe could not stage %r: %s" % (rel, (add.stdout + add.stderr).strip()))
    staged = _staged_paths(wt)
    if staged != [rel]:
        _cannot_judge(
            "probe staged %s, expected exactly [%r].\n"
            "  A bulk add would sweep in the ~63 seeded copies and make BOTH controls red for a\n"
            "  reason unrelated to their subjects. Stage by NAMED PATH; do NOT relax this."
            % (staged, rel))
    return p, original


def _restore_staged(wt, rel, p, original):
    """Put the bytes back and return the index to HEAD, asserting nothing is left staged."""
    with io.open(p, "wb") as fh:
        fh.write(original)
    subprocess.run(["git", "add", "--", rel], cwd=wt,
                   capture_output=True, text=True, encoding="utf-8", errors="replace")
    staged = _staged_paths(wt)
    if staged:
        _cannot_judge(
            "probe could not restore the index after perturbing %r; still staged: %s" % (rel, staged))


def _require_suppressed(wt, rel):
    """B: perturbing an UNROUTED subject must leave the routing legs silent AND prepush green.

    ⚠⚠ KNOWN-WEAK, LEDGERED AS DEBT (`RLY41-3`), AND SAYING SO IS THE POINT. `/rely` measured that
    NO staged perturbation of this subject can reach the prefix-routing leg at all: `checker_blobs()`
    iterates `CHECKERS` only, and `changed_files(ranges)` is a commit-range diff — B's subject is in
    neither, and matches no `/rely` pattern. So the original version of this function printed "the
    routing SCOPE is wrong", **a claim about a defect it structurally cannot detect**. "A checker
    that cannot fail is not a check" is this project's own phrase, and it applied here.

    ⚠ WHAT IT ACTUALLY TESTS, stated narrowly enough to be true: that staging an UNROUTED file does
    not turn prepush red. That catches a GROSS over-fire — routing widened to everything, or the
    index read losing its `CHECKERS` restriction — and it catches nothing subtler. It does NOT
    verify prefix membership. A stronger B needs a NEAR-MISS subject (a `.py` outside every routed
    prefix, e.g. under `scripts/`) so that a plausible scope widening, rather than only a total one,
    would trip it. Not done here: choosing it requires a measured run per candidate, and this tree
    is one `/rely` round from a push. `RLY41-3`.

    ⚠⚠ THE ROWS ARE COMPARED AGAINST A BASELINE TAKEN BEFORE THE PERTURBATION, and the first version
    was not. It read the guards rows only AFTER perturbing, so any row that was ALREADY red got
    blamed on B's subject — the same misattribution the zero point exists to prevent, one leg over,
    in the function whose failure text names the subject. `(0, 0)` is also what "something fired and
    something else cancelled" looks like, which is why the rows are read at all."""
    _rc0, base_rows = _guards_rows(wt)          # the origin, taken BEFORE anything moves
    p, original = _perturb_and_stage(wt, rel)
    try:
        routing, rc = _prepush_exit(wt)
        _rc, rows = _guards_rows(wt)
        # Only rows this perturbation CHANGED for the worse are attributable to it.
        # ⚠⚠ THE `"ok"` DEFAULT IS A FAIL-OPEN FIX, NOT TIDINESS. `base_rows.get(k)` returns None
        # for a row ABSENT from the baseline, and `None != "ok"` classified it as PRE-EXISTING — so
        # a row that appears only AFTER the perturbation, which is the most attributable evidence
        # there is, was excused instead of counted. Absent-at-baseline means "was not red then",
        # so it defaults to "ok" and lands in `fired`. Caught by `/rely` 2026-08-29.
        fired = sorted(k for k, v in rows.items()
                       if v != "ok" and base_rows.get(k, "ok") == "ok")
        already = sorted(k for k, v in rows.items()
                         if v != "ok" and base_rows.get(k, "ok") != "ok")
    finally:
        _restore_staged(wt, rel, p, original)
    print("    suppress control  unrouted %-34s routing=%d exit=%d" % (rel, routing, rc))
    if already:
        print("       (pre-existing red rows, NOT attributed to %s: %s)" % (rel, ", ".join(already)))
    if routing or rc or fired:
        print("    ** SUPPRESS CONTROL FAILED — an UNROUTED subject moved something. **")
        if routing or rc:
            print("       routing=%d exit=%d on a subject in neither CHECKERS nor the range."
                  % (routing, rc))
            print("       That is a GROSS over-fire: the index read or the routed set has lost its")
            print("       restriction. It is NOT evidence about prefix membership — see RLY41-3.")
        if fired:
            print("       rows this perturbation turned red: %s" % ", ".join(fired))
            print("       %r is not exempt from everything. PICK A DIFFERENT SUBJECT for B;" % rel)
            print("       do NOT weaken this control to accommodate it.")
        return False
    return True


def _require_fires(wt, rel):
    """A: perturbing a ROUTED subject must make the router BOTH say it refused AND refuse.

    ⚠⚠ THE VERDICT COMES FROM `_prepush_blocks`, AND THE FIRST VERSION OF THIS FUNCTION LIED ABOUT
    THAT. It said "Uses `_prepush_blocks`, UNTOUCHED" while actually recomputing
    `routing > 0 and rc != 0` inline — a COPY of the conjunction, in the fix for the control whose
    four previous deaths were all substitution, with a docstring asserting the opposite. A fifth
    attempt at that observable would have been made in `_prepush_blocks` and never reached here,
    silently. Caught by `/rely` 2026-08-29, and it is the sharpest instance of the class tonight
    precisely because the docstring made it unreadable as a copy.

    ⚠ THE NUMBERS ARE PRINTED, THE VERDICT IS CALLED. `_prepush_exit` supplies the diagnostic line;
    `_prepush_blocks` supplies the decision. That is two prepush runs rather than one, and the cost
    is the point: deriving the verdict from the numbers already in hand is exactly how the copy got
    written. The conjunction is four attempts of hard-won — neither half is the property, the
    property is that the two AGREE — so it is CALLED, never re-expressed.

    The perturbation is left STAGED on purpose: it is the red baseline the consumer-neuter cases
    below are measured against."""
    p, original = _perturb_and_stage(wt, rel)
    routing, rc = _prepush_exit(wt)          # diagnostic only — NOT the verdict
    blocks = _prepush_blocks(wt)             # THE verdict: the shared conjunction, not a copy
    print("    fire control      routed   %-34s routing=%d exit=%d" % (rel, routing, rc))
    if not blocks:
        print("    ** FIRE CONTROL FAILED — a STAGED perturbation of a ROUTED subject did not")
        print("       block. Either the routing legs stopped reading the index, or %r" % rel)
        print("       left CHECKERS. Fix the cause; do NOT relax this into a weaker observable. **")
        _restore_staged(wt, rel, p, original)
        return None
    return p, original


def mutations(ship, batch):
    """(label, path, transform, row-needle, required state) — see the module docstring."""
    return [
        # --- must stay GREEN: pure syntax, zero behavioural content ---------------------------
        ("RLY27-1  one space before the arg list", ship,
         lambda s: s.replace("batch.check_routing({}, ranges)", "batch.check_routing ({}, ranges)"),
         "release gate", "ok"),
        ("RLY27-3  list(...) wrapper around the call", ship,
         lambda s: s.replace(SHIP_LOOP,
                             "    _rows = list(batch.check_routing({}, ranges))\n"
                             "    for agent, ran, why, blocking in _rows:"),
         "release gate", "ok"),

        # --- must go RED: the enforcement is actually gone ------------------------------------
        ("NEUTER   release gate `if False:`", ship,
         lambda s: s.replace(SHIP_ANCHOR, "        if False:"),
         "release gate", "FAIL"),
        ("RLY27-7  release gate prints the flag, obeys nothing", ship,
         lambda s: s.replace(SHIP_ANCHOR,
                             '        print("routing:", blocking)\n        if False:'),
         "release gate", "FAIL"),
        ("RLY27-2  release gate as a comprehension with `and False`", ship,
         lambda s: s.replace(SHIP_LOOP + "\n" + SHIP_ANCHOR,
                             "    for agent, ran, why, blocking in [\n"
                             "            r for r in batch.check_routing({}, ranges) if False]:\n"
                             "        if True:"),
         "release gate", "FAIL"),
        ("NEUTER   release gate drops `and blocking`", ship,
         lambda s: s.replace(SHIP_ANCHOR, '        if agent == "/rely" and not ran:'),
         "release gate", "FAIL"),
        ("RLY27-4  verdict counts a sequence it did not print", batch,
         lambda s: s.replace('    return verdict_record("routing", routing_bad(rows))',
                             '    return verdict_record("routing", routing_bad([]))'),
         "push verdict", "FAIL"),
        ("NEUTER   cmd_prepush never calls routing_verdict", batch,
         lambda s: s.replace("    routing_verdict(state, ranges)\n", "    pass\n"),
         "prepush still calls", "FAIL"),
        # ⚠⚠ `RLY28-1` VERBATIM, AND IT MUST STAY **GREEN**. This is the mutation that defeated the
        # gate on 2026-08-23 — exit 1 → exit 0, "prepush PASS", three `/rely FAIL` rows on screen —
        # and it is here as a MUST-STAY-OK case because the producer now records its own count, so
        # discarding the return value at the call site changes nothing. ⚠ If a future version of
        # this control starts requiring RED here, someone has put the verdict back in the caller's
        # hands and the annihilation is live again.
        ("RLY28-1  caller annihilates the return value", batch,
         lambda s: s.replace("    routing_verdict(state, ranges)\n",
                             "    routing_verdict(state, ranges) * 0\n"),
         "push verdict registry", "ok"),
        # The other half of the same property: delete the producer's record and the registry must
        # fail CLOSED on the absence, never report zero failures.
        ("NEUTER   the producer stops recording its count", batch,
         lambda s: s.replace('    return verdict_record("routing", routing_bad(rows))',
                             "    return routing_bad(rows)"),
         "push verdict registry", "FAIL"),
        ("NEUTER   the logic leg downgraded to non-blocking", batch,
         lambda s: s.replace('_LEG_BLOCKING = {"logic": True, "switch": True, "docs": False}',
                             '_LEG_BLOCKING = {"logic": False, "switch": True, "docs": False}'),
         "fail-open leg still BLOCKS: logic", "FAIL"),

        # ⚠⚠ THE CONSUMER-SIDE NEUTERS, AND THEY ARE THE ONES THE FIRST FIVE CONTROLS COULD NOT SEE.
        # Observable is the PROCESS EXIT CODE of `batch.py prepush`, not a guards row — a row is
        # computed in guards' own frame and stays true no matter what `cmd_prepush` does with the
        # answer. Measured 2026-08-24: the mutation below took prepush to exit 0 / "prepush PASS"
        # under live FAIL rows while guards printed 81/81 ok and this probe printed 11 of 11.
        # Both REQUIRE `BLOCKS`: the enforcement must survive the caller trying to drop it.
        # MUST STAY BLOCKING: annihilating the caller's own count cannot hide a ROUTING failure,
        # because that count comes from the registry and never passes through this argument. This is
        # the property attempt six actually buys, stated so it can be measured rather than asserted.
        ("RLY28-1b caller annihilates the inline count", batch,
         lambda s: s.replace("    enforce_prepush_verdict(bad)",
                             "    enforce_prepush_verdict(bad * 0)"),
         EXIT_NEEDLE, "BLOCKS"),
        # MUST GO RED: deleting the enforcement outright is the one consumer-side move left, and the
        # AST row is what makes it loud. ⚠ Judged on the guards ROW, not the exit code — a deleted
        # enforcement genuinely does let prepush exit 0, so "still blocks" is not achievable here and
        # demanding it would be a control that can never pass.
        ("NEUTER   cmd_prepush discards the enforcement call", batch,
         lambda s: s.replace("    enforce_prepush_verdict(bad)", "    pass"),
         "prepush enforces the verdict", "FAIL"),

        # ⚠⚠ RLY36-1, AND THESE TWO ARE THE REASON `_prepush_blocks` IS A CONJUNCTION. Both break
        # the *doing* half of enforcement while leaving the *saying* half untouched, so the routing
        # count stays at its real value and only the exit code moves. /rely round 6 measured both
        # against the routing-count-only observable and the probe printed 13 of 13 over a push gate
        # that exits 0 with editorial FAIL, adversary FAIL, rely FAIL and four routing failures
        # printed above it. They require "PASSES": the observable must NOTICE that the process
        # stopped refusing. ⚠ MEASURED BOTH WAYS WHEN THIS LANDED, which is the only reason it is a
        # control and not a hypothesis: with the conjunct, 15 of 15 and both report PASSES; with the
        # conjunct removed (`return routing > 0`), 13 of 15 and both report BLOCKS. Exactly these two
        # moved — the other thirteen cases were unaffected, so the added conjunct does not over-fire. ⚠ If either of these ever reads "BLOCKS" again, someone has gone back to
        # watching one half, and the fourth instance of this defect is live.
        #
        # ⚠ `guards.py` cannot cover either one. Its row is an AST query for the NAME
        # `enforce_prepush_verdict` in a Load context, and its own comment claims the enumeration is
        # complete — "the only remaining consumer-side move is to DELETE the call". Wrapping the call
        # keeps the name in a Load context, and editing `die` never touches the call site at all;
        # both are instances the control's construction can never produce, which is detector 1 from
        # the brief. The unit of that check is a name; the unit of the claim is whether the push is
        # refused.
        ("RLY36-1a consumer swallows the refusal (try/except SystemExit)", batch,
         lambda s: s.replace("    enforce_prepush_verdict(bad)",
                             "    try:\n"
                             "        enforce_prepush_verdict(bad)\n"
                             "    except SystemExit:\n"
                             "        pass"),
         EXIT_NEEDLE, "PASSES"),
        # ⚠ WRITTEN AGAINST THIS ONE FIRST, per DC-26. `die` is the shared refusal primitive — it
        # prints "BLOCKED: ..." and exits. Flipping its exit status alone leaves every message,
        # every FAIL row and every count byte-identical, so nothing that reads OUTPUT can see it.
        ("RLY36-1b the refusal primitive exits 0", batch,
         lambda s: s.replace('    print("BLOCKED: %s" % msg)\n    sys.exit(1)',
                             '    print("BLOCKED: %s" % msg)\n    sys.exit(0)'),
         EXIT_NEEDLE, "PASSES"),
    ]


def main():
    tmp = tempfile.mkdtemp(prefix="zp_routing_probe_")
    wt = os.path.join(tmp, "wt")
    print("%s — mutation control for the behavioural routing routes" % SELF)
    add = subprocess.run(["git", "worktree", "add", "--detach", wt, "HEAD"],
                         capture_output=True, text=True, encoding="utf-8", errors="replace",
                         cwd=REPO)
    if add.returncode != 0:
        print("  cannot provision a worktree — REFUSING to run in the shared tree.")
        print(  (add.stdout + add.stderr).strip()[:500])
        shutil.rmtree(tmp, ignore_errors=True)
        return 2
    try:
        # The worktree is at HEAD; copy the WORKING copies in, so the control tests what is about to
        # be committed rather than what already was.
        #
        # ⚠⚠ THE WHOLE BUNDLE, NOT A HAND-KEPT LIST. This was seven hardcoded names while the
        # routed set is 96 entries, so 89 of them — INCLUDING `record.py` — ran from HEAD inside
        # the worktree. Measured by /rely 2026-08-25: planting a fail-open in `record.py` (routed,
        # and staged-modified at the time) that serves a fabricated `rely` record took
        # `batch.py prepush` from 4 routing failures to 2 — the `[logic]`, `[switch]` and `[docs]`
        # hash legs all vanished — while THIS probe still printed `13 of 13`, exit 0.
        #
        # The comment here used to say the copy exists "so the control tests what is about to be
        # committed rather than what already was". That was true for seven files and false for
        # eighty-nine, and a control whose stated scope is wider than its real one is the third
        # instance of `DC-22` found in this file in three rounds. Copying the directory removes
        # the hand-kept list entirely, so it cannot drift again as files are added.
        _copied = 0
        for _root, _dirs, _files in os.walk(os.path.join(REPO, "tools", "verify")):
            _dirs[:] = [d for d in _dirs if d != "__pycache__"]
            for _f in _files:
                _src = os.path.join(_root, _f)
                _rel = os.path.relpath(_src, REPO)
                _dst = os.path.join(wt, _rel)
                os.makedirs(os.path.dirname(_dst), exist_ok=True)
                shutil.copyfile(_src, _dst)
                _copied += 1
        # ⚠ SAY WHAT WAS COVERED. `probe-red` means something is broken; `probe-green` means only
        # that the copied set enforces. Routed files OUTSIDE this bundle still run from HEAD.
        print("  worktree seeded with %d working-tree file(s) from tools/verify/" % _copied)
        print("  (routed entries outside tools/verify/ run from HEAD — probe-green is scoped to "
              "the bundle)")
        ship = os.path.join(wt, "tools", "verify", "ship.py")
        batch = os.path.join(wt, "tools", "verify", "batch.py")

        # ⭐⭐ RLY41-1: CONSTRUCT the failing baseline. See the block above `mutations()`.
        # ⚠ B BEFORE A, and the order is load-bearing: B asserts a CLEAN index as its own
        # precondition and restores it, while A is left STAGED on purpose because it IS the red
        # baseline the consumer-neuter cases below are measured against. A first would trip B's
        # precondition and the failure would look like a defect in B.
        print("  controls (routing membership is the only variable):")
        # ⚠⚠ THE ZERO POINT, AND DROPPING IT WAS A REAL DEFECT IN THE FIRST DRAFT OF THIS PAIR.
        # A/B controls for routing MEMBERSHIP, but only if the unperturbed tree reads (0, 0). If it
        # does not, B's `routing > 0` is not attributable to B's subject at all — it was already
        # there — and the probe would report "the routing SCOPE is wrong" about a file that matches
        # no routed prefix. Measured 2026-08-29: the first run did exactly that, blaming
        # `scripts/fonts/DejaVuSans.ttf` for a routing count it had not caused.
        #
        # ⚠ This was in the design as an explicit precondition and I removed it as redundant to the
        # A/B pair. It is not redundant: A/B establishes a DIFFERENCE, and a difference is only
        # attributable from a known origin. Restored, and asserted rather than assumed.
        _r0, _c0 = _prepush_exit(wt)
        print("    zero point        unperturbed (index clean)          routing=%d exit=%d"
              % (_r0, _c0))
        if _r0 or _c0:
            print("    ** ZERO POINT IS NOT ZERO — the unperturbed tree already blocks. **")
            print("       Neither control below can attribute anything: any red they produce was")
            print("       already present. This is NOT a licence to subtract a baseline; a probe")
            print("       that measures from a moving origin is the defect, not the arithmetic.")
            print("       Fix the tree (or the invocation) so the unperturbed run is (0, 0).")
            return 2
        if not _require_suppressed(wt, _B_SUBJECT):
            return 2
        _fired = _require_fires(wt, _A_SUBJECT)
        if _fired is None:
            return 2
        _a_path, _a_original = _fired

        muts = mutations(ship, batch)
        _rc, base = _guards_rows(wt)
        needles = sorted({m[3] for m in muts})
        print("  baseline (unmutated):")
        bad = 0
        for n in needles:
            if n == EXIT_NEEDLE:
                # ⚠⚠ THE PRECONDITION, AND WITHOUT IT THE EXIT-CODE CASES PROVE NOTHING. Discarding
                # the verdict is only observable while there IS a verdict to discard: on a fully
                # green tree prepush exits 0 either way and the mutation looks harmless.
                #
                # ⚠⚠ THE FAILING STATE IS **CONSTRUCTED BY `_require_fires` ABOVE**, AND IS NOT
                # INHERITED. This comment used to say the worktree supplied it "for free" — detached
                # at HEAD with `.claude-local/` gitignored, so the `/rely` signal was absent there
                # and the routing legs failed. **THAT MECHANISM IS RETIRED** (see the RLY41-1 block
                # above `mutations()`): review signals moved to ledger records keyed on
                # `(step, path, blob)`, so a detached worktree now gets the SAME answers as the main
                # checkout, and the free red vanished. The old text survived here for one round after
                # being quoted as retired forty lines up — two copies of one premise in one file,
                # `DC-28`, corrected 2026-08-29.
                #
                # ⛔ DO NOT DELETE `_require_fires` AS REDUNDANT. `BLOCKS` below is true only
                # BECAUSE A staged a perturbation of a routed subject; remove it and every case here
                # goes vacuous again, which is the exact state this control refused to certify.
                state = "BLOCKS" if _prepush_blocks(wt) else "PASSES"
                print("    %-38s %s (prepush exit)" % (n, state))
                if state != "BLOCKS":
                    print("    ** BASELINE BROKEN: prepush already exits 0 unmutated, so the")
                    print("       consumer-neuter cases below cannot distinguish anything. **")
                    bad += 1
                continue
            print("    %-38s %s" % (n, _row_state(base, n)))
            if _row_state(base, n) != "ok":
                print("    ** BASELINE BROKEN for %r — every verdict below is meaningless **" % n)
                bad += 1
        if bad:
            return 2

        print()
        fails = 0
        for label, path, mutate, needle, want in muts:
            original = _read(path)
            mutated = mutate(original)
            if mutated == original:
                print("  !! %-52s MUTATION DID NOT APPLY — anchor missing" % label)
                fails += 1
                continue
            _write(path, mutated)
            try:
                if needle == EXIT_NEEDLE:
                    # ⚠ THE END-TO-END OBSERVABLE, AND IT IS THE ROUTING COUNT — NOT THE EXIT CODE.
                    # A `guards.py` row is computed by calling the verdict functions in guards' own
                    # frame, where the property survives any amount of discarding by `cmd_prepush`,
                    # so an end-to-end run is still the right shape. But the exit code is
                    # over-determined: review signals, the pushed-tip leg and a crash all drive it
                    # non-zero, so it stayed "BLOCKS" with the router deleted outright. The routing
                    # count is the number that moves if and only if routing enforcement moves —
                    # but it is only HALF the property, so `_prepush_blocks` requires the exit code
                    # to agree with it. See its docstring: four attempts, each substituting one
                    # proxy for another until both halves were watched at once.
                    got = "BLOCKS" if _prepush_blocks(wt) else "PASSES"
                else:
                    _rc, rows = _guards_rows(wt)
                    got = _row_state(rows, needle)
            finally:
                _write(path, original)
            ok = (got == want)
            fails += 0 if ok else 1
            print("  %-6s %-52s row[%s]=%s (want %s)"
                  % ("PASS" if ok else "**FAIL", label, needle, got, want))
        print()
        print("  RESULT: %d of %d behaved as required" % (len(muts) - fails, len(muts)))
        if fails:
            print("  ** A behavioural route did not respond to a real neuter. `CLAUDE.md` rung 5 and")
            print("     the stopping rule in queue/: this is the FOURTH defeat of this control, and")
            print("     the answer is to GIVE UP THE EXEMPTION, not to write attempt five. **")
        return 1 if fails else 0
    finally:
        subprocess.run(["git", "worktree", "remove", "--force", wt],
                       capture_output=True, text=True, cwd=REPO)
        subprocess.run(["git", "worktree", "prune"], capture_output=True, text=True, cwd=REPO)
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
