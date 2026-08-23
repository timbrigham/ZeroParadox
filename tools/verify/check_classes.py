#!/usr/bin/env python3
"""check_classes.py - was the DEGENERACY question asked of each requirements class?

WHY THIS EXISTS (2026-08-07, Tim's call).
A requirements class is only informative if something FAILS to be a member. The corpus has
repeatedly shipped classes whose membership was cited as meaningful and which turned out to be
satisfiable by anything:

  WheelValuationStructure  - constant-top valuation on any commutative ring   -> WVSNondegenerate added
  AbstractSelfApp          - trivialSelfApp inhabits it                       -> gauge present
  InfinitudeFloor          - characterised as EXACTLY `Infinite a`            -> gauge added 2026-08-07
  SeparatedSuccession      - Unit + always-true relation discharges every field (found 2026-08-07)

That is one design habit, not four incidents: writing a class without asking what it EXCLUDES.

WHAT THIS CHECKS - and what it deliberately does NOT.
It cannot decide degeneracy; that requires BUILDING a witness, which is a synthesis task. It checks
the cheaper and still-useful thing: does the corpus show any sign the question was ASKED? Evidence
counts as any of --
  * a non-degeneracy predicate            (`<Name>Nondegenerate`, or `Nondegenerate` in the file)
  * a degenerate/trivial witness          (`trivial<Name>`, `degenerate<Name>`, `bookkeeping...`)
  * an explicit no-go section             (`NO-GO` in the declaring file)
  * a recorded verdict in prose           (`degenerate` / `degeneracy` / `vacuous` in the file)

Same design as check_pov.py: it enforces that a convention was FOLLOWED, never that a claim is true.

USAGE (run with no arguments to have the exact invocation path printed back)
  check_classes.py            # WARN  (pre-commit)
  check_classes.py --block    # BLOCK (pre-push), NEW sites only
  check_classes.py --baseline # regenerate the grandfather list

Baselined like check_pov.py / check_modal.py: the corpus already carries many un-audited classes, and
a gate that blocks everything on day one gets muted. Blocks on NEW classes only. SHRINK the baseline as
files are touched; never grow it deliberately.
"""

import os
import re
import sys

# Roots come from `common` — one derivation for the whole bundle; the baseline travels WITH the
# checker, so a move never strands it. SELF is derived, never written down: a hardcoded invocation
# path is a copy of the path and drifts exactly like a mirrored file does.
#
# ⚠ COERCED TO `str`, not re-derived. This module speaks `os.path`; `common` speaks `pathlib`. One
# line of type conversion is not a second definition — change the layout and there is still exactly
# one place to edit.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402
from vendored import is_vendored  # noqa: E402

HERE = str(common.HERE)
REPO = str(common.REPO)
SRC = str(common.SRC)
SELF = common.self_rel(__file__)
BASELINE = os.path.join(HERE, "class_baseline.txt")

# `class Foo` / `structure Foo` / `class Foo (a : T) extends ...`
# ⚠ The name class must accept UNICODE. `[A-Za-z0-9_']` truncated `structure Q₂BallDepth` to `Q`
# at the subscript, which then sat in the baseline as an entry matching no declaration in the
# corpus. Same defect as the `[^']+` name pattern in the CI report: an ASCII identifier class in a
# corpus whose names routinely carry ₂ ε ω ℚ. `\w` is Unicode-aware in Python 3.
#     `[^\W\da-z]` is "a word character that is neither a digit nor ASCII-lowercase" — i.e. any
#     uppercase or non-ASCII letter. It closes the LEADING case too (`ΔUnauditedThing`, `εTest`),
#     which `[A-Z]` missed entirely, while still rejecting `lowercaseThing`. Verified against both.
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(class|structure)\s+([^\W\da-z][\w']*)", re.M | re.U)

# Mathlib-style bundled algebra we did not author; not requirements classes in the ZP sense.
SKIP_NAMES = {"PurityCheck"}


def evidence_patterns(name):
    """Signs that the degeneracy question was asked, SPLIT BY WHETHER THEY NAME THE CLASS.

    CHK-3: five of the original eight patterns are name-agnostic (`NO-GO`, `vacuous`,
    `degenerate…`), and they were searched over the WHOLE FILE. So one gauge cleared every class in
    the file, and the word "vacuous" anywhere cleared all of them. Measured 2026-08-09: a `NO-GO`
    section written for `APG` silently cleared `DecorationUniverse`, declared 60 lines later in the
    same file and never audited.

    Returns (named, generic). A NAMED pattern may match anywhere in the file - it says which class it
    is about, so distance does not matter. A GENERIC one must fall inside a window around the
    declaration, the way `check_prose.py` scopes a gloss to the line above its `#check`."""
    n = re.escape(name)
    named = [
        re.compile(n + r"Nondegenerate"),
        # ⚠ ANCHOR THE TAIL. `\btrivialFoo` is prefix-open, so it also matches `trivialFooBar` —
        # a witness for the LONGER class silently clears the SHORTER one, which is the same
        # one-gauge-clears-many defect as CHK-3 arriving through the named patterns instead of the
        # generic ones. Two real pairs sit in position today (`InfinitudeFloor`/`...Inversion`,
        # `Wheel`/`WheelValuationStructure`); neither fires yet, so this was latent, not live.
        # `(?![A-Za-z0-9_])` and not `\b`: `\b` after a word character is satisfied by `_`, which is
        # legal in a Lean identifier and would leave `trivialFoo_bar` matching.
        re.compile(r"\btrivial" + n + r"(?![A-Za-z0-9_])", re.I),
        re.compile(r"\bdegenerate" + n + r"(?![A-Za-z0-9_])", re.I),
    ]
    # ⚠ NO GENERIC PATTERNS. They were the whole of CHK-3: `NO-GO` / `vacuous` / `degenerate`
    # matched file-wide, so one gauge cleared every class in the file. Scoping them to a window
    # around the declaration was NOT enough — a control showed a gauge naming a DIFFERENT class,
    # sitting immediately above `structure Foo`, still cleared `Foo`. The gauge must NAME the class
    # it is about; anything weaker answers "was a question asked here?" rather than "was it asked
    # about this?".
    return named


# Lines of context around a declaration in which a GENERIC gauge is taken to be about it. A NO-GO
# section usually sits just above the declaration, but sometimes just below it, so the window runs
# both ways. ⚠ The first version ran -30/+5 and missed a gauge 5 lines BELOW its declaration by one
# line — an off-by-one that reads as "unaudited" and manufactures work.
EVIDENCE_BEFORE, EVIDENCE_AFTER = 30, 40

# Vocabulary that marks a passage as a degeneracy gauge rather than incidental prose.
GAUGE = re.compile(r"NO-GO|degenerat|vacuous|nondegenerate|newtype|trivially inhabited|"
                   r"nothing (?:can |could |else )?fail|bundled proposition", re.I)
NEAR = 400   # chars either side of a class-name mention that count as "beside it"


def named_gauge(text, name):
    """True if the class is NAMED within `NEAR` chars of gauge vocabulary, in EITHER order.

    Order matters and a lookahead cannot express both directions: a section headed
    `NO-GO gauge — what fails to be a `Foo`?` puts the keyword BEFORE the name, while
    `Foo is degenerate` puts it after. Checking a window around each mention handles both, and
    keeps the evidence tied to the class it names rather than to the file it sits in.

    WARNING: the DECLARATION ITSELF must not count as a mention. A control caught this - with
    `structure Foo where` matching the name, any gauge within `NEAR` chars of the declaration read
    as "named", which silently collapses this back into the proximity check it replaced."""
    for m in re.finditer(r"`?\b" + re.escape(name) + r"\b`?", text):
        if re.search(r"\b(class|structure)\s+$", text[max(0, m.start() - 12): m.start()]):
            continue                       # this occurrence IS the declaration
        lo, hi = max(0, m.start() - NEAR), m.end() + NEAR
        if GAUGE.search(text[lo:hi]):
            return True
    return False


def lean_files():
    """Vendored backports are EXEMPT STRUCTURALLY (see vendored.py). Nothing here fires on them
    today, so this closes a latent hole: a future backport declaring a class must not be reported
    as an un-audited class of ours."""
    for dirpath, _dirnames, filenames in os.walk(SRC):
        for fn in filenames:
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                if not is_vendored(p, os.path.relpath(p, REPO)):
                    yield p


def scan():
    """-> list of (relpath, lineno, kind, name) for classes with NO evidence."""
    unaudited = []
    for path in lean_files():
        try:
            text = open(path, encoding="utf-8").read()
        except (OSError, UnicodeDecodeError):
            continue
        rel = os.path.relpath(path, REPO).replace("\\", "/")
        for m in DECL.finditer(text):
            kind, name = m.group(1), m.group(2)
            if name in SKIP_NAMES:
                continue
            named = evidence_patterns(name)
            # The gauge must NAME this class - see the CHK-3 note in evidence_patterns().
            if any(p.search(text) for p in named) or named_gauge(text, name):
                continue
            lineno = text.count("\n", 0, m.start()) + 1
            unaudited.append((rel, lineno, kind, name))
    return sorted(unaudited)


def key(entry):
    rel, _lineno, kind, name = entry
    return "%s::%s %s" % (rel, kind, name)   # line-number-independent


def load_baseline():
    return common.load_baseline(BASELINE)


def main():
    block = "--block" in sys.argv
    if "--baseline" in sys.argv:
        common.refuse_baseline_write("class_baseline.txt")
    rebuild = "--baseline" in sys.argv

    found = scan()

    if rebuild:
        common.write_text_lf(
            BASELINE,
            "# check_classes.py baseline - requirements classes whose DEGENERACY question\n"
            "# was never asked, grandfathered at creation time. SHRINK as files are touched;\n"
            "# never grow deliberately. Regenerate with --baseline only after a real audit.\n"
            + "".join(key(e) + "\n" for e in found))
        print("baseline written: %d entries" % len(found))
        return 0

    base = load_baseline()
    new = [e for e in found if key(e) not in base]

    # ⚠ Recorded before the reporting branches: this function has several exits and a record
    # emitted on only some of them would make coverage depend on the verdict.
    if "--record" in sys.argv[1:]:
        _bad = {e[0] for e in new}
        _scanned = [os.path.relpath(p, REPO).replace("\\", "/") for p in lean_files()]
        _rc = common.emit_verdict("check_classes",
                                  ok_rels=[r for r in _scanned if r not in _bad],
                                  bad_rels=sorted(_bad),
                                  reason="requirements class added with no degeneracy verdict")
        if _rc:
            return _rc

    print("=" * 40)
    print("  requirements-class degeneracy check")
    print("  classes with the question unasked: %d" % len(found))
    print("  grandfathered (baseline):          %d" % len(base))
    print("  NEW un-audited classes:            %d" % len(new))
    print("=" * 40)

    if new:
        print()
        print("  A requirements class is only informative if something FAILS to be a member.")
        print("  For each below: BUILD the trivial witness, or prove you cannot. Both answers are")
        print("  worth having. Record the verdict in the declaring file (a NO-GO section, a")
        print("  `Nondegenerate` predicate, or a named degenerate witness).")
        print()
        for rel, lineno, kind, name in new:
            print("    %s:%d" % (rel, lineno))
            print("        %s %s" % (kind, name))
        print()

    if block:
        if new:
            print("BLOCKED: %d requirements class(es) added without a degeneracy verdict." % len(new))
            return 1
        print("OK: no new un-audited requirements classes.")
        return 0

    if new:
        print("WARNING ONLY (no --block). Audit these before pushing.")
    return 0


# --------------------------------------------------------------------------- controls
# ⚠ These were RUN on 2026-08-09 and not retained — they lived in a throwaway heredoc, so the
# validation could not be repeated by anyone. A validation nobody can re-run is a claim about a
# past session, not a control. Transcribed here so `--selftest` reproduces it.
#
# The MUST-FIRE cases encode CHK-3: evidence used to match file-wide, so a gauge about a DIFFERENT
# class, or one merely near the declaration, cleared it. The gauge must NAME the class.

MUST_FIRE = [                      # must NOT be treated as audited
    ("bare class, no gauge", "structure Foo where\n  a : Nat\n"),
    ("gauge names a DIFFERENT class",
     "/-! NO-GO: `Bar` is vacuous. -/\nstructure Foo where\n  a : Nat\n"),
    ("gauge far away, unnamed",
     "/-! NO-GO gauge here. -/\n" + "\n" * 60 + "structure Foo where\n  a : Nat\n"),
    ("generic gauge nearby, unnamed",
     "/-! This is vacuous on a subsingleton. -/\nstructure Foo where\n  a : Nat\n"),
]
MUST_SUPPRESS = [                  # must be treated as audited
    ("gauge above, names it",
     "/-! NO-GO — what fails to be a `Foo`? Nothing. -/\nstructure Foo where\n  a : Nat\n"),
    ("gauge BELOW, names it",
     "structure Foo where\n  a : Nat\n\n/-! NO-GO gauge — `Foo` is trivially inhabited. -/\n"),
    ("named far away",
     "structure Foo where\n  a : Nat\n" + "\n" * 80 + "/-! `Foo` is degenerate on Unit. -/\n"),
    ("Nondegenerate predicate",
     "structure Foo where\n  a : Nat\ndef FooNondegenerate : Prop := True\n"),
    ("named trivial witness",
     "structure Foo where\n  a : Nat\ndef trivialFoo : Foo := ⟨0⟩\n"),
]


def _audited(text, name="Foo"):
    return any(p.search(text) for p in evidence_patterns(name)) or named_gauge(text, name)


def selftest():
    # ⚠ THE POLARITY IS INVERTED RELATIVE TO EVERY OTHER CHECKER, AND THAT IS NOT A MISTAKE.
    # `_audited` reports that a class was CLEARED, so this gate FIRES when it is False. A must-fire
    # control therefore expects `_audited == False`. Writing that as a hand-rolled loop is exactly
    # how `check_modal`'s selftest once tallied FAIL(5) while printing `ok` five times; passing the
    # expected polarity as a parameter makes it a value rather than a line of arithmetic.
    bad = common.run_controls([
        ("MUST FIRE (must NOT be treated as audited)", MUST_FIRE,
         _audited, False, "FALSELY CLEARED"),
        ("MUST SUPPRESS (must be treated as audited)", MUST_SUPPRESS,
         _audited, True, "FALSE POSITIVE"),
    ], width=32)
    # ⚠ THE SCOPE PIN (SCOPE-3). This checker walks `ZeroParadox/` privately. The controls above run
    # on planted strings in memory, so they are scope-independent by construction and cannot notice
    # if the walk stops covering the corpus.
    # ⚠ THE VOCABULARY PIN (PAT-1). The controls above prove the patterns they exercise;
    # this proves the rest are still there. Measured before it was written: 30 of 34
    # list-shaped patterns could be deleted with every control green, and the compiled
    # regexes carrying the rest of the vocabulary were pinned by nothing at all.
    print("PATTERNS")
    bad += common.check_vocabulary("check_classes", globals())
    print("SCOPE")
    bad += common.check_scope(
        "check_classes",
        [os.path.relpath(p, REPO).replace("\\", "/") for p in lean_files()])
    if bad:
        print("\nselftest: FAIL (%d)" % bad)
    return 1 if bad else 0


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    sys.exit(main())
