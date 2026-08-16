"""check_modal.py — flag MODAL CLAIMS that no footprint measurement can establish.

WHY THIS EXISTS (2026-08-03). A ZP-P remark-box sentence was wrong in SIX consecutive versions across
four gate rounds. Every round verified the wording against its sources and passed, because the sources
were always correct. The defect was one level down: the claim the sentence existed to support -- that
Mathlib's `Classical.choice` in `cofix_nonempty` is "an artifact, not a necessity" -- had never been
measured. One probe settled it: `QPF.Cofix` carries choice IN THE TYPE, so no proof of any statement
mentioning it can be clean, and "removable in principle" was unprovable as stated.

The same sweep then found a FALSE UNIVERSAL NEGATIVE live in a published PDF
(`ZP_Choice_Free_Core_Addendum`): "The framework has no proven-necessity case anywhere." Two taboo
reductions exist (`em_of_wellOrder_comparable`, `wem_of_fixedPointFree`). A 2026-08-01 sweep had
recorded both universal negatives as removed from the corpus -- it grepped `.lean` and missed a Python
build script, so the claim survived in RENDERED PUBLIC PROSE for two days.

THE RULE THIS ENFORCES
  * ACCIDENTAL is proved only by EXHIBITING the clean proof.
  * ESSENTIAL  is proved only by a REDUCTION to a recognised taboo.
  * `#print axioms` follows the STATEMENT, not the proof. A TYPE can carry an axiom -- then NO proof
    is clean and "removable" is false for every possible proof. MEASURE THE TYPE, not just the theorem.

WHAT IT DOES
  Flags modal-removability vocabulary ("not a necessity", "an artifact", "in principle", "removable",
  "eliminable") that is NOT accompanied by evidence vocabulary ("measured", "#print axioms",
  "UNCLASSIFIED", "retracted", "does not show", a reduction, or a named witness).

WHAT IT DELIBERATELY DOES NOT DO
  It cannot tell a live claim from a retraction of one -- retraction text quotes the error verbatim.
  So a hit is a PROMPT TO READ, never a verdict. Sites that measured honestly (e.g. SnapNucleus's
  "UNCLASSIFIED, not irreducible") are recognised by their evidence vocabulary and pass.

Usage (the exact invocation path is printed in this tool's own output):
    check_modal.py            # WARN (advisory, exit 0)
    check_modal.py --block    # exit 1 on any NEW unbaselined site
    check_modal.py --baseline # rewrite the baseline from current state

Baseline: modal_baseline.txt, beside this file -- grandfathers known-good sites so the gate fires
only on NEW ones (same as-touched model as check_pov.py). SHRINK it as files are touched; never grow
it deliberately. A muted gate is worse than none.
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common  # noqa: E402
from common import HERE, REPO, normalize_separators, strip_module_docstring  # noqa: E402
from vendored import is_vendored  # noqa: E402

# ⚠ THIS FILE WAS A LIBRARY UNTIL 2026-08-16, AND THAT WAS THE DEFECT (`DEFECTS.md` MIG-3).
# `check_negatives` and `check_figures` imported `tracked_md`, `normalize_separators` and
# `strip_module_docstring` FROM HERE, so two checkers depended on a peer's internals. Those three now
# live in `common.py`; nothing imports this module any more, and nothing should.
SELF = common.self_rel(__file__)
BASELINE = HERE / 'modal_baseline.txt'

# Claims about what CANNOT be proved. No footprint measurement establishes one.
#
# ⚠ EVERY SPACE IS `\s+`, NOT A LITERAL SPACE. Found while reproducing gate finding F-2: the first
# version used literal spaces, so a claim wrapped across a line -- "not a\n   necessity" -- was
# invisible. Lean docstrings and Python string literals wrap constantly, so that blind spot covered a
# large fraction of the corpus. This is CLAUDE.md's own "grep LOOSELY" rule, missed in the tool
# written to enforce it. Build the alternation from tokens so no space can be literal by accident.
_MODAL_PHRASES = [
    "not a necessity", "not asserted as a necessity", "rather than as a necessity",
    # ⚠ A BARE `artifact`, not just the three phrasings the first version listed. Gate finding O-2,
    # 2026-08-03: the corpus's actual wordings slipped straight through -- "as a QUOTIENT-LAYER
    # artifact, not an M-type one" and "the Mathlib M-type corecursion artifact" matched none of the
    # literal phrases, INCLUDING text written by the very commit the gate was reviewing. The `SCOPE`
    # guard is what keeps this from firing on ordinary-English "artifact"; do not narrow it here.
    "artifact",
    "choice-free in principle", "removable in principle",
    "could be removed", "can be removed", "is removable", "are removable",
    "eliminable", "not forced by the mathematics",
    # Added 2026-08-03: the corpus's own wordings kept slipping the literal list, including text
    # written by the commit a gate was reviewing at the time. Grep the CLAIM, not one phrasing.
    "not a fact about the mathematics", "not a fact about",
    # ⚠ NOT YET ADDED, and the omission is DELIBERATE and TRACKED -- see DEFECTS.md M-1.
    # Gate round 3 finding O-5 (2026-08-05) is correct: CLAUDE.md lists "inherited from Mathlib" as a
    # trigger phrase and this list has NO entry for it, so a provenance claim ("its choice is
    # inherited from Mathlib's PMF layer, it would carry it either way") reads as measured while the
    # checker reports 0 new -- and that claim sat at the exact site of a BEDROCK finding.
    # MEASURED before reverting: adding `"inherited from Mathlib"` here (scoped to the `Mathlib` form;
    # bare "inherited from" has an ordinary structural sense SCOPE cannot separate) yields
    # **22 new sites, 8 of them in published PDF build scripts** -- the surface the 2026-08-01 sweep
    # missed by grepping only `.lean`. Those 22 are UNREAD. This baseline's stated premise is that
    # every grandfathered site is "verified by READING it, not by counting", so blanket-baselining
    # them would falsify the one property that makes the baseline worth anything.
    # DO IT AS ITS OWN BATCH: add the phrase, read all 22, fix or baseline each with a reason.
]
MODAL = re.compile("|".join(r"\s+".join(re.escape(w) for w in p.split()) for p in _MODAL_PHRASES),
                   re.I)

# Evidence that the site did the work: a reduction, an honest tier, a retraction, or a TYPE-level
# measurement.
#
# ⚠ `#print axioms` IS DELIBERATELY *NOT* EVIDENCE HERE, and that is the whole point of this gate.
# A footprint measurement can never establish a modal claim -- it reports what one proof used. Listing
# it as evidence was the first version's bug, caught by injection probe: a planted false claim landed
# beside a PurityCheck block and was silently suppressed. PurityCheck blocks are exactly where these
# claims live, so that bug gave a free pass to the highest-risk sites. VERIFY THE DETECTOR BEFORE
# BELIEVING A ZERO.
#
# NOTE `measur` not `measured` -- the first tuning pass missed a correct site that said "measurement".
EVIDENCE = re.compile(
    r"measur|UNCLASSIFIED|retract|corrected"
    r"|does \*\*not\*\* show|does not show|no such re-proof|not attempted"
    r"|reduction|taboo|em_of_wellOrder_comparable|wem_of_fixedPointFree"
    # `axiom-free` alone was too blunt (gate finding, 2026-08-03): the word appears in correct AND
    # incorrect contexts, so on its own it suppressed sites that had done no work. It now counts only
    # when paired with a named carrier/witness, which is what makes it an EXHIBITED clean proof.
    r"|in the type|in the TYPE|strict_cofix_nonempty|open question|is open"
    # ⚠ `PFunctor.M is axiom-free` WAS listed here and is REMOVED (2026-08-03). It is the discredited
    # warrant itself: true of the type FORMER, silent about its ELIMINATORS (`M.children`/`M.dest`
    # carry choice). Listing it made the checker suppress the exact defect class that caused two
    # bedrock findings. An evidence list must never contain the fallacy it is meant to catch.
    r"|destructor|eliminator|M\.children|M\.dest|axiom-free witness"
    # An explicit non-claim is evidence: the site declined to assert eliminability.
    # `\(open\)` and `NOT claimed` added 2026-08-03 after the tightened pass flagged a scope box whose
    # whole content was a disclaimer. Do NOT relax this to a bare `open` -- that is a Lean keyword and
    # would suppress the entire corpus.
    r"|does not settle|honest tier|not classified|\(open\)|NOT claimed|not claimed"
    # Naming an EXHIBITED choice-free witness is exactly how an accidental claim is proved.
    r"|choice-free outright|choice-free \(his|Thm 1|Theorem 1",
    re.I)

# SCOPE GUARD. "artifact" has an ordinary English sense that has nothing to do with axioms
# ("an artifact of treating L as having a view from outside"). Four such false positives were
# measured on the first run. A modal phrase only counts when AXIOM vocabulary is nearby -- that is
# the actual scope of this rule, and narrowing beats tolerating: a gate that cries wolf gets muted.
SCOPE = re.compile(r"Classical\.choice|axiom|choice-free|#print axioms|propext|Quot\.sound|LLPO"
                   r"|excluded middle|constructive", re.I)

# "artifact" has a second ordinary sense in THIS corpus specifically: `checkable artifact` is the
# project's own phrase for a Lean file you can build, and it sits right next to axiom vocabulary, so
# SCOPE alone cannot separate them. Measured 2026-08-03: widening MODAL to a bare `artifact` produced
# 20 hits, 19 of them this sense -- and 1 real find (`Ordinal/Kruskal.lean`, "the Classical.choice
# here is a route artifact"). Exclude the compounds, keep the pattern; dropping it would lose the find.
# Enumerating the ordinary compounds does not converge -- "checkable", "curated", "axiom-profile",
# "method-", "proof ", "artifact-first" all appeared. The reliable discriminator is that the MODAL
# sense is predicated of a footprint, so `Classical.choice` sits right beside it (Kruskal.lean: "the
# `Classical.choice` here is a route artifact" -- 30 chars). The ordinary sense names a FILE, and
# `Classical.choice` is nowhere near. So: bare `artifact` requires that token within ARTIFACT_NEAR.
ARTIFACT_NEAR = 110
ARTIFACT_SCOPE = re.compile(r"Classical\.choice", re.I)

# ⚠ TWO-TIER EVIDENCE (gate finding F-2, 2026-08-03). A single wide window produced a FALSE NEGATIVE:
# a live "a Mathlib M-type artifact, not a necessity" passed because the word "measured" sat six lines
# away describing a DIFFERENT measurement ("the measured invariant of the fork"). Proximity is not
# aboutness. So:
#   WEAK evidence -- "measur", "in the type", a named witness -- must appear in the SAME SENTENCE as
#   the claim, because those words are common and only count when they are about THIS claim.
#   STRONG evidence -- "retracted", "UNCLASSIFIED", "does not settle", "NOT claimed" -- may sit in the
#   wider window, because they are structural markers about the passage rather than stray tokens.
WINDOW = 420        # wide window: scope guard + strong evidence
SENTENCE = 260      # tight window: weak evidence must be this close (roughly one sentence)

STRONG = re.compile(
    r"UNCLASSIFIED|retract|corrected|does not settle|honest tier|not classified"
    r"|\(open\)|NOT claimed|not claimed|does \*\*not\*\* show|does not show"
    r"|no such re-proof|not attempted|open question|is open",
    re.I)

# register.md's Notes column and each build script's module docstring are THE CHANGELOG OF RECORD
# (CLAUDE.md exempts them). They quote what past versions said, verbatim and on purpose -- exactly the
# retraction-pollution case. Structurally exempt, not grandfathered -- and shared, so the exemption
# cannot hold in one checker and lapse in another (`common.SKIP_NAMES`). What stays here is only what
# is genuinely THIS checker's: its own source and its own baseline.
SKIP_NAMES = {'check_modal.py', 'modal_baseline.txt'}


def targets():
    """The shared enumerator. Scope, skips and the vendored exemption all live in `common`.

    Vendored backports are EXEMPT STRUCTURALLY (see vendored.py). Nothing here fires on them today,
    so that closes a latent hole rather than a live one: a backport whose header discusses what is
    "removable" or "in principle" is upstream's prose, not a claim of ours to measure."""
    return common.targets(skip_names=SKIP_NAMES, is_vendored=is_vendored)


def scan_text(t):
    """Modal-claim hits in one already-normalized string, as (offset, phrase).

    EXTRACTED so `--selftest` exercises the real decision path. `scan()` walks a file tree, so any
    control would otherwise test a hand-copied replica — and a replica drifts from the thing it
    certifies, which is the mirror problem this project keeps paying for."""
    out = []
    for m in MODAL.finditer(t):
        win = t[max(0, m.start() - WINDOW): m.start() + WINDOW]
        if not SCOPE.search(win):
            continue              # ordinary-English "artifact" etc., not an axiom claim
        if m.group(0).lower().strip() == 'artifact':
            tight = t[max(0, m.start() - ARTIFACT_NEAR): m.start() + ARTIFACT_NEAR]
            if not ARTIFACT_SCOPE.search(tight):
                continue          # names a FILE ("checkable artifact"), not a footprint
        if STRONG.search(win):
            continue              # structural marker: retraction, honest tier, explicit non-claim
        near = t[max(0, m.start() - SENTENCE): m.start() + SENTENCE]
        if EVIDENCE.search(near):
            continue              # weak evidence, but close enough to be ABOUT this claim
        out.append((m.start(), re.sub(r'\s+', ' ', m.group(0))))
    return out


# --------------------------------------------------------------------------- controls
# ⚠ Phrases are taken FROM `_MODAL_PHRASES` and the evidence patterns, never paraphrased. A guessed
# vocabulary produced three dead controls in `check_pov.py` on the same day.
_S = 'The `Classical.choice` in this proof is '        # supplies SCOPE (axiom context)

MUST_FIRE = [
    ('bare eliminability claim', _S + 'an artifact, not a necessity.'),
    ('removable in principle', _S + 'removable in principle, though nobody has done it.'),
    ('wrapped across a line',                       # Lean docstrings wrap constantly
     'The `Classical.choice` here is not a\nnecessity; it is inherited plumbing.'),
]
MUST_SUPPRESS = [
    ('measured, in the same sentence',
     _S + 'an artifact — measured 2026-08-03, the footprint is [propext].'),
    ('explicit non-claim', _S + 'an artifact. UNCLASSIFIED: not claimed, open question.'),
    ('retraction', 'CORRECTED: the claim that `Classical.choice` was removable is retracted.'),
    ('a named exhibited witness',
     _S + 'an artifact; `strict_cofix_nonempty` is the axiom-free witness.'),
    ('ordinary English, no axiom scope',
     'The checkable artifact is a Lean build, linked in the first sentence.'),
]


def selftest():
    # ⚠ THE INVERSION USED TO BE HAND-WRITTEN HERE, AND IT WAS WRITTEN WRONG ONCE: the suppression
    # loop reused the must-fire loop's `bad += 0 if got else 1` and reported FAIL(5) while printing
    # `ok` on all five. The summary contradicting the detail is the only reason it was caught.
    # `common.fire_suppress` takes the expected polarity as a parameter, so there is no second loop
    # to get backwards -- in this file or in the fourteen others that had their own copy.
    return common.fire_suppress(
        MUST_FIRE, MUST_SUPPRESS,
        lambda text: scan_text(normalize_separators(text)),
        'unmeasured modal claim')


def scan():
    hits = []
    for p, rel in targets():
        try:
            t = p.read_text(encoding='utf-8')
        except (OSError, UnicodeDecodeError):
            continue
        stripped = strip_module_docstring(t, rel)
        t = normalize_separators(stripped)
        # Line numbers come from `stripped`, NOT from `t`: normalize_separators consumes the newline
        # in a Python adjacent-string-literal join, so counting on `t` drifts (measured: line 78
        # reported as 40). `strip_module_docstring` IS line-count-preserving, so `stripped` is safe.
        for off, phrase in scan_text(t):
            ln = stripped.count('\n', 0, off) + 1
            hits.append((rel, ln, phrase))
    return sorted(set(hits))


def load_baseline():
    return common.load_baseline(BASELINE)


def key(h):
    return '%s|%s' % (h[0], h[2].lower())


def main():
    block = '--block' in sys.argv
    hits = scan()

    if '--baseline' in sys.argv:
        # ⚠ LF, via the shared writer. A bare `write_text` emits CRLF on Windows, and this file is
        # TRACKED — so regenerating the baseline used to break `check_invariants` on the next run.
        common.write_text_lf(
            BASELINE,
            '# check_modal.py baseline - grandfathered modal claims lacking evidence vocabulary.\n'
            '# SHRINK as files are touched; never grow deliberately. Format: <path>|<phrase>\n'
            '#\n'
            '# ⚠ ADD ENTRIES BY HAND. This regeneration DISCARDS EVERY COMMENT: it once took this\n'
            '# file from 26 lines to 5, destroying the per-site reading notes the header requires.\n'
            + ''.join(sorted(key(h) + '\n' for h in hits)))
        print('baseline written: %d site(s)' % len(hits))
        return 0

    base = load_baseline()
    new = [h for h in hits if key(h) not in base]

    print('=' * 40)
    print('  modal-claim check')
    print('  grandfathered (baseline): %d' % len(base))
    print('  NEW unmeasured modal claims: %d' % len(new))
    for rel, ln, phrase in new:
        print('    %s:%d  [%s]' % (rel, ln, phrase))
    if new:
        print()
        print('  A modal claim ("not a necessity" / "an artifact" / "in principle" /')
        print('  "removable" / "eliminable") asserts what CANNOT be proved. No footprint')
        print('  measurement establishes one:')
        print('    ACCIDENTAL -> prove it by EXHIBITING the clean proof.')
        print('    ESSENTIAL  -> prove it by a REDUCTION to a taboo.')
        print('  `#print axioms` follows the STATEMENT: a TYPE carrying an axiom makes')
        print('  "removable" false for every possible proof. MEASURE THE TYPE.')
        print('  Then state what was measured, mark it UNCLASSIFIED, or delete the claim.')
    print('=' * 40)

    return 1 if (block and new) else 0


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(selftest())
    sys.exit(main())
