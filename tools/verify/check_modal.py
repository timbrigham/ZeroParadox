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
  Since `MODAL-2` (2026-10-14) it also flags IMPOSSIBILITY vocabulary ("cannot be", "cannot satisfy",
  "could not be", "is impossible" and kin), under the same axiom-vocabulary scope guard. A proved
  impossibility passes by naming its theorem: a backticked corpus theorem in the same sentence, or a
  bare one in a PDF build script. A regex checks only that SOME corpus theorem is named there, never
  that it proves the claim. Engineer's Takes are exempt (Tim's voice), as in `check_prose`.

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
import check_prose  # noqa: E402  the Engineer's Take detector, reused not restated (`mask_takes`)

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

# IMPOSSIBILITY claims (`MODAL-2`, ruled by Tim 2026-10-14). "X cannot be equipped with Y" asserts that
# no construction exists, which is a modal claim exactly like "not a necessity" -- and this list had
# no entry for it, so the checker reported 0 new on a tree carrying two live false impossibilities
# (*cannot be EQUIPPED*, later its inverse *can always be equipped*). The ruling: every impossibility
# form must carry a pointer to the proving theorem or a dated measurement. Kept under the same SCOPE
# guard as the eliminability phrases -- measured 2026-10-14 without it: 338 new sites in 133 files,
# 187 of them under `tools/` and `.claude/` rather than the corpus; with it, 32 in 25.
_IMPOSSIBILITY_PHRASES = [
    "cannot be", "can not be", "can't be", "can’t be", "could not be",
    "cannot satisfy", "cannot exist", "cannot hold", "is impossible",
]
IMPOSSIBLE = re.compile("|".join(r"\s+".join(re.escape(w) for w in p.split())
                                 for p in _IMPOSSIBILITY_PHRASES), re.I)

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
    r"|choice-free outright|choice-free \(his|Thm 1\b|Theorem 1\b",
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
#   wider window for an ELIMINABILITY hit, as structural markers about the passage.
#   An IMPOSSIBILITY hit uses neither tier. Its evidence is `IMPOSSIBLE_EVIDENCE`, in the claim's
#   own sentence: an unrelated "Typo corrected." two paragraphs up passed a new claim through the
#   window, and "a Lebesgue measure" or "dimension reduction" in the sentence itself passed too.
WINDOW = 420        # wide window: scope guard + strong evidence (eliminability hits)
SENTENCE = 260      # tight window: weak evidence must be this close (roughly one sentence)

STRONG = re.compile(
    r"UNCLASSIFIED|retract|corrected|does not settle|honest tier|not classified"
    r"|\(open\)|NOT claimed|not claimed|does \*\*not\*\* show|does not show"
    r"|no such re-proof|not attempted|open question|is open",
    re.I)

# IMPOSSIBILITY EVIDENCE (Tim, 2026-10-15): only (a) an evidence theorem that is a real corpus
# declaration, (b) a DATED measurement, (c) an explicit status marker. Plain English evidence words
# ("measure", "reduction", "corrected", "Theorem 1") excuse nothing here.
IMPOSSIBLE_EVIDENCE = re.compile(
    r"em_of_wellOrder_comparable|wem_of_fixedPointFree|strict_cofix_nonempty"
    r"|\bmeasured\b(?:\W+\w+){0,3}?\W+20\d\d-\d\d(?:-\d\d)?\b"
    r"|(?-i:\bUNCLASSIFIED\b)|\bnot\s+claimed\b|\(open\)|\bopen\s+question\b|\bretracted\b",
    re.I)

# THE THEOREM-FORM POINTER (`MODAL-2`, Tim 2026-10-14). A PROVED impossibility passes by naming the
# declaration that proves it: a backticked Lean name in the SAME SENTENCE as the claim. What is
# CHECKED is weaker -- that some corpus theorem is named there; whether it proves the claim is the
# reader's call. It applies to
# IMPOSSIBLE hits only. For an eliminability claim a theorem name proves nothing -- "the
# `Classical.choice` in `foo` is an artifact" names a declaration and is exactly the unmeasured claim.
#
# ⚠ THE NAME MUST RESOLVE, TO A THEOREM. A backticked token counts only if it names a `theorem` or
# `lemma` in `ZeroParadox/**/*.lean`, so an invented name is not a pointer, and neither is a class or
# a def -- the first run without that restriction passed a site on `ValBridge` (a class) and another
# on `L` (a functor `def`), neither of which proves anything. Names resolve as the full qualified name
# or with the house `ZeroParadox.` prefix dropped: `theorem f_snap_impossible` inside `namespace
# ZeroParadox` answers to `f_snap_impossible` and `ZeroParadox.f_snap_impossible`, never to
# `Nat.f_snap_impossible`. A theorem in a DEEPER namespace keeps its qualifier -- `theorem hs` in
# `ZeroParadox.ProvabilityLogic` answers to `ProvabilityLogic.hs`, not to `hs` -- because the same
# run passed a site whose backticked `hs` was a local hypothesis that happened to share that short
# name. Mathlib names do NOT resolve -- the index is the corpus, read from disk -- so a claim proved
# upstream cites the corpus re-export or carries a dated measurement instead.
#
# ⚠ SENTENCE, NOT WINDOW. The corpus is dense with backticked names, so the ±SENTENCE window would
# find one beside almost any claim -- F-2's "proximity is not aboutness" again. The span is cut at
# sentence ends (`.`/`!`/`?` before whitespace, or a blank line), with dots INSIDE backticks masked
# so `Ordinal.foo` does not end a sentence, and still capped at SENTENCE either side.
# ⚠ CLOSING MARKUP DOES NOT HIDE A SENTENCE END: `.**`, `.)`, `."`, `.'`, a build script's `.'),`,
# a closing tag `.</b>`, a footnote `.[^1]` and a link `.](x.md)` end one, as do `.<br/>`, `.—` and
# a literal `\n` in a Python string. Without that, `**claim.** See `thm`` passed on the NEXT
# sentence's name -- and reportlab's `<b>…</b>` lead sentence occurs 103 times under `scripts/`.
# In `.md`/`.lean` a line opening with a list marker or heading starts a sentence, and a heading
# line ends one, punctuated or not (`LINE_START`).
DECL_TOKEN = re.compile(r"`@?([^\W\d][\w'.!?]*)`")
DECL_SRC = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|scoped)\s+)*"
    r"(?:theorem|lemma)\s+([^\W\d][\w'.!?]*)")
SCOPE_OPEN = re.compile(r"^\s*(?:noncomputable\s+)?(namespace|section|mutual)\b[ \t]*([\w'.]*)")
SCOPE_END = re.compile(r"^\s*end\b")
SENTENCE_END = re.compile(
    r"[.!?](?:[*_)\]\"'”’`]|</\w+>|\[\^[^\]\s]*\]|\]\([^)\s]*\))*"
    r"(?:(?<=[)\]\"'”’*_>])[,;])?(?:(?=\s|\Z|\\n)|<br\s*/?>|[—–])|\n[ \t]*\n")
LINE_START = re.compile(r"^[ \t]*(?:#{1,6}|[-*+]|\d{1,3}[.)])[ \t]", re.M)
STAR_BULLET = re.compile(r"^[ \t]*\*(?=[ \t])", re.M)   # restored after normalisation (`prepare`)
WRAP_LINE = re.compile(r"[\w,][ \t]*$")                  # a line that stops mid-sentence

decl_index = None       # lazily built: each corpus theorem, qualified and `ZeroParadox.`-relative


def _strip_lean_comments(src):
    """Lean source with comments removed. Block comments NEST, so this is a depth counter, not a
    regex -- the same reasoning as `batch.strip_comments`, which is not imported because a checker
    must not depend on a peer's internals (`MIG-3`). Without it, a docstring line opening with
    `theorem` would index a phantom declaration and give an invented name a free pass."""
    out, depth, i, n = [], 0, 0, len(src)
    while i < n:
        two = src[i:i + 2]
        if two == "/-":
            depth, i = depth + 1, i + 2
        elif two == "-/" and depth:
            depth, i = depth - 1, i + 2
        elif depth:
            if src[i] == "\n":
                out.append("\n")
            i += 1
        elif two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def declared_names():
    """Each `theorem`/`lemma` under `ZeroParadox/`, read from DISK, as its fully qualified name and
    as that name relative to the house `ZeroParadox` namespace."""
    global decl_index
    if decl_index is not None:
        return decl_index
    names = set()
    for p in sorted((REPO / 'ZeroParadox').rglob('*.lean')):
        try:
            names |= index_source(p.read_text(encoding='utf-8', errors='replace'))
        except OSError:
            continue
    decl_index = names
    return names


def index_source(src):
    """The theorem names one Lean source declares, comments stripped. Split out of
    `declared_names` so `--selftest` can hold the comment stripping."""
    names = set()
    stack = []
    for line in _strip_lean_comments(src).split('\n'):
        o = SCOPE_OPEN.match(line)
        if o:
            stack.append(o.group(2) if o.group(1) == 'namespace' else '')
            continue
        if SCOPE_END.match(line):
            if stack:
                stack.pop()
            continue
        d = DECL_SRC.match(line)
        if not d:
            continue
        name = d.group(1)
        parts = (name[len('_root_.'):] if name.startswith('_root_.')
                 else '.'.join([s for s in stack if s] + [name])).split('.')
        names.add('.'.join(parts))
        if parts[0] == 'ZeroParadox' and len(parts) > 1:
            names.add('.'.join(parts[1:]))
    return names


def _sentence(t, lo, hi, lines=False):
    """`(start, end)` of the sentence holding `t[lo:hi]`, capped at SENTENCE either side. `lines`
    (a `.md`/`.lean` file) adds the list-item and heading boundaries of `LINE_START`."""
    a, b = max(0, lo - SENTENCE), min(len(t), hi + SENTENCE)
    seg = re.sub(r"`[^`\n]*`", lambda m: 'x' * len(m.group(0)), t[a:b])
    bounds = [(m.start(), m.end()) for m in SENTENCE_END.finditer(seg)]
    for m in (LINE_START.finditer(seg) if lines else ()):
        if m.start() == 0 and a > 0 and t[a - 1] != '\n':
            continue              # the cap fell mid-line; this is no line start
        bounds.append((m.start(), m.start()))
        nl = seg.find('\n', m.end())
        if nl >= 0 and m.group(0).strip().startswith('#'):
            bounds.append((nl, nl))
    left = max((y for x, y in bounds if y <= lo - a), default=0)
    right = min((x for x, y in bounds if x >= hi - a), default=len(seg))
    return a + left, a + right


# BUILD SCRIPTS NAME THEOREMS BARE (Tim, 2026-10-14; R-LEANPDF: "declaration names stay BARE and
# unprefixed"). A backtick would print literally in the PDF, so in `scripts/build_*.py` -- and ONLY
# there -- a bare token counts too, under the same resolution rules. The discriminator against an
# English word that happens to equal a theorem name is that the bare token must contain an UNDERSCORE
# or a DOT, which no English word does and the corpus's theorem names nearly always do
# (`c_t_iz_null_balance`, `ZeroParadox.no_quine_atom`). A sentence-final dot is stripped first, so
# "converges." is not a dotted token.
BUILD_SCRIPT = re.compile(r"^scripts/build_[^/]*\.py$")
BARE_DECL_TOKEN = re.compile(r"(?<![\w.`])([^\W\d][\w']*(?:[_.][\w']+)+)")

# ⚠ A THEOREM NAMED AS THE SUBJECT IS NOT ITS OWN POINTER. "`em_of_wellOrder_comparable` cannot be
# dismissed as an implication with an unsatisfiable antecedent" makes a claim ABOUT the theorem; what
# would prove it is a witness of the antecedent, which that sentence names only as a Mathlib lemma. So
# the subject does not count, and neither does any other mention of its name in the sentence.
# RULE: a name before the phrase is its subject when, once parenthetical, dash- or comma-bounded
# asides and short prepositional phrases are deleted from the gap, no `,;:()—–` and no other
# backticked name remain ("`thm`, as stated, cannot be", "`thm` at `r` cannot be"). A citation still
# counts: "a snap (`thm`) cannot be" and "by `thm`, X cannot be" keep a break in the gap. Cost:
# "`thm` shows X cannot be" reads as a subject too; write "X cannot be (`thm`)".
CLAUSE_BREAK = re.compile(r"[,;:()—–]")
ASIDE = re.compile(r"\([^()]*\)|—[^—]*—|–[^–]*–|,[^,;:()]*,"
                   r"|\s(?:at|over|on|in|of|for|with|under|from)(?:\s+(?:the|an?))?"
                   r"\s+(?:`[^`\n]*`|[\w.']+)")


def _subjects(t, s, lo):
    """The names in `t[s:lo]`, backticked or bare, that are the claim's SUBJECT."""
    out = set()
    for pat in (DECL_TOKEN, BARE_DECL_TOKEN):
        for m in pat.finditer(t, s, lo):
            gap = ASIDE.sub(' ', t[m.end():lo])
            if not CLAUSE_BREAK.search(gap) and not DECL_TOKEN.search(gap):
                out.add(m.group(1).rstrip('.!?'))
    return out


def cites_declaration(t, lo, hi, bare=False, lines=False):
    """True iff the claim's sentence names a corpus theorem that is not the claim's own subject:
    backticked everywhere, or bare as well when `bare` (a build script). A regex checks only that
    SOME corpus theorem is named there, never that it is the one proving the claim."""
    known = declared_names()
    s, e = _sentence(t, lo, hi, lines)
    subj = _subjects(t, s, lo)
    pats = (DECL_TOKEN, BARE_DECL_TOKEN) if bare else (DECL_TOKEN,)
    for pat in pats:
        for m in pat.finditer(t, s, e):
            name = m.group(1).rstrip('.!?')
            if name in subj:
                continue          # the theorem is the subject of the claim, not evidence for it
            if name in known:
                return True
    return False


def _ident_char(c):
    return c.isalnum() or c in "_.'"


def _evidence_in(seg, pat, known):
    """True iff `pat` matches `seg` as a WORD, or as a name that is a corpus theorem. A match inside
    a backticked or identifier-shaped token (`em_of_wellOrder_comparable_zz`) is not evidence."""
    ticks = [(m.start(), m.end()) for m in re.finditer(r"`[^`\n]*`", seg)]
    for m in pat.finditer(seg):
        tick = next(((x, y) for x, y in ticks if x <= m.start() < y), None)
        if tick:
            tok = seg[tick[0] + 1:tick[1] - 1].lstrip('@')
        else:
            i, j = m.start(), m.end()
            while i > 0 and _ident_char(seg[i - 1]):
                i -= 1
            while j < len(seg) and _ident_char(seg[j]):
                j += 1
            words = m.group(0).split()   # a phrase match ("measured 2026-10-14") is judged at its edges
            edges = (seg[i:m.start()] + words[0], words[-1] + seg[m.end():j])
            name, tok = seg[i:j].strip(".'"), ' '.join(w.strip(".'") for w in edges)
            if '_' not in tok and '.' not in tok:
                return True       # an ordinary word or marker ("retracted", "UNCLASSIFIED")
            tok = name
        if tok.rstrip('.!?') in known:
            return True
    return False


def sentence_evidence(t, lo, hi, lines=False):
    """True iff `IMPOSSIBLE_EVIDENCE` sits in the claim's own sentence, outside every mention of
    its subject's name -- `em_of_wellOrder_comparable` is evidence, and as the subject it would
    excuse itself."""
    s, e = _sentence(t, lo, hi, lines)
    seg = t[s:e]
    for name in _subjects(t, s, lo):
        seg = re.sub(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'])", lambda m: ' ' * len(m.group(0)), seg)
    known = declared_names()
    return _evidence_in(seg, IMPOSSIBLE_EVIDENCE, known)


def mask_takes(text, rel):
    """`text` with every Engineer's Take line blanked, length and line count preserved.

    ⚠ THE TAKE DETECTOR IS `check_prose`'s, IMPORTED, NOT RESTATED (Tim, 2026-10-14): `TAKE_RE` finds
    the heading and `countable_block_lines` decides where the Take ends -- the next heading or `---`,
    else the end of its block. A line is in the Take exactly when that function does not count it.
    The block is each `/-! ... -/` in a `.lean` file, as `check_prose.scan_file` delimits them, and
    the whole file in a `.md` companion, which has no block syntax. The Take is Tim's voice, never
    a claim an agent may edit, so a hit there is not owed work by anyone this checker reports to.
    ⚠ This makes `check_prose` a library of this checker -- the `MIG-3` shape. Changing its Take
    detector changes this checker's behaviour while only `check_prose.py`'s blob moves."""
    lines = text.split('\n')
    if not (rel.endswith('.lean') or rel.endswith('.md')) or \
            not any(check_prose.TAKE_RE.search(ln) for ln in lines):
        return text
    blocks, i = [], 0
    if rel.endswith('.md'):
        blocks = [(0, len(lines) - 1)]
    while rel.endswith('.lean') and i < len(lines):
        st = lines[i].strip()
        if st.startswith('/-!') and '-/' not in st[3:]:
            j = next((k for k in range(i + 1, len(lines)) if '-/' in lines[k]), len(lines) - 1)
            blocks.append((i, j))
            i = j
        i += 1
    orig = list(lines)      # the detector reads the UNMASKED lines; a blanked heading would close it
    for a, b in blocks:
        if not any(check_prose.TAKE_RE.search(orig[k]) for k in range(a, b + 1)):
            continue
        prev = 0
        for k in range(a, b + 1):
            n = check_prose.countable_block_lines(orig, a, k)[0]
            if n == prev:
                lines[k] = ' ' * len(lines[k])
            prev = n
    return '\n'.join(lines)

# RELEASES.md and each build script's module docstring are THE CHANGELOG OF RECORD
# (`tools/process/document-workflow.md` exempts them; CLAUDE.md does NOT, and this comment claimed it
# did until 2026-09-24 -- R-REGISTER says the opposite, that a version appears in exactly one rendered
# place). They quote what past versions said, verbatim and on purpose -- exactly the
# retraction-pollution case. Structurally exempt, not grandfathered -- and shared, so the exemption
# cannot hold in one checker and lapse in another (`common.SKIP_NAMES`). What stays here is only what
# is genuinely THIS checker's: its own source and its own baseline.
# ⚠ register.md was named here too and was dropped from the shared set 2026-09-24 (`REGDESC-1`): the
# Notes column it referred to is gone, so there is no past wording left in that file to protect.
SKIP_NAMES = {'check_modal.py', 'modal_baseline.txt'}

# `--selftest` floors on the real `targets()`: live 2026-10-15 was 227 / 71 / 43, floors are half.
FLOOR_LEAN, FLOOR_MD, FLOOR_BUILD = 113, 35, 21


def targets():
    """The shared enumerator. Scope, skips and the vendored exemption all live in `common`.

    Vendored backports are EXEMPT STRUCTURALLY (see vendored.py). Nothing here fires on them today,
    so that closes a latent hole rather than a live one: a backport whose header discusses what is
    "removable" or "in principle" is upstream's prose, not a claim of ours to measure."""
    return common.targets(skip_names=SKIP_NAMES, is_vendored=is_vendored)


def prepare(text, rel):
    """One file's text as `scan_text` reads it: Engineer's Takes blanked, then separators joined.
    Shared by `scan()` and `--selftest`, so the controls run the order the tree scan runs.
    ⚠ `normalize_separators` blanks a line-leading `*` (a C-comment continuation), which in `.md`
    and `.lean` is a BULLET that `LINE_START` needs, so it is put back; offsets are unchanged.
    Not in `.lean` when the line before is unterminated prose (`WRAP_LINE`) and no bullet itself:
    that `*` continues a wrapped comment ("cannot\\n * be"). Two `* ` lines in a row stay bullets."""
    masked = mask_takes(text, rel)
    t = normalize_separators(masked)
    if (rel.endswith('.md') or rel.endswith('.lean')) and len(t) == len(masked):
        t = list(t)
        for m in STAR_BULLET.finditer(masked):
            prev = masked[masked.rfind('\n', 0, max(0, m.start() - 1)) + 1:max(0, m.start() - 1)]
            if rel.endswith('.lean') and m.start() > 0 and WRAP_LINE.search(prev) \
                    and not LINE_START.match(prev):
                continue          # a C-style continuation of the line above, not a bullet
            t[m.end() - 1] = '*'
        t = ''.join(t)
    return t


def scan_text(t, rel=''):
    """Modal-claim hits in one already-normalized string, as (offset, phrase).

    EXTRACTED so `--selftest` exercises the real decision path. `scan()` walks a file tree, so any
    control would otherwise test a hand-copied replica — and a replica drifts from the thing it
    certifies, which is the mirror problem this project keeps paying for. `rel` decides only whether
    a BARE theorem name counts as the pointer (`BUILD_SCRIPT`) and whether line starts can bound a
    sentence (`.md`/`.lean`, `LINE_START`)."""
    rel = rel.replace('\\', '/')
    bare = bool(BUILD_SCRIPT.match(rel))
    lines = rel.endswith('.md') or rel.endswith('.lean')
    out = []
    hits = [(m, False) for m in MODAL.finditer(t)] + [(m, True) for m in IMPOSSIBLE.finditer(t)]
    for m, impossibility in sorted(hits, key=lambda h: h[0].start()):
        win = t[max(0, m.start() - WINDOW): m.start() + WINDOW]
        if not SCOPE.search(win):
            continue              # ordinary-English "artifact" etc., not an axiom claim
        if impossibility and cites_declaration(t, m.start(), m.end(), bare, lines):
            continue              # a proved impossibility, pointing at the theorem that proves it
        if m.group(0).lower().strip() == 'artifact':
            tight = t[max(0, m.start() - ARTIFACT_NEAR): m.start() + ARTIFACT_NEAR]
            if not ARTIFACT_SCOPE.search(tight):
                continue          # names a FILE ("checkable artifact"), not a footprint
        # Evidence for an impossibility, weak AND strong, must sit in ITS sentence, as its pointer
        # must: the windows passed on "measured" in the next section's heading and on an unrelated
        # "corrected" two paragraphs up. Eliminability hits keep the windows.
        if impossibility:
            if sentence_evidence(t, m.start(), m.end(), lines):
                continue
            out.append((m.start(), re.sub(r'\s+', ' ', m.group(0))))
            continue
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
_I = 'In the constructive setting, a snap cannot be realized in a dense ordered field'  # SCOPE too

MUST_FIRE = [
    ('bare eliminability claim', _S + 'an artifact, not a necessity.'),
    ('removable in principle', _S + 'removable in principle, though nobody has done it.'),
    ('wrapped across a line',                       # Lean docstrings wrap constantly
     'The `Classical.choice` here is not a\nnecessity; it is inherited plumbing.'),
    # MODAL-2. `f_snap_impossible` is a real corpus theorem (`ZeroParadox/Reals/OrderedField.lean`,
    # inside `namespace ZeroParadox`); `f_snap_impossible_zz` and the `Nat.` form name nothing.
    # `ValBridge` is a real corpus CLASS (`ZeroParadox/Valuation/ScaleBridge.lean`), and `hs` a real
    # theorem one namespace deeper (`ZeroParadox.ProvabilityLogic.hs`, `Settheory/Loeb.lean`).
    ('impossibility, no pointer', _I + '.'),
    ('impossibility, invented pointer', _I + ' (`f_snap_impossible_zz`).'),
    ('impossibility, pointer under a wrong namespace', _I + ' (`Nat.f_snap_impossible`).'),
    ('impossibility, pointer to a class, not a theorem', _I + ' (`ValBridge`).'),
    ('impossibility, sub-namespace theorem named bare', _I + ' (`hs`).'),
    ('impossibility, pointer in the NEXT sentence',
     _I + '. See `f_snap_impossible` for a different fact.'),
    ('impossibility, pointer in the PREVIOUS sentence',
     'See `f_snap_impossible` for a different fact. ' + _I + '.'),
    ('bold-closed claim, pointer in the next sentence',
     '**' + _I + '.** See `f_snap_impossible` for a different fact.'),
    ('paren-closed claim, pointer in the next sentence',
     '(' + _I + '.) See `f_snap_impossible` for a different fact.'),
    ('impossibility, weak evidence in the PREVIOUS sentence', 'We measured X. ' + _I + '.'),
    ('a theorem pointer does not excuse eliminability',
     _S + 'an artifact, not a necessity (`f_snap_impossible`).'),
    ('impossibility, pointer past the SENTENCE cap',
     _I + ' ' + 'and so on ' * 30 + '(`f_snap_impossible`).'),
    ('impossibility, STRONG word paragraphs away', 'Typo corrected.\n\n' + _I + '.'),
    ('eliminability, STRONG word past the WINDOW',
     'Typo corrected. ' + 'x ' * 300 + _S + 'an artifact, not a necessity.'),
    ('impossibility, evidence name inside an invented name',
     _I + ' (`em_of_wellOrder_comparable_zz`).'),
    ('impossibility, Theorem 12 is not Theorem 1', _I + ', as Theorem 12 of a survey notes.'),
    # Tim's ruling: plain English evidence words excuse no impossibility.
    ('impossibility, "measure" in its sentence', _I + ', carrying a Lebesgue measure.'),
    ('impossibility, "corrected" in its sentence', _I + ', as the corrected draft says.'),
    ('impossibility, "reduction" in its sentence', _I + ', even after a dimension reduction.'),
    ('impossibility, "Theorem 1" in its sentence', _I + ', as Theorem 1 of a survey notes.'),
    ('impossibility wrapped onto a C-style ` * ` continuation line',
     '/-! In the constructive setting the snap cannot\n * be realized in a dense ordered field. -/\n'),
    ('impossibility, an UNDATED "measured" in its sentence', _I + ', as measured by the probe.'),
    ('impossibility, a lowercase "unclassified" in its sentence', _I + ', an unclassified remark.'),
    ('impossibility, the date more than 3 tokens after "measured"',
     _I + ', measured by a long chain of several further words in 2026-10-14.'),
    ('impossibility, subject search reaches past 40 characters',
     'In the constructive setting, `f_snap_impossible` in the case of the dense ordered field of'
     ' real numbers cannot be dismissed.'),
    ('cannot satisfy, no pointer',
     'Without an extra axiom, this carrier cannot satisfy the cover law.'),
    ('is impossible, no pointer', 'Under the Foundation axiom, self-membership is impossible here.'),
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
    ('impossibility, pointer to a real theorem', _I + ' (`f_snap_impossible`).'),
    ('impossibility, namespace-qualified pointer', _I + ' (`ZeroParadox.f_snap_impossible`).'),
    ('impossibility in ordinary English, no axiom scope',
     'The meeting cannot be moved to Tuesday because the room is booked.'),
    ('impossibility, a dated measurement in its sentence', _I + ', measured 2026-10-14.'),
    ('impossibility, an explicit status marker in its sentence', _I + ' (UNCLASSIFIED).'),
]


def selftest():
    # ⚠ THE INVERSION USED TO BE HAND-WRITTEN HERE, AND IT WAS WRITTEN WRONG ONCE: the suppression
    # loop reused the must-fire loop's `bad += 0 if got else 1` and reported FAIL(5) while printing
    # `ok` on all five. The summary contradicting the detail is the only reason it was caught.
    # `common.fire_suppress` takes the expected polarity as a parameter, so there is no second loop
    # to get backwards -- in this file or in the fourteen others that had their own copy.
    bad = common.fire_suppress(
        MUST_FIRE, MUST_SUPPRESS,
        lambda text: scan_text(prepare(text, 'probe.lean'), 'probe.lean'),
        'unmeasured modal claim')
    # The surface-dependent rules, each run under the path that decides it. LOCAL lists, not module
    # constants: a constant-cased list would be collected into the vocabulary pin as if it were one.
    # `padding` is a real corpus theorem whose name is an English word (`ZeroParadox.padding`).
    build, md, lean, py = 'scripts/build_probe.py', 'Probe.md', 'Probe.lean', 'tools/probe.py'
    # Each item's "text" is a `(path, source)` pair, so the shared harness keeps the polarity.
    surface_fire = [
        ('bare pointer outside a build script', (md, _I + ' (f_snap_impossible).')),
        ('bare invented name in a build script', (build, _I + ' (f_snap_impossible_zz).')),
        ('bare English-word theorem in a build script', (build, _I + ' without padding.')),
        ('theorem as the SUBJECT, backticked',
         (md, 'In the constructive setting, `f_snap_impossible` cannot be dismissed as vacuous.')),
        ('theorem as the SUBJECT, bare in a build script',
         (build, 'In the constructive setting, f_snap_impossible cannot be dismissed as vacuous.')),
        ('theorem as the SUBJECT, a word in the gap',
         (md, 'In the constructive setting, `f_snap_impossible` simply cannot be dismissed.')),
        ('SUBJECT theorem whose name is in EVIDENCE',
         (md, 'In the constructive setting, `em_of_wellOrder_comparable` cannot be dismissed.')),
        ('build script: claim literal, pointer in the next literal',
         (build, "li('" + _I + ".'),\n        li('f_snap_impossible: a different fact.')")),
        ('build script: tag-closed claim, pointer next',
         (build, "p('<b>" + _I + ".</b> f_snap_impossible is a different fact.')")),
        ('md: list item claim, pointer in the next item',
         (md, '- ' + _I + '\n- `f_snap_impossible` is a different fact.')),
        ('md: `*` bullet claim, pointer in the next bullet',
         (md, '* ' + _I + '\n* `f_snap_impossible` is a different fact.')),
        ('lean: `*` bullet claim in a docstring, pointer in the next bullet',
         (lean, '/-!\n* ' + _I + '\n* `f_snap_impossible` is a different fact.\n-/\n')),
        ('md: heading claim, pointer on the next line',
         (md, '## ' + _I + '\n`f_snap_impossible` is a different fact.')),
        ('SUBJECT behind a comma-bounded aside',
         (md, 'In the constructive setting, `f_snap_impossible`, as stated, cannot be dismissed.')),
        ('SUBJECT behind a prepositional phrase',
         (md, 'In the constructive setting, `f_snap_impossible` at `r` cannot be dismissed.')),
        ('bare EVIDENCE-name SUBJECT in .md',
         (md, 'In the constructive setting, em_of_wellOrder_comparable cannot be dismissed.')),
        ('build script: evidence word inside a bare invented name',
         (build, "p('" + _I + " (em_of_wellOrder_comparable_zz).')")),
        ('bare EVIDENCE-name SUBJECT in a build script',
         (build, "p('In the constructive setting, em_of_wellOrder_comparable cannot be dismissed.')")),
        ('lean: claim after the Take is closed by a heading',
         (lean, "/-!\n## Engineer's Take\nTim's words.\n\n## Notes\n" + _I + '.\n-/\n')),
        ('lean: claim in a docstring after the Take block',
         (lean, "/-!\n## Engineer's Take\nTim's words.\n-/\n/-- " + _I
          + '. -/\ntheorem x : True := trivial\n')),
        ('md: claim in a section before the Take',
         (md, '# T\n\n## Notes\n\n' + _I + ".\n\n## Engineer's Take\n\nTim's words.\n")),
        ('py: a Take heading exempts nothing in .py', (py, "# Engineer's Take\n" + _I + '.')),
        ('py: impossibility wrapped onto a ` * ` continuation line',
         (py, 'x = 1\ny = """In the constructive setting a snap cannot\n * be realized here."""\n')),
    ]
    surface_suppress = [
        ('bare pointer in a build script', (build, _I + ' (f_snap_impossible).')),
        # The real shape: a Python list item opening with the theorem name, `li('name: ...')`.
        ('bare pointer just after a string quote',
         (build, "li('f_snap_impossible: in the constructive setting a snap cannot be realized.')")),
        ('parenthesised citation before the phrase',
         (md, 'In the constructive setting, a snap (`f_snap_impossible`) cannot be realized here.')),
        ('citation after the phrase',
         (md, 'In the constructive setting, a snap cannot be realized here (`f_snap_impossible`).')),
        ('"by `thm`," opening the sentence',
         (md, 'By `f_snap_impossible`, in the constructive setting a snap cannot be realized here.')),
        ("lean: claim inside an Engineer's Take",
         (lean, "/-!\n# Title\n\n## Engineer's Take\n" + _I + '.\n-/\n')),
        ("md: claim inside an Engineer's Take", (md, "# T\n\n## Engineer's Take\n\n" + _I + '.\n')),
    ]
    # Through `scan_file`, the path `scan()` takes, so how `rel` reaches `scan_text` is held too.
    bad += common.fire_suppress(
        surface_fire, surface_suppress,
        lambda item: scan_file(item[1], item[0]),
        'surface rules: build scripts, subjects, Takes', width=50)
    # The declaration index reads code only: a theorem named in a comment is no pointer.
    bad += common.fire_suppress(
        [('a real declaration', 'theorem phantom_thm : True := trivial\n')],
        [('inside a docstring', '/--\ntheorem phantom_thm : True\n-/\ntheorem x : True := trivial\n'),
         ('inside a nested block comment', '/- /- a -/\ntheorem phantom_thm : True\n-/\n')],
        lambda src: 'phantom_thm' in index_source(src),
        'declaration index', width=50)
    # The real `scan()` over a temporary tree, so the per-file loop cannot drop a surface unseen.
    import tempfile
    tree = {'scripts/build_x.py': "p('" + _I + ".')\n", 'Notes.md': _I + '.\n',
            'ZeroParadox/X.lean': '/-- ' + _I + '. -/\ntheorem x : True := trivial\n',
            'Pointed.md': _I + ' (`f_snap_impossible`).\n'}
    with tempfile.TemporaryDirectory() as tmp:
        for rel, src in tree.items():
            (Path(tmp) / rel).parent.mkdir(parents=True, exist_ok=True)
            (Path(tmp) / rel).write_text(src, encoding='utf-8')
        found = {h[0] for h in scan([(Path(tmp) / rel, rel) for rel in tree])}
    bad += common.fire_suppress(
        [('build script, unpointed claim', 'scripts/build_x.py'), ('md, unpointed claim', 'Notes.md'),
         ('lean, unpointed claim', 'ZeroParadox/X.lean')],
        [('md, pointed claim', 'Pointed.md')],
        lambda rel: rel in found, 'scan() end to end', width=50)
    # `targets()` on the REAL tree must reach the corpus, not merely each family: a COUNT floor and
    # a named sentinel per family. FAILS CLOSED: an enumeration that raises counts as empty.
    try:
        rels = set(rel for _p, rel in targets())
    except Exception as exc:          # noqa: BLE001 -- any failure is an empty enumeration
        print('  targets() raised: %r' % exc)
        rels = set()
    zl = sum(1 for r in rels if r.startswith('ZeroParadox/') and r.endswith('.lean'))
    zm = sum(1 for r in rels if r.startswith('ZeroParadox/') and r.endswith('.md'))
    bs = sum(1 for r in rels if BUILD_SCRIPT.match(r))
    bad += common.fire_suppress(
        [('ZeroParadox/**/*.lean >= FLOOR_LEAN', zl >= FLOOR_LEAN),
         ('ZeroParadox/**/*.md >= FLOOR_MD', zm >= FLOOR_MD),
         ('scripts/build_*.py >= FLOOR_BUILD', bs >= FLOOR_BUILD),
         ('sentinel ZeroParadox/Order/Snap.lean', 'ZeroParadox/Order/Snap.lean' in rels),
         ('sentinel ZeroParadox/Ordinal/SnapNucleus.md', 'ZeroParadox/Ordinal/SnapNucleus.md' in rels),
         ('sentinel scripts/build_zpf.py', 'scripts/build_zpf.py' in rels)],
        [], lambda ok: ok, 'targets() reaches the corpus (%d/%d/%d)' % (zl, zm, bs), width=50)
    # ⚠ THE PATTERN PIN (PAT-1). Three controls guard fourteen phrases. Mutation-tested 2026-08-16:
    # replacing any of the other eleven with a string that cannot match leaves `--selftest` green and
    # `--block` at exit 0 — the checker silently stops catching the defect class it exists for. The
    # controls prove the patterns they exercise; the pin proves the rest are still there.
    print('PATTERNS')
    bad += common.check_vocabulary('check_modal', globals())
    if bad:
        print('\nselftest: FAIL (%d)' % bad)
    return 1 if bad else 0


def scan_file(text, rel):
    """One file's hits as `(rel, line, phrase)`: the per-file path `scan()` runs, so `--selftest`
    exercises how `rel` reaches `scan_text`."""
    stripped = strip_module_docstring(text, rel)
    t = prepare(stripped, rel)
    # Line numbers come from `stripped`, NOT from `t`: normalize_separators consumes the newline
    # in a Python adjacent-string-literal join, so counting on `t` drifts (measured: line 78
    # reported as 40). `strip_module_docstring` IS line-count-preserving, so `stripped` is safe.
    hits = []
    for off, phrase in scan_text(t, rel):
        ln = stripped.count('\n', 0, off) + 1
        hits.append((rel, ln, phrase))
    return hits


def scan(files=None):
    """Every hit in the tree. `files` replaces `targets()` only for `--selftest`'s temporary tree."""
    hits = []
    for p, rel in (targets() if files is None else files):
        try:
            t = p.read_text(encoding='utf-8')
        except (OSError, UnicodeDecodeError):
            continue
        hits.extend(scan_file(t, rel))
    return sorted(set(hits))


def load_baseline():
    return common.load_baseline(BASELINE)


def key(h):
    # ⚠ No line number: one baselined `path|cannot be` exempts every future "cannot be" in that file.
    return '%s|%s' % (h[0], h[2].lower())


def main():
    block = '--block' in sys.argv
    hits = scan()

    if '--baseline' in sys.argv:
        common.refuse_baseline_write('modal_baseline.txt')
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
        print('  An IMPOSSIBILITY ("cannot be" / "cannot satisfy" / "is impossible" ...)')
        print('  passes by naming the theorem that PROVES it in the same sentence:')
        print('  backticked, or bare in scripts/build_*.py -- and not as the claim\'s subject.')
        print('  Otherwise carry a dated measurement in that sentence, or delete it.')
    print('=' * 40)

    rc = _record(new)
    if rc:
        return rc

    return 1 if (block and new) else 0


def _record(new):
    """The universe is THIS checker's own scope — never a shared roster."""
    return common.record_if_asked('check_modal', [rel for _p, rel in targets()],
                                  {h[0] for h in new}, 'unmeasured modal claim',
                                  switches=['tools/verify/modal_baseline.txt',
                                            'tools/verify/vendored_files.txt'])


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(selftest())
    sys.exit(main())
