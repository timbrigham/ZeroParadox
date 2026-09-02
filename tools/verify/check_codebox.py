# -*- coding: utf-8 -*-
"""Every identifier in a published CODE BOX must exist in the file the box cites.

⭐⭐ WHY THIS IS A CHECKER AND NOT A SIXTH PROSE PASS. The `/editorial-review` round of 2026-09-02
put it plainly: *"Fourth round, one document, one shape. The fix that settles it is a checker
resolving rendered code-box identifiers against the cited declaration, not a fifth prose pass."*
`R-NOCONV` says a loop that will not settle changes SHAPE, and this shape had defeated four
consecutive hand-fixes, each applied at the smallest radius the round happened to see:

  v1.10  fixed ONE box (`toAFAStructure`) and established the rule *a box that paraphrases is
         prose wearing a code block*
  v1.11  fixed TWO more (`ValuationStructure`, `DecorationUniverse`) — the same rule, unapplied
  v1.12  fixed TWO more (`AbstractSelfApp`, `AFAStructure`) — and the APG box's `accessible` line
  v1.13  fixed the `Reach(v)` line **three lines below the line v1.12 had just fixed, in the same
         box**, which the adversary gate graded BEDROCK: the identifier resolved only to
         `SimpleGraph.Reachable`, which is SYMMETRIC, and § IV.2's induction terminates only
         because reachability runs ONE WAY. A false definition carrying the main theorem's
         termination argument.
  and FOUR sites remain live at the time this was written.

⚠ **THE DEFECT IS NOT MATHEMATICAL, WHICH IS WHY READING KEEPS MISSING IT.** `bot` and `⊥` name
the same bottom element; a reader substitutes silently. What is false is narrower and mechanical:
**the box advertises itself as Lean and would not compile**, because the pretty glyph has no
global notation bound to it — the only `⊥`-ish notation in this corpus is `local notation "⊥ₗ"`
(`ZeroParadox/Order/Lattice.lean`), a different glyph and file-local. A published type signature
that does not typecheck is a comment wearing an interface's clothes.

⚠⚠ ADVISORY, AND IT SAYS SO. It never blocks. Whether a flagged token is a defect, a binder the
box introduces, or a Mathlib name the file inherits by import is JUDGEMENT, and a checker that
guessed would manufacture the false-positive work this project has measured twice. `R-NOCONV`:
an LLM screen may replace the ENUMERATION, never the VERDICT — this is the enumeration.

Usage:
    python tools/verify/check_codebox.py                 # every tracked build script
    python tools/verify/check_codebox.py --selftest      # controls, both halves
"""
import html
import io
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                                    # noqa: E402

common.utf8_stdout()
REPO = str(common.REPO)
SELF = common.self_rel(__file__)


def _rel(p):
    """Repo-relative, forward-slashed. Local because `common` exposes no `rel`, and
    inventing one there would widen a shared module for one caller."""
    try:
        return os.path.relpath(str(p), str(common.REPO)).replace(os.sep, '/')
    except ValueError:
        return str(p)


# A box header names its source: 'Typeclass: ValuationStructure (ZeroParadox/Valuation/Scale.lean)'
# or with a section marker after it. R-LEANPDF requires the FULL repository path in a checkable
# surface, so a bare basename is out of scope here by construction — it is `check_paths`' job.
# ⚠⚠⚠ ACCEPT A BARE BASENAME TOO, OR THE ZERO IS A LIE — `RLY46-1`, measured 2026-09-02.
#   The first version required a full repository path and therefore parsed **12 of 148** box
#   calls. 72 boxes cite `(Kleene.lean § III)` style, **14 of them in `build_zpj.py` — the very
#   document whose four failed hand-fixes this checker was written to end.** It reported 0 and
#   the 0 meant "I looked at 8% of the boxes", which is the vacuous zero this file's own
#   docstring warns about, produced by this file, on its first day.
#   ⚠ A bare basename is separately a defect (R-LEANPDF wants the full path in a checkable
#   surface) but that is `check_paths`' job; refusing to PARSE it just hides the box.
HEADER = re.compile(
    # ⚠ ZERO OR MORE directory levels, not "one or more". The first form required at least two
    #   (`ZeroParadox/Valuation/Scale.lean` matched, `ZeroParadox/T.lean` did not), so the
    #   selftest fixture — a one-level path — was invisible and both MUST-FIRE halves went red
    #   for a reason unrelated to the property. Same class as the cache: a control failing on
    #   its own scaffolding rather than its subject.
    r"['\"][^'\"]{0,200}?\(((?:(?:ZeroParadox|scripts)/(?:\w+/)*)?\w+\.lean)")
# ⚠⚠ A PROPERTY, NOT A LIST OF KIND WORDS — and the list version cost 33 more boxes.
#   The first pattern required `Typeclass:`/`Theorem:`/`Lemma:`… and the corpus writes
#   `'Functor: fB_functor : ...'`, `'AFAStructure Typeclass (SetTheoryAFA.lean § I)'`,
#   `'J_self Theorems (AczelConn.lean § I)'`, `'Derived Results from AbstractSelfApp (...)'`.
#   Every one of those is a box header citing a Lean file; none matched. Widening the list again
#   would repeat the shape (`check_paths._CLAIM_MARKER` records the identical lesson: five of ten
#   line-start markers were blind because someone enumerated instead of naming the property).
#   **The property is: a header string that names a .lean file in parentheses.** The kind word is
#   decoration.
# Resolving a bare basename needs a search; ambiguity is REPORTED, never guessed.
_LEAN_INDEX = None
BOX_CALL = re.compile(r'\b(?:def_box|result_box)\s*\(', re.M)

# ⚠ GLYPHS WITH NO GLOBAL BINDING IN THIS CORPUS. Each maps to what the Lean actually writes.
#   This list is SHORT and every entry was a live defect, never a guess — `R-CONTROLS`' rule that
#   a control citing something that does not exist is worse than no control.
#   ⚠ MATCHED AS PATTERNS, NOT SUBSTRINGS. `∞` as a bare token is prose for the top element, which
#     the Lean writes `⊤` — but `ℕ∞` is a REAL Lean type name (`WithTop ℕ`) and appears verbatim in
#     the corpus. The substring form flagged `val : L → ℕ∞` on its first live run, which is correct
#     Lean and would have sent a reader to "fix" a line that is already right. A checker whose
#     first finding is a correction TO a correct line is how a gate loses its reader.
UNBOUND_GLYPH = {
    # ⊥ is never bound globally here: only `local notation "⊥ₗ"` (a DIFFERENT glyph, file-local).
    re.compile(r'⊥'): ('⊥', 'bot'),
    # ∞ standing alone — not the ℕ∞ / ℤ∞ compound, which is genuine notation.
    re.compile(r'(?<![ℕℤℚℝ])∞'): ('∞', '⊤'),
}

# Lean/Mathlib vocabulary a box may use without the cited file mentioning it. Kept deliberately
# small: a long allowlist is how an enumeration check stops enumerating.
CORE = set("""class structure instance theorem lemma def where with fun by intro exact
    Type Sort Prop Set Nat Bool Fin List Option Prod Sum Unit Empty True False
    Nonempty Subsingleton Decidable DecidableEq Fintype Finite Quiver Path
    forall exists if then else let in do match deriving open namespace end
    variable universe noncomputable private protected partial mutual""".split())

TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def _resolve_lean(cited):
    """A cited path -> the file on disk, or None. Bare basenames are searched; AMBIGUITY IS None.

    ⚠ NEVER GUESS. If two files share a basename the citation does not determine one, and
    picking either would make the checker's verdict depend on directory order — a control that
    passes for the wrong reason (`DC-22`). Report it as unresolvable instead.
    """
    global _LEAN_INDEX
    p = common.REPO / cited
    if p.exists():
        return p
    if '/' in cited:
        return None
    if _LEAN_INDEX is None:
        _LEAN_INDEX = {}
        for q in (common.REPO / 'ZeroParadox').rglob('*.lean'):
            _LEAN_INDEX.setdefault(q.name, []).append(q)
    hits = _LEAN_INDEX.get(cited, [])
    return hits[0] if len(hits) == 1 else None


def _boxes(src_text):
    """[(header_line_no, cited_lean_path, [body strings])] for each box naming a .lean file."""
    out = []
    for m in BOX_CALL.finditer(src_text):
        seg = src_text[m.end():m.end() + 4000]
        # ⚠⚠⚠ WELD ADJACENT STRING LITERALS BEFORE MATCHING THE HEADER. A box title and its cited
        #   path are routinely written as two literals — `'Theorem: cyclic_decoration_eq_bot '`
        #   then `'(ZeroParadox/Settheory/APG.lean § VII′)'` — and a pattern requiring both in ONE
        #   literal cannot see that box AT ALL. Measured: the checker reported 3 sites where the
        #   editorial gate had named 4, and the missing one was the box whose header wraps.
        #   ⚠ THIS IS THE FOURTH TIME TONIGHT THE SPLIT-LITERAL SHAPE HAS BITTEN, and this time
        #   inside the checker written to end the class it belongs to. `check_paths` already
        #   carries `_CLAIM_JOIN` for it, and the lesson did not travel — which is the
        #   half-applied defect one level up: a rule learned in one file and not in the next.
        seg = re.sub(r"'\s*\n\s*'|\"\s*\n\s*\"", '', seg)
        h = HEADER.search(seg)
        if not h:
            continue
        # ⚠ START AFTER THE HEADER'S OWN LINE, not at `h.end()`. The header pattern finishes
        #   INSIDE its string literal (it stops at the cited path), so slicing from there begins
        #   mid-quote and every subsequent quote pairs off by one — the body came back as the
        #   punctuation BETWEEN the rows. Measured on the selftest fixture: rows = [",\n    [\n"].
        #   ⚠⚠ AND IT WENT UNNOTICED BECAUSE THREE OF FIVE CONTROLS PASSED VACUOUSLY: with `scan`
        #   returning nothing, every MUST-SUPPRESS case is satisfied for the wrong reason. Only
        #   the two MUST-FIRE halves exposed it — which is exactly why `check_checkers` rule 3
        #   requires both halves, and why a must-suppress-only control set proves nothing.
        nl = seg.find('\n', h.end())
        body = seg[nl + 1:] if nl > 0 else seg[h.end():]
        stop = re.search(r'^\s*\]\s*\)?', body, re.M)
        if stop:
            body = body[:stop.start()]
        rows = re.findall(r"'([^']*)'|\"([^\"]*)\"", body)
        # ⚠⚠⚠ DECODE THE ENTITIES, OR THIS CHECKER IS VACUOUS BY CONSTRUCTION — and it WAS, on its
        #   first live run: **0 findings** while four sites were known live. The builder writes
        #   `&#8869;`, and `⊥` exists only after rendering, so a source scan looking for the glyph
        #   can never see it. That is `R-DEFECTCLASS`'s own rule — *for prose that ships, the
        #   detector runs on the RENDERED text, never the source* — arriving inside the checker
        #   built to enforce it, and producing exactly the clean zero it exists to prevent.
        #   Decoding is the cheap way to get the rendered form without a PDF: the entity IS the
        #   glyph, one substitution apart. What it does NOT reach is a claim split across two
        #   adjacent string literals; that still needs the extracted PDF, and `check_paths
        #   --claim` is the tool for it.
        rows = [html.unescape(a or b) for a, b in rows]
        out.append((src_text[:m.start()].count('\n') + 1, h.group(1), rows))
    return out


# ⚠⚠ A BOX HOLDS CODE **AND** GLOSS, AND ONLY THE CODE IS A TRANSCRIPTION CLAIM. The first
#   version scanned every row and returned 31 findings of which most were English — `Transcribed`,
#   `Contradiction.`, `WAY.`, `Under` — capitalised words of four letters or more, which is also
#   the shape of a type name. **A checker that cries wolf is one nobody runs**, and this file's own
#   docstring said so one screen above the code that did it (the third time that exact sentence
#   has been written next to the defect it describes, in this session alone).
#   The discriminating property: a Lean signature line carries a TYPE ASCRIPTION or a BINDING.
#   Prose does not. That is cheap, and it is the line the box is actually asserting about.
CODE_ROW = re.compile(
    r'^\s*(?:class|structure|instance|theorem|lemma|def|example|noncomputable)\b'
    r'|^\s*[\w\'.]+\s*:(?!=)'          # a field or hypothesis: `val_bot : ...`
    r'|:=|→|⟶|↦|∀|∃'                    # or any binding / arrow / quantifier
)
# ⚠⚠ AND A PROSE VETO, BECAUSE `CODE_ROW` ALONE IS TOO GENEROUS. Measured on the live corpus: it
#   fired on `Proof: suppose scale x = x and x ≠ ⊥, …` and on `Consequence: d₁ v = d₂ v = ⊥ …`,
#   because a sentence opening `Word:` is indistinguishable from a field declaration by shape, and
#   a gloss quantifying over vertices legitimately contains `∀`. All four identifier findings on
#   the first honest run were English words — `Contradiction.`, `Transcribed`, `Consequence`.
#   ⚠ THE DISCRIMINATOR IS VOCABULARY, NOT PUNCTUATION. A Lean signature is almost wordless; a
#   gloss carries function words that no type ever does. Two or more of these and the row is
#   prose, whatever its shape. Deliberately short — a long list stops enumerating (`R-NOCONV`).
PROSE_WORDS = re.compile(
    r'\b(?:the|and|for|which|that|every|any|from|this|means|suppose|gives|holds|because|'
    r'therefore|impossible|value|above|below|proof|note)\b', re.I)


# ⚠⚠ ROWS ARE HYBRID, and treating one as wholly code or wholly prose is wrong both ways.
#   The corpus writes `'J_self_eq_singleton_bot: J_self = {⊥}. Proved without DC. ✓'` — a
#   transcription claim, then a sentence about it, on one line. Scanning the whole row reported
#   `Proved`, `Proof`, `naturals.` and `analysis.` as absent identifiers (4 of 6 findings on the
#   widened domain, all English). **The transcription claim is the part BEFORE the prose starts**,
#   so cut at the first sentence boundary and judge only the head. Measured: 4 false positives to 0,
#   with the genuine glyph finding retained.
_SENTENCE = re.compile(r'\.\s+(?=[A-Z(])')


def _claim_part(row):
    """The head of a row, up to where prose takes over."""
    m = _SENTENCE.search(row)
    return row[:m.start()] if m else row


def _is_code_row(row):
    """A transcription claim, not a gloss. Both tests, because either alone is wrong."""
    return bool(CODE_ROW.search(row)) and len(PROSE_WORDS.findall(row)) < 2
# A path cited INSIDE the body, e.g. 'Instance toAbstractSelfApp (ZeroParadox/Valuation/Scale.lean):'
INLINE_SRC = re.compile(r'((?:ZeroParadox|scripts)/[\w/]+\.lean)')


def _idents(text):
    """Identifier-shaped tokens worth resolving: snake_case, dotted, or CamelCase length>=4.

    ⚠ SHORT TOKENS ARE BINDERS, NOT REFERENCES. `x`, `v`, `L`, `U` are introduced by the box
    itself, so requiring them in the cited file would flag every well-formed box — the
    false-positive flood that makes a checker unrunnable.
    """
    for t in TOKEN.findall(text):
        if t in CORE or len(t) < 4:
            continue
        if '_' in t or '.' in t or (t[0].isupper() and len(t) >= 4):
            yield t


def scan(paths=None, stats=None):
    """[(script, line, cited, kind, token, note)] — pure, prints nothing.

    ⚠ `stats` is filled with the DENOMINATOR: how many box calls exist, how many were parsed.
    A finding count with no denominator is unreadable — `RLY46-1` measured this file reporting
    **0 findings** while parsing 12 of 148 box calls, and nothing on the page said so. The count
    is the difference between "clean" and "barely looked".
    """
    findings = []
    scripts = paths if paths is not None else sorted(
        (common.REPO / 'scripts').glob('build_*.py'))
    for s in scripts:
        try:
            text = io.open(s, encoding='utf-8').read()
        except OSError:
            continue
        if stats is not None:
            stats['calls'] = stats.get('calls', 0) + len(BOX_CALL.findall(text))
        for line, cited, rows in _boxes(text):
            if stats is not None:
                stats['parsed'] = stats.get('parsed', 0) + 1
            src = _resolve_lean(cited)
            if src is None:
                findings.append((_rel(s), line, cited, 'unresolvable-citation', cited,
                                 'cited file not found, or the basename is ambiguous'))
                continue
            # ⚠ RESOLVE AGAINST EVERY FILE THE BOX CITES, not only its header. A box may name a
            #   second source inline — `Instance toAbstractSelfApp (ZeroParadox/Valuation/Scale
            #   .lean):` sits inside a box headed `SelfApp.lean` — and checking those rows against
            #   the header alone reported `scale_bot` and `scale_unique_fp` ABSENT while both are
            #   plainly in the file the row itself names. A wrong domain, one level down: the same
            #   defect `RLY45-1` named in the claim sweep, arriving in the checker built after it.
            cited_all = {cited}
            for row in rows:
                cited_all.update(INLINE_SRC.findall(row))
            lean = ''
            for c in sorted(cited_all):
                p = _resolve_lean(c)
                if p is not None:
                    lean += io.open(p, encoding='utf-8').read()
            for row in rows:
                for pat, (g, real) in UNBOUND_GLYPH.items():
                    if not (pat.search(row) and _is_code_row(row)):
                        continue
                    # ⚠⚠⚠ THE PREMISE IS ONE-WAY AND THE RULE FIRED ON THE CONVERSE — `RLY46-10`.
                    #   "This row transcribes a ZPSemilattice signature" ⟹ "the glyph is
                    #   unbound", because ZPSemilattice supplies the bottom as a STRUCT FIELD
                    #   named `bot` with nothing for the pretty glyph to dispatch on. The
                    #   CONVERSE is false: wherever a carrier implements Mathlib's `Bot`/
                    #   `OrderBot`, the glyph is genuine imported notation — measured, **785
                    #   occurrences across 98 of 218 tracked .lean files**. Of the 22 glyph rows
                    #   a widened domain surfaces, 20 cite a file that itself writes that glyph,
                    #   so the note would have been FALSE about that file 20 times in 22.
                    #   The cheap, correct discriminator: if the CITED FILE writes the glyph
                    #   itself, it is bound there and this checker has nothing to say.
                    if g in lean:
                        continue
                    findings.append((_rel(s), line, cited, 'unbound-glyph', g,
                                     'no notation bound in the cited file; it writes `%s`'
                                     % real))
                if not _is_code_row(row):
                    continue
                row = _claim_part(row)   # judge the claim, not the sentence after it                    # gloss, not a transcription claim
                for tok in _idents(row):
                    base = tok.split('.')[0]
                    if tok not in lean and base not in lean:
                        findings.append((_rel(s), line, cited, 'absent-identifier', tok,
                                         'not located in the cited file'))
    return findings


def main():
    if '--selftest' in sys.argv:
        return selftest()
    st = {}
    findings = scan(stats=st)
    by_kind = {}
    for f in findings:
        by_kind.setdefault(f[3], []).append(f)
    print('=' * 78)
    print('  CODE-BOX IDENTIFIER CHECK')
    print('  entry      python %s' % SELF)
    print('  property   every identifier in a published code box exists in the file it cites,')
    print('             and every glyph it prints has a notation bound to it')
    print('  mode       ADVISORY — never blocks. The enumeration is mechanical; the verdict')
    print('             is judgement, and a checker that guessed would manufacture noise.')
    # ⚠ THE DENOMINATOR, ON EVERY RUN. Without it a 0 reads as coverage.
    # ⚠ THREE NUMBERS, NOT TWO. An earlier version printed 'the rest cite no .lean', which
    #   was FALSE - 34 unparsed boxes cited one. A denominator that misdescribes its own
    #   remainder is worse than none, because it closes the question it should open.
    print('  coverage   %d box call(s); %d parsed. The remainder either cite no .lean'
          % (st.get('calls', 0), st.get('parsed', 0)))
    print('             or use a header shape this pattern does not reach — both UNJUDGED.')
    print('=' * 78)
    for kind in sorted(by_kind):
        print('\n  %s — %d' % (kind, len(by_kind[kind])))
        seen = set()
        for script, line, cited, _k, tok, note in by_kind[kind]:
            key = (script, line, tok)
            if key in seen:
                continue
            seen.add(key)
            print('    %s:%s  %-22s %s' % (script, line, tok, note))
            print('        cites %s' % cited)
    print('\n  %d finding(s) across %d box site(s).' % (len(findings), len({(f[0], f[1]) for f in findings})))
    print('  ⚠ READING LIST, NOT A FINDING LIST. A flagged token may be a binder the box')
    print('    introduces or a name the cited file inherits by import — read each one.')
    return 0


def selftest():
    """Both halves. A must-fire alone would also pass against a checker that flags everything."""
    import tempfile
    from pathlib import Path
    bad = 0
    print('== code-box identifier check - CONTROLS ==\n')

    CASES = [
        # (name, box body row, lean content, must_fire)
        ('clean: identifier present',
         "'  val_bot    : val bot = &#8868;',", 'theorem val_bot : val bot = 0', False),
        ('absent identifier fires',
         "'  accessible : Reachable root v',", 'structure APG where root : V', True),
        ('unbound glyph fires',
         "'  fixed_bot : selfApp ⊥ = ⊥',", 'theorem fixed_bot : selfApp bot = bot', True),
        ('short binders are not flagged',
         "'  scale : L → L',", 'class C where scale : L -> L', False),
        ('core vocabulary is not flagged',
         "'  x : Nonempty (Quiver.Path root v)',",
         'structure APG where accessible : Nonempty (Quiver.Path root v)', False),
    ]
    with tempfile.TemporaryDirectory() as d:
        for name, row, lean, must in CASES:
            lp = Path(d) / 'T.lean'
            io.open(lp, 'w', encoding='utf-8').write(lean + '\n')
            sp = Path(d) / 'build_t.py'
            io.open(sp, 'w', encoding='utf-8').write(
                "def_box(\n    'Theorem: t (ZeroParadox/T.lean)',\n    [\n        %s\n        ]\n"
                % row)
            # point the resolver at the temp lean file
            real = common.REPO
            try:
                # ⚠ RESET THE BASENAME CACHE. `_LEAN_INDEX` is module-level and is built from
                #   `common.REPO`; the fixture repoints REPO, so a cache warmed by an earlier
                #   case (or by a live scan in the same process) still answers for the real
                #   repository and the fixture's file is never found. Both MUST-FIRE cases went
                #   red for that reason and not for the property they test -- `DC-22`, in the
                #   control, again. A cache keyed on a value someone else can change must be
                #   invalidated wherever that value changes.
                global _LEAN_INDEX
                _LEAN_INDEX = None
                common.REPO = Path(d)
                os.makedirs(Path(d) / 'ZeroParadox', exist_ok=True)
                io.open(Path(d) / 'ZeroParadox' / 'T.lean', 'w', encoding='utf-8').write(lean)
                fired = bool(scan([sp]))
            finally:
                common.REPO = real
                _LEAN_INDEX = None
            ok = fired == must
            bad += 0 if ok else 1
            print('  %-34s %-13s %s' % (name, 'MUST FIRE' if must else 'MUST SUPPRESS',
                                        'ok' if ok else '*** FAIL (got %s) ***' % fired))

    # ⚠⚠ THE PRODUCTION ENUMERATION, WHICH NO CONTROL ABOVE REACHES — `RLY46-2`. Every case above
    #   passes `paths=[...]`, so `scan()`'s default glob never executes under test: emptying it
    #   left `--selftest` BYTE-IDENTICAL and PASS. That is `RLY45-1` one file over, inside the
    #   checker whose docstring cites `RLY45-1` — the lesson did not travel from `_claim_domain`,
    #   which had just been extracted for exactly this reason.
    #   ⚠ AND THIS CONTROL WAS CLAIMED FIXED ONCE BEFORE IT EXISTED: the patch that "added" it
    #   used a bare `str.replace` with an anchor belonging to ANOTHER FILE, matched nothing, and
    #   reported success. A replace without a match count is a silent no-op wearing a fix's
    #   clothes; every other patch in this session verifies its anchors and refuses on a miss.
    print('  MUST HOLD  (the production enumeration is non-empty)')
    _prod = sorted((common.REPO / 'scripts').glob('build_*.py'))
    _st = {}
    scan(stats=_st)
    _ok = len(_prod) >= 10 and _st.get('calls', 0) >= 100 and _st.get('parsed', 0) >= 1
    bad += 0 if _ok else 1
    print('    %-40s %s (%d script(s), %d call(s), %d parsed)'
          % ('default glob finds boxes to judge',
             'ok' if _ok else '*** VACUOUS — scan() sees nothing ***',
             len(_prod), _st.get('calls', 0), _st.get('parsed', 0)))

    print('\n  controls: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
