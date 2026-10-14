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

⚠ WHAT IT READS AND WHAT IT DOES NOT. Identifiers, unbound glyphs, and one SHAPE property — a
declaration that binds one name twice (`W4K-7`). It does not compare a box's binder list against
the ELABORATED signature, so a box that drops, adds or reorders a distinct binder passes.

Usage:
    python tools/verify/check_codebox.py                 # every tracked build script
    python tools/verify/check_codebox.py --selftest      # controls, both halves
"""
import ast
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
# or with a section marker after it.
# ⚠⚠⚠ ACCEPT A BARE BASENAME TOO, OR THE ZERO IS A LIE — `RLY46-1`, measured 2026-09-02.
#   The first version required a full repository path and therefore parsed **12 of 148** box
#   calls. 72 boxes cite `(Kleene.lean § III)` style, **14 of them in `build_zpj.py` — the very
#   document whose four failed hand-fixes this checker was written to end.** It reported 0 and
#   the 0 meant "I looked at 8% of the boxes", which is the vacuous zero this file's own
#   docstring warns about, produced by this file, on its first day.
#   ⚠ A bare basename is separately a defect (R-LEANPDF wants the full path in a checkable
#   surface) but that is `check_paths`' job; refusing to PARSE it just hides the box.
# ⚠ ZERO OR MORE directory levels, and no kind word. `HEADER_SHAPES` in the selftest holds one
#   fixture per header shape the corpus writes, and the control asserts EVERY one parses and the
#   parsed count equals the fixture count (`RLY47-1`): narrowing this pattern to a directory slash
#   or a kind-word list turns a named shape red, where `parsed >= 1` admitted a 94 -> 1 collapse.
HEADER = re.compile(r"\(((?:(?:ZeroParadox|scripts)/(?:\w+/)*)?\w+\.lean)")
# ⚠⚠ A PROPERTY, NOT A LIST OF KIND WORDS — and the list version cost 33 more boxes.
#   The first pattern required `Typeclass:`/`Theorem:`/`Lemma:`… and the corpus writes
#   `'Functor: fB_functor : ...'`, `'AFAStructure Typeclass (SetTheoryAFA.lean § I)'`,
#   `'J_self Theorems (AczelConn.lean § I)'`, `'Derived Results from AbstractSelfApp (...)'`.
#   **The property is: a header string that names a .lean file in parentheses.** The kind word is
#   decoration.
# Resolving a bare basename needs a search; ambiguity is REPORTED, never guessed. The index is
# keyed on the repository root it was built from (`RLY47-5`): a cache that answers for a root
# nobody asked about returns a verdict on a file the checker never opened.
_LEAN_INDEX = (None, None)
BOX_FUNCS = ('def_box', 'result_box')
# A path cited INSIDE the body, e.g. 'Instance toAbstractSelfApp (ZeroParadox/Valuation/Scale.lean):'
# or 'Witnesses: fork_collapse_iff (RequirementsGap.lean)'.
INLINE_SRC = re.compile(r"(?<![\w/])((?:(?:ZeroParadox|scripts)/(?:\w+/)*)?\w+\.lean)")

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

# ⚠ A DOT MUST BE FOLLOWED BY AN IDENTIFIER CHARACTER (`RLY47-6`). The first form ended in
#   `[A-Za-z0-9_'.]*`, so a sentence-final period joined the word and the English `naturals.`
#   qualified as a dotted identifier — every sentence-final word of four or more letters in a
#   veto-passing row was a candidate.
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*")


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
    root, index = _LEAN_INDEX
    if root != common.REPO:
        index = {}
        for q in (common.REPO / 'ZeroParadox').rglob('*.lean'):
            index.setdefault(q.name, []).append(q)
        _LEAN_INDEX = (common.REPO, index)
    hits = index.get(cited, [])
    return hits[0] if len(hits) == 1 else None


def _const_str(node):
    return node.value if isinstance(node, ast.Constant) and isinstance(node.value, str) else None


def _boxes(src_text, stats=None):
    """[(call_line_no, title_citation_or_None, [body strings])] — one entry per box call.

    ⚠⚠⚠ THE CALL IS PARSED, NOT WINDOWED (`RLY47-2`). The first form searched a fixed 4000-character
    window after `def_box(` for the first `(X.lean)`, so a box citing nothing took a LATER box's
    citation, and a box citing only in a body row lost every row above that one. `ast` gives the
    call's own arguments: implicit string concatenation is already welded (the split-literal header
    that bit four times is gone by construction) and entities stay literal for `html.unescape`.
    """
    out = []
    for node in ast.walk(ast.parse(src_text)):
        if not isinstance(node, ast.Call):
            continue
        f = node.func
        name = f.id if isinstance(f, ast.Name) else (f.attr if isinstance(f, ast.Attribute) else None)
        if name not in BOX_FUNCS:
            continue
        if stats is not None:
            stats['calls'] = stats.get('calls', 0) + 1
        # `build_zpg.py` overrides the signature as (title, status, rows): the rows are the first
        # list argument, and every string argument before it is header text.
        title, rows_node = '', None
        for a in node.args:
            if isinstance(a, (ast.List, ast.Tuple)):
                rows_node = a
                break
            title += (_const_str(a) or '') + ' '
        rows, unread = [], 0
        for e in (rows_node.elts if rows_node is not None else ()):
            v = _const_str(e)
            if v is None:
                unread += 1
            else:
                # ⚠⚠⚠ DECODE THE ENTITIES, OR THIS CHECKER IS VACUOUS BY CONSTRUCTION — and it WAS,
                #   on its first live run: **0 findings** while four sites were known live. The
                #   builder writes `&#8869;`, and `⊥` exists only after rendering, so a source scan
                #   looking for the glyph can never see it (`R-DEFECTCLASS`: for prose that ships,
                #   the detector runs on the RENDERED text). An entity-encoded MUST-FIRE case
                #   controls it (`RLY47-3`).
                rows.append(html.unescape(v))
        if stats is not None:
            stats['rows'] = stats.get('rows', 0) + len(rows)
            stats['rows_unread'] = stats.get('rows_unread', 0) + unread + (rows_node is None)
        h = HEADER.search(html.unescape(title))
        out.append((node.lineno, h.group(1) if h else None, rows))
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


# ⚠ A GLOSS LABEL IS NOT A FIELD (`RLY47-6`). `Proof: case split; simp [snapEmbed].` passed
#   `CODE_ROW` on its `Word:` shape and the prose veto on having one listed word, so `Proof` was
#   reported absent at six sites. A leading capitalised English word followed by `:` labels the
#   row; it is stripped before either test, so the row is judged on what follows the label.
GLOSS_LABEL = re.compile(r"^\s*[A-Z][a-z]+(?:\s+[a-z]+)?\s*:(?!=)\s*")

# ⚠⚠ THE SHAPE LEG (`W4K-7`). A duplicated binder is two well-formed identifiers, so the identifier
#   legs above cannot see it: a rendered `decoration_unique` box declared `(_G : APG V)` beside the
#   `(G : APG V)` it was meant to replace and this checker reported 0. One declaration whose
#   explicit, implicit or instance binders repeat a name — up to a leading `_` — is reported.
#   ⚠ ARITY IS NOT CHECKED: comparing a box's binders against the ELABORATED signature needs Lean,
#   and nothing here runs it. A box that drops or adds a distinct binder passes this leg.
DECL_START = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
                        r"(?:theorem|lemma|def|abbrev|example|instance|structure|class)\b")
BINDER = re.compile(r"[({\[⦃]\s*([^\s:(){}\[\]⦃⦄]+(?:\s+[^\s:(){}\[\]⦃⦄]+)*)\s*:[^(){}\[\]⦃⦄]+[)}\]⦄]")


def _duplicate_binders(rows):
    """[(declaration head, repeated name)] across each declaration the box's code rows spell."""
    out, names, head = [], {}, None
    for row in rows:
        if DECL_START.match(row):
            names, head = {}, row.strip()[:60]
        elif head is None or not _is_code_row(row):
            continue
        for grp in BINDER.findall(row):
            for n in grp.split():
                key = n.lstrip('_')
                if not key:
                    continue
                if key in names:
                    out.append((head, '%s / %s' % (names[key], n)))
                names.setdefault(key, n)
    return out


def scan(paths=None, stats=None):
    """[(script, line, cited, kind, token, note)] — pure, prints nothing.

    ⚠ `stats` is filled with the DENOMINATOR (`RLY46-1`, `RLY47-2`): box calls found, boxes judged
    against a resolved file, boxes citing no .lean anywhere, rows read and code rows judged, rows
    that are not string literals, and scripts that could not be read or parsed. A finding count
    with no denominator is unreadable, and a denominator that counts BOXES says nothing about ROWS.
    """
    findings = []
    st = stats if stats is not None else {}
    scripts = paths if paths is not None else sorted(
        (common.REPO / 'scripts').glob('build_*.py'))
    for s in scripts:
        try:
            text = io.open(s, encoding='utf-8').read()
            boxes = _boxes(text, st)
        except (OSError, SyntaxError, ValueError) as e:
            # R-ZERONULL: an unreadable script is COUNTED and NAMED, never a silent zero.
            st.setdefault('unreadable', []).append('%s (%s)' % (_rel(s), type(e).__name__))
            continue
        for line, cited, rows in boxes:
            # ⚠ RESOLVE AGAINST EVERY FILE THE BOX CITES, not only its header. A box may name a
            #   second source inline — `Instance toAbstractSelfApp (ZeroParadox/Valuation/Scale
            #   .lean):` sits inside a box headed `SelfApp.lean` — and checking those rows against
            #   the header alone reported `scale_bot` and `scale_unique_fp` ABSENT while both are
            #   plainly in the file the row itself names. A wrong domain, one level down: the same
            #   defect `RLY45-1` named in the claim sweep, arriving in the checker built after it.
            cited_all = {cited} if cited else set()
            for row in rows:
                cited_all.update(INLINE_SRC.findall(row))
            if not cited_all:
                st['uncited'] = st.get('uncited', 0) + 1
                continue
            label = cited or ', '.join(sorted(cited_all))
            if cited and _resolve_lean(cited) is None:
                findings.append((_rel(s), line, cited, 'unresolvable-citation', cited,
                                 'cited file not found, or the basename is ambiguous'))
                continue
            lean = ''
            for c in sorted(cited_all):
                p = _resolve_lean(c)
                if p is not None:
                    lean += io.open(p, encoding='utf-8').read()
            if not lean:
                findings.append((_rel(s), line, label, 'unresolvable-citation', label,
                                 'no cited file found, or every basename is ambiguous'))
                continue
            st['parsed'] = st.get('parsed', 0) + 1
            for head, pair in _duplicate_binders(rows):
                findings.append((_rel(s), line, label, 'duplicate-binder', pair,
                                 'one declaration binds this name twice: %s' % head))
            for row in rows:
                for pat, (g, real) in UNBOUND_GLYPH.items():
                    if not (pat.search(row) and _is_code_row(row)):
                        continue
                    # ⚠⚠⚠ THE PREMISE IS ONE-WAY AND THE RULE FIRED ON THE CONVERSE — `RLY46-10`.
                    #   "This row transcribes a ZPSemilattice signature" ⟹ "the glyph is
                    #   unbound", because ZPSemilattice supplies the bottom as a STRUCT FIELD
                    #   named `bot` with nothing for the pretty glyph to dispatch on. The
                    #   CONVERSE is false: wherever a carrier implements Mathlib's `Bot`/
                    #   `OrderBot`, the glyph is genuine imported notation. The cheap, correct
                    #   discriminator: if the CITED FILE writes the glyph itself, it is bound
                    #   there and this checker has nothing to say.
                    if g in lean:
                        continue
                    findings.append((_rel(s), line, label, 'unbound-glyph', g,
                                     'no notation bound in the cited file; it writes `%s`'
                                     % real))
                row = GLOSS_LABEL.sub('', row, count=1)
                if not _is_code_row(row):
                    continue
                st['code_rows'] = st.get('code_rows', 0) + 1
                row = _claim_part(row)   # judge the claim, not the sentence after it
                for tok in _idents(row):
                    base = tok.split('.')[0]
                    if tok not in lean and base not in lean:
                        findings.append((_rel(s), line, label, 'absent-identifier', tok,
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
    print('             every glyph it prints has a notation bound to it, and no declaration')
    print('             binds one name twice (binder ARITY against Lean is not checked)')
    print('  mode       ADVISORY — never blocks. The enumeration is mechanical; the verdict')
    print('             is judgement, and a checker that guessed would manufacture noise.')
    # ⚠ THE DENOMINATOR, ON EVERY RUN, AND EVERY REMAINDER NAMED. Without it a 0 reads as coverage.
    print('  coverage   %d box call(s): %d judged against a resolved file, %d cite no .lean'
          % (st.get('calls', 0), st.get('parsed', 0), st.get('uncited', 0)))
    print('             anywhere (UNJUDGED); %d row(s) read, %d judged as code, %d not a string'
          % (st.get('rows', 0), st.get('code_rows', 0), st.get('rows_unread', 0)))
    print('             literal (UNJUDGED)')
    for u in st.get('unreadable', []):
        print('  UNREAD     %s — every box in it is UNJUDGED' % u)
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


def _run_fixture(d, files, script):
    """Write `files` ({repo-relative path: text}) and one build script under `d`, point the checker
    at `d`, and return (findings, stats). The real root is restored whatever happens."""
    from pathlib import Path
    for rel, text in files.items():
        p = Path(d) / rel
        os.makedirs(p.parent, exist_ok=True)
        io.open(p, 'w', encoding='utf-8').write(text + '\n')
    sp = Path(d) / 'build_t.py'
    io.open(sp, 'w', encoding='utf-8').write(script)
    real = common.REPO
    try:
        common.REPO = Path(d)
        st = {}
        return scan([sp], st), st
    finally:
        common.REPO = real


def _box(title, *rows):
    return "def_box(\n    %s,\n    [\n%s    ]\n)\n" % (title, ''.join('        %s\n' % r for r in rows))


# One fixture per header shape the corpus writes (`RLY47-1`). Every one must PARSE, so each box
# carries an absent identifier and must fire, and the parsed count must EQUAL the fixture count —
# a counter that double-counts or a pattern that narrows both turn this red.
HEADER_SHAPES = [
    ('two directory levels', "'Typeclass: C (ZeroParadox/Valuation/V.lean)'"),
    ('one directory level', "'Theorem: t (ZeroParadox/T.lean)'"),
    ('bare basename', "'Kleene recursion (T.lean § III)'"),
    ('no kind word before', "'AFAStructure Typeclass (T.lean § I)'"),
    ('kind word with a colon', "'Functor: fB_functor (T.lean)'"),
    ('split literal', "'Theorem: cyclic_decoration_eq_bot '\n    '(ZeroParadox/T.lean § VII′)'"),
]


def selftest():
    """Both halves. A must-fire alone would also pass against a checker that flags everything."""
    import tempfile
    from pathlib import Path
    bad = 0
    print('== code-box identifier check - CONTROLS ==\n')

    def report(name, must, got, detail=''):
        nonlocal bad
        ok = got == must
        bad += 0 if ok else 1
        print('  %-38s %-13s %s%s' % (name, 'MUST FIRE' if must else 'MUST SUPPRESS',
                                      'ok' if ok else '*** FAIL (got %s) ***' % got, detail))

    T = "'Theorem: t (ZeroParadox/T.lean)'"
    CASES = [
        # (name, box body rows, lean content, kind that must fire or None for must-suppress)
        ('clean: identifier present',
         ["'  val_bot    : val bot = &#8868;',"], 'theorem val_bot : val bot = 0', None),
        ('absent identifier fires',
         ["'  accessible : Reachable root v',"], 'structure APG where root : V', 'absent-identifier'),
        ('unbound glyph fires',
         ["'  fixed_bot : selfApp ⊥ = ⊥',"], 'theorem fixed_bot : selfApp bot = bot', 'unbound-glyph'),
        # RLY47-3: the builder writes the ENTITY; only decoding makes the glyph visible.
        ('unbound glyph fires as an ENTITY',
         ["'  fixed_bot : selfApp &#8869; = &#8869;',"], 'theorem fixed_bot : selfApp bot = bot',
         'unbound-glyph'),
        ('short binders are not flagged',
         ["'  scale : L → L',"], 'class C where scale : L -> L', None),
        ('core vocabulary is not flagged',
         ["'  x : Nonempty (Quiver.Path root v)',"],
         'structure APG where accessible : Nonempty (Quiver.Path root v)', None),
        # RLY47-6: a gloss label is not an identifier, and a sentence-final period is not a dot.
        ('a Proof: label is not an identifier',
         ["'Proof: case split ↦ simp [snapEmbed].',"], 'def snapEmbed := 0', None),
        ('a sentence-final word is not dotted',
         ["'(2) val : L &#8594; X  &#8212; valuation into the extended naturals.',"],
         'def val := 0', None),
        # W4K-7: the SHAPE leg. A replaced binder left beside its replacement.
        ('duplicated binder fires',
         ["'theorem decoration_unique (G : APG V) (_G : APG V) : True',"],
         'theorem decoration_unique : True\nstructure APG', 'duplicate-binder'),
        ('one name in two declarations is fine',
         ["'theorem decoration_unique (G : APG V) : True',",
          "'theorem decoration_eq (G : APG V) : True',"],
         'theorem decoration_unique\ntheorem decoration_eq\nstructure APG', None),
    ]
    for name, rows, lean, kind in CASES:
        with tempfile.TemporaryDirectory() as d:
            f, _ = _run_fixture(d, {'ZeroParadox/T.lean': lean}, _box(T, *rows))
        kinds = {x[3] for x in f}
        report(name, kind is not None, (kind in kinds) if kind else bool(f),
               '' if kind is None else '  [%s]' % kind)

    # RLY47-2: the call is parsed, not windowed. A box citing nothing must not BORROW the next box's
    # citation, and a box citing only in a body row must not LOSE the rows above that one.
    with tempfile.TemporaryDirectory() as d:
        f, st = _run_fixture(d, {'ZeroParadox/T.lean': 'theorem present_one : True'},
                             _box("'Theorem: uncited'", "'  absent_one : Reachable root v',")
                             + _box(T, "'  present_one : True',"))
    report('uncited box does not borrow a citation', False, bool(f),
           '  (uncited=%d, want 1)' % st.get('uncited', 0))
    bad += 0 if st.get('uncited', 0) == 1 else 1
    with tempfile.TemporaryDirectory() as d:
        f, _ = _run_fixture(d, {'ZeroParadox/T.lean': 'theorem present_one : True'},
                            _box("'Theorem: t'", "'  absent_one : Reachable root v',",
                                 "'Witness: present_one (ZeroParadox/T.lean).',"))
    report('rows above a body citation are judged', True, bool(f))
    # R-ZERONULL: a script that does not parse is NAMED as unread, never a silent zero.
    with tempfile.TemporaryDirectory() as d:
        f, st = _run_fixture(d, {}, "def_box(\n    'Theorem: t (ZeroParadox/T.lean)',\n")
    report('an unparsable script is reported unread', True, len(st.get('unreadable', [])) == 1)

    # RLY47-1: every header shape parses, and the count is exact.
    with tempfile.TemporaryDirectory() as d:
        lean = {'ZeroParadox/T.lean': 'theorem t', 'ZeroParadox/Valuation/V.lean': 'theorem t'}
        script = ''.join(_box(title, "'  absent_%d : Reachable root v'," % i)
                         for i, (_, title) in enumerate(HEADER_SHAPES))
        f, st = _run_fixture(d, lean, script)
    fired = {int(x[4].split('_')[1]) for x in f
             if x[3] == 'absent-identifier' and x[4].startswith('absent_')}
    for i, (shape, _) in enumerate(HEADER_SHAPES):
        report('header shape parses: %s' % shape, True, i in fired)
    exact = st.get('parsed', 0) == len(HEADER_SHAPES) == st.get('calls', 0)
    bad += 0 if exact else 1
    print('  %-38s %-13s %s' % ('parsed count is exact', 'MUST HOLD',
                                'ok (%d of %d)' % (st.get('parsed', 0), len(HEADER_SHAPES)) if exact
                                else '*** FAIL: parsed %d, calls %d, fixtures %d ***'
                                % (st.get('parsed', 0), st.get('calls', 0), len(HEADER_SHAPES))))

    # RLY47-5: the basename index. Ambiguity is reported, and the cache answers for the root it was
    # built from — warm it on one root, repoint, and the other root's file must be the one found.
    with tempfile.TemporaryDirectory() as d:
        f, _ = _run_fixture(d, {'ZeroParadox/A/D.lean': 'theorem t', 'ZeroParadox/B/D.lean': 'theorem t'},
                            _box("'Theorem: t (D.lean)'", "'  t_t : True',"))
    report('ambiguous basename is unresolvable', True,
           any(x[3] == 'unresolvable-citation' for x in f))
    with tempfile.TemporaryDirectory() as d1, tempfile.TemporaryDirectory() as d2:
        real = common.REPO
        try:
            for d, sub in ((d1, 'One'), (d2, 'Two')):
                os.makedirs(Path(d) / 'ZeroParadox' / sub)
                io.open(Path(d) / 'ZeroParadox' / sub / 'Q.lean', 'w', encoding='utf-8').write('x')
            common.REPO = Path(d1)
            _resolve_lean('Q.lean')
            common.REPO = Path(d2)
            got = _resolve_lean('Q.lean')
        finally:
            common.REPO = real
    report('basename cache answers for the current root', True,
           got is not None and str(got).startswith(str(d2)))

    # ⚠⚠ THE PRODUCTION ENUMERATION, WHICH NO CONTROL ABOVE REACHES — `RLY46-2`. Every case above
    #   passes `paths=[...]`, so `scan()`'s default glob never executes under test: emptying it
    #   left `--selftest` BYTE-IDENTICAL and PASS.
    print('  MUST HOLD  (the production enumeration is non-empty and fully read)')
    _prod = sorted((common.REPO / 'scripts').glob('build_*.py'))
    _st = {}
    scan(stats=_st)
    _ok = (len(_prod) >= 10 and _st.get('calls', 0) >= 100 and _st.get('parsed', 0) >= 1
           and not _st.get('unreadable'))
    bad += 0 if _ok else 1
    print('    %-40s %s (%d script(s), %d call(s), %d parsed, %d unreadable)'
          % ('default glob finds boxes to judge',
             'ok' if _ok else '*** VACUOUS OR UNREAD ***',
             len(_prod), _st.get('calls', 0), _st.get('parsed', 0), len(_st.get('unreadable', []))))

    print('\n  controls: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
