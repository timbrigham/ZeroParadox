"""
Zero Paradox — ZP-G: Category Theory PDF Builder
Version 1.6 | May 2026
Changes from v1.5:
  - D7' well-definedness note corrected: "all structural claims below are invariant under this
    additive constant" replaced with explicit scoping — invariance is a consequence of what
    ZP-G chooses to claim (finite/zero/undefined), not a general AIT property.
Changes from v1.4:
  - Lean scope remark for T6-b/T6-c strengthened: now states explicitly that the Lean proofs
    verify nothing about Kolmogorov complexity — they prove only that a ℕ-valued function is ≥ 0
    (Nat.zero_le _), which is true by type for any such function. T6-b strict inequality and
    T6-c subadditivity have no Lean proofs. T6-b and T6-c status lines and validation table rows
    updated to remove unqualified ✓ and mark as PDF-level only.
Changes from v1.3:
  - Lean scope note added after T6-c: T6-b strict inequality and T6-c subadditivity are
    K-specific AIT content outside the ZPSurprisal skeleton; Lean proofs reduce to Nat.zero_le _
Changes from v1.2:
  - R2 added: Remark connecting initial object structure (T2 + AX-G2) to ZP-A CC-2 (⊥ = {⊥})
  - All prior results, axioms, and definitions unchanged
Changes from v1.1:
  - Theorem/Proposition/Lemma hierarchy applied: T1→Proposition, T2/T3→Lemma,
    T4/T5→Proposition, T6-a/T6-b→Lemma, T6-c→Proposition; T6/T7 remain Theorems
  - Companion cross-reference note added after intro paragraphs
Follows all rules in pdf rendering standards:
  - DejaVu fonts only
  - Checkmark always wrapped in <font name="DV">
  - All table cells are Paragraph objects
  - No unicode subscripts — use sub/super tags
  - US Letter, 1-inch margins, TW = 6.5 inch
"""

import os
from reportlab.lib import colors
from reportlab.lib.pagesizes import LETTER
from reportlab.lib.units import inch
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer,
                                 Table, TableStyle, HRFlowable)
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

# ── 1. FONT REGISTRATION ──────────────────────────────────────────────────────
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
FONT_DIR   = os.path.join(SCRIPT_DIR, 'fonts') + os.sep

print(f'[build_zpg] SCRIPT_DIR: {SCRIPT_DIR}')
print(f'[build_zpg] FONT_DIR:   {FONT_DIR}')
print('[build_zpg] Registering fonts...')
pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'));         print('  DV ok')
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'));    print('  DV-B ok')
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf')); print('  DV-I ok')
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf')); print('  DV-BI ok')
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'STIXTwo-Math.ttf'));         print('  DVS ok')
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'STIXTwo-Math.ttf'));   print('  DVS-B ok')
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'STIXTwo-Math.ttf')); print('  DVS-I ok')
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'STIXTwo-Math.ttf')); print('  DVS-BI ok')
print('[build_zpg] Fonts registered.')

# ── 2. COLORS ─────────────────────────────────────────────────────────────────
BLUE        = colors.HexColor('#2E75B6')
BLUE_LITE   = colors.HexColor('#D5E8F0')
GREEN       = colors.HexColor('#2E7D32')
GREEN_LITE  = colors.HexColor('#E8F5E9')
ORANGE      = colors.HexColor('#BF4E30')
ORANGE_LITE = colors.HexColor('#FBE9E7')
SLATE       = colors.HexColor('#455A64')
SLATE_LITE  = colors.HexColor('#ECEFF1')
AMBER       = colors.HexColor('#B07800')
AMBER_LITE  = colors.HexColor('#FFF8E7')
GREY_LITE   = colors.HexColor('#F5F5F5')
WHITE       = colors.white

# ── 3. PAGE GEOMETRY ──────────────────────────────────────────────────────────
TW = 6.5 * inch
LM = RM = 1.0 * inch
TM = BM = 1.0 * inch

# ── 4. PARAGRAPH STYLES ───────────────────────────────────────────────────────
S = {
    'title':      ParagraphStyle('title',      fontName='DV-B',  fontSize=18, leading=24,
                                 spaceAfter=6, alignment=1),
    'subtitle':   ParagraphStyle('subtitle',   fontName='DV-I',  fontSize=11, leading=15,
                                 spaceAfter=4, alignment=1),
    'h1':         ParagraphStyle('h1',         fontName='DV-B',  fontSize=13, leading=18,
                                 spaceBefore=14, spaceAfter=5, textColor=BLUE),
    'h2':         ParagraphStyle('h2',         fontName='DV-B',  fontSize=11, leading=15,
                                 spaceBefore=10, spaceAfter=4, textColor=BLUE),
    'body':       ParagraphStyle('body',       fontName='DVS',   fontSize=10, leading=14,
                                 spaceAfter=6),
    'bodyI':      ParagraphStyle('bodyI',      fontName='DVS-I', fontSize=10, leading=14,
                                 spaceAfter=6),
    'label':      ParagraphStyle('label',      fontName='DV-B',  fontSize=9,  leading=13,
                                 textColor=WHITE),
    'labelAmber': ParagraphStyle('labelAmber', fontName='DV-B',  fontSize=9,  leading=13,
                                 textColor=AMBER),
    'cell':       ParagraphStyle('cell',       fontName='DVS',   fontSize=9,  leading=13),
    'cellI':      ParagraphStyle('cellI',      fontName='DVS-I', fontSize=9,  leading=13),
    'note':       ParagraphStyle('note',       fontName='DVS-I', fontSize=9,  leading=13,
                                 spaceAfter=4),
    'endnote':    ParagraphStyle('endnote',    fontName='DVS-I', fontSize=9,  leading=13,
                                 alignment=1),
}

# ── 5. HELPERS ────────────────────────────────────────────────────────────────

def sp(n=6):
    return Spacer(1, n)

def hr():
    return HRFlowable(width='100%', thickness=0.5,
                      color=colors.HexColor('#AAAAAA'),
                      spaceAfter=6, spaceBefore=2)

def fix(text):
    sub_map = {'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4',
               '₅':'5','₆':'6','₇':'7','₈':'8','₉':'9',
               'ₙ':'n','ₖ':'k','ₘ':'m','ᵢ':'i','ⱼ':'j'}
    for ch, rep in sub_map.items():
        text = text.replace(ch, f'<sub>{rep}</sub>')
    text = text.replace('✓', '<font name="DV">&#10003;</font>')
    text = text.replace('∅', '<font name="DV">&#8709;</font>')
    replacements = [
        ('⊥','&#8869;'),('∨','&#8744;'),('∧','&#8743;'),
        ('≤','&#8804;'),('≥','&#8805;'),('≠','&#8800;'),
        ('∈','&#8712;'),('∉','&#8713;'),('⊆','&#8838;'),
        ('∀','&#8704;'),('∃','&#8707;'),('∞','&#8734;'),
        ('→','&#8594;'),('←','&#8592;'),('↔','&#8596;'),
        ('⇒','&#8658;'),('∘','&#8728;'),('—','&#8212;'),
        ('–','&#8211;'),('·','&#183;'),('×','&#215;'),
        ('−','&#8722;'),('≡','&#8801;'),('≅','&#8773;'),
        ('≇','&#8775;'),('≇','&#8775;'),
        ('ε','&#949;'),('α','&#945;'),('β','&#946;'),
        ('γ','&#947;'),('δ','&#948;'),('ι','&#953;'),
        ('τ','&#964;'),('φ','&#966;'),
        ('ℚ','&#8474;'),('ℤ','&#8484;'),('ℂ','&#8450;'),
        ('ℕ','&#8469;'),('ℝ','&#8477;'),
        ('≈','&#8776;'),('∑','&#8721;'),('¬','&#172;'),
    ]
    for char, entity in replacements:
        if char in text:
            text = text.replace(char, entity)
    return text

def body(text, style='body'):
    return Paragraph(fix(text), S[style])

def _box(title, title_style, hdr_bg, status, status_bg, rows):
    data = [
        [Paragraph(fix(title), S[title_style])],
        [Paragraph(fix(status), S['cellI'])],
    ]
    for r in rows:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  hdr_bg),
        ('BACKGROUND',    (0,1), (-1,1),  status_bg),
        ('BACKGROUND',    (0,2), (-1,-1), GREY_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, hdr_bg),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, hdr_bg),
        ('LINEBELOW',     (0,1), (-1,-2), 0.5, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW], repeatRows=1)
    t.setStyle(ts)
    return t

def def_box(title, status, rows):
    return _box(title, 'label', BLUE, status, BLUE_LITE, rows)

def result_box(title, status, rows):
    return _box(title, 'label', GREEN, status, GREEN_LITE, rows)

def axiom_box(title, status, rows):
    return _box(title, 'label', ORANGE, status, ORANGE_LITE, rows)

def remark_box(title, status, rows):
    return _box(title, 'label', SLATE, status, SLATE_LITE, rows)

def import_box(title, status, rows):
    data = [
        [Paragraph(fix(title), S['labelAmber'])],
        [Paragraph(fix(status), S['cellI'])],
    ]
    for r in rows:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), AMBER_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, AMBER),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, AMBER),
        ('LINEBELOW',     (0,1), (-1,-2), 0.5, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW], repeatRows=1)
    t.setStyle(ts)
    return t

def data_table(headers, rows_data, col_widths):
    hdr_row = [Paragraph(fix(h), S['label']) for h in headers]
    data    = [hdr_row]
    for row in rows_data:
        data.append([Paragraph(fix(str(c)), S['cell']) for c in row])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  BLUE),
        ('ROWBACKGROUNDS',(0,1), (-1,-1), [WHITE, GREY_LITE]),
        ('BOX',           (0,0), (-1,-1), 0.5, BLUE),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, BLUE),
        ('INNERGRID',     (0,1), (-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 4),
        ('BOTTOMPADDING', (0,0), (-1,-1), 4),
        ('LEFTPADDING',   (0,0), (-1,-1), 6),
        ('RIGHTPADDING',  (0,0), (-1,-1), 6),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=col_widths, repeatRows=1)
    t.setStyle(ts)
    return t

def make_doc(path):
    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        ft = (f'Zero Paradox ZP-G: Category Theory  |  Version 1.6  |  May 2026  |'
              f'  Internal Working Document  |  Page {doc.page}')
        canvas.drawCentredString(LETTER[0] / 2, 0.6 * inch, ft)
        canvas.restoreState()
    return SimpleDocTemplate(
        path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title='ZP-G: Category Theory',
        author='Zero Paradox Project',
        onFirstPage=footer_cb, onLaterPages=footer_cb,
    )


def build_zpg(out_path):
    print(f'[build_zpg] Output: {out_path}')
    doc = make_doc(out_path)
    E   = []

    print('[build_zpg] Building title block...')
    # ── TITLE BLOCK ───────────────────────────────────────────────────────────
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-G: Category Theory', S['subtitle']),
        Paragraph('Version 1.6 | May 2026', S['bodyI']),
        Paragraph(
            '<i>Supersedes v1.4 | v1.5: Lean scope disclosure for T6-b and T6-c strengthened — '
            'Lean proofs verify only that a &#8469;-valued function is &#8805; 0 (Nat.zero_le _), '
            'which is trivially true by type for any such function and says nothing about Kolmogorov '
            'complexity. T6-b strict inequality (K &gt; 0 for distinct objects) and T6-c subadditivity '
            'have no Lean proofs. Status lines and validation table updated accordingly. | '
            'v1.4: Lean scope note added after T6-c — K-specific AIT content outside ZPSurprisal '
            'skeleton identified | All prior results unchanged</i>',
            S['note']),
        sp(8),
        hr(),
        sp(4),
    ]

    # ── INTRO PARAGRAPHS ──────────────────────────────────────────────────────
    E += [
        body('This document is self-contained within category theory, with one explicit import from '
             'ZP-C: the conditional Kolmogorov complexity K(x|n) and the coding theorem connecting '
             'it to Shannon entropy. That import is named and labelled; it replaces the v1.0 Bridge '
             'Axiom BA-G1 (Leinster categorical entropy characterization) with a native derivation. All '
             'other content from ZP-A, ZP-B, ZP-D, and ZP-E remains excluded from this document. '
             'Cross-framework connections are deferred to ZP-H.'),
        body('Honest labelling is the governing discipline. Every claim is marked as Axiom, Definition, '
             'Derived, Import, Design Commitment, or Remark. Nothing slides between categories.'),
        Paragraph(
            '<i>Version 1.1 changes from v1.0: '
            '(1) D7 replaced by D7\' (conditional Kolmogorov complexity K(B|A) as native categorical surprisal). '
            '(2) Import I-KC added: K(x|y) and the Kolmogorov coding theorem imported from ZP-C as a named dependency. '
            '(3) BA-G1 (Leinster Bridge Axiom) demoted to Remark R-BA: a compatibility result, no longer a theorem premise. '
            '(4) T6 rebuilt on D7\'; proof is now self-contained within ZP-G plus the named ZP-C import. OQ-G1 closed. '
            '(5) All theorems from v1.0 that did not depend on BA-G1 (T1 through T5, T7) are unchanged in statement and proof.</i>',
            S['note']),
        Paragraph(
            '<i>Version 1.2 changes from v1.1: Theorem/Proposition/Lemma hierarchy applied throughout. '
            'T1 relabelled Proposition (subsidiary uniqueness result). '
            'T2, T3 relabelled Lemma (stepping-stone results for T6/T7). '
            'T4, T5 relabelled Proposition (derived but subsidiary). '
            'T6-a, T6-b relabelled Lemma (helpers for T6). '
            'T6-c relabelled Proposition (supports T6 but not the central claim). '
            'T6 and T7 remain Theorems — central claims of their sections. '
            'All statements and proofs are unchanged.</i>',
            S['note']),
        Paragraph(
            '<i>Version 1.3 changes from v1.2: Remark R2 added (Categorical Expression of Self-Containment). '
            'Connects initial object structure (T2 + AX-G2) to ZP-A CC-2 (⊥ = {⊥}). '
            'All prior results, axioms, and definitions unchanged.</i>',
            S['note']),
        Paragraph(
            '<i>Version 1.4 changes from v1.3: Lean scope note added after T6-c — T6-b strict inequality '
            'and T6-c subadditivity are K-specific AIT content outside the ZPSurprisal skeleton; '
            'Lean proofs reduce to Nat.zero_le _ (non-negativity by type). '
            'T6-b and T6-c statements and proofs unchanged.</i>',
            S['note']),
        Paragraph(
            '<i>Version 1.6 changes from v1.5: D7\' well-definedness note corrected — '
            '"all structural claims below are invariant under this additive constant" replaced '
            'with explicit scoping: invariance holds because of what ZP-G chooses to claim '
            '(finite/zero/undefined), not as a general property of K-complexity.</i>',
            S['note']),
        Paragraph(
            '<i>Version 1.5 changes from v1.4: Lean scope disclosure strengthened. The v1.4 note '
            'correctly identified the limitation but did not make the consequence fully explicit. '
            'v1.5 states it plainly: the Lean proofs for T6-b and T6-c verify nothing about '
            'Kolmogorov complexity. Nat.zero_le _ is trivially true for any &#8469;-valued function, '
            'regardless of mathematical content. T6-b (strict inequality) and T6-c (subadditivity) '
            'are not Lean-verified. T6-b and T6-c status lines updated from "Derived — ✓" to '
            '"Derived (PDF-level); not Lean-verified". Validation table updated accordingly.</i>',
            S['note']),
        body('<i>Illustrated Companion: A paired ZP-G Illustrated Companion provides concrete examples '
             'and visual intuitions for the results here. Examples are kept separate from the formal '
             'layers to distinguish illustrative material from proofs.</i>', 'bodyI'),
        body('<i>Note on sequencing: The Zero Paradox framework labels its layers A through H, '
             'intentionally omitting F. ZP-G follows ZP-E directly; there is no missing document.</i>',
             'bodyI'),
        sp(4),
        hr(),
    ]

    print('[build_zpg] Building Section I: Categorical Primitives...')
    # ── I. CATEGORICAL PRIMITIVES ─────────────────────────────────────────────
    E.append(Paragraph('I. Categorical Primitives', S['h1']))
    E.append(body('Definitions D1 through D6 and results T1 through T5 are unchanged from v1.0. '
                  'They are reproduced here for completeness and self-reference.'))

    E.append(Paragraph('1.1 The Definition of a Category', S['h2']))
    E.append(def_box(
        'Definition D1 — Category',
        'Status: Definition — foundational',
        [
            'A category C consists of:',
            '(i) Objects: A collection ob(C), written A, B, X, 0, ...',
            '(ii) Morphisms: For each ordered pair (A, B), a collection hom(A, B) of morphisms, written f: A → B.',
            '(iii) Composition: ∘: hom(B,C) × hom(A,B) → hom(A,C), written g ∘ f.',
            '(iv) Identity: For each A, a morphism id<sub>A</sub>: A → A.',
            'Associativity: h ∘ (g ∘ f) = (h ∘ g) ∘ f.',
            'Unit laws: id<sub>B</sub> ∘ f = f = f ∘ id<sub>A</sub>.',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'Definition D2 — Morphism Uniqueness Notation',
        'Status: Definition',
        [
            'A morphism f: A → B is unique if for any g, h: A → B, g = h. Written: ∃! f: A → B.',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('1.2 Initial and Terminal Objects', S['h2']))
    E.append(def_box(
        'Definition D3 — Initial Object',
        'Status: Definition — load-bearing',
        [
            'An object 0 ∈ ob(C) is initial if for every X ∈ ob(C), there exists a unique morphism '
            '&#953;<sub>X</sub>: 0 → X.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Proposition T1 — Uniqueness of the Initial Object',
        'Status: Derived — standard category theory [unchanged from v1.0]',
        [
            'If 0 and 0\' are both initial in C, ∃! isomorphism 0 ≅ 0\'. '
            'The initial object is unique up to unique isomorphism.',
            'Proof: ∃! f: 0 → 0\' and ∃! g: 0\' → 0. Initiality forces g ∘ f = id<sub>0</sub> and '
            'f ∘ g = id<sub>0\'</sub>. Therefore f is a unique isomorphism. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'Definition D4 — Terminal Object',
        'Status: Definition — defined for exclusion',
        [
            'An object 1 ∈ ob(C) is terminal if for every X ∈ ob(C), ∃! morphism '
            '&#964;<sub>X</sub>: X → 1. The Zero Paradox framework is not a zero object category (0 ≇ 1).',
        ]
    ))

    print('[build_zpg] Building Section II: Foundational Axioms...')
    # ── II. THE FOUNDATIONAL AXIOMS OF ZP-G ──────────────────────────────────
    E.append(Paragraph('II. The Foundational Axioms of ZP-G', S['h1']))

    E.append(axiom_box(
        'Axiom AX-G1 — Asymmetry Axiom',
        'Status: Axiom — foundational structural commitment [unchanged from v1.0]',
        [
            'The category C possesses an initial object 0 and no terminal object.',
            'Formally: ∃ 0 ∈ ob(C) satisfying D3. ¬∃ 1 ∈ ob(C) satisfying D4.',
            'Correspondence: In ZP-A: join-semilattice without &#8868; and without ∧. '
            'In ZP-B: Q<sub>2</sub> has no element to which all paths converge. '
            'The present axiom is the categorical generalization.',
        ]
    ))
    E.append(sp(6))

    E.append(axiom_box(
        'Axiom AX-G2 — Source Asymmetry',
        'Status: Axiom — foundational [unchanged from v1.0]',
        [
            'For any non-initial object X ≠ 0: hom(X, 0) = ∅.',
            'Motivation: The categorical expression of irreversibility. Morphisms '
            '&#953;<sub>X</sub>: 0 → X exist for all X. Their reversal does not exist. '
            'AX-G2 is consistent with AX-G1 but not derivable from it.',
        ]
    ))

    print('[build_zpg] Building Section III: Universal Constituent and Unreachability...')
    # ── III. UNIVERSAL CONSTITUENT AND UNREACHABILITY ─────────────────────────
    E.append(Paragraph('III. Universal Constituent and Unreachability', S['h1']))

    E.append(result_box(
        'Lemma T2 — Universal Constituent',
        'Status: Derived — from D3 and AX-G1 [unchanged from v1.0]',
        [
            'For every X ∈ ob(C), ∃! &#953;<sub>X</sub>: 0 → X. '
            'The initial object 0 is the universal categorical source.',
            'Proof: Immediate from D3 and AX-G1. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Lemma T3 — Unreachability of 0',
        'Status: Derived — from AX-G2 [unchanged from v1.0]',
        [
            'For any X ≠ 0: hom(X, 0) = ∅. The initial object 0 is unreachable from any non-initial object.',
            'Proof: Direct from AX-G2. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark R1 — Structural Inversion — The Categorical Zero Paradox',
        'Status: Remark [unchanged from v1.0]',
        [
            'T2 and T3 together constitute the categorical Zero Paradox. 0 reaches every object (T2); '
            'no non-initial object reaches 0 (T3). This is not a logical contradiction. It is a structural '
            'inversion: the unique universal source is the unique object with no incoming non-trivial morphisms.',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark R2 — Categorical Expression of Self-Containment',
        'Status: Remark — connecting note to ZP-A CC-2 [new in v1.3]',
        [
            'R1 frames the structural inversion of 0. This remark connects that structure to ZP-A CC-2: '
            '⊥ = {⊥}. The null state is its own extension — a Quine atom. A self-containing object has '
            'no external interpreter by structure; it IS its own interpretation.',
            'In categorical terms, this corresponds to two conditions together: (1) AX-G2: '
            'hom(X, 0) = ∅ for all X ≠ 0 — no morphism can reach inside 0 from outside; and '
            '(2) T2: ∃! &#953;<sub>X</sub>: 0 → X for all X — 0 is structurally present in every object. '
            'Together these are the categorical image of undifferentiated self-containment: unreachable '
            'from without, yet constitutive of everything.',
            '0 "points in all directions" (T2) because it is the undifferentiated ground from which all '
            'differentiation proceeds — not because it selects a direction. The uniqueness of each '
            '&#953;<sub>X</sub> is not a choice among alternatives; it is the absence of internal '
            'structure that would allow differentiation among morphisms.',
            'This remark bridges ZP-G to ZP-A CC-2. The formal correspondence between the categorical '
            'initial object structure and the set-theoretic Quine atom ⊥ = {⊥} is made explicit in ZP-H.',
        ]
    ))

    print('[build_zpg] Building Section IV: Monotone Structure...')
    # ── IV. MONOTONE STRUCTURE AND THE ADDITIVE ONTOLOGY ─────────────────────
    E.append(Paragraph('IV. Monotone Structure and the Additive Ontology', S['h1']))

    E.append(def_box(
        'Definition D5 — Morphism Chain',
        'Status: Definition [unchanged from v1.0]',
        [
            'A morphism chain of length n from 0 is a sequence:',
            '0 = X<sub>0</sub> → X<sub>1</sub> → ... → X<sub>n</sub>',
            'where each X<sub>k</sub> → X<sub>k+1</sub> is a morphism in C.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Proposition T4 — Chains are Forward-Only',
        'Status: Derived — from AX-G2 [unchanged from v1.0]',
        [
            'No morphism chain from 0 can return to 0 through non-initial objects.',
            'Proof: A return morphism X<sub>n</sub> → 0 for X<sub>n</sub> ≠ 0 would contradict AX-G2. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'Definition D6 — Functor',
        'Status: Definition — standard category theory [unchanged from v1.0]',
        [
            'A functor F: C → D consists of an object map F: ob(C) → ob(D) and a morphism map '
            'F: hom<sub>C</sub>(A,B) → hom<sub>D</sub>(F(A), F(B)), preserving composition and identity.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Proposition T5 — Functors Preserve Initial Objects',
        'Status: Derived — [OQ-G2 closed in ZP-H T-H1; unchanged from v1.0]',
        [
            'For each instantiation functor F ∈ {F<sub>A</sub>, F<sub>B</sub>, F<sub>C</sub>, F<sub>D</sub>}, '
            'F(0) is an initial object in the codomain. '
            'Verified by direct universal property check in ZP-H T-H1. ✓',
        ]
    ))

    print('[build_zpg] Building Section V: Kolmogorov Import...')
    # ── V. THE KOLMOGOROV IMPORT FROM ZP-C ───────────────────────────────────
    E.append(Paragraph('V. The Kolmogorov Import from ZP-C', S['h1']))
    E.append(body('This section contains the single import from outside category theory that ZP-G v1.1 '
                  'requires. It is named, scoped, and labelled explicitly. It replaces BA-G1 (the Leinster '
                  'Bridge Axiom from v1.0) as the informational foundation of D7\'.'))

    E.append(import_box(
        'Import I-KC — Conditional Kolmogorov Complexity from ZP-C',
        'Status: Import — from ZP-C D1 and standard algorithmic information theory',
        [
            'What is imported: The conditional Kolmogorov complexity K(x|y), defined as the length of the '
            'shortest program p such that U(p, y) = x, where U is a fixed universal Turing machine:',
            'K(x|y) = min { |p| : U(p, y) = x }',
            'Key property — The Coding Theorem: For any computable probability measure P, Kolmogorov '
            'complexity and Shannon entropy are related up to an additive constant c (depending only on U, '
            'not on x or y):',
            'K(x|y) &#8776; &#8722;log<sub>2</sub> P(x|y) + O(c)',
            'The coding theorem is a standard result of algorithmic information theory (Li and Vitanyi, An '
            'Introduction to Kolmogorov Complexity and Its Applications). It is not derived within ZP-G. '
            'It is imported as a named result.',
            'Scope of import: I-KC imports K(x|y) and the coding theorem only. No other content from ZP-C is '
            'imported into ZP-G. The Kolmogorov complexity machinery is already present in ZP-C D1 '
            '(incompressibility threshold P<sub>0</sub>), so I-KC introduces no new external dependency into the overall '
            'Zero Paradox framework — it only introduces a dependency within ZP-G specifically.',
            'Computability note: K(x|y) is not computable in general (it is approximable from above by standard '
            'results). This is not a defect for the present purposes: the framework requires that K(x|y) be '
            'well-defined, not that it be computable. The ontological claims of ZP-G do not depend on computability.',
            'Status: This is an import, not a bridge axiom. A bridge axiom is a claim that cannot be derived '
            'from either side and must be assumed. K(x|y) is a defined mathematical object with a complete '
            'internal theory. I-KC is a decision to use that object within ZP-G, not an assumption about it.',
        ]
    ))

    print('[build_zpg] Building Section VI: Categorical Information Theory...')
    # ── VI. CATEGORICAL INFORMATION THEORY [REBUILT IN v1.1] ─────────────────
    E.append(Paragraph('VI. Categorical Information Theory [Rebuilt in v1.1]', S['h1']))
    E.append(Paragraph('6.1 Native Categorical Surprisal — Definition D7\'', S['h2']))
    E.append(body('Version 1.0 defined categorical surprisal via the Shannon entropy functor H imported '
                  'through BA-G1. Version 1.1 replaces this with conditional Kolmogorov complexity, '
                  'imported via I-KC. The definition is native to the morphism structure of C.'))

    E.append(def_box(
        'Definition D7\' — Native Categorical Surprisal',
        'Status: Definition — from D5, I-KC [replaces D7 from v1.0]',
        [
            'Let f: A → B be a morphism in C. Represent A and B as binary strings x<sub>A</sub> and x<sub>B</sub> '
            'via any injective encoding consistent with the morphism structure of C. The categorical surprisal of f is:',
            'I(f) = K(x<sub>B</sub> | x<sub>A</sub>)',
            'the conditional Kolmogorov complexity of the target given the source.',
            'Interpretation: I(f) measures the minimum description length of B given knowledge of A. It is the '
            'irreducible informational content added by the transition f: A → B, independent of any probability distribution.',
            'Well-definedness: K(x<sub>B</sub>|x<sub>A</sub>) depends on the encoding of objects as strings. Different encodings '
            'yield values differing by at most an additive constant c (the coding theorem constant of I-KC). '
            'All claims in ZP-G are stated in terms of whether I(f) is finite, zero, or undefined — qualitative '
            'properties that are invariant under any additive constant. This invariance is a consequence of what '
            'ZP-G chooses to claim, not a general property of K-complexity (additive constants can matter '
            'for precise K-complexity comparisons in AIT).',
            'Relationship to v1.0 D7: By the coding theorem (I-KC), K(x<sub>B</sub>|x<sub>A</sub>) ≈ &#8722;log<sub>2</sub> P(x<sub>B</sub>|x<sub>A</sub>) + O(c) '
            'for any computable measure P. Therefore D7\' and D7 are equivalent up to O(c). The choice of D7\' '
            'over D7 is not a change in what is being measured; it is a change in how the measure is defined — '
            'natively versus via import.',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('6.2 Properties of the Native Surprisal', S['h2']))

    E.append(result_box(
        'Lemma T6-a — Surprisal of the Identity Morphism is Zero',
        'Status: Derived — from D7\' and I-KC',
        [
            'Claim: I(id<sub>A</sub>) = K(x<sub>A</sub>|x<sub>A</sub>) = 0 up to the additive constant c.',
            'Proof: The shortest program producing x<sub>A</sub> given x<sub>A</sub> is the empty program (output the input). '
            'Therefore K(x<sub>A</sub>|x<sub>A</sub>) = 0 up to c. The identity morphism adds no informational content. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Lemma T6-b — Surprisal is Non-Negative for Forward Morphisms',
        'Status: Derived — PDF-level (from D5, D7\', AX-G2); NOT Lean-verified — see Lean scope remark below',
        [
            'Claim: For any morphism f: A → B in a forward morphism chain from 0, I(f) ≥ 0 up to c, '
            'with strict inequality when A ≠ B.',
            'Proof: K(x<sub>B</sub>|x<sub>A</sub>) ≥ 0 by definition (program length is non-negative). Strict inequality holds '
            'when x<sub>B</sub> cannot be computed from x<sub>A</sub> by the empty program — i.e., when A and B are distinct objects '
            'encoding distinct states. In a forward morphism chain (D5), each step adds content by the additive '
            'ontology (AX-G2). ✓',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Proposition T6-c — Surprisal Accumulates Along Chains',
        'Status: Derived — PDF-level (from D5, T6-b, subadditivity of K); NOT Lean-verified — see Lean scope remark below',
        [
            'Claim: For a morphism chain 0 = X<sub>0</sub> → X<sub>1</sub> → ... → X<sub>n</sub>, the total surprisal '
            '&#8721; I(X<sub>k</sub> → X<sub>k+1</sub>) ≥ 0, with monotone accumulation as n increases.',
            'Proof: By subadditivity of Kolmogorov complexity: K(x<sub>n</sub>|x<sub>0</sub>) ≤ '
            '&#8721; K(x<sub>k+1</sub>|x<sub>k</sub>) + O(n&#183;c). Each term is ≥ 0 by T6-b. '
            'Adding distinct objects strictly increases the total. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark — Lean Scope of T6-b and T6-c',
        'Status: Scope note [strengthened v1.5] — T6-b and T6-c are NOT Lean-verified for their mathematical claims',
        [
            '<b>T6-b and T6-c are not Lean-verified.</b> The ZPG.lean proofs for these results compile '
            'without error, but they verify nothing about Kolmogorov complexity. The ZPSurprisal typeclass '
            'defines surp : hom &#8594; &#8469; (surprisal as a natural number) and the proofs reduce to '
            'Nat.zero_le _, which states that any natural number is &#8805; 0. This is trivially true by '
            'type for <i>any</i> &#8469;-valued function, regardless of its mathematical content. '
            'A compiling Lean proof here does not mean the K-theoretic claims have been verified.',
            'What the Lean proofs do NOT establish: (1) T6-b strict inequality — '
            'K(x<sub>B</sub>|x<sub>A</sub>) &gt; 0 when A &#8775; B (distinct objects cannot have zero description length). '
            '(2) T6-c subadditivity — K(x<sub>n</sub>|x<sub>0</sub>) &#8804; '
            '&#8721; K(x<sub>k+1</sub>|x<sub>k</sub>) + O(n&#183;c) (total surprisal along a chain). '
            'These are standard and correct results from algorithmic information theory, but they require '
            'a K-formalization that does not exist in Lean 4 / Mathlib.',
            'What IS Lean-verified: T6-a (identity morphism has zero surprisal — from surp_id), '
            'T6 Part II (inward surprisal is undefined — from AX-G2 and the absence of morphisms to 0), '
            'and T7 insofar as it depends on Parts II, III, V, VI. T6 Part I (outward accumulation) '
            'and T7 Part IV rely on T6-b and T6-c and are therefore also PDF-level only.',
            'Readers citing "the Lean-verified ZP-G framework" should note this boundary. '
            'The PDF-level arguments for T6-b and T6-c are mathematically valid — these are standard '
            'K-theoretic results (Li and Vitanyi). The gap is Lean scope, not mathematical correctness.',
        ]
    ))

    print('[build_zpg] Building Section VII: Informational Singularity...')
    # ── VII. THE INFORMATIONAL SINGULARITY OF 0 [REBUILT IN v1.1] ────────────
    E.append(Paragraph('VII. The Informational Singularity of 0 [Rebuilt in v1.1]', S['h1']))
    E.append(body('This is the central theorem of the information-theoretic section. In v1.0, it depended on '
                  'BA-G1. In v1.1, it is proved from D7\' and AX-G2 alone, with I-KC as the only external dependency.'))

    E.append(result_box(
        'Theorem T6 — Informational Singularity of 0',
        'Status: Derived — from AX-G2, D7\', I-KC [rebuilt from v1.0, OQ-G1 closed]',
        [
            'Setup: Let 0 be the initial object of C (AX-G1). Let I(f) = K(x<sub>B</sub>|x<sub>A</sub>) be the categorical '
            'surprisal (D7\'). Let I-KC provide the Kolmogorov framework.',
            'Part I — Outward surprisal accumulates (from T6-b, T6-c): For any morphism chain '
            '0 = X<sub>0</sub> → ... → X<sub>n</sub>, &#8721; I(X<sub>k</sub> → X<sub>k+1</sub>) ≥ 0, '
            'with strict accumulation as n increases. ✓',
            'Part II — Inward surprisal is undefined (from AX-G2): For any X ≠ 0, hom(X, 0) = ∅ (AX-G2). '
            'Therefore D7\' cannot be applied to any morphism f: X → 0 from outside 0 — no such morphism '
            'exists. I(X → 0) is undefined not because K diverges to infinity, but because there is no morphism '
            'to apply D7\' to. The undefined-domain condition is strictly stronger than divergence. ✓',
            'Part III — The singularity: 0 is the unique object in C for which outward surprisal is defined and '
            'accumulates (Part I) while inward surprisal is undefined by absence of morphisms (Part II). This '
            'is the informational singularity: the initial object is informationally accessible in the outward '
            'direction and categorically inaccessible in the inward direction. The singularity is structural, not '
            'numerical. It does not require K to diverge — it requires only AX-G2 and D7\'. ✓',
            'Comparison with ZP-C (to be reconciled in ZP-H T-H2): ZP-C establishes that the discrete surprisal '
            'DF diverges (numerically, to &#8734;) along infinite sequences approaching 0 in Q<sub>2</sub>. T6 Part II '
            'establishes that I(X → 0) is undefined (domain-absent) for any X ≠ 0 in C. These are compatible: '
            'undefined is stronger than infinite. ZP-H T-H2 proves they describe the same obstruction under '
            'the functor F<sub>C</sub>.',
            'Status: DERIVED. Depends on AX-G1, AX-G2, D3, D5, D7\', I-KC, T6-a, T6-b, T6-c. OQ-G1 is closed. '
            'BA-G1 is no longer a premise of T6. ✓',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('7.1 Compatibility with Shannon Entropy — BA-G1 Demoted to Remark', S['h2']))

    E.append(remark_box(
        'Remark R-BA — Compatibility of D7\' with the Shannon Entropy Functor',
        'Status: Remark — BA-G1 demoted from Bridge Axiom [v1.0] to Compatibility Remark [v1.1]',
        [
            'Version 1.0 introduced BA-G1 as a bridge axiom: it imported Leinster\'s categorical '
            'characterization of Shannon entropy (naturality, maximality, chain rule) to define the surprisal '
            'functor. BA-G1 was the only bridge axiom in ZP-G v1.0 and was the source of OQ-G1.',
            'In v1.1, BA-G1 is no longer a premise of any theorem. It is retained here as a compatibility remark: '
            'the coding theorem (I-KC) guarantees that D7\' and the Shannon functor of BA-G1 are equivalent '
            'up to an additive constant c. Specifically:',
            'K(x<sub>B</sub>|x<sub>A</sub>) ≈ H(F(B)) &#8722; H(F(A)) + O(c)',
            'for any computable probability measure P consistent with the morphism structure of C. This '
            'means all quantitative results that v1.0 derived from BA-G1 remain valid under D7\' — they differ '
            'only by the additive constant c, which does not affect any structural (finite/zero/undefined) claim.',
            'BA-G1 is not false. It is not retired. It is now a derived compatibility result rather than an assumed '
            'premise. Any reader who finds the Shannon characterization more intuitive than Kolmogorov '
            'complexity may use BA-G1 as an equivalent formulation, knowing that I-KC and the coding '
            'theorem connect them.',
        ]
    ))

    print('[build_zpg] Building Section VIII: Categorical Zero Paradox...')
    # ── VIII. THE CATEGORICAL ZERO PARADOX — FORMAL STATEMENT ─────────────────
    E.append(Paragraph('VIII. The Categorical Zero Paradox — Formal Statement', S['h1']))
    E.append(body('Theorem T7 is the closing theorem of ZP-G. Its statement is unchanged from v1.0. Its '
                  'proof is strengthened: Part IV (informational singularity) now rests on T6 as rebuilt in '
                  'v1.1, which does not depend on BA-G1.'))

    E.append(result_box(
        'Theorem T7 — The Categorical Zero Paradox',
        'Status: Derived — Closing Theorem [Part IV strengthened in v1.1]',
        [
            'Setup: Let C satisfy AX-G1 and AX-G2. Let I be the categorical surprisal from D7\'. '
            'Let I-KC provide the Kolmogorov framework.',
            'Part I — Universal Constituent (T2): &#8704;X ∈ ob(C), ∃! &#953;<sub>X</sub>: 0 → X. '
            'The initial object 0 is the universal categorical source.',
            'Part II — Unreachability (T3): &#8704;X ≠ 0, hom(X, 0) = ∅. No non-initial object reaches 0.',
            'Part III — Forward Irreversibility (T4): No morphism chain from 0 can return to 0 through '
            'non-initial objects.',
            'Part IV — Informational Singularity (T6, rebuilt): I(X → 0) is undefined for all X ≠ 0 '
            '(no such morphism exists, AX-G2). Outward surprisal from 0 accumulates along any morphism '
            'chain (T6-b, T6-c). 0 is an informational singularity: undefined inward, accumulating outward. '
            'This part no longer depends on BA-G1.',
            'Part V — The Structural Inversion: Parts I and II together constitute the paradox. 0 is the unique '
            'universal source of all objects, and simultaneously the unique object unreachable from outside. '
            'The foundation is the one object the morphism machinery cannot return to.',
            'Part VI — Resolution: The paradox is not a logical contradiction. It is a structural inversion. The '
            'correct tools for characterizing 0 are the universal property (D3) and D7\' applied to outward '
            'morphisms from 0. Under these tools, 0 is fully characterized. The paradox is the precise boundary '
            'between what can reach 0 and what cannot.',
            'Status: DERIVED — Closing Theorem. Depends on D3, D5, D7\', AX-G1, AX-G2, I-KC, T2, T3, T4, '
            'T6. BA-G1 is not a dependency. ✓',
        ]
    ))

    print('[build_zpg] Building Section IX: Open Items Register...')
    # ── IX. OPEN ITEMS REGISTER FOR ZP-G v1.2 ────────────────────────────────
    E.append(Paragraph('IX. Open Items Register for ZP-G v1.5', S['h1']))

    oq_rows = [
        ['OQ-G1',
         'Closed — D7\', T6',
         'Native categorical derivation of surprisal without importing Shannon entropy. Closed by replacing D7 '
         'with D7\' (conditional Kolmogorov complexity K(B|A)). BA-G1 demoted from Bridge Axiom to Compatibility '
         'Remark R-BA. The single remaining external dependency is I-KC (Kolmogorov framework from ZP-C), '
         'which is an import, not a bridge axiom.'],
        ['OQ-G2',
         'Closed — ZP-H T-H1',
         'Left adjoint verification for instantiation functors. Resolved in ZP-H v1.0 by direct universal '
         'property verification for each functor.'],
        ['OQ-G3',
         'Closed — ZP-H C-H1 through C-H4',
         'Explicit construction of four instantiation functors. Resolved in ZP-H v1.0.'],
        ['OQ-G4',
         'Closed — ZP-H T-H2',
         'Reconciliation of categorical and ZP-C singularity characterizations. Resolved in ZP-H v1.0. '
         'Undefined domain (ZP-G) and infinite accumulation (ZP-C) shown to be the same obstruction '
         'under the functor F<sub>C</sub>.'],
        ['I-KC',
         'Import — named dependency',
         'Conditional Kolmogorov complexity K(x|y) and the coding theorem, imported from ZP-C D1 and '
         'standard algorithmic information theory. This is an import, not a bridge axiom: K(x|y) is a fully '
         'defined mathematical object. ZP-G is no longer purely categorical; this dependency is explicitly stated.'],
        ['AX-G1',
         'Axiom — intentional',
         'Asymmetry: initial object 0, no terminal object. Foundational structural commitment. Not a gap.'],
        ['AX-G2',
         'Axiom — intentional',
         'Source asymmetry: hom(X, 0) = ∅ for X ≠ 0. Foundational irreversibility commitment. Not a gap.'],
        ['R-BA',
         'Remark — BA-G1 demoted',
         'Leinster Shannon entropy characterization is now a compatibility remark, not a bridge axiom premise. '
         'Derivable from D7\' and I-KC via the coding theorem. Not a gap.'],
    ]
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.10, TW*0.18, TW*0.72]
    ))

    print('[build_zpg] Building Section X: Validation Status...')
    # ── X. VALIDATION STATUS ──────────────────────────────────────────────────
    E.append(Paragraph('X. Validation Status', S['h1']))

    val_rows = [
        ['D1: Category',
         'Valid — Definition. Standard; foundational. Unchanged.'],
        ['D2: Uniqueness notation',
         'Valid — Definition. Unchanged.'],
        ['D3: Initial object',
         'Valid — Definition. Load-bearing for T2, T7. Unchanged.'],
        ['D4: Terminal object',
         'Valid — Definition. Defined for exclusion. AX-G1 prohibits it. Unchanged.'],
        ['D5: Morphism chain',
         'Valid — Definition. Native to C. Unchanged.'],
        ['D6: Functor',
         'Valid — Definition. Standard. Unchanged.'],
        ['D7\': Native categorical surprisal',
         'Valid — Definition [new in v1.1]. K(x<sub>B</sub>|x<sub>A</sub>) via I-KC. Replaces D7. '
         'Well-defined up to additive constant c. Structurally invariant.'],
        ['I-KC: Kolmogorov import',
         'Import — named [new in v1.1]. K(x|y) and coding theorem from ZP-C. '
         'Not a bridge axiom. Introduces explicit ZP-C dependency into ZP-G.'],
        ['AX-G1: Asymmetry Axiom',
         'Axiom — intentional. Unchanged.'],
        ['AX-G2: Source Asymmetry',
         'Axiom — intentional. Unchanged.'],
        ['R-BA: BA-G1 compatibility remark',
         'Remark — [BA-G1 demoted from Bridge Axiom in v1.0]. Shannon entropy functor '
         'compatible with D7\' up to O(c) by coding theorem. No longer a premise of any theorem.'],
        ['Proposition T1: Uniqueness of initial object',
         'Valid — Derived. Relabelled Proposition in v1.2 (subsidiary uniqueness result). Unchanged. ✓'],
        ['Lemma T2: Universal constituent',
         'Valid — Derived. Relabelled Lemma in v1.2 (stepping-stone result). Unchanged. ✓'],
        ['Lemma T3: Unreachability of 0',
         'Valid — Derived. Relabelled Lemma in v1.2 (stepping-stone result). Unchanged. ✓'],
        ['R1: Structural inversion',
         'Valid — Remark. Unchanged.'],
        ['R2: Categorical expression of self-containment',
         'Valid — Remark [new in v1.3]. Connects T2 + AX-G2 to ZP-A CC-2 (⊥ = {⊥}). '
         'No new derivation; explanatory bridge note.'],
        ['Proposition T4: Chains are forward-only',
         'Valid — Derived. Relabelled Proposition in v1.2. Unchanged. ✓'],
        ['Proposition T5: Functors preserve initial objects',
         'Valid — Conditional on ZP-H T-H1 (closed). Relabelled Proposition in v1.2. Unchanged. ✓'],
        ['Lemma T6-a: Identity surprisal is zero',
         'Valid — Derived [new in v1.1]. Relabelled Lemma in v1.2. K(x<sub>A</sub>|x<sub>A</sub>) = 0 up to c. ✓'],
        ['Lemma T6-b: Non-negative outward surprisal',
         'Valid (PDF-level) — Derived from D5, D7\', AX-G2. K &#8805; 0; strict inequality for distinct objects. '
         'NOT Lean-verified: Lean proof reduces to Nat.zero_le _ (trivially true for any &#8469;-valued function; '
         'verifies nothing about K).'],
        ['Proposition T6-c: Surprisal accumulates along chains',
         'Valid (PDF-level) — Derived from D5, T6-b, subadditivity of K. '
         'NOT Lean-verified: Lean proof reduces to Nat.zero_le _. '
         'Subadditivity of K is a standard AIT result but requires K-formalization absent from Mathlib.'],
        ['Theorem T6: Informational singularity',
         'Valid — Derived [rebuilt in v1.1]. Does not depend on BA-G1. '
         'Part II: undefined domain (AX-G2) — fully Lean-verified. '
         'Parts I, III: accumulation via T6-b, T6-c — PDF-level only (T6-b/T6-c not Lean-verified).'],
        ['Theorem T7: Categorical Zero Paradox',
         'Valid — Derived [Part IV strengthened in v1.1]. All six parts derived. BA-G1 not a dependency. ✓'],
        ['OQ-G1: Native surprisal derivation',
         'Closed — D7\', T6. No bridge axiom remains as a theorem premise.'],
    ]
    E.append(data_table(
        ['Component', 'Status / Notes'],
        val_rows,
        [TW*0.38, TW*0.62]
    ))

    E += [
        sp(12),
        Paragraph(
            '<i>Zero Paradox ZP-G: Category Theory | Version 1.6 | May 2026 | '
            'Supersedes v1.4 | T6-b and T6-c: PDF-level only; Lean proofs verify non-negativity by type only (Nat.zero_le _), '
            'not K-theoretic content | T6 Part II: Lean-verified | Internal Working Document</i>',
            S['endnote']),
    ]

    print(f'[build_zpg] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zpg] Written: {out_path}')


if __name__ == '__main__':
    repo_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    out = os.path.abspath(os.path.join(repo_root, 'ZP-G_Category_Theory_v1_6.pdf'))
    build_zpg(out)
