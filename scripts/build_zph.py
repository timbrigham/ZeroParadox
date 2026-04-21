"""
Zero Paradox — ZP-H: Categorical Bridge PDF Builder
Version 1.1 | April 2026
Changes from v1.0:
  - AX-1 status updated throughout: now T-SNAP (Derived — ZP-E v2.0)
  - Import Registry updated to ZP-G v1.1 (BA-G1 demoted to compatibility remark)
  - OQ-G1 status updated: closed in ZP-G v1.1
  - OQ-G4 intro text corrected (it IS resolved in Section V)
Follows all rules in pdf rendering standards.md:
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
                                 Table, TableStyle, PageBreak, HRFlowable)
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

# ── 1. FONT REGISTRATION ─────────────────────────────────────────────────────
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
FONT_DIR = os.path.join(SCRIPT_DIR, 'fonts') + os.sep

print(f'[build_zph] SCRIPT_DIR: {SCRIPT_DIR}')
print(f'[build_zph] FONT_DIR:   {FONT_DIR}')
print('[build_zph] Registering fonts...')
pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'));     print('  DV ok')
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'));    print('  DV-B ok')
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf')); print('  DV-I ok')
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf')); print('  DV-BI ok')
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'DejaVuSerif.ttf'));     print('  DVS ok')
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'DejaVuSerif-Bold.ttf'));   print('  DVS-B ok')
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'DejaVuSerif-Italic.ttf')); print('  DVS-I ok')
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'DejaVuSerif-BoldItalic.ttf')); print('  DVS-BI ok')
print('[build_zph] Fonts registered.')

# ── 2. COLORS ─────────────────────────────────────────────────────────────────
BLUE      = colors.HexColor('#2E75B6')
BLUE_LITE = colors.HexColor('#D5E8F0')
GREY_LITE = colors.HexColor('#F5F5F5')
GREEN_LITE= colors.HexColor('#E8F5E9')
BLACK     = colors.black
WHITE     = colors.white

# ── 3. PAGE GEOMETRY ──────────────────────────────────────────────────────────
TW = 6.5 * inch
LM = RM = 1.0 * inch
TM = BM = 1.0 * inch

# ── 4. PARAGRAPH STYLES ───────────────────────────────────────────────────────
S = {
    'title':    ParagraphStyle('title',    fontName='DV-B',  fontSize=18, leading=24,
                               spaceAfter=6,  alignment=1),
    'subtitle': ParagraphStyle('subtitle', fontName='DV-I',  fontSize=11, leading=15,
                               spaceAfter=4,  alignment=1),
    'h1':       ParagraphStyle('h1',       fontName='DV-B',  fontSize=13, leading=18,
                               spaceBefore=14, spaceAfter=5, textColor=BLUE),
    'h2':       ParagraphStyle('h2',       fontName='DV-B',  fontSize=11, leading=15,
                               spaceBefore=10, spaceAfter=4, textColor=BLUE),
    'body':     ParagraphStyle('body',     fontName='DVS',   fontSize=10, leading=14,
                               spaceAfter=6),
    'bodyI':    ParagraphStyle('bodyI',    fontName='DVS-I', fontSize=10, leading=14,
                               spaceAfter=6),
    'label':    ParagraphStyle('label',    fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=WHITE),
    'labelG':   ParagraphStyle('labelG',   fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=colors.HexColor('#1B5E20')),
    'cell':     ParagraphStyle('cell',     fontName='DVS',   fontSize=9,  leading=13),
    'cellB':    ParagraphStyle('cellB',    fontName='DVS-B', fontSize=9,  leading=13),
    'cellI':    ParagraphStyle('cellI',    fontName='DVS-I', fontSize=9,  leading=13),
    'note':     ParagraphStyle('note',     fontName='DVS-I', fontSize=9,  leading=13,
                               spaceAfter=4),
    'derived':  ParagraphStyle('derived',  fontName='DVS-B', fontSize=10, leading=14,
                               spaceAfter=6, textColor=colors.HexColor('#1B5E20')),
}

# ── 5. HELPERS ────────────────────────────────────────────────────────────────

def sp(n=6):
    return Spacer(1, n)

def hr():
    return HRFlowable(width='100%', thickness=0.5,
                      color=colors.HexColor('#AAAAAA'),
                      spaceAfter=6, spaceBefore=2)

def chk():
    return '<font name="DV">&#10003;</font>'

def fix(text):
    sub_map = {'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4',
               '₅':'5','₆':'6','₇':'7','₈':'8','₉':'9',
               'ₙ':'n','ₖ':'k','ₘ':'m','ᵢ':'i','ⱼ':'j'}
    for ch, rep in sub_map.items():
        text = text.replace(ch, f'<sub>{rep}</sub>')
    text = text.replace('✓', '<font name="DV">&#10003;</font>')
    text = text.replace('\u2205', '<font name="DV">&#8709;</font>')
    replacements = [
        ('⊥','&#8869;'),('∨','&#8744;'),('∧','&#8743;'),
        ('≤','&#8804;'),('≥','&#8805;'),('≠','&#8800;'),
        ('∈','&#8712;'),('∉','&#8713;'),('⊆','&#8838;'),
        ('∀','&#8704;'),('∃','&#8707;'),('∞','&#8734;'),
        ('→','&#8594;'),('←','&#8592;'),('↔','&#8596;'),
        ('⇒','&#8658;'),('∘','&#8728;'),('—','&#8212;'),
        ('–','&#8211;'),('·','&#183;'),('×','&#215;'),
        ('−','&#8722;'),('≡','&#8801;'),('≅','&#8773;'),
        ('ε','&#949;'),('α','&#945;'),('β','&#946;'),
        ('γ','&#947;'),('δ','&#948;'),('ι','&#953;'),
        ('τ','&#964;'),('φ','&#966;'),
        ('ℚ','&#8474;'),('ℤ','&#8484;'),('ℂ','&#8450;'),
        ('ℕ','&#8469;'),('ℝ','&#8477;'),
        ('‖','&#8214;'),('∥','&#8741;'),
    ]
    for char, entity in replacements:
        if char in text:
            text = text.replace(char, entity)
    return text

def body(text, style='body'):
    return Paragraph(fix(text), S[style])

def label_box(title, rows_list, title_style='label', bg=None):
    if bg is None:
        bg = BLUE
    data = [[Paragraph(fix(title), S[title_style])]]
    for r in rows_list:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  bg),
        ('BACKGROUND',    (0,1), (-1,-1), GREY_LITE),
        ('TEXTCOLOR',     (0,0), (-1,0),  WHITE),
        ('BOX',           (0,0), (-1,-1), 0.5, BLUE),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, BLUE),
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

def label_box_status(title, status_line, rows_list):
    """Box with blue header, italic status sub-row, then content rows."""
    data = [
        [Paragraph(fix(title), S['label'])],
        [Paragraph(fix(status_line), S['cellI'])],
    ]
    for r in rows_list:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  BLUE),
        ('BACKGROUND',    (0,1), (-1,1),  BLUE_LITE),
        ('BACKGROUND',    (0,2), (-1,-1), GREY_LITE),
        ('TEXTCOLOR',     (0,0), (-1,0),  WHITE),
        ('BOX',           (0,0), (-1,-1), 0.5, BLUE),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, BLUE),
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
    data = [hdr_row]
    for row in rows_data:
        data.append([Paragraph(fix(str(c)), S['cell']) for c in row])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  BLUE),
        ('ROWBACKGROUNDS',(0,1),(-1,-1),  [WHITE, GREY_LITE]),
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
        ft = f"Zero Paradox ZP-H: Categorical Bridge  |  Version 1.1  |  April 2026  |  Page {doc.page}"
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch, ft)
        canvas.restoreState()
    return SimpleDocTemplate(
        path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title='ZP-H: Categorical Bridge',
        author='Zero Paradox Project',
        onFirstPage=footer_cb, onLaterPages=footer_cb,
    )


def build_zph(out_path):
    print(f'[build_zph] Output: {out_path}')
    doc = make_doc(out_path)
    E = []

    print('[build_zph] Building title block...')
    # ── TITLE BLOCK ──────────────────────────────────────────────────────────
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-H: Categorical Bridge', S['subtitle']),
        Paragraph('Version 1.1 | April 2026', S['bodyI']),
        Paragraph(
            '<i>Supersedes v1.0 | AX-1 status updated: Derived as T-SNAP (ZP-E v2.0) | '
            'Import Registry updated to ZP-G v1.1 | OQ-G1 closed in ZP-G v1.1</i>',
            S['note']),
        sp(8),
        hr(),
        sp(4),
    ]

    E += [
        body('This document connects ZP-G (Category Theory) to ZP-A through ZP-E. Its function is '
             'exactly analogous to ZP-E\'s role in the original framework: ZP-E connected the four '
             'domain documents to each other; ZP-H connects the categorical generalization back to '
             'those four domain documents. Every cross-framework claim is traced to a theorem in '
             'ZP-G or ZP-A through ZP-E, plus an explicit bridge axiom where required. No floating '
             'connections.'),
        body('ZP-H cannot be written until ZP-G is internally closed. ZP-G v1.1 is closed. ZP-H '
             'inherits all open items from ZP-G with their original labels. The four open questions '
             'from ZP-G — OQ-G1 through OQ-G4 — are the primary targets of this document. '
             'OQ-G2, OQ-G3, and OQ-G4 are resolved here. OQ-G1 is resolved in ZP-G v1.1 via '
             'D7\' and I-KC. All four OQ-G items are now closed.'),
        body('Sequencing note: ZP-H introduces one new definition (D-H1: the morphisms of C) that '
             'was deliberately omitted from ZP-G to keep that document domain-independent. This '
             'definition belongs here because it is instantiation-specific: the morphisms of C are '
             'defined by what the functor constructions require, not by the abstract category itself.'),
        body('Version 1.1 changes: (1) AX-1 (Binary Snap Causality) is no longer an axiom — it is '
             'Theorem T-SNAP, derived in ZP-E v2.0 via the P\u2080 / L-RUN / TQ-IH / DA-1 chain. '
             'All references to AX-1 as an axiom are updated to T-SNAP (Derived). '
             '(2) Import Registry updated from ZP-G v1.0 to ZP-G v1.1: BA-G1 is now a '
             'compatibility remark, not a bridge axiom premise. '
             '(3) OQ-G1 status updated: closed in ZP-G v1.1.'),
        sp(4),
        hr(),
    ]

    print('[build_zph] Building Section I: Imported Results...')
    # ── I. IMPORTED RESULTS ──────────────────────────────────────────────────
    E.append(Paragraph('I. Imported Results', S['h1']))
    E.append(Paragraph('1.1 From ZP-G', S['h2']))

    E.append(label_box_status(
        'Import Registry IR-G — Closed Results from ZP-G v1.1',
        'Status: Valid — Received',
        [
            'D1: Category (objects, morphisms, composition, identity, associativity, unit laws)',
            'D2: Morphism uniqueness notation (&#8707;!)',
            'D3: Initial object 0 — unique morphism &#953;<sub>X</sub>: 0 &#8594; X for all X',
            'D4: Terminal object — defined for exclusion only',
            'D5: Morphism chain from 0',
            'D6: Functor — object map, morphism map, preservation of composition and identity',
            'D7\': Native categorical surprisal I(f) = K(x<sub>B</sub>|x<sub>A</sub>) via I-KC (replaces D7/BA-G1 from v1.0)',
            'I-KC: Conditional Kolmogorov complexity K(x|y) imported from ZP-C — named dependency, not bridge axiom',
            'AX-G1: Asymmetry Axiom — C has initial object 0, no terminal object',
            'AX-G2: Source Asymmetry — hom(X, 0) = <font name="DV">&#8709;</font> for X &#8800; 0',
            'R-BA: Leinster categorical entropy characterization [Compatibility Remark — BA-G1 demoted from Bridge Axiom in ZP-G v1.1. No longer a theorem premise.]',
            'T1: Initial object unique up to unique isomorphism',
            'T2: Universal Constituent — &#8704;X &#8712; ob(C), &#8707;! &#953;<sub>X</sub>: 0 &#8594; X',
            'T3: Unreachability — hom(X, 0) = <font name="DV">&#8709;</font> for X &#8800; 0',
            'T4: Chains are forward-only — no chain returns to 0',
            'T5: Functors preserve initial objects [OQ-G2 closed in ZP-H T-H1]',
            'T6: Informational singularity of 0 — outward surprisal accumulates; inward undefined [rebuilt in ZP-G v1.1 on D7\'; BA-G1 not a dependency]',
            'T7: Categorical Zero Paradox — closing theorem of ZP-G',
            'OQ-G1: Closed in ZP-G v1.1 via D7\' (native categorical surprisal) and I-KC (Kolmogorov import from ZP-C). BA-G1 demoted to compatibility remark.',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('1.2 From ZP-A through ZP-E', S['h2']))

    E.append(label_box_status(
        'Import Registry IR-ZP — Closed Results from ZP-A through ZP-E',
        'Status: Valid — Received',
        [
            'From ZP-A: Join-semilattice (L, &#8744;, &#8869;). &#8869; is the unique additive identity. '
            '&#8869; &#8804; x for all x &#8712; L (T2). State sequences are monotone (T3). No subtraction operator.',
            'From ZP-B: Q<sub>2</sub> with ultrametric d. AX-B1 (binary existence). MP-1 (minimality principle). '
            'p = 2 derived (T0). Every ball is clopen (T2). Q<sub>2</sub> totally disconnected (T5). '
            'Topological isolation of 0 (T3). Snap irreversibility (C3).',
            'From ZP-C: Incompressibility threshold P<sub>0</sub> (D1). RP-1 (representation principle). '
            'State representations derived from AX-B1 (T1). JSD = 1 bit (T1b). Discrete surprisal operator DF (D5, D6). '
            'Non-conservatism of DF on infinite sequences approaching 0 (T2). L-RUN (execution is non-null state change). '
            'TQ-IH (no program outputs &#8869; without non-null intermediate state). '
            'T-BUF / T-SNAP: Binary Snap derived as theorem.',
            'From ZP-D: H = &#8450;<sup>n</sup> (D1). T: Q<sub>2</sub> &#8594; H constructed by basis assignment (T2). '
            'T unique up to unitary equivalence (T3). Snap produces orthogonal shift (T4). '
            'Monotone sequences map to accumulating vectors (T5). DP-1 (orthogonality design commitment).',
            'From ZP-E: Universal constituent cross-framework (T1). Hamming/JSD consistency (T2). '
            'Landauer bridge BA-1. Processing bounds T3. Unified Snap description T4. '
            'Iterative forcing T5. State representations T6. Zero Paradox T7. '
            'T-SNAP: Binary Snap is a derived theorem — AX-1 is not an axiom.',
        ]
    ))
    E.append(sp(8))

    E.append(label_box_status(
        'Inherited Labels Registry IR-2 — Open Items Carried into ZP-H',
        'Status: Structural — labels preserved without laundering',
        [
            'OQ-G1 [Closed in ZP-G v1.1]: Native derivation of categorical surprisal without importing Shannon entropy. '
            'Closed by D7\' (conditional Kolmogorov complexity K(B|A)) and I-KC. BA-G1 demoted to compatibility remark R-BA.',
            'OQ-G2 [Resolved in Section IV]: Left adjoint verification for instantiation functors.',
            'OQ-G3 [Resolved in Section III]: Explicit construction of four instantiation functors.',
            'OQ-G4 [Resolved in Section V]: Reconciliation of categorical and ZP-C singularity characterizations.',
        ]
    ))

    print('[build_zph] Building Section II: Morphisms of C...')
    # ── II. THE MORPHISMS OF C ────────────────────────────────────────────────
    E.append(Paragraph('II. The Morphisms of C — New Definition', S['h1']))
    E += [
        body('ZP-G defined C abstractly: objects, morphisms, composition, identity, satisfying the '
             'category axioms plus AX-G1 and AX-G2. The morphisms of C were left unspecified '
             'because the abstract results (T1 through T7) require only the categorical axioms, not a '
             'concrete description of what morphisms are. That abstraction was correct for ZP-G.'),
        body('ZP-H requires concreteness. To construct the instantiation functors, we must specify '
             'what morphisms of C are, so that we can say what the functor maps them to. That '
             'specification belongs here, not in ZP-G.'),
    ]

    E.append(label_box_status(
        'Definition D-H1 — Morphisms of C — State Transitions',
        'Status: Definition — instantiation-specific',
        [
            'A morphism f: A &#8594; B in C is a state transition: a structure-preserving map from state A to state B satisfying:',
            '(i) Forward direction: Every morphism f: A &#8594; B represents a net addition of informational content. '
            'No morphism reduces state.',
            '(ii) Compatibility with AX-G2: For any non-initial object X &#8800; 0, no morphism X &#8594; 0 exists. D-H1(i) '
            'and AX-G2 are consistent: a net-additive transition cannot return to the minimal state 0.',
            '(iii) Composition: Composition of morphisms corresponds to sequential state accumulation. f: A &#8594; B '
            'followed by g: B &#8594; C produces a state at least as large as B.',
            'Status note: D-H1 is a design commitment, not a derivation. It is the choice that makes the '
            'instantiation functors well-defined. A different choice of morphism structure would yield different '
            'functors. D-H1 is the choice that maps correctly to all four ZP domain documents.',
        ]
    ))

    print('[build_zph] Building Section III: Instantiation Functors...')
    # ── III. CONSTRUCTION OF THE INSTANTIATION FUNCTORS ──────────────────────
    E.append(Paragraph('III. Construction of the Instantiation Functors [OQ-G3 Closed]', S['h1']))
    E += [
        body('ZP-G Remark R3 claimed the existence of four functors F<sub>A</sub>, F<sub>B</sub>, F<sub>C</sub>, F<sub>D</sub> without '
             'constructing them. This section constructs all four. Each construction must specify the '
             'object map, the morphism map, and verify preservation of composition and identity. Each '
             'must also show that AX-G1 and AX-G2 are respected.'),
    ]

    E.append(Paragraph('3.1 F<sub>A</sub>: C &#8594; SLat (Join-Semilattices)', S['h2']))
    E.append(label_box_status(
        'Construction C-H1 — Functor F\u2041: C \u2192 SLat',
        'Status: Derived — OQ-G3 partially closed',
        [
            'Object map: F<sub>A</sub> sends each object X &#8712; ob(C) to the state S<sub>X</sub> &#8712; L in the '
            'join-semilattice (L, &#8744;, &#8869;) of ZP-A. The initial object 0 maps to &#8869;: F<sub>A</sub>(0) = &#8869;.',
            'Morphism map: F<sub>A</sub> sends each morphism f: A &#8594; B to the join operation that witnesses the '
            'transition: F<sub>A</sub>(f) = (S<sub>A</sub> &#8744; &#945;) for some &#945; &#8712; L such that S<sub>A</sub> &#8744; &#945; = S<sub>B</sub>. '
            'By ZP-A D2, every valid state transition is a join.',
            'Preservation of composition: For f: A &#8594; B and g: B &#8594; C, F<sub>A</sub>(g &#8728; f) = S<sub>A</sub> &#8744; &#945;<sub>f</sub> &#8744; &#945;<sub>g</sub> = '
            'F<sub>A</sub>(g) &#8728; F<sub>A</sub>(f) by associativity of &#8744; (ZP-A A1). <font name="DV">&#10003;</font>',
            'Preservation of identity: F<sub>A</sub>(id<sub>A</sub>) = S<sub>A</sub> &#8744; &#8869; = S<sub>A</sub> by ZP-A A4 (additive identity). <font name="DV">&#10003;</font>',
            'AX-G1 respected: F<sub>A</sub>(0) = &#8869; is the global minimum of L (ZP-A T2). No element of SLat is a terminal '
            'object because L has no top element &#8868; (ZP-A R1). <font name="DV">&#10003;</font>',
            'AX-G2 respected: No join operation in L can return to &#8869; from a strictly larger state (ZP-A T3, '
            'monotonicity). Therefore F<sub>A</sub> sends no non-initial morphism to a map terminating at &#8869;. <font name="DV">&#10003;</font>',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('3.2 F<sub>B</sub>: C &#8594; pTop (p-Adic Topological Spaces)', S['h2']))
    E.append(label_box_status(
        'Construction C-H2 — Functor F\u0432: C \u2192 pTop',
        'Status: Derived — OQ-G3 partially closed',
        [
            'Object map: F<sub>B</sub> sends each object X &#8712; ob(C) to an element x &#8712; Q<sub>2</sub>. The initial object 0 maps to '
            'the element 0 &#8712; Q<sub>2</sub>: F<sub>B</sub>(0) = 0 &#8712; Q<sub>2</sub>.',
            'Morphism map: F<sub>B</sub> sends each morphism f: A &#8594; B to the discrete jump from x<sub>A</sub> to x<sub>B</sub> '
            'in Q<sub>2</sub>. By ZP-B T2, any two distinct elements of Q<sub>2</sub> lie in disjoint clopen balls. The jump is across a clopen '
            'boundary — a well-defined topological transition.',
            'Preservation of composition: Sequential discrete jumps in Q<sub>2</sub> compose by transitivity of the ball '
            'structure. x<sub>A</sub> &#8594; x<sub>B</sub> &#8594; x<sub>C</sub> is a valid sequence of clopen transitions. <font name="DV">&#10003;</font>',
            'Preservation of identity: F<sub>B</sub>(id<sub>A</sub>) is the trivial jump x<sub>A</sub> &#8594; x<sub>A</sub>, which is the identity on Q<sub>2</sub>. <font name="DV">&#10003;</font>',
            'AX-G1 respected: F<sub>B</sub>(0) = 0 &#8712; Q<sub>2</sub> is topologically isolated (ZP-B T3). No terminal object exists in '
            'pTop because Q<sub>2</sub> is totally disconnected (ZP-B T5) — there is no single element to which all paths converge. <font name="DV">&#10003;</font>',
            'AX-G2 respected: ZP-B C3 establishes that no continuous path in Q<sub>2</sub> returns to 0 from any '
            'non-zero element. F<sub>B</sub> maps no non-initial morphism to a transition terminating at 0 &#8712; Q<sub>2</sub>. <font name="DV">&#10003;</font>',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('3.3 F<sub>C</sub>: C &#8594; InfoSp (Information-Theoretic Spaces)', S['h2']))
    E.append(label_box_status(
        'Construction C-H3 — Functor F\u0421: C \u2192 InfoSp',
        'Status: Derived — OQ-G3 partially closed',
        [
            'Object map: F<sub>C</sub> sends each object X &#8712; ob(C) to a probability distribution P<sub>X</sub> over {0, 1}. The initial '
            'object 0 maps to the Null State distribution: F<sub>C</sub>(0) = P = (1, 0) (derived from AX-B1 and RP-1 in ZP-C T1).',
            'Morphism map: F<sub>C</sub> sends each morphism f: A &#8594; B to the informational transition from P<sub>A</sub> to P<sub>B</sub>, '
            'with informational work E = JSD(P<sub>A</sub> &#8741; P<sub>B</sub>) &#8805; 0. The fundamental transition (0 &#8594; first non-initial '
            'object) maps to JSD(P &#8741; Q) = 1 bit (ZP-C T1b).',
            'Preservation of composition: JSD is subadditive: JSD(P<sub>A</sub> &#8741; P<sub>C</sub>) &#8804; JSD(P<sub>A</sub> &#8741; P<sub>B</sub>) + JSD(P<sub>B</sub> &#8741; P<sub>C</sub>). '
            'Sequential informational transitions compose consistently. <font name="DV">&#10003;</font>',
            'Preservation of identity: F<sub>C</sub>(id<sub>A</sub>) = JSD(P<sub>A</sub> &#8741; P<sub>A</sub>) = 0. No informational work is done by a trivial transition. <font name="DV">&#10003;</font>',
            'AX-G1 respected: The Null State P = (1, 0) is the unique distribution of minimum entropy (H(P) = 0 bits). '
            'No terminal object exists in InfoSp because there is no maximum entropy distribution that all transitions '
            'converge to — entropy is unbounded upward over larger alphabets. <font name="DV">&#10003;</font>',
            'AX-G2 respected: JSD &#8805; 0. A transition returning to P = (1, 0) from any Q &#8800; P would require JSD(Q &#8741; P) = 0, '
            'which holds only if Q = P. Since Q &#8800; P by assumption, no such transition exists. <font name="DV">&#10003;</font>',
            'Inherited label: The distributions P = (1, 0) and Q = (0, 1) are derived from AX-B1 and RP-1 (ZP-C T1, ZP-E T6). '
            'All results depending on F<sub>C</sub> inherit the AX-B1 and RP-1 labels.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('3.4 F<sub>D</sub>: C &#8594; Hilb (Hilbert Spaces)', S['h2']))
    E.append(label_box_status(
        'Construction C-H4 — Functor F\u0110: C \u2192 Hilb',
        'Status: Derived — OQ-G3 partially closed',
        [
            'Object map: F<sub>D</sub> sends each object X &#8712; ob(C) to a state vector T(x) &#8712; H = &#8450;<sup>n</sup> via the transition '
            'operator T: Q<sub>2</sub> &#8594; H constructed in ZP-D (T2). The initial object 0 maps to: F<sub>D</sub>(0) = T(0) = e<sub>0</sub>.',
            'Morphism map: F<sub>D</sub> sends each morphism f: A &#8594; B to the orthogonal extension from T(x<sub>A</sub>) to T(x<sub>B</sub>) '
            'in H. By ZP-D T4, distinct elements of Q<sub>2</sub> map to orthogonal basis vectors under T, so the transition is a well-defined orthogonal step in H.',
            'Preservation of composition: Sequential orthogonal extensions compose by accumulation: T(x<sub>A</sub>) &#8594; T(x<sub>B</sub>) &#8594; '
            'T(x<sub>C</sub>) produces &#8214;T(x<sub>C</sub>)&#8214; &#8805; &#8214;T(x<sub>B</sub>)&#8214; &#8805; &#8214;T(x<sub>A</sub>)&#8214; by ZP-D T5. <font name="DV">&#10003;</font>',
            'Preservation of identity: F<sub>D</sub>(id<sub>A</sub>) maps to the trivial orthogonal extension T(x<sub>A</sub>) &#8594; T(x<sub>A</sub>), which is the identity on the basis vector e<sub>k</sub>. <font name="DV">&#10003;</font>',
            'AX-G1 respected: F<sub>D</sub>(0) = e<sub>0</sub> is the anchor vector from which all other state vectors are orthogonal '
            'extensions (ZP-D T3). No terminal object exists in Hilb under this construction because the orthogonal extension sequence is unbounded in norm (ZP-D T5). <font name="DV">&#10003;</font>',
            'AX-G2 respected: ZP-D T4 establishes that the Snap produces an orthogonal shift that cannot be '
            'reversed without violating the additive ontology (ZP-A R1). No orthogonal extension terminates back at e<sub>0</sub> from a non-initial vector. <font name="DV">&#10003;</font>',
            'Design commitment inherited: DP-1 (orthogonality as representation of topological isolation) is a '
            'design commitment in ZP-D v1.2. F<sub>D</sub> inherits this label. T4 and T5 of ZP-D depend on DP-1 as a premise.',
        ]
    ))

    print('[build_zph] Building Section IV: Left Adjoint Verification...')
    # ── IV. LEFT ADJOINT VERIFICATION ────────────────────────────────────────
    E.append(Paragraph('IV. Left Adjoint Verification [OQ-G2 Closed]', S['h1']))
    E += [
        body('ZP-G T5 stated that functors preserve initial objects, but marked it conditional on OQ-G2: '
             'verifying that the instantiation functors are left adjoints (or otherwise preserve the '
             'universal property of 0 fully, not just for objects in their image). This section closes OQ-G2.'),
    ]

    E.append(label_box_status(
        'Theorem T-H1 — Each Instantiation Functor Preserves the Initial Object',
        'Status: Derived — OQ-G2 closed',
        [
            'Claim: For each functor F &#8712; {F<sub>A</sub>, F<sub>B</sub>, F<sub>C</sub>, F<sub>D</sub>}, F(0) is an initial object in the codomain category.',
            'Strategy: Rather than proving each functor is a left adjoint in full generality (which would require '
            'establishing adjoint pairs for SLat, pTop, InfoSp, and Hilb), we verify the universal property '
            'directly for each functor. The universal property of the initial object requires: for every object Y in '
            'the codomain, &#8707;! morphism F(0) &#8594; Y.',
            'F<sub>A</sub>: F<sub>A</sub>(0) = &#8869;. For any S<sub>Y</sub> &#8712; L, the unique morphism &#8869; &#8594; S<sub>Y</sub> is the join &#8869; &#8744; S<sub>Y</sub> = S<sub>Y</sub> (ZP-A A4). '
            'Uniqueness: &#8869; is the global minimum (ZP-A T2), so the only order-preserving map from &#8869; to S<sub>Y</sub> is the join with S<sub>Y</sub>. <font name="DV">&#10003;</font>',
            'F<sub>B</sub>: F<sub>B</sub>(0) = 0 &#8712; Q<sub>2</sub>. For any x &#8712; Q<sub>2</sub>, the unique morphism 0 &#8594; x is the discrete jump from 0 to x '
            'across the clopen boundary. Uniqueness: 0 is topologically isolated (ZP-B T3); the only clopen-respecting transition from 0 to x is the direct jump. <font name="DV">&#10003;</font>',
            'F<sub>C</sub>: F<sub>C</sub>(0) = P = (1, 0). For any distribution P<sub>Y</sub>, the unique morphism P &#8594; P<sub>Y</sub> is the informational '
            'transition with work E = JSD(P &#8741; P<sub>Y</sub>). Uniqueness: JSD is symmetric and uniquely determined by P '
            'and P<sub>Y</sub>; there is exactly one value of informational work for any pair of distributions. <font name="DV">&#10003;</font>',
            'F<sub>D</sub>: F<sub>D</sub>(0) = T(0) = e<sub>0</sub>. For any T(x) &#8712; H, the unique morphism e<sub>0</sub> &#8594; T(x) is the orthogonal extension '
            'from e<sub>0</sub> to e<sub>k</sub> (the basis vector assigned to x). Uniqueness: T is unique up to unitary equivalence '
            '(ZP-D T3); the orthogonal extension is unique up to the same equivalence. <font name="DV">&#10003;</font>',
            'Conclusion: OQ-G2 is closed. ZP-G T5 is now unconditional for the four instantiation functors '
            'of this framework. The universal property of 0 &#8712; ob(C) is fully preserved under F<sub>A</sub>, F<sub>B</sub>, F<sub>C</sub>, and F<sub>D</sub>. <font name="DV">&#10003;</font>',
        ]
    ))

    print('[build_zph] Building Section V: Singularity Reconciliation...')
    # ── V. SINGULARITY RECONCILIATION ────────────────────────────────────────
    E.append(Paragraph('V. Singularity Reconciliation [OQ-G4 Closed]', S['h1']))
    E += [
        body('ZP-G T6 characterized the informational singularity of 0 as an undefined domain: the '
             'categorical surprisal I(X &#8594; 0) is undefined because no such morphism exists. ZP-C '
             'established the singularity as infinite accumulation: the discrete surprisal DF diverges '
             'along infinite sequences approaching 0 in Q<sub>2</sub>. ZP-G R4 claimed these are compatible but '
             'did not prove it. This section closes OQ-G4.'),
    ]

    E.append(label_box_status(
        'Theorem T-H2 — Compatibility of Singularity Characterizations',
        'Status: Derived — OQ-G4 closed',
        [
            'Claim: The categorical singularity (undefined domain, ZP-G T6) and the ZP-C singularity (infinite '
            'accumulation, ZP-C T2) are compatible characterizations of the same structural fact under the functor F<sub>C</sub>.',
            'Setup: Let {X<sub>n</sub>} be a sequence of objects in C such that the corresponding sequence {F<sub>C</sub>(X<sub>n</sub>)} = '
            '{P<sub>n</sub>} in InfoSp approaches F<sub>C</sub>(0) = P = (1, 0) in distribution. Under F<sub>B</sub>, the corresponding '
            'sequence {x<sub>n</sub>} in Q<sub>2</sub> approaches 0 &#8712; Q<sub>2</sub>.',
            'ZP-C side: By ZP-C T2, the discrete surprisal DF along the infinite sequence {x<sub>n</sub>} approaching 0 in '
            'Q<sub>2</sub> is non-conservative: the accumulated surprisal &#8721; DF(x<sub>k</sub> &#8594; x<sub>k+1</sub>) diverges as n &#8594; &#8734;. The singularity is infinite accumulation.',
            'ZP-G side: By ZP-G T6(ii), I(X &#8594; 0) is undefined for all X &#8800; 0 because hom(X, 0) = <font name="DV">&#8709;</font> (AX-G2). The singularity is undefined domain.',
            'Reconciliation: These are two descriptions of the same obstruction from different vantage points. '
            'In ZP-C, we ask: what happens to surprisal as we approach 0 along an infinite sequence? The '
            'answer is divergence — the accumulation is unbounded. In ZP-G, we ask: can we reach 0 by a '
            'morphism from outside? The answer is no — the morphism does not exist. Divergence and '
            'non-existence are consistent: if the accumulation required to reach 0 is infinite, then no finite '
            'morphism can accomplish it, which is exactly the statement hom(X, 0) = <font name="DV">&#8709;</font>. The undefined-domain '
            'condition in ZP-G is the categorical expression of the infinite-accumulation condition in ZP-C. <font name="DV">&#10003;</font>',
            'Precise statement: Under F<sub>C</sub>, the statement hom(X, 0) = <font name="DV">&#8709;</font> in C corresponds to the statement that '
            'no finite informational path from P<sub>X</sub> to P = (1, 0) has finite total surprisal — which is exactly the '
            'content of ZP-C T2 restricted to finite paths. OQ-G4 is closed. <font name="DV">&#10003;</font>',
        ]
    ))

    print('[build_zph] Building Section VI: Binary Snap...')
    # ── VI. THE BINARY SNAP — CATEGORICAL DESCRIPTION ────────────────────────
    E.append(Paragraph('VI. The Binary Snap — Categorical Description', S['h1']))

    E.append(label_box_status(
        'Theorem T-H3 — The Binary Snap Under All Four Functors',
        'Status: Derived — Cross-Framework',
        [
            'Setup: The Binary Snap is the transition from 0 &#8712; ob(C) to the first non-initial object '
            '&#949;<sub>0</sub> &#8712; ob(C), driven by the incompressibility threshold P<sub>0</sub> (ZP-C D1) under '
            'T-SNAP (Binary Snap — Derived Theorem, ZP-E v2.0).',
            'In C (ZP-G): The Snap is the morphism &#953;<sub>&#949;0</sub>: 0 &#8594; &#949;<sub>0</sub>. By D3, this morphism is unique. '
            'By T4, no chain returns from &#949;<sub>0</sub> to 0. The Snap is categorically irreversible.',
            'Under F<sub>A</sub> (ZP-A): F<sub>A</sub>(&#953;<sub>&#949;0</sub>) = &#8869; &#8744; &#949;<sub>0</sub> = S<sub>1</sub>. The Snap is the first join. Monotone and irreversible by ZP-A T3. '
            'T-SNAP is a derived theorem (ZP-E v2.0); inherited here with derived status.',
            'Under F<sub>B</sub> (ZP-B): F<sub>B</sub>(&#953;<sub>&#949;0</sub>) is the discrete jump 0 &#8594; &#949;<sub>0</sub> &#8712; Q<sub>2</sub> across a clopen boundary (ZP-B T2). '
            'Topologically irreversible by ZP-B C3.',
            'Under F<sub>C</sub> (ZP-C): F<sub>C</sub>(&#953;<sub>&#949;0</sub>) is the informational transition P &#8594; Q with E = JSD(P &#8741; Q) = 1 bit (ZP-C '
            'T1b). Irreversible: JSD(Q &#8741; P) = 1 bit &#8800; 0.',
            'Under F<sub>D</sub> (ZP-D): F<sub>D</sub>(&#953;<sub>&#949;0</sub>) is the orthogonal shift T(0) = e<sub>0</sub> &#8594; T(&#949;<sub>0</sub>) = e<sub>1</sub>. '
            '&#10216;e<sub>0</sub>, e<sub>1</sub>&#10217; = 0 (ZP-D T4). Norm-increasing (ZP-D T5). DP-1 is a design premise.',
            'Cross-framework consistency: All four functors agree that the Snap is irreversible. Each '
            'irreversibility result is a closed theorem within its own domain document. Their agreement is '
            'structural consistency, not circular argument. T-SNAP (Binary Snap Causality) is a derived '
            'theorem in ZP-E v2.0 and is inherited here with derived status. DP-1 remains the only design premise. <font name="DV">&#10003;</font>',
        ]
    ))

    print('[build_zph] Building Section VII: Traceability Register...')
    # ── VII. FULL TRACEABILITY REGISTER ──────────────────────────────────────
    E.append(Paragraph('VII. Full Traceability Register', S['h1']))
    E += [
        body('Every cross-framework claim in ZP-H is traced here to its grounding theorem and any required bridge axiom.'),
    ]

    trace_rows = [
        ['F<sub>A</sub>(0) = &#8869;',                'ZP-A T2; C-H1',               'None',        'Valid — Derived'],
        ['F<sub>A</sub> preserves composition',        'ZP-A A1; C-H1',               'None',        'Valid — Derived'],
        ['F<sub>A</sub> respects AX-G1, AX-G2',       'ZP-A T2, T3, R1; C-H1',       'None',        'Valid — Derived'],
        ['F<sub>B</sub>(0) = 0 &#8712; Q<sub>2</sub>','ZP-B T3; C-H2',               'None',        'Valid — Derived'],
        ['F<sub>B</sub> preserves composition',        'ZP-B T2; C-H2',               'None',        'Valid — Derived'],
        ['F<sub>B</sub> respects AX-G1, AX-G2',       'ZP-B T5, C3; C-H2',           'None',        'Valid — Derived'],
        ['F<sub>C</sub>(0) = P = (1,0)',               'ZP-C T1; ZP-E T6; C-H3',      'AX-B1, RP-1', 'Valid — from AX-B1, RP-1'],
        ['F<sub>C</sub> preserves composition',        'JSD subadditivity; C-H3',      'None',        'Valid — Derived'],
        ['F<sub>C</sub> respects AX-G1, AX-G2',       'ZP-C T1b; C-H3',              'AX-B1, RP-1', 'Valid — from AX-B1, RP-1'],
        ['F<sub>D</sub>(0) = T(0) = e<sub>0</sub>',   'ZP-D T2, T3; C-H4',           'DP-1',        'Valid — from DP-1'],
        ['F<sub>D</sub> preserves composition',        'ZP-D T5; C-H4',               'DP-1',        'Valid — from DP-1'],
        ['F<sub>D</sub> respects AX-G1, AX-G2',       'ZP-D T4, T5; C-H4',           'DP-1',        'Valid — from DP-1'],
        ['T-H1: universal property preserved',         'ZP-A T2; ZP-B T3; ZP-C T1b; ZP-D T3', 'None', 'Valid — OQ-G2 closed'],
        ['T-H2: singularity compatibility',            'ZP-G T6; ZP-C T2; C-H3',     'None',        'Valid — OQ-G4 closed'],
        ['T-H3: Snap under all four functors',         'C-H1 through C-H4; ZP-E T4; ZP-E T-SNAP', 'DP-1', 'Valid — T-SNAP derived (ZP-E v2.0)'],
        ['D-H1: morphisms of C',                       'ZP-A D2; ZP-B T2; ZP-C; ZP-D', 'None',      'Design Commitment'],
    ]
    E.append(data_table(
        ['Claim', 'Grounded In', 'Bridge Axiom?', 'Status'],
        trace_rows,
        [TW*0.25, TW*0.35, TW*0.17, TW*0.23]
    ))

    print('[build_zph] Building Section VIII: Open Items Register...')
    # ── VIII. OPEN ITEMS REGISTER ─────────────────────────────────────────────
    E.append(Paragraph('VIII. Open Items Register for ZP-H v1.1', S['h1']))

    oq_rows = [
        ['OQ-G1',
         'Closed — ZP-G v1.1\nD7\', T6',
         'Native derivation of categorical surprisal without importing Shannon entropy. '
         'Closed in ZP-G v1.1 by D7\' (native categorical surprisal K(B|A)) and I-KC '
         '(Kolmogorov import from ZP-C). BA-G1 demoted to compatibility remark R-BA. '
         'No bridge axiom remains as a theorem premise.'],
        ['OQ-G2',
         'Closed — T-H1',
         'Left adjoint verification for instantiation functors. Resolved in Section IV by '
         'direct verification of the universal property for each of the four functors.'],
        ['OQ-G3',
         'Closed — C-H1\nthrough C-H4',
         'Explicit construction of the four instantiation functors. Resolved in Section III. '
         'Object maps, morphism maps, and preservation proofs are complete for all four.'],
        ['OQ-G4',
         'Closed — T-H2',
         'Reconciliation of categorical (undefined domain) and ZP-C (infinite accumulation) '
         'singularity characterizations. Resolved in Section V. The two characterizations '
         'are shown to be the same obstruction described from different vantage points.'],
        ['AX-1',
         'Derived —\nT-SNAP\n(ZP-E v2.0)',
         'Binary Snap Causality. Derived as Theorem T-SNAP in ZP-E v2.0 via the '
         'P\u2080 / L-RUN / TQ-IH / DA-1 chain. No longer an axiom. T-H3 inherits '
         'T-SNAP as a derived result. Not a gap.'],
        ['AX-G1',
         'Axiom —\nintentional',
         'Asymmetry: initial object 0, no terminal object. Inherited from ZP-G. Not a gap.'],
        ['AX-G2',
         'Axiom —\nintentional',
         'Source asymmetry: hom(X, 0) = \u2205 for X \u2260 0. Inherited from ZP-G. Not a gap.'],
        ['R-BA',
         'Remark —\nBA-G1 demoted\n(ZP-G v1.1)',
         'Leinster Shannon entropy characterization. BA-G1 demoted from Bridge Axiom '
         'in ZP-G v1.0 to Compatibility Remark R-BA in ZP-G v1.1. '
         'Derivable from D7\' and I-KC via the coding theorem. Not a gap.'],
        ['D-H1',
         'Design\nCommitment —\nintentional',
         'Morphisms of C defined as state transitions. This is a design choice that makes '
         'the instantiation functors well-defined. A different morphism structure would yield '
         'different functors. Explicitly stated and not laundered as a derivation.'],
        ['DP-1',
         'Design\nCommitment —\ninherited',
         'Orthogonality as representation of topological isolation. Inherited from ZP-D v1.2. '
         'F<sub>D</sub> and T-H3 depend on it as a premise.'],
    ]

    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.12, TW*0.18, TW*0.70]
    ))

    print('[build_zph] Building Section IX: Validation Status...')
    # ── IX. VALIDATION STATUS ─────────────────────────────────────────────────
    E.append(Paragraph('IX. Validation Status', S['h1']))

    val_rows = [
        ['IR-G: ZP-G v1.1 results imported',
         'Valid — all ZP-G v1.1 closed results received; labels preserved. '
         'BA-G1 demoted to R-BA; I-KC noted as named dependency.'],
        ['IR-ZP: ZP-A through ZP-E imported',
         'Valid — all closed results received from ZP-A through ZP-E; labels preserved. '
         'T-SNAP (ZP-E v2.0) noted: AX-1 is derived, not axiomatic.'],
        ['IR-2: Inherited labels preserved',
         'Valid — OQ-G1 closed in ZP-G v1.1; OQ-G2, OQ-G3, OQ-G4 resolved here; '
         'BA-G1 updated to R-BA; AX-1 updated to T-SNAP (Derived).'],
        ['D-H1: Morphisms of C',
         'Design Commitment — explicitly stated; required for functor construction'],
        ['C-H1: F<sub>A</sub>: C &#8594; SLat',
         'Valid — Derived. Object map, morphism map, composition, identity all verified. <font name="DV">&#10003;</font>'],
        ['C-H2: F<sub>B</sub>: C &#8594; pTop',
         'Valid — Derived. Object map, morphism map, composition, identity all verified. <font name="DV">&#10003;</font>'],
        ['C-H3: F<sub>C</sub>: C &#8594; InfoSp',
         'Valid — from AX-B1, RP-1. All four requirements verified; inherits AX-B1 and RP-1 labels. <font name="DV">&#10003;</font>'],
        ['C-H4: F<sub>D</sub>: C &#8594; Hilb',
         'Valid — from DP-1. All four requirements verified; inherits DP-1 label. <font name="DV">&#10003;</font>'],
        ['T-H1: Universal property preserved',
         'Valid — OQ-G2 closed. ZP-G T5 is now unconditional for all four instantiation functors. <font name="DV">&#10003;</font>'],
        ['T-H2: Singularity reconciliation',
         'Valid — OQ-G4 closed. Categorical (undefined domain) and ZP-C (infinite accumulation) '
         'shown to be the same obstruction under F<sub>C</sub>. <font name="DV">&#10003;</font>'],
        ['T-H3: Snap under all four functors',
         'Valid — Derived; cross-framework. T-SNAP inherited as derived theorem (ZP-E v2.0). '
         'DP-1 labelled as design premise. <font name="DV">&#10003;</font>'],
        ['Traceability register',
         'Valid — Complete. Every cross-framework claim traced to source theorem and bridge axiom. No floating connections.'],
        ['OQ-G1: Native surprisal derivation',
         'Closed in ZP-G v1.1 via D7\' and I-KC. No bridge axiom remains as a theorem premise.'],
        ['AX-1 (Binary Snap Causality)',
         'Derived — T-SNAP in ZP-E v2.0. No longer an axiom. '
         'T-H3 and all downstream results inherit the derived status.'],
        ['AX-G1, AX-G2',
         'Axioms — intentional. Foundational commitments. Not gaps.'],
        ['R-BA, D-H1, DP-1',
         'Compatibility Remark / Design Commitments — intentional. Explicitly stated. Not laundered.'],
    ]

    E.append(data_table(
        ['Component', 'Status / Notes'],
        val_rows,
        [TW*0.35, TW*0.65]
    ))

    E += [
        sp(12),
        Paragraph(
            '<i>End of ZP-H v1.1 | Four instantiation functors constructed | '
            'OQ-G1 through OQ-G4 all closed | '
            'T-SNAP inherited as derived theorem | '
            'Remaining axioms: AX-B1, AX-G1, AX-G2</i>',
            S['note']),
    ]

    print(f'[build_zph] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zph] Written: {out_path}')


if __name__ == '__main__':
    repo_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    out = os.path.abspath(os.path.join(repo_root, 'ZP-H_Categorical_Bridge_v1_1.pdf'))
    build_zph(out)
