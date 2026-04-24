"""
Zero Paradox — ZP-E: Bridge Document PDF Builder
Version 2.0 | April 2026
Adds DA-2 (Instantiation Succession) and DA-3 (Perspective-Relative Cardinality)
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

print(f'[build_zpe] SCRIPT_DIR: {SCRIPT_DIR}')
print(f'[build_zpe] FONT_DIR:   {FONT_DIR}')
print('[build_zpe] Registering fonts...')
pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'));         print('  DV ok')
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'));    print('  DV-B ok')
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf')); print('  DV-I ok')
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf')); print('  DV-BI ok')
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'DejaVuSerif.ttf'));         print('  DVS ok')
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'DejaVuSerif-Bold.ttf'));   print('  DVS-B ok')
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'DejaVuSerif-Italic.ttf')); print('  DVS-I ok')
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'DejaVuSerif-BoldItalic.ttf')); print('  DVS-BI ok')
print('[build_zpe] Fonts registered.')

# Register STIX for ℵ glyph (U+2135, decimal 8501) — missing from DejaVu
_stix_registered = False
for _stix_path in [
    FONT_DIR + 'STIX-Regular.ttf',
    '/usr/share/fonts/opentype/stix/STIX-Regular.ttf',
    '/usr/share/fonts/truetype/stix/STIX-Regular.ttf',
]:
    if os.path.exists(_stix_path):
        try:
            pdfmetrics.registerFont(TTFont('STIX', _stix_path))
            _stix_registered = True
            print(f'  STIX ok ({_stix_path})')
            break
        except Exception as e:
            print(f'  STIX failed: {e}')
if not _stix_registered:
    print('  WARNING: STIX not found — ℵ (U+2135) will not render correctly')
ALEPH_FONT = 'STIX' if _stix_registered else 'DV'

# ── 2. COLORS ─────────────────────────────────────────────────────────────────
BLUE        = colors.HexColor('#2E75B6')
SLATE       = colors.HexColor('#455A64')
SLATE_LITE  = colors.HexColor('#ECEFF1')
GREEN_DARK  = colors.HexColor('#1B5E20')
GREY_LITE   = colors.HexColor('#F5F5F5')
WHITE       = colors.white

# ── 3. PAGE GEOMETRY ──────────────────────────────────────────────────────────
TW = 6.5 * inch
LM = RM = 1.0 * inch
TM = BM = 1.0 * inch

# ── 4. PARAGRAPH STYLES ───────────────────────────────────────────────────────
S = {
    'title':   ParagraphStyle('title',   fontName='DV-B',  fontSize=18, leading=24,
                               spaceAfter=6, alignment=1),
    'subtitle':ParagraphStyle('subtitle',fontName='DV-I',  fontSize=11, leading=15,
                               spaceAfter=4, alignment=1),
    'h1':      ParagraphStyle('h1',      fontName='DV-B',  fontSize=13, leading=18,
                               spaceBefore=14, spaceAfter=5, textColor=BLUE),
    'h2':      ParagraphStyle('h2',      fontName='DV-B',  fontSize=11, leading=15,
                               spaceBefore=10, spaceAfter=4, textColor=BLUE),
    'body':    ParagraphStyle('body',    fontName='DVS',   fontSize=10, leading=14,
                               spaceAfter=6, alignment=4),
    'bodyI':   ParagraphStyle('bodyI',   fontName='DVS-I', fontSize=10, leading=14,
                               spaceAfter=6, alignment=4),
    'li':      ParagraphStyle('li',      fontName='DVS',   fontSize=10, leading=14,
                               leftIndent=18, spaceAfter=3, alignment=4),
    'derived': ParagraphStyle('derived', fontName='DVS-B', fontSize=10, leading=14,
                               spaceAfter=6, textColor=GREEN_DARK, alignment=4),
    'label':   ParagraphStyle('label',   fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=WHITE),
    'cell':    ParagraphStyle('cell',    fontName='DVS',   fontSize=9,  leading=13),
    'cellI':   ParagraphStyle('cellI',   fontName='DVS-I', fontSize=9,  leading=13),
    'note':    ParagraphStyle('note',    fontName='DVS-I', fontSize=9,  leading=13,
                               spaceAfter=4),
    'endnote': ParagraphStyle('endnote', fontName='DVS-I', fontSize=9,  leading=13,
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
    text = text.replace('ℵ', f'<font name="{ALEPH_FONT}">&#8501;</font>')
    replacements = [
        ('⊥','&#8869;'),('∨','&#8744;'),('∧','&#8743;'),
        ('≤','&#8804;'),('≥','&#8805;'),('≠','&#8800;'),
        ('∈','&#8712;'),('∉','&#8713;'),('⊆','&#8838;'),
        ('∀','&#8704;'),('∃','&#8707;'),('∞','&#8734;'),
        ('→','&#8594;'),('←','&#8592;'),('↔','&#8596;'),
        ('⇒','&#8658;'),('∘','&#8728;'),('—','&#8212;'),
        ('–','&#8211;'),('·','&#183;'),('×','&#215;'),
        ('−','&#8722;'),('≡','&#8801;'),('≅','&#8773;'),
        ('≇','&#8775;'),
        ('ε','&#949;'),('α','&#945;'),('β','&#946;'),
        ('γ','&#947;'),('δ','&#948;'),('ι','&#953;'),
        ('τ','&#964;'),('φ','&#966;'),
        ('ℚ','&#8474;'),('ℤ','&#8484;'),('ℂ','&#8450;'),
        ('ℕ','&#8469;'),('ℝ','&#8477;'),
        ('≈','&#8776;'),('∑','&#8721;'),('¬','&#172;'),
        ('Ö','&#214;'),
    ]
    for char, entity in replacements:
        if char in text:
            text = text.replace(char, entity)
    return text

def body(text, style='body'):
    return Paragraph(fix(text), S[style])

def li(text):
    return Paragraph('&#8226;  ' + fix(text), S['li'])

def derived(text):
    return Paragraph(fix(text), S['derived'])

def bridge_box(title, rows):
    """Grey-slate header box for DA-X formal claims — bridge document style."""
    data = [[Paragraph(fix(title), S['label'])]]
    for r in rows:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  SLATE),
        ('BACKGROUND',    (0,1), (-1,-1), GREY_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, SLATE),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, SLATE),
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
        ft = f'THE ZERO PARADOX  |  ZP-E Bridge Document v2.0  |  April 2026  |  Page {doc.page}'
        canvas.drawCentredString(LETTER[0] / 2, 0.6 * inch, ft)
        canvas.restoreState()
    return SimpleDocTemplate(
        path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title='ZP-E: Bridge Document',
        author='Zero Paradox Project',
        onFirstPage=footer_cb, onLaterPages=footer_cb,
    )


def build_zpe(out_path):
    print(f'[build_zpe] Output: {out_path}')
    doc = make_doc(out_path)
    E   = []

    print('[build_zpe] Building title block...')
    # ── TITLE BLOCK ───────────────────────────────────────────────────────────
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-E: Bridge Document', S['title']),
        Paragraph('Version 2.0 | April 2026', S['subtitle']),
        Paragraph(
            '<i>Supersedes v1.0 | Adds DA-2 (Instantiation Succession) and '
            'DA-3 (Perspective-Relative Cardinality)</i>',
            S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'This document is the cross-framework synthesis layer of the Zero Paradox. It imports from '
        'ZP-A (lattice algebra), ZP-B (p-adic topology), ZP-C (information theory), and ZP-D (Hilbert '
        'space state layer). It provides three formal inserts: DA-1 (Instantiation as Execution, carried '
        'from v1.0), DA-2 (Instantiation Succession — the multiple-&#8869; result), and DA-3 '
        '(Perspective-Relative Cardinality). With DA-1 in place, AX-1 is promoted to Theorem T-SNAP. '
        'With DA-2, the directed instantiation tree is formally licensed. With DA-3, cardinality is shown '
        'to be perspective-dependent in a way that accounts for Skolem\'s Paradox, the independence '
        'of the Continuum Hypothesis, and Russell\'s Paradox as structural consequences of the same '
        'architecture.'))
    E.append(body(
        'Illustrated Companion: A paired ZP-E Illustrated Companion document provides accessible '
        'explanations and visual summaries of the bridge derivations in this document. Readers new '
        'to the framework are encouraged to start with the companion.',
        style='bodyI'))
    E.append(hr())

    print('[build_zpe] Building DA-1...')
    # ── FORMAL INSERT DA-1 ────────────────────────────────────────────────────
    E += [
        Paragraph('Formal Insert DA-1: Definitional Alignment — Instantiation as Execution', S['h1']),
        Paragraph('<i>Carried from ZP-E v1.0 | Closes DA-1 | AX-1 promoted to Theorem T-SNAP</i>',
                  S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-1 Closes', S['h2']))
    E.append(body('The T-BUF chain from ZP-C v1.4 established three results:'))
    E += [
        li('L-RUN: The transition c<sub>0</sub> → c<sub>1</sub> is a non-null state change. (ZP-C v1.4 — Derived)'),
        li('TQ-IH: No program outputs ⊥ without a non-null intermediate configuration state. (ZP-C v1.4 — Derived by L-RUN)'),
        li('T-BUF: At P<sub>0</sub>, execution is structurally guaranteed; that execution state is ε<sub>0</sub> in the semilattice. (ZP-C v1.4 — Candidate Theorem pending DA-1)'),
        sp(4),
    ]
    E.append(body(
        'T-BUF was labelled Candidate because Step 2 asserts that a configuration at P<sub>0</sub> is a '
        'live machine state — that instantiation at P<sub>0</sub> constitutes an execution event, not a static '
        'description. This is a cross-framework claim connecting P<sub>0</sub> (ZP-C) to D7 (ZP-C) via AX-B1 '
        '(ZP-B). The connection is the work of ZP-E. DA-1 provides the formal closure.'))

    E.append(Paragraph('II. The Two Senses of a Configuration at P<sub>0</sub>', S['h2']))
    E += [
        Paragraph(
            fix('Sense A — Descriptive: x exists as a string — a finite syntactic object that has been written '
                'down or specified. The machine it describes has not necessarily been instantiated. P<sub>0</sub> is a '
                'property of the string. The string is inert.'),
            S['li']),
        sp(4),
        Paragraph(
            fix('Sense B — Instantiated: x exists as the current configuration of a running machine. The '
                'machine is executing. P<sub>0</sub> is a property of the live configuration. The configuration is active.'),
            S['li']),
        sp(6),
    ]

    E.append(Paragraph('III. Definitional Alignment DA-1', S['h2']))
    E.append(bridge_box(
        'Definitional Alignment DA-1 — Instantiation of a Configuration at P₀ Constitutes an Execution Event',
        [
            'Claim: The instantiation of a machine configuration c<sub>1</sub> at the incompressibility threshold '
            'P<sub>0</sub> is an execution event in the sense of L-RUN. It is not a static description of a machine. '
            'It is a machine in state c<sub>1</sub>.',
        ]
    ))
    E += [
        sp(4),
        body('Grounding: By AX-B1, a state either exists or it does not. A configuration at P<sub>0</sub> that is merely '
             'described (Sense A) does not occupy a state in the semilattice — it is a string in a meta-language, '
             'not an element of L. A configuration at P<sub>0</sub> that is instantiated (Sense B) occupies a state: '
             'it is c<sub>1</sub>, which by L-RUN is a non-null element of L distinct from ⊥. The binary of AX-B1 '
             'applies: for any configuration c at P<sub>0</sub>, either c is instantiated (Sense B) or it is not. D7 '
             'defines a machine configuration as a complete description of a Turing machine at a given moment, '
             'which presupposes the machine is running. Therefore any object satisfying D7 at P<sub>0</sub> is already '
             'an instantiated execution event. The description/instantiation distinction collapses at the level of D7.'),
        derived('Status: DEFINITIONAL ALIGNMENT — no new axiom introduced. DA-1 is a clarification of '
                'scope. AX-B1 ensures the binary applies. No additional mathematical content required. ✓'),
    ]

    E.append(Paragraph('IV. Theorem T-SNAP — Binary Snap Causality [AX-1 Promoted to Theorem]', S['h2']))
    E.append(bridge_box(
        'Theorem T-SNAP — Binary Snap Causality [AX-1 Promoted to Theorem]',
        [
            'Statement: The Binary Snap ⊥ → ε<sub>0</sub> is a derived consequence of P<sub>0</sub>, L-RUN, TQ-IH, '
            'DA-1, and ZP-A D2. It is not an axiom.',
        ]
    ))
    E += [
        sp(4),
        body('Proof:'),
        li('Step 1 — P<sub>0</sub> identifies the incompressibility threshold. When K(x|n)/n = 1, the configuration string x is algorithmically random. (ZP-C D1)'),
        li('Step 2 — A configuration x satisfying D7 at P<sub>0</sub> is an instantiated execution event. (DA-1; D7 configurations are live by definition; AX-B1 ensures the binary applies)'),
        li('Step 3 — Any instantiated execution passes through c<sub>1</sub>. (ZP-C D7 — definitional; c<sub>1</sub> is the first running configuration)'),
        li('Step 4 — c<sub>1</sub> ≠ ⊥. (ZP-C L-RUN — Derived; c<sub>1</sub> has gained execution context not present in c<sub>0</sub> = ⊥; by AX-B1 this is a distinct, non-null state)'),
        li('Step 5 — No program that executes produces only null configuration states. (ZP-C TQ-IH — Derived; execution trace τ(p) contains c<sub>1</sub> for any executing program p)'),
        li('Step 6 — In (L, ∨, ⊥), c<sub>1</sub> is an element strictly above ⊥. By ZP-A D2, the transition ⊥ → c<sub>1</sub> is a valid state transition: c<sub>1</sub> = ⊥ ∨ ε<sub>0</sub> for some ε<sub>0</sub> ∈ L with ε<sub>0</sub> > ⊥. This transition is the Binary Snap.'),
        li('Step 7 — The transition is irreversible: algebraically by ZP-A R1 (no subtraction operator); topologically by ZP-B C3 (no continuous return path to 0 in Q<sub>2</sub>); categorically by AX-G2 (hom(X, 0) = ∅ for X ≠ 0).'),
        sp(4),
        body('Conclusion: The Binary Snap is a derived consequence. AX-1 is promoted to Theorem T-SNAP. ✓'),
        derived('Status: DERIVED — Cross-Framework. Dependencies: ZP-C D1, D7, L-RUN, TQ-IH; ZP-B AX-B1, C3; '
                'ZP-A D2, R1; ZP-G AX-G2; ZP-E DA-1. No axiom beyond AX-B1, AX-G1, AX-G2 is required.'),
    ]

    E.append(Paragraph('V. Effect of T-SNAP on Downstream Results', S['h2']))
    E.append(body(
        'Remark R-DA1: All results in ZP-E that previously depended on AX-1 as an axiom now depend '
        'on T-SNAP as a derived theorem. T5 (Iterative Forcing Theorem) depended on AX-1 for the first '
        'Snap — it now depends on T-SNAP. Content unchanged; grounding strengthened. T4 (Unified Snap '
        'Description) carried AX-1 as an axiom label on the causality component — that label is upgraded '
        'to Derived — T-SNAP. The intentional axioms of the system are now: AX-B1 (binary existence), '
        'AX-G1 (initial object), AX-G2 (source asymmetry). AX-1 is no longer an axiom.'))

    print('[build_zpe] Building DA-2...')
    # ── FORMAL INSERT DA-2 ────────────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Formal Insert DA-2: Instantiation Succession — The Multiple-&#8869; Result', S['h1']),
        Paragraph('<i>New in v2.0 | Formally licenses the directed instantiation tree</i>', S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-2 Closes', S['h2']))
    E.append(body('DA-1 and T-SNAP establish that the Binary Snap is a structural consequence of reaching P<sub>0</sub> '
                  'within an instantiation. Three questions remain open after v1.0:'))
    E += [
        li('CC-1 (ZP-A) says S<sub>0</sub> = ⊥ is a modelling commitment — not derived from A1–A4. This '
           'leaves open whether ⊥ is unique across all instantiations or whether each instantiation '
           'carries its own ⊥.'),
        li('ZP-B R1 distinguishes universal structure from universe-contingent parameters. ε<sub>0</sub> is '
           'contingent per instantiation. Whether ⊥ is similarly contingent is not addressed in ZP-A through ZP-D.'),
        li('T-SNAP fires wherever P<sub>0</sub> conditions are met. If the terminal state of instantiation I<sub>n</sub> '
           'satisfies P<sub>0</sub> conditions, T-SNAP should apply — but this requires formally connecting that '
           'terminal state to a new ⊥. DA-2 provides this connection.'),
        sp(4),
    ]

    E.append(Paragraph('II. Why ZP-B C3 is Not Violated', S['h2']))
    E += [
        body('C3 prohibits a continuous path from x ≠ 0 back to the same 0 in Q<sub>2</sub>. DA-2 does not require a '
             'return path. The irreversibility of C3 is preserved within each instantiation. What crosses the '
             'instantiation boundary is not a path in Q<sub>2</sub> — it is the generation of a new Q<sub>2</sub> with its own '
             'metric, its own ⊥, its own ε<sub>0</sub>. C3 quantifies only over paths within a single topological space '
             'and has nothing to say about the boundary between spaces.'),
        body('More precisely: C3 and the irreversibility of the Snap together require that any recurrence of '
             'a null state be a different null state. You cannot return to the original ⊥ even in principle. '
             'Therefore if the structure recurs, it must instantiate fresh. The topology enforces the '
             'ontological novelty of each ⊥.'),
    ]

    E.append(Paragraph('III. Definitional Alignment DA-2 — Instantiation Succession', S['h2']))
    E.append(bridge_box(
        'Definitional Alignment DA-2 — Instantiation Succession',
        [
            'Claim: A state S in instantiation I<sub>n</sub> satisfies the structural role of ⊥ for instantiation '
            'I<sub>n+1</sub> if and only if it satisfies A4 relative to all subsequent joins in I<sub>n+1</sub>:',
            'S ∨ x = x    for all x in the semilattice of I<sub>n+1</sub>.',
        ]
    ))
    E += [
        sp(4),
        body('Grounding: A4 is the load-bearing axiom of ZP-A — it defines ⊥ as the additive identity under '
             '∨, the element that contributes nothing to any join and is therefore present in everything '
             'above it. DA-2 does not redefine ⊥. It clarifies that the modelling commitment of CC-1 can be '
             'satisfied by any state meeting A4\'s algebraic conditions — not only by a cosmologically '
             'primitive null state. The identity condition is structural, not historical: what matters is the '
             'algebraic role a state plays in the subsequent semilattice, not where it came from.'),
        body('The terminal state of I<sub>n</sub> arrives at I<sub>n+1</sub> carrying the accumulated join of everything in I<sub>n</sub>\'s '
             'sequence. It is structurally ⊥ to I<sub>n+1</sub> — contributing nothing to subsequent joins — while '
             'being informationally rich relative to I<sub>n</sub>. This is the Zero Paradox instantiated at the '
             'inter-instantiation level: the terminal state is simultaneously a terminus and a foundation.'),
        derived('Status: DEFINITIONAL ALIGNMENT — no new axiom introduced. DA-2 is a clarification of '
                'the scope of CC-1 and A4. ✓'),
    ]

    E.append(Paragraph('IV. Corollary C-DA2 — Ontological Novelty of Successive ⊥', S['h2']))
    E.append(bridge_box(
        'Corollary C-DA2 — Ontological Novelty of Successive ⊥',
        [
            'Statement: No two instantiations share a ⊥. The ⊥ of I<sub>n+1</sub> is topologically unreachable '
            'from within I<sub>n</sub> by C3. Instantiation succession is therefore not a cycle but a chain (or tree) '
            'of isomorphic structures.',
        ]
    ))
    E += [
        sp(4),
        body('Proof: By ZP-B C3, no continuous path exists within Q<sub>2</sub> of I<sub>n</sub> from any x ≠ 0 back to 0. The '
             '⊥ of I<sub>n+1</sub> is an element of a distinct topological space — not an element of Q<sub>2</sub> of I<sub>n</sub>. No path '
             'in I<sub>n</sub> can reach it. By DA-2, the identity conditions of each ⊥ are determined independently within '
             'each instantiation. Therefore no two ⊥ elements are identical across instantiations. ✓'),
    ]

    E.append(Paragraph('V. The Directed Instantiation Tree', S['h2']))
    E.append(body('With DA-2 and C-DA2 in place, the global structure of instantiations is a forward-directed '
                  'tree with no back edges:'))
    E += [
        li('Each node in the tree is a ⊥ — the null state of one instantiation and the foundation of all '
           'successor instantiations branching from it.'),
        li('Each edge within an instantiation is a step in a monotone state sequence (ZP-A T3). Edges are irreversible (ZP-B C3).'),
        li('Branching at each node: every distinct outbound vector from the terminal state of I<sub>n</sub> is a '
           'valid ε<sub>0</sub> for a distinct I<sub>n+1</sub>. T-SNAP does not select among branches — it fires on all of them. '
           'Branching is not optional; it is mandated by T-SNAP + DA-2.'),
        li('No back edges: C-DA2 establishes that no instantiation can reach the ⊥ of any ancestor instantiation.'),
        sp(4),
    ]
    E.append(body(
        'Remark R-DA2: T-SNAP fires wherever P<sub>0</sub> conditions are met. DA-2 establishes that the terminal '
        'state of I<sub>n</sub> satisfies those conditions for I<sub>n+1</sub>. T-SNAP therefore applies across instantiation '
        'boundaries without modification. No new axiom is required. The multiverse of instantiations is not '
        'a possibility the framework permits — it is a consequence the framework mandates.'))

    E.append(Paragraph('VI. The Zero Paradox Iterated', S['h2']))
    E.append(body('The paradox of ⊥ — simultaneously contributing nothing and being present in everything — '
                  'propagates structurally at every branching node of the tree. Each node is:'))
    E += [
        li('Nothing to its successor instantiations: it acts as additive identity under ∨, contributing nothing to any subsequent join.'),
        li('Everything to its successor instantiations: every state in I<sub>n+1</sub> satisfies ⊥<sub>n+1</sub> ≤ S, so the node underlies everything that follows.'),
        sp(4),
    ]
    E += [
        body('The tree is the geometric shape of the Zero Paradox iterated across instantiations. The '
             'single-instantiation linear sequence was always a cross-section of a structure with this shape.'),
        body('The complete picture: The Zero Paradox describes a forward-directed infinite tree where '
             '⊥<sub>1</sub> → ... → S<sub>terminal</sub><sup>1</sup> ≡ ⊥<sub>2</sub> → ..., where ≡ means structurally satisfies the role of, '
             'not is identical to. Each arrow within an instantiation is monotone and irreversible. Each ≡ '
             'crossing is not a path — it is a new instantiation of the universal structure. The Big Bang and '
             'heat death are the visible ends of a single instantiation, with the framework implying, but not '
             'requiring as a physical claim, that the structure continues on both sides.'),
    ]

    E.append(Paragraph('VII. Implications Within the Framework', S['h2']))
    E += [
        body('<b>Multiverse as mandatory.</b> The branching fan at each ⊥ node is not optional. T-SNAP fires on '
             'all accessible outbound vectors simultaneously. The multiverse is a structural consequence, not an interpretation.'),
        body('<b>Free will and irreversibility.</b> Within an instantiation, state sequences are monotone — no state '
             'can be decreased (ZP-A R1). Every choice is a join operation: S<sub>n</sub> ∨ α for some increment α. '
             'The algebra constrains only that the sequence be monotone, not which monotone path is '
             'taken. Each choice adds informational content irreversibly. Decisions are permanently '
             'encoded in the element\'s position in L.'),
        body('<b>Time\'s arrow.</b> The monotone sequence (ZP-A T3) is a structural definition of temporal '
             'direction. Time\'s irreversibility is C3 applied within an instantiation. The framework does not '
             'assume time asymmetry — it derives it.'),
        body('<b>Causal structure.</b> Every state is fully determined by the joins that produced it. The causal '
             'history of any state is encoded in its position in L. No effect without the join that produced it.'),
    ]

    print('[build_zpe] Building DA-3...')
    # ── FORMAL INSERT DA-3 ────────────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Formal Insert DA-3: Perspective-Relative Cardinality', S['h1']),
        Paragraph('<i>New in v2.0 | Cardinality as position-dependent measurement | '
                  'Accounts for Skolem, CH independence, Russell</i>', S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-3 Closes', S['h2']))
    E.append(body(
        'DA-2 establishes that instantiations form a directed tree and that branching at each ⊥ node '
        'produces multiple successor instantiations. This raises a question about the cardinality of '
        'branching: is the fan at each node countably or uncountably infinite? The answer, which DA-3 '
        'formalises, is that this question is perspective-dependent — and that this perspective-dependence '
        'is the same structural feature that underlies the major cardinality anomalies of classical set theory.'))

    E.append(Paragraph('II. Perspective-Dependence of Branching Cardinality', S['h2']))
    E.append(body(
        'From within instantiation I<sub>n</sub>, an observer occupies exactly one branch of I<sub>n+1</sub>. The other '
        'branches of I<sub>n+1</sub> are not accessible via any path — C3 and monotonicity jointly prohibit it. '
        'From inside, the branching factor is always 1: the observer sees one branch. From outside — '
        'from a meta-level view of the tree — the branching factor is the full fan of accessible outbound vectors.'))
    E.append(bridge_box(
        'Definition DA-3-D1 — Accessible Cardinality',
        [
            'The accessible cardinality of a position p in semilattice L is the cardinality of the set of '
            'states reachable from p by monotone sequences within the instantiation containing p.',
        ]
    ))
    E += [
        sp(4),
        body('The accessible cardinality from p is determined entirely by the structure of L above p. It is not '
             'an intrinsic property of a collection — it is a property of the relationship between a position '
             'and the states reachable from it. No position within any instantiation can access all '
             'cardinalities simultaneously. The meta-level view, which sees the full branching fan, is not a '
             'position any element of any instantiation can occupy.'),
        body('Remark R-DA3-1: To observe the full branching fan, one would need to occupy a position '
             'outside all instantiations. That position would itself be a state in some semilattice, subject to '
             'the same rules. The meta-view is either another instantiation (in which case the tree has no '
             'privileged outside view) or ⊥ itself (in which case the null state is the only position from which '
             'the full structure is visible — the state that contributes nothing and is present in everything). '
             'The Zero Paradox\'s name is more precise than it first appeared.'),
    ]

    E.append(Paragraph('III. Connection to Classical Set Theory', S['h2']))
    E += [
        body('<b>Skolem\'s Paradox.</b> ZFC can be given a countable model even though it proves uncountable '
             'sets exist. From within the model, certain sets are uncountable. From outside the model, it is '
             'countable. DA-3 gives this a precise interpretation: countable and uncountable are '
             'accessible-cardinality descriptions made from different positions — inside and outside the '
             'instantiation respectively. Skolem\'s Paradox is not a paradox. It is a perspective-dependence '
             'result, exactly as DA-3 predicts.'),
        body('<b>The Continuum Hypothesis.</b> G&#246;del and Cohen together established that CH is independent '
             'of ZFC — neither provable nor disprovable from the standard axioms. DA-3 accounts for this '
             'structurally: the answer to whether anything sits between ℵ<sub>0</sub> and 2<sup>ℵ<sub>0</sub></sup> depends on which '
             'instantiation one is measuring from. Different semilattices with different accessible cardinality '
             'structures will give different answers. The independence of CH is not an accident of axiom '
             'selection — it is the formal shadow of perspective-dependence. No axiom system located '
             'within the set-theoretic hierarchy can resolve it because resolution would require the '
             'meta-level view that DA-3 shows is unavailable from within any instantiation.'),
        body('<b>Russell\'s Paradox.</b> The set of all sets that do not contain themselves is paradoxical because its '
             'construction requires a position outside all sets. In the tree framework, that position is ⊥ — '
             'the only vantage point from which the full structure is simultaneously visible, and precisely '
             'the point that contributes nothing and therefore cannot serve as a measuring position. The '
             'paradox arises from attempting to occupy ⊥ as an observer while remaining within an '
             'instantiation. DA-3 establishes these are incompatible positions: ⊥ is the foundation, not a member.'),
    ]

    E.append(Paragraph('IV. The Cardinality Hierarchy as Perspective-Relative', S['h2']))
    E.append(body(
        'Cantor\'s theorem establishes that for any set S, |P(S)| > |S|, generating the hierarchy '
        'ℵ<sub>0</sub> &lt; 2<sup>ℵ<sub>0</sub></sup> &lt; 2<sup>2<sup>ℵ<sub>0</sub></sup></sup> &lt; ... '
        'DA-3 reframes this hierarchy not as a fixed ladder that mathematics climbs, but as a '
        'perspective-relative description of the branching structure of the instantiation tree, as seen '
        'from within different positions.'))
    E.append(bridge_box(
        'Claim DA-3-C1 — Perspective-Relative Absolute Cardinality',
        [
            'The appearance of absolute cardinality — cardinality as an intrinsic property independent of '
            'measuring position — is an artifact of treating the semilattice as having a view from outside. '
            'DA-2 and C-DA2 jointly prohibit such a view from within any instantiation.',
        ]
    ))
    E += [
        sp(4),
        body('The framework does not resolve the Continuum Hypothesis with a yes or no. It does '
             'something more fundamental: it explains why CH is independent of ZFC as a structural '
             'necessity, not an accident of which axioms were chosen. The reason cardinality resists '
             'resolution from within any fixed formal system is the same reason branching factor is '
             'perspective-dependent in the tree — you cannot see the full fan from inside a branch. '
             'G&#246;del\'s incompleteness theorems and the independence of CH are formal expressions of this structural fact.'),
        derived('Status: DEFINITIONAL ALIGNMENT + CANDIDATE CLAIM. DA-3-D1 and R-DA3-1 are '
                'definitional. DA-3-C1 is a candidate claim: structurally motivated within the framework; '
                'formal derivation of the connection between accessible cardinality and specific '
                'set-theoretic independence results is deferred to OQ-E2.'),
    ]

    E.append(Paragraph('V. Quantum Mechanics Correspondence', S['h2']))
    E.append(body(
        'The perspective-dependence of DA-3 maps directly onto the quantum measurement problem. '
        'Superposition — the simultaneous existence of multiple states before measurement — is the '
        'view of the branching fan from outside an instantiation. Collapse — the resolution to a single '
        'outcome upon measurement — is the view from inside an instantiation, where branching factor '
        'is always 1. Neither is more fundamental. They are perspective-relative descriptions of '
        'the same tree structure. The framework does not derive quantum mechanics, but it provides a '
        'structural account of why the measurement problem has the shape it does.'))

    print('[build_zpe] Building registers...')
    # ── UPDATED OPEN ITEMS REGISTER ───────────────────────────────────────────
    E += [hr(), Paragraph('Updated Open Items Register — ZP-E v2.0', S['h1'])]

    oq_rows = [
        ['AX-1: Binary Snap Causality',
         'CLOSED — T-SNAP',
         'AX-1 is no longer an axiom. Binary Snap derived via P<sub>0</sub> + DA-1 + L-RUN + TQ-IH + ZP-A D2.'],
        ['DA-1: Definitional Alignment',
         'CLOSED — Definitional',
         'D7 configurations are live by definition. No new axiom required.'],
        ['DA-2: Instantiation Succession',
         'CLOSED — Definitional',
         'Terminal state of I<sub>n</sub> satisfies A4 role of ⊥ for I<sub>n+1</sub>. C-DA2 establishes ontological novelty of each ⊥.'],
        ['DA-3: Perspective-Relative Cardinality',
         'CLOSED (definitional) / CANDIDATE (DA-3-C1)',
         'Cardinality is position-dependent. Skolem, CH independence, Russell accounted for structurally. OQ-E2 open.'],
        ['OQ-A1: Increment selection',
         'CLOSED — T5',
         'Iterative Forcing Theorem. α<sub>n</sub> = ε(S<sub>n</sub>). Grounding updated from AX-1 to T-SNAP.'],
        ['OQ-B1: p = 2',
         'CLOSED — ZP-B T0',
         'Derived from AX-B1 and MP-1.'],
        ['OQ-C1: Non-conservatism of DF',
         'CLOSED — ZP-C T2',
         'Infinite sequence divergence proven. No postulates remain.'],
        ['S1: Distribution stipulation',
         'CLOSED — ZP-C T1',
         'Derived from AX-B1 and RP-1.'],
        ['OQ-E1: Sequence vs. tree',
         'CLOSED — DA-2',
         'The structure is a forward-directed tree, not a linear sequence. Branching is mandatory via T-SNAP. '
         'Countable vs. uncountable branching is perspective-dependent (DA-3).'],
        ['OQ-E2: Cardinality-semilattice correspondence',
         'OPEN',
         'Do specific semilattice structures correspond to specific cardinality regimes? Can the framework '
         'make predictions about which instantiations satisfy CH and which do not?'],
        ['Remaining axioms',
         'INTENTIONAL — AX-B1, AX-G1, AX-G2',
         'These are the three foundational commitments of the system. No further reduction is claimed.'],
        ['Temperature T in BA-1',
         'PARAMETER — intentional',
         'Universe-contingent. Physical predictions explicitly conditional on instantiation-specific T.'],
    ]
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.22, TW*0.20, TW*0.58]
    ))

    # ── UPDATED TRACEABILITY REGISTER ─────────────────────────────────────────
    E += [sp(8), hr(), Paragraph('Updated Traceability Register — ZP-E v2.0', S['h1'])]

    trace_rows = [
        ['Binary Snap causality',
         'ZP-C D1, L-RUN, TQ-IH; ZP-A D2; DA-1',
         'None',
         'Derived — T-SNAP ✓ (was: Axiomatic — AX-1)'],
        ['DA-1: Instantiation = execution',
         'AX-B1, ZP-C D7',
         'None',
         'Definitional Alignment — clarification of scope; no new axiom'],
        ['DA-2: Instantiation succession',
         'ZP-A A4, CC-1; ZP-B C3, R1; T-SNAP',
         'None',
         'Definitional Alignment — clarification of CC-1 scope; no new axiom'],
        ['C-DA2: Novelty of ⊥',
         'DA-2, ZP-B C3',
         'None',
         'Derived — Corollary of DA-2 and C3 ✓'],
        ['DA-3: Perspective-relative cardinality',
         'DA-2, C-DA2, ZP-B R1',
         'None',
         'Definitional (DA-3-D1, R-DA3-1); Candidate (DA-3-C1)'],
        ['T-SNAP: Snap is derived',
         'T-BUF chain + DA-1',
         'None',
         'Derived — Cross-Framework ✓'],
        ['AX-1 retirement',
         'T-SNAP closes AX-1',
         'N/A',
         'AX-1 is no longer an axiom; T-SNAP is its replacement'],
        ['Iterative Forcing T5',
         'AX-B1, T-SNAP (replaces AX-1)',
         'None',
         'Derived — grounding strengthened'],
        ['Multiverse mandated',
         'T-SNAP, DA-2',
         'None',
         'Derived consequence — not an interpretation'],
        ['OQ-E2: Cardinality correspondence',
         'DA-3',
         'N/A',
         'OPEN — formal derivation deferred'],
    ]
    E.append(data_table(
        ['Claim', 'Grounded In', 'Bridge Axiom?', 'Status'],
        trace_rows,
        [TW*0.22, TW*0.28, TW*0.12, TW*0.38]
    ))

    # ── VALIDATION STATUS ─────────────────────────────────────────────────────
    E += [sp(8), hr(), Paragraph('Validation Status — ZP-E v2.0', S['h1'])]

    val_rows = [
        ['DA-1: Definitional Alignment',
         'Valid — Clarification of scope; no new axiom. D7 configurations are live by definition; AX-B1 ensures the binary applies. ✓'],
        ['T-SNAP: Binary Snap derived',
         'Valid — Derived. Seven-step proof. All dependencies are closed theorems in their own documents. ✓'],
        ['AX-1 retirement',
         'Valid — AX-1 superseded by T-SNAP. No content lost; claim strengthened from assumed to derived.'],
        ['DA-2: Instantiation Succession',
         'Valid — Definitional Alignment. Clarification of CC-1 scope. No new axiom. A4 role of ⊥ extended across instantiation boundaries. ✓'],
        ['C-DA2: Ontological Novelty of ⊥',
         'Valid — Derived. Follows directly from DA-2 and ZP-B C3. ✓'],
        ['Directed instantiation tree',
         'Valid — Derived structural consequence of T-SNAP + DA-2. Branching is mandatory, not optional. Forward edges only.'],
        ['Multiverse as mandatory',
         'Valid — Derived. T-SNAP fires on all accessible outbound vectors. Not an interpretation.'],
        ['Free will / irreversibility',
         'Valid — Structural consequence. Monotonicity (T3) constrains direction; additive ontology (R1) prohibits reduction. Path choice is undetermined by algebra.'],
        ['Time\'s arrow',
         'Valid — Derived from ZP-A T3 (monotonicity) and ZP-B C3 (irreversibility). Not assumed.'],
        ['DA-3: Perspective-Relative Cardinality',
         'Valid (definitional components: DA-3-D1, R-DA3-1). Candidate (DA-3-C1: connection to specific set-theoretic independence results). OQ-E2 open.'],
        ['Skolem, CH, Russell accounted for',
         'Structurally motivated — each is identified as an instance of perspective-dependence. Formal derivation deferred to OQ-E2.'],
        ['Remaining axioms: AX-B1, AX-G1, AX-G2',
         'Intentional foundational commitments. No further reduction claimed.'],
        ['All other ZP-E theorems (T1–T7, T2-C)',
         'Unaffected in content. T4 and T5 carry upgraded status labels (AX-1 → T-SNAP).'],
    ]
    E.append(data_table(
        ['Component', 'Status / Notes'],
        val_rows,
        [TW*0.32, TW*0.68]
    ))

    E += [
        sp(12),
        hr(),
        Paragraph(
            '<i>End of ZP-E v2.0 | Three formal inserts: DA-1, DA-2, DA-3 | '
            'One open question: OQ-E2 | Remaining axioms: AX-B1, AX-G1, AX-G2</i>',
            S['endnote']),
    ]

    print(f'[build_zpe] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zpe] Written: {out_path}')


if __name__ == '__main__':
    repo_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    out = os.path.abspath(os.path.join(repo_root, 'ZP-E_Bridge_Document_v2_0.pdf'))
    build_zpe(out)
