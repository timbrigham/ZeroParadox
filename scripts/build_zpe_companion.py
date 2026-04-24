"""
Build ZP-E Illustrated Companion
Covers: four-framework convergence diagram, AX-1 → T-SNAP derivation chain,
remaining structural commitments table.
"""

import os
from reportlab.lib import colors
from reportlab.lib.pagesizes import LETTER
from reportlab.lib.units import inch
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.graphics.shapes import Drawing, Line, String, Rect
from reportlab.graphics import renderPDF

FONT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fonts') + os.sep
pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'))
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf'))
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf'))
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'STIXTwo-Math.ttf'))

# Companion palette: 15% white tint on formal document header colors
COMP_BLUE  = colors.HexColor('#4D89C0')
COMP_GREEN = colors.HexColor('#4D9050')
COMP_SLATE = colors.HexColor('#60727B')
COMP_AMBER = colors.HexColor('#BB8C26')
SLATE_LITE = colors.HexColor('#ECEFF1')
AMBER_LITE = colors.HexColor('#FFF8E7')
AMBER_BOX  = colors.HexColor('#E65100')  # diagram: ε₀ snap state
BLACK      = colors.black
WHITE      = colors.white
GREY       = colors.HexColor('#888888')
GREY_TEXT  = colors.HexColor('#555555')  # diagram caption text

TW = 6.5 * inch
LM = RM = TM = BM = 1.0 * inch

CS = {
    'title':    ParagraphStyle('ctitle',   fontName='DV-B',  fontSize=22, leading=28,
                               alignment=1, spaceAfter=4, textColor=BLACK),
    'subtitle': ParagraphStyle('csubtitle',fontName='DV-I',  fontSize=12, leading=16,
                               alignment=1, spaceAfter=4),
    'meta':     ParagraphStyle('cmeta',    fontName='DV',    fontSize=9,  leading=13,
                               alignment=1, spaceAfter=8, textColor=colors.grey),
    'disc':     ParagraphStyle('cdisc',    fontName='DVS-I', fontSize=9,  leading=13,
                               spaceAfter=10, textColor=GREY_TEXT),
    'h1':       ParagraphStyle('ch1',      fontName='DV-B',  fontSize=13, leading=17,
                               spaceBefore=14, spaceAfter=5, textColor=COMP_BLUE),
    'body':     ParagraphStyle('cbody',    fontName='DVS',   fontSize=10, leading=14,
                               spaceAfter=6),
    'caption':  ParagraphStyle('ccaption', fontName='DVS-I', fontSize=9,  leading=12,
                               spaceAfter=8, textColor=GREY_TEXT),
    'ex_title': ParagraphStyle('cex_title',fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=COMP_AMBER),
    'ex_body':  ParagraphStyle('cex_body', fontName='DVS',   fontSize=9,  leading=13),
    'rem':      ParagraphStyle('crem',     fontName='DVS-I', fontSize=9,  leading=13),
    'kr_hdr':   ParagraphStyle('ckr_hdr',  fontName='DVS-B', fontSize=9,  leading=13,
                               textColor=WHITE),
    'kr_body':  ParagraphStyle('ckr_body', fontName='DVS',   fontSize=9,  leading=13),
    'tbl_hdr':  ParagraphStyle('ctbl_hdr', fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=WHITE),
    'tbl_cell': ParagraphStyle('ctbl_cell',fontName='DVS',   fontSize=9,  leading=13),
}

def sp(n=6): return Spacer(1, n)

def fix(text):
    sub_map = {'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4',
               '₅':'5','₆':'6','₇':'7','₈':'8','₉':'9','ₙ':'n'}
    for ch, rep in sub_map.items():
        text = text.replace(ch, f'<sub>{rep}</sub>')
    for char, ent in [('⊥','&#8869;'),('∨','&#8744;'),('≤','&#8804;'),
                      ('≥','&#8805;'),('≠','&#8800;'),('∈','&#8712;'),
                      ('→','&#8594;'),('∞','&#8734;'),('—','&#8212;'),
                      ('ε','&#949;')]:
        text = text.replace(char, ent)
    return text

def cbody(t): return Paragraph(fix(t), CS['body'])
def ccaption(t): return Paragraph(fix(t), CS['caption'])

def example_box(title, rows):
    data = [[Paragraph(title, CS['ex_title'])]]
    for r in rows:
        data.append([Paragraph(fix(r), CS['ex_body'])])
    ts = TableStyle([
        ('BOX',          (0,0),(-1,-1), 1.5, COMP_AMBER),
        ('LINEBELOW',    (0,0),(-1,0),  0.5, COMP_AMBER),
        ('BACKGROUND',   (0,0),(-1,-1), AMBER_LITE),
        ('TOPPADDING',   (0,0),(-1,-1), 5), ('BOTTOMPADDING',(0,0),(-1,-1), 5),
        ('LEFTPADDING',  (0,0),(-1,-1), 8), ('RIGHTPADDING', (0,0),(-1,-1), 8),
        ('VALIGN',       (0,0),(-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW]); t.setStyle(ts); return t

def remember_box(text):
    ts = TableStyle([
        ('BACKGROUND',   (0,0),(-1,-1), SLATE_LITE),
        ('BOX',          (0,0),(-1,-1), 0.5, COMP_SLATE),
        ('TOPPADDING',   (0,0),(-1,-1), 8), ('BOTTOMPADDING',(0,0),(-1,-1), 8),
        ('LEFTPADDING',  (0,0),(-1,-1), 10),('RIGHTPADDING', (0,0),(-1,-1), 10),
    ])
    t = Table([[Paragraph(fix(text), CS['rem'])]], colWidths=[TW])
    t.setStyle(ts); return t

def key_result_box(title, body_text):
    data = [[Paragraph(fix(title), CS['kr_hdr'])],
            [Paragraph(fix(body_text), CS['kr_body'])]]
    ts = TableStyle([
        ('BACKGROUND',   (0,0),(-1,0),  COMP_GREEN),
        ('BACKGROUND',   (0,1),(-1,-1), colors.white),
        ('BOX',          (0,0),(-1,-1), 0.5, COMP_GREEN),
        ('TOPPADDING',   (0,0),(-1,-1), 6), ('BOTTOMPADDING',(0,0),(-1,-1), 6),
        ('LEFTPADDING',  (0,0),(-1,-1), 8), ('RIGHTPADDING', (0,0),(-1,-1), 8),
        ('VALIGN',       (0,0),(-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW]); t.setStyle(ts); return t

def four_framework_diagram():
    """Central 'Binary Snap' circle with four framework boxes pointing inward."""
    dw, dh = TW, 3.4 * inch
    d = Drawing(dw, dh)

    cx, cy = dw / 2, dh / 2

    # Central amber circle
    cr = 42
    from reportlab.graphics.shapes import Circle
    d.add(Circle(cx, cy, cr, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(String(cx - 26, cy + 6,  'Binary', fontSize=9.5, fontName='DV-B', fillColor=WHITE))
    d.add(String(cx - 17, cy - 7, 'Snap',   fontSize=9.5, fontName='DV-B', fillColor=WHITE))

    # Helper: draw a teal box with two text lines and an arrow toward the center
    def framework_box(bx, by, bw, bh, label, sub1, sub2, ax1, ay1, ax2, ay2):
        d.add(Rect(bx, by, bw, bh, fillColor=COMP_BLUE, strokeColor=COMP_BLUE,
                   strokeWidth=1, rx=4, ry=4))
        d.add(String(bx + 8, by + bh - 16, label, fontSize=9.5,
                     fontName='DV-B', fillColor=WHITE))
        d.add(String(bx + 8, by + bh - 28, sub1, fontSize=7.5,
                     fontName='DV-I', fillColor=colors.white))
        d.add(String(bx + 8, by + bh - 39, sub2, fontSize=7.5,
                     fontName='DV-I', fillColor=colors.white))
        # Arrow
        d.add(Line(ax1, ay1, ax2, ay2, strokeColor=COMP_BLUE, strokeWidth=1.8))
        dx, dy = ax2 - ax1, ay2 - ay1
        ln = (dx*dx + dy*dy) ** 0.5
        if ln > 0:
            ux, uy = dx/ln, dy/ln
            px, py = -uy, ux
            hs = 6
            d.add(Line(ax2, ay2,
                       ax2 - hs*ux + hs*0.5*px, ay2 - hs*uy + hs*0.5*py,
                       strokeColor=COMP_BLUE, strokeWidth=1.8))
            d.add(Line(ax2, ay2,
                       ax2 - hs*ux - hs*0.5*px, ay2 - hs*uy - hs*0.5*py,
                       strokeColor=COMP_BLUE, strokeWidth=1.8))

    bw, bh = 1.35*inch, 0.62*inch

    # Top: ZP-A (above)
    bx = cx - bw/2; by = cy + cr + 14
    framework_box(bx, by, bw, bh,
                  'ZP-A: Algebra', '⊥ ≤ x for all x', 'Join accumulates',
                  cx, by, cx, cy + cr + 2)

    # Bottom: ZP-C (below)
    by2 = cy - cr - 14 - bh
    framework_box(cx - bw/2, by2, bw, bh,
                  'ZP-C: Info Theory', 'I(x) → ∞ as x → 0', 'Singularity',
                  cx, by2 + bh, cx, cy - cr - 2)

    # Left: ZP-B
    bxl = cx - cr - 16 - bw; byl = cy - bh/2
    framework_box(bxl, byl, bw, bh,
                  'ZP-B: Topology', '0 is isolated', 'No path returns',
                  bxl + bw, cy, cx - cr - 2, cy)

    # Right: ZP-D
    bxr = cx + cr + 16; byr = cy - bh/2
    framework_box(bxr, byr, bw, bh,
                  'ZP-D: Hilbert', 'T(0) = e₀', 'Orthogonal shift',
                  bxr, cy, cx + cr + 2, cy)

    d.add(String(14, 10,
                 'The Binary Snap (amber) described simultaneously in all four frameworks. '
                 'Each arrow is an independent proof of the same structural fact.',
                 fontSize=7.5, fontName='DV-I', fillColor=GREY_TEXT))
    return d

def tsnap_chain_diagram():
    """P₀ → DA-1 → L-RUN → TQ-IH → ZP-A D2 → T-SNAP derivation chain."""
    dw, dh = TW, 1.6 * inch
    d = Drawing(dw, dh)

    steps = [
        ('P₀',      'Incomp.\nthreshold'),
        ('DA-1',    'D7 configs\nare live'),
        ('L-RUN',   'Exec =\nnon-null'),
        ('TQ-IH',   'No null-only\ntrace'),
        ('ZP-A D2', 'State change\n= Snap'),
        ('T-SNAP',  'Derived\ntheorem'),
    ]
    n = len(steps)
    bw = (dw - 0.3*inch) / n - 6
    bh = 0.52 * inch
    by = dh * 0.52
    gap = 6
    x0 = 10

    for i, (label, sub) in enumerate(steps):
        bx = x0 + i * (bw + gap)
        fill = AMBER_BOX if i == n-1 else COMP_BLUE
        d.add(Rect(bx, by, bw, bh, fillColor=fill, strokeColor=COMP_BLUE,
                   strokeWidth=0.8, rx=3, ry=3))
        lw = len(label) * 6.2
        d.add(String(bx + bw/2 - lw/2, by + bh - 16, label,
                     fontSize=9, fontName='DV-B', fillColor=WHITE))
        # Sub-label lines
        sub_lines = sub.split('\n')
        sub_y = by - 14
        for sl in sub_lines:
            sw = len(sl) * 5.2
            d.add(String(bx + bw/2 - sw/2, sub_y, sl,
                         fontSize=7, fontName='DV-I', fillColor=GREY_TEXT))
            sub_y -= 10

        if i < n-1:
            nx = bx + bw + gap
            ax1, ax2 = bx + bw + 1, nx - 1
            amid = by + bh/2
            d.add(Line(ax1, amid, ax2, amid, strokeColor=COMP_BLUE, strokeWidth=1.5))
            d.add(Line(ax2-5, amid-3, ax2, amid, strokeColor=COMP_BLUE, strokeWidth=1.5))
            d.add(Line(ax2-5, amid+3, ax2, amid, strokeColor=COMP_BLUE, strokeWidth=1.5))

    d.add(String(14, dh - 14,
                 'AX-1 (Binary Snap Causality) is now Theorem T-SNAP — derived, not assumed.',
                 fontSize=8, fontName='DV-B', fillColor=AMBER_BOX))
    return d

def axioms_table():
    """AX-B1 / AX-G1 / AX-G2 table."""
    hdr = [Paragraph('Commitment', CS['tbl_hdr']),
           Paragraph('Statement', CS['tbl_hdr'])]
    rows = [
        ['AX-B1',
         'Binary Existence. A state either exists or it does not. No third option. '
         'Directly verifiable by computation — not a novel commitment.'],
        ['AX-G1',
         'Initial Object Exists. There is a starting point that reaches everything. '
         'Not a novel commitment — grounded in ⊥ as the bottom element of the ZP-A semilattice.'],
        ['AX-G2',
         'Source Asymmetry. Nothing returns to the initial object. '
         'The origin is unreachable from outside. '
         'Not a novel commitment — follows from ZP-A antisymmetry and ZP-B C3.'],
    ]
    data = [hdr] + [[Paragraph(fix(r[0]), CS['tbl_cell']),
                     Paragraph(fix(r[1]), CS['tbl_cell'])] for r in rows]
    ts = TableStyle([
        ('BACKGROUND',    (0,0),(-1,0),  COMP_BLUE),
        ('ROWBACKGROUNDS',(0,1),(-1,-1), [WHITE, colors.HexColor('#F0F8F8')]),
        ('BOX',           (0,0),(-1,-1), 0.5, COMP_BLUE),
        ('LINEBELOW',     (0,0),(-1,0),  0.5, COMP_BLUE),
        ('INNERGRID',     (0,1),(-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0),(-1,-1), 5), ('BOTTOMPADDING',(0,0),(-1,-1), 5),
        ('LEFTPADDING',   (0,0),(-1,-1), 7), ('RIGHTPADDING', (0,0),(-1,-1), 7),
        ('VALIGN',        (0,0),(-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW*0.18, TW*0.82])
    t.setStyle(ts); return t

def build():
    out_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                            'ZP-E_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState(); canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-E Companion  |  Bridge Document  |  April 2026')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
                            title='ZP-E Illustrated Companion', author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # Header banner
    hdr_ts = TableStyle([('BACKGROUND',(0,0),(-1,-1),COMP_BLUE),
                         ('TOPPADDING',(0,0),(-1,-1),8),('BOTTOMPADDING',(0,0),(-1,-1),8),
                         ('LEFTPADDING',(0,0),(-1,-1),10)])
    hdr = Table([[Paragraph('ZP-E Illustrated Companion',
                            ParagraphStyle('hdr',fontName='DV-B',fontSize=11,textColor=WHITE))]],
                colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E += [hdr, sp(6),
          Paragraph('Where all four frameworks converge —\nand AX-1 becomes a theorem',
                    CS['title']),
          Paragraph('Bridge Document | DA-1 / T-SNAP Update', CS['subtitle']),
          Paragraph('ZP Companion | April 2026', CS['meta']),
          Paragraph(
              'This companion explains the ideas in plain language with diagrams and real-world '
              'examples. It is not the formal ontology — every claim here restates a result '
              'already proven in the corresponding technical document. Consult that document for '
              'the authoritative mathematics.', CS['disc'])]

    # What Is ZP-E Doing?
    E.append(Paragraph('What Is ZP-E Doing?', CS['h1']))
    E.append(cbody(
        'ZP-E is the cross-framework synthesis. Written last — after ZP-A through ZP-D are each '
        'internally closed — its job is to show that the four independent frameworks all describe '
        'the same event: the Binary Snap, from four different mathematical vantage points.'))
    E.append(cbody(
        'ZP-E does not re-derive anything. It imports closed results from each sub-document and '
        'shows their consistency. Where a cross-framework connection requires an assumption, '
        'that assumption is named explicitly as a bridge axiom — not hidden inside the argument.'))
    E.append(sp(4))

    # Four Descriptions
    E.append(Paragraph('The Four Descriptions of the Same Event', CS['h1']))
    E.append(cbody(
        'The Binary Snap — the transition from nothing (⊥) to the first state (ε₀) — looks '
        'different depending on which mathematical language you use. ZP-E\'s central result is '
        'that all four descriptions are consistent: one event, four angles.'))
    E.append(four_framework_diagram())
    E.append(ccaption(
        'The Binary Snap (amber center) described simultaneously in all four frameworks. '
        'Each arrow represents an independent proof of the same structural fact.'))
    E.append(sp(4))
    E.append(example_box('Real-world example — A car crash described by four witnesses', [
        'An engineer (forces), a doctor (injuries), a lawyer (liability), and a physicist '
        '(energy) each describe the same crash completely within their own discipline. '
        'ZP-E shows the four mathematical frameworks are in exactly this relationship to '
        'the Binary Snap.',
    ]))
    E.append(remember_box(
        'Remember: The car crash illustrates what it means to describe one event in multiple '
        'frameworks. The Zero Paradox is not about car crashes — it is about the emergence '
        'of any state from a null condition.'))
    E.append(sp(6))

    # AX-1 → T-SNAP
    E.append(Paragraph('The Central Advance: AX-1 is Now a Theorem', CS['h1']))
    E.append(cbody(
        'In earlier versions, the Binary Snap causality was listed as AX-1 — an axiom: a '
        'foundational assumption that could not be derived. The claim was: when P₀ is reached, '
        'the Snap happens. Why? Because AX-1 says so.'))
    E.append(cbody(
        'The DA-1 insert changes this. The argument is now complete: reaching P₀ means a '
        'live machine configuration exists (DA-1). Any live configuration passes through c₁ '
        '(definition). c₁ is non-null (L-RUN). No program avoids this (TQ-IH). A non-null '
        'state change from ⊥ is the Binary Snap (ZP-A D2). The Snap is derived — not assumed.'))
    E.append(tsnap_chain_diagram())
    E.append(ccaption(
        'The T-SNAP derivation chain: six steps, no axioms beyond AX-B1 and the definition '
        'of a Turing machine. AX-1 (amber) is now a theorem.'))
    E.append(sp(4))
    E.append(example_box('Real-world example — A legal case that becomes undeniable', [
        'A court case starts with an assumption: "the defendant was at the scene." Then '
        'surveillance footage, phone records, and witness testimony all confirm it. The '
        'assumption becomes a proven fact. T-SNAP is the mathematical equivalent: what was '
        'assumed (AX-1) is now proven (T-SNAP) by an independent chain of evidence.',
    ]))
    E.append(sp(8))

    # Remaining Commitments
    E.append(Paragraph('What the Framework Still Assumes', CS['h1']))
    E.append(cbody(
        'After T-SNAP, the framework rests on exactly three commitments — '
        'none of them novel starting assumptions:'))
    E.append(axioms_table())
    E.append(sp(6))
    E.append(cbody(
        'AX-1 is no longer on this list. The framework makes no stronger claim than it has to.'))
    E.append(sp(8))
    E.append(remember_box(
        'Remember: The structural results — monotonicity, topological isolation, '
        'informational singularity, orthogonal shifts — hold in any instantiation of the '
        'framework. The Zero Paradox is a universal ontology of state emergence, not a '
        'physical theory of our particular universe.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
