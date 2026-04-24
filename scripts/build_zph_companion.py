"""
Build ZP-H Illustrated Companion (v1.1, new standalone document)
Standalone companion for ZP-H: Categorical Bridge only.
ZP-G has its own companion (build_zpg_companion.py).

Accessibility target: 2 years of college math.
Assumes reader has read ZP-G companion. Builds on category/functor vocabulary.
"""

import os
from reportlab.lib import colors
from reportlab.lib.pagesizes import LETTER
from reportlab.lib.units import inch
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Polygon
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
BLACK      = colors.black
WHITE      = colors.white

# Domain colors for the four-functor diagram (semantic distinction between functors)
TEAL   = colors.HexColor('#2A8080')
GREEN  = colors.HexColor('#2E7D32')
RED    = colors.HexColor('#8B1A1A')
PURPLE = colors.HexColor('#5B2D8E')
INDIGO = colors.HexColor('#3D3D8F')

TW = 6.5 * inch
LM = RM = 1.0 * inch
TM = BM = 1.0 * inch

CS = {
    'title':    ParagraphStyle('ctitle',   fontName='DV-B',  fontSize=22, leading=28,
                               alignment=1, spaceAfter=4, textColor=BLACK),
    'subtitle': ParagraphStyle('csubtitle',fontName='DV-I',  fontSize=12, leading=16,
                               alignment=1, spaceAfter=4),
    'meta':     ParagraphStyle('cmeta',    fontName='DV',    fontSize=9,  leading=13,
                               alignment=1, spaceAfter=8, textColor=colors.grey),
    'disc':     ParagraphStyle('cdisc',    fontName='DVS-I', fontSize=9,  leading=13,
                               spaceAfter=10, textColor=colors.HexColor('#555555')),
    'h1':       ParagraphStyle('ch1',      fontName='DV-B',  fontSize=13, leading=17,
                               spaceBefore=14, spaceAfter=5, textColor=COMP_BLUE),
    'body':     ParagraphStyle('cbody',    fontName='DVS',   fontSize=10, leading=14,
                               spaceAfter=6),
    'caption':  ParagraphStyle('ccaption', fontName='DVS-I', fontSize=9,  leading=12,
                               spaceAfter=8, textColor=colors.HexColor('#555555')),
    'ex_title': ParagraphStyle('cex_title',fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=COMP_AMBER),
    'ex_body':  ParagraphStyle('cex_body', fontName='DVS',   fontSize=9,  leading=13),
    'rem':      ParagraphStyle('crem',     fontName='DVS-I', fontSize=9,  leading=13),
    'kr_hdr':   ParagraphStyle('ckr_hdr',  fontName='DVS-B', fontSize=9,  leading=13,
                               textColor=WHITE),
    'kr_body':  ParagraphStyle('ckr_body', fontName='DVS',   fontSize=9,  leading=13),
}

def sp(n=6):
    return Spacer(1, n)

def fix(text):
    sub_map = {'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4',
               '₅':'5','₆':'6','₇':'7','₈':'8','₉':'9',
               'ₙ':'n','ₖ':'k','ₘ':'m'}
    for ch, rep in sub_map.items():
        text = text.replace(ch, f'<sub>{rep}</sub>')
    text = text.replace('✓', '<font name="DV">&#10003;</font>')
    text = text.replace('∅', '<font name="DV">&#8709;</font>')
    for char, entity in [('ℚ','&#8474;'),('ℤ','&#8484;'),('ℂ','&#8450;'),
                          ('ℕ','&#8469;'),('ℝ','&#8477;')]:
        text = text.replace(char, f'<font name="DV">{entity}</font>')
    replacements = [
        ('⊥', '&#8869;'), ('∨', '&#8744;'), ('≤', '&#8804;'), ('≥', '&#8805;'),
        ('≠', '&#8800;'), ('∈', '&#8712;'), ('→', '&#8594;'), ('←', '&#8592;'),
        ('∞', '&#8734;'), ('⟨', '&#10216;'), ('⟩', '&#10217;'),
        ('—', '&#8212;'), ('–', '&#8211;'), ('×', '&#215;'), ('−', '&#8722;'),
        ('ε', '&#949;'), ('ι', '&#953;'), ('∀', '&#8704;'), ('∃', '&#8707;'),
        ('∘', '&#8728;'), ('∥', '&#8741;'), ('‖', '&#8214;'),
    ]
    for char, entity in replacements:
        text = text.replace(char, entity)
    return text

def cbody(text):
    return Paragraph(fix(text), CS['body'])

def ccaption(text):
    return Paragraph(fix(text), CS['caption'])

def example_box(title, rows):
    data = [[Paragraph(title, CS['ex_title'])]]
    for r in rows:
        data.append([Paragraph(fix(r), CS['ex_body'])])
    ts = TableStyle([
        ('BOX',           (0,0), (-1,-1), 1.5, COMP_AMBER),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, COMP_AMBER),
        ('BACKGROUND',    (0,0), (-1,-1), AMBER_LITE),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW])
    t.setStyle(ts)
    return t

def remember_box(text):
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), SLATE_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, COMP_SLATE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
        ('RIGHTPADDING',  (0,0), (-1,-1), 10),
    ])
    t = Table([[Paragraph(fix(text), CS['rem'])]], colWidths=[TW])
    t.setStyle(ts)
    return t

def key_result_box(title, body_text):
    data = [[Paragraph(fix(title), CS['kr_hdr'])],
            [Paragraph(fix(body_text), CS['kr_body'])]]
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  COMP_GREEN),
        ('BACKGROUND',    (0,1), (-1,-1), colors.white),
        ('BOX',           (0,0), (-1,-1), 0.5, COMP_GREEN),
        ('TOPPADDING',    (0,0), (-1,-1), 6),
        ('BOTTOMPADDING', (0,0), (-1,-1), 6),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW])
    t.setStyle(ts)
    return t

def four_functor_diagram():
    """Central category C with four arrows going to four domain frameworks."""
    # dh must be tall enough for boxes at cy±65 (box half-height 17) plus caption (14) + margin
    dw, dh = TW, 3.4 * inch
    d = Drawing(dw, dh)

    cx = dw / 2
    # Shift cy up slightly so bottom boxes have clearance for caption string
    cy = dh / 2 + 14

    # Central C box
    box_w, box_h = 64, 36
    bx1, by1 = cx - box_w/2, cy - box_h/2
    d.add(Rect(bx1, by1, box_w, box_h,
               fillColor=colors.HexColor('#F0EAF8'), strokeColor=colors.HexColor('#5B2D8E'),
               strokeWidth=1.5))
    d.add(String(cx - 8, cy - 6, 'C', fontSize=16, fontName='DV-B',
                 fillColor=colors.HexColor('#5B2D8E')))

    # Four target boxes — keep within [0, dh].
    # cy + 65 = top targets;  cy - 65 = bottom targets (box half-height 17 → min y = cy-82 > 14 ok)
    targets = [
        # (label, color, box center x, box center y, arrow end x, arrow end y)
        ('ZP-A\nLattice',   TEAL,   cx - 195, cy + 65,  cx - 150, cy + 52),
        ('ZP-B\np-Adic',    GREEN,  cx + 100, cy + 65,  cx + 142, cy + 52),
        ('ZP-C\nInfo',      RED,    cx - 195, cy - 65,  cx - 150, cy - 52),
        ('ZP-D\nHilbert',   INDIGO, cx + 100, cy - 65,  cx + 142, cy - 52),
    ]

    functor_labels = ['FA', 'FB', 'FC', 'FD']
    arrow_starts = [
        (cx - box_w/2, cy + box_h/4),
        (cx + box_w/2, cy + box_h/4),
        (cx - box_w/2, cy - box_h/4),
        (cx + box_w/2, cy - box_h/4),
    ]

    for i, (lbl, col, bx, by, aex, aey) in enumerate(targets):
        asx, asy = arrow_starts[i]
        # Draw arrow
        d.add(Line(asx, asy, aex, aey, strokeColor=col, strokeWidth=2))
        # Arrowhead
        import math
        dx, dy = aex - asx, aey - asy
        L = math.sqrt(dx*dx + dy*dy) or 1
        ux, uy = dx/L, dy/L
        px, py = -uy, ux
        d.add(Polygon([aex, aey,
                       aex - ux*9 + px*4, aey - uy*9 + py*4,
                       aex - ux*9 - px*4, aey - uy*9 - py*4],
                      fillColor=col, strokeColor=col, strokeWidth=0))
        # Functor label on arrow midpoint
        mx = (asx + aex) / 2
        my = (asy + aey) / 2
        fl = functor_labels[i]
        d.add(String(mx - 8, my + 4, fl[0], fontSize=9, fontName='DV-B', fillColor=col))
        d.add(String(mx - 2, my, fl[1], fontSize=6, fontName='DV-B', fillColor=col))

        # Target box
        tw, th = 70, 34
        d.add(Rect(bx - tw/2, by - th/2, tw, th,
                   fillColor=colors.white, strokeColor=col, strokeWidth=1.2))
        lines = lbl.split('\n')
        for j, line in enumerate(lines):
            ly_text = by + (len(lines) - 1 - j) * 11 - 6
            d.add(String(bx - tw/2 + 6, ly_text, line,
                         fontSize=8.5, fontName='DV-B', fillColor=col))

    d.add(String(dw/2 - 200, 16,
                 'Four functors carry the abstract structure of C into four concrete mathematical frameworks',
                 fontSize=8, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    return d

def snap_convergence_diagram():
    """Shows the Binary Snap described by all four frameworks."""
    dw, dh = TW, 1.6 * inch
    d = Drawing(dw, dh)

    cy = dh / 2
    lx = 30
    rx = dw - 30
    snap_x = dw / 2

    domain_colors = [TEAL, GREEN, RED, INDIGO]
    domain_labels = ['Lattice: first join', 'p-Adic: clopen jump', 'Info: 1-bit cost', 'Hilbert: right-angle shift']
    y_offsets = [30, 10, -10, -30]

    # Draw lines from left (0) to snap, then snap to right (e0)
    for i, (col, lbl, yoff) in enumerate(zip(domain_colors, domain_labels, y_offsets)):
        y = cy + yoff
        d.add(Line(lx + 20, y, snap_x - 10, y, strokeColor=col, strokeWidth=1.5))
        d.add(Line(snap_x + 10, y, rx - 20, y, strokeColor=col, strokeWidth=1.5))

    # Left dot: 0
    d.add(Circle(lx + 18, cy, 8, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(String(lx + 12, cy - 6, '0', fontSize=9, fontName='DV-B', fillColor=WHITE))
    d.add(String(lx + 4, cy - 20, '(null)', fontSize=7.5, fontName='DV-I',
                 fillColor=colors.HexColor('#888888')))

    # Snap marker (vertical line)
    d.add(Line(snap_x, cy - 40, snap_x, cy + 40, strokeColor=BLACK, strokeWidth=2))
    d.add(String(snap_x - 18, cy + 44, 'T-SNAP', fontSize=8, fontName='DV-B', fillColor=BLACK))

    # Right dot: e0
    d.add(Circle(rx - 18, cy, 8, fillColor=INDIGO, strokeColor=INDIGO, strokeWidth=0))
    d.add(String(rx - 26, cy - 6, 'e0', fontSize=8, fontName='DV-B', fillColor=WHITE))
    d.add(String(rx - 30, cy - 20, '(first state)', fontSize=7.5, fontName='DV-I',
                 fillColor=colors.HexColor('#888888')))

    # Labels on right side
    for i, (col, lbl, yoff) in enumerate(zip(domain_colors, domain_labels, y_offsets)):
        y = cy + yoff
        d.add(String(rx - 16, y - 5, lbl, fontSize=7, fontName='DV-I', fillColor=col))

    d.add(String(dw/2 - 165, dh - 12,
                 'All four frameworks describe the same Binary Snap — each from its own perspective',
                 fontSize=8.5, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    return d

def build():
    out_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                            'ZP-H_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-H Companion  |  Categorical Bridge  |  April 2026  |  v1.1')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM,
                            title='ZP-H Illustrated Companion',
                            author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # ── Header banner ──────────────────────────────────────────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('ZP-H Illustrated Companion',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    E += [
        Paragraph('Four maps, one structure', CS['title']),
        Paragraph('Categorical Bridge | Version 1.1', CS['subtitle']),
        Paragraph('ZP Companion | April 2026', CS['meta']),
        Paragraph(
            'This companion explains the ideas in plain language with diagrams and real-world '
            'examples. It is not the formal ontology — every claim here restates a result already '
            'proven in the corresponding technical document. Consult that document for the '
            'authoritative mathematics. This document assumes familiarity with the ZP-G '
            'Illustrated Companion.',
            CS['disc']),
    ]

    # ── What ZP-H is doing ─────────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-H Doing?', CS['h1']))
    E.append(cbody(
        'ZP-G built an abstract category C and proved that its structure — an initial object '
        'with no return morphisms — captures the essential shape of the Zero Paradox. But an '
        'abstract category on its own is just a skeleton. ZP-H puts flesh on the bones.'))
    E.append(cbody(
        'ZP-H constructs four explicit <b>functors</b> — structure-preserving maps — from the '
        'abstract category C into the four concrete mathematical frameworks of the Zero '
        'Paradox: the lattice algebra of ZP-A, the p-adic topology of ZP-B, the information '
        'theory of ZP-C, and the Hilbert space of ZP-D.'))
    E.append(cbody(
        'The result is a verification that all four frameworks are, in a precise sense, '
        'realizations of the same abstract structure. They are not four separate arguments '
        'for the same conclusion — they are four different windows looking at one thing.'))
    E.append(four_functor_diagram())
    E.append(ccaption(
        'ZP-H constructs four functors from the abstract category C (center) into the four '
        'domain frameworks. Each functor F carries objects and morphisms faithfully, '
        'preserving the initial object and the forward-only structure.'))
    E.append(sp(6))

    # ── Morphisms of C ─────────────────────────────────────────────────────────
    E.append(Paragraph('What Are the Morphisms of C?', CS['h1']))
    E.append(cbody(
        'ZP-G defined C abstractly — objects, morphisms, composition, identity — without '
        'specifying what the morphisms actually <i>are</i>. That abstraction was intentional: '
        'the theorems in ZP-G hold for any category with AX-G1 and AX-G2, regardless of the '
        'morphism content.'))
    E.append(cbody(
        'ZP-H fills in the detail (Definition D-H1): morphisms in C are <b>state transitions</b>. '
        'A morphism f: A → B represents a net addition of informational content — you can '
        'only move forward. Morphisms compose by sequential accumulation: going from A to B '
        'then B to C produces a state at least as large as B. This design choice is what '
        'makes the four functors well-defined.'))
    E.append(remember_box(
        'D-H1 is a design commitment, not a derived result. A different choice of morphism '
        'structure would produce different functors. ZP-H states this explicitly: the choice '
        'is the one that maps correctly to all four domain frameworks, and it is not '
        'laundered as a derivation.'))
    E.append(sp(6))

    # ── The four functors ──────────────────────────────────────────────────────
    E.append(Paragraph('The Four Functors', CS['h1']))
    E.append(cbody(
        'Each functor takes the abstract objects and morphisms of C and maps them into '
        'one of the four frameworks, verifying that the mapping preserves composition, '
        'identity, and the privileged role of the initial object.'))
    E.append(cbody(
        '<b>FA (Lattice):</b> The initial object 0 maps to ⊥ (bottom of the lattice). '
        'Each morphism f: A → B maps to the join operation ⊥ ∨ S = S that witnesses the '
        'transition. Composition corresponds to iterated joins. The forward-only structure '
        'of C maps to the monotone structure of ZP-A.'))
    E.append(cbody(
        '<b>FB (p-Adic Topology):</b> The initial object 0 maps to the element 0 ∈ ℚ₂. '
        'Each morphism maps to a discrete jump across a clopen boundary. Composition '
        'corresponds to sequential jumps. The irreversibility of ZP-B C3 (no path returns '
        'to 0 in ℚ₂) is the topological realization of AX-G2.'))
    E.append(cbody(
        '<b>FC (Information Theory):</b> The initial object 0 maps to the Null State '
        'distribution P = (1, 0). Each morphism maps to an informational transition with '
        'a non-negative cost measured in bits. The fundamental transition costs exactly '
        '1 bit (ZP-C T1b). The informational singularity of ZP-G maps to the diverging '
        'surprisal of ZP-C T2.'))
    E.append(cbody(
        '<b>FD (Hilbert Space):</b> The initial object 0 maps to the basis vector e₀. '
        'Each morphism maps to an orthogonal extension — a step to a perpendicular basis '
        'vector. The Binary Snap becomes a right-angle turn in state space. The design '
        'commitment DP-1 (orthogonality represents topological isolation) is inherited here.'))

    E.append(example_box('Real-world analogy — Four instruments, one melody', [
        'Imagine the same musical phrase played on four different instruments: violin, '
        'trumpet, piano, and voice. Each sounds different, but any musician can hear that '
        'they are playing the same structure — the same intervals, the same rhythm. ZP-H '
        'shows that ZP-A through ZP-D are doing the same thing. They are four instruments '
        'playing one mathematical structure.',
    ]))
    E.append(sp(6))

    # ── T-H1: Universal property preserved ─────────────────────────────────────
    E.append(key_result_box('T-H1: Each Functor Preserves the Initial Object',
        'For each of the four functors, the image of 0 is an initial object in the target '
        'framework — a universal source from which every other object has a unique morphism. '
        'The privileged status of 0 is not an artifact of the abstract category: it is '
        'preserved faithfully in every concrete realization.'))
    E.append(sp(6))

    # ── T-H2: Singularity compatibility ────────────────────────────────────────
    E.append(Paragraph('Two Descriptions of One Obstruction', CS['h1']))
    E.append(cbody(
        'ZP-G said: there is no morphism from any non-initial object back to 0 (AX-G2). '
        'ZP-C said: the surprisal along any sequence approaching 0 diverges — the '
        'accumulated informational cost grows without bound. These look like two different '
        'statements about the same thing. Are they compatible?'))
    E.append(cbody(
        'T-H2 proves they are. The two characterizations are the same obstruction seen from '
        'different vantage points. In ZP-C, ask: what happens to surprisal as you approach '
        '0 along an infinite path? The answer is divergence. In ZP-G, ask: can you reach '
        '0 by a morphism from outside? The answer is no. '
        'If infinite cost is required to reach 0, then no finite morphism can accomplish '
        'it — which is exactly what "no morphism exists" means. Divergence and non-existence '
        'are two faces of the same fact.'))

    E.append(key_result_box('T-H2: Singularity Compatibility',
        'The categorical singularity (no return morphism to 0) and the information-theoretic '
        'singularity (diverging surprisal approaching 0) are two descriptions of the same '
        'structural fact. Under the functor FC, they correspond precisely.'))
    E.append(sp(6))

    # ── T-H3: The Binary Snap ──────────────────────────────────────────────────
    E.append(Paragraph('The Binary Snap Under All Four Functors', CS['h1']))
    E.append(cbody(
        'The Binary Snap is the transition from 0 to the first non-initial object. '
        'In the abstract category C, it is the unique morphism from 0 to ε₀ — guaranteed '
        'to exist by AX-G1 and to be unique by the definition of an initial object. '
        'In ZP-E, this transition was derived as a theorem (T-SNAP), not assumed as an axiom.'))
    E.append(cbody(
        'T-H3 shows that all four functors agree on what the Snap is:'))
    E.append(cbody(
        '• In lattice algebra: the first join — ⊥ ∨ ε₀ — producing the first non-bottom state.'
        '<br/>'
        '• In p-adic topology: a discrete jump from 0 to ε₀ across a clopen boundary, '
        'irreversible by the topological structure of ℚ₂.'
        '<br/>'
        '• In information theory: an informational transition costing exactly 1 bit — the '
        'minimum possible information cost for any state change.'
        '<br/>'
        '• In Hilbert space: an orthogonal shift from basis vector e₀ to e₁, with '
        'inner product ⟨e₀, e₁⟩ = 0.'))

    E.append(snap_convergence_diagram())
    E.append(ccaption(
        'All four frameworks describe the Binary Snap (T-SNAP) in their own language. '
        'The vertical line marks the moment of the Snap. '
        'Left: the null state. Right: the first non-null state.'))
    E.append(sp(6))

    E.append(key_result_box('T-H3: The Binary Snap Under All Four Functors',
        'The four functor images of the Binary Snap are mutually consistent: each framework '
        'independently establishes that the transition is irreversible, costs something '
        '(informational work, topological separation, orthogonal displacement), and is '
        'the minimal first step. T-SNAP is a derived theorem inherited here from ZP-E. '
        'The only design premise is DP-1 (ZP-D).'))
    E.append(sp(8))

    E.append(cbody(
        '<b>What this means:</b> The Binary Snap is not a construct of any one framework. '
        'It is a structural fact that survives translation into four independent mathematical '
        'languages. ZP-H is the document that verifies this translation is faithful.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
