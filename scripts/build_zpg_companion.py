"""
Build ZP-G Illustrated Companion (v1.2)
Standalone companion for ZP-G Category Theory only.
ZP-H gets its own companion (build_zph_companion.py).
Changes from v1.1: plain-language explanation of ⊥ = {⊥} connection added (R2).

Accessibility target: 2 years of college math (calculus, some linear algebra).
No prior category theory assumed.
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
PURPLE     = colors.HexColor('#5B2D8E')  # kept for category diagram nodes

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
        ('∘', '&#8728;'),
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

def category_diagram():
    """Diagram: objects as dots, morphisms as arrows, initial object 0."""
    dw, dh = TW, 2.0 * inch
    d = Drawing(dw, dh)

    # Positions for objects
    cx = dw / 2
    cy = dh / 2

    # Object 0 (initial) at left
    ox = cx - 160
    oy = cy

    # Objects A, B, C arranged in a triangle to the right
    ax = cx + 20;  ay = cy + 55
    bx = cx + 120; by = cy + 55
    cx2 = cx + 70; cy2 = cy - 30

    dot_r = 6

    # Draw arrows (morphisms) from 0 to A, B, C
    def arrow(x1, y1, x2, y2, col=PURPLE, label='', lx=0, ly=0):
        # shorten by dot_r on each end
        import math
        dx, dy = x2 - x1, y2 - y1
        L = math.sqrt(dx*dx + dy*dy)
        ux, uy = dx/L, dy/L
        sx, sy = x1 + ux*dot_r, y1 + uy*dot_r
        ex, ey = x2 - ux*(dot_r+4), y2 - uy*(dot_r+4)
        d.add(Line(sx, sy, ex, ey, strokeColor=col, strokeWidth=1.5))
        # arrowhead
        perp_x, perp_y = -uy, ux
        d.add(Polygon([ex, ey,
                       ex - ux*8 + perp_x*4, ey - uy*8 + perp_y*4,
                       ex - ux*8 - perp_x*4, ey - uy*8 - perp_y*4],
                      fillColor=col, strokeColor=col, strokeWidth=0))
        if label:
            d.add(String(lx, ly, label, fontSize=8, fontName='DV-I', fillColor=col))

    arrow(ox, oy, ax, ay, label='i', lx=ox+18, ly=oy+22)
    arrow(ox, oy, bx, by, label='i', lx=ox+68, ly=oy+26)
    arrow(ox, oy, cx2, cy2, label='i', lx=ox+42, ly=oy-10)
    # Arrows between A, B, C (non-initial morphisms)
    arrow(ax, ay, bx, by, col=colors.HexColor('#888888'), label='f', lx=(ax+bx)/2, ly=ay+5)
    arrow(ax, ay, cx2, cy2, col=colors.HexColor('#888888'))
    arrow(bx, by, cx2, cy2, col=colors.HexColor('#888888'))

    # Dots for objects
    d.add(Circle(ox, oy, dot_r, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(Circle(ax, ay, dot_r, fillColor=PURPLE, strokeColor=PURPLE, strokeWidth=0))
    d.add(Circle(bx, by, dot_r, fillColor=PURPLE, strokeColor=PURPLE, strokeWidth=0))
    d.add(Circle(cx2, cy2, dot_r, fillColor=PURPLE, strokeColor=PURPLE, strokeWidth=0))

    # Labels
    d.add(String(ox - 12, oy - 20, '0', fontSize=10, fontName='DV-B', fillColor=COMP_AMBER))
    d.add(String(ox - 30, oy - 32, '(initial)', fontSize=7.5, fontName='DV-I',
                 fillColor=colors.HexColor('#888888')))
    d.add(String(ax - 4, ay + 12, 'A', fontSize=10, fontName='DV-B', fillColor=PURPLE))
    d.add(String(bx - 4, by + 12, 'B', fontSize=10, fontName='DV-B', fillColor=PURPLE))
    d.add(String(cx2 - 4, cy2 - 18, 'C', fontSize=10, fontName='DV-B', fillColor=PURPLE))

    # Title
    d.add(String(dw/2 - 155, dh - 14,
                 'A category: objects (dots), morphisms (arrows), one initial object 0',
                 fontSize=8.5, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    return d

def functor_diagram():
    """Diagram: two categories C and D with a functor F between them."""
    dw, dh = TW, 1.8 * inch
    d = Drawing(dw, dh)
    cy_mid = dh / 2

    # Category C (left box)
    lx1, ly1, lx2, ly2 = 20, 20, 180, dh - 20
    d.add(Rect(lx1, ly1, lx2 - lx1, ly2 - ly1,
               fillColor=colors.HexColor('#F5F0FC'), strokeColor=PURPLE, strokeWidth=1.2))
    d.add(String(lx1 + 10, ly2 - 18, 'C', fontSize=13, fontName='DV-B', fillColor=PURPLE))

    # Dots in C
    c0x, c0y = lx1 + 35, cy_mid + 18
    cax, cay = lx1 + 100, cy_mid + 30
    cbx, cby = lx1 + 130, cy_mid - 15
    dot_r = 5
    d.add(Circle(c0x, c0y, dot_r, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(Circle(cax, cay, dot_r, fillColor=PURPLE, strokeColor=PURPLE, strokeWidth=0))
    d.add(Circle(cbx, cby, dot_r, fillColor=PURPLE, strokeColor=PURPLE, strokeWidth=0))
    d.add(String(c0x - 12, c0y - 14, '0', fontSize=8, fontName='DV-B', fillColor=COMP_AMBER))
    d.add(String(cax + 4, cay + 4, 'A', fontSize=8, fontName='DV-B', fillColor=PURPLE))
    d.add(String(cbx + 4, cby - 12, 'B', fontSize=8, fontName='DV-B', fillColor=PURPLE))
    # Arrow 0->A in C
    d.add(Line(c0x + dot_r, c0y, cax - dot_r, cay, strokeColor=PURPLE, strokeWidth=1.2))
    d.add(Line(c0x + dot_r, c0y, cbx - dot_r, cby, strokeColor=PURPLE, strokeWidth=1.2))

    # Category D (right box)
    rx1, ry1, rx2, ry2 = dw - 200, 20, dw - 20, dh - 20
    d.add(Rect(rx1, ry1, rx2 - rx1, ry2 - ry1,
               fillColor=colors.HexColor('#EDF7ED'), strokeColor=colors.HexColor('#2E7D32'),
               strokeWidth=1.2))
    DGREEN = colors.HexColor('#2E7D32')
    d.add(String(rx1 + 10, ry2 - 18, 'D', fontSize=13, fontName='DV-B', fillColor=DGREEN))

    # Dots in D (F(0), F(A), F(B))
    d0x, d0y = rx1 + 35, cy_mid + 18
    dax, day = rx1 + 100, cy_mid + 30
    dbx, dby = rx1 + 130, cy_mid - 15
    d.add(Circle(d0x, d0y, dot_r, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(Circle(dax, day, dot_r, fillColor=DGREEN, strokeColor=DGREEN, strokeWidth=0))
    d.add(Circle(dbx, dby, dot_r, fillColor=DGREEN, strokeColor=DGREEN, strokeWidth=0))
    d.add(String(d0x - 20, d0y - 14, 'F(0)', fontSize=7.5, fontName='DV-B', fillColor=COMP_AMBER))
    d.add(String(dax + 4, day + 4, 'F(A)', fontSize=7.5, fontName='DV-B', fillColor=DGREEN))
    d.add(String(dbx + 4, dby - 12, 'F(B)', fontSize=7.5, fontName='DV-B', fillColor=DGREEN))
    d.add(Line(d0x + dot_r, d0y, dax - dot_r, day, strokeColor=DGREEN, strokeWidth=1.2))
    d.add(Line(d0x + dot_r, d0y, dbx - dot_r, dby, strokeColor=DGREEN, strokeWidth=1.2))

    # Big arrow F between the boxes
    fx1, fx2 = lx2 + 8, rx1 - 8
    fmy = cy_mid
    d.add(Line(fx1, fmy, fx2 - 10, fmy, strokeColor=BLACK, strokeWidth=2))
    d.add(Polygon([fx2, fmy, fx2 - 10, fmy + 5, fx2 - 10, fmy - 5],
                  fillColor=BLACK, strokeColor=BLACK, strokeWidth=0))
    d.add(String((fx1 + fx2) / 2 - 5, fmy + 7, 'F', fontSize=12, fontName='DV-B',
                 fillColor=BLACK))

    d.add(String(dw/2 - 155, dh - 14,
                 'Functor F: maps objects and arrows in C to objects and arrows in D',
                 fontSize=8.5, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    return d

def build():
    out_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                            'ZP-G_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-G Companion  |  Category Theory  |  April 2026  |  v1.2')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM,
                            title='ZP-G Illustrated Companion',
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
    hdr = Table([[Paragraph('ZP-G Illustrated Companion',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    E += [
        Paragraph('Structure without substance', CS['title']),
        Paragraph('Category Theory | Version 1.2', CS['subtitle']),
        Paragraph('ZP Companion | April 2026', CS['meta']),
        Paragraph(
            'This companion explains the ideas in plain language with diagrams and real-world '
            'examples. It is not the formal ontology — every claim here restates a result already '
            'proven in the corresponding technical document. Consult that document for the '
            'authoritative mathematics.',
            CS['disc']),
    ]

    # ── Background: What is a category? ────────────────────────────────────────
    E.append(Paragraph('Background: What Is a Category?', CS['h1']))
    E.append(cbody(
        'A <b>category</b> is one of the most general structures in mathematics. It has two '
        'ingredients: <b>objects</b> and <b>morphisms</b> (also called arrows).'))
    E.append(cbody(
        'The <b>objects</b> are the things in the category — dots on a diagram. They can be '
        'anything: numbers, sets, vector spaces, topological spaces, or the abstract states '
        'of the Zero Paradox.'))
    E.append(cbody(
        'The <b>morphisms</b> are the relationships between objects — arrows from one object '
        'to another. A morphism f from object A to object B is written f: A → B. The key '
        'rule is that morphisms compose: if f: A → B and g: B → C, then there is a combined '
        'morphism g ∘ f: A → C. There is also an identity morphism on every object — the '
        '"do nothing" arrow from any object to itself.'))
    E.append(cbody(
        'That is all a category is. No specific substance is required — just objects, arrows, '
        'composition, and identity. The power of the framework is that the same structural '
        'theorems apply to any category, regardless of what the objects actually are.'))

    E.append(example_box('Real-world example — A city road network', [
        'Objects = cities. Morphisms = one-way roads. Composition = connecting roads: if there '
        'is a road from Boston to New York and a road from New York to Chicago, there is a '
        'composed route from Boston to Chicago. The identity morphism is a city road that loops '
        'back to itself (a "stay where you are" option). Category theory studies what structures '
        'of roads are possible — without caring what the cities actually contain.',
    ]))
    E.append(sp(4))
    E.append(category_diagram())
    E.append(ccaption(
        'A small category with initial object 0 (amber) and objects A, B, C (purple). '
        'Purple arrows (i) are the unique morphisms from 0 to each object. Grey arrows '
        'are morphisms between non-initial objects. No arrow points back to 0.'))
    E.append(sp(6))

    # ── Background: What is a functor? ─────────────────────────────────────────
    E.append(Paragraph('Background: What Is a Functor?', CS['h1']))
    E.append(cbody(
        'A <b>functor</b> is a structure-preserving map between two categories. If C and D are '
        'categories, a functor F: C → D assigns to each object in C an object in D, and to '
        'each morphism in C a morphism in D — in a way that respects composition and identity.'))
    E.append(cbody(
        'The word "structure-preserving" is the key. If f: A → B in C, then F(f): F(A) → F(B) '
        'in D. If f and g compose to g ∘ f in C, then their images under F compose to '
        'F(g) ∘ F(f) in D. Functors are the "translations" between mathematical worlds — they '
        'carry structure faithfully from one setting to another.'))
    E.append(cbody(
        'ZP-H (the companion bridge document) constructs four functors from the abstract '
        'category C to the four concrete frameworks of the Zero Paradox — lattice algebra, '
        'p-adic topology, information theory, and Hilbert space. ZP-G builds the abstract '
        'category that those functors will target.'))

    E.append(example_box('Real-world example — Translation between languages', [
        'A functor is like a careful translator. Objects are words; morphisms are grammatical '
        'relationships. A good translator preserves structure: if "A causes B" in English, the '
        'translation into French should still express "A causes B," not scramble the causal '
        'relationship. Functors do the same for mathematical structure.',
    ]))
    E.append(sp(4))
    E.append(functor_diagram())
    E.append(ccaption(
        'Functor F: C → D maps objects (dots) and morphisms (arrows) from category C (left) '
        'to category D (right). The initial object 0 maps to F(0); object A maps to F(A); '
        'morphisms are preserved. Structure is carried faithfully across.'))
    E.append(sp(6))

    # ── What ZP-G is doing ─────────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-G Doing?', CS['h1']))
    E.append(cbody(
        'ZP-G constructs a single abstract category C whose structure captures everything '
        'essential about the Zero Paradox: there is a privileged starting point (the initial '
        'object), all structure flows forward from it, and no morphism ever returns to it. '
        'These properties are stated as two axioms within ZP-G — neither is a novel commitment. '
        'Both are grounded in structure established in prior layers.'))
    E.append(cbody(
        '<b>AX-G1 (Initial Object):</b> The category C has an initial object, called 0. '
        'An initial object is an object with exactly one morphism to every other object — a '
        'universal source. Every other object is "reachable" from 0 by exactly one route. '
        'This is not a new assumption: ⊥\'s existence as the bottom element of the ZP-A semilattice '
        'already guarantees it. ZP-G names it in categorical language.'))
    E.append(cbody(
        '<b>AX-G2 (Source Asymmetry):</b> No morphism points from any non-initial object '
        'back to 0. Once you leave the initial object, you cannot return. '
        'This is the categorical expression of irreversibility. '
        'Not a new assumption: it follows from antisymmetry of the ZP-A partial order '
        'and is independently confirmed by ZP-B C3 (topological irreversibility in ℚ₂).'))
    E.append(cbody(
        '<b>The connection to ⊥ = {⊥}:</b> ZP-A CC-2 characterizes the null state as a '
        '<i>Quine atom</i> — ⊥ = {⊥}, meaning ⊥ is its own only member. '
        'A self-containing object has no external interpreter: it IS its own interpretation. '
        'In categorical terms, this is exactly what AX-G1 and AX-G2 together express: '
        'nothing can reach inside 0 from outside (AX-G2), yet 0 constitutes every object '
        'in C through a unique outgoing morphism (T2). '
        'No external handle, present in everything — the categorical picture of self-containment.'))
    E.append(remember_box(
        'Remember: 0 here is not the number zero. It is a label for the initial object of the '
        'category — the privileged starting point from which all structure originates. '
        'The label was chosen because 0 plays the same role as ⊥ (bottom) in ZP-A, '
        '0 ∈ ℚ₂ in ZP-B, and the Null State in ZP-C.'))
    E.append(sp(6))

    # ── Key results ────────────────────────────────────────────────────────────
    E.append(Paragraph('Key Results', CS['h1']))
    E.append(key_result_box('T1: The Initial Object Is Unique',
        'There is exactly one initial object in C (up to a unique isomorphism — a "relabelling" '
        'that changes nothing structurally). No two distinct objects can each be a universal '
        'source.'))
    E.append(sp(6))
    E.append(key_result_box('T2: Universal Constituent',
        'For every object X in C, there exists a unique morphism from 0 to X. '
        'The initial object is a constituent of everything — every object has a unique '
        '"origin story" tracing back to 0.'))
    E.append(sp(6))
    E.append(key_result_box('T3: Unreachability',
        'No morphism from any non-initial object ever reaches 0. The initial object is '
        'unreachable from outside. This is the categorical expression of AX-G2.'))
    E.append(sp(6))
    E.append(key_result_box('T4: Chains Are Forward-Only',
        'No chain of morphisms starting from a non-initial object returns to 0. '
        'Forward movement is the only possibility. The structure of C is strictly directed.'))
    E.append(sp(6))

    # ── Surprisal and the informational singularity ────────────────────────────
    E.append(Paragraph('The Informational Singularity', CS['h1']))
    E.append(cbody(
        'ZP-G also introduces a notion of <b>surprisal</b> for morphisms. Informally: '
        'a morphism from a common object to a rare object is surprising; a morphism from '
        'a rare object to a common one is less so. The surprisal of a morphism f: A → B '
        'measures how much informational content the transition from A to B carries.'))
    E.append(cbody(
        'The initial object 0 has a special status: outward surprisal (from 0 to anything) '
        'grows without bound as we consider more and more objects in C. But inward surprisal '
        '(from anything to 0) is undefined — because no such morphism exists (T3). '
        'This asymmetry is the <b>informational singularity</b> of 0.'))
    E.append(cbody(
        'T6 formalizes this: the surprisal associated with leaving 0 accumulates with each '
        'step, and the morphisms pointing back to 0 are absent by AX-G2. 0 is a one-way '
        'source of informational content.'))

    E.append(key_result_box('T7: The Categorical Zero Paradox',
        'The initial object 0 is simultaneously the universal constituent of C (every object '
        'has a unique morphism from 0) and informationally unreachable (no morphism returns to '
        '0 from outside). Presence without return — the categorical statement of the Zero '
        'Paradox. This closing theorem of ZP-G shows that the paradox is not an artifact of '
        'any one mathematical framework but a structural property of any category satisfying '
        'AX-G1 and AX-G2.'))
    E.append(sp(8))

    E.append(cbody(
        '<b>What comes next:</b> ZP-H (the Categorical Bridge) constructs four concrete '
        'functors from C to the four domain frameworks of the Zero Paradox, verifying that '
        'the abstract categorical structure is faithfully realized in lattice algebra, '
        'p-adic topology, information theory, and Hilbert space. See the ZP-H Illustrated '
        'Companion for that story.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
