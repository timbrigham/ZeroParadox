"""
Build ZP-C Illustrated Companion (v1.6)
v1.6: CC-2 and RP-2 added — c0 = bottom labeled as modeling commitment (CC-2, parallel to CC-1
      in ZP-A); branching measure labeled as representational commitment (RP-2). Plain-language
      explanations of both added to companion.
v1.5: L-INF section added — plain-language explanation of Informational Extremity of bottom;
      key result box updated to reflect T-SNAP as proven theorem (not merely Candidate).
v1.4: closing key result box replaced technical labels (TQ-IH, ZP-A D2) with
      plain-language descriptions for general readers.
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
    replacements = [
        ('⊥', '&#8869;'), ('∨', '&#8744;'), ('≤', '&#8804;'), ('≥', '&#8805;'),
        ('≠', '&#8800;'), ('∈', '&#8712;'), ('→', '&#8594;'), ('←', '&#8592;'),
        ('∞', '&#8734;'), ('∑', '&#8721;'), ('⟨', '&#10216;'), ('⟩', '&#10217;'),
        ('—', '&#8212;'), ('–', '&#8211;'), ('×', '&#215;'), ('−', '&#8722;'),
        ('ε', '&#949;'), ('ℚ', '&#8474;'), ('ℂ', '&#8450;'), ('ℝ', '&#8477;'),
    ]
    for char, entity in replacements:
        text = text.replace(char, entity)
    return text

def cbody(text):
    return Paragraph(fix(text), CS['body'])

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

def surprisal_graph():
    """I(x) → ∞ as x → 0 curve."""
    dw, dh = TW, 2.2 * inch
    d = Drawing(dw, dh)
    margin_l, margin_b = 60, 40
    plot_w = dw - margin_l - 30
    plot_h = dh - margin_b - 30

    # Axes
    ax = margin_l; ay = margin_b
    d.add(Line(ax, ay, ax, ay + plot_h, strokeColor=BLACK, strokeWidth=1.2))
    d.add(Line(ax, ay, ax + plot_w, ay, strokeColor=BLACK, strokeWidth=1.2))

    # Axis labels — use raw unicode in String(); HTML entities are NOT parsed here
    d.add(String(ax - 42, ay + plot_h / 2, 'I(x)', fontSize=9, fontName='DV-B',
                 fillColor=BLACK))
    d.add(String(ax + plot_w + 5, ay - 4, 'x (state)', fontSize=8, fontName='DV',
                 fillColor=BLACK))
    # '∞' (U+221E) is in DejaVuSans
    d.add(String(ax - 10, ay + plot_h + 2, '∞', fontSize=10, fontName='DV',
                 fillColor=colors.HexColor('#555555')))

    # Singularity marker at x=0
    sx = ax
    d.add(Line(sx, ay, sx, ay + plot_h - 5, strokeColor=COMP_AMBER,
               strokeWidth=1, strokeDashArray=[4, 3]))
    d.add(String(sx - 2, ay + plot_h + 2, 'singularity', fontSize=7,
                 fontName='DV-I', fillColor=COMP_AMBER))

    # Amber dot at origin
    d.add(Circle(sx, ay, 5, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))

    # Hyperbola-like curve
    pts = []
    steps = 60
    for i in range(steps + 1):
        t_frac = i / steps
        x_rel = 0.02 + t_frac * 0.98
        y_val = 1.0 / x_rel
        xp = ax + x_rel * plot_w
        yp = ay + min(y_val / 1.0 * plot_h * 0.45, plot_h - 8)
        pts.append((xp, yp))

    for i in range(len(pts) - 1):
        d.add(Line(pts[i][0], pts[i][1], pts[i+1][0], pts[i+1][1],
                   strokeColor=COMP_BLUE, strokeWidth=2))

    # Raw unicode → and ∞ work in String() with DV font
    d.add(String(ax + 8, ay + 6,
                 'As x approaches 0, surprisal I(x) → ∞.  Zero is infinitely surprising.',
                 fontSize=7.5, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    return d

def jsd_diagram():
    """Bar chart: P=(1,0) and Q=(0,1) with 1-bit arrow."""
    dw, dh = TW, 2.0 * inch
    d = Drawing(dw, dh)

    bar_w = 30
    base_y = 30
    max_h  = 90
    cx = dw / 2

    # P bars (left, amber)
    p_x = cx - 130
    # P(0)=1 bar
    d.add(Rect(p_x - bar_w/2, base_y, bar_w, max_h,
               fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(String(p_x - 14, base_y + max_h + 4, 'P(0)=1', fontSize=8,
                 fontName='DV-B', fillColor=COMP_AMBER))
    # P(1)=0 bar (thin line)
    d.add(Rect(p_x + bar_w, base_y, bar_w, 2,
               fillColor=colors.HexColor('#999999'), strokeColor=colors.HexColor('#999999'), strokeWidth=0))
    d.add(String(p_x + bar_w - 4, base_y - 12, 'P(1)=0', fontSize=8,
                 fontName='DV', fillColor=colors.HexColor('#888888')))
    d.add(String(p_x - 16, base_y - 22, 'P = (1,0)', fontSize=8,
                 fontName='DV-B', fillColor=BLACK))
    d.add(String(p_x - 14, base_y - 32, 'Null State', fontSize=7,
                 fontName='DVS-I', fillColor=colors.HexColor('#555555')))

    # Q bars (right, teal)
    q_x = cx + 100
    # Q(0)=0 bar
    d.add(Rect(q_x - bar_w/2, base_y, bar_w, 2,
               fillColor=colors.HexColor('#999999'), strokeColor=colors.HexColor('#999999'), strokeWidth=0))
    d.add(String(q_x - 16, base_y - 12, 'Q(0)=0', fontSize=8,
                 fontName='DV', fillColor=colors.HexColor('#888888')))
    # Q(1)=1 bar
    d.add(Rect(q_x + bar_w - bar_w/2, base_y, bar_w, max_h,
               fillColor=COMP_BLUE, strokeColor=COMP_BLUE, strokeWidth=0))
    d.add(String(q_x + bar_w - 14, base_y + max_h + 4, 'Q(1)=1', fontSize=8,
                 fontName='DV-B', fillColor=COMP_BLUE))
    d.add(String(q_x - 6, base_y - 22, 'Q = (0,1)', fontSize=8,
                 fontName='DV-B', fillColor=BLACK))
    d.add(String(q_x - 20, base_y - 32, 'First Atomic State', fontSize=7,
                 fontName='DVS-I', fillColor=colors.HexColor('#555555')))

    # Arrow + label
    ax1 = cx - 80
    ax2 = cx + 60
    ay  = base_y + max_h / 2 + 8
    d.add(Line(ax1, ay, ax2, ay, strokeColor=BLACK, strokeWidth=1.5))
    d.add(Line(ax2 - 7, ay - 4, ax2, ay, strokeColor=BLACK, strokeWidth=1.5))
    d.add(Line(ax2 - 7, ay + 4, ax2, ay, strokeColor=BLACK, strokeWidth=1.5))
    d.add(String(cx - 38, ay + 6, 'minimum possible', fontSize=7.5,
                 fontName='DVS-I', fillColor=colors.HexColor('#555555')))
    d.add(String(cx - 18, ay - 12, '1 bit', fontSize=10,
                 fontName='DV-B', fillColor=BLACK))
    d.add(String(cx - 26, ay - 22, '(JSD = 1 bit)', fontSize=7.5,
                 fontName='DVS-I', fillColor=colors.HexColor('#555555')))

    # Title above
    d.add(String(cx - 100, dh - 16,
                 'The Binary Snap: the minimum informational event (1 bit)',
                 fontSize=8.5, fontName='DVS-I', fillColor=colors.HexColor('#555555')))
    return d

def lrun_diagram():
    """c0 → c1 → ... → out execution trace.
    Note: unicode subscripts (₀₁) are missing from DejaVu fonts.
    We render 'c' then a manually-positioned smaller '0'/'1' to simulate subscripts.
    """
    dw, dh = TW, 1.5 * inch
    d = Drawing(dw, dh)
    cy = dh * 0.55
    r  = 22
    xs = [55, 170, 310, 430]
    # Plain labels for circle bodies; subscripts drawn separately below
    circle_letters = ['c', 'c', '...', 'out']
    circle_subs    = ['0', '1', '',    '']
    fills  = [COMP_AMBER, COMP_BLUE, colors.HexColor('#888888'), colors.HexColor('#555555')]

    # Title
    d.add(String(dw/2 - 80, dh - 16, 'Turning on IS a state (L-RUN)',
                 fontSize=9, fontName='DV-B', fillColor=COMP_BLUE))
    d.add(Line(dw/2 - 80, dh - 19, dw/2 + 80, dh - 19,
               strokeColor=COMP_BLUE, strokeWidth=0.5, strokeDashArray=[3,2]))

    for i, (x, ltr, sub, fc) in enumerate(zip(xs, circle_letters, circle_subs, fills)):
        d.add(Circle(x, cy, r, fillColor=fc, strokeColor=fc, strokeWidth=0))
        if sub:
            # 'c' then small subscript digit offset lower-right
            d.add(String(x - 10, cy - 3, ltr, fontSize=11, fontName='DV-B', fillColor=WHITE))
            d.add(String(x - 1,  cy - 10, sub, fontSize=7.5, fontName='DV-B', fillColor=WHITE))
        else:
            d.add(String(x - 10, cy - 5, ltr, fontSize=10, fontName='DV-B', fillColor=WHITE))
        if i < len(xs) - 1:
            x2 = xs[i+1]
            d.add(Line(x + r + 2, cy, x2 - r - 2, cy, strokeColor=COMP_BLUE, strokeWidth=2))
            d.add(Line(x2 - r - 9, cy - 4, x2 - r - 2, cy, strokeColor=COMP_BLUE, strokeWidth=2))
            d.add(Line(x2 - r - 9, cy + 4, x2 - r - 2, cy, strokeColor=COMP_BLUE, strokeWidth=2))

    # Sub-labels below circles — use raw unicode; ⊥ (U+22A5) is in DV-B
    d.add(String(xs[0] - 16, cy - r - 14, 'c', fontSize=8, fontName='DV-B', fillColor=COMP_AMBER))
    d.add(String(xs[0] - 8,  cy - r - 20, '0', fontSize=6, fontName='DV-B', fillColor=COMP_AMBER))
    d.add(String(xs[0] - 4,  cy - r - 14, ' = ⊥', fontSize=8, fontName='DV-B', fillColor=COMP_AMBER))
    d.add(String(xs[0] - 12, cy - r - 27, '(null)', fontSize=7.5,
                 fontName='DV-I', fillColor=colors.HexColor('#666666')))

    d.add(String(xs[1] - 16, cy - r - 14, 'c', fontSize=8, fontName='DV-B', fillColor=COMP_BLUE))
    d.add(String(xs[1] - 8,  cy - r - 20, '1', fontSize=6, fontName='DV-B', fillColor=COMP_BLUE))
    d.add(String(xs[1] - 4,  cy - r - 14, ' ≠ ⊥', fontSize=8, fontName='DV-B', fillColor=COMP_BLUE))
    d.add(String(xs[1] - 18, cy - r - 27, '(non-null!)', fontSize=7.5,
                 fontName='DV-I', fillColor=colors.HexColor('#666666')))

    # Vertical dashed line above c1 node
    d.add(Line(xs[1], cy + r + 2, xs[1], dh - 22,
               strokeColor=COMP_BLUE, strokeWidth=1, strokeDashArray=[4, 3]))
    return d

def build():
    out_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                            'ZP-C_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            f'Zero Paradox ZP-C Companion  |  Information Theory  |  April 2026  |  v1.6')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM,
                            title='ZP-C Illustrated Companion',
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
    hdr = Table([[Paragraph('ZP-C Illustrated Companion',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    E += [
        Paragraph('Why zero is an informational singularity', CS['title']),
        Paragraph('Information Theory | Version 1.6', CS['subtitle']),
        Paragraph('ZP Companion | April 2026', CS['meta']),
        Paragraph(
            'This companion explains the ideas in plain language with diagrams and real-world '
            'examples. It is not the formal ontology — every claim here restates a result already '
            'proven in the corresponding technical document. Consult that document for the '
            'authoritative mathematics.',
            CS['disc']),
    ]

    # ── Page 1 ─────────────────────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-C Doing?', CS['h1']))
    E.append(cbody(
        'ZP-C establishes the informational cost of the Binary Snap. It uses Kolmogorov '
        'complexity — a measure of how much information is needed to describe something — and '
        'shows that approaching zero requires unbounded informational content.'))
    E.append(cbody(
        'The key object is the incompressibility threshold P₀: the point at which a configuration '
        'string cannot be described by any shorter program. ZP-C operates in ℚ₂ (from ZP-B) — '
        'not smooth Euclidean space — because smooth calculus tools are not valid on a totally '
        'disconnected space.'))
    E.append(example_box('Real-world example — ZIP compression hitting a wall', [
        'Some files compress a lot; others barely at all. A file that cannot be compressed further '
        'has hit its incompressibility threshold. That\'s P₀: the point where there are no more '
        'shortcuts. The string must be described in full, every bit.',
    ]))
    E.append(sp(8))

    E.append(Paragraph('Surprisal: The Cost of a Transition', CS['h1']))
    E.append(cbody(
        'The surprisal of state x is I(x) = −log₂ P(x): how surprising it is to observe x. '
        'As x approaches 0, P(x) approaches 0, and I(x) approaches infinity. Zero is infinitely '
        'surprising — it cannot be reached by any path of finite informational cost.'))

    # ── Page 2 ─────────────────────────────────────────────────────────────────
    E.append(surprisal_graph())
    E.append(Paragraph(
        'Surprisal I(x) as x approaches 0 (amber singularity). Every path toward 0 accumulates '
        'unbounded informational cost.',
        CS['caption']))
    E.append(example_box('Real-world example — A perfectly random password', [
        'To describe a truly random password, you have to send every character — you can\'t '
        'summarize it. That\'s maximum surprisal: the information content equals the full length '
        'of the string. Zero in ℚ₂ is the limit of this — infinite depth, infinite surprisal.',
    ]))
    E.append(sp(10))

    E.append(Paragraph('Why the Singularity Forces Execution (L-INF)', CS['h1']))
    E.append(cbody(
        'The surprisal graph shows that I(x) goes to infinity as x approaches 0. ZP-C v1.5 '
        'makes this precise with Lemma L-INF (Informational Extremity of ⊥): at the '
        'incompressibility threshold P₀, the configuration\'s surprisal is not just very large — '
        'it is formally infinite. The branching measure assigns probability approaching zero to any '
        'specific configuration at P₀, so I(P₀) = ∞.'))
    E.append(cbody(
        'This matters because infinite surprisal means no finite external program can bound the '
        'informational content of the configuration. A static stored description always has finite '
        'content. So a configuration at P₀ cannot be a stored description — it must be something '
        'actively running. L-INF is the formal reason P₀ forces execution, and it is what connects '
        'the surprisal singularity to the L-RUN argument below.'))
    E.append(remember_box(
        'The branching measure — the way ZP-C assigns probabilities to states in D4 — is a '
        'representational commitment (RP-2 in ZP-C v1.6). It is well-motivated by the binary '
        'structure of AX-B1, but it is a choice, not a derivation. The framework labels it '
        'explicitly so readers know where a design decision is being made.'))
    E.append(example_box('Analogy — A file that cannot be described', [
        'A truly incompressible file has no pattern — every bit is essential, nothing can be '
        'summarized or shortened. At P₀, the configuration is like this file: no shorter '
        'description exists. The only way such a thing can "be present" is as something actively '
        'running — not a stored record waiting to be read.',
    ]))
    E.append(sp(8))

    E.append(Paragraph('The Binary Snap Costs Exactly 1 Bit', CS['h1']))
    E.append(cbody(
        'The Jensen-Shannon Divergence (JSD) between the Null State P = (1,0) and the First '
        'Atomic State Q = (0,1) is exactly 1 bit. These distributions are derived from AX-B1 — '
        'not assumed. The Snap is the minimum informational event possible.'))
    E.append(jsd_diagram())
    E.append(Paragraph(
        'P = (1,0): all probability on non-existence. Q = (0,1): all probability on existence. '
        'The informational distance is exactly 1 bit — the minimum possible transition.',
        CS['caption']))

    E.append(Paragraph('Turning On Is a State (L-RUN)', CS['h1']))
    E.append(cbody(
        'Can a program output the null state ⊥ without passing through any non-null intermediate '
        'state? The answer is no — because the act of turning on is itself a state.'))
    E.append(cbody(
        'Any program that executes must pass through a "first instruction fetched" configuration '
        '(c₁). That configuration is distinct from the not-yet-running state (c₀). By AX-B1 it is '
        'non-null. The output being null does not mean the intermediate states were null.'))
    E.append(remember_box(
        'The identification of c₀ with the null state ⊥ is a modeling commitment (CC-2 in '
        'ZP-C v1.6) — a choice made explicit in the formal document, parallel to CC-1 in ZP-A '
        '(which identifies the initial state S₀ with ⊥). It is not derived from the machine '
        'definition; it is chosen. Labeling it CC-2 keeps that choice visible.'))

    # ── Page 3 ─────────────────────────────────────────────────────────────────
    E.append(lrun_diagram())
    E.append(Paragraph(
        'L-RUN: the transition c₀ → c₁ is a non-null state change. Execution itself is a state '
        '— independent of output.',
        CS['caption']))

    E.append(example_box('Real-world example — Booting a computer', [
        'When you press the power button, the machine doesn\'t jump from "off" to "showing your '
        'desktop." It passes through BIOS, POST, bootloader, kernel — each a distinct non-null '
        'configuration state. Even if programmed to immediately wipe itself and show nothing, it '
        'still passed through those intermediate states.',
    ]))
    E.append(remember_box(
        'Remember: Computers illustrate the result. L-RUN applies to any Turing machine — '
        'the abstract mathematical model of computation. The conclusion is mathematical, not '
        'technological.'))
    E.append(sp(6))

    # ── v1.6: Named commitments section ────────────────────────────────────────
    E.append(Paragraph('New in v1.6: Two Named Commitments', CS['h1']))
    E.append(cbody(
        'ZP-C v1.6 adds explicit labels to two choices the framework makes. Labeling them is not '
        'a weakness — it is how the framework keeps track of what is proven versus what is chosen.'))
    E.append(cbody(
        'CC-2 (Modeling Commitment): The Turing machine initial configuration c₀ is identified '
        'with the null state ⊥. This is the same pattern as CC-1 in ZP-A, which identifies the '
        'initial state S₀ with ⊥. Neither identification is forced by the definitions — both are '
        'deliberate choices that make the multi-layer framework cohere.'))
    E.append(cbody(
        'RP-2 (Representational Commitment): The branching measure used to assign probabilities '
        'to states is a representational choice. It is the natural choice given a binary state '
        'space, but it is not the only valid option. Labeling it RP-2 makes the commitment '
        'visible to anyone evaluating the framework\'s assumptions.'))
    E.append(sp(6))

    # ── KEY RESULT BOX — revised for accessibility ─────────────────────────────
    # CHANGED: replaced internal labels "TQ-IH" and "ZP-A D2" with plain-language
    # descriptions so a general reader can follow the derivation chain without
    # consulting the formal documents.
    E.append(key_result_box(
        'Key Result: T-SNAP — The Binary Snap Is a Proven Theorem',
        'The derivation chain: the incompressibility threshold P₀ produces a configuration with '
        'infinite surprisal (L-INF). A configuration with infinite surprisal cannot be a static '
        'stored description — it must be a live computation (DA-1, ZP-E). Any live computation '
        'must execute a first instruction, and that execution is a non-null state (L-RUN). '
        'No Turing machine program can produce any output without passing through such a non-null '
        'intermediate state. And any non-null state change starting from ⊥ is precisely the '
        'Binary Snap (ZP-A D2). ZP-E closes the chain as Theorem T-SNAP. '
        'The Binary Snap is no longer assumed — it is derived.'
    ))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
