"""
Build ZP-B: p-Adic Topology (v1.4)
"""
import os, sys
sys.stdout.reconfigure(encoding='utf-8')
from reportlab.lib import colors
from reportlab.lib.pagesizes import LETTER
from reportlab.lib.units import inch
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer,
                                 Table, TableStyle, PageBreak, HRFlowable)
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FONT_DIR = os.path.join(PROJECT_ROOT, '.claude-local', 'fonts') + os.sep
pdfmetrics.registerFont(TTFont('DV',    FONT_DIR + 'DejaVuSans.ttf'))
pdfmetrics.registerFont(TTFont('DV-B',  FONT_DIR + 'DejaVuSans-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DV-I',  FONT_DIR + 'DejaVuSans-Oblique.ttf'))
pdfmetrics.registerFont(TTFont('DV-BI', FONT_DIR + 'DejaVuSans-BoldOblique.ttf'))
pdfmetrics.registerFont(TTFont('DVS',   FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-B', FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-I', FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-BI',FONT_DIR + 'STIXTwo-Math.ttf'))

BLUE      = colors.HexColor('#2E75B6')
BLUE_LITE = colors.HexColor('#D5E8F0')
GREY_LITE = colors.HexColor('#F5F5F5')
BLACK     = colors.black
WHITE     = colors.white
COMP_BLUE  = colors.HexColor('#4D89C0')
COMP_GREEN = colors.HexColor('#4D9050')
COMP_SLATE = colors.HexColor('#60727B')
COMP_AMBER = colors.HexColor('#BB8C26')
SLATE_LITE = colors.HexColor('#ECEFF1')
AMBER_LITE = colors.HexColor('#FFF8E7')

TW = 6.5 * inch
LM = RM = 1.0 * inch
TM = BM = 1.0 * inch

S = {
    'title':    ParagraphStyle('title',    fontName='DV-B',  fontSize=18, leading=24,
                               spaceAfter=6,  alignment=1),
    'subtitle': ParagraphStyle('subtitle', fontName='DV-I',  fontSize=11, leading=15,
                               spaceAfter=4,  alignment=1),
    'h1':       ParagraphStyle('h1',       fontName='DV-B',  fontSize=13, leading=18,
                               spaceBefore=14, spaceAfter=5, textColor=BLUE),
    'h2':       ParagraphStyle('h2',       fontName='DV-B',  fontSize=11, leading=15,
                               spaceBefore=10, spaceAfter=4, textColor=BLUE),
    'h3':       ParagraphStyle('h3',       fontName='DV-B',  fontSize=10, leading=14,
                               spaceBefore=8,  spaceAfter=3),
    'body':     ParagraphStyle('body',     fontName='DVS',   fontSize=10, leading=14,
                               spaceAfter=6),
    'bodyI':    ParagraphStyle('bodyI',    fontName='DVS-I', fontSize=10, leading=14,
                               spaceAfter=6),
    'label':    ParagraphStyle('label',    fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=WHITE),
    'cell':     ParagraphStyle('cell',     fontName='DVS',   fontSize=9,  leading=13),
    'cellB':    ParagraphStyle('cellB',    fontName='DVS-B', fontSize=9,  leading=13),
    'cellSans': ParagraphStyle('cellSans', fontName='DV',    fontSize=9,  leading=13),
    'cellI':    ParagraphStyle('cellI',    fontName='DVS-I', fontSize=9,  leading=13),
    'footer':   ParagraphStyle('footer',   fontName='DV-I',  fontSize=8,  leading=10,
                               textColor=colors.grey, alignment=1),
    'note':     ParagraphStyle('note',     fontName='DVS-I', fontSize=9,  leading=13,
                               spaceAfter=4),
}

def sp(n=6):
    return Spacer(1, n)

def chk():
    return '<font name="DV">&#10003;</font>'

def fix(text):
    sub_map = {'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4',
               '₅':'5','₆':'6','₇':'7','₈':'8','₉':'9',
               'ₙ':'n','ₖ':'k','ₘ':'m','ᵢ':'i','ⱼ':'j',
               '₊':'+','₋':'-'}
    sup_map = {'⁰':'0','¹':'1','²':'2','³':'3','⁴':'4',
               '⁵':'5','⁶':'6','⁷':'7','⁸':'8','⁹':'9',
               'ⁿ':'n','ᵏ':'k','∞':'&#8734;'}
    for ch, rep in sub_map.items():
        text = text.replace(ch, f'<sub>{rep}</sub>')
    for ch, rep in sup_map.items():
        text = text.replace(ch, f'<super>{rep}</super>')
    text = text.replace('✓', '<font name="DV">&#10003;</font>')
    text = text.replace('✗', '<font name="DV">&#10007;</font>')
    text = text.replace('∅', '<font name="DV">&#8709;</font>')
    replacements = [
        ('⊥', '&#8869;'), ('∨', '&#8744;'), ('∧', '&#8743;'),
        ('≤', '&#8804;'), ('≥', '&#8805;'), ('≠', '&#8800;'),
        ('∈', '&#8712;'), ('∉', '&#8713;'), ('⊆', '&#8838;'),
        ('∪', '&#8746;'), ('∩', '&#8745;'), ('∀', '&#8704;'),
        ('∃', '&#8707;'), ('∞', '&#8734;'), ('∑', '&#8721;'),
        ('→', '&#8594;'), ('←', '&#8592;'), ('↔', '&#8596;'),
        ('⇒', '&#8658;'), ('⟺', '&#10234;'), ('⟹', '&#10233;'),
        ('⟨', '&#10216;'), ('⟩', '&#10217;'), ('‖', '&#8214;'),
        ('—', '&#8212;'), ('–', '&#8211;'), ('·', '&#183;'),
        ('×', '&#215;'), ('−', '&#8722;'), ('≡', '&#8801;'),
        ('∘', '&#8728;'), ('⊗', '&#8855;'),
        ('ε', '&#949;'), ('α', '&#945;'), ('β', '&#946;'),
        ('γ', '&#947;'), ('δ', '&#948;'), ('η', '&#951;'),
        ('σ', '&#963;'), ('π', '&#960;'),
        ('Δ', '&#916;'), ('Σ', '&#931;'), ('Γ', '&#915;'),
        ('ℚ', '&#8474;'), ('ℤ', '&#8484;'), ('ℂ', '&#8450;'),
        ('ℕ', '&#8469;'), ('ℝ', '&#8477;'),
        ('∥', '&#8741;'), ('⊕', '&#8853;'),
    ]
    for char, entity in replacements:
        if char not in text:
            continue
        text = text.replace(char, entity)
    return text

def body(text, style='body'):
    return Paragraph(fix(text), S[style])

def label_box(title, rows_list):
    data = [[Paragraph(fix(title), S['label'])]]
    for r in rows_list:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',   (0,0), (-1,0),  BLUE),
        ('BACKGROUND',   (0,1), (-1,-1), GREY_LITE),
        ('TEXTCOLOR',    (0,0), (-1,0),  WHITE),
        ('BOX',          (0,0), (-1,-1), 0.5, BLUE),
        ('LINEBELOW',    (0,0), (-1,0),  0.5, BLUE),
        ('LINEBEFORE',   (0,0), (-1,-1), 0.5, colors.HexColor('#CCCCCC')),
        ('LINEAFTER',    (0,0), (-1,-1), 0.5, colors.HexColor('#CCCCCC')),
        ('LINEBELOW',    (0,1), (-1,-2), 0.5, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',   (0,0), (-1,-1), 5),
        ('BOTTOMPADDING',(0,0), (-1,-1), 5),
        ('LEFTPADDING',  (0,0), (-1,-1), 8),
        ('RIGHTPADDING', (0,0), (-1,-1), 8),
        ('VALIGN',       (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW], repeatRows=1)
    t.setStyle(ts)
    return t

def data_table(headers, rows_data, col_widths, header_bg=BLUE):
    hdr_row = [Paragraph(fix(h), S['label']) for h in headers]
    data = [hdr_row]
    for row in rows_data:
        data.append([Paragraph(fix(str(c)), S['cell']) for c in row])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  header_bg),
        ('BACKGROUND',    (0,1), (-1,-1), GREY_LITE),
        ('ROWBACKGROUNDS',(0,1), (-1,-1), [WHITE, GREY_LITE]),
        ('BOX',           (0,0), (-1,-1), 0.5, BLUE),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, BLUE),
        ('INNERGRID',     (0,1), (-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('LINEAFTER',     (0,0), (-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 4),
        ('BOTTOMPADDING', (0,0), (-1,-1), 4),
        ('LEFTPADDING',   (0,0), (-1,-1), 6),
        ('RIGHTPADDING',  (0,0), (-1,-1), 6),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=col_widths, repeatRows=1)
    t.setStyle(ts)
    return t

def make_doc(path, title_str, doc_id, version_str):
    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        footer_text = f"Zero Paradox {doc_id}  |  {version_str}  |  April 2026  |  Page {doc.page}"
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch, footer_text)
        canvas.restoreState()
    return SimpleDocTemplate(
        path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title=title_str, author="Zero Paradox Project",
        onFirstPage=footer_cb, onLaterPages=footer_cb,
    )


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-B_pAdic_Topology_v1_4.pdf')
    doc = make_doc(out_path, 'ZP-B: p-Adic Topology', 'ZP-B', 'Version 1.4')
    E = []
    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-B: p-Adic Topology', S['subtitle']),
          Paragraph('Version 1.4  |  April 2026', S['subtitle']),
          Paragraph('<i>Supersedes v1.3  |  T0 reframed: derived given MP-1 (design commitment); MP-1 acknowledged as load-bearing choice</i>', S['subtitle']),
          sp(10),
          body('This document is self-contained within p-adic analysis and topology. No abstract algebra from ZP-A, no probability, and no Hilbert space is imported. Cross-framework connections are deferred to ZP-D and ZP-E.'),
          body('<i>Illustrated Companion: A paired ZP-B Illustrated Companion provides concrete examples and visual intuitions for the results here. Examples are kept separate from the formal layers to distinguish illustrative material from proofs.</i>'),
          body('<i>Version 1.4 change: T0 status updated from "DERIVED from AX-B1 and MP-1" to "DERIVED given MP-1 (design commitment)". MP-1 is the load-bearing design choice; T0 is a valid derivation given MP-1. OQ-B1 closed given MP-1.</i>'),
          body('<i>Version 1.3 change: Theorem/Proposition hierarchy applied. T1 and T2 relabelled Proposition. T5 relabelled Proposition. T0 and T3 retain Theorem labels.</i>'),
          body('<i>Version 1.2 changes: T0 strengthened with MP-1; C2 fixed to derive from T2 only; T4 reclassified as C3 (corollary of T5).</i>'),
          sp()]

    E.append(Paragraph('I. The Foundational Distinction', S['h1']))
    E.append(Paragraph('1.1  The Binary Existence Axiom', S['h2']))
    E.append(label_box('Axiom AX-B1 — Binary Existence', [
        'The foundational distinction of the Zero Paradox framework is binary: a state either exists or it does not. There is no third option at this level.',
        '0 — non-existence (the Null State, corresponding to &#8869; in ZP-A)',
        '1 — existence (the First Atomic State, the minimal non-zero element)',
        'Status: AXIOM. This is the only non-topological commitment in ZP-B. It precedes p-adic analysis and is the premise from which the field selection is derived.',
        'Scope: AX-B1 asserts the structure of the ontological distinction, not its physical realisation. It is invariant across all instantiations.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('1.2  The Minimality Principle', S['h2']))
    E.append(label_box('Principle MP-1 — Minimality of Representation', [
        'The representational base of the framework must be the minimum base capable of encoding the ontological distinction of AX-B1 without redundancy and without information loss.',
        'Redundancy: a base p > minimum introduces representational states with no ontological counterpart, violating parsimony.',
        'Information loss: a base p < minimum cannot distinguish all ontologically distinct states, violating faithfulness.',
        'Status: PRINCIPLE — methodological commitment. Given AX-B1 (two ontological states) and MP-1 (minimum sufficient base), the representational base is uniquely determined as 2.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('1.3  Derivation of p = 2', S['h2']))
    E.append(label_box('Theorem T0 — p = 2 is the Unique Minimum Sufficient Representational Base', [
        'Given AX-B1 and MP-1, the p-adic field appropriate for the Zero Paradox framework is Q<sub>2</sub>.',
        'Note on MP-1: MP-1 is a design commitment — the choice to use the minimum sufficient base. '
        'Any Q<sub>p</sub> for prime p ≥ 2 contains elements 0 and 1 capable of representing the AX-B1 '
        'distinction; the choice of minimum base is what MP-1 encodes. T0 is a valid derivation '
        'from AX-B1 and MP-1, but MP-1 is the load-bearing design choice, not a mathematical necessity. '
        'OQ-B1 is closed given MP-1.',
        'Proof:',
        'Step 1 — AX-B1 establishes exactly two ontological states: non-existence (0) and existence (1).',
        'Step 2 — A p-adic field Q<sub>p</sub> uses coefficients from {0, 1, &#8230;, p&#8722;1}. The minimum base p capable of representing exactly two distinct values without redundancy is p = 2, with coefficient set {0, 1}. One coefficient per ontological state; no unused coefficients.',
        'Step 3 — p = 1 has only one coefficient value {0}. Cannot distinguish existence from non-existence. Fails faithfulness (MP-1).',
        'Step 4 — p > 2: coefficient set {0, &#8230;, p&#8722;1} contains values with no ontological counterpart. Violates no-redundancy condition of MP-1.',
        'Step 5 — p = 2 is the unique prime satisfying both conditions simultaneously.',
        'Step 6 — The binary branching at every level of Q<sub>2</sub>\'s ball structure reflects the eventual binary resolution of any representational complexity.',
        'Therefore p = 2. Status: DERIVED given MP-1 (design commitment). OQ-B1 closed. <font name="DV">&#10003;</font>',
    ]))

    E.append(Paragraph('II. The 2-Adic Field', S['h1']))
    E.append(Paragraph('2.1  The 2-Adic Absolute Value', S['h2']))
    E.append(body('Fix p = 2 (derived in T0). Every non-zero rational q &#8712; &#8474; can be written uniquely as q = 2<super>v</super> &#183; (a/b) where v &#8712; &#8484; and a, b are integers not divisible by 2. The integer v is the 2-adic valuation v<sub>2</sub>(q). By convention, v<sub>2</sub>(0) = +&#8734;.'))
    E.append(label_box('Definition D1 — 2-Adic Absolute Value', [
        'For q &#8712; &#8474;:   |q|<sub>2</sub>  =  2<super>&#8722;v<sub>2</sub>(q)</super>   for q &#8800; 0;   |0|<sub>2</sub>  =  0',
        'Elements with high powers of 2 are considered small under |&#183;|<sub>2</sub>. Elements with no factor of 2 have |&#183;|<sub>2</sub> = 1.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('2.2  The 2-Adic Field Q<sub>2</sub>', S['h2']))
    E.append(body('Q<sub>2</sub> is the completion of &#8474; under the metric induced by |&#183;|<sub>2</sub>. Elements of Q<sub>2</sub> are formal power series in 2: x = &#8721;<sub>n=v</sub><super>&#8734;</super> a<sub>n</sub> &#183; 2<super>n</super> where a<sub>n</sub> &#8712; {0,1}. The coefficients a<sub>n</sub> &#8712; {0,1} are precisely the binary values of AX-B1.'))
    E.append(sp(4))
    E.append(Paragraph('2.3  The Minimum Viable Deviation &#949;<sub>0</sub>', S['h2']))
    E.append(label_box('Definition D5 — Minimum Viable Deviation &#949;₀', [
        '&#949;<sub>0</sub> = 2<super>k</super> for some integer k, where k is the maximum valuation accessible in the instantiation.',
        'Structural role (universal): &#949;<sub>0</sub> is always the first element crossed by the Snap. Fixed by the structure of Q<sub>2</sub> and AX-B1.',
        'Numerical value (contingent): determined by physical constants of the instantiation. Planck-scale quantities in our universe.',
        'Status: DEFINED — universe-contingent parameter.',
    ]))

    E.append(Paragraph('III. The Ultrametric', S['h1']))
    E.append(label_box('Definition D2 — 2-Adic Metric', [
        'For x, y &#8712; Q<sub>2</sub>:   d(x, y)  =  |x &#8722; y|<sub>2</sub>',
    ]))
    E.append(sp(4))
    E.append(label_box('Proposition T1 — Strong Triangle Inequality (Ultrametric)', [
        'For all x, y, z &#8712; Q<sub>2</sub>:   d(x, z)  &#8804;  max( d(x, y),  d(y, z) )',
        'Proof: Write x &#8722; z = (x &#8722; y) + (y &#8722; z). The ultrametric property of v<sub>2</sub> gives v<sub>2</sub>(a+b) &#8805; min(v<sub>2</sub>(a), v<sub>2</sub>(b)), from which |a+b|<sub>2</sub> &#8804; max(|a|<sub>2</sub>, |b|<sub>2</sub>). Apply with a = x&#8722;y and b = y&#8722;z. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(label_box('Corollary C1 — All Triangles are Isosceles', [
        'If d(x,y) &#8800; d(y,z), then d(x,z) = max(d(x,y), d(y,z)).',
        'Proof: Suppose d(x,y) < d(y,z). By T1, d(x,z) &#8804; d(y,z). Also d(y,z) &#8804; max(d(y,x), d(x,z)) = d(x,z) since d(x,y) < d(y,z). Therefore d(x,z) = d(y,z). <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.2  Clopen Ball Structure', S['h2']))
    E.append(label_box('Definition D3 — Ball in Q₂', [
        'B(a, r)  =  { x &#8712; Q<sub>2</sub>  :  d(x, a) &#8804; r }   (closed ball)',
        'B&#176;(a, r)  =  { x &#8712; Q<sub>2</sub>  :  d(x, a) < r }   (open ball)',
    ]))
    E.append(sp(4))
    E.append(label_box('Proposition T2 — Every Ball is Clopen', [
        'In Q<sub>2</sub>, every closed ball is also open and every open ball is also closed.',
        'Proof (closed ball is open): Let y &#8712; B(a, r). For any z &#8712; B(y, r), T1 gives d(z, a) &#8804; max(d(z,y), d(y,a)) &#8804; r. So B(y,r) &#8838; B(a,r). Every point is an interior point. <font name="DV">&#10003;</font>',
        'Proof (open ball is closed): Let (x<sub>n</sub>) &#8594; x with all x<sub>n</sub> &#8712; B&#176;(a,r). Ball radii in Q<sub>2</sub> are discrete (powers of 2), so d(x,a) < r holds in the limit. Thus x &#8712; B&#176;(a,r). <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(label_box('Corollary C2 — Disjoint Balls Do Not Communicate  [v1.2: derived from T2 only]', [
        'If B(a, r) and B(b, r) are disjoint (d(a,b) > r), then no continuous path exists from any point in B(a, r) to any point in B(b, r).',
        'Proof: By T2, B(a, r) is clopen in Q<sub>2</sub>. Any continuous f: [0,1] &#8594; Q<sub>2</sub> with f(0) &#8712; B(a,r) and f(1) &#8712; B(b,r) would require f to map the connected set [0,1] onto a subset intersecting both B(a,r) and its clopen complement. The preimage of a clopen set under a continuous function is clopen in [0,1]. Since [0,1] is connected, the preimage is either empty or all of [0,1]. It cannot be all of [0,1] (since f(1) &#8713; B(a,r)) and cannot be empty (since f(0) &#8712; B(a,r)). Contradiction. <font name="DV">&#10003;</font>',
    ]))

    E.append(Paragraph('IV. Topological Isolation of Zero', S['h1']))
    E.append(label_box('Theorem T3 — Topological Isolation of 0', [
        'For any r = 2<super>&#8722;k</super>, the ball B(0,r) = { x &#8712; Q<sub>2</sub> : v<sub>2</sub>(x) &#8805; k }. Any x outside this ball has d(0,x) &#8805; 2<super>&#8722;k+1</super> > r. B(0,r) and its complement are separated by a gap of at least 2<super>&#8722;k</super>.',
        'The transition from 0 to any non-zero element is a discrete jump across a clopen boundary — the topological identity of the Snap.',
        'Relationship to &#949;<sub>0</sub>: &#949;<sub>0</sub> = 2<super>k</super> is the smallest non-zero element outside the tightest ball around 0. The Snap crosses exactly this gap. <font name="DV">&#10003;</font>',
    ]))

    E.append(Paragraph('V. Topological Structure of Q₂', S['h1']))
    E.append(Paragraph('5.1  Total Disconnectedness — proven before C3', S['h2']))
    E.append(label_box('Proposition T5 — Q₂ is Totally Disconnected', [
        'The only connected subsets of Q<sub>2</sub> are singletons.',
        'Proof: Let S &#8838; Q<sub>2</sub> contain two distinct points a, b with d(a,b) = r > 0. Choose s with 0 < s < r. By T2, B(a,s) is clopen. Then S = [S &#8745; B(a,s)] &#8746; [S \\ B(a,s)] is a separation of S into two disjoint non-empty clopen sets. Therefore S is not connected. Since S was arbitrary, the only connected subsets are singletons. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(Paragraph('5.2  Topological Irreversibility of the Snap', S['h2']))
    E.append(label_box('Definition D4 — Topological Irreversibility', [
        'A transition from a to b in a topological space X is topologically irreversible if there exists no continuous path &#947;: [0,1] &#8594; X with &#947;(0) = b and &#947;(1) = a.',
    ]))
    E.append(sp(4))
    E.append(label_box('Corollary C3 — The Snap is Topologically Irreversible  [reclassified from T4 in v1.1]', [
        'Let x &#8712; Q<sub>2</sub> with x &#8800; 0. There exists no continuous path &#947;: [0,1] &#8594; Q<sub>2</sub> with &#947;(0) = x and &#947;(1) = 0.',
        'Proof: By T5, Q<sub>2</sub> is totally disconnected. A continuous path &#947; with &#947;(0) = x &#8800; 0 and &#947;(1) = 0 would require &#947;([0,1]) to be a connected subset of Q<sub>2</sub> containing two distinct points. By T5, no such connected subset exists. <font name="DV">&#10003;</font>',
        'Derivation chain: T1 &#8594; T2 &#8594; T5 &#8594; C3. Reclassified from Theorem T4: this result is a corollary of T5, not an independent theorem.',
    ]))

    E.append(Paragraph('VI. Universal Structure vs. Contingent Parameters', S['h1']))
    E.append(label_box('Remark R1 — Universal Structure vs. Universe-Contingent Parameters', [
        'Universal (invariant across all instantiations): AX-B1 (binary distinction — logical, not physical). MP-1 (methodological commitment). T0 (p=2 derived). T1, T2, T3, T5, C1, C2, C3 (all topological results). Structural role of &#949;<sub>0</sub>.',
        'Universe-contingent (varies across instantiations): Numerical value of &#949;<sub>0</sub> (determined by physical constants). Physical predictions invoking &#949;<sub>0</sub> numerically.',
        'Consequence: The Zero Paradox is a universal ontology of state emergence, not a physical theory of our universe specifically.',
    ]))

    E.append(Paragraph('VII. Boundary Conditions for ZP-D and ZP-E', S['h1']))
    E.append(data_table(
        ['Export', 'Status', 'Receiving Document'],
        [['AX-B1', 'Axiom', 'ZP-E: foundational axiom'],
         ['MP-1', 'Principle', 'ZP-E: bridge between ontological and representational binary'],
         ['T0: p = 2', 'Derived from AX-B1 + MP-1', 'ZP-D: domain of T is Q<sub>2</sub>'],
         ['Q<sub>2</sub> with 2-adic metric (D1, D2)', 'Defined', 'ZP-D: topological domain of T'],
         ['T1: Ultrametric', 'Derived', 'ZP-D: non-Archimedean structure'],
         ['T2: Clopen balls', 'Derived', 'ZP-D: topological isolation maps to orthogonality in H'],
         ['T3: Topological isolation of 0', 'Derived', 'ZP-E: grounds ontological claim about the Snap'],
         ['T5: Total disconnectedness', 'Derived', 'ZP-E: supports C3'],
         ['C3: Snap topologically irreversible', 'Derived — Corollary of T5', 'ZP-E: cross-framework irreversibility'],
         ['&#949;<sub>0</sub> (D5)', 'Defined — contingent', 'ZP-E: Snap threshold; value depends on instantiation'],
         ['R1: Universal vs. contingent', 'Remark', 'ZP-E: framework is instantiation-independent']],
        [1.6*inch, 1.8*inch, 3.1*inch]
    ))

    E.append(Paragraph('VIII. Validation Status', S['h1']))
    E.append(data_table(
        ['Component', 'Status / Notes'],
        [['AX-B1', 'Axiom — explicit; load-bearing premise'],
         ['MP-1', 'Principle — explicit bridge; resolves reviewer gap in T0'],
         ['T0: p = 2', 'Valid — Derived given MP-1 (design commitment). MP-1 encodes the minimality choice; T0 follows. OQ-B1 closed.'],
         ['D1: 2-adic absolute value', 'Valid — standard definition'],
         ['D2: 2-adic metric', 'Valid — follows from D1'],
         ['T1: Strong triangle inequality', 'Valid — Derived'],
         ['C1: All triangles isosceles', 'Valid — Corollary of T1'],
         ['T2: Every ball is clopen', 'Valid — Derived from T1'],
         ['C2: Disjoint balls do not communicate', 'Valid — Derived from T2 only; forward citation to T5 removed'],
         ['T3: Topological isolation of 0', 'Valid — Derived from D1 and D2'],
         ['T5: Q<sub>2</sub> totally disconnected', 'Valid — Derived from T2; proven before C3'],
         ['C3: Snap topologically irreversible', 'Valid — Corollary of T5; reclassified from Theorem T4'],
         ['D5: &#949;<sub>0</sub>', 'Valid — Defined; structural role universal; value contingent'],
         ['R1', 'Valid — Remark; ontological scope clarified']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print(f'Built: {out_path}  ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
