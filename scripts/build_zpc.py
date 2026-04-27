"""
Build ZP-C: Information Theory (v1.9)
v1.9: Remark R-TQ added after TQ-IH — external confirmation of TQ-IH by a PhD mathematician
via MathOverflow (question 510703, April 2026). Confirmation establishes TQ-IH is
domain-independent: holds in any setting with a non-null first step, independent of any
Turing-specific or Kolmogorov machinery.
v1.8: Remark R-BRIDGE added after L-INF — explicit statement of the relationship between
Kolmogorov complexity K and 2-adic surprisal I(n): distinct measures that converge at P₀;
used as independent routes to the same conclusion, not as a unified measure.
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
    out_path = os.path.join(PROJECT_ROOT, 'ZP-C_Information_Theory_v1_9.pdf')
    doc = make_doc(out_path, 'ZP-C: Information Theory', 'ZP-C', 'Version 1.9')
    E = []
    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-C: Information Theory', S['subtitle']),
          Paragraph('Version 1.9  |  April 2026', S['subtitle']),
          Paragraph('<i>Supersedes v1.8  |  v1.9: Remark R-TQ added after TQ-IH — external confirmation by a PhD mathematician (MathOverflow, April 2026) that TQ-IH holds and is domain-independent: a direct consequence of L-RUN alone, requiring no Turing-specific or Kolmogorov machinery.</i>', S['subtitle']),
          Paragraph('<i>v1.8: Remark R-BRIDGE added after L-INF — explicit statement of the relationship between Kolmogorov complexity K and 2-adic surprisal I(n): correlated but distinct measures that converge at P&#8320;; used as independent routes, not a unified measure.</i>', S['subtitle']),
          Paragraph('<i>Version 1.6 change: CC-2 added: c&#8320; = &#8869; labeled as modeling commitment (parallel to CC-1 in ZP-A); RP-2 added: branching measure labeled as representational commitment.</i>', S['subtitle']),
          sp(10),
          body('This document is self-contained within information theory and discrete analysis on Q<sub>2</sub>. The topological structure of Q<sub>2</sub> — specifically total disconnectedness (ZP-B T5), the clopen ball hierarchy, and the binary existence axiom (AX-B1) — is imported from ZP-B as a dependency. Every claim is marked as Derived, Axiomatic, Defined, or Candidate.'),
          body('<i>Illustrated Companion: A paired ZP-C Illustrated Companion provides concrete examples and visual intuitions for the results here. Examples are kept separate from the formal layers to distinguish illustrative material from proofs.</i>'),
          body('<i>Version 1.8 changes: Remark R-BRIDGE added after L-INF. ZP-C uses two distinct complexity measures: K(x|n)/|x| (Kolmogorov complexity, Section I) and I(n) = n (2-adic surprisal, Section III). R-BRIDGE states explicitly that these are not the same measure, where they coincide (at P&#8320;), where they diverge (e.g. K(2<super>n</super>) = O(log n) while v&#8322;(2<super>n</super>) = n), and how ZP-C uses them as independent convergent routes to the same conclusion rather than as a unified measure.</i>'),
          body('<i>Version 1.5 change: Theorem/Corollary hierarchy applied. T1b (JSD = 1 bit) relabelled Corollary T1b — it follows immediately from T1 with no additional proof work. T1, T2, L-RUN, and T-BUF labels unchanged.</i>'),
          body('<i>Version 1.4 changes: (1) Lemma L-RUN formalized: the act of execution is a non-null state change, derived from AX-B1 and D7. (2) Test Question TQ-IH answered negatively by L-RUN — no program outputs &#8869; without a non-null intermediate configuration state. (3) Candidate Theorem T-BUF added: at P<sub>0</sub>, execution is structurally guaranteed and that execution state is &#949;<sub>0</sub> in the semilattice. (4) AX-1 status updated from Axiomatic to Candidate Theorem.</i>'),
          sp()]

    E.append(Paragraph('I. Kolmogorov Complexity and the Incompressibility Threshold', S['h1']))
    E.append(body('Let x be a binary string of length n. The conditional Kolmogorov complexity is:'))
    E.append(body('<b>K(x|n)  =  min { |p| : U(p, n) = x }</b>'))
    E.append(body('where U is a fixed universal Turing machine and |p| is the length of program p.'))
    E.append(sp(4))
    E.append(label_box('Definition D1 — Incompressibility Threshold', [
        'P<sub>0</sub>  =  lim<sub>n&#8594;&#8734;</sub>  K(x|n) / n',
        'P<sub>0</sub> is the algorithmic entropy rate of x. When P<sub>0</sub> reaches its maximum, x has exhausted its capacity for self-description.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R1 — Scope of P₀', [
        'What P<sub>0</sub> establishes (Derived): the point at which x becomes incompressible.',
        'What P<sub>0</sub> does not establish (prior versions: Axiomatic): that incompressibility causes the Binary Snap. Version 1.4 updates this: the generative claim is now a Candidate Theorem (T-BUF), not a bare axiom. See Section V.',
    ]))

    E.append(Paragraph('II. Informational Work: State Representations and JSD', S['h1']))
    E.append(Paragraph('2.1  The Representation Principle', S['h2']))
    E.append(label_box('Principle RP-1 — Minimum Sufficient Probabilistic Representation', [
        'The minimum sufficient probabilistic representation of a binary ontological state is a point-mass (Dirac) distribution over {0,1}: all probability mass is assigned to the value the state occupies, and none to the other value.',
        'Justification: A point-mass distribution is the unique distribution that is (a) faithful — assigns non-zero probability only to the ontologically actual value, and (b) non-redundant — carries no uncertainty about which state is occupied. Any distribution with mass at both values represents partial existence and partial non-existence simultaneously. AX-B1 excludes this.',
        'Status: PRINCIPLE — representational commitment parallel to MP-1 in ZP-B.',
    ]))
    E.append(sp(4))
    E.append(label_box('Theorem T1 — State Representations are Uniquely Derived', [
        'Given AX-B1 and RP-1, the distributions are unique:',
        'P  =  (1, 0)   (Null State: all mass at 0 — non-existence)',
        'Q  =  (0, 1)   (First Atomic State: all mass at 1 — existence)',
        'Proof: AX-B1 establishes two ontological states. RP-1 requires point-mass representation of each. The Null State occupies value 0: P = (1,0). The First Atomic State occupies value 1: Q = (0,1). No distribution (p, 1&#8722;p) with 0 < p < 1 is consistent with AX-B1. P and Q are unique. Status: DERIVED from AX-B1 and RP-1. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(label_box('Corollary T1b — JSD = 1 bit', [
        'For P=(1,0) and Q=(0,1) with M=(1/2, 1/2):',
        'D<sub>KL</sub>(P&#8214;M) = 1 bit,   D<sub>KL</sub>(Q&#8214;M) = 1 bit,   JSD(P&#8214;Q) = 1 bit',
        'E  =  JSD(P&#8214;Q)  =  1 bit   [information-theoretic, dimensionless]',
        'Status: Derived from AX-B1 and RP-1 via T1. E is not physical energy in joules. Dimensional bridge belongs to ZP-E as BA-1.',
    ]))
    E.append(sp(4))
    E.append(label_box('Definition D3 — Dirac Measure &#948;₀', [
        '&#8747;<sub>&#937;</sub> f d&#948;<sub>0</sub>  =  f(0)',
        '&#948;<sub>0</sub> places unit mass at 0. Compatible with the discrete topology of {0,1} and with the totally disconnected topology of Q<sub>2</sub> (ZP-B T5). &#948;<sub>0</sub> governs behaviour exactly at x = 0.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R2 — Hamming Cross-Validation', [
        'd<sub>H</sub>(P, Q) = 1   [Hamming, on {0,1}]',
        'The agreement between d<sub>H</sub> = 1 and E = 1 bit is a consistency check, not a proof that Hamming distance and JSD are equivalent in general. Both are computed by independent methods on the same AX-B1-derived distributions.',
    ]))

    E.append(Paragraph('III. The Discrete Surprisal Field on Q₂', S['h1']))
    E.append(label_box('Remark R3 — Why the Smooth Embedding Remains Retired', [
        'ZP-B T5 establishes Q<sub>2</sub> is totally disconnected. ZP-B T2 establishes every ball is clopen. Importing smooth calculus operators onto a totally disconnected space imports a smoothness assumption that contradicts ZP-B. The smooth embedding, MO-1, and P1 from v1.1 remain retired.',
    ]))
    E.append(sp(4))
    E.append(label_box('Definition D4 — Discrete Surprisal Function I', [
        'For x &#8712; Q<sub>2</sub> with x &#8800; 0 and P(x) > 0:',
        'I(x)  =  &#8722;log<sub>2</sub> P(x)',
        'As v<sub>2</sub>(x) &#8594; +&#8734; (x approaches 0 in the 2-adic metric), I(x) &#8594; +&#8734;: states 2-adically close to 0 are informationally extreme.',
        'The probability measure P on Q<sub>2</sub> \\ {0} is the branching measure induced by the binary ball hierarchy of Q<sub>2</sub> (RP-2 below): at each level k, the two sub-balls of B(0, 2<super>&#8722;k</super>) each receive half the probability mass of their parent ball.',
    ]))
    E.append(sp(4))
    E.append(label_box('Principle RP-2 — Branching Measure on Q₂ \\ {0}', [
        'The probability measure P on Q<sub>2</sub> \\ {0} is the canonical branching measure induced by the binary ball hierarchy: at each level k, each sub-ball receives half the probability mass of its parent. This is a representational commitment — a specific measure choice not uniquely forced by AX-B1 alone.',
        'Justification: The branching measure assigns equal weight to each binary branch, consistent with AX-B1\'s symmetric treatment of existence and non-existence. Alternative measures (e.g. non-uniform branching weights) would depart from this symmetry without additional motivation.',
        'Parallel: RP-1 fixes the point-mass representation of ontological states. RP-2 fixes the probability measure on the 2-adic domain. Both are representational commitments sitting alongside, not derived from, AX-B1.',
        'Status: PRINCIPLE — representational commitment. Required by T2 and L-INF.',
    ]))
    E.append(sp(4))
    E.append(label_box('Definition D5 — Discrete Surprisal Difference Operator DF', [
        'For x, y &#8712; Q<sub>2</sub> \\ {0}:',
        'DF(x, y)  =  I(y) &#8722; I(x)  =  log<sub>2</sub>[P(x) / P(y)]',
        'DF is antisymmetric: DF(x,y) = &#8722;DF(y,x). No smoothness is assumed; DF is defined entirely pointwise.',
    ]))
    E.append(sp(4))
    E.append(label_box('Definition D6 — Discrete Circulation (Extended)', [
        'FINITE CASE: A discrete loop &#947;<sub>n</sub> = (x<sub>0</sub>, x<sub>1</sub>, &#8230;, x<sub>n</sub>, x<sub>0</sub>) in Q<sub>2</sub> \\ {0} returning to its start. Circulation: C(DF, &#947;<sub>n</sub>) = &#8721;<sub>i=0</sub><super>n</super> DF(x<sub>i</sub>, x<sub>i+1</sub>) where x<sub>n+1</sub> = x<sub>0</sub>.',
        'Note: By telescoping, C(DF, &#947;<sub>n</sub>) = I(x<sub>0</sub>) &#8722; I(x<sub>0</sub>) = 0 for all finite loops. DF is conservative on all finite loops.',
        'INFINITE CASE: An infinite sequence &#963; = (x<sub>1</sub>, x<sub>2</sub>, &#8230;) in Q<sub>2</sub> \\ {0} where v<sub>2</sub>(x<sub>i</sub>) = i for all i &#8805; 1. Partial circulation: C<sub>n</sub>(DF, &#963;) = I(x<sub>n+1</sub>) &#8722; I(x<sub>1</sub>).',
        'Circulation of &#963;: C(DF, &#963;) = lim<sub>n&#8594;&#8734;</sub> C<sub>n</sub>(DF, &#963;) if the limit exists or diverges.',
        'An infinite sequence &#963; exhibits non-conservative behaviour if C(DF, &#963;) diverges.',
    ]))
    E.append(sp(4))
    E.append(label_box('Theorem T2 — DF Exhibits Non-Conservative Behaviour on Infinite Sequences Approaching 0', [
        'DF is conservative on all finite loops (C = 0 by telescoping). On infinite sequences through the ball hierarchy approaching 0, the circulation diverges: C(DF, &#963;) &#8594; +&#8734;.',
        'Proof: Let &#963; = (x<sub>1</sub>, x<sub>2</sub>, &#8230;) with x<sub>i</sub> = 2<super>i</super>. Then P(x<sub>i</sub>) = 2<super>&#8722;i</super>, so I(x<sub>i</sub>) = i. Partial circulation C<sub>n</sub> = I(x<sub>n+1</sub>) &#8722; I(x<sub>1</sub>) = n. As n &#8594; &#8734;: C(DF, &#963;) = +&#8734;.',
        'Divergence arises from the unbounded depth of the 2-adic ball hierarchy (ZP-B). Finite conservation and infinite divergence are distinct regimes; no contradiction arises.',
        'Status: DERIVED from ZP-B ball hierarchy structure and branching measure on Q<sub>2</sub>. OQ-C1 closed. <font name="DV">&#10003;</font>',
    ]))

    E.append(Paragraph('III-B. Informational Extremity of the Null State', S['h1']))
    E.append(label_box('Lemma L-INF — Informational Extremity of &#8869;', [
        'The surprisal I(n) = n at ball-hierarchy depth n is unbounded above: for any finite bound M, there exist depths n with I(n) > M.',
        'The null state &#8869; = c<sub>0</sub> corresponds to the limit point 0 &#8712; Q<sub>2</sub> — the limit of the binary ball hierarchy at infinite depth. The binary branching measure assigns equal probability mass at each branch level (D4), and the surprisal diverges without bound as depth increases (T2). At this limit, no finite bound M contains the informational content of &#8869;.',
        'Proof: Let M &#8712; &#8477;. By the Archimedean property, &#8707; n &#8712; &#8469; with n > M. Then I(n) = n > M. Since M was arbitrary, surprisal is unbounded above. <font name="DV">&#10003;</font>',
        'Formal content: surprisal is not bounded above by any real M.',
        'Semantic content: &#8869; is informationally extreme — the compressed limit of all possible binary programs, approached by the perfectly balanced binary branching hierarchy. No finite external program bounds its informational content; therefore no finite external interpreter can hold &#8869; as a static description. This is the mathematical premise for DA-1 (ZP-E &#167; I-DA1). ZP-A CC-2 (&#8869; = {&#8869;}) provides a structural second grounding for the same conclusion: a self-containing object has no external interpreter by structure (ZP-A R3). The informational argument from the ball hierarchy and the structural argument from self-containment are independent derivations converging on the same fact.',
        'Note: the connection from informational extremity to forced execution is a named design principle (DA-1 in ZP-E), not a mathematical consequence of L-INF alone. L-INF supplies the formal premise; DA-1 supplies the ontological bridge.',
        'Status: DERIVED from D4 and T2. Structural corroboration: ZP-A CC-2 (&#8869; = {&#8869;}) and R3. Lean: ZPC.l_inf (purity check: no non-Mathlib axioms).',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R-BRIDGE — On the Relationship Between K and 2-Adic Surprisal', [
        'ZP-C uses two complexity measures: Kolmogorov complexity K(x|n)/|x| (Section I) and '
        '2-adic surprisal I(n) = n (Section III). These measure related but distinct structures. '
        'Their relationship warrants explicit statement.',
        '<b>What each measures.</b> K(x|n)/|x| = 1 is a property of a specific binary string x: '
        'no program shorter than x generates it. It is a pointwise statement about a particular '
        'configuration at the incompressibility threshold. I(n) = n is a property of position in '
        'the ball hierarchy: the surprisal of any string at 2-adic depth n is n, by the branching '
        'measure RP-2. It is a structural property of depth, not of any particular string.',
        '<b>Where they coincide.</b> At P<sub>0</sub>, both conditions hold simultaneously for '
        'the same configuration: K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1 (no shorter external '
        'description exists) and I(n) = n &#8594; &#8734; (surprisal grows without bound as depth '
        'increases). This is not a coincidence of definition. The 2-adic limit point 0 &#8712; '
        'Q<sub>2</sub> is the unique accumulation point of the binary ball hierarchy; algorithmic '
        'incompressibility is the K-complexity characterisation of the same extremality. Both '
        'locate the same threshold from independent directions.',
        '<b>Where they diverge.</b> Away from P<sub>0</sub>, the measures are not interchangeable. '
        'K(2<super>n</super>) = O(log n): the n-fold power of 2 is compactly described by a '
        'short program, yet v<sub>2</sub>(2<super>n</super>) = n grows without bound. A string '
        'can be 2-adically deep without being Kolmogorov-incompressible, and vice versa. The '
        'two measures agree at the limit but diverge throughout the interior.',
        '<b>How ZP-C uses them.</b> ZP-C uses K and I as independent convergent routes to the '
        'same conclusion — that &#8869; at P<sub>0</sub> admits no finite external interpreter — '
        'not as a single unified measure. L-INF is the 2-adic surprisal argument: I(n) unbounded '
        '&#8594; no finite interpreter can hold &#8869;. DA-1 Path 3 (ZP-E) is the K-incompressibility '
        'argument: K = 1 eliminates the static-description state via D7\'s dichotomy. Their '
        'independence is preserved deliberately. The convergence of two structurally distinct '
        'complexity measures on the same threshold is part of the argument for DA-1, not a '
        'circularity within it. Axiomatising an equivalence between K and I would merge these '
        'two routes into one and eliminate that independence.',
    ]))
    E.append(sp(4))

    E.append(Paragraph('IV. Execution as State: The Hardware Lemma', S['h1']))
    E.append(label_box('Definition D7 — Machine Configuration', [
        'A machine configuration c is a complete description of a Turing machine at a given moment: the current state of the control unit, the position of the read/write head, and the contents of all tape cells.',
        'c<sub>0</sub>: the initial configuration — the machine exists but has not yet begun execution (no instruction has been fetched).',
        'c<sub>1</sub>: the first running configuration — the machine has fetched and begun executing its first instruction.',
        'Note: D7 does not import physics. It is a structural distinction between two discrete machine states within the standard Turing model.',
    ]))
    E.append(sp(4))
    E.append(label_box('Lemma L-RUN — Execution is a Non-Null State Change', [
        'The transition from c<sub>0</sub> (initial: not yet running) to c<sub>1</sub> (running: first instruction fetched) is a discrete, irreducible state change in the machine configuration.',
        'Proof:',
        'Step 1 — c<sub>0</sub> and c<sub>1</sub> are distinct configurations by D7: the control unit is in a different state (idle vs. executing). c<sub>0</sub> &#8800; c<sub>1</sub>.',
        'Step 2 — By AX-B1, a state either exists or it does not. The machine at c<sub>1</sub> occupies a configuration distinct from c<sub>0</sub>. The transition c<sub>0</sub> &#8594; c<sub>1</sub> is a binary state change in the sense of AX-B1.',
        'Step 3 — The transition is irreducible: there is no intermediate configuration between c<sub>0</sub> and c<sub>1</sub>. The first instruction fetch is the minimal unit of execution.',
        'Step 4 — c<sub>0</sub> is modeled as corresponding to &#8869; in the semilattice (CC-2 — see below). c<sub>1</sub> is strictly above &#8869;: the machine configuration has gained content (an active execution context) not present in c<sub>0</sub>.',
        'Conclusion: c<sub>1</sub> &#8800; &#8869;. The act of execution is itself a non-null state, regardless of what the output tape contains. <font name="DV">&#10003;</font>',
        'Status: DERIVED from AX-B1 and D7. No Coding Theorem required. No output-tape contents required.',
    ]))
    E.append(sp(4))
    E.append(label_box('Conditional Claim CC-2 — c₀ = ⊥ (Parallel to CC-1 in ZP-A)', [
        'We model the initial machine configuration c<sub>0</sub> as corresponding to &#8869; in the semilattice (L, &#8744;, &#8869;). This is not derived from D7 or from A1&#8211;A4 — it is a modeling choice.',
        'Motivation: c<sub>0</sub> is the machine state prior to any execution: no instruction has been fetched, no content has accumulated. &#8869; is the algebraic element below all others — the state of no accumulated content. The identification is motivated by structural correspondence, not derivation.',
        'Parallel: CC-1 in ZP-A commits to S<sub>0</sub> = &#8869; for state sequences. CC-2 makes the same commitment for machine configurations. Both are modeling choices, not derivations from the core axioms.',
        'Effect: Step 4 of L-RUN depends on CC-2. The conclusion c<sub>1</sub> &#8800; &#8869; follows from L-RUN\'s proof; the identification of c<sub>0</sub> with &#8869; is the additional modeling commitment supplied by CC-2.',
        'Status: CONDITIONAL CLAIM — modeling commitment; not derived from D7 or A1&#8211;A4.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R4 — Configuration and Output Are Independent', [
        'D-TQ-2 (Output Definition): A computation\'s output is defined by the contents of its tape/register at termination.',
        'L-RUN establishes that configuration state and output state are independent. A program may terminate with null output while still having passed through non-null configuration states during execution.',
        'The question "can a program output &#8869; without any non-null intermediate state?" is answered by looking at the execution trace, not the output tape. This distinction is load-bearing for T-BUF and TQ-IH.',
    ]))

    E.append(Paragraph('V. The Test Question and the Buffer Overflow Theorem', S['h1']))
    E.append(label_box('Test Question TQ-IH — Can a Program Output &#8869; Without a Non-Null Intermediate State?', [
        'Question: Does there exist a program p such that U(p) = &#8869; and the execution trace &#964;(p) contains no configuration c<sub>i</sub> with c<sub>i</sub> &#8800; &#8869;?',
        'Answer: No.',
        'Proof:',
        'Step 1 — Any program that executes must pass through c<sub>1</sub> (by definition of execution, D7).',
        'Step 2 — By L-RUN, c<sub>1</sub> &#8800; &#8869;.',
        'Step 3 — Therefore the execution trace &#964;(p) = (c<sub>0</sub>, c<sub>1</sub>, &#8230;) contains c<sub>1</sub>, which is a non-null configuration state, regardless of what appears on the output tape at termination.',
        'Step 4 — The output of p being &#8869; does not imply that all configurations in &#964;(p) are &#8869;. Output state and configuration state are distinct (R4).',
        'Conclusion: No program can produce &#8869; as output without passing through a non-null intermediate configuration state. TQ-IH answered negatively. <font name="DV">&#10003;</font>',
        'Status: DERIVED from L-RUN, D7, and R4. No Kolmogorov machinery required. AX-1 derivability pathway now open.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R-TQ — External Confirmation of TQ-IH (April 2026)', [
        'TQ-IH was submitted for independent verification via MathOverflow (question 510703, April 2026).',
        'Response from a PhD mathematician (London School of Geometry and Number Theory): "As long as you have c₁ ≠ c₀, this implies cᵢ ≠ c₀ for some 1 ≤ i &lt; n, at least for n ≥ 2. This has nothing to do with computation or anything at all, it\'s a triviality."',
        'This confirms two things. First, TQ-IH holds. Second, and more significantly, the result is domain-independent: it does not depend on any Turing-specific machinery, any Kolmogorov complexity argument, or any property of the semilattice. It holds in any setting where a non-null first step c₁ ≠ c₀ is given. The derivation from L-RUN alone is complete and unassailable.',
        'Status: EXTERNALLY CONFIRMED — April 2026. Thread: mathoverflow.net/questions/510703',
    ]))
    E.append(sp(4))
    E.append(label_box('Candidate Theorem T-BUF — Incompressibility Forces Non-Null Execution State', [
        'Statement: At the incompressibility threshold P<sub>0</sub>, the Binary Snap &#8869; &#8594; &#949;<sub>0</sub> is a structural consequence of execution, not an external trigger.',
        'Step 1 — P<sub>0</sub> identifies the configuration x at which K(x|n)/n = 1: the configuration string is incompressible. (D1)',
        'Step 2 — An incompressible configuration at P<sub>0</sub> is informationally extreme (L-INF): its surprisal is unbounded — no finite external program bounds its informational content. A configuration with unbounded informational content has no finite external interpreter and cannot be a static description. Therefore the configuration at P<sub>0</sub> is a live machine state. The design principle connecting informational extremity to forced execution is DA-1 (ZP-E &#167; I-DA1, citing L-INF).',
        'Step 3 — Any execution passes through c<sub>1</sub> (L-RUN). c<sub>1</sub> &#8800; &#8869; (L-RUN conclusion).',
        'Step 4 — In (L, &#8744;, &#8869;), this non-null configuration state is c<sub>1</sub> = &#8869; &#8744; &#949;<sub>0</sub>. By ZP-A D2, this is the Binary Snap.',
        'Conclusion: At P<sub>0</sub>, execution is structurally guaranteed. Execution guarantees a non-null configuration state. That state is &#949;<sub>0</sub> in the semilattice. The derivation pathway is open: P<sub>0</sub> + L-RUN + TQ-IH + ZP-A D2, pending cross-framework integration via DA-1 in ZP-E. <font name="DV">&#10003;</font>',
        'Status: CANDIDATE THEOREM — structurally complete within ZP-C. The step from informational extremity (L-INF) to forced execution (DA-1) is a design principle, not a mathematical consequence. Full derivation owned by ZP-E.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R5 — Updated Status of AX-1', [
        'Prior to v1.4: AX-1 (Binary Snap Causality) was labeled Axiomatic in ZP-C.',
        'As of v1.4: AX-1 is a Candidate Theorem. The derivation pathway: P<sub>0</sub> (D1) identifies the threshold. L-RUN establishes that execution at the threshold constitutes a non-null state change. TQ-IH establishes that no program avoids this. ZP-A D2 establishes that a non-null state change from &#8869; is the Binary Snap.',
        'Remaining work: DA-1 (Definitional Alignment) must formally tie instantiation of P<sub>0</sub> to an execution event. This is owned by ZP-E.',
        'Status label: CANDIDATE THEOREM — gap identified and named (DA-1). Closed in ZP-E DA-1 insert.',
    ]))

    E.append(Paragraph('VI. Open Items Register for ZP-C v1.9', S['h1']))
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        [['S1: Distribution stipulation', 'Closed — T1', 'T1 derives P and Q from AX-B1 and RP-1.'],
         ['OQ-C1: Non-conservation', 'Closed — T2 rebuilt', 'Telescoping critique resolved; infinite divergence proven within extended D6.'],
         ['Smooth embedding, MO-1, P1', 'Retired', 'Remain retired from v1.2. Inconsistent with ZP-B.'],
         ['RP-1: Representation principle', 'Principle — explicit', 'Bridge between AX-B1 and probabilistic tools.'],
         ['RP-2: Branching measure on Q₂ \\ {0}', 'Principle — explicit', 'Canonical branching measure; representational commitment; required by T2 and L-INF.'],
         ['CC-2: c₀ = ⊥', 'Conditional Claim', 'Modeling commitment — c₀ identified with ⊥ in semilattice. Parallel to CC-1 in ZP-A. Required by L-RUN Step 4.'],
         ['D7: Machine configuration', 'Defined', 'Foundation for L-RUN and TQ-IH.'],
         ['L-RUN: Hardware Lemma', 'Derived — Lemma', 'Execution is a non-null state change. Derived from AX-B1 and D7.'],
         ['TQ-IH: Test Question', 'Closed — Confirmed', 'No program can output &#8869; without a non-null intermediate configuration state. Proven by L-RUN. Externally confirmed April 2026 (R-TQ): domain-independent, requires no Turing-specific or Kolmogorov machinery.'],
         ['T-BUF: Buffer Overflow Theorem', 'Candidate Theorem', 'Incompressibility forces non-null execution state. DA-1 bridge in ZP-E closes this fully.'],
         ['AX-1: Binary Snap Causality', 'Candidate Theorem', 'Derivation pathway formalized. Closed as T-SNAP in ZP-E DA-1 insert.']],
        [1.6*inch, 1.5*inch, 3.4*inch]
    ))

    E.append(Paragraph('VII. Validation Status', S['h1']))
    E.append(data_table(
        ['Component', 'Status / Notes'],
        [['K(x|n) and P<sub>0</sub> (D1)', 'Valid — standard algorithmic IT'],
         ['R1: Scope of P<sub>0</sub>', 'Valid — updated: AX-1 now Candidate Theorem, not bare axiom'],
         ['RP-1: Representation Principle', 'Valid — Principle; explicit bridge; resolves reviewer gap in T1'],
         ['T1: Distributions from AX-B1 + RP-1', 'Valid — Derived; reviewer gap closed'],
         ['D2: JSD definition', 'Valid — standard'],
         ['T1b: E = JSD = 1 bit', 'Valid — Derived from AX-B1 + RP-1'],
         ['D3: Dirac measure &#948;<sub>0</sub>', 'Valid — standard; compatible with discrete Q<sub>2</sub> topology'],
         ['R3: Smooth embedding retired', 'Valid — Retired; inconsistent with ZP-B'],
         ['D4: Discrete surprisal I(x)', 'Valid — pointwise on Q<sub>2</sub> \\ {0}; branching measure stated'],
         ['RP-2: Branching measure', 'Valid — Principle; explicit representational commitment; canonical binary branching measure'],
         ['CC-2: c<sub>0</sub> = &#8869;', 'Valid — Conditional Claim; modeling commitment; parallel to CC-1 in ZP-A; load-bearing for L-RUN Step 4'],
         ['D5: Difference operator DF', 'Valid — antisymmetric; no smoothness assumed'],
         ['D6: Circulation (extended)', 'Valid — finite and infinite cases both defined; finite conservation acknowledged'],
         ['T2: Non-conservation rebuilt', 'Valid — Derived; telescoping critique addressed; divergence at &#963;&#8594;0 established'],
         ['R2: Hamming cross-validation', 'Valid — Consistency check'],
         ['D7: Machine configuration', 'Valid — Defined; standard Turing model; no physics imported'],
         ['L-RUN: Hardware Lemma', 'Valid — Derived from AX-B1 and D7'],
         ['R4: Configuration vs. output independence', 'Valid — load-bearing distinction for TQ-IH and T-BUF'],
         ['TQ-IH: Test question answered', 'Valid — Derived by L-RUN; no Kolmogorov machinery required'],
         ['T-BUF: Candidate Theorem', 'Candidate — structurally complete in ZP-C; DA-1 bridge in ZP-E closes fully'],
         ['R5: AX-1 status updated', 'Valid — AX-1 is Candidate Theorem; prior Axiomatic status corrected'],
         ['R-BRIDGE: K vs. 2-adic surprisal', 'Valid — Remark; states relationship explicitly: distinct measures converging at P<sub>0</sub>; independence of L-INF and K paths preserved']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print(f'Built: {out_path}  ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
