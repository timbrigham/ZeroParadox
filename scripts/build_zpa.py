"""
Build ZP-A: Lattice Algebra (v1.5)
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
    import re
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
    out_path = os.path.join(PROJECT_ROOT, 'ZP-A_Lattice_Algebra_v1_5.pdf')
    doc = make_doc(out_path, 'ZP-A: Lattice Algebra', 'ZP-A', 'Version 1.5')
    E = []

    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-A: Lattice Algebra', S['subtitle']),
          Paragraph('Version 1.5  |  April 2026', S['subtitle']),
          Paragraph('<i>Supersedes v1.4  |  Theorem/Proposition/Lemma hierarchy applied; R2 terminology note; CC-1 corollary clarified</i>', S['subtitle']),
          sp(10),
          body('This document is self-contained within abstract algebra. No topology, probability, or Hilbert space is imported. Every claim is provable using only the tools of semilattice theory. Cross-framework connections are deferred to ZP-E.'),
          body('<i>Illustrated Companion: A paired ZP-A Illustrated Companion document provides concrete examples and visual intuitions for the results in this document. Examples are kept separate from the formal layers to distinguish illustrative material from proofs. The companion is a reading aid; no proof-critical judgements should be drawn from examples alone.</i>'),
          body('<i>Version 1.5 changes: (1) Theorem/Proposition/Lemma hierarchy applied throughout: T1 relabelled Proposition (partial order properties are infrastructure), T2 relabelled Lemma (the global minimum result is a stepping stone for CC-1 and T3). T3 retains Theorem (monotonicity is the primary result of ZP-A). (2) Remark R2 added after D3 connecting the term "state sequence" to the standard order-theory term "ascending chain". (3) CC-1 corollary reworded to make explicit that T2 gives &#8869; &#8804; S&#8320; for any initialisation; CC-1 strengthens this to equality.</i>'),
          body('<i>Version 1.4 change: OQ-A1 section heading and box label corrected from "Open Question" to "CLOSED". The resolution was already recorded in the status line (closed by ZP-E T5 via AX-B1) but the section header was misleading. Status line expanded to answer both sub-questions explicitly.</i>'),
          body('<i>Version 1.3 changes: (1) Definition D2: the equivalence statement now makes explicit that &#945; depends on x — "for each x &#8712; L, f(x) = x &#8744; &#945; for some &#945; &#8712; L". (2) Theorem T3 proof: replaced the single spelled-out "iff" with &#10234; for consistency. (3) CC-1: removed circular conditional framing; reframed as a direct modelling commitment; corrected the consequence chain to S&#8320; = &#8869; &#8804; S&#8321; &#8804; &#8230;; replaced informal "constituent" with direct T2 reference.</i>'),
          body('<i>Version 1.2 changes: (1) Definition D1: the notation :&#10234; (non-standard) replaced by the standard definitional framing "define the relation &#8804; by". (2) Definition D2: the equivalence between x &#8804; f(x) and f(x) = x &#8744; &#945; is now accompanied by an explicit two-line proof of both directions.</i>'),
          body('<i>Version 1.1 change: Theorem T4 reclassified as Conditional Claim CC-1. The v1.0 label "Theorem" was imprecise: the result holds only given the assumption that the state sequence is initialised at the minimum of L. This assumption is not derived from A1&#8211;A4 — it is a modelling commitment.</i>'),
          sp()]

    E.append(Paragraph('I. Primitives and Axioms', S['h1']))
    E.append(Paragraph('1.1  Signature', S['h2']))
    E.append(body('The algebraic signature of the Zero Paradox state space is a triple: <b>(L, &#8744;, &#8869;)</b>'))
    E.append(body('L is a non-empty set (the carrier set of states). &#8744;&nbsp;:&nbsp;L&nbsp;&#215;&nbsp;L&nbsp;&#8594;&nbsp;L is a binary operation called <i>join</i>. &#8869; &#8712; L is a distinguished constant called the <i>bottom element</i>.'))
    E.append(sp(4))
    E.append(label_box('Axiom Block A — Join-Semilattice with Bottom', [
        'A1 — Associativity:   (x &#8744; y) &#8744; z = x &#8744; (y &#8744; z)   for all x, y, z &#8712; L',
        'A2 — Commutativity:  x &#8744; y = y &#8744; x   for all x, y &#8712; L',
        'A3 — Idempotency:    x &#8744; x = x   for all x &#8712; L',
        'A4 — Identity (Additive):   &#8869; &#8744; x = x   for all x &#8712; L',
    ]))
    E.append(sp(4))
    E.append(body('<b>A4 is the load-bearing axiom.</b> It makes &#8869; the additive identity of the algebra: the element that contributes nothing to a join and is therefore present in every state as the neutral constituent.'))

    E.append(Paragraph('II. The Induced Partial Order', S['h1']))
    E.append(Paragraph('2.1  Definition of &#8804;', S['h2']))
    E.append(label_box('Definition D1 — Lattice Order', [
        'For x, y &#8712; L, define the relation &#8804; by:',
        'x &#8804; y   &#10234;   x &#8744; y = y',
    ]))
    E.append(sp(4))
    E.append(label_box('Proposition T1 — &#8804; is a Partial Order', [
        'Reflexivity: x &#8804; x — by A3, x &#8744; x = x. <font name="DV">&#10003;</font>',
        'Antisymmetry: if x &#8804; y and y &#8804; x, then x &#8744; y = y and y &#8744; x = x. By A2, y = x &#8744; y = y &#8744; x = x. <font name="DV">&#10003;</font>',
        'Transitivity: if x &#8804; y and y &#8804; z, then x &#8744; z = x &#8744; (y &#8744; z) = (x &#8744; y) &#8744; z = y &#8744; z = z, so x &#8804; z. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(Paragraph('2.2  &#8869; is the Least Element', S['h2']))
    E.append(label_box('Lemma T2 — &#8869; is a Global Minimum under &#8804;', [
        'For all x &#8712; L:   &#8869; &#8804; x',
        'Proof: By A4, &#8869; &#8744; x = x. By D1, this is the definition of &#8869; &#8804; x. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(body('T2 is the algebraic statement of the foundational claim: &#8869; is not a void that states depart from — it is the minimum element that every state sits above. Since &#8869; &#8804; x for all x, and join accumulates from the bottom, &#8869; is algebraically present in every element of L.'))

    E.append(Paragraph('III. The Additive Ontology', S['h1']))
    E.append(Paragraph('3.1  No Subtraction Operator', S['h2']))
    E.append(label_box('Remark R1 — Join-Semilattice vs. Lattice', [
        'A full lattice (L, &#8744;, &#8743;, &#8869;, &#8868;) includes a meet operator &#8743; and a top element &#8868;. The Zero Paradox restricts to the join-semilattice with bottom. The meet operator is excluded because it would allow state reduction — the removal of informational content from a state. The additive ontology requires that no operation decreases informational content.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.2  Join is the Only State Transition', S['h2']))
    E.append(label_box('Definition D2 — State Transition', [
        'A state transition is any function f: L &#8594; L such that x &#8804; f(x) for all x &#8712; L.',
        'Equivalently, for each x &#8712; L, f(x) = x &#8744; &#945; for some &#945; &#8712; L.',
        'Proof of equivalence:',
        '(&#8658;) If x &#8804; f(x), then x &#8744; f(x) = f(x) by D1. Take &#945; = f(x): then f(x) = x &#8744; &#945;. <font name="DV">&#10003;</font>',
        '(&#8656;) If f(x) = x &#8744; &#945; for some &#945; &#8712; L, then x &#8744; f(x) = x &#8744; (x &#8744; &#945;) = (x &#8744; x) &#8744; &#945; = x &#8744; &#945; = f(x) by A1, A3. By D1, x &#8804; f(x). <font name="DV">&#10003;</font>',
    ]))

    E.append(Paragraph('IV. Monotonicity of State Sequences', S['h1']))
    E.append(Paragraph('4.1  State Sequences', S['h2']))
    E.append(label_box('Definition D3 — State Sequence', [
        'A state sequence is a function S: &#8469; &#8594; L, written (S<sub>0</sub>, S<sub>1</sub>, S<sub>2</sub>, &#8230;), such that:',
        'S<sub>n+1</sub> = S<sub>n</sub> &#8744; &#945;<sub>n</sub>   for some &#945;<sub>n</sub> &#8712; L, for all n &#8712; &#8469;',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R2 — Terminology: State Sequence and Ascending Chain', [
        'In the order-theory literature, a sequence (S<sub>n</sub>) satisfying S<sub>n</sub> &#8804; S<sub>n+1</sub> for all n is called an <i>ascending chain</i>. The term "state sequence" is used here in place of "ascending chain" to align with the state-transition framing of ZP-D and ZP-E, where the same structure is introduced as sequences of system states. The two terms denote the same mathematical object. Readers familiar with order theory should read "state sequence" as "ascending chain". For concrete illustrations, see the ZP-A Illustrated Companion.',
    ]))
    E.append(sp(4))
    E.append(label_box('Theorem T3 — State Sequences are Monotone', [
        'For any state sequence (S<sub>n</sub>) satisfying D3:   S<sub>n</sub> &#8804; S<sub>n+1</sub>   for all n &#8712; &#8469;',
        'Proof: By D3, S<sub>n+1</sub> = S<sub>n</sub> &#8744; &#945;<sub>n</sub>. By D1, S<sub>n</sub> &#8804; S<sub>n</sub> &#8744; &#945;<sub>n</sub> &#10234; S<sub>n</sub> &#8744; (S<sub>n</sub> &#8744; &#945;<sub>n</sub>) = S<sub>n</sub> &#8744; &#945;<sub>n</sub>. By A1, (S<sub>n</sub> &#8744; S<sub>n</sub>) &#8744; &#945;<sub>n</sub> = S<sub>n</sub> &#8744; &#945;<sub>n</sub>. By A3, S<sub>n</sub> &#8744; S<sub>n</sub> = S<sub>n</sub>. Therefore S<sub>n</sub> &#8744; &#945;<sub>n</sub> = S<sub>n+1</sub>. <font name="DV">&#10003;</font>',
        'Monotonicity is a theorem, not a postulate. It is derived from A1&#8211;A3 via D3.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('4.2  The Initial State', S['h2']))
    E.append(label_box('Conditional Claim CC-1 — S₀ = &#8869; (Reclassified from T4 in v1.0)', [
        'We commit to initialising every state sequence at the minimum of L: S<sub>0</sub> = &#8869;. This is not derived from A1&#8211;A4 — it is a modelling choice.',
        'Under CC-1 and T3:   S<sub>0</sub> = &#8869; &#8804; S<sub>1</sub> &#8804; S<sub>2</sub> &#8804; &#8230;',
        'Note: By T2, &#8869; &#8804; S<sub>0</sub> for any initialisation — this holds unconditionally from A4. CC-1 strengthens this to equality: S<sub>0</sub> = &#8869;. The commitment is not needed to establish &#8869; &#8804; S<sub>0</sub>; it is needed to fix the starting point precisely.',
        'Status: CONDITIONAL CLAIM — modelling commitment; not derived from A1&#8211;A4.',
    ]))

    E.append(Paragraph('V. OQ-A1 — Sufficiency of Monotonicity', S['h1']))
    E.append(label_box('OQ-A1 — Sufficiency of Monotonicity  [CLOSED — ZP-E T5]', [
        'Is the monotonicity constraint (T3) sufficient to characterise all valid state sequences, or are additional axioms required?',
        'OQ-A1a: Is there algebraic reason to restrict &#945;<sub>n</sub> to join-irreducible elements (not expressible as joins of strictly smaller elements)?',
        'OQ-A1b: Does the open-ended semilattice (without top element &#8868;) permit unbounded ascending chains?',
        'Status: CLOSED — Both sub-questions resolved by ZP-E Theorem T5 (Iterative Forcing Theorem) via AX-B1 from ZP-B. OQ-A1a: &#945;<sub>n</sub> = &#949;(S<sub>n</sub>), the minimum viable deviation. OQ-A1b: AX-B1\'s binary constraint bounds ascending chains.',
    ]))

    E.append(Paragraph('VI. Boundary Conditions', S['h1']))
    E.append(data_table(
        ['Export', 'Status / Receiving Document'],
        [['(L, &#8744;, &#8869;) as join-semilattice', 'Derived (A1&#8211;A4) — ZP-D: algebraic structure of state space'],
         ['&#8804; partial order (D1, T1)', 'Derived — ZP-D: ordering on states'],
         ['Monotonicity of state sequences (T3)', 'Derived from A1&#8211;A3 — ZP-D: state layer ordering'],
         ['&#8869; as global minimum (T2, CC-1)', 'Derived / Conditional — ZP-E: ontological grounding claim'],
         ['No subtraction / additive ontology (R1)', 'Structural — ZP-C: no operation may reduce informational content'],
         ['OQ-A1 — increment selection', 'Open within ZP-A; closed by ZP-E T5']],
        [2.5*inch, 4.0*inch]
    ))

    E.append(Paragraph('VII. Validation Status', S['h1']))
    E.append(data_table(
        ['Component', 'Status / Notes'],
        [['A1&#8211;A4 join-semilattice axioms', 'Valid — Axioms; self-contained'],
         ['&#8804; partial order (D1, T1)', 'Valid — Derived from A1&#8211;A3'],
         ['&#8869; as least element (T2)', 'Valid — Derived from A4 and D1'],
         ['Additive ontology / no subtraction (R1)', 'Valid — Structural; signature restriction'],
         ['State transition as join (D2)', 'Valid — Defined; consistent with signature'],
         ['Monotonicity of state sequences (T3)', 'Valid — Derived from A1&#8211;A3 and D3'],
         ['CC-1: S<sub>0</sub> = &#8869;', 'Conditional Claim — modelling commitment; not derived from A1&#8211;A4'],
         ['OQ-A1: Sufficiency of monotonicity', 'Open within ZP-A; closed by ZP-E T5']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print(f'Built: {out_path}  ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
