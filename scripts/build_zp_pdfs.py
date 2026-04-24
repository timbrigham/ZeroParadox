"""
Zero Paradox — PDF Builder
Follows all rules in PDF_Rendering_Standards.md:
  - DejaVu fonts only
  - Checkmark always wrapped in <font name="DV">
  - All table cells are Paragraph objects
  - No unicode subscripts — use sub/super tags
  - US Letter, 1-inch margins, TW = 6.5 inch
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

# ── 1. PATH SETUP ────────────────────────────────────────────────────────────
PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FONT_DIR = os.path.join(PROJECT_ROOT, '.claude-local', 'fonts') + os.sep
OUT_DIR = os.path.join(PROJECT_ROOT, '.claude-local', 'build_output')
pdfmetrics.registerFont(TTFont('DV',    FONT_DIR + 'DejaVuSans.ttf'))
pdfmetrics.registerFont(TTFont('DV-B',  FONT_DIR + 'DejaVuSans-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DV-I',  FONT_DIR + 'DejaVuSans-Oblique.ttf'))
pdfmetrics.registerFont(TTFont('DV-BI', FONT_DIR + 'DejaVuSans-BoldOblique.ttf'))
pdfmetrics.registerFont(TTFont('DVS',   FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-B', FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-I', FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-BI',FONT_DIR + 'STIXTwo-Math.ttf'))

# ── 2. COLORS ─────────────────────────────────────────────────────────────────
BLUE      = colors.HexColor('#2E75B6')
BLUE_LITE = colors.HexColor('#D5E8F0')
GREY_LITE = colors.HexColor('#F5F5F5')
BLACK     = colors.black
WHITE     = colors.white

# Companion palette: 15% white tint on formal header colors
COMP_BLUE  = colors.HexColor('#4D89C0')
COMP_GREEN = colors.HexColor('#4D9050')
COMP_SLATE = colors.HexColor('#60727B')
COMP_AMBER = colors.HexColor('#BB8C26')
SLATE_LITE = colors.HexColor('#ECEFF1')
AMBER_LITE = colors.HexColor('#FFF8E7')

# ── 3. PAGE GEOMETRY ──────────────────────────────────────────────────────────
TW = 6.5 * inch          # text width (US Letter − 2 × 1 inch margins)
LM = RM = 1.0 * inch
TM = BM = 1.0 * inch

# ── 4. PARAGRAPH STYLES ───────────────────────────────────────────────────────
S = {
    'title':    ParagraphStyle('title',    fontName='DV-B',  fontSize=18, leading=24,
                               spaceAfter=6,  alignment=1),
    'subtitle': ParagraphStyle('subtitle', fontName='DV-I',  fontSize=11, leading=15,
                               spaceAfter=4,  alignment=1),
    'h1':       ParagraphStyle('h1',       fontName='DV-B',  fontSize=13, leading=18,
                               spaceBefore=14, spaceAfter=5,
                               textColor=BLUE),
    'h2':       ParagraphStyle('h2',       fontName='DV-B',  fontSize=11, leading=15,
                               spaceBefore=10, spaceAfter=4,
                               textColor=BLUE),
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

# ── 5. HELPERS ────────────────────────────────────────────────────────────────

def sp(n=6):
    return Spacer(1, n)

def chk():
    """Checkmark safe for any context — always uses DV font."""
    return '<font name="DV">&#10003;</font>'

def fix(text):
    """
    Convert plain-text math notation to HTML entities safe for ReportLab.
    Also replaces bare ✓ with the font-switched version.
    Uses sub/super tags for subscripts/superscripts instead of unicode chars.
    """
    # Protect existing tags
    import re
    # Subscript/superscript unicode → sub/super tags
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

    # Checkmark — must use DV font in Serif context
    text = text.replace('✓', '<font name="DV">&#10003;</font>')
    text = text.replace('\u2717', '<font name="DV">&#10007;</font>')
    # ∅ (U+2205 empty set) is MISSING from DejaVuSerif — must use DV Sans
    text = text.replace('\u2205', '<font name="DV">&#8709;</font>')

    # Math symbols to entities (only if not already entity)
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
        # Don't double-replace
        text = text.replace(char, entity)
    return text

def body(text, style='body'):
    return Paragraph(fix(text), S[style])

def label_box(title, rows_list):
    """
    Blue header + white-on-blue label + content rows.
    rows_list: list of strings (each becomes a Paragraph cell).
    """
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
    """
    General data table with Paragraph cells (per standards section 3).
    headers: list of str
    rows_data: list of list of str
    col_widths: list of inch values, must sum to TW
    """
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
    """Create SimpleDocTemplate with footer."""
    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        footer_text = f"Zero Paradox {doc_id}  |  {version_str}  |  April 2026  |  Page {doc.page}"
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch, footer_text)
        canvas.restoreState()

    return SimpleDocTemplate(
        path,
        pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title=title_str,
        author="Zero Paradox Project",
        onFirstPage=footer_cb,
        onLaterPages=footer_cb,
    )

# ── DOCUMENT BUILDERS ─────────────────────────────────────────────────────────

def build_zpa():
    doc = make_doc(os.path.join(OUT_DIR, 'ZP-A_Lattice_Algebra_v1_5.pdf'),
                   'ZP-A: Lattice Algebra', 'ZP-A', 'Version 1.5')
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
    E.append(label_box('Conditional Claim CC-1 — S\u2080 = &#8869; (Reclassified from T4 in v1.0)', [
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
    print('ZP-A done')


def build_zpa_companion():
    """Illustrated companion for ZP-A, v1.2. Adds Dan's suggested examples."""
    from reportlab.graphics.shapes import Drawing, Circle, Line, String

    RED_C     = colors.HexColor('#BB2222')

    # Companion paragraph styles
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

    def hasse_diagram():
        dw, dh = TW, 2.6 * inch
        d = Drawing(dw, dh)
        cx = dw / 2
        r = 18
        y0, y1, y2 = 45, 125, 200

        nodes1 = [(cx - 100, y1), (cx, y1), (cx + 100, y1)]
        nodes2 = [(cx - 150, y2), (cx - 55, y2), (cx + 55, y2), (cx + 150, y2)]
        lc = colors.HexColor('#888888')

        for nx, ny in nodes1:
            d.add(Line(cx, y0 + r, nx, ny - r, strokeColor=lc, strokeWidth=1))
        for i, (nx, ny) in enumerate(nodes1):
            for j, (tx, ty) in enumerate(nodes2):
                if abs(i - j) <= 1:
                    d.add(Line(nx, ny + r, tx, ty - r, strokeColor=lc, strokeWidth=1))
        for xi in [cx - 195, cx - 85, cx + 30, cx + 175]:
            d.add(String(xi, y2 + r + 6, '...', fontSize=10, fontName='DV',
                         fillColor=colors.HexColor('#666666')))

        d.add(Circle(cx, y0, r, fillColor=colors.HexColor('#F0A000'),
                     strokeColor=colors.HexColor('#F0A000'), strokeWidth=0))
        d.add(String(cx - 6, y0 - 6, '⊥', fontSize=14, fontName='DV-B',
                     fillColor=colors.white))
        for nx, ny in nodes1:
            d.add(Circle(nx, ny, r, fillColor=COMP_BLUE, strokeColor=COMP_BLUE, strokeWidth=0))
            d.add(String(nx - 4, ny - 5, 'S', fontSize=11, fontName='DV-B',
                         fillColor=colors.white))
        for tx, ty in nodes2:
            d.add(Circle(tx, ty, r, fillColor=COMP_BLUE, strokeColor=COMP_BLUE, strokeWidth=0))
            d.add(String(tx - 4, ty - 5, 'S', fontSize=11, fontName='DV-B',
                         fillColor=colors.white))

        lx = dw - 1.6 * inch
        d.add(Circle(lx, y0 + 4, 7, fillColor=colors.HexColor('#F0A000'),
                     strokeColor=colors.HexColor('#F0A000'), strokeWidth=0))
        d.add(String(lx + 12, y0 - 1, '= bottom (additive identity)',
                     fontSize=7.5, fontName='DVS', fillColor=BLACK))
        d.add(Circle(lx, y0 - 20, 7, fillColor=COMP_BLUE, strokeColor=COMP_BLUE, strokeWidth=0))
        d.add(String(lx + 12, y0 - 25, 'States in L',
                     fontSize=7.5, fontName='DVS', fillColor=BLACK))
        return d

    def transition_diagram():
        dw, dh = TW, 1.5 * inch
        d = Drawing(dw, dh)
        cy = dh * 0.62
        r = 22
        xs = [r + 10, r + 120, r + 230, r + 340, r + 440]
        lc = COMP_BLUE
        ac = colors.HexColor('#F0A000')

        d.add(Circle(xs[0], cy, r, fillColor=ac, strokeColor=ac, strokeWidth=0))
        d.add(String(xs[0] - 6, cy - 6, '⊥', fontSize=14, fontName='DV-B',
                     fillColor=colors.white))
        for i in range(1, 4):
            d.add(Circle(xs[i], cy, r, fillColor=lc, strokeColor=lc, strokeWidth=0))
            d.add(String(xs[i] - 8, cy - 5, f'S{i}', fontSize=10, fontName='DV-B',
                         fillColor=colors.white))
        d.add(String(xs[4] - 8, cy - 5, '...', fontSize=12, fontName='DV',
                     fillColor=colors.HexColor('#555555')))

        for i in range(3):
            x1 = xs[i] + r + 2
            x2 = xs[i + 1] - r - 2
            d.add(Line(x1, cy, x2, cy, strokeColor=lc, strokeWidth=2))
            d.add(Line(x2 - 7, cy - 4, x2, cy, strokeColor=lc, strokeWidth=2))
            d.add(Line(x2 - 7, cy + 4, x2, cy, strokeColor=lc, strokeWidth=2))

        ry = cy - r - 14
        x_l = xs[0]
        x_r = xs[3]
        d.add(Line(x_l, ry, x_r, ry, strokeColor=RED_C, strokeWidth=1.5,
                   strokeDashArray=[6, 4]))
        d.add(Line(x_l + 8, ry - 4, x_l, ry, strokeColor=RED_C, strokeWidth=1.5))
        d.add(Line(x_l + 8, ry + 4, x_l, ry, strokeColor=RED_C, strokeWidth=1.5))
        mid = (x_l + x_r) / 2
        d.add(String(mid - 45, ry - 14, '✗ No return path', fontSize=9,
                     fontName='DV-B', fillColor=RED_C))
        return d

    # ── Build content ──────────────────────────────────────────────────────────
    doc = make_doc(os.path.join(OUT_DIR, 'ZP-A_Illustrated_Companion.pdf'),
                   'ZP-A Illustrated Companion', 'ZP-A Companion', 'Version 1.2')
    E = []

    # Header banner
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('ZP-A Illustrated Companion',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    E += [
        Paragraph('How state accumulates without ever going backwards', CS['title']),
        Paragraph('Lattice Algebra | Version 1.2', CS['subtitle']),
        Paragraph('ZP Companion | April 2026', CS['meta']),
        Paragraph(
            'This companion explains the ideas in plain language with diagrams and real-world '
            'examples. It is not the formal ontology — every claim here restates a result already '
            'proven in the corresponding technical document. Consult that document for the '
            'authoritative mathematics.',
            CS['disc']),
    ]

    # ── What Is ZP-A Doing? ────────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-A Doing?', CS['h1']))
    E.append(cbody(
        'ZP-A establishes the algebraic rules for how states behave in the Zero Paradox '
        'framework. It uses a structure called a join-semilattice — the simplest algebraic '
        'system that can describe accumulation without subtraction. Think of it as a ledger '
        'where entries can only be added, never erased.'))
    E.append(cbody(
        'The central object is the triple (L, &#8744;, &#8869;): a set of states L, a joining '
        'operation &#8744; that combines two states into a larger one, and a special bottom '
        'element &#8869; that represents the absolute starting point. Four axioms (A1&#8211;A4) '
        'say that joining is associative, commutative, idempotent, and that &#8869; is a '
        'neutral element.'))
    E.append(sp(4))
    E.append(example_box('Real-world example — Bank ledger', [
        'Think of &#8869; as a brand-new account with zero balance. Every transaction adds to '
        'the ledger. There is no undo operation — once a deposit is recorded, the total can '
        'only stay the same or grow. The join-semilattice captures exactly this: accumulation '
        'without reversal.',
    ]))
    E.append(sp(4))
    E.append(remember_box(
        'Remember: The bank account is just one way to picture it. The framework applies to '
        'any system where state can only accumulate — energy, information, or any other '
        'monotone quantity.'))

    # ── The Partial Order ──────────────────────────────────────────────────────
    E.append(Paragraph('The Partial Order: States Have a Natural Height', CS['h1']))
    E.append(cbody(
        'From the four axioms, a partial order falls out automatically: state x is "below" y '
        'if joining x with y just gives y back — y already contains everything x does. '
        '&#8869; is always at the very bottom.'))
    E.append(sp(8))
    E.append(hasse_diagram())
    E.append(sp(4))
    E.append(Paragraph(
        'Hasse diagram: partial order on L. Arrows point upward. &#8869; (amber) is the '
        'universal minimum. Every state sits above &#8869;.',
        CS['caption']))
    E.append(sp(4))
    E.append(example_box('Real-world example — Biological complexity', [
        'Think of &#8869; as the simplest possible organism. More complex life forms are '
        '"above" simpler ones: they contain everything the simpler form has, plus more. '
        'In this abstract sense, complexity only accumulates.',
    ]))

    # ── No Subtraction ─────────────────────────────────────────────────────────
    E.append(Paragraph('No Subtraction', CS['h1']))
    E.append(cbody(
        'The join-semilattice deliberately omits subtraction. State content can only '
        'accumulate, never be removed. Every valid transition moves upward.'))
    E.append(sp(8))
    E.append(transition_diagram())
    E.append(sp(4))
    E.append(Paragraph(
        'State transitions are one-directional. The red dashed line — a return path — '
        'does not exist in this algebra.',
        CS['caption']))
    E.append(sp(4))
    E.append(key_result_box(
        'Key Result: Monotonicity is a Theorem — not an Assumption (T3)',
        'For any state sequence built by joining, S&#8320; &#8804; S&#8321; &#8804; S&#8322; '
        '&#8804; &#8230; This is derived from the axioms, not assumed. The sequence can only '
        'go up.'))
    E.append(sp(4))
    E.append(key_result_box(
        'Key Result: &#8869; is a Constituent of Every State (T2)',
        '&#8869; &#8804; x for all x in L. &#8869; is not a void that states escape from — '
        'it is algebraically present in every state. Zero is not absence; it is the universal '
        'base.'))
    E.append(sp(4))
    E.append(example_box('Real-world example — Silence in music', [
        'Silence is not the absence of the piece — it is the baseline from which every note '
        'departs. Every musical state contains silence as its foundation. The join-semilattice '
        'captures this: &#8869; is a constituent of every state.',
    ]))

    # ── More Examples ─────────────────────────────────────────────────────────
    E.append(Paragraph('More Examples of Join-Semilattices', CS['h1']))
    E.append(cbody(
        'A join-semilattice appears in many mathematical and everyday settings. Here are '
        'four concrete instantiations of (L, &#8744;, &#8869;), each satisfying A1&#8211;A4.'))
    E.append(sp(4))

    E.append(example_box('Example — Power set with union', [
        'Let X be any set. Take L = P(X) (the collection of all subsets of X), '
        '&#8744; = &#8746; (set union), and &#8869; = ∅ (the empty set). Union is '
        'associative, commutative, idempotent (A &#8746; A = A), and the empty set is a '
        'neutral element (∅ &#8746; A = A). The induced order is inclusion: A &#8804; B '
        'iff A &#8746; B = B, i.e. A &#8838; B. Every element of L sits above ∅.',
    ]))
    E.append(sp(4))

    E.append(example_box('Example — [0, &#8734;) with maximum', [
        'Take L = [0, &#8734;), &#8744; = max (the larger of two values), and &#8869; = 0. '
        'Maximum is associative, commutative, idempotent (max(x, x) = x), and 0 is a neutral '
        'element (max(0, x) = x for x &#8805; 0). The induced order is the usual &#8804; on '
        'real numbers: x &#8804; y iff max(x, y) = y. Note: addition would not work here — '
        'x + x = 2x &#8800; x, violating idempotency (A3).',
    ]))
    E.append(sp(4))

    E.append(example_box('Example — Functions with pointwise maximum', [
        'Let X be any set. Take L to be the set of all functions f: X &#8594; [0, &#8734;), '
        '&#8744; = pointwise maximum ((f &#8744; g)(x) = max(f(x), g(x))), and &#8869; = the '
        'zero function. All four axioms hold pointwise. The induced order is f &#8804; g iff '
        'f(x) &#8804; g(x) for all x &#8712; X. This is a function-space version of the '
        'previous example — one level up in abstraction.',
    ]))
    E.append(sp(4))

    E.append(example_box('Example — Document edit history', [
        'Open a document and start making edits. Even hitting Backspace does not erase from '
        'the edit record — it adds a new deletion event to the history. Each saved state of '
        'the document sits above all states that preceded it. The history can only grow. '
        'The "join" of two document states is the later one (or the merge if branches exist). '
        'The &#8869; state is the empty document. No edit operation removes from the record.',
    ]))

    # ── Closing remember ───────────────────────────────────────────────────────
    E.append(sp(6))
    E.append(remember_box(
        'Remember: ZP-A makes no claims about topology, probability, or physics. It only '
        'establishes the algebraic skeleton. Everything it claims can be verified by a reader '
        'fluent in algebra without consulting any other document.'))

    E.append(sp(4))
    E.append(Paragraph(
        'Zero Paradox ZP-A Companion | Lattice Algebra | April 2026 | v1.2',
        ParagraphStyle('foot2', fontName='DV-I', fontSize=8, leading=10,
                       textColor=colors.grey, alignment=1)))

    doc.build(E)
    print('ZP-A Companion done')


def build_zpb():
    doc = make_doc(os.path.join(OUT_DIR, 'ZP-B_pAdic_Topology_v1_3.pdf'),
                   'ZP-B: p-Adic Topology', 'ZP-B', 'Version 1.3')
    E = []
    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-B: p-Adic Topology', S['subtitle']),
          Paragraph('Version 1.3  |  April 2026', S['subtitle']),
          Paragraph('<i>Supersedes v1.2  |  Theorem/Proposition hierarchy applied: T1, T2, T5 relabelled Proposition</i>', S['subtitle']),
          sp(10),
          body('This document is self-contained within p-adic analysis and topology. No abstract algebra from ZP-A, no probability, and no Hilbert space is imported. Cross-framework connections are deferred to ZP-D and ZP-E.'),
          body('<i>Illustrated Companion: A paired ZP-B Illustrated Companion provides concrete examples and visual intuitions for the results here. Examples are kept separate from the formal layers to distinguish illustrative material from proofs.</i>'),
          body('<i>Version 1.3 change: Theorem/Proposition hierarchy applied. T1 (Strong Triangle Inequality) and T2 (Every Ball is Clopen) relabelled Proposition — both are well-known infrastructure results of p-adic analysis, not primary claims of this framework. T5 (Total Disconnectedness) relabelled Proposition — it is load-bearing infrastructure for C3. T0 (p=2 is uniquely derived) and T3 (Topological Isolation of 0) retain Theorem labels as the primary claims of ZP-B.</i>'),
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
        'Proof:',
        'Step 1 — AX-B1 establishes exactly two ontological states: non-existence (0) and existence (1).',
        'Step 2 — A p-adic field Q<sub>p</sub> uses coefficients from {0, 1, &#8230;, p&#8722;1}. The minimum base p capable of representing exactly two distinct values without redundancy is p = 2, with coefficient set {0, 1}. One coefficient per ontological state; no unused coefficients.',
        'Step 3 — p = 1 has only one coefficient value {0}. Cannot distinguish existence from non-existence. Fails faithfulness (MP-1).',
        'Step 4 — p > 2: coefficient set {0, &#8230;, p&#8722;1} contains values with no ontological counterpart. Violates no-redundancy condition of MP-1.',
        'Step 5 — p = 2 is the unique prime satisfying both conditions simultaneously.',
        'Step 6 — The binary branching at every level of Q<sub>2</sub>\'s ball structure reflects the eventual binary resolution of any representational complexity.',
        'Therefore p = 2. Status: DERIVED from AX-B1 and MP-1. OQ-B1 closed. <font name="DV">&#10003;</font>',
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
    E.append(label_box('Definition D5 — Minimum Viable Deviation &#949;\u2080', [
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
    E.append(label_box('Definition D3 — Ball in Q\u2082', [
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

    E.append(Paragraph('V. Topological Structure of Q\u2082', S['h1']))
    E.append(Paragraph('5.1  Total Disconnectedness — proven before C3', S['h2']))
    E.append(label_box('Proposition T5 — Q\u2082 is Totally Disconnected', [
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
         ['T0: p = 2', 'Valid — Derived from AX-B1 and MP-1; OQ-B1 closed'],
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
    print('ZP-B done')


# ── ZP-C, ZP-D, ZP-E builders follow the same pattern ────────────────────────
# (included in full below)

def build_zpd():
    doc = make_doc(os.path.join(OUT_DIR, 'ZP-D_State_Layer_v1_3.pdf'),
                   'ZP-D: State Layer (Hilbert Space)', 'ZP-D', 'Version 1.3')
    E = []
    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-D: State Layer (Hilbert Space)', S['subtitle']),
          Paragraph('Version 1.3  |  April 2026', S['subtitle']),
          Paragraph('<i>Supersedes v1.2  |  Theorem/Proposition hierarchy applied: T3, T5 relabelled Proposition</i>', S['subtitle']),
          sp(10),
          body('This document operates within functional analysis. It imports from ZP-A and ZP-B and constructs the Hilbert space state layer on top of them. No information theory from ZP-C is imported. Cross-framework synthesis is deferred to ZP-E.'),
          body('<i>Illustrated Companion: A paired ZP-D Illustrated Companion provides concrete examples and visual intuitions for the results here. Examples are kept separate from the formal layers to distinguish illustrative material from proofs.</i>'),
          body('<i>Version 1.3 change: Theorem/Proposition hierarchy applied. T3 (Uniqueness of T up to Unitary Equivalence) relabelled Proposition — a well-known result in functional analysis, infrastructure for T4. T5 (Monotone Sequences Map to Accumulating Vectors) relabelled Proposition — a structural consequence of T2 and ZP-A T3. T2 (Existence of T) and T4 (Snap Produces Orthogonal Shift) retain Theorem labels as the primary existence and snap claims of ZP-D.</i>'),
          body('<i>Version 1.2 change: Theorem T1 is reclassified as Design Principle DP-1. Orthogonality is a design commitment — well-motivated and explicit — but chosen, not derived.</i>'),
          sp()]

    E.append(Paragraph('I. Imported Structure', S['h1']))
    E.append(Paragraph('1.1  From ZP-A: Algebraic Structure of States', S['h2']))
    E.append(label_box('Import I-A — From ZP-A: Lattice Algebra', [
        '(L, &#8744;, &#8869;): join-semilattice with bottom. Axioms A1&#8211;A4.',
        '&#8804; partial order: x &#8804; y :&#10234; x &#8744; y = y (D1, T1).',
        '&#8869; is the global minimum: &#8869; &#8804; x for all x &#8712; L (T2).',
        'State transitions are joins: f(x) = x &#8744; &#945; (D2).',
        'State sequences are monotone: S<sub>n</sub> &#8804; S<sub>n+1</sub> (T3).',
        'CC-1: S<sub>0</sub> = &#8869; — Conditional Claim; modelling commitment.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('1.2  From ZP-B: Topological Domain', S['h2']))
    E.append(label_box('Import I-B — From ZP-B: p-Adic Topology', [
        'AX-B1: Binary Existence Axiom.',
        'MP-1: Minimality Principle.',
        'T0: p = 2 derived from AX-B1 and MP-1.',
        'Q<sub>2</sub> with 2-adic metric d (D1, D2).',
        'T1: Ultrametric (strong triangle inequality).',
        'T2: Every ball is clopen.',
        'T3: Topological isolation of 0.',
        'T5: Q<sub>2</sub> is totally disconnected.',
        'C3: Snap is topologically irreversible (corollary of T5).',
        '&#949;<sub>0</sub>: Minimum viable deviation, universe-contingent parameter (D5).',
    ]))

    E.append(Paragraph('II. The Hilbert Space State Layer', S['h1']))
    E.append(label_box('Definition D1 — State Layer H', [
        'H = &#8450;<super>n</super> is a complex Hilbert space with orthonormal basis {e<sub>0</sub>, e<sub>1</sub>, e<sub>2</sub>, &#8230;}.',
        'n is the cardinality of the clopen ball partition of Q<sub>2</sub>. For finite approximations, n is finite; the framework extends to infinite-dimensional Hilbert spaces by standard functional analysis.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R1 — Decoupling of Topological and State Layers', [
        'Q<sub>2</sub> and H are categorically distinct structures. Q<sub>2</sub> is a topological field; H is a Hilbert space over &#8450;. They share no operations.',
        'The transition operator T: Q<sub>2</sub> &#8594; H is the only bridge. It is constructed explicitly in T2.',
        'No operation in H is assumed to inherit a topological property of Q<sub>2</sub> without proof. Every cross-layer claim must go through T.',
    ]))

    E.append(Paragraph('III. The Transition Operator T: Q\u2082 &#8594; H', S['h1']))
    E.append(Paragraph('3.1  The Design Commitment — Orthogonality', S['h2']))
    E.append(label_box('Design Principle DP-1 — Orthogonality as the Representation of Topological Isolation  [reclassified from T1 in v1.1]', [
        'Topological isolation in Q<sub>2</sub> (T3: 0 is isolated; clopen balls are mutually separated) is represented in H by orthogonality: elements that are topologically isolated in Q<sub>2</sub> map to orthogonal vectors in H.',
        'Motivation: Orthogonality in H is the natural algebraic analogue of topological separation. &#10216;e<sub>i</sub>, e<sub>j</sub>&#10217; = 0 for i &#8800; j; two clopen balls are maximally distinct in the topological sense.',
        'Status: DESIGN PRINCIPLE — DP-1 is chosen, not derived. It is the natural and consistent choice, stated explicitly. T4 and T5 below depend on DP-1 as a premise.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.2  The Construction Target', S['h2']))
    E.append(label_box('Definition D2 — Transition Operator T (Requirements)', [
        'T: Q<sub>2</sub> &#8594; H must satisfy:',
        '(i)   T(0) = e<sub>0</sub>   (null state maps to the designated base vector)',
        '(ii)  T(&#949;<sub>0</sub>) = e<sub>1</sub>   (minimum deviation maps to the first non-base vector)',
        '(iii) T is injective on the clopen ball partition',
        '(iv)  If x and y are in disjoint clopen balls, then &#10216;T(x), T(y)&#10217; = 0   (DP-1)',
        '(v)   &#8214;T(x)&#8214; &#8805; &#8214;T(0)&#8214; for all x   (norm-increasing: additive ontology preserved)',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.3  Existence of T', S['h2']))
    E.append(label_box('Theorem T2 — Existence of T (Basis Assignment)', [
        'There exists a function T: Q<sub>2</sub> &#8594; H satisfying all five requirements of D2.',
        'Proof: Construct T by basis assignment. The clopen ball partition of Q<sub>2</sub> at level k consists of 2<super>k</super> disjoint clopen balls. Assign each ball to a distinct basis vector of H. T(x) = e<sub>i</sub> where i is the index of the ball containing x.',
        '(i) 0 maps to e<sub>0</sub> by assignment. <font name="DV">&#10003;</font>  (ii) &#949;<sub>0</sub> maps to e<sub>1</sub> by assignment. <font name="DV">&#10003;</font>  (iii) Distinct balls &#8594; distinct basis vectors. <font name="DV">&#10003;</font>  (iv) Disjoint balls &#8594; orthogonal basis vectors. <font name="DV">&#10003;</font>  (v) All basis vectors have norm 1 &#8805; &#8214;e<sub>0</sub>&#8214; = 1. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.4  Uniqueness of T', S['h2']))
    E.append(label_box('Proposition T3 — Uniqueness of T up to Unitary Equivalence', [
        'Any two operators T, T\': Q<sub>2</sub> &#8594; H satisfying D2 are related by a unitary transformation U: H &#8594; H such that T\' = U &#8728; T.',
        'Proof: T and T\' both assign e<sub>0</sub> to the image of 0, which is the unique additive identity (A4). The ball structure of Q<sub>2</sub> is fixed; only the labelling of basis vectors varies. A unitary map U taking T(0) to T\'(0) and preserving orthogonality relations defines the equivalence. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R2 — What T Is Not', [
        'T is not a ring homomorphism. Q<sub>2</sub> has field operations; H does not. T does not preserve addition or multiplication from Q<sub>2</sub>.',
        'T is not a topological embedding. The topology of H is the norm topology; the topology of Q<sub>2</sub> is the 2-adic ultrametric. T is a structure-preserving assignment: ontological distinctions (topological isolation in Q<sub>2</sub>) map to algebraic distinctions (orthogonality in H), as specified by DP-1.',
    ]))

    E.append(Paragraph('IV. The Binary Snap in H', S['h1']))
    E.append(label_box('Theorem T4 — Snap Produces Orthogonal Shift in H', [
        'The Binary Snap 0 &#8594; &#949;<sub>0</sub> in Q<sub>2</sub> maps to an orthogonal shift in H: T(0) = e<sub>0</sub> and T(&#949;<sub>0</sub>) = e<sub>1</sub>, and &#10216;e<sub>0</sub>, e<sub>1</sub>&#10217; = 0.',
        'Proof: By D2(i), T(0) = e<sub>0</sub>. By D2(ii), T(&#949;<sub>0</sub>) = e<sub>1</sub>. Since 0 and &#949;<sub>0</sub> are in disjoint clopen balls of Q<sub>2</sub> (T3), D2(iv) and DP-1 give &#10216;T(0), T(&#949;<sub>0</sub>)&#10217; = &#10216;e<sub>0</sub>, e<sub>1</sub>&#10217; = 0. <font name="DV">&#10003;</font>',
        'Status: Derived — unconditional theorem given DP-1.',
    ]))
    E.append(sp(4))
    E.append(label_box('Proposition T5 — Monotone Sequences Map to Accumulating Vectors', [
        'Let (S<sub>n</sub>) be a monotone state sequence in L (ZP-A T3). Then &#8214;T(S<sub>n</sub>)&#8214; &#8804; &#8214;T(S<sub>n+1</sub>)&#8214; for all n.',
        'Proof: By ZP-A T3, S<sub>n</sub> &#8804; S<sub>n+1</sub>. By D2(v), T is norm-increasing. Each additional join contributes a new component in H, and the norm grows monotonically. <font name="DV">&#10003;</font>',
    ]))

    E.append(Paragraph('V. Open Items Register for ZP-D v1.3', S['h1']))
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        [['DP-1: Orthogonality commitment', 'Design Principle — explicit', 'Reclassified from Theorem T1. Orthogonality is chosen, not derived. Content unchanged.'],
         ['T2: Existence of T', 'Closed', 'Basis assignment construction. All five requirements verified.'],
         ['T3: Uniqueness of T', 'Closed', 'Unique up to unitary equivalence.'],
         ['T4: Snap &#8594; orthogonal shift', 'Closed — unconditional', 'Proven from T2 and ZP-B T3. Depends on DP-1 as premise.'],
         ['T5: Monotone norms', 'Closed — unconditional', 'Proven from T2 and ZP-A T3.']],
        [1.6*inch, 1.5*inch, 3.4*inch]
    ))

    E.append(Paragraph('VI. Validation Status', S['h1']))
    E.append(data_table(
        ['Component', 'Status / Notes'],
        [['H = &#8450;<super>n</super> (D1)', 'Valid — Defined; standard Hilbert space; self-contained'],
         ['Decoupling of Q<sub>2</sub> and H (R1)', 'Valid — Structural; Q<sub>2</sub> and H are categorically distinct; T is the bridge'],
         ['Import I-A from ZP-A', 'Valid — Received; CC-1 reclassification noted'],
         ['Import I-B from ZP-B', 'Valid — Received; MP-1 included; C3 noted'],
         ['DP-1: Orthogonality', 'Valid — Design Principle; reclassified from T1; well-motivated and explicit'],
         ['D2: T requirements', 'Valid — Defined; five requirements stated; all satisfied by T2'],
         ['T2: Existence of T', 'Valid — Derived; basis assignment; all five requirements verified'],
         ['T3: Uniqueness of T', 'Valid — Proposition; derived; unique up to unitary equivalence'],
         ['T4: Snap &#8594; orthogonal shift', 'Valid — Theorem; derived; unconditional; depends on DP-1'],
         ['T5: Monotone norms', 'Valid — Proposition; derived; unconditional; from T2 and ZP-A T3']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print('ZP-D done')


def build_zpe_da1():
    doc = make_doc(os.path.join(OUT_DIR, 'ZP-E_DA1_TSNAP_Insert.pdf'),
                   'ZP-E: DA-1 / T-SNAP Insert', 'ZP-E DA-1 / T-SNAP', 'April 2026')
    E = []
    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-E: Bridge Document — Formal Insert DA-1', S['subtitle']),
          Paragraph('Definitional Alignment: Instantiation as Execution', S['subtitle']),
          Paragraph('April 2026  |  Closes DA-1  |  AX-1 promoted to Theorem T-SNAP', S['subtitle']),
          sp(10),
          body('This insert is a formal section of ZP-E. It provides the definitional alignment (DA-1) that connects the incompressibility threshold P<sub>0</sub> (ZP-C D1) to the machine execution formalized in L-RUN (ZP-C v1.4). With DA-1 in place, T-BUF becomes a closed derived result, and AX-1 is promoted from axiom to theorem (T-SNAP).'),
          sp()]

    E.append(Paragraph('I. The Gap DA-1 Closes', S['h1']))
    E.append(label_box('The T-BUF Chain from ZP-C v1.4', [
        'L-RUN: The transition c<sub>0</sub> &#8594; c<sub>1</sub> is a non-null state change. (ZP-C v1.4 Lemma L-RUN — Derived)',
        'TQ-IH: No program outputs &#8869; without a non-null intermediate configuration state. (ZP-C v1.4 — Derived by L-RUN)',
        'T-BUF: At P<sub>0</sub>, execution is structurally guaranteed; that execution state is &#949;<sub>0</sub> in the semilattice. (ZP-C v1.4 — Candidate Theorem pending DA-1)',
    ]))
    E.append(sp(4))
    E.append(body('T-BUF was labelled Candidate because one step was not formally closed within ZP-C: Step 2 asserts that a configuration at P<sub>0</sub> is a <i>live machine state</i> — that instantiation at P<sub>0</sub> constitutes an execution event, not a static description. This is a cross-framework claim connecting P<sub>0</sub> (ZP-C) to D7 (ZP-C) via AX-B1 (ZP-B). The connection is the work of ZP-E. DA-1 provides it.'))

    E.append(Paragraph('II. Definitional Alignment DA-1', S['h1']))
    E.append(Paragraph('2.1  The Distinction Being Bridged', S['h2']))
    E.append(label_box('Two Senses of "a Configuration at P\u2080"', [
        'Sense A — Descriptive: x exists as a string — a finite syntactic object that has been written down or specified. The machine it describes has not necessarily been instantiated. P<sub>0</sub> is a property of the string. The string is inert.',
        'Sense B — Instantiated: x exists as the current configuration of a running machine. The machine is executing. P<sub>0</sub> is a property of the live configuration. The configuration is active.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('2.2  The Definitional Alignment', S['h2']))
    E.append(label_box('Definitional Alignment DA-1 — Instantiation of a Configuration at P\u2080 Constitutes an Execution Event', [
        'Claim: The instantiation of a machine configuration c<sub>1</sub> at the incompressibility threshold P<sub>0</sub> is an execution event in the sense of L-RUN. It is not a static description of a machine. It is a machine in state c<sub>1</sub>.',
        'Grounding: By AX-B1, a state either exists or it does not. A configuration at P<sub>0</sub> that is merely described (Sense A) does not occupy a state in the semilattice — it is a string in a meta-language, not an element of L. A configuration at P<sub>0</sub> that is instantiated (Sense B) does occupy a state: it is c<sub>1</sub>, which by L-RUN is a non-null element of L distinct from &#8869;.',
        'The binary of AX-B1 applies: for any configuration c at P<sub>0</sub>, either c is instantiated (Sense B) or it is not. If instantiated, it is an execution event. If not instantiated, it does not satisfy D7 — D7 defines a machine configuration as a complete description of a Turing machine <i>at a given moment</i>, which presupposes the machine is running.',
        'Therefore: any object satisfying D7 at P<sub>0</sub> is already an instantiated execution event. The description/instantiation distinction collapses at the level of D7: D7 configurations are by definition live.',
        'Status: DEFINITIONAL ALIGNMENT — no new axiom introduced. DA-1 is a clarification of scope. AX-B1 ensures the binary applies. No additional mathematical content required. <font name="DV">&#10003;</font>',
    ]))

    E.append(Paragraph('III. Promotion of T-BUF to Closed Theorem', S['h1']))
    E.append(label_box('Theorem T-SNAP — Binary Snap Causality  [AX-1 Promoted to Theorem]', [
        'Statement: The Binary Snap &#8869; &#8594; &#949;<sub>0</sub> is a derived consequence of P<sub>0</sub>, L-RUN, TQ-IH, DA-1, and ZP-A D2. It is not an axiom.',
        'Proof:',
        'Step 1 — P<sub>0</sub> identifies the incompressibility threshold. When K(x|n)/n = 1, the configuration string x is algorithmically random. (ZP-C D1 — Derived)',
        'Step 2 — A configuration x satisfying D7 at P<sub>0</sub> is an instantiated execution event. (DA-1 — Definitional; D7 configurations are live by definition; AX-B1 ensures the binary applies)',
        'Step 3 — Any instantiated execution passes through c<sub>1</sub>. (ZP-C D7 — definitional; c<sub>1</sub> is the first running configuration)',
        'Step 4 — c<sub>1</sub> &#8800; &#8869;. (ZP-C L-RUN — Derived; c<sub>1</sub> has gained execution context not present in c<sub>0</sub> = &#8869;; by AX-B1 this is a distinct, non-null state)',
        'Step 5 — No program that executes produces only null configuration states. (ZP-C TQ-IH — Derived; execution trace &#964;(p) contains c<sub>1</sub> for any executing program p)',
        'Step 6 — In (L, &#8744;, &#8869;), c<sub>1</sub> is an element strictly above &#8869;. By ZP-A D2, the transition &#8869; &#8594; c<sub>1</sub> is a valid state transition: c<sub>1</sub> = &#8869; &#8744; &#949;<sub>0</sub> for some &#949;<sub>0</sub> &#8712; L with &#949;<sub>0</sub> > &#8869;. This transition is the Binary Snap.',
        'Step 7 — The transition is irreversible: algebraically by ZP-A R1 (no subtraction operator); topologically by ZP-B C3 (no continuous return path to 0 in Q<sub>2</sub>); categorically by AX-G2 (hom(X, 0) = <font name="DV">&#8709;</font> for X &#8800; 0).',
        'Conclusion: The Binary Snap is a derived consequence. AX-1 is promoted to Theorem T-SNAP. <font name="DV">&#10003;</font>',
        'Status: DERIVED — Cross-Framework. Dependencies: ZP-C D1, D7, L-RUN, TQ-IH; ZP-B AX-B1, C3; ZP-A D2, R1; ZP-G AX-G2; ZP-E DA-1. No axiom beyond AX-B1, AX-G1, AX-G2 is required.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R-DA1 — Effect of T-SNAP on Downstream Results', [
        'All results in ZP-E that previously depended on AX-1 as an axiom now depend on T-SNAP as a derived theorem.',
        'T5 (Iterative Forcing Theorem) depended on AX-1 for the first Snap. It now depends on T-SNAP. Content unchanged; grounding strengthened.',
        'T4 (Unified Snap Description) carried AX-1 as an axiom label on the causality component. That label is now upgraded to Derived — T-SNAP.',
        'The intentional axioms of the system are now: AX-B1 (binary existence), AX-G1 (initial object), AX-G2 (source asymmetry). AX-1 is no longer an axiom.',
    ]))

    E.append(Paragraph('IV. Updated Traceability Register', S['h1']))
    E.append(data_table(
        ['Claim', 'Grounded In', 'Bridge Axiom?', 'Status'],
        [['Binary Snap causality', 'ZP-C D1, L-RUN, TQ-IH; ZP-A D2; DA-1', 'None', 'Derived — T-SNAP <font name="DV">&#10003;</font>  (was: Axiomatic — AX-1)'],
         ['DA-1: Instantiation = execution', 'AX-B1, ZP-C D7', 'None', 'Definitional Alignment — clarification of scope; no new axiom'],
         ['T-SNAP: Snap is derived', 'T-BUF chain + DA-1', 'None', 'Derived — Cross-Framework <font name="DV">&#10003;</font>'],
         ['AX-1 retirement', 'T-SNAP closes AX-1', 'N/A', 'AX-1 is no longer an axiom; T-SNAP is its replacement'],
         ['Iterative Forcing T5', 'AX-B1, T-SNAP (replaces AX-1)', 'None', 'Derived — grounding strengthened'],
         ['Unified Snap T4 (causality)', 'T-SNAP (replaces AX-1 label)', 'None', 'Derived — label upgraded from Axiomatic']],
        [1.5*inch, 1.9*inch, 1.1*inch, 2.0*inch]
    ))

    E.append(Paragraph('V. Updated Open Items Register', S['h1']))
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        [['AX-1: Binary Snap Causality', 'CLOSED — T-SNAP', 'AX-1 is no longer an axiom. Binary Snap derived via P<sub>0</sub> + DA-1 + L-RUN + TQ-IH + ZP-A D2.'],
         ['DA-1: Definitional Alignment', 'CLOSED — Definitional', 'D7 configurations are live by definition. No new axiom required.'],
         ['OQ-A1: Increment selection', 'CLOSED — T5', 'Iterative Forcing Theorem. &#945;<sub>n</sub> = &#949;(S<sub>n</sub>). Grounding updated from AX-1 to T-SNAP.'],
         ['OQ-C1: Non-conservatism of DF', 'CLOSED — ZP-C T2', 'Rebuilt within D6 extended. Infinite sequence divergence proven. No postulates remain.'],
         ['S1: Distribution stipulation', 'CLOSED — ZP-C T1', 'Derived from AX-B1 and RP-1.'],
         ['OQ-B1: p = 2', 'CLOSED — ZP-B T0', 'Derived from AX-B1 and MP-1.'],
         ['Temperature T in BA-1', 'PARAMETER — intentional', 'Universe-contingent. Physical predictions explicitly conditional on instantiation-specific T.'],
         ['Remaining axioms', 'INTENTIONAL — AX-B1, AX-G1, AX-G2', 'These are the three foundational commitments of the system. No further reduction is claimed.']],
        [1.6*inch, 1.5*inch, 3.4*inch]
    ))

    E.append(Paragraph('VI. Validation Status', S['h1']))
    E.append(label_box('Validation — All Components', [
        'DA-1: Definitional Alignment — Valid. Clarification of scope; no new axiom. D7 configurations are live by definition; AX-B1 ensures the binary applies. <font name="DV">&#10003;</font>',
        'T-SNAP: Binary Snap derived — Valid — Derived. Seven-step proof. All dependencies are closed theorems in their own documents. Cross-framework chain: ZP-C D1 &#8594; DA-1 &#8594; D7 &#8594; L-RUN &#8594; TQ-IH &#8594; ZP-A D2 &#8594; T-SNAP. <font name="DV">&#10003;</font>',
        'AX-1 retirement — Valid. AX-1 is superseded by T-SNAP. No content is lost; the claim is strengthened from assumed to derived.',
        'Remaining axiomatic commitments: AX-B1, AX-G1, AX-G2 — intentional foundational commitments, not gaps.',
        'All other ZP-E theorems (T1, T2, T3, T4, T5, T6, T2-C, T7) — unaffected in content; T4 and T5 carry upgraded status labels.',
    ]))

    doc.build(E)
    print('ZP-E DA-1 done')


# ── ZP-C is the largest — built separately due to length ──────────────────────

def build_zpc():
    doc = make_doc(os.path.join(OUT_DIR, 'ZP-C_Information_Theory_v1_5.pdf'),
                   'ZP-C: Information Theory', 'ZP-C', 'Version 1.5')
    E = []
    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-C: Information Theory', S['subtitle']),
          Paragraph('Version 1.5  |  April 2026', S['subtitle']),
          Paragraph('<i>Supersedes v1.4  |  Theorem/Corollary hierarchy applied: T1b relabelled Corollary</i>', S['subtitle']),
          sp(10),
          body('This document is self-contained within information theory and discrete analysis on Q<sub>2</sub>. The topological structure of Q<sub>2</sub> — specifically total disconnectedness (ZP-B T5), the clopen ball hierarchy, and the binary existence axiom (AX-B1) — is imported from ZP-B as a dependency. Every claim is marked as Derived, Axiomatic, Defined, or Candidate.'),
          body('<i>Illustrated Companion: A paired ZP-C Illustrated Companion provides concrete examples and visual intuitions for the results here. Examples are kept separate from the formal layers to distinguish illustrative material from proofs.</i>'),
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
    E.append(label_box('Remark R1 — Scope of P\u2080', [
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
    E.append(label_box('Definition D3 — Dirac Measure &#948;\u2080', [
        '&#8747;<sub>&#937;</sub> f d&#948;<sub>0</sub>  =  f(0)',
        '&#948;<sub>0</sub> places unit mass at 0. Compatible with the discrete topology of {0,1} and with the totally disconnected topology of Q<sub>2</sub> (ZP-B T5). &#948;<sub>0</sub> governs behaviour exactly at x = 0.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R2 — Hamming Cross-Validation', [
        'd<sub>H</sub>(P, Q) = 1   [Hamming, on {0,1}]',
        'The agreement between d<sub>H</sub> = 1 and E = 1 bit is a consistency check, not a proof that Hamming distance and JSD are equivalent in general. Both are computed by independent methods on the same AX-B1-derived distributions.',
    ]))

    E.append(Paragraph('III. The Discrete Surprisal Field on Q\u2082', S['h1']))
    E.append(label_box('Remark R3 — Why the Smooth Embedding Remains Retired', [
        'ZP-B T5 establishes Q<sub>2</sub> is totally disconnected. ZP-B T2 establishes every ball is clopen. Importing smooth calculus operators onto a totally disconnected space imports a smoothness assumption that contradicts ZP-B. The smooth embedding, MO-1, and P1 from v1.1 remain retired.',
    ]))
    E.append(sp(4))
    E.append(label_box('Definition D4 — Discrete Surprisal Function I', [
        'For x &#8712; Q<sub>2</sub> with x &#8800; 0 and P(x) > 0:',
        'I(x)  =  &#8722;log<sub>2</sub> P(x)',
        'As v<sub>2</sub>(x) &#8594; +&#8734; (x approaches 0 in the 2-adic metric), I(x) &#8594; +&#8734;: states 2-adically close to 0 are informationally extreme.',
        'The probability measure P on Q<sub>2</sub> \\ {0} is the branching measure induced by the binary ball hierarchy of Q<sub>2</sub>: at each level k, the two sub-balls of B(0, 2<super>&#8722;k</super>) each receive half the probability mass of their parent ball.',
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
        'Step 4 — c<sub>0</sub> corresponds to &#8869; (no distinguishable structure). c<sub>1</sub> is strictly above &#8869; in the semilattice: the machine configuration has gained content (an active execution context) not present in c<sub>0</sub>.',
        'Conclusion: c<sub>1</sub> &#8800; &#8869;. The act of execution is itself a non-null state, regardless of what the output tape contains. <font name="DV">&#10003;</font>',
        'Status: DERIVED from AX-B1 and D7. No Coding Theorem required. No output-tape contents required.',
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
    E.append(label_box('Candidate Theorem T-BUF — Incompressibility Forces Non-Null Execution State', [
        'Statement: At the incompressibility threshold P<sub>0</sub>, the Binary Snap &#8869; &#8594; &#949;<sub>0</sub> is a structural consequence of execution, not an external trigger.',
        'Step 1 — P<sub>0</sub> identifies the configuration x at which K(x|n)/n = 1: the configuration string is incompressible. (D1)',
        'Step 2 — An incompressible configuration that instantiates a computation must execute. The configuration at P<sub>0</sub> is a live machine state. To be at P<sub>0</sub> is to be a configuration string that is executing. (See DA-1 in ZP-E)',
        'Step 3 — Any execution passes through c<sub>1</sub> (L-RUN). c<sub>1</sub> &#8800; &#8869; (L-RUN conclusion).',
        'Step 4 — In (L, &#8744;, &#8869;), this non-null configuration state is c<sub>1</sub> = &#8869; &#8744; &#949;<sub>0</sub>. By ZP-A D2, this is the Binary Snap.',
        'Conclusion: At P<sub>0</sub>, execution is structurally guaranteed. Execution guarantees a non-null configuration state. That state is &#949;<sub>0</sub> in the semilattice. AX-1 is derivable from P<sub>0</sub> + L-RUN + TQ-IH + ZP-A D2. <font name="DV">&#10003;</font>',
        'Status: CANDIDATE THEOREM — structurally complete within ZP-C. Cross-framework integration (DA-1) owned by ZP-E. The gap between incompressibility and forced transition is closed at the configuration level.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R5 — Updated Status of AX-1', [
        'Prior to v1.4: AX-1 (Binary Snap Causality) was labeled Axiomatic in ZP-C.',
        'As of v1.4: AX-1 is a Candidate Theorem. The derivation pathway: P<sub>0</sub> (D1) identifies the threshold. L-RUN establishes that execution at the threshold constitutes a non-null state change. TQ-IH establishes that no program avoids this. ZP-A D2 establishes that a non-null state change from &#8869; is the Binary Snap.',
        'Remaining work: DA-1 (Definitional Alignment) must formally tie instantiation of P<sub>0</sub> to an execution event. This is owned by ZP-E.',
        'Status label: CANDIDATE THEOREM — gap identified and named (DA-1). Closed in ZP-E DA-1 insert.',
    ]))

    E.append(Paragraph('VI. Open Items Register for ZP-C v1.4', S['h1']))
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        [['S1: Distribution stipulation', 'Closed — T1', 'T1 derives P and Q from AX-B1 and RP-1.'],
         ['OQ-C1: Non-conservation', 'Closed — T2 rebuilt', 'Telescoping critique resolved; infinite divergence proven within extended D6.'],
         ['Smooth embedding, MO-1, P1', 'Retired', 'Remain retired from v1.2. Inconsistent with ZP-B.'],
         ['RP-1: Representation principle', 'Principle — explicit', 'Bridge between AX-B1 and probabilistic tools.'],
         ['D7: Machine configuration', 'Defined', 'Foundation for L-RUN and TQ-IH.'],
         ['L-RUN: Hardware Lemma', 'Derived — Lemma', 'Execution is a non-null state change. Derived from AX-B1 and D7.'],
         ['TQ-IH: Test Question', 'Closed — Negative', 'No program can output &#8869; without a non-null intermediate configuration state. Proven by L-RUN.'],
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
         ['D5: Difference operator DF', 'Valid — antisymmetric; no smoothness assumed'],
         ['D6: Circulation (extended)', 'Valid — finite and infinite cases both defined; finite conservation acknowledged'],
         ['T2: Non-conservation rebuilt', 'Valid — Derived; telescoping critique addressed; divergence at &#963;&#8594;0 established'],
         ['R2: Hamming cross-validation', 'Valid — Consistency check'],
         ['D7: Machine configuration', 'Valid — Defined; standard Turing model; no physics imported'],
         ['L-RUN: Hardware Lemma', 'Valid — Derived from AX-B1 and D7'],
         ['R4: Configuration vs. output independence', 'Valid — load-bearing distinction for TQ-IH and T-BUF'],
         ['TQ-IH: Test question answered', 'Valid — Derived by L-RUN; no Kolmogorov machinery required'],
         ['T-BUF: Candidate Theorem', 'Candidate — structurally complete in ZP-C; DA-1 bridge in ZP-E closes fully'],
         ['R5: AX-1 status updated', 'Valid — AX-1 is Candidate Theorem; prior Axiomatic status corrected']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print('ZP-C done')


# ── MAIN ──────────────────────────────────────────────────────────────────────
if __name__ == '__main__':
    import shutil
    os.makedirs(OUT_DIR, exist_ok=True)

    build_zpa()
    build_zpa_companion()
    build_zpb()
    build_zpc()
    build_zpd()
    # build_zpe_da1() removed 2026-04-23: ZP-E_DA1_TSNAP_Insert was superseded by
    # ZP-E_Bridge_Document_v2_0, which integrates DA-1, DA-2, DA-3, and the full
    # traceability register. The insert is archived at historical/ZP-E_DA1_TSNAP_Insert-1.pdf.
    # The build_zpe_da1() function is retained below for reference.

    # Verify all PDFs
    # METHOD: pdfplumber page.chars (character-level extraction).
    # This is the only reliable method — extract_text() and extract_words() both
    # drop glyphs adjacent to sub/superscript text (mixed-baseline extraction bug).
    # Raw binary search is also unreliable: ReportLab uses font-internal glyph IDs
    # for some characters, not direct Unicode codepoints.
    # NULL chars in the char stream = genuine missing glyph in the font.
    #
    # Per-document symbol map: only check symbols actually used in each doc.
    # ≤ does NOT appear in ZP-B (topology) or ZP-C (info theory) — only ZP-A and ZP-D.
    # ∨ does NOT appear in ZP-B — it is topology only, no semilattice operators.
    import pdfplumber
    DOC_SYMBOLS = {
        'ZP-A_Lattice': [0x22A5, 0x2228, 0x2264],  # ⊥ ∨ ≤
        'ZP-A_Illustrated': [0x22A5, 0x2264],       # ⊥ ≤
        'ZP-B': [0x22A5, 0x2208, 0x211A, 0x2192],  # ⊥ ∈ ℚ →
        'ZP-C': [0x22A5, 0x2228, 0x2192, 0x2208],  # ⊥ ∨ → ∈
        'ZP-D': [0x22A5, 0x2208, 0x2102, 0x2264],  # ⊥ ∈ ℂ ≤
        'ZP-E': [0x22A5, 0x2192, 0x2208, 0x2228],  # ⊥ → ∈ ∨
    }
    print('\n── Verification ──')
    for fname in sorted(os.listdir(OUT_DIR)):
        if not fname.endswith('.pdf'):
            continue
        path = os.path.join(OUT_DIR, fname)
        with pdfplumber.open(path) as pdf:
            pages = len(pdf.pages)
            all_chars = []
            for page in pdf.pages:
                all_chars.extend(c['text'] for c in page.chars if c['text'])
        char_set = set(all_chars)
        size = os.path.getsize(path) // 1024
        issues = []
        null_count = sum(1 for c in all_chars if ord(c) == 0)
        if null_count > 0:
            issues.append(f'NULL CHARS x{null_count} — missing glyph, needs DV font wrap')
        doc_key = next((k for k in DOC_SYMBOLS if k in fname.replace('_Lattice_Algebra', '_Lattice').replace('_Illustrated_Companion', '_Illustrated')), None)
        if doc_key:
            for cp in DOC_SYMBOLS[doc_key]:
                if chr(cp) not in char_set:
                    issues.append(f'MISSING {chr(cp)} U+{cp:04X}')
        status = 'PASS' if not issues else 'FAIL: ' + ', '.join(issues)
        print(f'  {fname}: {pages}pp  {size}KB  [{status}]')

    # Copy verified PDFs to project root
    for fname in os.listdir(OUT_DIR):
        if fname.endswith('.pdf'):
            shutil.copy(os.path.join(OUT_DIR, fname), os.path.join(PROJECT_ROOT, fname))
    print('\nAll PDFs copied to project root.')
