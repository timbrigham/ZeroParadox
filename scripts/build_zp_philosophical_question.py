"""
Build: The Philosophical Question That Started This (v1.0)
A standalone philosophical document in the Zero Paradox project.

Not a formal layer. Not a companion. An essay on the question
that generated the framework and what the framework discovered
about that question — including what it dissolves and what it snaps.

April 2026.
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

FONT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fonts') + os.sep
pdfmetrics.registerFont(TTFont('DV',    FONT_DIR + 'DejaVuSans.ttf'))
pdfmetrics.registerFont(TTFont('DV-B',  FONT_DIR + 'DejaVuSans-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DV-I',  FONT_DIR + 'DejaVuSans-Oblique.ttf'))
pdfmetrics.registerFont(TTFont('DVS',   FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-B', FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-I', FONT_DIR + 'STIXTwo-Math.ttf'))

GOLD        = colors.HexColor('#A0742A')
GOLD_LITE   = colors.HexColor('#FDF6E3')
GOLD_MED    = colors.HexColor('#F0E0A0')
SLATE       = colors.HexColor('#455A64')
SLATE_LITE  = colors.HexColor('#ECEFF1')
INDIGO      = colors.HexColor('#3949AB')
INDIGO_LITE = colors.HexColor('#E8EAF6')
GREEN_DARK  = colors.HexColor('#1B5E20')
GREEN_LITE  = colors.HexColor('#E8F5E9')
AMBER       = colors.HexColor('#F9A825')
AMBER_LITE  = colors.HexColor('#FFF8E1')
WHITE       = colors.white
BLACK       = colors.black

TW = 6.5 * inch
LM = RM = 1.0 * inch
TM = BM = 1.0 * inch

S = {
    'title':    ParagraphStyle('title',    fontName='DV-B',  fontSize=20, leading=26,
                               spaceAfter=6, alignment=1, textColor=BLACK),
    'subtitle': ParagraphStyle('subtitle', fontName='DVS-I', fontSize=12, leading=17,
                               spaceAfter=4, alignment=1, textColor=SLATE),
    'meta':     ParagraphStyle('meta',     fontName='DV-I',  fontSize=9,  leading=13,
                               spaceAfter=10, alignment=1, textColor=colors.grey),
    'h1':       ParagraphStyle('h1',       fontName='DV-B',  fontSize=13, leading=18,
                               spaceBefore=16, spaceAfter=6, textColor=GOLD),
    'body':     ParagraphStyle('body',     fontName='DVS',   fontSize=10.5, leading=16,
                               spaceAfter=8, alignment=4),
    'bodyI':    ParagraphStyle('bodyI',    fontName='DVS-I', fontSize=10.5, leading=16,
                               spaceAfter=8, alignment=4, textColor=SLATE),
    'note':     ParagraphStyle('note',     fontName='DVS-I', fontSize=9,   leading=13,
                               spaceAfter=4, textColor=colors.HexColor('#666666')),
    'lbl':      ParagraphStyle('lbl',      fontName='DV-B',  fontSize=9,   leading=13,
                               textColor=WHITE),
    'cell':     ParagraphStyle('cell',     fontName='DVS',   fontSize=10,  leading=14),
    'cellI':    ParagraphStyle('cellI',    fontName='DVS-I', fontSize=10,  leading=14),
    'snap':     ParagraphStyle('snap',     fontName='DVS-B', fontSize=11,  leading=16,
                               spaceAfter=4, textColor=INDIGO, alignment=1),
    'endnote':  ParagraphStyle('endnote',  fontName='DVS-I', fontSize=9,   leading=13,
                               alignment=1, textColor=SLATE),
}

def sp(n=6):
    return Spacer(1, n)

def hr():
    return HRFlowable(width='100%', thickness=0.5,
                      color=colors.HexColor('#BBBBBB'),
                      spaceAfter=6, spaceBefore=4)

def fix(text):
    sub_map = {'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4',
               '₅':'5','₆':'6','₇':'7','₈':'8','₉':'9',
               'ₙ':'n','ₖ':'k','ₘ':'m'}
    for ch, rep in sub_map.items():
        text = text.replace(ch, f'<sub>{rep}</sub>')
    text = text.replace('✓','<font name="DV">&#10003;</font>')
    replacements = [
        ('⊥','&#8869;'),('∨','&#8744;'),('≤','&#8804;'),('≥','&#8805;'),
        ('≠','&#8800;'),('∈','&#8712;'),('→','&#8594;'),('∞','&#8734;'),
        ('—','&#8212;'),('–','&#8211;'),('×','&#215;'),('−','&#8722;'),
        ('ε','&#949;'),('∀','&#8704;'),('∃','&#8707;'),('′','&#8242;'),
        ('ω','&#969;'),('⊂','&#8834;'),('≡','&#8801;'),
        ('ℚ','&#8474;'),('ℝ','&#8477;'),('ℕ','&#8469;'),
    ]
    for ch, ent in replacements:
        text = text.replace(ch, ent)
    return text

def body(text):
    return Paragraph(fix(text), S['body'])

def bodyI(text):
    return Paragraph(fix(text), S['bodyI'])

def callout(text, bg=GOLD_LITE, border=GOLD):
    ts = TableStyle([
        ('BACKGROUND',    (0,0),(-1,-1), bg),
        ('BOX',           (0,0),(-1,-1), 1.2, border),
        ('TOPPADDING',    (0,0),(-1,-1), 10),
        ('BOTTOMPADDING', (0,0),(-1,-1), 10),
        ('LEFTPADDING',   (0,0),(-1,-1), 12),
        ('RIGHTPADDING',  (0,0),(-1,-1), 12),
    ])
    t = Table([[Paragraph(fix(text), S['body'])]], colWidths=[TW])
    t.setStyle(ts)
    return t

def distinction_box(left_title, left_body, right_title, right_body):
    """Two-column box for crisp contrasts."""
    half = TW / 2 - 4
    left_data = [
        [Paragraph(left_title,  S['lbl'])],
        [Paragraph(fix(left_body),  S['cell'])],
    ]
    right_data = [
        [Paragraph(right_title, S['lbl'])],
        [Paragraph(fix(right_body), S['cell'])],
    ]
    left_ts = TableStyle([
        ('BACKGROUND',  (0,0),(-1,0),  INDIGO),
        ('BACKGROUND',  (0,1),(-1,-1), INDIGO_LITE),
        ('BOX',         (0,0),(-1,-1), 0.5, INDIGO),
        ('TOPPADDING',  (0,0),(-1,-1), 6),
        ('BOTTOMPADDING',(0,0),(-1,-1), 6),
        ('LEFTPADDING', (0,0),(-1,-1), 8),
        ('RIGHTPADDING',(0,0),(-1,-1), 8),
        ('VALIGN',      (0,0),(-1,-1), 'TOP'),
    ])
    right_ts = TableStyle([
        ('BACKGROUND',  (0,0),(-1,0),  GREEN_DARK),
        ('BACKGROUND',  (0,1),(-1,-1), GREEN_LITE),
        ('BOX',         (0,0),(-1,-1), 0.5, GREEN_DARK),
        ('TOPPADDING',  (0,0),(-1,-1), 6),
        ('BOTTOMPADDING',(0,0),(-1,-1), 6),
        ('LEFTPADDING', (0,0),(-1,-1), 8),
        ('RIGHTPADDING',(0,0),(-1,-1), 8),
        ('VALIGN',      (0,0),(-1,-1), 'TOP'),
    ])
    lt = Table(left_data,  colWidths=[half])
    lt.setStyle(left_ts)
    rt = Table(right_data, colWidths=[half])
    rt.setStyle(right_ts)
    outer = Table([[lt, rt]], colWidths=[half + 4, half])
    outer.setStyle(TableStyle([
        ('VALIGN',      (0,0),(-1,-1), 'TOP'),
        ('LEFTPADDING', (0,0),(-1,-1), 0),
        ('RIGHTPADDING',(0,0),(-1,-1), 0),
        ('TOPPADDING',  (0,0),(-1,-1), 0),
        ('BOTTOMPADDING',(0,0),(-1,-1), 0),
    ]))
    return outer

def amber_note(text):
    ts = TableStyle([
        ('BACKGROUND',    (0,0),(-1,-1), SLATE_LITE),
        ('BOX',           (0,0),(-1,-1), 0.5, SLATE),
        ('TOPPADDING',    (0,0),(-1,-1), 8),
        ('BOTTOMPADDING', (0,0),(-1,-1), 8),
        ('LEFTPADDING',   (0,0),(-1,-1), 12),
        ('RIGHTPADDING',  (0,0),(-1,-1), 12),
    ])
    t = Table([[Paragraph(fix(text), S['note'])]], colWidths=[TW])
    t.setStyle(ts)
    return t


def build():
    out_path = os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        'ZP_Philosophical_Question.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(
            LETTER[0] / 2, 0.6 * inch,
            'Zero Paradox  |  The Philosophical Question That Started This  |  April 2026  |  v1.0')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM,
                            title='The Philosophical Question That Started This',
                            author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # ── Transparency notice ────────────────────────────────────────────────────
    E.append(callout(
        '<b>A note on transparency:</b> This document lives in the public Zero Paradox '
        'repository but is not yet linked from the main project index. It is a '
        'philosophical essay — not a formal layer, not a Lean proof — addressing the '
        'question that motivated the mathematical framework. The main entry point for '
        'the Zero Paradox is README.md.',
        bg=AMBER_LITE, border=AMBER))
    E.append(sp(10))

    # ── Title block ────────────────────────────────────────────────────────────
    E += [
        Paragraph('THE ZERO PARADOX', S['meta']),
        Paragraph('The Philosophical Question That Started This', S['title']),
        Paragraph(
            'On the gap between formal description and instantiation, '
            'what the framework dissolves, and what it snaps.',
            S['subtitle']),
        Paragraph('Version 1.0  |  April 2026', S['meta']),
        hr(),
        sp(4),
    ]

    # ── Opening ────────────────────────────────────────────────────────────────
    E.append(body(
        'The Zero Paradox began with a philosophical question, not a mathematical one. '
        'The question was Leibniz\'s: <i>why is there something rather than nothing?</i> '
        'The standard response — in philosophy and in physics — is that this question '
        'has no formal answer. Existence must be assumed somewhere. Every formal system '
        'has a starting point it does not derive.'))
    E.append(body(
        'The Zero Paradox does not accept this. It asks: what if the emergence of '
        'something from nothing is not a starting assumption but a structural '
        'consequence — something the mathematics forces on any model that takes '
        'a null state seriously? If that is true, then the Binary Snap (⊥ → ε₀, '
        'the first transition from nothing to something) is not an axiom. It is a theorem.'))
    E.append(body(
        'Eight formal layers later — ZP-A through ZP-I, partially verified in Lean 4 '
        '— the framework has an answer. But the answer is more interesting than either '
        '"yes, fully proved" or "no, still assumed." What the framework found is a '
        'third possibility: the question itself, applied with sufficient precision, '
        'dissolves. This document is about that dissolution — and about the precise '
        'distinction between what dissolves and what snaps.'))
    E.append(hr())

    # ── Section 1 ──────────────────────────────────────────────────────────────
    E.append(Paragraph('I. The Mathematical Response', S['h1']))
    E.append(body(
        'The framework built to answer the question spans eight layers. Each is '
        'self-contained before any cross-layer claim is made:'))
    E.append(body(
        '<b>ZP-A</b> establishes the join-semilattice (L, ∨, ⊥) — a state space with '
        'a null element, monotone transitions, and no top element (R1: the ascent '
        'cannot stop). <b>ZP-B</b> grounds the topology in the 2-adic metric on ℚ₂, '
        'where the null state is the element of infinite depth and all transitions '
        'are irreversible (C3). <b>ZP-C</b> builds the information theory: '
        'surprisal, the incompressibility threshold P₀, and the key lemmas '
        'L-RUN and TQ-IH establishing that execution is always a non-null state change. '
        '<b>ZP-D</b> adds the Hilbert space representation. <b>ZP-E</b> derives '
        '<b>T-SNAP</b> — the Binary Snap as a theorem — through DA-1 (instantiation '
        'equals execution at P₀), closing what had been the framework\'s one axiom '
        '(AX-1). <b>ZP-G</b> and <b>ZP-H</b> extend the result categorically: '
        'four functors show that all four frameworks are realizations of one abstract '
        'structure. <b>ZP-I</b> proves T-IZ — every maximal ascending chain converges '
        'to its own successor null — establishing that the framework is a closed cycle, '
        'not merely an emergence theorem.'))
    E.append(body(
        'The topological and algebraic cores of these results are verified in Lean 4. '
        'T-SNAP is derived. The Binary Snap is not assumed.'))
    E.append(hr())

    # ── Section 2 ──────────────────────────────────────────────────────────────
    E.append(Paragraph('II. The Gap', S['h1']))
    E.append(body(
        'At the critical juncture sits DA-1: the argument that a configuration at '
        'the incompressibility threshold P₀ constitutes a live execution event. '
        'DA-1 is the bridge between the formal mathematics (the system is in state '
        'X with Kolmogorov complexity at maximum) and the ontological claim (therefore '
        'it is running, not merely described). DA-1 is only partially formalized. '
        'Its full argument requires Kolmogorov complexity — not yet in Lean\'s Mathlib — '
        'and ZF+AFA for the self-grounding null state (⊥ = {⊥}). These are gaps in '
        'available tooling, not in principle, but they are gaps.'))
    E.append(body(
        'More fundamentally: T-SNAP as a Lean theorem states ⊥ ∨ ε₀ = ε₀. This is '
        'trivially true for any join-semilattice with a bottom element — it is axiom A4 '
        'itself. The philosophically significant claim — that existence necessarily '
        'emerges from null — requires DA-1 to establish that the formal configuration '
        'IS the moment of instantiation, not merely a description of one. And no formal '
        'system can prove its own instantiation from within. A perfect Lean proof of '
        'DA-1 would still be, from inside the formalism, a claim about symbols. '
        'Whether the symbols correspond to anything running is a question the symbols '
        'cannot answer.'))
    E.append(callout(
        'This is the honest statement of the problem. It is not unique to the Zero '
        'Paradox. It is the wall every formal ontological argument hits. The question '
        'is whether the Zero Paradox hits it differently.',
        bg=GOLD_LITE, border=GOLD))
    E.append(hr())

    # ── Section 3 ──────────────────────────────────────────────────────────────
    E.append(Paragraph('III. Every Instance of Zero', S['h1']))
    E.append(body(
        'The framework\'s axioms do not describe one specific null state. They describe '
        'what ⊥ <i>is</i> — structurally — in any system that has one. The axioms apply '
        'to any join-semilattice with a bottom element satisfying A1-A4. This universality '
        'is not incidental. It is the key.'))
    E.append(body(
        'Consider what it would mean to deny the Snap. To deny it, you need a position — '
        'some state — from which the denial is made. That state is either null or non-null. '
        'If non-null, the Snap has already occurred: you are in ε₀ or beyond. '
        'If null, you are in exactly the state from which T-SNAP derives the Snap — '
        'the denial generates the thing denied. There is no position from which the '
        'denial is coherent. Every attempt to occupy a counterexample is itself an '
        'instance of the zero the framework describes.'))
    E.append(body(
        'This is a transcendental argument. It does not prove existence from scratch. '
        'It shows that any attempt to instantiate a counterexample already assumes '
        'the conditions that produce the Snap. The framework fits into every instance '
        'of zero — including the zero of the argument against it. The denial is '
        'self-undermining not because it is logically contradictory in the classical '
        'sense, but because instantiating the denial is itself a Snap.'))
    E.append(hr())

    # ── Section 4 ──────────────────────────────────────────────────────────────
    E.append(Paragraph('IV. The Gödelian Reframing', S['h1']))
    E.append(body(
        'Gödel\'s incompleteness theorems are standardly read as a ceiling: there are '
        'truths formal systems cannot reach from within. For any sufficiently powerful '
        'consistent system, there exists a true statement the system cannot prove. '
        'The ceiling is above; the truths are unreachable.'))
    E.append(body(
        'The Zero Paradox locates the structure at the floor. Every formal system '
        'has a ⊥ — an empty proof, a null type, a bottom element. That structure is '
        'not passive. It generates. The Gödelian undecidable sentence is not unreachable '
        'truth above the system. It is the ε₀ of that system\'s null state: forced '
        'by the same mechanism that forces every Binary Snap. Incompleteness is not '
        'the limit of formal systems. It is where the Snap lives inside every one of '
        'them. The ceiling is the floor seen from the other side.'))
    E.append(body(
        'If this is right, then making Gödel\'s work complete is not a matter of '
        'finding more axioms — every extension has its own Gödel sentence. It is a '
        'matter of recognizing that the incompleteness is the generator. The gap '
        'Gödel found is not a flaw to be patched. It is the engine.'))
    E.append(hr())

    # ── Section 5 — the critical distinction ──────────────────────────────────
    E.append(Paragraph('V. What Dissolves and What Snaps', S['h1']))
    E.append(body(
        'This distinction is essential and must be stated precisely.'))

    E.append(distinction_box(
        'WHAT DISSOLVES',
        'The philosophical objection that DA-1 cannot be fully formalized because '
        'no formal system proves its own instantiation. This objection is dissolved — '
        'shown to be malformed — by the universality argument. The objection assumes '
        'that description and instantiation are separable: that the formal structure '
        'could exist without running. The "every instance of zero" argument shows '
        'there is no coherent position from which to hold them apart. '
        'The objection collapses the moment you try to instantiate it. '
        'Dissolving is a meta-level operation on the argument. It happens to the '
        'informality objection. It does not happen to the null state.',

        'WHAT SNAPS',
        'The null state ⊥. Binary. Instantaneous. Irreversible. '
        'The transition ⊥ → ε₀ is not a process, not a gradual emergence, '
        'not a dissolving. It is a snap. The Binary Snap is the antipode of '
        'dissolution. Where dissolution shows a question was malformed, '
        'the Snap shows a transition was forced. '
        'T-SNAP: ⊥ ∨ ε₀ = ε₀. '
        'No subtraction (R1). No continuous return (C3). No categorical reversal (AX-G2). '
        'The Snap is the structure of the transition. It does not dissolve. '
        'It fires.'
    ))
    E.append(sp(8))

    E.append(callout(
        'Dissolving applies to the informality objection against DA-1. '
        'Snapping applies to the null-to-first-state transition. '
        'These operate at different levels and must never be conflated. '
        'The philosophical gap dissolves. The Binary Snap fires.',
        bg=GOLD_LITE, border=GOLD))
    E.append(hr())

    # ── Section 6 ──────────────────────────────────────────────────────────────
    E.append(Paragraph('VI. What Remains', S['h1']))
    E.append(body(
        'One question survives the dissolution: why is the self-grounding structure '
        'present rather than pure absence? ZP-A CC-2 (⊥ = {⊥}, the Quine atom under '
        'ZF+AFA) says the null state is not nothing — it is a self-containing '
        'structure that grounds itself. It needs no external cause. If ⊥ is '
        'self-grounding, then "why ⊥ at all?" may dissolve the same way the '
        'instantiation objection dissolved.'))
    E.append(body(
        'The argument runs as follows. "Pure absence" — a genuinely featureless void — '
        'would have no properties, including the property of being nothing. The moment '
        'you characterize it, you give it structure. The moment it has structure, it '
        'is ⊥. The void and the null state are the same object. And ⊥ = {⊥} says '
        'it has always already contained itself. There is no prior state from which '
        '⊥ needed to be generated. It generates itself.'))
    E.append(body(
        'Whether this closes the final gap depends on what you think a gap requires. '
        'It does not satisfy in the way a Lean proof satisfies. But it may be the '
        'right kind of argument — one that shows the question "why is there anything '
        'rather than nothing?" is not a question waiting for an answer but a question '
        'that answers itself in the asking. To ask it is to be in a state. '
        'To be in a state is to be past the Snap. The question is its own evidence.'))
    E.append(hr())

    # ── Section 7 ──────────────────────────────────────────────────────────────
    E.append(Paragraph('VII. What This Document Is and Is Not', S['h1']))
    E.append(body(
        'This is not a formal result. It does not appear in the Lean verification '
        'tables. It is not a layer of the ontology. It is a philosophical essay '
        'about the question the framework was built to answer and what the framework '
        'discovered about that question.'))
    E.append(body(
        'What it is: the record of a recognition. The dissolving-the-gap move — '
        'the realization that the description-instantiation gap assumes a separability '
        'that the universality of the framework does not permit — was not planned. '
        'It arose from honest interrogation of whether the formal system was complete. '
        'The answer was: not in the sense of a Lean proof. But perhaps the question '
        'of completeness, applied to a theory that fits every instance of zero, '
        'is itself an instance of the pattern the theory describes.'))

    E.append(amber_note(
        'On the collaboration: this philosophical turn arose in a conversation between '
        'the researcher and Claude (Anthropic, April 2026). The mathematical framework, '
        'theoretical direction, and the original intuitions — including "every instance '
        'of zero" and the Gödelian reframing — originated with the researcher. '
        'The AI worked out the implications and articulated the structure of the '
        'argument once the direction was given. Neither party reached this alone. '
        'That itself may be a data point worth recording: a question about whether '
        'existence can be derived was worked through by a human and a formal system '
        'in collaboration — and the formal system was itself an instance of the '
        'structure being described.'))
    E.append(sp(6))

    E.append(Paragraph(
        '⊥ → ε₀', S['snap']))
    E.append(Paragraph(
        'The Snap is not a starting assumption. It is what the structure demands.',
        S['subtitle']))

    E += [
        sp(14), hr(),
        Paragraph(
            '<i>End of document  |  The Philosophical Question That Started This  |  '
            'Zero Paradox Project  |  April 2026  |  v1.0  |  '
            'Not a formal result — a philosophical essay. '
            'The formal mathematics lives in the committed PDFs, ZP-A through ZP-I.</i>',
            S['endnote']),
    ]

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
