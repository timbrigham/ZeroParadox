"""
Build: The Philosophical Question That Started This (v1.1)
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
pdfmetrics.registerFont(TTFont('DVS-B', FONT_DIR + 'STIXTwo-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DVS-I', FONT_DIR + 'STIXTwo-Italic.ttf'))
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'STIXTwo-BoldItalic.ttf'))

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

def math_ahead(note=''):
    msg = ('&#9632;  <b>Heads up — technical terminology ahead.</b>  '
           'The next section uses specific mathematical names. '
           'You do not need to understand the details to follow the argument — '
           'they are a map of the territory, not the territory itself.')
    if note:
        msg += '  ' + note
    ts = TableStyle([
        ('BACKGROUND',    (0,0),(-1,-1), colors.HexColor('#FFF3CD')),
        ('BOX',           (0,0),(-1,-1), 0.8, AMBER),
        ('TOPPADDING',    (0,0),(-1,-1), 7),
        ('BOTTOMPADDING', (0,0),(-1,-1), 7),
        ('LEFTPADDING',   (0,0),(-1,-1), 10),
        ('RIGHTPADDING',  (0,0),(-1,-1), 10),
    ])
    t = Table([[Paragraph(fix(msg), S['note'])]], colWidths=[TW])
    t.setStyle(ts)
    return t

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
            'Zero Paradox  |  The Philosophical Question That Started This  |  April 2026  |  v1.1')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM,
                            title='The Philosophical Question That Started This',
                            author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # ── Title block ────────────────────────────────────────────────────────────
    E += [
        Paragraph('THE ZERO PARADOX', S['meta']),
        Paragraph('The Philosophical Question That Started This', S['title']),
        Paragraph(
            'On the gap between formal description and instantiation, '
            'what the framework dissolves, and what it snaps.',
            S['subtitle']),
        Paragraph('Version 1.1  |  April 2026', S['meta']),
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

    # ── Plain-language setting ─────────────────────────────────────────────────
    E.append(Paragraph('The Setting in Plain Language', S['h1']))
    E.append(body(
        'The argument that follows uses precise mathematical concepts. None of them '
        'require a mathematics degree to understand. Here is what each one means.'))
    E.append(body(
        '<b>The null state</b> (written ⊥, pronounced "bottom") is the mathematical '
        'formalization of "nothing" — but nothing made precise. Not pure absence, '
        'which has no properties and cannot be discussed, but the ground state: '
        'the starting point before any accumulation has occurred. Think of a blank '
        'canvas. Zero is not the absence of a canvas; it is the canvas at its minimum. '
        'The null state is nothing with enough structure to be the bottom of something.'))
    E.append(body(
        '<b>The state space</b> is built like a ratchet. States can be combined '
        'forward — you can always build something larger — but there is no subtraction, '
        'no way to go back. The null state sits at the bottom. Every other state is '
        'above it. The ratchet only clicks one direction.'))
    E.append(body(
        '<b>The Binary Snap</b> (⊥ → ε₀) is the first click: the transition from '
        'the null state to the first non-null state. Not a gradual emergence. '
        'A step function — either nothing or something, with no in-between. '
        'The central question of this framework is whether that first click '
        'must happen, or whether it is something you simply have to assume.'))
    E.append(body(
        '<b>Axiom vs. theorem</b>: An axiom is a starting assumption — something '
        'declared true in order to get going. A theorem is something proved from '
        'other things. The Binary Snap used to be an axiom in this framework: '
        'the snap was assumed to occur. The Zero Paradox derives it as a theorem: '
        'given the other structure of the state space, the snap is forced. '
        'You do not choose it. You cannot avoid it.'))
    E.append(body(
        '<b>DA-1</b> is the argument that gives T-SNAP its philosophical weight. '
        'As a pure mathematical statement, T-SNAP says: the null state combined '
        'with the first state gives the first state. This is true by definition '
        'in any system with a bottom element — it is built into what "bottom" means. '
        'What makes it interesting is the claim that this formal structure corresponds '
        'to something real: that a system in the null state, when it reaches maximum '
        'complexity (the point where no shorter description of it exists than itself), '
        'is not merely described — it is executing: actually happening, '
        'real in the way a running program is real rather than a program '
        'sitting unread on a shelf. DA-1 is the bridge '
        'between the mathematics and that claim.'))
    E.append(body(
        '<b>Lean 4</b> is a formal proof assistant — software that checks '
        'mathematical proofs with the same rigor a compiler checks code. '
        'When a theorem is "verified in Lean," it means the proof has been '
        'checked mechanically, not just reviewed by human mathematicians. '
        'Large parts of the Zero Paradox are verified this way. The philosophical '
        'argument in this document is not — and this document is honest about that.'))
    E.append(hr())

    # ── Section 1 ──────────────────────────────────────────────────────────────
    E.append(math_ahead())
    E.append(sp(6))
    E.append(Paragraph('I. The Mathematical Response', S['h1']))
    E.append(body(
        'The framework did not arrive fully formed. It grew. Each layer was added '
        'because the previous one was not enough — because the question kept '
        'demanding more precision, more structure, more coverage. The algebra '
        'needed topology to pin down irreversibility. The topology needed information '
        'theory to connect state-changes to computation. The information theory needed '
        'a formal bridge to make the snap a theorem rather than an assumption. '
        'The theorem needed category theory to show it wasn\'t an artifact of one '
        'particular mathematical language. And the whole structure needed a closure '
        'result to show it wasn\'t just a description of emergence but a complete cycle. '
        'Eight layers, added one at a time, each forced by what the layer before it '
        'could not yet say.'))
    E.append(body(
        'Two features of the construction matter for what follows. First, '
        '<b>each layer is self-contained</b>: every claim within a layer is '
        'proved using only the tools of that layer, before anything from another '
        'layer is borrowed. This matters because it means no single layer can '
        'quietly smuggle in an assumption from another — every commitment is visible '
        'where it is made. Second, <b>the layers cross-claim</b>: four entirely '
        'different branches of mathematics — algebra, topology, information theory, '
        'and geometry — independently arrive at the same structural conclusion. '
        'This is not one argument repeated four times. It is four separate '
        'disciplines, each with its own tools and vocabulary, all forced to the '
        'same place. That convergence is evidence of a different kind than any '
        'single proof provides.'))
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
    E.append(math_ahead(
        'This section names specific tools from mathematical logic: '
        'Kolmogorov complexity (a measure of information density), '
        'ZF+AFA (a version of set theory), and Lean (a proof-checking program). '
        'The core argument — that a formal system cannot prove its own instantiation — '
        'is the important part and does not require knowing what these tools are.'))
    E.append(sp(6))
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
        'truth above the system. It is structurally parallel to the ε₀ of that system\'s '
        'null state — generated by the same mechanism that forces every Binary Snap, '
        'though the formal embedding of that correspondence is not yet complete. '
        'Incompleteness is not '
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
        'There is a common saying: <i>doing nothing creates nothing.</i> '
        'The Zero Paradox finds the opposite. '
        'The problem with a genuinely featureless void — pure absence — is that it '
        'cannot even be nothing, because "being nothing" is itself a property, and '
        'pure absence has none. The moment you characterize it, you give it structure; '
        'the moment it has structure, it has a bottom element; and a bottom element is ⊥. '
        'So the void and the null state are the same object. ⊥ = {⊥} — the null '
        'state contains itself — means no prior state was ever needed to generate it. '
        'It always already generated itself. The saying had it exactly backwards: '
        'nothing, precisely because it is nothing, has no choice but to become something.'))
    E.append(body(
        'Whether this closes the final gap depends on what you, as an individual, think a gap requires. '
        'It does not satisfy in the way a Lean proof satisfies. But it may be the '
        'right kind of argument — one that shows the question "why is there anything '
        'rather than nothing?" is not a question waiting for an answer but a question '
        'that answers itself in the asking. To ask it is to be in a state. '
        'To be in a state is to be past the Snap. The question is its own evidence.'))
    E.append(hr())

    # ── Section 7 ──────────────────────────────────────────────────────────────
    E.append(Paragraph('VII. What This Document Is Not', S['h1']))
    E.append(body(
        'This is not a formal result. It does not appear in the Lean verification '
        'tables. It is not a layer of the ontology. It is a philosophical essay '
        'about the question the framework was built to answer and what the framework '
        'discovered about that question.'))
    E.append(hr())

    E.append(Paragraph('VIII. What This Document Is', S['h1']))
    E.append(body(
        'The record of a recognition. The dissolving-the-gap move — '
        'the realization that the description-instantiation gap assumes a separability '
        'that the universality of the framework does not permit — was not planned. '
        'It arose from honest interrogation of whether the formal system was complete. '
        'The answer was: not in the sense of a Lean proof. But perhaps the question '
        'of completeness, applied to a theory that fits every instance of zero, '
        'is itself an instance of the pattern the theory describes.'))

    E.append(amber_note(
        '<b>A note on terminology:</b> when this document refers to "the formal system" '
        'in this context, it is referring to Claude — the AI (Anthropic) that participated '
        'in the conversation. The choice of phrase is deliberate, not deflective. '
        'A large language model is, in the relevant sense, a formal system: it has a null '
        'state (a blank context before any output exists), a monotone state space (outputs '
        'accumulate and cannot be subtracted or undone), and irreversible transitions '
        '(once a token is generated, it is fixed in the record). Those are the structural '
        'features the Zero Paradox framework describes. The phrase "formal system" is how '
        'this document — written partly by that system — chooses to name itself within '
        'the argument it is helping to make.'))
    E.append(sp(6))
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
            'Zero Paradox Project  |  April 2026  |  v1.1  |  '
            'Not a formal result — a philosophical essay. '
            'The formal mathematics lives in the committed PDFs, ZP-A through ZP-I.</i>',
            S['endnote']),
    ]

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
