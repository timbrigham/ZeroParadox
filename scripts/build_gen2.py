"""
Zero Paradox — Generation 2: Applications and Open Problems PDF Builder
Version 1.0 | April 2026
Covers: Arrow of Time, Fine-Tuning, Unreasonable Effectiveness of Mathematics,
        Why Something Rather Than Nothing, Skolem / Set-Theoretic Independence
Follows all rules in pdf rendering standards.md.
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

# ── 1. FONTS ──────────────────────────────────────────────────────────────────
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
FONT_DIR   = os.path.join(SCRIPT_DIR, 'fonts') + os.sep

print(f'[build_gen2] SCRIPT_DIR: {SCRIPT_DIR}')
print(f'[build_gen2] FONT_DIR:   {FONT_DIR}')
print('[build_gen2] Registering fonts...')
pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'));          print('  DV ok')
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'));     print('  DV-B ok')
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf')); print('  DV-I ok')
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf')); print('  DV-BI ok')
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'STIXTwo-Regular.ttf'));          print('  DVS ok')
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'STIXTwo-Bold.ttf'));    print('  DVS-B ok')
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'STIXTwo-Italic.ttf')); print('  DVS-I ok')
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'STIXTwo-BoldItalic.ttf')); print('  DVS-BI ok')
print('[build_gen2] Fonts registered.')

# ── 2. COLORS ─────────────────────────────────────────────────────────────────
BLUE      = colors.HexColor('#2E75B6')
BLUE_LITE = colors.HexColor('#D5E8F0')
GREY_LITE = colors.HexColor('#F5F5F5')
GREEN     = colors.HexColor('#2E7D32')
GREEN_LITE= colors.HexColor('#E8F5E9')
AMBER_LITE= colors.HexColor('#FFF8E7')
AMBER     = colors.HexColor('#B07800')
RED_LITE  = colors.HexColor('#FFEBEE')
WHITE     = colors.white

# ── 3. GEOMETRY ───────────────────────────────────────────────────────────────
TW = 6.5 * inch
LM = RM = TM = BM = 1.0 * inch

# ── 4. STYLES ─────────────────────────────────────────────────────────────────
S = {
    'title':   ParagraphStyle('title',   fontName='DV-B',  fontSize=18, leading=24,
                              spaceAfter=6, alignment=1),
    'sub':     ParagraphStyle('sub',     fontName='DV-I',  fontSize=11, leading=15,
                              spaceAfter=4, alignment=1),
    'h1':      ParagraphStyle('h1',      fontName='DV-B',  fontSize=13, leading=18,
                              spaceBefore=14, spaceAfter=5, textColor=BLUE),
    'h2':      ParagraphStyle('h2',      fontName='DV-B',  fontSize=11, leading=15,
                              spaceBefore=10, spaceAfter=4, textColor=BLUE),
    'body':    ParagraphStyle('body',    fontName='DVS',   fontSize=10, leading=14,
                              spaceAfter=6),
    'bodyI':   ParagraphStyle('bodyI',   fontName='DVS-I', fontSize=10, leading=14,
                              spaceAfter=6),
    'label':   ParagraphStyle('label',   fontName='DV-B',  fontSize=9,  leading=13,
                              textColor=WHITE),
    'cell':    ParagraphStyle('cell',    fontName='DVS',   fontSize=9,  leading=13),
    'cellB':   ParagraphStyle('cellB',   fontName='DVS-B', fontSize=9,  leading=13),
    'cellI':   ParagraphStyle('cellI',   fontName='DVS-I', fontSize=9,  leading=13),
    'note':    ParagraphStyle('note',    fontName='DVS-I', fontSize=9,  leading=13,
                              spaceAfter=4),
    'green':   ParagraphStyle('green',   fontName='DVS-B', fontSize=10, leading=14,
                              spaceAfter=6, textColor=GREEN),
}

# ── 5. HELPERS ────────────────────────────────────────────────────────────────
def sp(n=6):  return Spacer(1, n)
def hr():     return HRFlowable(width='100%', thickness=0.5,
                                color=colors.HexColor('#AAAAAA'),
                                spaceAfter=6, spaceBefore=2)

def fix(text):
    sub_map = {'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4',
               '₅':'5','₆':'6','₇':'7','₈':'8','₉':'9',
               'ₙ':'n','ₖ':'k'}
    for ch, rep in sub_map.items():
        text = text.replace(ch, f'<sub>{rep}</sub>')
    replacements = [
        ('⊥','&#8869;'),('∨','&#8744;'),('→','&#8594;'),('≠','&#8800;'),
        ('∈','&#8712;'),('∀','&#8704;'),('∃','&#8707;'),('∞','&#8734;'),
        ('ε','&#949;'),('≤','&#8804;'),('≥','&#8805;'),('—','&#8212;'),
        ('✓','<font name="DV">&#10003;</font>'),
        ('∅','<font name="DV">&#8709;</font>'),
    ]
    for char, ent in replacements:
        text = text.replace(char, ent)
    return text

def body(text, style='body'):
    return Paragraph(fix(text), S[style])

def callout(text, bg=BLUE_LITE, border=BLUE):
    data = [[Paragraph(fix(text), S['bodyI'])]]
    t = Table(data, colWidths=[TW - 0.4*inch])
    t.setStyle(TableStyle([
        ('BOX',          (0,0),(-1,-1), 1.0, border),
        ('BACKGROUND',   (0,0),(-1,-1), bg),
        ('TOPPADDING',   (0,0),(-1,-1), 10),
        ('BOTTOMPADDING',(0,0),(-1,-1), 10),
        ('LEFTPADDING',  (0,0),(-1,-1), 14),
        ('RIGHTPADDING', (0,0),(-1,-1), 14),
    ]))
    return t

def case_header(title, fit, status_bg=BLUE_LITE, status_border=BLUE):
    data = [
        [Paragraph(fix(title), S['label']),
         Paragraph(fix(fit),   S['label'])],
    ]
    t = Table(data, colWidths=[TW*0.70, TW*0.30])
    t.setStyle(TableStyle([
        ('BACKGROUND',   (0,0),(-1,-1), BLUE),
        ('TOPPADDING',   (0,0),(-1,-1), 6),
        ('BOTTOMPADDING',(0,0),(-1,-1), 6),
        ('LEFTPADDING',  (0,0),(-1,-1), 8),
        ('RIGHTPADDING', (0,0),(-1,-1), 8),
        ('VALIGN',       (0,0),(-1,-1), 'MIDDLE'),
    ]))
    return t

def data_table(headers, rows, col_widths):
    hdr = [Paragraph(fix(h), S['label']) for h in headers]
    data = [hdr] + [[Paragraph(fix(str(c)), S['cell']) for c in row] for row in rows]
    ts = TableStyle([
        ('BACKGROUND',    (0,0),(-1,0),  BLUE),
        ('ROWBACKGROUNDS',(0,1),(-1,-1), [WHITE, GREY_LITE]),
        ('BOX',           (0,0),(-1,-1), 0.5, BLUE),
        ('LINEBELOW',     (0,0),(-1,0),  0.5, BLUE),
        ('INNERGRID',     (0,1),(-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0),(-1,-1), 4),
        ('BOTTOMPADDING', (0,0),(-1,-1), 4),
        ('LEFTPADDING',   (0,0),(-1,-1), 6),
        ('RIGHTPADDING',  (0,0),(-1,-1), 6),
        ('VALIGN',        (0,0),(-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=col_widths, repeatRows=1)
    t.setStyle(ts)
    return t

def make_doc(path):
    def footer(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(
            LETTER[0]/2, 0.6*inch,
            f'Zero Paradox: Generation 2 — Applications and Open Problems  |  '
            f'April 2026  |  Page {doc.page}')
        canvas.restoreState()
    return SimpleDocTemplate(path, pagesize=LETTER,
                             leftMargin=LM, rightMargin=RM,
                             topMargin=TM, bottomMargin=BM,
                             onFirstPage=footer, onLaterPages=footer)


def build_gen2(out_path):
    print(f'[build_gen2] Output: {out_path}')
    doc = make_doc(out_path)
    E = []

    # ── TRANSPARENCY NOTICE ───────────────────────────────────────────────────
    print('[build_gen2] Transparency notice...')
    E += [
        sp(12),
        callout(
            '<b>A note on transparency:</b> This document lives in the public repository '
            'but is intentionally unlinked from the main project index. The Generation 1 '
            'framework (ZP-A through ZP-H) is now formally complete and machine-verified '
            '(Lean 4 + Mathlib, April 2026). Generation 2 applications remain speculative '
            '&#8212; the formal foundation is certified, but the bridges from that foundation '
            'to the problems addressed here are works in progress. '
            'You are seeing this in its unvarnished development state &#8212; I believe in '
            'being open about the process.',
            bg=AMBER_LITE, border=AMBER),
        sp(10),
    ]

    # ── TITLE ─────────────────────────────────────────────────────────────────
    print('[build_gen2] Title block...')
    E += [
        sp(6),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('Generation 2: Applications and Open Problems', S['sub']),
        Paragraph('Version 1.0 | April 2026', S['bodyI']),
        sp(6),
        body(
            'The Generation 1 framework — ZP-A through ZP-H — establishes a single central '
            'result: the Binary Snap (&#8869; &#8594; &#949;<sub>0</sub>) is a theorem, not an axiom. '
            'That result is derived across seven independent mathematical disciplines and is '
            'formally closed. Generation 2 asks what that result does to problems that have '
            'remained open in physics, mathematics, and philosophy. '
            'This document is not a formal proof document. It is a structured account of '
            'where the framework reaches, what it requires to reach there, and how well it fits.'),
        sp(4), hr(),
    ]

    # ── I. WORKING ASSUMPTIONS ────────────────────────────────────────────────
    print('[build_gen2] Section I: Working Assumptions...')
    E.append(Paragraph('I. Working Assumptions', S['h1']))
    E.append(body(
        'The Generation 1 framework is instantiation-independent — it makes no physical '
        'claims without additional commitments. The following assumptions are required for '
        'the physical and philosophical applications in this document. They are simplifications. '
        'Each is stated explicitly so that any claim can be traced back to what it requires.'))

    assump_rows = [
        ['A-1', 'The Big Bang corresponds to &#949;<sub>0</sub> — the first atomic state, the forced '
                'transition at P<sub>0</sub>. The Binary Snap is the structural account of the origin event.',
         'Simplification — not proven by framework; consistent with it'],
        ['A-2', 'Heat death corresponds to the asymptotic approach to &#8869; from outside — '
                'zero available energy as the informational singularity approached but never '
                'formally reached in finite time.',
         'Simplification — consistent with both framework and current cosmological models'],
        ['A-3', 'The physical universe is a mathematically describable system.',
         'Required — framework is silent on systems that are not'],
        ['A-4', 'The instantiation frame is the physical universe itself.',
         'Required — DA-3 frame-dependence must be anchored to something'],
    ]
    E.append(data_table(
        ['Label', 'Statement', 'Status'],
        assump_rows,
        [TW*0.08, TW*0.57, TW*0.35]
    ))
    E.append(sp(8))

    # ── II. CASE 1 — ARROW OF TIME ────────────────────────────────────────────
    print('[build_gen2] Section II: Arrow of Time...')
    E.append(Paragraph('II. The Arrow of Time', S['h1']))
    E.append(case_header(
        'Case 1 — The Arrow of Time',
        'Fit: Very Strong'))
    E += [
        sp(4),
        body('<b>The problem.</b> The arrow of time is genuinely unsolved in physics. '
             'Not in the sense that we do not observe it — we clearly do. Unsolved in the '
             'sense that no one has successfully derived it from first principles. '
             'The fundamental equations of physics — General Relativity, quantum mechanics, '
             'classical mechanics — are time-symmetric. The asymmetry is imported from '
             'thermodynamics, assumed, or treated as a brute fact. That has been an open '
             'problem for over a century.'),
        body('<b>What the framework provides.</b> The arrow of time is an instance of the '
             'Zero Paradox under stated conditions A-1, A-2, and A-3. Under those conditions, '
             'the arrow of time is not a separate phenomenon requiring separate explanation. '
             'It is what the Zero Paradox looks like when instantiated in a system with '
             'those boundary conditions. The forward-only direction falls out automatically:'),
    ]
    E.append(data_table(
        ['Source', 'Contribution to Arrow of Time'],
        [
            ['ZP-A Monotonicity', 'State sequences are forward-only. No subtraction operator. '
                                   'No return to a lower state. Derived, not assumed.'],
            ['ZP-B C3', 'Topological irreversibility. No continuous path in Q<sub>2</sub> '
                        'returns to 0 from any non-zero element. Derived from clopen structure.'],
            ['AX-G2', 'Source asymmetry. No morphism returns to the initial object. '
                      'Categorical irreversibility is structural, not imported.'],
        ],
        [TW*0.20, TW*0.80]
    ))
    E += [
        sp(6),
        callout(
            'The arrow of time is an instance of the Zero Paradox under conditions A-1, A-2, A-3. '
            'The monotonicity, irreversibility, and source asymmetry are all derived — not assumed. '
            'This is more than physics currently has on paper for this problem.',
            bg=GREEN_LITE, border=GREEN),
        sp(6),
        body('<b>What this framing does and does not claim.</b> '
             '"The arrow of time is an instance of the Zero Paradox under stated conditions" '
             'is a structural claim the framework formally supports. '
             '"Proof of the arrow of time" would require a formal bridge document mapping '
             'the semilattice\'s monotonicity to thermodynamic entropy increase — that bridge '
             'is not yet written and is the primary target of the next stage of this work.'),
        body('<b>Required assumptions:</b> A-1, A-2, A-3.'),
        body('<b>Gap:</b> Formal thermodynamic bridge document. Probably a significant paper '
             'in its own right.'),
    ]

    # ── III. CASE 2 — WHY SOMETHING RATHER THAN NOTHING ──────────────────────
    print('[build_gen2] Section III: Why Something Rather Than Nothing...')
    E.append(Paragraph('III. Why Is There Something Rather Than Nothing?', S['h1']))
    E.append(case_header(
        'Case 2 — Why Something Rather Than Nothing?',
        'Fit: Very Strong'))
    E += [
        sp(4),
        body('<b>The problem.</b> Leibniz\'s question. The most fundamental question in '
             'metaphysics and cosmology. Why does anything exist at all? Why not pure nothing? '
             'Standard answers: divine design, brute fact, the question is malformed, '
             'or no answer available.'),
        body('<b>What the framework provides.</b> T-SNAP provides a formal structural answer. '
             'Nothing (&#8869;) at the incompressibility threshold P<sub>0</sub> cannot persist. '
             'The transition to something (&#949;<sub>0</sub>) is structurally forced. '
             'The question assumes nothing is stable. The framework proves it is not. '
             '"Why something rather than nothing" is answered by showing that nothing, '
             'properly characterised, contains the conditions for its own transition.'),
        callout(
            'Nothing at P₀ cannot hold. The transition to the first atomic state is '
            'structurally forced by the properties of the null state itself — not by an '
            'external trigger, a divine agent, or a brute fact.',
            bg=GREEN_LITE, border=GREEN),
        sp(6),
        body('<b>Scope of the answer.</b> The framework answers why nothing transitions to '
             'something given the structural conditions for that transition. It does not answer '
             'why those structural conditions exist. That would be a deeper question — the one '
             'remaining path toward a fully axiom-free framework via the Imbalance Hypothesis.'),
        body('<b>Required assumptions:</b> A-3. No physical assumptions required — '
             'this operates on the mathematical structure directly.'),
        body('<b>Gap:</b> Why the structural conditions themselves exist. '
             'Addressed by the Imbalance Hypothesis (TQ-IH proof path) — open.'),
    ]

    # ── IV. CASE 3 — UNREASONABLE EFFECTIVENESS ───────────────────────────────
    print('[build_gen2] Section IV: Unreasonable Effectiveness...')
    E.append(Paragraph('IV. The Unreasonable Effectiveness of Mathematics', S['h1']))
    E.append(case_header(
        'Case 3 — The Unreasonable Effectiveness of Mathematics',
        'Fit: Strong'))
    E += [
        sp(4),
        body('<b>The problem.</b> Physicist Eugene Wigner (1960) asked why mathematics — '
             'developed in the abstract, often with no physical application in mind — '
             'turns out to describe physical reality with extraordinary precision. '
             'Complex numbers, non-Euclidean geometry, group theory — invented as pure '
             'mathematics, later found to be exactly the right tool for physics. '
             'Standard answer: coincidence, selection bias, or no answer.'),
        body('<b>What the framework provides.</b> If physical reality and mathematics both '
             'emerge from the same structural conditions at &#8869; — if they share a common '
             'foundation in the forced transition from null to first state — then they were '
             'never separate things to begin with. Mathematics works on physics not because '
             'of a lucky correspondence but because they are both expressions of the same '
             'underlying structure. The "unreasonable" effectiveness is expected.'),
        callout(
            'Mathematics and physical reality share a common foundation in the structural '
            'properties of &#8869;. Their agreement is not a coincidence — it is a consequence '
            'of common origin.',
            bg=BLUE_LITE, border=BLUE),
        sp(6),
        body('<b>Required assumptions:</b> A-1, A-3.'),
        body('<b>Gap:</b> The claim that mathematics and physics share a common foundation '
             'in &#8869; is structurally supported but not yet explicitly formalized as a '
             'theorem. Would benefit from a dedicated bridge argument.'),
    ]

    # ── V. CASE 4 — FINE-TUNING ───────────────────────────────────────────────
    print('[build_gen2] Section V: Fine-Tuning...')
    E.append(Paragraph('V. The Fine-Tuning Problem', S['h1']))
    E.append(case_header(
        'Case 4 — The Fine-Tuning Problem',
        'Fit: Medium-Strong'))
    E += [
        sp(4),
        body('<b>The problem.</b> Why are the physical constants — gravitational constant, '
             'speed of light, electron mass, and others — tuned so precisely that a universe '
             'capable of structure and life results? Even small variations in most constants '
             'produce universes with no atoms, no stars, no complexity. '
             'Standard answers: divine design, multiverse, or no answer.'),
        body('<b>What the framework provides.</b> If &#949;<sub>0</sub> is forced by structural '
             'necessity rather than chosen, the constants are not selected by an external agent. '
             'DA-3 (perspective-relative cardinality) establishes that what counts as the '
             'initial state depends on the instantiation context. The apparent "tuning" may be '
             'an artifact of measuring from inside a particular instantiation frame rather than '
             'a fact about external selection.'),
        body('<b>Required assumptions:</b> A-1, A-3, A-4. Additionally, DA-3 must be extended '
             'to cover physical constant assignment — this is not currently in the framework '
             'and would require new work.'),
        body('<b>Gap:</b> The extension of DA-3 to physical constants is not formalized. '
             'The structural argument is sound in direction; the specific mapping is open. '
             'Medium-strong fit — right direction, incomplete formalization.'),
    ]

    # ── VI. CASE 5 — SKOLEM ───────────────────────────────────────────────────
    print('[build_gen2] Section VI: Skolem...')
    E.append(Paragraph('VI. Skolem\'s Paradox and Set-Theoretic Independence', S['h1']))
    E.append(case_header(
        'Case 5 — Skolem\'s Paradox / Continuum Hypothesis Independence',
        'Fit: Strong'))
    E += [
        sp(4),
        body('<b>The problem.</b> Skolem\'s paradox: a mathematical system containing an '
             'uncountable set (like the real numbers) can also have a model where that same '
             'set appears countable — depending on which formal system you stand in. '
             'The Continuum Hypothesis — whether there is a set size between the integers '
             'and the real numbers — is independent of the standard axioms of set theory. '
             'Neither provable nor disprovable from within. '
             'Standard answer: these are just facts about formal systems. No deeper explanation.'),
        body('<b>What the framework provides.</b> DA-3 (perspective-relative cardinality) '
             'provides a structural account. What counts as the cardinality of a set depends '
             'on which instantiation frame is doing the counting. Skolem\'s paradox is not a '
             'bug — it is a structural consequence of frame-dependence. The Continuum '
             'Hypothesis is independent not because the right axiom has not been found yet, '
             'but because cardinality is genuinely relative to the instantiation context.'),
        body('<b>Required assumptions:</b> No physical assumptions required. '
             'This operates purely within the mathematical framework.'),
        body('<b>Gap:</b> Formal derivation of DA-3\'s cardinality claims is deferred (OQ-E2). '
             'The structural account is in place; the formal derivation remains pending.'),
    ]

    # ── VII. CASES THAT DON'T FIT ─────────────────────────────────────────────
    print('[build_gen2] Section VII: Cases That Don\'t Fit...')
    E.append(Paragraph('VII. Cases Outside Current Scope', S['h1']))
    E.append(body(
        'The following problems are often raised in connection with foundational frameworks. '
        'They are listed here with honest accounts of why the Zero Paradox does not currently '
        'address them — and what would be needed to change that.'))

    E.append(data_table(
        ['Problem', 'Why It Does Not Fit', 'What Would Be Needed'],
        [
            ['Hard problem of consciousness',
             'Framework is deliberately silent on subjective experience. State transitions '
             'are accounted for; whether any state is experienced is not. Intentional boundary.',
             'New machinery entirely. Not a gap — a scope decision.'],
            ['Quantum measurement problem',
             'Instantiation-relative perspective is structurally tempting but the '
             'identification requires new formal work not currently in the framework.',
             'A dedicated bridge from DA-3 to quantum decoherence / measurement. Feasible direction.'],
            ['Dark matter / dark energy',
             'Empirical gaps in physics. Framework is instantiation-independent and does '
             'not determine specific physical content.',
             'Physical instantiation of &#949;<sub>0</sub> — belongs to physics, not this framework.'],
            ['Specific values of physical constants',
             'Framework establishes constants are frame-relative but does not determine '
             'what they are in any given frame.',
             'Same as above — physical instantiation question.'],
        ],
        [TW*0.22, TW*0.42, TW*0.36]
    ))

    # ── VIII. OPEN PROBLEMS ───────────────────────────────────────────────────
    print('[build_gen2] Section VIII: Open Problems...')
    E.append(Paragraph('VIII. Open Problems and Next Steps', S['h1']))

    E.append(data_table(
        ['Item', 'Description', 'Priority'],
        [
            ['Thermodynamic bridge',
             'Formal document mapping ZP-A monotonicity to thermodynamic entropy increase, '
             'ZP-B irreversibility to second law, AX-G2 to fixed past / open future. '
             'Closes the arrow of time case fully.',
             'High'],
            ['OQ-E2',
             'Formal derivation of DA-3\'s cardinality claims deferred pending further work.',
             'Open'],
            ['Physical constant mapping',
             'Extension of DA-3 to cover physical constant assignment under a specific '
             'instantiation frame. Addresses fine-tuning formally.',
             'Medium'],
            ['Imbalance Hypothesis (TQ-IH proof)',
             'Proving that any complete self-description of &#8869; must pass through a '
             'non-zero intermediate state. Would allow AX-B1 itself to be derived — '
             'the path to a fully axiom-free framework.',
             'Longer term'],
            ['Lean 4 formal verification',
             'Complete. ZP-A through ZP-H machine-verified in Lean 4 + Mathlib, April 2026. '
             'Zero errors, zero warnings. Proof docs at proofs/ on lake_testing branch.',
             'Complete'],
        ],
        [TW*0.20, TW*0.62, TW*0.18]
    ))

    # ── IX. SUMMARY ───────────────────────────────────────────────────────────
    print('[build_gen2] Section IX: Summary...')
    E.append(Paragraph('IX. Summary', S['h1']))

    E.append(data_table(
        ['Case', 'Fit', 'Key Gap'],
        [
            ['Arrow of time', 'Very Strong',
             'Formal thermodynamic bridge document'],
            ['Why something rather than nothing', 'Very Strong',
             'Why the structural conditions themselves exist (TQ-IH path)'],
            ['Unreasonable effectiveness of mathematics', 'Strong',
             'Explicit formalization of common-origin claim'],
            ['Fine-tuning problem', 'Medium-Strong',
             'Extension of DA-3 to physical constant assignment'],
            ['Skolem\'s paradox / CH independence', 'Strong',
             'OQ-E2: formal derivation of DA-3 cardinality claims pending'],
        ],
        [TW*0.32, TW*0.18, TW*0.50]
    ))

    E += [
        sp(10),
        callout(
            'These five problems come from cosmology, philosophy of mathematics, physics, '
            'metaphysics, and mathematical logic. They have separate literatures and are '
            'usually treated as unrelated. The Zero Paradox framework touches all of them '
            'through the same mechanism: the structural properties of &#8869; and the forced '
            'transition to &#949;<sub>0</sub>. That convergence suggests these problems may share '
            'a common root — the same question asked from different angles. '
            'Solving any one of them individually would be significant. '
            'Identifying the common root is more significant still.',
            bg=BLUE_LITE, border=BLUE),
        sp(12),
        Paragraph(
            '<i>Zero Paradox Generation 2 | Applications and Open Problems | April 2026 | v1.0</i>',
            S['note']),
    ]

    print(f'[build_gen2] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_gen2] Written: {out_path}')


if __name__ == '__main__':
    repo_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    out = os.path.abspath(os.path.join(repo_root, 'ZP_Gen2_Applications.pdf'))
    build_gen2(out)
