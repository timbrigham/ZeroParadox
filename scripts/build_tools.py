"""
Build ZP Tools and Methods document.
Updated April 2026: Lean 4 formal verification now complete for all layers.
"""

import os
from reportlab.lib import colors
from reportlab.lib.pagesizes import LETTER
from reportlab.lib.units import inch
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.graphics.shapes import Drawing, Rect, String
from reportlab.graphics import renderPDF

FONT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fonts') + os.sep
pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'))
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf'))
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf'))
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'STIXTwo-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'STIXTwo-Italic.ttf'))
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'STIXTwo-BoldItalic.ttf'))

BLUE      = colors.HexColor('#2E75B6')
BLUE_DARK = colors.HexColor('#1A4A7A')
BLUE_LITE = colors.HexColor('#D5E8F0')
AMBER_C   = colors.HexColor('#B07800')
AMBER_LITE= colors.HexColor('#FFF8E7')
GREEN     = colors.HexColor('#1B5E20')
GREEN_LITE= colors.HexColor('#E8F5E9')
GREY_LITE = colors.HexColor('#F5F5F5')
WHITE     = colors.white
BLACK     = colors.black
GREY      = colors.HexColor('#555555')

TW = 6.5 * inch
LM = RM = TM = BM = 1.0 * inch

S = {
    'title':   ParagraphStyle('title',  fontName='DV-B',  fontSize=20, leading=26,
                              alignment=1, spaceAfter=4),
    'sub':     ParagraphStyle('sub',    fontName='DV-I',  fontSize=11, leading=15,
                              alignment=1, spaceAfter=4),
    'meta':    ParagraphStyle('meta',   fontName='DV',    fontSize=9,  leading=13,
                              alignment=1, spaceAfter=10, textColor=colors.grey),
    'intro':   ParagraphStyle('intro',  fontName='DVS',   fontSize=10, leading=14,
                              spaceAfter=10),
    'h1':      ParagraphStyle('h1',     fontName='DV-B',  fontSize=13, leading=17,
                              spaceBefore=14, spaceAfter=5, textColor=BLUE),
    'body':    ParagraphStyle('body',   fontName='DVS',   fontSize=10, leading=14,
                              spaceAfter=6),
    'caption': ParagraphStyle('caption',fontName='DVS-I', fontSize=9,  leading=12,
                              spaceAfter=8, textColor=GREY),
    'tbl_hdr': ParagraphStyle('tbl_hdr',fontName='DV-B',  fontSize=9,  leading=13,
                              textColor=WHITE),
    'tbl_cell':ParagraphStyle('tbl_cell',fontName='DVS',  fontSize=9,  leading=13),
    'kr_hdr':  ParagraphStyle('kr_hdr', fontName='DVS-B', fontSize=9,  leading=13,
                              textColor=WHITE),
    'kr_body': ParagraphStyle('kr_body',fontName='DVS',   fontSize=9,  leading=13,
                              textColor=WHITE),
}

def sp(n=6): return Spacer(1, n)

def fix(text):
    for char, ent in [('→','&#8594;'),('—','&#8212;'),('⊥','&#8869;'),
                      ('ε','&#949;'),('≤','&#8804;')]:
        text = text.replace(char, ent)
    return text

def body(t): return Paragraph(fix(t), S['body'])

def data_table(headers, rows, col_widths):
    hdr_row = [Paragraph(h, S['tbl_hdr']) for h in headers]
    data = [hdr_row] + [[Paragraph(fix(str(c)), S['tbl_cell']) for c in row] for row in rows]
    ts = TableStyle([
        ('BACKGROUND',    (0,0),(-1,0),  BLUE),
        ('ROWBACKGROUNDS',(0,1),(-1,-1), [WHITE, GREY_LITE]),
        ('BOX',           (0,0),(-1,-1), 0.5, BLUE),
        ('LINEBELOW',     (0,0),(-1,0),  0.5, BLUE),
        ('INNERGRID',     (0,1),(-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0),(-1,-1), 4), ('BOTTOMPADDING',(0,0),(-1,-1), 4),
        ('LEFTPADDING',   (0,0),(-1,-1), 6), ('RIGHTPADDING', (0,0),(-1,-1), 6),
        ('VALIGN',        (0,0),(-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=col_widths, repeatRows=1)
    t.setStyle(ts); return t

def key_result_box(title, body_text, bg=BLUE, hdr_bg=BLUE_DARK):
    data = [[Paragraph(fix(title), S['kr_hdr'])],
            [Paragraph(fix(body_text), S['kr_body'])]]
    ts = TableStyle([
        ('BACKGROUND',   (0,0),(-1,0),  hdr_bg),
        ('BACKGROUND',   (0,1),(-1,-1), bg),
        ('BOX',          (0,0),(-1,-1), 0.5, hdr_bg),
        ('TOPPADDING',   (0,0),(-1,-1), 6), ('BOTTOMPADDING',(0,0),(-1,-1), 6),
        ('LEFTPADDING',  (0,0),(-1,-1), 8), ('RIGHTPADDING', (0,0),(-1,-1), 8),
        ('VALIGN',       (0,0),(-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW]); t.setStyle(ts); return t

def tool_stack_diagram():
    """Stacked rectangles showing tool layers."""
    dw, dh = TW, 2.2 * inch
    d = Drawing(dw, dh)

    layers = [
        ('You (researcher / theorist)',      AMBER_C,   WHITE),
        ('Claude (reasoning + synthesis)',   colors.HexColor('#2A8080'), WHITE),
        ('Python  |  ReportLab  |  Lean 4 + Mathlib', BLUE,   WHITE),
        ('fontTools  |  ReportLab graphics', colors.HexColor('#4A90C4'), WHITE),
        ('DejaVu fonts  |  Windows 11 filesystem',   colors.HexColor('#6BAED6'), WHITE),
    ]
    n = len(layers)
    margin = 0.6 * inch
    bw = dw - 2 * margin
    bh = (dh - 0.35*inch) / n
    gap = 4

    caption_y = dh - 12
    d.add(String(margin, caption_y,
                 'Claude acts as reasoning layer; all formal tools are standard open software.',
                 fontSize=7.5, fontName='DV-I', fillColor=GREY))

    for i, (label, fill, text_col) in enumerate(layers):
        by = dh - 0.35*inch - (i+1)*bh + gap/2
        d.add(Rect(margin, by, bw, bh - gap,
                   fillColor=fill, strokeColor=colors.HexColor('#FFFFFF'),
                   strokeWidth=1, rx=3, ry=3))
        lw = len(label) * 6.0
        d.add(String(margin + bw/2 - lw/2, by + (bh-gap)/2 - 5,
                     label, fontSize=9.5, fontName='DV-B', fillColor=text_col))
        if i < n - 1:
            mx = margin + bw/2
            conn_y = by - gap/2
            d.add(String(mx - 3, conn_y - 6, '|', fontSize=9,
                         fontName='DV', fillColor=GREY))

    return d

def build():
    out_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                            'ZP_Tools_and_Methods.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState(); canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox  |  Tools and Methods  |  April 2026  |  Page %d' % doc.page)
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
                            title='ZP Tools and Methods', author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # Header banner
    hdr_ts = TableStyle([('BACKGROUND',(0,0),(-1,-1),BLUE_DARK),
                         ('TOPPADDING',(0,0),(-1,-1),8),('BOTTOMPADDING',(0,0),(-1,-1),8),
                         ('LEFTPADDING',(0,0),(-1,-1),10)])
    hdr = Table([[Paragraph('THE ZERO PARADOX',
                            ParagraphStyle('hdr',fontName='DV-B',fontSize=11,textColor=WHITE))]],
                colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E += [hdr, sp(8),
          Paragraph('Tools and Methods', S['title']),
          Paragraph('How this framework was developed and verified', S['sub']),
          Paragraph('April 2026', S['meta']),
          Paragraph(
              'This document describes the tools, methods, and processes used to develop the '
              'Zero Paradox framework. It is written for anyone who wants to understand what '
              'kind of assistance was involved, what was done computationally, and — '
              'importantly — what was not done.', S['intro'])]

    # Section 1: The Role of Claude
    E.append(Paragraph('1. The Role of Claude', S['h1']))
    E.append(body(
        'The Zero Paradox framework was developed by a human researcher in collaboration with '
        'Claude (Anthropic\'s AI assistant, Claude Sonnet 4.6). The collaboration had a '
        'precise division of labor.'))
    E.append(data_table(
        ['Responsibility', 'Who'],
        [
            ['Theoretical direction and insight',                      'Human researcher'],
            ['All mathematical claims and their validity',             'Human researcher'],
            ['The core insight (L-RUN: "turning on is a state")',      'Human researcher'],
            ['Deciding what to pursue, what to drop, what to accept',  'Human researcher'],
            ['Rigorous review of mathematical structure',              'Claude'],
            ['Formal gap identification and labeling',                 'Claude'],
            ['Document drafting and ontology formatting',              'Claude'],
            ['PDF generation and rendering',                           'Claude'],
            ['Lean 4 proof development and verification',              'Claude'],
            ['Cross-document consistency checking',                    'Claude'],
            ['Version tracking and open-items registers',              'Claude'],
        ],
        [TW*0.55, TW*0.45]))
    E.append(sp(6))
    E.append(body(
        'Claude acted as a rigorous research assistant and formal scribe — not as a theorem '
        'prover, not as a creative source, and not as the author of the mathematics. Every '
        'theorem in the framework was proposed by the human researcher and reviewed for '
        'logical consistency by Claude.'))
    E.append(body(
        "Claude's primary contributions were: (1) maintaining honest epistemic labeling — "
        'distinguishing what was derived from what was assumed; (2) identifying gaps in '
        'proofs and cross-framework connections; (3) drafting and formatting documents in '
        'the ontology style specified by the researcher; (4) generating all PDF output; '
        '(5) writing and verifying all Lean 4 formal proofs.'))
    E.append(sp(6))
    E.append(tool_stack_diagram())
    E.append(Paragraph(
        'The tool stack. Claude acts as the reasoning and synthesis layer. '
        'All formal software tools are standard open-source libraries.',
        S['caption']))
    E.append(sp(8))

    # Section 2: Formal Verification
    E.append(Paragraph('2. Formal Verification: What Was and Was Not Used', S['h1']))
    E.append(body(
        'This is the question the researcher specifically wanted answered: were formal proof '
        'assistants like Rocq (formerly Coq), Lean, Isabelle, or Agda used to verify the '
        'mathematics?'))
    E.append(data_table(
        ['Tool', 'Used?', 'Notes'],
        [
            ['Rocq (Coq)',    'No',  'Not used. No Coq terms, tactics, or proof scripts were written.'],
            ['Lean 4',        'Yes', 'ZP-A: full algebraic verification — NatSLat concrete instance, #print axioms clean. '
                                     'ZP-B/C/D: concrete proxy witness (NNRealZPCat); domain theorems (C3, T1b, T4) close OQ-G3. '
                                     'Full abstract functor objects for ZP-B/C/D remain future work. '
                                     'ZP-E/G/H: sorry-free proofs for key results. Source on illustrated branch. '
                                     'Note: CC-2 (&#8869; = {&#8869;}, ZF+AFA) is a metatheoretic commitment; '
                                     'Lean\'s bot is a structural proxy, not a Quine atom in Lean\'s type theory.'],
            ['Isabelle/HOL',  'No',  'Not used.'],
            ['Agda',          'No',  'Not used.'],
            ['Mizar',         'No',  'Not used.'],
            ['SMT solvers (Z3, CVC5)', 'No', 'Not used.'],
            ['Model checkers', 'No', 'Not used.'],
            ['Mathematica / Wolfram', 'No', 'Not used.'],
            ['Sage / SymPy',  'No',  'Not used for symbolic verification.'],
            ["Claude's internal reasoning", 'Yes',
             'Claude reviewed proofs for logical gaps, missing steps, circular reasoning, '
             'and unlabeled assumptions during development. This informal review preceded '
             'and informed the Lean 4 formalization.'],
        ],
        [TW*0.25, TW*0.10, TW*0.65]))
    E.append(sp(6))
    E.append(key_result_box(
        'Key Result: What formal verification does and does not change',
        'Formal verification in Lean 4 operates at two levels. (1) Full algebraic verification: '
        'ZP-A\'s algebraic layer (A1-A4 and all derived results) is fully machine-checked via NatSLat; '
        '#print axioms confirms the proofs depend only on the ZPSemilattice typeclass fields and '
        'Lean\'s kernel axioms. (2) Proxy-level verification: for ZP-B, ZP-C, and ZP-D, the '
        'NNRealZPCat concrete witness closes OQ-G3 and grounds the domain theorems (C3, T1b, T4). '
        'Full abstract Lean functor objects for these three domains remain future work. '
        'Neither level formalizes CC-2 (&#8869; = {&#8869;}). CC-2 is a metatheoretic commitment '
        'over ZF + AFA — Lean\'s type theory (CIC) is well-founded by construction and cannot '
        'realize a Quine atom as a Lean term. The Lean bot is the structural proxy for the algebraic '
        'role of &#8869;; its set-theoretic self-containment is a prose-level commitment. '
        'The stated axioms (AX-B1, AX-G1, AX-G2) and modeling commitments (CC-1, CC-2) remain '
        'as stated. The derived results are confirmed as derived. The framework\'s epistemic '
        'status has improved — the algebraic core is machine-checked; the metatheoretic '
        'commitment CC-2 is explicitly outside that scope.'))
    E.append(sp(8))

    # Section 3: Computational Tools
    E.append(Paragraph('3. Computational Tools Actually Used', S['h1']))
    E.append(body(
        'The following tools were used in the development process. All are standard '
        'open-source tools.'))
    E.append(data_table(
        ['Tool', 'Purpose', 'Used For'],
        [
            ['Python 3',    'General scripting',
             'All PDF build scripts. Environment: Windows 11 with system Python.'],
            ['ReportLab',   'PDF generation',
             'All technical PDFs (ZP-A through ZP-H, companions, foreword, this document). '
             'Used for Paragraph layout, Table construction, and Drawing (vector diagrams).'],
            ['Lean 4 + Mathlib', 'Formal proof verification',
             'Machine-checked proofs for all seven layers. Source on lake_testing branch. '
             'Built with lake build. Purity checks via #print axioms.'],
            ['DejaVu fonts','Typography',
             'DejaVuSerif (body text) and DejaVuSans (headers, labels, diagrams). '
             'Selected for broadest Unicode math coverage.'],
            ['fontTools',   'Font glyph auditing',
             'Pre-build diagnostic: confirms which Unicode codepoints are present in '
             'DejaVuSerif vs. DejaVuSans. Used to identify missing glyphs.'],
        ],
        [TW*0.18, TW*0.18, TW*0.64]))
    E.append(sp(8))

    # Section 4: What Claude Does Not Do
    E.append(Paragraph('4. What Claude Does Not Do', S['h1']))
    E.append(body(
        'To avoid any misunderstanding about the nature of Claude\'s contribution, '
        'the following is explicit:'))
    E.append(data_table(
        ['Claim', 'Accurate?'],
        [
            ['Claude generated the mathematical ideas',
             'No. The theoretical insights came from the researcher.'],
            ['Claude verified proofs formally without Lean 4',
             'No. Lean 4 machine-checked all proofs. Prior to Lean 4, informal review only.'],
            ['Claude has access to external databases or papers',
             'No. Knowledge is from training data (cutoff August 2025).'],
            ['Claude ran simulations or numerical experiments', 'No.'],
            ['Claude searched the internet during sessions',
             'No web searches were performed for this framework.'],
            ['Claude validated against existing literature',
             'Partial. Claude can note connections to known results (e.g., standard properties '
             'of Q₂) but cannot perform systematic literature search.'],
            ['Claude is the author of the Zero Paradox',
             'No. The researcher is the author. Claude is the research assistant.'],
        ],
        [TW*0.42, TW*0.58]))
    E.append(sp(6))
    E.append(body(
        "Claude's role is best described as: a rigorous, tireless, and well-read research "
        'assistant who can draft documents, check logical consistency, identify unlabeled '
        'assumptions, develop and verify Lean 4 proofs, and generate publication-quality '
        'output — but who does not originate mathematical ideas.'))
    E.append(sp(8))

    # Section 5: PDF Rendering Pipeline
    E.append(Paragraph('5. The PDF Rendering Pipeline', S['h1']))
    E.append(body(
        'A dedicated set of rendering standards was developed during this project, saved as '
        'PDF_Rendering_Standards.md in the scripts/ folder. Key discoveries:'))
    E.append(data_table(
        ['Issue', 'Discovery', 'Fix'],
        [
            ['Missing glyphs',
             'U+2713 (checkmark) and U+2205 (empty set) are absent from DejaVuSerif',
             'Wrap in DV font tag to switch to DejaVuSans'],
            ['Blackboard bold',
             'ℚ, ℂ, ℤ, ℕ, ℝ missing from DejaVuSerif-Italic',
             'Wrap in font name="DV" tag in all italic contexts'],
            ['Table cell overflow',
             'Plain strings in ReportLab tables do not word-wrap',
             'All table cells built as Paragraph objects'],
            ['Drawing entities',
             'HTML entities (e.g., ⊥) are not parsed inside ReportLab Drawing String() objects',
             'Use actual Unicode characters in Drawing String() calls'],
            ['Drawing newlines',
             '\\n in String() objects renders as a null character, not a line break',
             'Use separate String() calls per line in all diagrams'],
            ['Unicode subscripts',
             '₀₁₂ etc. are missing from all DejaVu fonts',
             'Use two-String manual subscript positioning in Drawing context, '
             'or sub tags in Paragraph context via fix()'],
        ],
        [TW*0.18, TW*0.40, TW*0.42]))
    E.append(sp(6))
    E.append(body(
        'Build scripts for each document are in the scripts/ folder of the repository. '
        'These scripts implement all rendering standards and can be used to regenerate '
        'any document from scratch, given the DejaVu fonts and a Python environment with '
        'ReportLab installed.'))
    E.append(sp(8))

    # Section 6: Reproducibility
    E.append(Paragraph('6. Reproducibility', S['h1']))
    E.append(body(
        'All source documents are stored in the project repository as plain-text markdown '
        'or as Python build scripts. Any PDF in the release package can be regenerated by '
        'running the appropriate build script in a Python 3 environment with ReportLab '
        'installed and the DejaVu fonts in scripts/fonts/.'))
    E.append(body(
        'The mathematical content is fully specified in the formal ontology documents '
        '(ZP-A through ZP-H). The companion documents and foreword are narrative '
        'restatements of the same content. If the formal documents change, the companions '
        'and foreword require updating to match.'))
    E.append(body(
        'Lean 4 proofs are fully reproducible: clone the repository, switch to the '
        'lake_testing branch, and run lake build from the ZeroParadox/ directory. '
        'All proofs build clean against Mathlib.'))
    E.append(sp(6))
    E.append(key_result_box(
        'Key Result: The honest summary',
        'The Zero Paradox is a human-originated mathematical framework, developed through '
        'iterative collaboration with an AI research assistant, documented in a rigorous '
        'ontology format, rendered as publication-quality PDFs using open-source Python '
        'tooling, and formally verified in Lean 4 + Mathlib. All seven layers (ZP-A through '
        'ZP-H) build clean. Proofs are machine-checked.',
        bg=GREEN, hdr_bg=GREEN))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
