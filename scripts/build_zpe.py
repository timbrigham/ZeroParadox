"""
Zero Paradox — ZP-E: Bridge Document PDF Builder
Version 3.9 | April 2026
v3.9: R-ε₀ reframed — remark now leads with explicit informal-analogy disclaimer; "structural
correspondence" changed to "structural analogy" throughout R-ε₀. Reviewer feedback: hedge was
buried at end of remark; readers might miss it after several paragraphs of parallel-drawing.
v3.8: DA-1 Path 2 recharacterized — from "outside Lean scope (informational bridge)" to
"foundational commitment: a missing principle, not a missing proof." No computability library
closes the gap between 'system at P₀' and 'system is running.' Forward paths: new axiom,
Chalmers' implementation notion, or ZP-PQ dissolution argument. ZP-PQ already contains the
dissolution: the description-instantiation gap assumes a separability the framework dissolves.
v3.7: DA-1 formally closed via ZP-K — KleeneStructure MachinePhase instance proved in Lean 4.
da1_closed_concrete : IsQuineAtom (bot : MachinePhase). DA-1 Path 1 (structural/AFA) and
Path 3 (computational/Kleene) now in Lean scope. Path 2 (informational bridge) remains outside
Lean scope. "Outside Lean Scope" designation removed from ZPE.lean DA-1 section.
v3.6: DA-1 Path 1 rewritten — argument direction reversed. Previously: CC-2 (⊥ = {⊥}) asserted,
then "no external interpreter" derived. Now: "nothing external to ⊥ can execute ⊥" argued first,
⊥ = {⊥} derived as the only coherent structure, ZP-J T-EXEC cited as formal verification.
CC-1 and CC-2 status updated throughout — no longer freestanding commitments; both derived via ZP-J.
v3.5: Open Items Register DA-1 status updated — "CLOSED — DP-2 (formal core); CC-2 + L-INF + AIT
(corroboration of precondition)" now matches v3.3 path-hierarchy framing.
v3.4: R-AFA minimality argument made explicit — added one sentence to "What remains
conditional" stating that ⊥ = {⊥} is uniquely minimal among AFA non-well-founded sets:
exactly one member, no internal differentiation; any extension exceeds A4's constraint.
v3.3: DA-1 path hierarchy foregrounded — added explicit framing before Paths 1–3 stating
that the three informal paths are corroboration of the precondition DP-2 formalizes, not
parallel proofs of DA-1 itself. Shrinks attack surface on Angle 1 (DA-1 doing too much work).
v3.2: Remark R-AFA added — Foundation ruled out by R3 and ZP-C L-INF; AFA identified as the
forced metatheoretic replacement rather than an arbitrary choice; CC-2 status clarified.
v3.1: Remark R-ε₀ added — notation justification for ε₀ symbol choice; structural correspondence
with the Cantor-Gentzen proof-theoretic ordinal explained.
v3.0: DP-2 (Execution Distinguishability) added — DA-1 formally grounded in TrackedOutput construction
(ZPE.lean §VI); da1_minimal_path proved axiom-free in Lean. First Lean formalization of DA-1,
conditional on DP-2. Section III (DP-2) inserted in DA-1 insert; existing III/IV/V renumbered IV/V/VI.
v2.9: DA-1 Lean scope note added — functional role carried by ZPC.l_run/tq_ih; AIT+ZF+AFA bridge
outside Lean scope (same category as ZP-A CC-2). PDF status line updated to reflect Lean scope.
v2.8: DA-1 formal bridge added: incompressibility = self-description argument (ZP-C D1 + standard AIT).
At P0, K(c1|n)/|c1| = 1 means description and execution coincide; CC-2/R3 and L-INF become corroboration.
v2.7: DA-1 upgraded from Design Principle to Derived Proposition — grounded in ZP-A CC-2 and R3.
Follows all rules in pdf rendering standards:
  - DejaVu fonts only
  - Checkmark always wrapped in <font name="DV">
  - All table cells are Paragraph objects
  - No unicode subscripts — use sub/super tags
  - US Letter, 1-inch margins, TW = 6.5 inch
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

# ── 1. FONT REGISTRATION ──────────────────────────────────────────────────────
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
FONT_DIR   = os.path.join(SCRIPT_DIR, 'fonts') + os.sep

print(f'[build_zpe] SCRIPT_DIR: {SCRIPT_DIR}')
print(f'[build_zpe] FONT_DIR:   {FONT_DIR}')
print('[build_zpe] Registering fonts...')
pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'));         print('  DV ok')
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'));    print('  DV-B ok')
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf')); print('  DV-I ok')
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf')); print('  DV-BI ok')
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'STIXTwo-Regular.ttf'));         print('  DVS ok')
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'STIXTwo-Bold.ttf'));   print('  DVS-B ok')
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'STIXTwo-Italic.ttf')); print('  DVS-I ok')
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'STIXTwo-BoldItalic.ttf')); print('  DVS-BI ok')
print('[build_zpe] Fonts registered.')

# Register STIX for ℵ glyph (U+2135, decimal 8501) — missing from DejaVu
_stix_registered = False
for _stix_path in [
    FONT_DIR + 'STIXTwo-Math.ttf',
    FONT_DIR + 'STIX-Regular.ttf',
    FONT_DIR + 'seguisym.ttf',
    r'C:\Windows\Fonts\seguisym.ttf',
    '/usr/share/fonts/opentype/stix/STIX-Regular.ttf',
    '/usr/share/fonts/truetype/stix/STIX-Regular.ttf',
]:
    if os.path.exists(_stix_path):
        try:
            pdfmetrics.registerFont(TTFont('STIX', _stix_path))
            _stix_registered = True
            print(f'  STIX ok ({_stix_path})')
            break
        except Exception as e:
            print(f'  STIX failed: {e}')
if not _stix_registered:
    print('  WARNING: STIX not found — ℵ (U+2135) will not render correctly')
ALEPH_FONT = 'STIX' if _stix_registered else 'DV'

# ── 2. COLORS ─────────────────────────────────────────────────────────────────
BLUE        = colors.HexColor('#2E75B6')
SLATE       = colors.HexColor('#455A64')
SLATE_LITE  = colors.HexColor('#ECEFF1')
GREEN_DARK  = colors.HexColor('#1B5E20')
GREY_LITE   = colors.HexColor('#F5F5F5')
WHITE       = colors.white

# ── 3. PAGE GEOMETRY ──────────────────────────────────────────────────────────
TW = 6.5 * inch
LM = RM = 1.0 * inch
TM = BM = 1.0 * inch

# ── 4. PARAGRAPH STYLES ───────────────────────────────────────────────────────
S = {
    'title':   ParagraphStyle('title',   fontName='DV-B',  fontSize=18, leading=24,
                               spaceAfter=6, alignment=1),
    'subtitle':ParagraphStyle('subtitle',fontName='DV-I',  fontSize=11, leading=15,
                               spaceAfter=4, alignment=1),
    'h1':      ParagraphStyle('h1',      fontName='DV-B',  fontSize=13, leading=18,
                               spaceBefore=14, spaceAfter=5, textColor=BLUE),
    'h2':      ParagraphStyle('h2',      fontName='DV-B',  fontSize=11, leading=15,
                               spaceBefore=10, spaceAfter=4, textColor=BLUE),
    'body':    ParagraphStyle('body',    fontName='DVS',   fontSize=10, leading=14,
                               spaceAfter=6, alignment=4),
    'bodyI':   ParagraphStyle('bodyI',   fontName='DVS-I', fontSize=10, leading=14,
                               spaceAfter=6, alignment=4),
    'li':      ParagraphStyle('li',      fontName='DVS',   fontSize=10, leading=14,
                               leftIndent=18, spaceAfter=3, alignment=4),
    'derived': ParagraphStyle('derived', fontName='DVS-B', fontSize=10, leading=14,
                               spaceAfter=6, textColor=GREEN_DARK, alignment=4),
    'label':   ParagraphStyle('label',   fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=WHITE),
    'cell':    ParagraphStyle('cell',    fontName='DVS',   fontSize=9,  leading=13),
    'cellI':   ParagraphStyle('cellI',   fontName='DVS-I', fontSize=9,  leading=13),
    'note':    ParagraphStyle('note',    fontName='DVS-I', fontSize=9,  leading=13,
                               spaceAfter=4),
    'endnote': ParagraphStyle('endnote', fontName='DVS-I', fontSize=9,  leading=13,
                               alignment=1),
}

# ── 5. HELPERS ────────────────────────────────────────────────────────────────

def sp(n=6):
    return Spacer(1, n)

def hr():
    return HRFlowable(width='100%', thickness=0.5,
                      color=colors.HexColor('#AAAAAA'),
                      spaceAfter=6, spaceBefore=2)

def fix(text):
    sub_map = {'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4',
               '₅':'5','₆':'6','₇':'7','₈':'8','₉':'9',
               'ₙ':'n','ₖ':'k','ₘ':'m','ᵢ':'i','ⱼ':'j'}
    for ch, rep in sub_map.items():
        text = text.replace(ch, f'<sub>{rep}</sub>')
    text = text.replace('✓', '<font name="DV">&#10003;</font>')
    text = text.replace('∅', '<font name="DV">&#8709;</font>')
    text = text.replace('ℵ', f'<font name="{ALEPH_FONT}">&#8501;</font>')
    replacements = [
        ('⊥','&#8869;'),('∨','&#8744;'),('∧','&#8743;'),
        ('≤','&#8804;'),('≥','&#8805;'),('≠','&#8800;'),
        ('∈','&#8712;'),('∉','&#8713;'),('⊆','&#8838;'),
        ('∀','&#8704;'),('∃','&#8707;'),('∞','&#8734;'),
        ('→','&#8594;'),('←','&#8592;'),('↔','&#8596;'),
        ('⇒','&#8658;'),('∘','&#8728;'),('—','&#8212;'),
        ('–','&#8211;'),('·','&#183;'),('×','&#215;'),
        ('−','&#8722;'),('≡','&#8801;'),('≅','&#8773;'),
        ('≇','&#8775;'),
        ('ω','&#969;'),('ö','&#246;'),
        ('ε','&#949;'),('α','&#945;'),('β','&#946;'),
        ('γ','&#947;'),('δ','&#948;'),('ι','&#953;'),
        ('τ','&#964;'),('φ','&#966;'),
        ('ℚ','&#8474;'),('ℤ','&#8484;'),('ℂ','&#8450;'),
        ('ℕ','&#8469;'),('ℝ','&#8477;'),
        ('≈','&#8776;'),('∑','&#8721;'),('¬','&#172;'),
        ('Ö','&#214;'),
    ]
    for char, entity in replacements:
        if char in text:
            text = text.replace(char, entity)
    return text

def body(text, style='body'):
    return Paragraph(fix(text), S[style])

def li(text):
    return Paragraph('&#8226;  ' + fix(text), S['li'])

def derived(text):
    return Paragraph(fix(text), S['derived'])

def bridge_box(title, rows):
    """Grey-slate header box for DA-X formal claims — bridge document style."""
    data = [[Paragraph(fix(title), S['label'])]]
    for r in rows:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  SLATE),
        ('BACKGROUND',    (0,1), (-1,-1), GREY_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, SLATE),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, SLATE),
        ('LINEBELOW',     (0,1), (-1,-2), 0.5, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW], repeatRows=1)
    t.setStyle(ts)
    return t

def data_table(headers, rows_data, col_widths):
    hdr_row = [Paragraph(fix(h), S['label']) for h in headers]
    data    = [hdr_row]
    for row in rows_data:
        data.append([Paragraph(fix(str(c)), S['cell']) for c in row])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  BLUE),
        ('ROWBACKGROUNDS',(0,1), (-1,-1), [WHITE, GREY_LITE]),
        ('BOX',           (0,0), (-1,-1), 0.5, BLUE),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, BLUE),
        ('INNERGRID',     (0,1), (-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 4),
        ('BOTTOMPADDING', (0,0), (-1,-1), 4),
        ('LEFTPADDING',   (0,0), (-1,-1), 6),
        ('RIGHTPADDING',  (0,0), (-1,-1), 6),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=col_widths, repeatRows=1)
    t.setStyle(ts)
    return t

def make_doc(path):
    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        ft = f'THE ZERO PARADOX  |  ZP-E Bridge Document v3.9  |  April 2026  |  Page {doc.page}'
        canvas.drawCentredString(LETTER[0] / 2, 0.6 * inch, ft)
        canvas.restoreState()
    return SimpleDocTemplate(
        path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title='ZP-E: Bridge Document',
        author='Zero Paradox Project',
        onFirstPage=footer_cb, onLaterPages=footer_cb,
    )


def build_zpe(out_path):
    print(f'[build_zpe] Output: {out_path}')
    doc = make_doc(out_path)
    E   = []

    print('[build_zpe] Building title block...')
    # ── TITLE BLOCK ───────────────────────────────────────────────────────────
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-E: Bridge Document', S['title']),
        Paragraph('Version 3.9 | April 2026', S['subtitle']),
        Paragraph(
            '<i>Supersedes v3.8 | v3.9: R-&#949;<sub>0</sub> reframed — remark now leads with explicit '
            'informal-analogy disclaimer; "structural correspondence" changed to "structural analogy" '
            'throughout R-&#949;<sub>0</sub>. | '
            'v3.8: DA-1 Path 2 recharacterized — from "outside Lean scope (informational bridge)" to '
            '"foundational commitment: a missing principle, not a missing proof." No computability library closes the gap '
            'between \'system at P<sub>0</sub>\' and \'system is running.\' Forward paths: new axiom, Chalmers\' implementation '
            'notion, or ZP-PQ dissolution argument. '
            'v3.7: DA-1 formally closed via ZP-K — da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase) proved in Lean 4. '
            'KleeneStructure MachinePhase instance added; Paths 1 and 3 now IN LEAN SCOPE. '
            '"Outside Lean Scope" designation removed from ZPE.lean. '
            'v3.6: DA-1 Path 1 rewritten — argument direction reversed; CC-1 and CC-2 now derived via ZP-J (no longer freestanding commitments). '
            'v3.5: DA-1 Open Items Register status updated — "CLOSED — DP-2 (formal core); CC-2 + L-INF + AIT (corroboration of precondition)" now matches v3.3 path-hierarchy framing. '
            'v3.4: R-AFA minimality explicit — &#8869; = {&#8869;} uniquely minimal among AFA non-well-founded sets; any extension exceeds A4\'s constraint. '
            'v3.3: DA-1 path hierarchy foregrounded — three informal paths framed as corroboration of DP-2\'s precondition, not parallel proofs. '
            'v3.2: Remark R-AFA added — Foundation ruled out by R3 + L-INF; AFA forced rather than chosen; CC-2 metatheoretic status clarified. '
            'v3.1: Remark R-&#949;<sub>0</sub> added — notation justification for '
            '&#949;<sub>0</sub> symbol choice; structural correspondence with Cantor-Gentzen '
            'proof-theoretic ordinal explained. '
            'v3.0: DP-2 (Execution Distinguishability) added — DA-1 formally grounded '
            'in TrackedOutput construction (ZPE.lean &#167;VI); da1_minimal_path proved axiom-free in Lean. '
            'First Lean formalization of DA-1, conditional on DP-2.</i>',
            S['note']),
        Paragraph(
            '<i>v2.9: DA-1 Lean scope note added: functional role carried by ZPC.l_run/tq_ih (proved); '
            'AIT and ZF+AFA bridge outside Lean scope — same category as ZP-A CC-2.</i>',
            S['note']),
        Paragraph(
            '<i>v2.8: DA-1 formal bridge added: incompressibility = self-description argument '
            '(ZP-C D1 + standard AIT). At P<sub>0</sub>, K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1 means description '
            'and execution coincide; CC-2/R3 and L-INF are independent corroboration of the same conclusion.</i>',
            S['subtitle']),
        Paragraph(
            '<i>v2.7: DA-1 upgraded from Design Principle to Derived Proposition — grounded in ZP-A CC-2 (&#8869; = {&#8869;}) and R3. '
            'v2.6: DA-3 candidate applications removed. '
            'v2.5: Physical analogies removed from formal sections. '
            'v2.4: R-DA2 framing corrected. '
            'v2.3: CC-1 added to T-SNAP dependency list. '
            'v2.2: DA-1 redesigned to L-INF-based Design Principle. '
            'v2.1: Adds DA-2 and DA-3.</i>',
            S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'This document is the cross-framework synthesis layer of the Zero Paradox. It imports from '
        'ZP-A (lattice algebra), ZP-B (p-adic topology), ZP-C (information theory), and ZP-D (Hilbert '
        'space state layer). It provides three formal inserts: DA-1 (Instantiation as Execution — '
        'upgraded to Derived Proposition in v2.7; in v3.0, DP-2 provides the first Lean-formalizable '
        'grounding via TrackedOutput, proved axiom-free), DA-2 (Instantiation Succession), and '
        'DA-3 (Perspective-Relative Cardinality). With DA-1 in place, AX-1 is promoted to Theorem '
        'T-SNAP. With DA-2, the directed instantiation tree is formally licensed. With DA-3, '
        'cardinality is shown to be position-dependent within the instantiation structure.'))
    E.append(body(
        'Illustrated Companion: A paired ZP-E Illustrated Companion document provides accessible '
        'explanations and visual summaries of the bridge derivations in this document. Readers new '
        'to the framework are encouraged to start with the companion.',
        style='bodyI'))
    E.append(hr())

    print('[build_zpe] Building DA-1...')
    # ── FORMAL INSERT DA-1 ────────────────────────────────────────────────────
    E += [
        Paragraph('Formal Insert DA-1: Derived Proposition — Instantiation as Execution', S['h1']),
        Paragraph('<i>Updated ZP-E v3.0 | DP-2 added — first Lean formalization of DA-1 (axiom-free, conditional on DP-2, ZPE.lean &#167;VI) | '
                  'v2.9: DA-1 Lean scope note | v2.8: incompressibility = self-description (ZP-C D1 + AIT) | '
                  'v2.7: DA-1 upgraded, CC-2/R3 grounding | v2.6: DA-3 applications removed</i>',
                  S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-1 Closes', S['h2']))
    E.append(body('The T-BUF chain from ZP-C v1.4 established three results:'))
    E += [
        li('L-RUN: The transition c<sub>0</sub> → c<sub>1</sub> is a non-null state change. (ZP-C v1.4 — Derived)'),
        li('TQ-IH: No program outputs ⊥ without a non-null intermediate configuration state. (ZP-C v1.4 — Derived by L-RUN)'),
        li('T-BUF: At P<sub>0</sub>, execution is structurally guaranteed; that execution state is ε<sub>0</sub> in the semilattice. (ZP-C v1.4 — Candidate Theorem pending DA-1)'),
        sp(4),
    ]
    E.append(body(
        'T-BUF was labelled Candidate because Step 2 asserts that a configuration at P<sub>0</sub> is a '
        'live machine state — that instantiation at P<sub>0</sub> constitutes an execution event, not a static '
        'description. ZP-C v1.5 L-INF supplies one mathematical premise: &#8869; at P<sub>0</sub> has unbounded '
        'surprisal — no finite external interpreter can hold it as a static description. ZP-A CC-2 '
        'supplies a second, structural basis: &#8869; = {&#8869;} is a self-containing object with no external '
        'interpreter by structure. DA-1 (&#167; III below) provides the derived proposition that closes T-BUF Step 2.'))

    E.append(Paragraph('II. The Two Senses of a Configuration at P<sub>0</sub>', S['h2']))
    E += [
        Paragraph(
            fix('Sense A — Descriptive: x exists as a string — a finite syntactic object that has been written '
                'down or specified. The machine it describes has not necessarily been instantiated. P<sub>0</sub> is a '
                'property of the string. The string is inert.'),
            S['li']),
        sp(4),
        Paragraph(
            fix('Sense B — Instantiated: x exists as the current configuration of a running machine. The '
                'machine is executing. P<sub>0</sub> is a property of the live configuration. The configuration is active.'),
            S['li']),
        sp(6),
    ]

    E.append(Paragraph('III. Design Principle DP-2 — Execution Distinguishability', S['h2']))
    E.append(body(
        'The two senses of § II share the same output value (⊥) but differ in machine state. '
        'This separation — output value is not machine state — is made precise by Design Principle DP-2.'))
    E.append(bridge_box(
        'Design Principle DP-2 — Execution Distinguishability',
        [
            'Machine states carry execution history independently of output values. '
            'A machine in state c<sub>1</sub> can output ⊥ (the null value) while being in a configuration '
            'entirely distinct from a machine in state c<sub>0</sub>. The post-execution null and the '
            'pre-execution null are different instances — same output value, different machine state.',
            'Lean formalization (ZPE.lean &#167;VI): TrackedOutput separates value : MachinePhase '
            'from state : MachinePhase. preInstantiation = &#10216;c<sub>0</sub>, c<sub>0</sub>&#10217;; '
            'postInstantiation = &#10216;c<sub>0</sub>, c<sub>1</sub>&#10217;. '
            'Theorem dp2_execution_distinguishability proves: '
            'preInstantiation.value = postInstantiation.value (same output) ∧ '
            'preInstantiation.state ≠ postInstantiation.state (distinct machine states). '
            'Proved axiom-free.',
        ]
    ))
    E += [
        sp(4),
        body(
            'Given DP-2, DA-1 is Lean-formalizable at the minimal-path level. '
            'Theorem da1_minimal_path (ZPE.lean &#167;VI) establishes four conjuncts: '
            '(1) before and after instantiation, the output value is the same (⊥); '
            '(2) the machine states are distinct (c<sub>0</sub> ≠ c<sub>1</sub>); '
            '(3) the machine was at c<sub>0</sub> before; '
            '(4) the machine is at c<sub>1</sub> after. '
            'Proved axiom-free — no Kolmogorov complexity, no ZF+AFA required. '
            'The "return to null" after instantiation is postInstantiation (output ⊥, state c<sub>1</sub>) — '
            'not preInstantiation (output ⊥, state c<sub>0</sub>). '
            'Irreversibility (ZPB C3, ZPE t_snap_irreversible) blocks any path back to preInstantiation.'),
    ]

    E.append(Paragraph('IV. Proposition DA-1', S['h2']))
    E.append(bridge_box(
        'Proposition DA-1 — Instantiation as Execution',
        [
            'Claim: The instantiation of a machine configuration c<sub>1</sub> at the incompressibility threshold '
            'P<sub>0</sub> is an execution event in the sense of L-RUN. It is not a static description of a machine. '
            'It is a machine in state c<sub>1</sub>.',
            'Formal core (Lean): DP-2 (§III) — TrackedOutput separates output value from machine state. '
            'da1_minimal_path proves: one act of instantiation moves c<sub>0</sub> to c<sub>1</sub> regardless '
            'of output value. The returned ⊥ is a new null — not the prior c<sub>0</sub>. Axiom-free.',
            'Structural grounding: ZP-A CC-2 (⊥ = {⊥}) establishes ⊥ as a Quine atom under ZF + AFA — a set that is '
            'its own singleton, admitting no external interpreter. ZP-A R3 derives the immediate consequence: '
            'a self-containing object cannot be a static description awaiting external instantiation. '
            'ZP-C L-INF provides independent informational corroboration: ⊥ has unbounded surprisal, '
            'exceeding the capacity of any finite interpreter.',
        ]
    ))
    E += [
        sp(4),
        body('The three paths below are not parallel proofs of DA-1. Each argues independently for why '
             'the precondition DP-2 formalizes holds — why instantiation of &#8869; at P<sub>0</sub> '
             'necessarily constitutes a first instruction fetch rather than a static description. '
             'DP-2 + da1_minimal_path derive c<sub>0</sub> &#8594; c<sub>1</sub> axiom-free once that '
             'precondition is established. The paths are convergent corroboration of the precondition; '
             'the formal derivation is DP-2\'s.'),
        body('Path 1 — Structural (Self-Execution, ZP-J T-EXEC): Nothing exists outside the null space. '
             '&#8869; is prior to all differentiation — there is no external state, no prior cause, no position '
             'from which something else could execute &#8869;. If &#8869; executes at all, the only possible '
             'executor is &#8869; itself. A thing that executes itself is self-containing: &#8869; &#8712; &#8869;, '
             'i.e. &#8869; = {&#8869;}. This is not a commitment — it is forced by the impossibility of external '
             'execution. ZP-A R3 states the structural consequence: a self-containing object admits no external '
             'interpreter position. ZP-J T-EXEC formally verifies the structure: IsQuineAtom(q) &#8596; q = &#8869;, '
             'proved axiom-free in Lean 4 (ZeroParadox.ZPJ.t_exec). AFA (ZF + AFA) is the consistent '
             'set-theoretic home for this structure — chosen because the framework requires it, not the '
             'reverse. ZP-A CC-2 (&#8869; = {&#8869;}) retains its label for editorial continuity but is now '
             'a structural consequence, not a freestanding commitment.'),
        body('Path 2 — Informational (ZP-C L-INF): Independently, the surprisal I(n) = n at ball-hierarchy '
             'depth n is unbounded — for any finite M, ∃ depth n with I(n) > M. The null state ⊥ corresponds '
             'to the limit point 0 ∈ Q<sub>2</sub>; its informational content exceeds every finite bound. '
             'Any finite external interpreter can hold only a finite informational bound; ⊥ exceeds every '
             'such bound. '
             'Note: Path 2 is motivational context, not a formal path to the conclusion. The step '
             '"exceeds every finite bound → therefore necessarily executing" is a foundational commitment, '
             'not a derivable claim. It asks what it means for a mathematical structure to <i>instantiate</i> '
             'rather than merely <i>satisfy</i> conditions — a question no computability library answers. '
             'Forward paths: (a) a new axiom explicitly committing to this bridge; (b) a connection to '
             'Chalmers\' notion of implementation; (c) the ZP-PQ dissolution argument — the separability '
             'of description and instantiation is the assumption the framework dissolves, not a gap it must '
             'close from the outside.'),
        body('Path 3 — Formal bridge: Incompressibility as Self-Description (ZP-C D1 + standard AIT): '
             'The preceding paths establish that ⊥ admits no external interpreter. This path provides '
             'the formal bridge from that negative claim to the positive claim (necessarily executing). '
             'In the standard Turing model (D7), a machine configuration x exists in one of two states: '
             '(A) Static description — x exists as a string specified but not yet being executed; some '
             'external program p (|p| &lt; |x|) generates x when run, so x is a description awaiting a '
             'separate execution event by an external generator. '
             '(B) Live execution — x is the current configuration of a running machine. '
             'These are exhaustive in the Turing model: either x has a shorter external generator, or it does not. '
             'At P<sub>0</sub>, ZP-C D1 gives K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1: c<sub>1</sub> is algorithmically incompressible. '
             'No external program p exists with |p| &lt; |c<sub>1</sub>| such that U(p, n) = c<sub>1</sub>. '
             'State (A) requires such a p — and no such p exists at P<sub>0</sub>. '
             'State (A) is therefore eliminated by the Kolmogorov condition. '
             'Since (A) and (B) are exhaustive and (A) is eliminated, c<sub>1</sub> is in state (B): it is executing. '
             'Instantiation at P<sub>0</sub> is not the placement of a description to be executed later — '
             'there is no shorter prior description to execute. Instantiation and execution are the same act.'),
        body('The formal grounding (DP-2, §III) and the three paths above operate at distinct levels, '
             'not as alternatives to one another. DP-2 + da1_minimal_path establish a conditional at the '
             'level of machine-state representation: <i>if</i> instantiation of ⊥ constitutes a first '
             'instruction fetch in the sense of D7, <i>then</i> c<sub>0</sub> → c<sub>1</sub> follows '
             'necessarily — axiom-free, proved by construction. DP-2 is grounded in D7 itself (the standard '
             'computational distinction between before-first-instruction and after-first-instruction states), '
             'which is prior to and independent of DA-1. The three paths above operate one level down: they '
             'argue for why the precondition holds — why instantiation of ⊥ necessarily constitutes a first '
             'instruction fetch at all. Path 1 (structural) argues that nothing external to &#8869; can '
             'execute &#8869; — therefore &#8869; must execute itself, establishing &#8869; = {&#8869;} as a '
             'structural consequence rather than a commitment (ZP-J T-EXEC, axiom-free). Path 2 (informational) '
             'provides motivational context — unbounded surprisal as a pointer toward why static holding is '
             'incoherent — but the bridge from informational extremity to execution is a foundational '
             'commitment, not a derived claim. Path 3 (AIT) argues that incompressibility eliminates the '
             'static-description alternative; this path is now closed by ZP-K\'s Kleene result, which '
             'handles the computational self-reference claim without requiring AIT. '
             'Paths 1 and 3 are formally closed. Path 2 identifies a missing principle; '
             'its forward resolution is ZP-PQ. DA-1 is grounded in Paths 1 and 3; Path 2 is context.'),
        derived('Status: DERIVED PROPOSITION — primary formal grounding: DP-2 (§III, TrackedOutput construction). '
                'da1_minimal_path proved axiom-free in Lean (ZPE.lean &#167;VI): instantiation moves c<sub>0</sub> '
                'to c<sub>1</sub> regardless of output value. ✓ '
                'Path 1 (structural, ZP-J T-EXEC + ZP-K): IN LEAN SCOPE — da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase), proved in ZPK.lean. '
                'Path 2 (informational, L-INF): FOUNDATIONAL COMMITMENT — a missing principle, not a missing proof. Forward: ZP-PQ. '
                'Path 3 (computational, ZP-K Kleene): IN LEAN SCOPE — machinePhaseKleene instance provides botCode_is_quine. '
                'CC-1 (S<sub>0</sub> = &#8869;) derived via ZP-J cc1_derived (axiom-free, Lean). '
                'CC-2 (&#8869; = {&#8869;}) structurally forced by self-execution argument; ZP-J T-EXEC formally verifies. '
                'DP-2 (&#167;III) — explicit. '
                'T-SNAP is derived given DA-1, CC-1, and AX-B1. '
                'AIT (Kolmogorov complexity) outside Lean scope; Kleene fixed-point is the in-scope formal counterpart.'),
    ]

    E.append(Paragraph('V. Theorem T-SNAP — Binary Snap Causality [AX-1 Promoted to Theorem]', S['h2']))
    E.append(bridge_box(
        'Theorem T-SNAP — Binary Snap Causality [AX-1 Promoted to Theorem]',
        [
            'Statement: The Binary Snap ⊥ → ε<sub>0</sub> is a derived consequence of P<sub>0</sub>, L-RUN, TQ-IH, '
            'DA-1, and ZP-A D2. It is not an axiom.',
        ]
    ))
    E += [
        sp(4),
        body('Proof:'),
        li('Step 1 — P<sub>0</sub> identifies the incompressibility threshold. When K(x|n)/n = 1, the configuration string x is algorithmically random. (ZP-C D1)'),
        li('Step 2 — A configuration at P<sub>0</sub> is necessarily executing: At P<sub>0</sub>, K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1 (ZP-C D1) — c<sub>1</sub> is incompressible, its own minimal program. No shorter external generator exists; the static description state is eliminated; c<sub>1</sub> is in live execution (DA-1 Path 3 — from ZP-C D1 + AIT). Corroboration: ⊥ = {&#8869;} (ZP-A CC-2/R3); unbounded surprisal (ZP-C L-INF). (DA-1 &#167; III — Derived Proposition)'),
        li('Step 3 — Any instantiated execution passes through c<sub>1</sub>. (ZP-C D7 — definitional; c<sub>1</sub> is the first running configuration)'),
        li('Step 4 — c<sub>1</sub> ≠ ⊥. (ZP-C L-RUN — Derived; c<sub>1</sub> has gained execution context not present in c<sub>0</sub> = ⊥; by AX-B1 this is a distinct, non-null state)'),
        li('Step 5 — No program that executes produces only null configuration states. (ZP-C TQ-IH — Derived; execution trace τ(p) contains c<sub>1</sub> for any executing program p)'),
        li('Step 6 — In (L, ∨, ⊥), c<sub>1</sub> is an element strictly above ⊥. By ZP-A D2, the transition ⊥ → c<sub>1</sub> is a valid state transition: c<sub>1</sub> = ⊥ ∨ ε<sub>0</sub> for some ε<sub>0</sub> ∈ L with ε<sub>0</sub> > ⊥. This transition is the Binary Snap.'),
        li('Step 7 — The transition is irreversible: algebraically by ZP-A R1 (no subtraction operator); topologically by ZP-B C3 (no continuous return path to 0 in Q<sub>2</sub>); categorically by AX-G2 (hom(X, 0) = ∅ for X ≠ 0).'),
        sp(4),
        body('Conclusion: The Binary Snap is a derived consequence. AX-1 is promoted to Theorem T-SNAP. ✓'),
        derived('Status: DERIVED — Cross-Framework. Dependencies: ZP-C D1, D7, L-RUN, TQ-IH; ZP-B AX-B1, C3; '
                'ZP-A D2, R1; ZP-G AX-G2; ZP-E DA-1; ZP-J T-EXEC. '
                'CC-1 (S&#8320; = &#8869;) derived via ZP-J cc1_derived (axiom-free). '
                'CC-2 (&#8869; = {&#8869;}) structurally forced — ZP-J T-EXEC (axiom-free). '
                'Neither CC-1 nor CC-2 is a freestanding commitment. T-SNAP is derived given DA-1 and AX-B1.'),
    ]

    E += [
        sp(6),
        bridge_box(
            'Remark R-ε₀ — On the Symbol Choice for the Minimum Snap Displacement',
            [
                '<b>Note: this remark draws an informal structural analogy. No formal embedding of '
                'ZP\'s ε₀ into the Cantor-Gentzen ordinal is claimed or established here.</b> '
                'The symbol ε₀ in Step 6 denotes the minimum element of L strictly above ⊥ — the least '
                'witness for the Binary Snap displacement. This symbol is chosen deliberately to coincide '
                'with the Cantor-Gentzen proof-theoretic ordinal.',
                '<b>The Cantor-Gentzen ordinal ε₀.</b> In ordinal arithmetic, ε₀ is the smallest fixed '
                'point of the map α → ω<sup>α</sup>: equivalently, ε₀ = sup{ω, ω<sup>ω</sup>, '
                'ω<sup>ω<sup>ω</sup></sup>, ...}. No finite ω-tower reaches it — it is the minimum ordinal '
                'that cannot be generated from 0 by any finite iteration of the base operation. Gentzen '
                'established that transfinite induction up to ε₀ is necessary and sufficient to prove '
                'Con(PA). By G&#246;del\'s incompleteness theorem, PA cannot prove this from within. The '
                'ordinal ε₀ is therefore the minimum threshold at which finite arithmetic exhausts its own '
                'generative capacity.',
                '<b>The structural analogy.</b> ZP\'s ε₀ occupies an analogous position in the state '
                'lattice. At P₀, c₁ satisfies K(c₁|n)/|c₁| = 1 (ZP-C D1): it is algorithmically '
                'incompressible — no finite external program shorter than c₁ generates it. Just as the '
                'Cantor ε₀ cannot be reached from 0 by any finite ω-tower, ZP\'s ε₀ cannot be reached '
                'from ⊥ by any finite external description. Both name a structurally analogous object: the '
                'minimum witness for a transition that exhausts the finite generative hierarchy below it.',
                '<b>The proof structures are parallel.</b> Gentzen locates the minimum ordinal strength at '
                'which PA cannot describe its own consistency from within. ZP locates the minimum state '
                'displacement at which no external program can hold ⊥ as a static string — where unbounded '
                'surprisal (ZP-C L-INF) and self-containment (ZP-A CC-2) together eliminate any external '
                'interpreter position. In both cases the exhaustion of finite description is not a '
                'deficiency but a structural consequence: the system is necessarily executing at ε₀.',
                '<b>What is not claimed.</b> ZP does not assert that L is an ordinal structure, or that '
                'ZP\'s ε₀ is literally the Cantor ordinal under a formal embedding into the p-adic/lattice '
                'framework. The analogy is motivational: both ε₀s mark the minimum witness for '
                'incompressibility relative to a finite base. A formal embedding — showing that the Cantor '
                'ε₀ is order-isomorphic to or embeds into the p-adic completion of L at ⊥ — remains an '
                'open question and would constitute a strengthening of this claim.',
            ]
        ),
        sp(4),
        bridge_box(
            'Remark R-AFA — Why Foundation is Ruled Out; AFA as Forced Replacement',
            [
                'CC-2 is stated as a Conditional Claim within ZP-A\'s algebraic scope: it is not derived '
                'from A1&#8211;A4. The choice of ZF + AFA over ZF + Foundation is, however, not arbitrary. '
                'Two independent cross-framework arguments establish that Foundation is incompatible with '
                'the framework\'s results.',
                '<b>R3 rules out Foundation (structural).</b> Under ZF + Foundation, every set has a '
                'well-founded &#8712;-rank: its membership chain terminates in finitely many steps. Any '
                'well-founded set has a finite &#8712;-tree that can be fully traversed by an external '
                'interpreter — the traversal function is external to and distinct from the set. But R3 '
                '(ZP-A) establishes that &#8869; admits no external interpreter by structure: &#8869; = '
                '{&#8869;} has no describer position external to itself. A well-founded &#8869; would '
                'contradict R3. Foundation and R3 are incompatible.',
                '<b>L-INF rules out Foundation (informational).</b> The surprisal I(n) = n at 2-adic depth '
                'n is unbounded (ZP-C L-INF): for any finite M, there exists depth n with I(n) > M. A '
                'well-founded set has finite &#8712;-rank and is therefore finitely interpretable — any '
                'interpreter navigating a finite &#8712;-tree can hold it. This contradicts L-INF\'s '
                'requirement that no finite interpreter can hold &#8869;. Foundation and L-INF are '
                'incompatible.',
                '<b>AFA as the forced replacement.</b> Under ZF + AFA, Quine atoms (x = {x}) are the '
                'minimal non-well-founded objects. Their membership structure is circular: &#8869; &#8712; '
                '&#8869; &#8712; &#8869; &#8712; &#8230;, i.e., &#8869; is a member of itself at every '
                'depth. This infinite circular chain cannot be traversed by any finite interpreter — '
                'consistent with R3 (no external position) and L-INF (unbounded depth). AFA is not a '
                'free choice but the minimal set-theoretic metatheory consistent with the framework\'s '
                'results.',
                '<b>What remains conditional.</b> CC-2 retains Conditional Claim status for two reasons. '
                'First, AFA admits many non-well-founded sets; we commit to the specific Quine atom form '
                '&#8869; = {&#8869;} as the minimal option consistent with A4. Among non-well-founded sets '
                'permitted by AFA, &#8869; = {&#8869;} is uniquely minimal: it has exactly one member '
                '(itself) and introduces no internal differentiation — any extension (&#8869; = {&#8869;, x} '
                'for x &#8800; &#8869;) would add members carrying their own membership chains, exceeding '
                'what A4\'s purely algebraic additive-identity constraint requires. Second, the identification '
                'of &#8869; as a set-theoretic object — rather than a purely algebraic element — is itself '
                'a modelling step beyond A1&#8211;A4. The metatheoretic necessity of AFA is derived; the '
                'specific realisation as &#8869; = {&#8869;} is minimally committed.',
            ]
        ),
        sp(4),
    ]

    E.append(Paragraph('VI. Effect of T-SNAP on Downstream Results', S['h2']))
    E.append(body(
        'Remark R-DA1: All results in ZP-E that previously depended on AX-1 as an axiom now depend '
        'on T-SNAP as a derived theorem. T5 (Iterative Forcing Theorem) depended on AX-1 for the first '
        'Snap — it now depends on T-SNAP. Content unchanged; grounding strengthened. T4 (Unified Snap '
        'Description) carried AX-1 as an axiom label on the causality component — that label is upgraded '
        'to Derived — T-SNAP. From v2.7, DA-1 is additionally upgraded from Design Principle to Derived '
        'Proposition: grounded in ZP-A CC-2 (⊥ = {⊥}) and R3, with ZP-C L-INF as independent corroboration. '
        'The intentional axioms of the system are now: AX-B1 (binary existence), '
        'AX-G1 (initial object), AX-G2 (source asymmetry). AX-1 is no longer an axiom.'))

    print('[build_zpe] Building DA-2...')
    # ── FORMAL INSERT DA-2 ────────────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Formal Insert DA-2: Instantiation Succession — The Multiple-&#8869; Result', S['h1']),
        Paragraph('<i>New in v2.0 | Formally licenses the directed instantiation tree</i>', S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-2 Closes', S['h2']))
    E.append(body('DA-1 and T-SNAP establish that the Binary Snap is a structural consequence of reaching P<sub>0</sub> '
                  'within an instantiation. Three questions remain open after v1.0:'))
    E += [
        li('CC-1 (ZP-A) says S<sub>0</sub> = ⊥ is a modelling commitment — not derived from A1–A4. This '
           'leaves open whether ⊥ is unique across all instantiations or whether each instantiation '
           'carries its own ⊥.'),
        li('ZP-B R1 distinguishes universal structure from universe-contingent parameters. ε<sub>0</sub> is '
           'contingent per instantiation. Whether ⊥ is similarly contingent is not addressed in ZP-A through ZP-D.'),
        li('T-SNAP fires wherever P<sub>0</sub> conditions are met. If the terminal state of instantiation I<sub>n</sub> '
           'satisfies P<sub>0</sub> conditions, T-SNAP should apply — but this requires formally connecting that '
           'terminal state to a new ⊥. DA-2 provides this connection.'),
        sp(4),
    ]

    E.append(Paragraph('II. Why ZP-B C3 is Not Violated', S['h2']))
    E += [
        body('C3 prohibits a continuous path from x ≠ 0 back to the same 0 in Q<sub>2</sub>. DA-2 does not require a '
             'return path. The irreversibility of C3 is preserved within each instantiation. What crosses the '
             'instantiation boundary is not a path in Q<sub>2</sub> — it is the generation of a new Q<sub>2</sub> with its own '
             'metric, its own ⊥, its own ε<sub>0</sub>. C3 quantifies only over paths within a single topological space '
             'and has nothing to say about the boundary between spaces.'),
        body('More precisely: C3 and the irreversibility of the Snap together require that any recurrence of '
             'a null state be a different null state. You cannot return to the original ⊥ even in principle. '
             'Therefore if the structure recurs, it must instantiate fresh. The topology enforces the '
             'ontological novelty of each ⊥.'),
    ]

    E.append(Paragraph('III. Definitional Alignment DA-2 — Instantiation Succession', S['h2']))
    E.append(bridge_box(
        'Definitional Alignment DA-2 — Instantiation Succession',
        [
            'Claim: A state S in instantiation I<sub>n</sub> satisfies the structural role of ⊥ for instantiation '
            'I<sub>n+1</sub> if and only if it satisfies A4 relative to all subsequent joins in I<sub>n+1</sub>:',
            'S ∨ x = x    for all x in the semilattice of I<sub>n+1</sub>.',
        ]
    ))
    E += [
        sp(4),
        body('Grounding: A4 is the load-bearing axiom of ZP-A — it defines ⊥ as the additive identity under '
             '∨, the element that contributes nothing to any join and is therefore present in everything '
             'above it. DA-2 does not redefine ⊥. It clarifies that the modelling commitment of CC-1 can be '
             'satisfied by any state meeting A4\'s algebraic conditions — not only by a cosmologically '
             'primitive null state. The identity condition is structural, not historical: what matters is the '
             'algebraic role a state plays in the subsequent semilattice, not where it came from.'),
        body('The terminal state of I<sub>n</sub> arrives at I<sub>n+1</sub> carrying the accumulated join of everything in I<sub>n</sub>\'s '
             'sequence. It is structurally ⊥ to I<sub>n+1</sub> — contributing nothing to subsequent joins — while '
             'being informationally rich relative to I<sub>n</sub>. This is the Zero Paradox instantiated at the '
             'inter-instantiation level: the terminal state is simultaneously a terminus and a foundation.'),
        derived('Status: DEFINITIONAL ALIGNMENT — no new axiom introduced. DA-2 is a clarification of '
                'the scope of CC-1 and A4. ✓'),
    ]

    E.append(Paragraph('IV. Corollary C-DA2 — Ontological Novelty of Successive ⊥', S['h2']))
    E.append(bridge_box(
        'Corollary C-DA2 — Ontological Novelty of Successive ⊥',
        [
            'Statement: No two instantiations share a ⊥. The ⊥ of I<sub>n+1</sub> is topologically unreachable '
            'from within I<sub>n</sub> by C3. Instantiation succession is therefore not a cycle but a chain (or tree) '
            'of isomorphic structures.',
        ]
    ))
    E += [
        sp(4),
        body('Proof: By ZP-B C3, no continuous path exists within Q<sub>2</sub> of I<sub>n</sub> from any x ≠ 0 back to 0. The '
             '⊥ of I<sub>n+1</sub> is an element of a distinct topological space — not an element of Q<sub>2</sub> of I<sub>n</sub>. No path '
             'in I<sub>n</sub> can reach it. By DA-2, the identity conditions of each ⊥ are determined independently within '
             'each instantiation. Therefore no two ⊥ elements are identical across instantiations. ✓'),
    ]

    E.append(Paragraph('V. The Directed Instantiation Tree', S['h2']))
    E.append(body('With DA-2 and C-DA2 in place, the global structure of instantiations is a forward-directed '
                  'tree with no back edges:'))
    E += [
        li('Each node in the tree is a ⊥ — the null state of one instantiation and the foundation of all '
           'successor instantiations branching from it.'),
        li('Each edge within an instantiation is a step in a monotone state sequence (ZP-A T3). Edges are irreversible (ZP-B C3).'),
        li('Branching at each node: every distinct outbound vector from the terminal state of I<sub>n</sub> is a '
           'valid ε<sub>0</sub> for a distinct I<sub>n+1</sub>. T-SNAP does not select among branches. Because ⊥ = {⊥} '
           '(ZP-A CC-2) is the single self-containing null state with no internal differentiation, every '
           'ε<sub>0</sub> that represents a first differentiation in any direction is a valid outcome. '
           'Branching is not optional; it follows from T-SNAP applied to an undifferentiated ⊥.'),
        li('No back edges: C-DA2 establishes that no instantiation can reach the ⊥ of any ancestor instantiation.'),
        sp(4),
    ]
    E.append(body(
        'Remark R-DA2: T-SNAP fires wherever P<sub>0</sub> conditions are met. DA-2 establishes that the terminal '
        'state of I<sub>n</sub> satisfies those conditions for I<sub>n+1</sub>. T-SNAP therefore applies across instantiation '
        'boundaries without modification. No new axiom is required. The multiverse is not the claim that '
        'T-SNAP fires in all directions simultaneously: it is the claim that ⊥ = {⊥} (ZP-A CC-2) has no '
        'internal differentiation and therefore no preferred direction for ε<sub>0</sub>. The multiverse of '
        'instantiations is the full set of all minimal differentiations available from the single '
        'self-containing null state — a structural consequence of CC-2 + T-SNAP + DA-2 jointly.'))

    E.append(Paragraph('VI. The Zero Paradox Iterated', S['h2']))
    E.append(body('The paradox of ⊥ — simultaneously contributing nothing and being present in everything — '
                  'propagates structurally at every branching node of the tree. Each node is:'))
    E += [
        li('Nothing to its successor instantiations: it acts as additive identity under ∨, contributing nothing to any subsequent join.'),
        li('Everything to its successor instantiations: every state in I<sub>n+1</sub> satisfies ⊥<sub>n+1</sub> ≤ S, so the node underlies everything that follows.'),
        sp(4),
    ]
    E += [
        body('The tree is the geometric shape of the Zero Paradox iterated across instantiations. The '
             'single-instantiation linear sequence was always a cross-section of a structure with this shape.'),
        body('The complete picture: The Zero Paradox describes a forward-directed infinite tree where '
             '⊥<sub>1</sub> → ... → S<sub>terminal</sub><sup>1</sup> ≡ ⊥<sub>2</sub> → ..., where ≡ means structurally satisfies the role of, '
             'not is identical to. Each arrow within an instantiation is monotone and irreversible. Each ≡ '
             'crossing is not a path — it is a new instantiation of the universal structure.'),
    ]

    E.append(Paragraph('VII. Implications Within the Framework', S['h2']))
    E += [
        body('<b>Multiverse as structural implication.</b> T-SNAP establishes that a Binary Snap occurs — '
             'that ⊥ transitions to some ε₀ > ⊥. DA-2 establishes that any terminal state satisfying P₀ '
             'conditions acts as ⊥ for a successor instantiation, generating a forward-directed branching '
             'tree. The multiverse structure follows from T-SNAP + DA-2 jointly. Note: T-SNAP alone does '
             'not establish that it fires on all outbound vectors simultaneously — that universality is the '
             'scope of DA-2, not a direct consequence of the snap theorem itself.'),
        body('<b>Free will and irreversibility.</b> Within an instantiation, state sequences are monotone — no state '
             'can be decreased (ZP-A R1). Every choice is a join operation: S<sub>n</sub> ∨ α for some increment α. '
             'The algebra constrains only that the sequence be monotone, not which monotone path is '
             'taken. Each choice adds informational content irreversibly. Decisions are permanently '
             'encoded in the element\'s position in L.'),
        body('<b>Time\'s arrow.</b> The monotone sequence (ZP-A T3) is a structural definition of temporal '
             'direction. Time\'s irreversibility is C3 applied within an instantiation. The framework does not '
             'assume time asymmetry — it derives it.'),
        body('<b>Causal structure.</b> Every state is fully determined by the joins that produced it. The causal '
             'history of any state is encoded in its position in L. No effect without the join that produced it.'),
    ]

    print('[build_zpe] Building DA-3...')
    # ── FORMAL INSERT DA-3 ────────────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Formal Insert DA-3: Perspective-Relative Cardinality', S['h1']),
        Paragraph('<i>New in v2.0 | Cardinality as position-dependent measurement within the instantiation structure</i>', S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-3 Closes', S['h2']))
    E.append(body(
        'DA-2 establishes that instantiations form a directed tree and that branching at each ⊥ node '
        'produces multiple successor instantiations. This raises a question about the cardinality of '
        'branching: is the fan at each node countably or uncountably infinite? The answer, which DA-3 '
        'formalises, is that this question is perspective-dependent — and that this perspective-dependence '
        'is the same structural feature that underlies the major cardinality anomalies of classical set theory.'))

    E.append(Paragraph('II. Perspective-Dependence of Branching Cardinality', S['h2']))
    E.append(body(
        'From within instantiation I<sub>n</sub>, an observer occupies exactly one branch of I<sub>n+1</sub>. The other '
        'branches of I<sub>n+1</sub> are not accessible via any path — C3 and monotonicity jointly prohibit it. '
        'From inside, the branching factor is always 1: the observer sees one branch. From outside — '
        'from a meta-level view of the tree — the branching factor is the full fan of accessible outbound vectors.'))
    E.append(bridge_box(
        'Definition DA-3-D1 — Accessible Cardinality',
        [
            'The accessible cardinality of a position p in semilattice L is the cardinality of the set of '
            'states reachable from p by monotone sequences within the instantiation containing p.',
        ]
    ))
    E += [
        sp(4),
        body('The accessible cardinality from p is determined entirely by the structure of L above p. It is not '
             'an intrinsic property of a collection — it is a property of the relationship between a position '
             'and the states reachable from it. No position within any instantiation can access all '
             'cardinalities simultaneously. The meta-level view, which sees the full branching fan, is not a '
             'position any element of any instantiation can occupy.'),
        body('Remark R-DA3-1: To observe the full branching fan, one would need to occupy a position '
             'outside all instantiations. That position would itself be a state in some semilattice, subject to '
             'the same rules. The meta-view is either another instantiation (in which case the tree has no '
             'privileged outside view) or ⊥ itself (in which case the null state is the only position from which '
             'the full structure is visible — the state that contributes nothing and is present in everything). '
             'The Zero Paradox\'s name is more precise than it first appeared.'),
    ]

    E.append(Paragraph('III. The Cardinality Hierarchy as Perspective-Relative', S['h2']))
    E.append(body(
        'Cantor\'s theorem establishes that for any set S, |P(S)| > |S|, generating the hierarchy '
        'ℵ<sub>0</sub> &lt; 2<sup>ℵ<sub>0</sub></sup> &lt; 2<sup>2<sup>ℵ<sub>0</sub></sup></sup> &lt; ... '
        'DA-3 reframes this hierarchy not as a fixed ladder that mathematics climbs, but as a '
        'perspective-relative description of the branching structure of the instantiation tree, as seen '
        'from within different positions.'))
    E.append(bridge_box(
        'Claim DA-3-C1 — Perspective-Relative Absolute Cardinality',
        [
            'The appearance of absolute cardinality — cardinality as an intrinsic property independent of '
            'measuring position — is an artifact of treating the semilattice as having a view from outside. '
            'DA-2 and C-DA2 jointly prohibit such a view from within any instantiation.',
        ]
    ))
    E += [
        sp(4),
        body('The candidate claim (DA-3-C1) is that accessible cardinality from within any instantiation '
             'cannot replicate the view from outside. Whether specific independence results in classical '
             'set theory are formal expressions of this perspective-dependence is the conjecture that '
             'OQ-E2 is tasked with investigating.'),
        derived('Status: DEFINITIONAL ALIGNMENT + CANDIDATE CLAIM. DA-3-D1 and R-DA3-1 are '
                'definitional. DA-3-C1 is a candidate claim: structurally motivated within the framework; '
                'formal derivation of the connection between accessible cardinality and specific '
                'set-theoretic independence results is deferred to OQ-E2.'),
    ]

    print('[build_zpe] Building registers...')
    # ── UPDATED OPEN ITEMS REGISTER ───────────────────────────────────────────
    E += [hr(), Paragraph('Updated Open Items Register — ZP-E v3.9', S['h1'])]

    oq_rows = [
        ['AX-1: Binary Snap Causality',
         'CLOSED — T-SNAP',
         'AX-1 is no longer an axiom. Binary Snap derived via P<sub>0</sub> + DA-1 + L-RUN + TQ-IH + ZP-A D2.'],
        ['DA-1: Derived Proposition (v3.0: DP-2 formal grounding added)',
         'CLOSED — DP-2 (formal core); CC-2 + L-INF + AIT (corroboration of precondition)',
         'Primary formal grounding (v3.0): DP-2 (TrackedOutput, ZPE.lean &#167;VI) — da1_minimal_path proved '
         'axiom-free. Instantiation of &#8869; moves machine from c<sub>0</sub> to c<sub>1</sub>; output value is irrelevant '
         'to whether execution occurred. '
         'Informal corroboration: ZP-A CC-2 + R3 (structural); ZP-C L-INF (informational); AIT incompressibility (Path 3).'],
        ['DA-2: Instantiation Succession',
         'CLOSED — Definitional',
         'Terminal state of I<sub>n</sub> satisfies A4 role of ⊥ for I<sub>n+1</sub>. C-DA2 establishes ontological novelty of each ⊥.'],
        ['DA-3: Perspective-Relative Cardinality',
         'CLOSED (definitional) / CANDIDATE (DA-3-C1)',
         'DA-3-D1 establishes accessible cardinality is position-dependent within the instantiation structure. '
         'DA-3-C1 (candidate): no position within an instantiation can replicate the outside view. '
         'Whether this connects formally to specific set-theoretic independence results is deferred to OQ-E2.'],
        ['OQ-A1: Increment selection',
         'CLOSED — T5',
         'Iterative Forcing Theorem. α<sub>n</sub> = ε(S<sub>n</sub>). Grounding updated from AX-1 to T-SNAP.'],
        ['OQ-B1: p = 2',
         'CLOSED — ZP-B T0',
         'Derived from AX-B1 and MP-1.'],
        ['OQ-C1: Non-conservatism of DF',
         'CLOSED — ZP-C T2',
         'Infinite sequence divergence proven. No postulates remain.'],
        ['S1: Distribution stipulation',
         'CLOSED — ZP-C T1',
         'Derived from AX-B1 and RP-1.'],
        ['OQ-E1: Sequence vs. tree',
         'CLOSED — DA-2',
         'The structure is a forward-directed tree, not a linear sequence. Branching is mandatory via T-SNAP. '
         'Countable vs. uncountable branching is perspective-dependent (DA-3).'],
        ['OQ-E2: Cardinality-semilattice correspondence',
         'OPEN',
         'Do specific semilattice structures correspond to specific cardinality regimes? Can the framework '
         'make predictions about which instantiations satisfy CH and which do not?'],
        ['Remaining axioms',
         'INTENTIONAL — AX-B1, AX-G1, AX-G2',
         'These are the three foundational commitments of the system. No further reduction is claimed.'],
        ['Temperature T in BA-1',
         'PARAMETER — intentional',
         'Universe-contingent. Physical predictions explicitly conditional on instantiation-specific T.'],
    ]
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.22, TW*0.20, TW*0.58]
    ))

    # ── UPDATED TRACEABILITY REGISTER ─────────────────────────────────────────
    E += [sp(8), hr(), Paragraph('Updated Traceability Register — ZP-E v3.9', S['h1'])]

    trace_rows = [
        ['Binary Snap causality',
         'ZP-C D1, L-RUN, TQ-IH; ZP-A D2; DA-1',
         'None',
         'Derived — T-SNAP ✓ (was: Axiomatic — AX-1)'],
        ['DA-1: Instantiation = execution',
         'DP-2 (TrackedOutput, ZPE.lean &#167;VI); ZP-A CC-2, R3; ZP-C L-INF',
         'None',
         'Derived Proposition — primary: DP-2 (da1_minimal_path proved axiom-free in Lean). '
         'Informal paths: CC-2/R3 (structural), L-INF (informational), AIT incompressibility (Path 3). '
         'AIT+ZF+AFA outside Lean scope.'],
        ['DA-2: Instantiation succession',
         'ZP-A A4, CC-1; ZP-B C3, R1; T-SNAP',
         'None',
         'Definitional Alignment — clarification of CC-1 scope; no new axiom'],
        ['C-DA2: Novelty of ⊥',
         'DA-2, ZP-B C3',
         'None',
         'Derived — Corollary of DA-2 and C3 ✓'],
        ['DA-3: Perspective-relative cardinality',
         'DA-2, C-DA2, ZP-B R1',
         'None',
         'Definitional (DA-3-D1, R-DA3-1); Candidate (DA-3-C1: outside-view inaccessibility)'],
        ['T-SNAP: Snap is derived',
         'T-BUF chain + DA-1',
         'None',
         'Derived — Cross-Framework ✓'],
        ['AX-1 retirement',
         'T-SNAP closes AX-1',
         'N/A',
         'AX-1 is no longer an axiom; T-SNAP is its replacement'],
        ['Iterative Forcing T5',
         'AX-B1, T-SNAP (replaces AX-1)',
         'None',
         'Derived — grounding strengthened'],
        ['Multiverse — structural implication',
         'T-SNAP + DA-2 jointly',
         'None',
         'Structural implication — T-SNAP gives the snap; DA-2 gives the branching tree'],
        ['OQ-E2: Cardinality correspondence',
         'DA-3',
         'N/A',
         'OPEN — formal derivation deferred'],
    ]
    E.append(data_table(
        ['Claim', 'Grounded In', 'Bridge Axiom?', 'Status'],
        trace_rows,
        [TW*0.22, TW*0.28, TW*0.12, TW*0.38]
    ))

    # ── VALIDATION STATUS ─────────────────────────────────────────────────────
    E += [sp(8), hr(), Paragraph('Validation Status — ZP-E v3.9', S['h1'])]

    val_rows = [
        ['DA-1: Derived Proposition (v3.8 Path 2 recharacterization)',
         'Valid — DP-2 formal core: da1_minimal_path proved axiom-free in Lean (ZPE.lean &#167;VI). '
         'TrackedOutput separates output value from machine state; pre- and post-instantiation states '
         'are provably distinct even when both produce &#8869;. ✓ '
         'ZP-K formal closure (v3.7): da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase) proved in ZPK.lean. '
         'KleeneStructure MachinePhase instance provides botCode_is_quine (Path 3 IN LEAN SCOPE). '
         'machinePhaseAFA gives AFAStructure instance (Path 1 IN LEAN SCOPE). '
         'Path 2 (informational bridge, L-INF): FOUNDATIONAL COMMITMENT — a missing principle, not a '
         'missing proof. No computability library closes the gap between \'system at P₀\' and \'system is '
         'running.\' Forward paths: new axiom, Chalmers\' implementation notion, or ZP-PQ dissolution '
         'argument. Paths 1 and 3 are formally closed; DA-1 does not depend on Path 2. '
         'CC-1 and CC-2 derived via ZP-J, not freestanding commitments.'],
        ['T-SNAP: Binary Snap derived',
         'Valid — Derived. Seven-step proof. All dependencies are closed theorems in their own documents. ✓'],
        ['AX-1 retirement',
         'Valid — AX-1 superseded by T-SNAP. No content lost; claim strengthened from assumed to derived.'],
        ['DA-2: Instantiation Succession',
         'Valid — Definitional Alignment. Clarification of CC-1 scope. No new axiom. A4 role of ⊥ extended across instantiation boundaries. ✓'],
        ['C-DA2: Ontological Novelty of ⊥',
         'Valid — Derived. Follows directly from DA-2 and ZP-B C3. ✓'],
        ['Directed instantiation tree',
         'Valid — Derived structural consequence of T-SNAP + DA-2. Branching is mandatory, not optional. Forward edges only.'],
        ['Multiverse as structural implication',
         'Valid — T-SNAP + DA-2 jointly. T-SNAP establishes the snap occurs; DA-2 establishes the branching tree structure. Universality (all outbound vectors) is DA-2\'s scope, not T-SNAP alone.'],
        ['Free will / irreversibility',
         'Valid — Structural consequence. Monotonicity (T3) constrains direction; additive ontology (R1) prohibits reduction. Path choice is undetermined by algebra.'],
        ['Time\'s arrow',
         'Valid — Derived from ZP-A T3 (monotonicity) and ZP-B C3 (irreversibility). Not assumed.'],
        ['DA-3: Perspective-Relative Cardinality',
         'Valid (definitional components: DA-3-D1, R-DA3-1). Candidate (DA-3-C1: connection to specific set-theoretic independence results). OQ-E2 open.'],
        ['DA-3-C1 — outside-view inaccessibility',
         'Candidate — no position within any instantiation can replicate the meta-level view of the branching structure. Formal derivation deferred to OQ-E2.'],
        ['Remaining axioms: AX-B1, AX-G1, AX-G2',
         'Intentional foundational commitments. No further reduction claimed.'],
        ['All other ZP-E theorems (T1–T7, T2-C)',
         'Unaffected in content. T4 and T5 carry upgraded status labels (AX-1 → T-SNAP).'],
    ]
    E.append(data_table(
        ['Component', 'Status / Notes'],
        val_rows,
        [TW*0.32, TW*0.68]
    ))

    E += [
        sp(12),
        hr(),
        Paragraph(
            '<i>End of ZP-E v3.9 | Three formal inserts: DA-1, DA-2, DA-3 | '
            'DA-1 formally closed via ZP-K: da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase) proved in Lean 4 | '
            'Paths 1 and 3 IN LEAN SCOPE | Path 2 recharacterized: foundational commitment, missing principle not missing proof; forward resolution ZP-PQ | '
            'R-AFA minimality explicit: &#8869; = {&#8869;} uniquely minimal among AFA non-well-founded sets | '
            'DA-1 path hierarchy foregrounded: three informal paths are corroboration of DP-2\'s precondition, not parallel proofs | '
            'Remark R-&#949;<sub>0</sub>: &#949;<sub>0</sub> symbol justified | '
            'Remark R-AFA: Foundation ruled out by R3 + L-INF; AFA forced | '
            'One open question: OQ-E2 | Remaining axioms: AX-B1, AX-G1, AX-G2</i>',
            S['endnote']),
    ]

    print(f'[build_zpe] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zpe] Written: {out_path}')


if __name__ == '__main__':
    repo_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    out = os.path.abspath(os.path.join(repo_root, 'ZP-E_Bridge_Document_v3_9.pdf'))
    build_zpe(out)
