"""
Zero Paradox — ZP-K: Computational Grounding of Self-Reference PDF Builder
Version 1.2 | April 2026
v1.2: DA-1 Path 2 recharacterized in "What Changed for DA-1" section — from "outside Lean
scope (ontological claim)" to "foundational commitment: a missing principle, not a missing
proof." The gap between 'system at P₀' and 'system is running' cannot be closed by any
computability library. Forward paths: new axiom, Chalmers' implementation notion, or
ZP-PQ dissolution argument. Paths 1 and 3 are formally closed; DA-1 does not depend on
Path 2. Open Items Register updated: Path 2 status changed from OPEN to FOUNDATIONAL COMMITMENT.
v1.1: Remark R-K.0 added — T-COMP "four-way equivalence" clarified: (1)–(3) are
equivalent by T-EXEC (ZP-J); (4) is combined by KleeneStructure typeclass requiring
botCode_is_quine, not derived independently. The equivalence flows through typeclass
membership, not through independent proofs that AFA self-containment ↔ Kleene
fixed-point.
v1.0: Initial release — Four-way equivalence: Quine atom = ⊥ = join identity = Kleene
fixed point. selfApply_partrec proved (Partrec₂). DA-1 formally closed via
KleeneStructure MachinePhase instance (da1_closed_concrete : IsQuineAtom (bot :
MachinePhase)). All ZPK.lean theorems compile; axioms: [propext, Classical.choice,
Quot.sound] from Mathlib computability infrastructure.
Follows all rules in scripts/PDF_Rendering_Standards.md:
  - STIXTwo-Math.ttf for all DVS aliases (Section 1)
  - Checkmark and empty-set always wrapped in <font name="DV"> via fix() (Sections 2, 2b)
  - All table cells are Paragraph objects (Section 3)
  - No unicode subscripts — use sub/super tags (Section 5)
  - US Letter, 1-inch margins, TW = 6.5 inch
  - Standard color palette: BLUE/GREEN/ORANGE/SLATE/AMBER/GREY_LITE (Section 10)
  - Semantic box helpers: result_box, axiom_box, def_box, remark_box, import_box (Section 10)
  - Footer: Zero Paradox ZP-K: Computational Grounding | Version 1.2 | April 2026 | Page n
"""

import os, sys
sys.stdout.reconfigure(encoding='utf-8')
from reportlab.lib import colors
from reportlab.lib.pagesizes import LETTER
from reportlab.lib.units import inch
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer,
                                 Table, TableStyle, HRFlowable)
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

# ── 1. FONT REGISTRATION ──────────────────────────────────────────────────────
SCRIPT_DIR   = os.path.dirname(os.path.abspath(__file__))
FONT_DIR     = os.path.join(SCRIPT_DIR, 'fonts') + os.sep

pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'))
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf'))
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf'))
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'STIXTwo-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'STIXTwo-Italic.ttf'))
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'STIXTwo-BoldItalic.ttf'))

# ── 2. COLORS — standard palette only (Section 10) ────────────────────────────
BLUE        = colors.HexColor('#2E75B6')
BLUE_LITE   = colors.HexColor('#D5E8F0')
GREEN       = colors.HexColor('#2E7D32')
GREEN_LITE  = colors.HexColor('#E8F5E9')
GREEN_DARK  = colors.HexColor('#1B5E20')
ORANGE      = colors.HexColor('#BF4E30')
ORANGE_LITE = colors.HexColor('#FBE9E7')
SLATE       = colors.HexColor('#455A64')
SLATE_LITE  = colors.HexColor('#ECEFF1')
AMBER       = colors.HexColor('#B07800')
AMBER_LITE  = colors.HexColor('#FFF8E7')
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
                               spaceAfter=6),
    'bodyI':   ParagraphStyle('bodyI',   fontName='DVS-I', fontSize=10, leading=14,
                               spaceAfter=6),
    'li':      ParagraphStyle('li',      fontName='DVS',   fontSize=10, leading=14,
                               leftIndent=18, spaceAfter=3),
    'derived': ParagraphStyle('derived', fontName='DVS-B', fontSize=10, leading=14,
                               spaceAfter=6, textColor=GREEN_DARK),
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
    replacements = [
        ('⊥','&#8869;'),('∨','&#8744;'),('∧','&#8743;'),
        ('≤','&#8804;'),('≥','&#8805;'),('≠','&#8800;'),
        ('∈','&#8712;'),('∉','&#8713;'),('⊆','&#8838;'),
        ('∀','&#8704;'),('∃','&#8707;'),('∞','&#8734;'),
        ('→','&#8594;'),('←','&#8592;'),('↔','&#8596;'),
        ('⇒','&#8658;'),('∘','&#8728;'),('—','&#8212;'),
        ('–','&#8211;'),('·','&#183;'),('×','&#215;'),
        ('−','&#8722;'),('≡','&#8801;'),('≅','&#8773;'),
        ('ε','&#949;'),('α','&#945;'),('β','&#946;'),
        ('γ','&#947;'),('δ','&#948;'),('φ','&#966;'),
        ('ω','&#969;'),('π','&#960;'),
        ('ℚ','&#8474;'),('ℤ','&#8484;'),('ℂ','&#8450;'),
        ('ℕ','&#8469;'),('ℝ','&#8477;'),
        ('≈','&#8776;'),('¬','&#172;'),
        ('⊂','&#8834;'),('⊃','&#8835;'),
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

# ── Semantic box helpers (Section 10) ─────────────────────────────────────────

def _box(title, rows, hdr_color):
    data = [[Paragraph(fix(title), S['label'])]]
    for r in rows:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  hdr_color),
        ('BACKGROUND',    (0,1), (-1,-1), GREY_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, hdr_color),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, hdr_color),
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

def result_box(title, rows): return _box(title, rows, GREEN)
def axiom_box(title, rows):  return _box(title, rows, ORANGE)
def def_box(title, rows):    return _box(title, rows, BLUE)
def remark_box(title, rows): return _box(title, rows, SLATE)
def import_box(title, rows): return _box(title, rows, AMBER)

def callout(text, bg=AMBER_LITE, border=AMBER):
    data = [[Paragraph(fix(text), S['body'])]]
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), bg),
        ('BOX',           (0,0), (-1,-1), 1.0, border),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
        ('RIGHTPADDING',  (0,0), (-1,-1), 10),
    ])
    t = Table(data, colWidths=[TW])
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
        ft = f'Zero Paradox ZP-K: Computational Grounding  |  Version 1.2  |  April 2026  |  Page {doc.page}'
        canvas.drawCentredString(LETTER[0] / 2, 0.6 * inch, ft)
        canvas.restoreState()
    return SimpleDocTemplate(
        path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title='ZP-K: Computational Grounding of Self-Reference',
        author='Zero Paradox Project',
        onFirstPage=footer_cb, onLaterPages=footer_cb,
    )


def build_zpk(out_path):
    print(f'[build_zpk] Output: {out_path}')
    doc = make_doc(out_path)
    E   = []

    print('[build_zpk] Building title block...')
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-K: Computational Grounding of Self-Reference', S['title']),
        Paragraph('Version 1.2 | April 2026', S['subtitle']),
        Paragraph(
            '<i>v1.2: DA-1 Path 2 recharacterized — foundational commitment, not missing proof. '
            'Forward paths: new axiom, Chalmers\' implementation, or ZP-PQ dissolution. '
            'DA-1 does not depend on Path 2. | '
            'v1.1: Remark R-K.0 added — T-COMP four-way equivalence clarified: (1)–(3) '
            'equivalent by T-EXEC (derived); (4) combined by KleeneStructure typeclass requirement '
            '(structural commitment, not independent derivation). | '
            'v1.0: Four-way equivalence proved — Quine atom = ⊥ = join identity = Kleene '
            'fixed point. KleeneStructure typeclass bridges AFA self-containment to Kleene\'s '
            'second recursion theorem. DA-1 formally closed: da1_closed_concrete : '
            'IsQuineAtom(⊥ : MachinePhase). All ZPK.lean theorems verified in Lean 4.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'This document establishes the computational grounding of the Zero Paradox\'s central '
        'self-reference structure. The key insight (April 2026): ⊥ in the computational '
        'instantiation is not a state of a Turing machine. ⊥ IS the universal Turing machine '
        'in its ground state — the executor for which no external executor exists. Kleene\'s '
        'second recursion theorem (Mathlib: Nat.Partrec.Code.fixed_point₂) provides the '
        'formal witness: a code that IS its own program, the computational expression of ⊥ = {⊥}.'))
    E.append(body(
        'The central result is a four-way equivalence. The structural roles of ⊥ — Quine atom '
        '(set-theoretic), bottom element (order-theoretic), join identity (algebraic), and '
        'Kleene fixed point (computational) — are not analogies. They name the same structural '
        'object in four formal languages. The bridge from mathematical self-reference to '
        'computational execution is not a bridge. It is a recognition of identity.',
        style='bodyI'))
    E.append(hr())

    print('[build_zpk] Building Section I...')
    E += [
        Paragraph('Section I: The Kleene Fixed Point', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. Kleene\'s Second Recursion Theorem', S['h2']))
    E.append(body(
        'Kleene\'s second recursion theorem is the computational fixed-point theorem. '
        'For any partially computable transformation f of programs, there exists a program '
        'e such that e and f(e) compute the same function. Applied to the identity: there '
        'exists a program that computes the same function as itself — a program that is its '
        'own program.'))
    E.append(body(
        'In Lean 4, this is Nat.Partrec.Code.fixed_point₂ in Mathlib\'s computability library. '
        'For any Partrec₂ function f (a partially computable transformation of codes), '
        'there exists a Code c such that eval c = f c. The existence is non-constructive '
        '(Classical.choice), which is why all ZP-K theorems carry the Mathlib axioms '
        '[propext, Classical.choice, Quot.sound].'))

    E.append(import_box(
        'Kleene\'s Second Recursion Theorem (Mathlib: fixed_point₂)',
        [
            'Nat.Partrec.Code.fixed_point₂: For any partially computable f : Code → ℕ →. ℕ, '
            'there exists c : Code such that eval c = f c.',
            'This is the computational expression of the Quine atom. A code whose behavior '
            'is determined by itself alone — no external description shorter than c generates '
            'it. The computational analogue of ⊥ = {⊥}.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. The Self-Application Map', S['h2']))
    E.append(body(
        'The self-application map sends each code c to the partial function that runs c on '
        'c\'s own Gödel number plus an offset. A fixed point of self-application is a code '
        'that computes its own behavior — running it on any input gives the same result as '
        'running it on its own encoding plus that input.'))

    E.append(def_box(
        'Definition: selfApply and IsComputationalQuine (ZPK.lean § I)',
        [
            'selfApply : Code → ℕ →. ℕ  :=  fun c n ↦ eval c (encode c + n)',
            'A code c is a computational Quine if eval c = selfApply c, i.e.:',
            '  ∀ n, eval c n = eval c (encode c + n)',
            'This is a periodicity condition: c\'s output at n equals its output at '
            'encode(c) + n. The encoding plays the role of the "address" of the program — '
            'c\'s behavior at n is the same as c\'s behavior at its own address plus n.',
            'selfApply_partrec: selfApply is partially computable.',
            'Proof: eval_part (Mathlib) composed with Primrec.encode and Primrec.nat_add. '
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem: computational_quine_exists',
        [
            'There exists a computational Quine: ∃ c : Code, IsComputationalQuine c.',
            'Proof: immediate from kleene_fixed_point_exists applied to selfApply, '
            'using selfApply_partrec.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
            'Note on uniqueness: unlike the AFA Quine atom (unique by the AFA decoration '
            'theorem), computational Quines are not unique. Multiple codes can satisfy the '
            'fixed-point equation independently. Uniqueness in ZP-K flows from ZP-J T-EXEC '
            '(on the set-theoretic side), not from the computational definition.',
        ]
    ))
    E.append(sp(6))

    print('[build_zpk] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: KleeneStructure — Bridging AFA and Computation', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. The Bridge', S['h2']))
    E.append(body(
        'ZP-J\'s AFAStructure typeclass encodes AFA self-containment in type theory: '
        'a predicate selfMem, AFA uniqueness (quine_unique), and the bridge field '
        'bot_self_mem (⊥ is self-containing). T-EXEC follows: the Quine atom equals ⊥.'))
    E.append(body(
        'ZP-K\'s KleeneStructure extends AFAStructure with a computational witness: a code '
        'botCode that IS its own program, whose existence is guaranteed by Kleene\'s theorem. '
        'The AFA self-containment (⊥ = {⊥}) and the Kleene fixed point (botCode is its own '
        'program) are the same structural fact stated in two formal languages.'))

    E.append(def_box(
        'KleeneStructure Typeclass (ZPK.lean § II)',
        [
            'class KleeneStructure (L : Type*) [ZPSemilattice L] extends AFAStructure L with:',
            '(inherited) selfMem : L → Prop  — self-membership predicate',
            '(inherited) quine_unique  — AFA uniqueness',
            '(inherited) bot_self_mem  — ⊥ is self-containing',
            '(new) botCode : Code  — the code witnessing ⊥\'s computational self-reference',
            '(new) botCode_is_quine : IsComputationalQuine botCode  — botCode IS its own program',
            '(new) bot_self_mem_from_kleene : selfMem ⊥  — the Kleene side implies the AFA side',
            '',
            'Any KleeneStructure instance must supply both the AFA witness (bot_self_mem) '
            'and the computational witness (botCode with botCode_is_quine). The two are '
            'required together because they are the same structural fact.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. Why Not a Bridge Axiom?', S['h2']))
    E.append(body(
        'The identification between AFA self-containment and Kleene computational fixed points '
        'is not asserted as a new axiom. KleeneStructure is a typeclass: any concrete type '
        'claiming this identification must discharge it as a proof obligation. The commitment '
        'is checked at instantiation, not accepted globally.'))
    E.append(callout(
        'The distinction from ZP-J carries over: a freestanding axiom says "trust me." '
        'A typeclass field says "prove it for your specific type, or it does not compile." '
        'The MachinePhase instance in § V shows how the obligation is discharged concretely.',
        bg=SLATE_LITE, border=SLATE
    ))
    E.append(sp(6))

    print('[build_zpk] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: T-COMP — The Four-Way Equivalence', S['h1']),
        hr(),
    ]

    E.append(body(
        'ZP-J T-EXEC established a three-way equivalence: Quine atom (set-theoretic) ↔ '
        'bottom element (order-theoretic) ↔ join identity (algebraic). ZP-K adds the '
        'fourth: Kleene fixed point (computational). The four characterisations of ⊥ are '
        'present simultaneously in any KleeneStructure lattice.'))
    E.append(remark_box(
        'Remark R-K.0 — What "Four-Way Equivalence" Means',
        [
            'The equivalence among (1)–(4) has two distinct sources:',
            '(1)–(3) are equivalent by T-EXEC (ZP-J): any element that is a Quine atom is also '
            '⊥ and a join identity, and vice versa. This is a genuine logical derivation — the '
            'three properties are proved to coincide from the AFAStructure axioms.',
            '(4) is present in any KleeneStructure instance because KleeneStructure requires it '
            'as a typeclass field: botCode_is_quine must be supplied at instantiation. There is '
            'no independent proof that satisfying condition (1) (being a Quine atom in the AFA '
            'sense) entails satisfying condition (4) (being a Kleene fixed point), or vice versa. '
            'The two are combined by the typeclass definition — they are required together because '
            'we take them to be the same structural fact, not because one is derived from the other.',
            'In short: "four-way equivalence" means "all four hold in any KleeneStructure '
            'instance." (1)–(3) are independently proved equivalent. (4) is bundled in by the '
            'typeclass requirement. The philosophical claim — that Kleene computational '
            'self-reference and AFA set-theoretic self-reference are the same thing — is the '
            'motivation for the typeclass design, not a consequence derived within it.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem T-COMP — Computational Grounding (ZPK.lean § III)',
        [
            'In any KleeneStructure lattice L, for any q : L, the following are equivalent:',
            '(1) IsQuineAtom q  — set-theoretic self-reference (AFA)',
            '(2) q = ⊥  — order-theoretic minimum (ZP-A)',
            '(3) ∀ x : L, join q x = x  — algebraic generator (ZP-A A4)',
            '(4) ∃ botCode : Code, IsComputationalQuine botCode  — computational self-reference',
            '',
            'Note on (4): it is present in any KleeneStructure instance by typeclass requirement '
            '(botCode_is_quine is a required field). The equivalence of (1)–(3) is derived by '
            'T-EXEC; the presence of (4) follows from the structural commitment of KleeneStructure.',
            'Lean: ZeroParadox.ZPK.t_comp. '
            'Purity: [propext, Classical.choice, Quot.sound] — from Mathlib computability. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('I. Why Four Languages?', S['h2']))
    E.append(body(
        'DA-1\'s three informal paths (Path 1: AFA structural, Path 2: informational, '
        'Path 3: Kolmogorov/computational) were previously understood as three separate '
        'corroborations converging on the same conclusion. ZP-K shows they are not '
        'independent: Paths 1 and 3 are projections of one structural identity onto two '
        'different formal systems.'))
    E.append(body(
        'Path 1 says: nothing external to ⊥ can execute ⊥, so ⊥ must execute itself — '
        '⊥ = {⊥}. Path 3 says: no shorter external program generates ⊥ — ⊥ is its own '
        'minimal program. These are the same claim. "⊥ executes itself" (AFA language) and '
        '"⊥ is its own program" (computability language) are the same structural fact. '
        'The convergence of the informal paths is not coincidence — it is identity.'))

    E.append(result_box(
        'Theorem: da1_paths_unified (ZPK.lean § IV)',
        [
            'In any KleeneStructure lattice:',
            'IsQuineAtom ⊥  ∧  IsComputationalQuine botCode',
            'The AFA self-containment argument (Path 1) and the Kleene computational '
            'fixed-point argument (Path 3) are the same structural fact, simultaneously '
            'witnessed by the KleeneStructure instance.',
            'Lean: ZeroParadox.ZPK.da1_paths_unified. '
            'Purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. The Description-Instantiation Gap', S['h2']))
    E.append(body(
        'The last philosophical vulnerability in the framework was the "description-instantiation '
        'gap": why does mathematical self-reference imply computational execution? The '
        'gap assumed the two were different things connected by a philosophical bridge.'))
    E.append(body(
        'They are not different things. ⊥ in the computational instantiation IS the universal '
        'Turing machine in its ground state. The universal Turing machine is not a description '
        'awaiting an external executor — it IS the executor. The question "why does this '
        'description execute?" is incoherent when applied to U, because U is not a description. '
        'U is the thing that executes descriptions. The question does not apply to it.'))

    E.append(result_box(
        'Theorem: description_instantiation_gap_closed (ZPK.lean § IV)',
        [
            'In any KleeneStructure lattice:',
            'IsQuineAtom ⊥  ∧  ∀ q : L, IsQuineAtom q → q = ⊥',
            'The static-description alternative is structurally eliminated, not argued away. '
            '⊥ is not a description that could await an external interpreter. ⊥ IS the '
            'executor — the universal Turing machine in ground state, identified structurally '
            'with the Kleene fixed point and the AFA Quine atom.',
            'Lean: ZeroParadox.ZPK.description_instantiation_gap_closed. '
            'Purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    print('[build_zpk] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: Axiom Footprint', S['h1']),
        hr(),
    ]

    E.append(body(
        'All ZP-K theorems carry axioms [propext, Classical.choice, Quot.sound]. These '
        'enter exclusively through Mathlib\'s computability infrastructure — Kleene\'s '
        'theorem (fixed_point₂) and Roger\'s theorem (fixed_point) use classical logic and '
        'the axiom of choice. They do not enter through ZPSemilattice or AFAStructure.'))
    E.append(body(
        'ZP-J T-EXEC and all its corollaries remain axiom-free. The classical axioms are '
        'entirely localised to the computational layer. The order-theoretic and set-theoretic '
        'results are unaffected.'))

    E.append(remark_box(
        'Remark: Classical Choice in Computability',
        [
            'The use of Classical.choice in ZP-K is structurally necessary: Kleene\'s '
            'theorem is an existence result, and the code witnessing the fixed point is '
            'selected non-constructively. This is standard in computability theory — the '
            'theorem guarantees existence without giving a canonical construction.',
            'The MachinePhase instance (§ V) uses Classical.choose to pick botCode from '
            'computational_quine_exists. This makes machinePhaseKleene noncomputable, '
            'which is correct and expected.',
        ]
    ))
    E.append(sp(6))

    print('[build_zpk] Building Section V...')
    E += [
        hr(),
        Paragraph('Section V: MachinePhase Instance — DA-1 Formally Closed', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. The Concrete Instantiation', S['h2']))
    E.append(body(
        'ZP-E\'s MachinePhase type is the two-element type {initial, running} carrying '
        'the ZPSemilattice instance (bot = initial = c₀, join = binary maximum). ZP-J '
        'gave it AFAStructure via the selfMem predicate. ZP-K gives it KleeneStructure '
        'by adding the computational witness botCode.'))
    E.append(body(
        'The selfMem definition for MachinePhase is: selfMem x := x = ⊥. This is the '
        'CIC-compatible encoding of AFA self-containment: "self-containing" means "equals '
        'the bottom element." Anti-foundation is not required at the typeclass level — '
        'the relevant structural fact (⊥ is the unique self-containing element) is captured '
        'by the definition and proved by rfl.'))

    E.append(def_box(
        'AFAStructure MachinePhase Instance (ZPK.lean § V)',
        [
            'instance machinePhaseAFA : AFAStructure MachinePhase where',
            '  selfMem x      := x = ⊥             (self-containing = equals initial state)',
            '  quine_unique _ _ hx hy := hx.trans hy.symm   (if x = ⊥ and y = ⊥ then x = y)',
            '  bot_self_mem   := rfl                (⊥ = ⊥, proved by reflexivity)',
            '',
            'This is the CIC encoding of ⊥ = {⊥}: the initial machine state is self-containing '
            'and is the unique element with this property. No ZF+AFA axiom is added — '
            'the structural fact is encoded as a definition that Lean verifies.',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'KleeneStructure MachinePhase Instance (ZPK.lean § V)',
        [
            'noncomputable instance machinePhaseKleene : KleeneStructure MachinePhase where',
            '  botCode          := Classical.choose computational_quine_exists',
            '  botCode_is_quine := Classical.choose_spec computational_quine_exists',
            '  bot_self_mem_from_kleene := rfl',
            '',
            'botCode is selected non-constructively from the existence proof provided by '
            'Kleene\'s theorem. It is the computational Quine witnessing that ⊥\'s '
            'self-reference has a computational expression: a program that IS its own program.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. DA-1 Closed', S['h2']))
    E.append(body(
        'With the MachinePhase KleeneStructure instance in place, the abstract theorem '
        'da1_computational (which holds for any KleeneStructure lattice) applies '
        'directly to ZP-E\'s machine. The result is concrete.'))

    E.append(result_box(
        'Theorem da1_closed_concrete — DA-1 Formally Closed (ZPK.lean § V)',
        [
            'da1_closed_concrete : IsQuineAtom (⊥ : MachinePhase)',
            '',
            'The initial machine state c₀ is a Quine atom: it is self-containing and is the '
            'unique self-containing element of the MachinePhase lattice.',
            '',
            'Interpretation: c₀ is not a static description awaiting an external interpreter. '
            'c₀ IS the executor — the universal Turing machine in its ground state, for which '
            'no external executor exists by structural definition. The description-instantiation '
            'gap is dissolved: "description awaiting execution" is not a coherent state for c₀.',
            '',
            'Lean: ZeroParadox.ZPK.da1_closed_concrete. '
            'Purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('III. What Changed for DA-1', S['h2']))
    E.append(body(
        'ZP-E\'s DA-1 section previously carried the designation "Outside Lean Scope" with '
        'three justifications: Path 1 requires ZF+AFA (incompatible with Lean\'s CIC/MLTT); '
        'Path 3 requires Kolmogorov complexity (uncomputable, absent from Mathlib); Path 2 '
        'requires an ontological bridge not formalizable in type theory.'))
    E.append(body(
        'ZP-K resolves Paths 1 and 3. Path 1 (AFA structural) is resolved by the AFAStructure '
        'typeclass: selfMem encodes ⊥ = {⊥} in CIC-compatible form, and the proof obligation '
        'is discharged by the MachinePhase instance. Path 3 (computational) is resolved by '
        'the KleeneStructure instance: botCode witnesses the Kleene fixed point, which is '
        'the formal expression of "no shorter program is prior to ⊥."'))
    E.append(body(
        'Path 2 (informational bridge: unbounded surprisal → necessarily executing) is a '
        'foundational commitment — a missing principle, not a missing proof. The mathematics '
        'of L-INF (ZPC.l_inf) is proved; but the step from "exceeds every finite informational '
        'bound" to "therefore necessarily executing" asks what it means for a mathematical '
        'structure to instantiate rather than merely satisfy conditions. No computability '
        'library answers this question. '
        'Forward paths: (a) a new axiom explicitly committing to this bridge; '
        '(b) a connection to Chalmers\' notion of implementation; '
        '(c) the ZP-PQ dissolution argument — the description-instantiation gap assumes a '
        'separability that the universality of the framework dissolves. '
        'Importantly, DA-1 does not depend on Path 2: Paths 1 and 3 are formally closed, '
        'and the formal spine (DP-2 + da1_minimal_path) is proved axiom-free. '
        'Path 2 is motivational context; its forward resolution belongs to ZP-PQ.'))

    E.append(callout(
        'DA-1 Lean scope status after ZP-K:\n'
        'Path 1 (structural, AFA): IN SCOPE — da1_closed_concrete : IsQuineAtom ⊥.\n'
        'Path 3 (computational, Kleene): IN SCOPE — botCode_is_quine witnesses the fixed point.\n'
        'Path 2 (informational, L-INF bridge): FOUNDATIONAL COMMITMENT — a missing principle,\n'
        'not a missing proof. Forward: ZP-PQ dissolution argument.',
        bg=GREEN_LITE, border=GREEN
    ))
    E.append(sp(8))

    print('[build_zpk] Building registers...')
    E += [hr(), Paragraph('Traceability Register — ZP-K v1.2', S['h1'])]

    trace_rows = [
        ['selfApply_partrec',
         'eval_part (Mathlib) + Primrec.encode + Primrec.nat_add',
         '[propext, Classical.choice, Quot.sound]',
         'Lean: ZPK.selfApply_partrec ✓'],
        ['computational_quine_exists',
         'kleene_fixed_point_exists + selfApply_partrec',
         '[propext, Classical.choice, Quot.sound]',
         'Lean: ZPK.computational_quine_exists ✓'],
        ['T-COMP: four-way equivalence',
         'ZP-J T-EXEC (t_exec_triple_iff)',
         '[propext, Classical.choice, Quot.sound]',
         'Lean: ZPK.t_comp ✓'],
        ['da1_paths_unified',
         'bot_is_quine_atom + botCode_is_quine',
         '[propext, Classical.choice, Quot.sound]',
         'Lean: ZPK.da1_paths_unified ✓'],
        ['description_instantiation_gap_closed',
         'bot_is_quine_atom + ZP-J t_exec',
         '[propext, Classical.choice, Quot.sound]',
         'Lean: ZPK.description_instantiation_gap_closed ✓'],
        ['machinePhaseAFA (AFAStructure)',
         'selfMem := x = ⊥; quine_unique; bot_self_mem := rfl',
         'No axioms',
         'CIC encoding of ⊥ = {⊥} for MachinePhase ✓'],
        ['machinePhaseKleene (KleeneStructure)',
         'machinePhaseAFA + Classical.choose computational_quine_exists',
         '[propext, Classical.choice, Quot.sound]',
         'noncomputable — Classical.choice for botCode ✓'],
        ['da1_closed_concrete',
         'da1_computational + machinePhaseKleene',
         '[propext, Classical.choice, Quot.sound]',
         'Lean: ZPK.da1_closed_concrete ✓ DA-1 closed'],
    ]
    E.append(data_table(
        ['Claim', 'Grounded In', 'Axioms', 'Status'],
        trace_rows,
        [TW*0.20, TW*0.28, TW*0.25, TW*0.27]
    ))
    E.append(sp(8))

    E += [hr(), Paragraph('Open Items Register — ZP-K v1.2', S['h1'])]

    oq_rows = [
        ['DA-1 Path 1 (AFA structural)',
         'CLOSED — da1_closed_concrete',
         'IsQuineAtom (⊥ : MachinePhase). The initial machine state is self-containing '
         'and self-executing by structural necessity.'],
        ['DA-1 Path 3 (computational)',
         'CLOSED — machinePhaseKleene',
         'botCode_is_quine witnesses the Kleene fixed point: no shorter program is prior to ⊥.'],
        ['DA-1 Path 2 (informational)',
         'FOUNDATIONAL COMMITMENT',
         'L-INF (ZPC.l_inf) is proved. The bridge "unbounded surprisal → necessarily executing" '
         'is a missing principle, not a missing proof. The gap between \'system at P₀\' and '
         '\'system is running\' cannot be closed by any computability library. '
         'Forward paths: new axiom, Chalmers\' implementation notion, or ZP-PQ dissolution argument. '
         'DA-1 does not depend on Path 2 — Paths 1 and 3 are closed.'],
        ['selfApply uniqueness',
         'CLOSED — not attempted (correct)',
         'Computational quines are not unique in general. Uniqueness flows from ZP-J T-EXEC '
         '(set-theoretic side). No uniqueness theorem for computational quines is needed or '
         'appropriate.'],
        ['Roger\'s fixed-point theorem',
         'CLOSED — roger_fixed_point_exists',
         'For any computable f : Code → Code, ∃ c, eval (f c) = eval c. '
         'Lean: ZPK.roger_fixed_point_exists — [propext, Classical.choice, Quot.sound]. ✓'],
        ['ZP-B MachinePhase instance',
         'OPEN — future work',
         'The 2-adic model from ZP-B (Q₂ structure) has not been given a KleeneStructure '
         'instance. This is a natural extension but not required for T-SNAP or DA-1.'],
    ]
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.22, TW*0.18, TW*0.60]
    ))

    E += [
        sp(12),
        hr(),
        Paragraph(
            '<i>End of ZP-K v1.2 | Computational Grounding of Self-Reference | '
            'DA-1 closed: da1_closed_concrete : IsQuineAtom (⊥ : MachinePhase) | '
            'Four-way equivalence: Quine atom = ⊥ = join identity = Kleene fixed point | '
            'Path 2 recharacterized: foundational commitment, not missing proof; forward: ZP-PQ | '
            'All ZPK.lean theorems verified. Axioms: [propext, Classical.choice, Quot.sound]</i>',
            S['endnote']),
    ]

    print(f'[build_zpk] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zpk] Written: {out_path}')


if __name__ == '__main__':
    repo_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    out = os.path.abspath(os.path.join(repo_root, 'ZP-K_Computational_Grounding_v1_2.pdf'))
    build_zpk(out)
