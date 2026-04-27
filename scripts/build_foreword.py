"""
Zero Paradox — Foreword PDF Builder (v1.4, revised April 2026)
v1.4: Metatheoretic note (ZF+AFA) added in Section III before the commitments table.
v1.3: Fix ∅ rendering — was showing as a rectangle in DejaVuSerif; now forced through DV (DejaVuSans) via <font> tag.
Follows all rules in pdf rendering standards.md:
  - All table cells are Paragraph objects
  - No unicode subscripts — use sub/super tags
  - US Letter, 1-inch margins, TW = 6.5 inch
"""

import os, sys
from reportlab.lib import colors
from reportlab.lib.pagesizes import LETTER
from reportlab.lib.units import inch
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer,
                                 Table, TableStyle, HRFlowable)
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

# ── 1. FONT REGISTRATION ─────────────────────────────────────────────────────
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
FONT_DIR = os.path.join(SCRIPT_DIR, 'fonts') + os.sep

pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'))
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf'))
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf'))
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'STIXTwo-Math.ttf'))

# ── 2. COLORS ─────────────────────────────────────────────────────────────────
TEAL      = colors.HexColor('#1E7B74')
TEAL_LITE = colors.HexColor('#D0EDED')
BLACK     = colors.black
WHITE     = colors.white

# ── 3. PAGE GEOMETRY ──────────────────────────────────────────────────────────
TW = 6.5 * inch
LM = RM = 1.0 * inch
TM = BM = 1.0 * inch

# ── 4. PARAGRAPH STYLES ───────────────────────────────────────────────────────
S = {
    'title':    ParagraphStyle('title',    fontName='DV-B',  fontSize=20, leading=26,
                               spaceAfter=4, alignment=1),
    'subtitle': ParagraphStyle('subtitle', fontName='DV-I',  fontSize=12, leading=16,
                               spaceAfter=4, alignment=1),
    'date':     ParagraphStyle('date',     fontName='DV',    fontSize=10, leading=14,
                               spaceAfter=6, alignment=1),
    'epigraph': ParagraphStyle('epigraph', fontName='DVS-I', fontSize=11, leading=17,
                               spaceAfter=4, alignment=1, textColor=TEAL),
    'h1':       ParagraphStyle('h1',       fontName='DV-B',  fontSize=13, leading=18,
                               spaceBefore=16, spaceAfter=6, textColor=TEAL),
    'body':     ParagraphStyle('body',     fontName='DVS',   fontSize=10, leading=15,
                               spaceAfter=8),
    'bodyI':    ParagraphStyle('bodyI',    fontName='DVS-I', fontSize=10, leading=15,
                               spaceAfter=8, alignment=1, textColor=TEAL),
    'label':    ParagraphStyle('label',    fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=WHITE),
    'cell':     ParagraphStyle('cell',     fontName='DVS',   fontSize=9,  leading=13),
    'cellB':    ParagraphStyle('cellB',    fontName='DVS-B', fontSize=9,  leading=13),
    'cellI':    ParagraphStyle('cellI',    fontName='DVS-I', fontSize=9,  leading=13),
    'note':     ParagraphStyle('note',     fontName='DVS-I', fontSize=9,  leading=13,
                               spaceAfter=4),
}

def sp(n=6):
    return Spacer(1, n)

def hr():
    return HRFlowable(width='100%', thickness=0.5, color=colors.HexColor('#AAAAAA'),
                      spaceAfter=6, spaceBefore=2)

def box(text):
    """Teal-bordered italic callout box."""
    data = [[Paragraph(text, S['bodyI'])]]
    t = Table(data, colWidths=[TW - 0.4*inch])
    t.setStyle(TableStyle([
        ('BOX',         (0,0), (-1,-1), 1.0, TEAL),
        ('BACKGROUND',  (0,0), (-1,-1), TEAL_LITE),
        ('TOPPADDING',  (0,0), (-1,-1), 10),
        ('BOTTOMPADDING',(0,0),(-1,-1), 10),
        ('LEFTPADDING', (0,0), (-1,-1), 14),
        ('RIGHTPADDING',(0,0), (-1,-1), 14),
    ]))
    return t

def commitments_table():
    headers = [
        Paragraph('Label', S['label']),
        Paragraph('Type', S['label']),
        Paragraph('Statement', S['label']),
    ]
    rows = [
        ('AX-B1', 'Decidable',
         'Binary Existence. A state either exists or it does not. '
         'Directly verifiable by computation (decidable equality on finite types) — '
         'not a novel commitment of this framework.'),
        ('AX-G1', 'Axiom',
         'Initial Object Exists. There is a starting point that reaches every other object. '
         'Not a novel commitment — the existence of ⊥ as the bottom element of the ZP-A semilattice already guarantees this; ZP-G names it in categorical language.'),
        ('AX-G2', 'Axiom',
         'Source Asymmetry. No morphism returns to the initial object from outside. '
         'Not a novel commitment — follows from antisymmetry of the ZP-A partial order and ZP-B C3 (topological irreversibility).'),
        ('MP-1',  'Principle',
         'Minimality of Representation. The representational base must be the minimum '
         'sufficient base for AX-B1. Derives p = 2.'),
        ('RP-1',  'Principle',
         'Minimum Sufficient Probabilistic Representation. The probabilistic form of a '
         'binary ontological state is a point-mass distribution.'),
        ('DP-1',  'Design Commitment',
         'Orthogonality. Topological isolation in Q₂ is represented by orthogonality '
         'in H. Chosen, not derived. Stated explicitly.'),
        ('AX-1',  'Retired axiom → Theorem T-SNAP',
         'Binary Snap Causality. Previously an axiom; now derived as Theorem T-SNAP via '
         'the L-RUN / TQ-IH / DA-1 chain in ZP-C v1.4 and ZP-E.'),
        ('MC-1',  'Modeling Commitment',
         'Cross-Framework Identification. The four concrete frameworks (ZP-A semilattice, '
         'ZP-B p-adic topology, ZP-C information theory, ZP-D Hilbert space) are '
         'identified as instantiations of the abstract categorical structure in ZP-G. '
         'Demonstrated by the four functors in ZP-H; asserted as structural '
         'correspondence, not derived within any single layer.'),
        ('CC-1',  'Conditional Claim',
         'S₀ = ⊥. The initial state equals the null state. '
         'T2 establishes ⊥ ≤ S₀ unconditionally; CC-1 strengthens this to equality '
         'as an explicit modeling choice. Conditional on this identification '
         'holding in a given instantiation.'),
        ('CC-2',  'Conditional Claim',
         '⊥ = {⊥}. The null state is self-containing — a Quine atom under ZF+AFA. '
         'Requires the Anti-Foundation Axiom in place of the Foundation Axiom. '
         'Grounds the self-referential structure of ⊥ and supports DA-1. '
         'Incompatible with standard ZFC.'),
    ]

    table_data = [headers]
    for label, typ, stmt in rows:
        table_data.append([
            Paragraph(label, S['cellB']),
            Paragraph(typ,   S['cell']),
            Paragraph(stmt,  S['cell']),
        ])

    col_w = [TW * x for x in (0.10, 0.20, 0.70)]
    t = Table(table_data, colWidths=col_w, repeatRows=1)
    t.setStyle(TableStyle([
        ('BACKGROUND',   (0,0), (-1,0),  TEAL),
        ('TEXTCOLOR',    (0,0), (-1,0),  WHITE),
        ('ROWBACKGROUNDS',(0,1),(-1,-1), [WHITE, colors.HexColor('#F5F9F9')]),
        ('BOX',          (0,0), (-1,-1), 0.5, colors.HexColor('#AAAAAA')),
        ('INNERGRID',    (0,0), (-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',   (0,0), (-1,-1), 5),
        ('BOTTOMPADDING',(0,0), (-1,-1), 5),
        ('LEFTPADDING',  (0,0), (-1,-1), 6),
        ('RIGHTPADDING', (0,0), (-1,-1), 6),
        ('VALIGN',       (0,0), (-1,-1), 'TOP'),
    ]))
    return t


def build_foreword(out_path):
    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM)
    story = []

    # ── Title block ──────────────────────────────────────────────────────────
    story += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('A Foreword for the General Reader', S['subtitle']),
        Paragraph('April 2026  |  v1.4', S['date']),
        sp(10),
        Paragraph(
            'The paradox is not that zero is nothing.<br/>'
            'The paradox is that zero is the one thing<br/>'
            'that has to be there for everything else to exist —<br/>'
            'and is the one thing the tools of everything else cannot reach.',
            S['epigraph']),
        sp(8),
        hr(),
    ]

    # ── I. THE QUESTION ───────────────────────────────────────────────────────
    story += [
        Paragraph('I. THE QUESTION', S['h1']),
        Paragraph(
            'Mathematics has always had a complicated relationship with zero. '
            'The word “zero” does not name a single object — it names a role, '
            'and that role is filled differently depending on the framework. '
            'In arithmetic, zero is the additive identity: the number that leaves everything '
            'unchanged when you add it. '
            'In set theory, zero is the empty set <font name="DV">&#8709;</font>: the foundation from which the '
            'hierarchy of numbers is constructed. '
            'In algebra — vector spaces, rings, modules — zero is the neutral element '
            'of addition, inheriting whatever structure the framework provides. '
            'In logic, the corresponding element is falsehood: the proposition that implies '
            'everything and is implied by nothing. '
            'In every case, zero occupies the same structural position: it is where things start.',
            S['body']),
        Paragraph(
            'This raises two questions that are easy to state and surprisingly hard to answer. '
            'The first is structural: what are the properties of that starting element itself? '
            'Not what comes after it — that is the story of mathematics as we know it. '
            'But the ground floor. The state before any state. '
            'The second question is generative: across all these frameworks, is there a common '
            'account of what it means to transition from the null element to the first non-trivial '
            'state? Can that emergence be given a rigorous, multi-framework description?',
            S['body']),
        Paragraph(
            'These two questions are related but distinct. The first is about the properties of '
            '⊥. The second is about the transition ⊥ → ε₀. '
            'The Zero Paradox framework addresses both.',
            S['body']),
    ]

    story.append(box(
        'The central claim is this: zero is not the absence of mathematical structure. It is '
        'the presence of structure at its most fundamental — the element that is '
        'constituent of everything and directly describable by nothing.'
    ))
    story.append(sp(6))

    story += [
        Paragraph(
            'A note on the converse: one might observe that in any rich framework, zero is the '
            'trivial element — it inherits its structure from the framework around it. '
            'This is true, and it is not in conflict with ZP\'s thesis. '
            'The question ZP is asking is how minimal the framework needs to be before ⊥ '
            'still has non-trivial properties. '
            'The answer, across eight independent layers, is: very minimal. That is the surprise.',
            S['body']),
    ]

    # ── II. THE ARCHITECTURE ─────────────────────────────────────────────────
    story += [
        Paragraph('II. THE ARCHITECTURE', S['h1']),
        Paragraph(
            'The framework is built in eight layers, each self-contained within its own '
            'mathematical discipline, each contributing one dimension of the full picture. '
            'No layer is allowed to borrow from another until that other is internally closed.',
            S['body']),
        Paragraph(
            'The algebraic layer (ZP-A) works entirely within join-semilattice theory. '
            'It derives that ⊥ is the global minimum of the induced partial order, and that '
            'any sequence of states generated by repeated joins is monotone. '
            'Monotonicity is a theorem here, not an assumption.',
            S['body']),
        Paragraph(
            'The topological layer (ZP-B) works within p-adic number theory. '
            'From the single axiom that the foundational distinction is binary, together with '
            'a minimality principle, it derives that the appropriate field is Q₂, the '
            '2-adic numbers. The field Q₂ forces every ball to be clopen, which forces '
            'total disconnectedness, which makes the transition from null to first state '
            'topologically irreversible. This is proven, not assumed.',
            S['body']),
        Paragraph(
            'The information-theoretic layer (ZP-C) works within algorithmic information '
            'theory and discrete analysis on Q₂. It introduces the incompressibility '
            'threshold and establishes the informational cost of the null-to-first-state '
            'transition as exactly one bit. It also establishes — in v1.4 — that the '
            'act of execution is itself a non-null state, which allows the Binary Snap to be '
            'derived rather than assumed.',
            S['body']),
        Paragraph(
            'The Hilbert space layer (ZP-D) constructs an explicit map T from Q₂ into a '
            'complex Hilbert space H = ℂⁿ, with topological isolation in Q₂ '
            'corresponding to orthogonality in H. T is proven to exist and to be unique up to '
            'unitary equivalence.',
            S['body']),
        Paragraph(
            'The bridge layer (ZP-E) is written last. It connects all prior frameworks, traces '
            'every cross-framework claim to specific theorems, and arrives at the closing result: '
            'the Binary Snap is a theorem, not an axiom.',
            S['body']),
        Paragraph(
            'The category-theoretic layer (ZP-G) recasts the entire framework within category '
            'theory. It establishes the categorical zero — the initial object 0 — '
            'as the object with a unique morphism to every other object and no incoming '
            'morphisms from outside. The informational singularity at 0 is derived '
            'independently of the prior layers, converging on the same result from a '
            'structurally different direction.',
            S['body']),
        Paragraph(
            'The categorical bridge (ZP-H) constructs four instantiation functors connecting '
            'the categorical framework to each of the prior layers: '
            'F<sub>A</sub>: C → SLat (lattice algebra), '
            'F<sub>B</sub>: C → pTop (p-adic topology), '
            'F<sub>C</sub>: C → InfoSp (information theory), and '
            'F<sub>D</sub>: C → Hilb (Hilbert space). '
            'Each functor preserves the initial object and the singularity structure, '
            'proving that all eight layers are consistent accounts of the same foundational fact.',
            S['body']),
        Paragraph(
            'The closure layer (ZP-I) proves T-IZ — the Inside Zero theorem: every '
            'maximal ascending chain in the state space converges to a new null state '
            'at its limit. This establishes that the framework is not merely an emergence '
            'theorem but a closed cycle: the Snap produces states, states accumulate, '
            'and the accumulation eventually produces a new ⊥. '
            'The framework contains its own recurrence.',
            S['body']),
    ]

    # ── III. THE FOUNDATIONAL COMMITMENTS ─────────────────────────────────────
    story += [
        Paragraph('III. THE FOUNDATIONAL COMMITMENTS', S['h1']),
        Paragraph(
            'Every formal system rests on commitments it does not derive. The Zero Paradox '
            'framework is unusually explicit about its own. As of the current version, this '
            'framework introduces no novel axioms. Stated explicitly: two structural commitments '
            '(grounded in prior layers), two methodological principles, one design commitment, '
            'one modeling commitment (MC-1), and two conditional claims (CC-1, CC-2):',
            S['body']),
        Paragraph(
            'A note on metatheory: this framework is stated over ZF + AFA '
            '(Zermelo–Fraenkel set theory with Aczel’s Anti-Foundation Axiom), '
            'not standard ZFC. AFA permits self-containing sets — in particular, sets x '
            'satisfying x = {x}. This matters only for CC-2 in the table below; '
            'every other result in this framework holds in standard ZF. Standard ZFC is '
            'incompatible with CC-2: a well-founded ⊥ would admit an external interpreter, '
            'contradicting the self-execution argument. The Axiom of Choice is not assumed.',
            S['body']),
        commitments_table(),
        sp(8),
    ]

    # ── IV. THE PARADOX ───────────────────────────────────────────────────────
    story += [
        Paragraph('IV. THE PARADOX', S['h1']),
        Paragraph(
            'Zero — the null state ⊥, the element 0 ∈ Q₂, the vector '
            'T(0) ∈ H, the initial object in C — is the foundational element of every '
            'layer of the framework. '
            'Algebraically, ⊥ ≤ x for all x in L. '
            'Topologically, 0 is the base of every ball in Q₂. '
            'In Hilbert space, T(0) is the anchor from which every state vector is built. '
            'Categorically, 0 is the unique object with a morphism to every other. '
            'Zero is not prior to the framework. It is structurally present within every '
            'element of it.',
            S['body']),
    ]

    story.append(box(
        'At the same time: zero is the unique point in the framework where the standard '
        'tools of mathematical description fail. Not by accident. Not by inadequacy of '
        'construction. By necessity.'
    ))
    story.append(sp(6))

    # ── V. THE RESOLUTION ─────────────────────────────────────────────────────
    story += [
        Paragraph('V. THE RESOLUTION', S['h1']),
        Paragraph(
            'The paradox is resolved — not dissolved. The resolution provides the correct '
            'tools for working at the boundary: the discrete operators of ZP-C, native to '
            'Q₂, requiring no smoothness.',
            S['body']),
        Paragraph(
            'Under these operators, finite paths through Q₂ \\ {0} are conservative. '
            'Non-conservation appears in the infinite regime: infinite sequences through the '
            'ball hierarchy approaching zero accumulate surprisal without bound. '
            'The surprisal field has a singularity at zero. '
            'Every infinite path toward the foundational element encounters unbounded '
            'informational content.',
            S['body']),
        Paragraph(
            'The framework lives at that boundary intentionally. The eight layers — '
            'algebra, topology, information theory, Hilbert space, bridge, category theory, '
            'categorical bridge, and closure — each arrive independently at the same boundary '
            'from their own direction. That convergence is the framework\'s central result.',
            S['body']),
    ]

    story.append(box(
        'The Null State remains indescribable by smooth calculus. It becomes fully '
        'characterised by discrete calculus. The paradox is the precise boundary between '
        'these two regimes.'
    ))
    story.append(sp(6))

    # ── VI. WHAT THIS IS AND IS NOT ───────────────────────────────────────────
    story += [
        Paragraph('VI. WHAT THIS IS AND IS NOT', S['h1']),
        Paragraph(
            'This is a rigorous mathematical framework. Every theorem is proved from stated '
            'axioms and principles. Every cross-framework claim is traced to specific theorems '
            'with explicit bridge axioms where required.',
            S['body']),
        Paragraph(
            'This is not a physical theory. The framework is instantiation-independent. '
            'Physical theories are recovered by instantiating the free parameters. '
            'The minimum viable deviation ε₀ plays the structural role of a '
            'Planck-scale quantity, but its numerical value depends on the physical constants '
            'of the universe.',
            S['body']),
        Paragraph(
            'This is not a claim about consciousness, qualia, or the hard problem. '
            'The framework is silent on these questions.',
            S['body']),
        Paragraph(
            'The open commitments are honest. No novel axioms are introduced. '
            'Two structural commitments, two principles, one design commitment, '
            'one modeling commitment, and two conditional claims are stated. '
            'The framework does not launder their status. '
            'AX-B1 — binary existence — is not a novel commitment: it is directly verifiable '
            'by computation. Whether a finite type has two distinct elements requires no '
            'classical axioms — it can be decided mechanically. The theorems stand on their '
            'own axioms regardless.',
            S['body']),
    ]

    # ── VII. A NOTE ON READING THE DOCUMENTS ──────────────────────────────────
    story += [
        Paragraph('VII. A NOTE ON READING THE DOCUMENTS', S['h1']),
        Paragraph(
            'The technical documents ZP-A through ZP-I are formatted as ontologies, not as '
            'discursive mathematical writing. Each claim appears in a labeled box with its '
            'status — Axiom, Principle, Design Commitment, Defined, Derived, Conditional, '
            'or Remark. Proofs are included inline. Open items are tracked explicitly.',
            S['body']),
        Paragraph(
            'A mathematician reading ZP-A will find it elementary — basic semilattice '
            'theory with clean proofs. The novelty is not in the mathematics of any single '
            'layer. It is in the discipline of the connections: the requirement that each layer '
            'be internally closed before any cross-framework claim is made.',
            S['body']),
        Paragraph(
            'The bridge document ZP-E is worth reading last, after the four constituent '
            'algebraic, topological, information-theoretic, and Hilbert space layers, because '
            'it earns its claims in the only way that counts — by pointing back to proofs '
            'that are already complete. ZP-H plays an analogous role for the category-theoretic '
            'side: read it after ZP-G.',
            S['body']),
        Paragraph(
            'The mathematics here is not new in its parts. Join-semilattices, p-adic numbers, '
            'Jensen-Shannon divergence, Hilbert space basis assignment, initial objects in '
            'category theory — these are established structures with well-understood '
            'properties. What is new is the conjunction: the claim that these seven structures, '
            'independently developed within their own disciplines, converge on the same '
            'foundational point, characterise the same transition, and illuminate the same '
            'paradox from seven different directions.',
            S['body']),
        Paragraph(
            'The answer, if the framework holds, is that zero is not the absence of everything. '
            'It is the presence of the minimum sufficient condition for everything — the '
            'one element that every state inherits, that every measurement is taken from, that '
            'every description presupposes, and that no description, in the standard sense, '
            'can reach.',
            S['body']),
    ]

    # ── VIII. WHERE THE FRAMEWORK REACHES ────────────────────────────────────
    story += [
        Paragraph('VIII. WHERE THE FRAMEWORK REACHES', S['h1']),
        Paragraph(
            'The Generation 1 result — the Binary Snap as a derived theorem — '
            'has structural consequences beyond the framework itself. Under stated conditions '
            'and with explicit assumptions, it bears on several problems that have remained '
            'open in physics, mathematics, and philosophy.',
            S['body']),
        Paragraph(
            'The most direct connection is to the arrow of time. The irreversibility of the '
            'Binary Snap — derived independently in ZP-A (monotonicity), ZP-B '
            '(topological irreversibility), and ZP-G (source asymmetry) — provides a '
            'structural account of temporal asymmetry that does not import the arrow of time '
            'as an assumption. Under the condition that the physical universe instantiates '
            '⊥ and ε₀ as its boundary states, the arrow of time is an instance '
            'of the Zero Paradox, not a separate phenomenon requiring separate explanation.',
            S['body']),
        Paragraph(
            'Further connections — to Leibniz\'s question of why there is something '
            'rather than nothing, to Wigner\'s puzzle about the unreasonable effectiveness '
            'of mathematics, to the fine-tuning problem in cosmology, and to Skolem\'s '
            'paradox in set theory — are developed in the companion document '
            '"Generation 2: Applications and Open Problems." '
            'Each case states its required assumptions explicitly, assesses fit honestly, '
            'and names the gaps that remain.',
            S['body']),
    ]

    doc.build(story)
    print(f'Written: {out_path}')


if __name__ == '__main__':
    repo_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    out = os.path.abspath(os.path.join(repo_root, 'Zero_Paradox_Foreword.pdf'))
    build_foreword(out)
