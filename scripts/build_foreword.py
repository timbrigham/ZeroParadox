"""
Zero Paradox — Foreword PDF Builder (v2.7, revised June 2026)
v2.7: §IV — named Lawvere's fixed-point theorem as the recognized unification of the diagonal family
      (Cantor / Russell / the fixed-point lemma at the heart of Gödel / Kleene); fence firmed —
      "the bottom IS its diagonal fixed point" → "the Zero Paradox locates this diagonal fixed point at
      the bottom", so the true-Lawvere-fact and ZP's identification sit on different footings. AR pre-checked.
v2.6: §IV — added the diagonal fixed point keystone: ⊥ is the same self-referential fixed point
      across the layers (Quine atom / Kleene quine / v2(0)=inf / categorical initial as four faces);
      the Goedel inversion (self-reference at the floor, not the ceiling). Honesty fence kept: the full
      cross-framework unification is stated as an identification, not a closed theorem.
v2.5: AR fix — "provable fact in standard ZFC" → "standard ZF" in §III porthole passage.
      AR fix — residual "DA-1 is the bridge" → "connecting argument" (in PhilQ; Foreword unaffected).
v2.4: fix() guard added via Paragraph override — all rendered text now goes through unicode-to-entity conversion.
      ER kills: "v1.4" version refs removed; "categorical bridge" → "ZP-H"; CC-1 conditionality qualified;
      "All 24" → "All 25"; "ZP-A through ZP-I" → "ZP-A through ZP-M" in §VII; "ZFC/AFA" → "ZF+Foundation/ZF+AFA";
      "binary ontological state" → "binary state"; null state gloss added at first occurrence.
v2.3: ER/AR fixes — "linearly ordered field" → "densely ordered field" (F-1/F-2).
      §V "ten layers" → "thirteen" with simplified enumeration (F-6).
      AR scoping: "formal signature" clauses qualified with "in ZP's reading" (both passages).
v2.2: §II architecture updated to thirteen layers — ZP-F, ZP-J, ZP-K, ZP-L, ZP-M added.
      Layer counts corrected throughout (was eleven/ten). "Topological isolation" →
      "clopen separation" (vocabulary fix). "Seven structures" count corrected.
      AR fix: "see the same mathematical object" → "share the same arithmetic fact."
v2.1: §III porthole metaphor — "orthogonal" replaced with porthole image in prose.
      Wall is solid and opaque; one piece of glass (v₂(0) = ∞) does not open but lets
      both frameworks see the same object. "Orthogonal" retained in technical contexts.
v2.0: §III metatheory note extended — orthogonal frameworks / contact point framing.
      ZF+AFA and ZFC are mutually exclusive but meet at one contact point: v₂(0) = ∞.
      Clarifies that ZP is not a bridge between them but an identification of that point.
v1.9: AR fix — callout box "from which every state is reachable by joins" →
"the element below which no other state exists" — corrects imprecise constructive
reachability phrasing to match what T2 actually proves.
v1.8: Adversary-review pass — epigraph removed; Section VIII (WHERE THE FRAMEWORK REACHES)
cut entirely (applications content belongs in Gen2 document); Planck-scale analogy removed
from Section VI (ε₀ is a structural threshold, not a physical constant); callout box in
Section I rewritten ("directly describable by nothing" → precise algebraic description).
v1.7: Added note to Section III clarifying ZP-K's Classical.choice dependency is a standard
Lean infrastructure axiom, not a novel framework commitment — addresses 4.7 from outside review.
v1.6: AX-B1 status changed from "Decidable" to "Directly Verifiable"; plain-language description
replaces Lean jargon ("decidable equality on finite types"); in-PDF date corrected to May 2026.
v1.5: Layer count updated throughout — framework now has ten formal layers (ZP-J, ZP-K added).
v1.4: Metatheoretic note (ZF+AFA) added in Section III before the commitments table.
v1.3: Fix ∅ rendering — was showing as a rectangle in DejaVuSerif; now forced through DV (DejaVuSans) via <font> tag.
Follows all rules in pdf rendering standards.md:
  - All table cells are Paragraph objects
  - No unicode subscripts — use sub/super tags
  - US Letter, 1-inch margins, TW = 6.5 inch
"""

import os
from zp_utils import *

VERSION = '2.7'

# ── fix() guard: ensures all Paragraph text goes through Unicode-to-entity conversion ──
# PDF Rendering Standards require fix() on all rendered text. Rather than updating
# every call site, patch Paragraph here so it applies fix() automatically.
_Paragraph_orig = Paragraph
def Paragraph(text, style):
    return _Paragraph_orig(fix(text) if isinstance(text, str) else text, style)

# ── Local overrides: Foreword uses TEAL theme and slightly larger body text ──
S['title']    = ParagraphStyle('title',    fontName='DV-B',  fontSize=20, leading=26,
                                spaceAfter=4, alignment=1)
S['date']     = ParagraphStyle('date',     fontName='DV',    fontSize=10, leading=14,
                                spaceAfter=6, alignment=1)
S['epigraph'] = ParagraphStyle('epigraph', fontName='DVS-I', fontSize=11, leading=17,
                                spaceAfter=4, alignment=1, textColor=TEAL)
S['h1']       = ParagraphStyle('h1',       fontName='DV-B',  fontSize=13, leading=18,
                                spaceBefore=16, spaceAfter=6, textColor=TEAL)
S['body']     = ParagraphStyle('body',     fontName='DVS',   fontSize=10, leading=15,
                                spaceAfter=8)
S['bodyI']    = ParagraphStyle('bodyI',    fontName='DVS-I', fontSize=10, leading=15,
                                spaceAfter=8, alignment=1, textColor=TEAL)


def box(text):
    """Teal-bordered italic callout box."""
    data = [[Paragraph(text, S['bodyI'])]]
    t = Table(data, colWidths=[TW - 0.4*inch])
    t.setStyle(TableStyle([
        ('BOX',          (0,0), (-1,-1), 1.0, TEAL),
        ('BACKGROUND',   (0,0), (-1,-1), TEAL_LITE),
        ('TOPPADDING',   (0,0), (-1,-1), 10),
        ('BOTTOMPADDING',(0,0), (-1,-1), 10),
        ('LEFTPADDING',  (0,0), (-1,-1), 14),
        ('RIGHTPADDING', (0,0), (-1,-1), 14),
    ]))
    return t


def commitments_table():
    headers = [
        Paragraph('Label', S['label']),
        Paragraph('Type', S['label']),
        Paragraph('Statement', S['label']),
    ]
    rows = [
        ('AX-B1', 'Directly Verifiable',
         'Binary Existence. A state either exists or it does not. '
         'Not a novel commitment — directly verifiable by computation rather than requiring '
         'a leap of faith. The distinction between null and exist can be checked by a finite procedure.'),
        ('AX-G1', 'Axiom',
         'Initial Object Exists. There is a starting point that reaches every other object. '
         'Not a novel commitment — the existence of ⊥ as the bottom element of the ZP-A semilattice already guarantees this; ZP-G names it in categorical language.'),
        ('AX-G2', 'Axiom',
         'Source Asymmetry. No morphism returns to the initial object from outside. '
         'Not a novel commitment — follows from antisymmetry of the ZP-A partial order and ZP-B C3 (topological irreversibility).'),
        ('MP-1',  'Principle',
         'Minimality of Representation. The representational base must be the minimum '
         'sufficient base for AX-B1. Derives p = 2.'),
        ('RP-1',  'Principle',
         'Minimum Sufficient Probabilistic Representation. The probabilistic form of a '
         'binary state is a point-mass distribution.'),
        ('DP-1',  'Design Commitment',
         'Orthogonality. Clopen separation in Q₂ is represented by orthogonality '
         'in H. Chosen, not derived. Stated explicitly.'),
        ('AX-1',  'Retired axiom → Theorem T-SNAP',
         'Binary Snap Causality. Previously an axiom; now derived as Theorem T-SNAP via '
         'the L-RUN / TQ-IH / DA-1 chain in ZP-C and ZP-E.'),
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
        ('CC-2',  'Forced Metatheoretic Commitment',
         '⊥ = {⊥}. The null state is self-containing — a Quine atom under ZF+AFA. '
         'The metatheoretic choice of AFA over Foundation is not free: Foundation is ruled out '
         'by R3 and ZP-C L-INF. Foundation and AFA are dual framings of the same object — '
         'Foundation excludes the Quine atom; AFA uniquely permits it. '
         'Fixed-point content formally verified in ZFC by ZP-J (ZPJ_ScaleBridge). '
         'Set-theoretic interpretation requires ZF+AFA.'),
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
        ('BACKGROUND',    (0,0), (-1,0),  TEAL),
        ('TEXTCOLOR',     (0,0), (-1,0),  WHITE),
        ('ROWBACKGROUNDS',(0,1), (-1,-1), [WHITE, colors.HexColor('#F5F9F9')]),
        ('BOX',           (0,0), (-1,-1), 0.5, colors.HexColor('#AAAAAA')),
        ('INNERGRID',     (0,0), (-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 6),
        ('RIGHTPADDING',  (0,0), (-1,-1), 6),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ]))
    return t


def build():
    out_path = os.path.join(PROJECT_ROOT, 'Zero_Paradox_Foreword.pdf')
    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM)
    story = []

    # ── Title block ──────────────────────────────────────────────────────────
    story += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('A Foreword for the General Reader', S['subtitle']),
        Paragraph('June 2026  |  v' + VERSION, S['date']),
        sp(10),
        sp(8),
        hr(),
    ]

    # ── I. THE QUESTION ───────────────────────────────────────────────────────
    story += [
        Paragraph('I. THE QUESTION', S['h1']),
        Paragraph(
            'Mathematics has always had a complicated relationship with zero. '
            'The word "zero" does not name a single object — it names a role, '
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
            'But the ground floor. The state before any state — called the null state (written ⊥). '
            'The second question is generative: across all these frameworks, is there a common '
            'account of what it means to transition from the null state to the first non-trivial '
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
        'the unique minimal element of the induced partial order — the element below which '
        'no other state exists.'
    ))
    story.append(sp(6))

    story += [
        Paragraph(
            'A note on the converse: one might observe that in any rich framework, zero is the '
            'trivial element — it inherits its structure from the framework around it. '
            'This is true, and it is not in conflict with ZP\'s thesis. '
            'The question ZP is asking is how minimal the framework needs to be before ⊥ '
            'still has non-trivial properties. '
            'The answer, across thirteen independent layers, is: very minimal. That is the surprise.',
            S['body']),
    ]

    # ── II. THE ARCHITECTURE ─────────────────────────────────────────────────
    story += [
        Paragraph('II. THE ARCHITECTURE', S['h1']),
        Paragraph(
            'The framework is built in thirteen layers, each self-contained within its own '
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
            'transition as exactly one bit. It also establishes that the '
            'act of execution is itself a non-null state, which allows the Binary Snap to be '
            'derived rather than assumed.',
            S['body']),
        Paragraph(
            'The Hilbert space layer (ZP-D) constructs an explicit map T from Q₂ into a '
            'complex Hilbert space H = ℂⁿ, with clopen separation in Q₂ '
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
            'ZP-H constructs four instantiation functors connecting '
            'the categorical framework to each of the prior layers: '
            'F<sub>A</sub>: C → SLat (lattice algebra), '
            'F<sub>B</sub>: C → pTop (p-adic topology), '
            'F<sub>C</sub>: C → InfoSp (information theory), and '
            'F<sub>D</sub>: C → Hilb (Hilbert space). '
            'Each functor preserves the initial object and the singularity structure, '
            'proving that the four constituent frameworks are consistent accounts of the same foundational fact.',
            S['body']),
        Paragraph(
            'The closure layer (ZP-I) proves T-IZ — the Inside Zero theorem: every '
            'maximal ascending chain in the state space converges to a new null state '
            'at its limit. This establishes that the framework is not merely an emergence '
            'theorem but a closed cycle: the Snap produces states, states accumulate, '
            'and the accumulation eventually produces a new ⊥. '
            'The framework contains its own recurrence.',
            S['body']),
        Paragraph(
            'The counterexample layer (ZP-F) establishes the negative boundary: '
            'the Binary Snap cannot occur in any densely ordered field — '
            'structures where zero is a limit point of the nonzero elements. '
            'ℝ and ℚ are canonical instances. The proof is self-contained — '
            'no dependencies on the other layers — and answers the question of why Q₂ '
            'is structurally necessary by showing precisely where snap-geometry fails.',
            S['body']),
        Paragraph(
            'The self-reference layer (ZP-J) proves T-EXEC: in any ZP-A lattice with '
            'AFA grounding, the Quine atom Q = {Q} is provably identical to ⊥, axiom-free. '
            'CC-1 (S₀ = ⊥) follows as a derived theorem given that S₀ is identified with the Quine atom. The layer also formalises the '
            'ZF+Foundation / ZF+AFA relationship and proves APG decoration uniqueness — every '
            'finite self-referential graph has at most one consistent decoration into the lattice.',
            S['body']),
        Paragraph(
            'The computational grounding layer (ZP-K) proves T-COMP: a four-way equivalence '
            'connecting the Quine atom, ⊥, the join-identity element, and Kleene\'s fixed '
            'point. DA-1 is closed concretely here via da1_closed_concrete, grounding '
            'the framework in the theory of computation through Kleene\'s second recursion theorem.',
            S['body']),
        Paragraph(
            'The incomputability convergence layer (ZP-L) establishes ε₀ — the first '
            'ordinal fixed point of ω^x — as the formal snap threshold. It connects '
            'ordinal arithmetic, p-adic convergence, and Roger\'s fixed-point stability '
            'in a single canonical snap map. All 25 theorems are Lean-verified.',
            S['body']),
        Paragraph(
            'The Kleene-ordinal bridge (ZP-M) constructs an explicit type bridge '
            '(MachinePhase → ℤ₂), closes the free hypothesis gap from ZP-L, and '
            'co-proves the ordinal-2adic-phase triangle in a single theorem — '
            'the Kleene quine and ε₀ simultaneously witnessed in the same formal context.',
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
            'A note on metatheory: this framework is stated over ZF + AFA '
            '(Zermelo–Fraenkel set theory with Aczel\'s Anti-Foundation Axiom), '
            'not standard ZFC. AFA permits self-containing sets — in particular, sets x '
            'satisfying x = {x}. This matters only for CC-2 in the table below; '
            'every other result in this framework holds in standard ZF. Standard ZFC is '
            'incompatible with CC-2: a well-founded ⊥ would admit an external interpreter, '
            'contradicting the self-execution argument. The Axiom of Choice is not assumed '
            'as a framework commitment. One exception at the infrastructure level: ZP-K\'s '
            'Kleene computability machinery depends on Classical.choice as a standard Lean '
            'library axiom — the same dependency carried by any theorem using Mathlib\'s '
            'computability library, not a novel Zero Paradox commitment.',
            S['body']),
        Paragraph(
            'ZF+Foundation and ZF+AFA are not two theories this work bridges — '
            'they are mutually exclusive foundational choices. Choosing one forecloses '
            'the other. The right image is a porthole, not a bridge: a wall that is '
            'solid and opaque everywhere except one piece of glass. The glass does not '
            'open. Through it, both frameworks share the same arithmetic fact. '
            'That object is zero. In the 2-adic integers, zero is divisible by 2 '
            'infinitely many times — a provable fact in standard ZF. In ZF+AFA, '
            'the same fact carries additional weight: infinite 2-adic divisibility '
            'is, in ZP\'s reading, the formal signature of a set that contains only itself. '
            'This work is built in ZF+AFA because the question it asks is about '
            'that second reading — what the arithmetic of zero means at the '
            'foundation, not just what it computes.',
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
        Paragraph(
            'There is a deeper unity here than shared position. In each layer ⊥ is not merely '
            'the starting element — it is the same kind of element: the one that refers to '
            'itself. In set theory it is the Quine atom, the set whose only member is itself '
            '(⊥ = {⊥}). In computation it is the self-reproducing program, the fixed point of '
            'Kleene\'s recursion theorem — a process that runs on its own description. In the '
            '2-adic numbers it is the point infinitely divisible into itself, v₂(0) = ∞. '
            'In category theory it is the initial object, the source from which every arrow '
            'departs and to which none return. These are not loose analogies. The framework '
            'reads them as faces of one object: a self-referential fixed point. It proves '
            'several of those faces literally identical; how far that identity extends is '
            'the question the next paragraph returns to.',
            S['body']),
        Paragraph(
            'Mathematics already has a name for this shape, and a theorem that unifies it: '
            'Lawvere\'s fixed-point theorem shows that Cantor\'s diagonal argument, '
            'Russell\'s paradox, the fixed-point lemma at the heart of Gödel\'s incompleteness, '
            'and Kleene\'s recursion theorem are one move — the diagonal, the turn of a system '
            'back on itself. What is unusual in the Zero Paradox is its location. '
            'Self-reference is normally a ceiling phenomenon: it appears at the limits of a '
            'system, in the sentences a theory cannot prove about itself. Here it sits at the '
            'floor. The Zero Paradox locates this diagonal fixed point at the bottom of every '
            'framework. The framework formalises these faces as instances of a single '
            'self-application structure and proves several of them identical; whether they are '
            'all one object in the deepest sense remains, honestly, an identification we make '
            'rather than a theorem we have closed.',
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
            'The framework lives at that boundary intentionally. '
            'Thirteen independent layers each arrive at the same boundary '
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
            'This is not a physical theory. The framework is instantiation-independent — '
            'its results hold for any structure satisfying the axioms, not for our universe '
            'specifically. ε₀ is a structural threshold defined by the framework\'s axioms, '
            'not a physical constant.',
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
            'The technical documents ZP-A through ZP-M are formatted as ontologies, not as '
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
            'properties. What is new is the conjunction: the claim that these structures, '
            'independently developed within their own disciplines, converge on the same '
            'foundational point, characterise the same transition, and illuminate the same '
            'paradox from thirteen different directions.',
            S['body']),
        Paragraph(
            'The answer, if the framework holds, is that zero is not the absence of everything. '
            'It is the presence of the minimum sufficient condition for everything — the '
            'one element that every state inherits, that every measurement is taken from, that '
            'every description presupposes, and that no description, in the standard sense, '
            'can reach.',
            S['body']),
    ]

    doc.build(story)
    print(f'[build_foreword] Written: {out_path}')


if __name__ == '__main__':
    build()
