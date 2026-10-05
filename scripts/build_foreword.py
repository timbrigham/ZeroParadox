"""
Zero Paradox — Foreword PDF Builder (v2.33, revised October 2026)
Follows all rules in pdf rendering standards.md:
  - All table cells are Paragraph objects
  - No unicode subscripts — use sub/super tags
  - US Letter, 1-inch margins, TW = 6.5 inch
"""

import os
from zp_utils import *

VERSION = '2.33'
FIRST_RELEASED = 'April 2026'

# ── fix() and prose_check() guard on every Paragraph ──
# PDF Rendering Standards require fix() on all rendered text, and the vocabulary gate
# (prose_check) must see every string that renders, table cells and callout boxes included.
# Rather than updating every call site, patch Paragraph here so it applies both.
_Paragraph_orig = Paragraph
def Paragraph(text, style):
    if isinstance(text, str):
        prose_check(text)
        text = fix(text)
    return _Paragraph_orig(text, style)

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
        ('AX-B1', 'Modeling Commitment (the substantive one)',
         'Binary Existence. A state either exists or it does not — existence is discrete/Boolean, '
         'not a continuum of partial existence. This is the framework&#8217;s one substantive modeling '
         'commitment: the decide proof (ax_b1_distinct) verifies the two states are distinct given the '
         'two-element type, but the choice of a discrete alphabet over a continuum is the commitment '
         'itself, not what decide checks (the snap provably fails in the reals, f_snap_impossible).'),
        ('AX-G1', 'Axiom',
         'Initial Object Exists, and No Terminal Object. There is a starting point that reaches every object in exactly one way, '
         'and no end point that every object reaches in exactly one way. '
         'The starting point is not a novel commitment — the existence of ⊥ as the bottom element of the ZP-A '
         'semilattice already guarantees it. The absence of an end point is ZP-G&#8217;s own commitment: in ZP-A it is '
         'an optional hypothesis, which ZP-A&#8217;s two-state carriers do not satisfy.'),
        ('AX-G2', 'Axiom',
         'Source Asymmetry. No morphism returns to the initial object from outside. '
         'Not a novel commitment where the category is built from an order: there a morphism into the bottom '
         'forces equality by antisymmetry (on the order of ℕ, isEmpty_hom_one_to_zero), and in any category '
         'whose initial object is strict it follows (ax_g2_from_strict_initial). It is not automatic in every '
         'category: in the Hilbert-space realization a morphism does return to the initial object (fD_has_return). '
         'ZP-B C3 is its topological analogue: no path in Q₂ returns to 0.'),
        ('MP-1',  'Principle',
         'Minimality of Representation. The representational base must be the minimum '
         'sufficient base for AX-B1. Derives p = 2.'),
        ('RP-1',  'Principle',
         'Minimum Sufficient Probabilistic Representation. The probabilistic form of a '
         'binary state is a point-mass distribution.'),
        ('DP-1',  'Design Commitment',
         'Orthogonality. Clopen separation in Q₂ is represented by orthogonality '
         'in H. Chosen, not derived. Stated explicitly.'),
        ('AX-1',  'Retired: shape → Theorem T-SNAP; the snap occurs given the occurrence commitment and DA-1',
         'Binary Snap Causality. Previously an axiom, now retired. Its content was split in two: the shape of the Snap '
         'is proved, as Theorem T-SNAP (from L-RUN, TQ-IH and the bottom law, with no Lean kernel axioms), and that the Snap occurs '
         'is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2). '
         '(tsnap_holds_but_nothing_moves shows T-SNAP does not carry occurrence.)'),
        ('MC-1',  'The bottom family (not a commitment)',
         'The four domain bottoms (ZP-A semilattice, ZP-B p-adic topology, ZP-C information theory, '
         'ZP-D Hilbert space) form one family, each a member characterized by shared criteria and the '
         'same diagonal fixed-point shape. Membership is proved per domain: mc1_correspondence '
         '(ZeroParadox/Multihomed/MC1Bridge.lean) bundles the realizations in three genuine categories '
         '(Hilbert space, information, p-adic topology), and ZP-H&#8217;s four functors run into stand-in categories. The former '
         'numerical identity — that the four are one object — is retired as ill-typed (object equality across '
         'categories does not typecheck and is not invariant under equivalence); what separates the members is '
         'proved property by property (seam_unique_among_named, ZeroParadox/Category/SeamUniqueness.lean, for the named bottoms, in a lattice with no top).'),
        ('CC-1',  'Conditional Claim (restated in ZP-J, not forced)',
         'S₀ = ⊥. The initial state equals the bottom element ⊥ of the state semilattice. T2 establishes ⊥ ≤ S₀ unconditionally; '
         'the strengthening to equality is a modelling commitment. ZP-J restates it: in any AFAStructure '
         'lattice a sequence starts at a Quine atom exactly when it starts at ⊥ (cc1_derived, t_exec_iff; '
         'axiom-free, Lean), so the choice of starting point is expressed through the Quine-atom role, not removed.'),
        ('CC-2',  'Forced Metatheoretic Commitment',
         '⊥ = {⊥}. The bottom element is self-containing, read under ZF+AFA as a Quine atom. '
         'Foundation cannot host it: ⊥ = {⊥} is a member of itself, which Foundation (the Axiom of '
         'Regularity) forbids (no_quine_atom). That half is forced, and it runs one way: a host of a '
         'self-membered bottom is not well-founded (quineHost_not_wellFounded). Run backwards it selects no '
         'theory: which anti-foundation axiom to adopt is a further choice, and the framework adopts AFA as '
         'the canonical host (ZP-E Remark R-AFA). '
         'Fixed-point content formally verified in ZFC by ZP-J (ScaleBridge). '
         'The set-theoretic interpretation is given in ZF+AFA.'),
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
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['date']),
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
            'But the ground floor. The state before any state — called the bottom element (written ⊥). '
            'The second question is generative: across all these frameworks, is there a common '
            'account of what it means to transition from the bottom element to the first non-trivial '
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
            'The answer, layer after layer, is: very minimal. That is the surprise.',
            S['body']),
    ]

    # ── II. THE ARCHITECTURE ─────────────────────────────────────────────────
    story += [
        Paragraph('II. THE ARCHITECTURE', S['h1']),
        Paragraph(
            'The framework is built in layers, each self-contained within its own '
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
            'total disconnectedness, which makes the transition from zero to the first state '
            'topologically irreversible. This is proven, not assumed.',
            S['body']),
        Paragraph(
            'The information-theoretic layer (ZP-C) works within algorithmic information '
            'theory and discrete analysis on Q₂. It introduces the incompressibility '
            'threshold and establishes the informational cost of the zero-to-first-state '
            'transition as exactly one bit. It also establishes that the '
            'act of execution is itself a state above the bottom element (c₁, the first running '
            'configuration), which allows the shape of the Binary Snap to be derived rather than assumed.',
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
            'the shape of the Binary Snap is a theorem, not an axiom, and that the Snap occurs follows from the occurrence commitment together with DA-1.',
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
            'ZP-H constructs four instantiation functors F<sub>A</sub>, F<sub>B</sub>, F<sub>C</sub>, '
            'F<sub>D</sub>, one for each prior layer (lattice algebra, p-adic topology, information theory, '
            'Hilbert space). Each runs from the depth order on ℕ into a stand-in category for its layer and '
            'sends 0 to that category&#8217;s initial object. Three of them are also built into genuine '
            'categories, bundled as mc1_correspondence (ZeroParadox/Multihomed/MC1Bridge.lean): there 0 is '
            'initial in the Hilbert-space and information realizations and a limit in the p-adic one. That '
            'the layers describe one object is the reading MC-1 retires; what the functors carry is each '
            'layer&#8217;s member of the bottom family.',
            S['body']),
        Paragraph(
            'The closure layer (ZP-I) proves T-IZ — the Inside Zero theorem: every '
            'maximal ascending chain in the state space converges, at its limit, to zero. '
            'Reading that limit as something filling the bottom role again is a commitment '
            'rather than a consequence; what is proved is the other half, that anything '
            'filling that role IS the bottom already there. '
            'Read as a closed cycle, the Snap produces states, states accumulate, and the '
            'accumulation returns to the bottom. Whether the bottom it returns to is a NEW one, '
            'rather than the one it began at, is a modelling commitment (C-DA2) and not part of '
            'what T-IZ proves; in the 2-adic chart the arc comes back to the same zero.',
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
            'The self-reference layer (ZP-J) proves T-EXEC: in any ZP-A lattice carrying the '
            'AFAStructure typeclass, whatever fills the Quine-atom role (the lattice encoding of the set Q = {Q}) is ⊥, axiom-free. '
            'CC-1 (S₀ = ⊥) is restated as an equivalence, not forced: a sequence starts at a Quine atom exactly when it starts at ⊥, and on any lattice with a second point a valid sequence can start above ⊥. The layer also formalises the '
            'ZF+Foundation / ZF+AFA relationship and proves APG decoration uniqueness — every '
            'finite self-referential graph has at most one consistent decoration into the lattice.',
            S['body']),
        Paragraph(
            'The computational grounding layer (ZP-K) proves T-COMP: a three-way equivalence '
            'connecting the Quine atom, ⊥, and the join-identity element. Kleene\'s fixed point '
            'is not a fourth clause of it - the computational face enters as an assumption of the '
            'KleeneStructure class. da1_closed_concrete proves the structural half of DA-1, that '
            'c₀, the bottom of the two-state carrier MachinePhase, is a Quine atom; it mentions no code '
            'and no execution. That c₀ is self-executing is DA-1&#8217;s claim, and DA-1&#8217;s '
            'precondition is the occurrence commitment, which DA-1 consumes rather than proves (ZP-E Section IV).',
            S['body']),
        Paragraph(
            'The incomputability convergence layer (ZP-L) establishes ε₀ — the first '
            'ordinal fixed point of ω^x — as the formal snap threshold. It connects '
            'ordinal arithmetic, p-adic convergence, and Rogers\' fixed-point stability '
            'in a single canonical snap map. Its Lean development is ZeroParadox/Ordinal/Gentzen.lean.',
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
            'framework introduces one novel axiom clause, and names it. Among the commitments stated explicitly: one substantive modeling '
            'commitment (AX-B1), two structural commitments (AX-G1, AX-G2) grounded in prior layers except for '
            'AX-G1&#8217;s no-terminal half, which is ZP-G&#8217;s own, '
            'two methodological principles, and one design commitment. CC-1 is a Conditional Claim that ZP-J restates rather than forces, CC-2 '
            'is a Forced Metatheoretic Commitment, and MC-1 names the bottom family rather than a commitment:',
            S['body']),
        Paragraph(
            'A note on metatheory: this framework is stated over ZF + AFA '
            '(Zermelo–Fraenkel set theory with Aczel\'s Anti-Foundation Axiom), '
            'not standard ZFC. AFA permits self-containing sets — in particular, sets x '
            'satisfying x = {x}. This matters only for CC-2 in the table below; '
            'every other result in this framework holds in standard ZF. Standard ZFC (with '
            'Foundation) is incompatible with CC-2: ⊥ = {⊥} is a member of itself, which the Axiom of '
            'Regularity forbids (no set is self-membered, no_quine_atom), so a Foundation universe '
            'cannot host it. The Axiom of Choice is not assumed '
            'as a framework commitment, and the core does not use it: T-SNAP (t_snap_derived) '
            'depends on no Lean kernel axioms at all. Classical.choice does reach the realization '
            'layers, and not only by inheritance from Mathlib — the category-theory layer spends a '
            'bare classical written in framework source (fixedPointFree_of_nontrivial, in '
            'ZeroParadox/Category/Lawvere.lean), and that one is essential rather than incidental, '
            'since wem_of_fixedPointFree derives weak excluded middle from the general '
            'fixed-point-free principle. Where a dependence comes from and whether it can be '
            'removed are independent questions: an inherited dependence can be essential too '
            '(em_of_wellOrder_comparable, on Mathlib\'s InitialSeg.total). The measured footprints '
            'are a checkable artifact — ZeroParadox/AxiomProfile.lean, with ZP-K Section IV '
            'holding a dated measurement table for the computability layer.',
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
            'Zero — the bottom element ⊥ of the state semilattice L, the element 0 ∈ Q₂, the vector '
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
            '(⊥ = {⊥}). In computation it is read as the self-reproducing program, the fixed point of '
            'Kleene\'s recursion theorem — a process that runs on its own description. In the '
            '2-adic numbers it is the point infinitely divisible into itself, v₂(0) = ∞. '
            'In category theory it is the initial object, the source from which every arrow '
            'departs and to which none return. These are not loose analogies. The framework '
            'read them as faces of one object: a self-referential fixed point. It proves '
            'the lattice, 2-adic and categorical faces in their own domains and carries the '
            'computational one as a requirement; that they are one object is the reading the next '
            'paragraph retires.',
            S['body']),
        Paragraph(
            'Mathematics already has a name for this shape, and a theorem that unifies it: '
            'Lawvere\'s fixed-point theorem (1969) shows that Cantor\'s diagonal argument, '
            'Russell\'s paradox, the fixed-point lemma at the heart of Gödel\'s incompleteness, '
            'and Tarski\'s undefinability theorem are one move — the diagonal, the turn of a system '
            'back on itself. Yanofsky (2003) restated this in plain set-and-function terms and '
            'extended it across logic and computation, where it reaches Turing\'s halting argument '
            'and Kleene\'s recursion theorem. What is unusual in the Zero Paradox is '
            'its location. '
            'Self-reference is normally a ceiling phenomenon: it appears at the limits of a '
            'system, in the sentences a theory cannot prove about itself. Here it sits at the '
            'floor. The Zero Paradox locates this diagonal fixed point at the bottom of every '
            'framework. The framework formalises these faces as instances of a single '
            'self-application structure and proves membership per domain. Whether they are '
            'all one object is not an open question but a retired one: it is retired as ill-typed '
            '(object equality across categories does not typecheck and is not invariant under '
            'equivalence). What survives is the family.',
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
            'Each layer arrives at the same boundary '
            'from its own direction. That convergence is the framework\'s central result.',
            S['body']),
    ]

    story.append(box(
        'Zero, the bottom element ⊥, remains indescribable by smooth calculus. It becomes fully '
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
            'The open commitments are honest. The one novel axiom clause is named: AX-G1&#8217;s no-terminal half, '
            'ZP-G&#8217;s own. '
            'One substantive modeling commitment (AX-B1), two structural commitments, two principles, '
            'and one design commitment are stated; CC-1 is a Conditional Claim restated in ZP-J, CC-2 is a Forced Metatheoretic '
            'Commitment, and MC-1 is the bottom family. The framework does not launder their status. '
            'AX-B1 — binary existence — is the framework&#8217;s one substantive modeling commitment: '
            'that existence is discrete rather than a continuum of partial states. The decide proof '
            '(ax_b1_distinct) checks only that the two states are distinct given the two-element type; '
            'the discreteness choice itself is the commitment, and the snap provably fails on a '
            'continuum (f_snap_impossible). The theorems stand on their own axioms regardless.',
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
            'paradox from different directions.',
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
