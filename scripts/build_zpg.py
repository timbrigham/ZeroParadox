"""
Zero Paradox — ZP-G: Category Theory PDF Builder
Version 1.34 | November 2026
"""

import os
from zp_utils import *

VERSION = '1.34'
FIRST_RELEASED = 'April 2026'

# ZP-G uses a slightly different amber shade; override zp_utils default
AMBER = colors.HexColor('#B07800')  # ZP-OVERRIDE: ZP-G import_box label text uses darker amber

# ZP-G import box uses amber-colored label text (not white)
S['labelAmber'] = ParagraphStyle('labelAmber', fontName='DV-B', fontSize=9, leading=13,
                                  textColor=AMBER)


def _box(title, title_style, hdr_bg, status, status_bg, rows):
    """ZP-G box with a status row between header and content rows."""
    data = [
        [Paragraph(fix(title), S[title_style])],
        [Paragraph(fix(status), S['cellI'])],
    ]
    for r in rows:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  hdr_bg),
        ('BACKGROUND',    (0,1), (-1,1),  status_bg),
        ('BACKGROUND',    (0,2), (-1,-1), GREY_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, hdr_bg),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, hdr_bg),
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


def def_box(title, status, rows):    return _box(title, 'label', BLUE,   status, BLUE_LITE,   rows)
def result_box(title, status, rows): return _box(title, 'label', GREEN,  status, GREEN_LITE,  rows)
def axiom_box(title, status, rows):  return _box(title, 'label', ORANGE, status, ORANGE_LITE, rows)
def remark_box(title, status, rows): return _box(title, 'label', SLATE,  status, SLATE_LITE,  rows)


def import_box(title, status, rows):
    """ZP-G import box — amber background, amber-text header (not white)."""
    data = [
        [Paragraph(fix(title), S['labelAmber'])],
        [Paragraph(fix(status), S['cellI'])],
    ]
    for r in rows:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), AMBER_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, AMBER),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, AMBER),
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


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-G_Category_Theory.pdf')
    print(f'[build_zpg] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-G: Category Theory', 'ZP-G: Category Theory', 'Version ' + VERSION)
    E   = []

    print('[build_zpg] Building title block...')
    # ── TITLE BLOCK ───────────────────────────────────────────────────────────
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-G: Category Theory', S['subtitle']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        sp(8),
        hr(),
        sp(4),
    ]

    # ── INTRO PARAGRAPHS ──────────────────────────────────────────────────────
    E += [
        body('This document is self-contained within category theory, with one explicit import from '
             'ZP-C: the conditional Kolmogorov complexity K(x|n) and the coding theorem, which bounds it '
             'by the surprisal of a computable measure. That import is named and labelled; it replaces Bridge '
             'Axiom BA-G1 (Leinster categorical entropy characterization) with a native derivation. All '
             'other content from ZP-A, ZP-B, ZP-D, and ZP-E remains excluded from this document. '
             'Cross-framework connections are deferred to ZP-H.'),
        body('Honest labelling is the governing discipline. Every claim is marked as Axiom, Definition, '
             'Derived, Import, Design Commitment, or Remark. Nothing slides between categories.'),
        body('<i>Illustrated Companion: A paired ZP-G Illustrated Companion provides concrete examples '
             'and visual intuitions for the results here. Examples are kept separate from the formal '
             'layers to distinguish illustrative material from proofs.</i>', 'bodyI'),
        sp(4),
        hr(),
    ]

    print('[build_zpg] Building Section I: Categorical Primitives...')
    # ── I. CATEGORICAL PRIMITIVES ─────────────────────────────────────────────
    E.append(Paragraph('I. Categorical Primitives', S['h1']))
    E.append(body('Definitions D1 through D6 and results T1 through T5 are reproduced here for completeness and self-reference.'))

    E.append(Paragraph('1.1 The Definition of a Category', S['h2']))
    E.append(def_box(
        'Definition D1 — Category',
        'Status: Definition — foundational',
        [
            'A category C consists of:',
            '(i) Objects: A collection ob(C), written A, B, X, 0, ...',
            '(ii) Morphisms: For each ordered pair (A, B), a collection hom(A, B) of morphisms, written f: A → B.',
            '(iii) Composition: ∘: hom(B,C) × hom(A,B) → hom(A,C), written g ∘ f.',
            '(iv) Identity: For each A, a morphism id<sub>A</sub>: A → A.',
            'Associativity: h ∘ (g ∘ f) = (h ∘ g) ∘ f.',
            'Unit laws: id<sub>B</sub> ∘ f = f = f ∘ id<sub>A</sub>.',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'Definition D2 — Morphism Uniqueness Notation',
        'Status: Definition',
        [
            'A morphism f: A → B is unique if for any g, h: A → B, g = h. Written: ∃! f: A → B.',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('1.2 Initial and Terminal Objects', S['h2']))
    E.append(def_box(
        'Definition D3 — Initial Object',
        'Status: Definition — load-bearing',
        [
            'An object 0 ∈ ob(C) is initial if for every X ∈ ob(C), there exists a unique morphism '
            '&#953;<sub>X</sub>: 0 → X.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Proposition T1 — Uniqueness of the Initial Object',
        'Status: Derived — standard category theory',
        [
            'If 0 and 0\' are both initial in C, ∃! isomorphism 0 ≅ 0\'. '
            'The initial object is unique up to unique isomorphism.',
            'Proof: ∃! f: 0 → 0\' and ∃! g: 0\' → 0. Initiality forces g ∘ f = id<sub>0</sub> and '
            'f ∘ g = id<sub>0\'</sub>. Therefore f is a unique isomorphism. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'Definition D4 — Terminal Object',
        'Status: Definition — defined for exclusion',
        [
            'An object 1 ∈ ob(C) is terminal if for every X ∈ ob(C), ∃! morphism '
            '&#964;<sub>X</sub>: X → 1. The Zero Paradox framework is not a zero object category (0 ≇ 1).',
        ]
    ))

    print('[build_zpg] Building Section II: Foundational Axioms...')
    # ── II. THE FOUNDATIONAL AXIOMS OF ZP-G ──────────────────────────────────
    E.append(Paragraph('II. The Foundational Axioms of ZP-G', S['h1']))

    E.append(axiom_box(
        'Axiom AX-G1 — Asymmetry Axiom',
        'Status: Axiom — foundational structural commitment',
        [
            'The category C possesses an initial object 0 and no terminal object.',
            'Formally: ∃ 0 ∈ ob(C) satisfying D3. ¬∃ 1 ∈ ob(C) satisfying D4.',
            'Correspondence: in ZP-A, a join-semilattice with &#8869; and without ∧; a carrier with no top is '
            'an optional hypothesis there, and ZP-A\'s two-state carriers have a top, so the no-terminal half '
            'is ZP-G\'s own commitment. '
            'In ZP-B\'s stand-in, the &#8469;-indexed ball-depth category that ZP-H\'s fb_functor (ZeroParadox/Multihomed/CategoricalBridge.lean) '
            'lands in, there is no terminal object because the depth index has no maximum; in TopCat, where the realization fB_functor '
            '(ZeroParadox/Valuation/TopFunctor.lean) lands, the one-point space '
            'is a terminal object, so AX-G1 fails there (ZP-H C-H2). '
            'The present axiom is the categorical generalization.',
        ]
    ))
    E.append(sp(6))

    E.append(axiom_box(
        'Axiom AX-G2 — Source Asymmetry',
        'Status: Axiom — foundational',
        [
            'For any non-initial object X (not isomorphic to 0): hom(X, 0) = ∅.',
            'Motivation: The categorical expression of irreversibility. Morphisms '
            '&#953;<sub>X</sub>: 0 → X exist for all X. Their reversal does not exist. '
            'AX-G2 is consistent with AX-G1 but not derivable from it.',
        ]
    ))
    E.append(remark_box(
        'Remark R-AX — On the Non-Triviality of AX-G1 and AX-G2',
        'Status: Remark',
        [
            'AX-G2 holds in many categories — it is a structural condition, not an exotic one. '
            'AX-G2 is the standard notion of a <i>strict initial object</i> (Carboni, Lack and Walters, 1993): '
            'an initial object into which every morphism is an isomorphism. Strict initial objects are the norm '
            'in well-behaved categories — the initial object of any topos, extensive category, or cartesian '
            'closed category is strict — so AX-G2 names a recognised structural property, not a ZP-specific '
            'stipulation. Together with AX-G1 (no terminal object) it places C at a <i>non-trivial</i> strict '
            'initial object: a strict initial that is also terminal (a zero object) forces every object to be '
            'isomorphic to it, so AX-G1 rules that degenerate case out — but not conversely, since a non-trivial '
            'category can have a strict initial object and still have a terminal one (in the category of sets, '
            'the empty set is strict initial and the one-point set is terminal). '
            'The initial object of C is not identified with &#8869; of ZP-A\'s lattice, nor with any other '
            'domain\'s bottom: they live in different structures, and an equation across them is ill-typed '
            '(MC-1, the bottom family; ZP-H T-H3 makes no identification). What links them is a standard fact '
            'and a check, not an identity. The fact: a least element of a preorder is initial in its order '
            'category (Mathlib Preorder.isInitialBot). The check is in ZP-H: three Lean functors '
            '(fb_functor, fc_functor, fd_functor) send the natural-number depth order into an &#8469;-indexed '
            'stand-in category for their domain and send 0 to an initial object there; F<sub>A</sub> has no '
            'functor term, and its witness is 0 initial in &#8469;\'s order category (natSLat_initial_grounding). '
            'The axioms are not postulated in isolation; they are shown to hold in '
            'each of four ℕ-indexed depth categories, one per domain (ZP-H), and are not claimed for the three '
            'Mathlib categories ZP-H also targets (TopCat, KleisliCat PMF, ModuleCat ℂ) — each of which has a '
            'terminal object, so AX-G1 fails in every one of them. ModuleCat ℂ\'s zero module fD_functor.obj 0 is a zero object that '
            'every object maps into, so it is initial but not strict. The domain facts behind the stand-ins '
            '(ZP-A T2, ZP-B C3, ZP-C T1b, ZP-D T4) are proved separately in their own layers; the categorical check is '
            'the same ℕ-order instance each time.',
        ]
    ))

    print('[build_zpg] Building Section III: Universal Constituent and Unreachability...')
    # ── III. UNIVERSAL CONSTITUENT AND UNREACHABILITY ─────────────────────────
    E.append(Paragraph('III. Universal Constituent and Unreachability', S['h1']))

    E.append(result_box(
        'Lemma T2 — Universal Constituent',
        'Status: Derived — from D3 and AX-G1',
        [
            'For every X ∈ ob(C), ∃! &#953;<sub>X</sub>: 0 → X. '
            'The initial object 0 is the universal categorical source.',
            'Proof: Immediate from D3 and AX-G1. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Lemma T3 — Unreachability of 0',
        'Status: Derived — from AX-G2',
        [
            'For any X not isomorphic to 0: hom(X, 0) = ∅. The initial object 0 is unreachable from any non-initial object.',
            'Proof: Direct from AX-G2. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark R1 — Structural Inversion — The Categorical Zero Paradox',
        'Status: Remark',
        [
            'T2 and T3 together constitute the categorical Zero Paradox. 0 reaches every object in exactly one way (T2); '
            'no non-initial object reaches 0 (T3). This is not a logical contradiction. It is a structural '
            'inversion: the unique universal source is the unique object with no incoming non-trivial morphisms.',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark R2 — Categorical Expression of Self-Containment',
        'Status: Remark — connecting note to ZP-A CC-2',
        [
            'R1 frames the structural inversion of 0. This remark connects that structure to ZP-A CC-2, the Quine atom: '
            'a role, a point that steps to itself and to nothing else (Motion.SelfOnlyAt, ZeroParadox/Die.lean). Where a set '
            'steps to its members, a set occupies it exactly when x = {x} (zfset_selfOnlyAt_mem_iff); in a ZP-A lattice under a '
            'self-application map supplied by AbstractSelfApp, ⊥ of L is its only occupant (selfApp_quine_role_iff). An occupant has '
            'no external interpreter by structure; it IS its own interpretation.',
            'In categorical terms, this corresponds to two conditions together: (1) AX-G2: '
            'hom(X, 0) = ∅ for all X not isomorphic to 0 — no morphism can reach inside 0 from outside; and '
            '(2) T2: ∃! &#953;<sub>X</sub>: 0 → X for all X — 0 is structurally present in every object. '
            'Together these are the categorical image of undifferentiated self-containment: unreachable '
            'from without, yet constitutive of everything.',
            '0 "points in all directions" (T2) because it is the undifferentiated ground from which all '
            'differentiation proceeds — not because it selects a direction. The uniqueness of each '
            '&#953;<sub>X</sub> is not a choice among alternatives; it is the absence of internal '
            'structure that would allow differentiation among morphisms.',
            'This remark bridges ZP-G to ZP-A CC-2. The formal correspondence between the categorical '
            'initial object structure and the Quine-atom role (ZP-A CC-2) is made explicit in ZP-H.',
        ]
    ))

    print('[build_zpg] Building Section IV: Monotone Structure...')
    # ── IV. MONOTONE STRUCTURE AND THE ADDITIVE ONTOLOGY ─────────────────────
    E.append(Paragraph('IV. Monotone Structure and the Additive Ontology', S['h1']))

    E.append(def_box(
        'Definition D5 — Morphism Chain',
        'Status: Definition',
        [
            'A morphism chain of length n from 0 is a sequence:',
            '0 = X<sub>0</sub> → X<sub>1</sub> → ... → X<sub>n</sub>',
            'where each X<sub>k</sub> → X<sub>k+1</sub> is a morphism in C.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Proposition T4 — Chains are Forward-Only',
        'Status: Derived — from AX-G2',
        [
            'No morphism chain from 0 can return to 0 through non-initial objects.',
            'Proof: A return morphism X<sub>n</sub> → 0 for X<sub>n</sub> not isomorphic to 0 would contradict AX-G2. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'Definition D6 — Functor',
        'Status: Definition — standard category theory',
        [
            'A functor F: C → D consists of an object map F: ob(C) → ob(D) and a morphism map '
            'F: hom<sub>C</sub>(A,B) → hom<sub>D</sub>(F(A), F(B)), preserving composition and identity.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Proposition T5 — Functors Preserve Initial Objects',
        'Status: Derived — [OQ-G2 closed in ZP-H T-H1]',
        [
            'For each instantiation functor F ∈ {F<sub>A</sub>, F<sub>B</sub>, F<sub>C</sub>, F<sub>D</sub>}, '
            'F(0) is an initial object in the codomain (for F<sub>B</sub>, in its stand-in). '
            'Verified by direct universal property check in ZP-H T-H1. ✓',
        ]
    ))

    print('[build_zpg] Building Section V: Kolmogorov Import...')
    # ── V. THE KOLMOGOROV IMPORT FROM ZP-C ───────────────────────────────────
    E.append(Paragraph('V. The Kolmogorov Import from ZP-C', S['h1']))
    E.append(body('This section contains the single import from outside category theory that ZP-G '
                  'requires. It is named, scoped, and labelled explicitly. It replaces BA-G1 (the Leinster '
                  'Bridge Axiom) as the informational foundation of D7\'.'))

    E.append(import_box(
        'Import I-KC — Conditional Kolmogorov Complexity from ZP-C',
        'Status: Import — from ZP-C D1 and standard algorithmic information theory',
        [
            'What is imported: The conditional Kolmogorov complexity K(x|y), defined as the length of the '
            'shortest program p such that U(p, y) = x, where U is a fixed universal Turing machine:',
            'K(x|y) = min { |p| : U(p, y) = x }',
            'Key property — the coding theorem: prefix complexity equals &#8722;log<sub>2</sub> m(x) + O(1), for the '
            'a priori probability m (the maximal lower semicomputable semimeasure, which is not computable). The '
            'plain complexity K defined above is at most prefix complexity + O(1). So for a computable '
            'probability measure P, one direction holds for K, with a constant c<sub>P</sub> that depends on P:',
            'K(x) &#8804; &#8722;log<sub>2</sub> P(x) + c<sub>P</sub>',
            'Source: Shen, Uspensky and Vereshchagin, Kolmogorov Complexity and Algorithmic Randomness (AMS, 2017), '
            '§ 4.2, p. 79 (maximality: m\'(i) &#8804; c&#183;m(i) for every lower semicomputable semimeasure m\'), '
            'and § 4.5, Theorems 55, 56 and 58, pp. 91–93 (prefix complexity and &#8722;log m coincide up to an '
            'additive constant). Plain complexity is at most prefix complexity + O(1) unconditionally at § 4.6, p. 100; '
            'the conditional forms, with m(x|y), are § 4.7, p. 103, whose remark obtains the conditional inequalities '
            'by relativizing the unconditional proofs, and the plain-versus-prefix bound is applied here in that '
            'relativized form. The converse inequality fails for '
            'computable P: with P uniform on n-bit strings given n, &#8722;log<sub>2</sub> P(0<sup>n</sup>|n) = n '
            'while K(0<sup>n</sup>|n) is bounded. The coding theorem is not derived within ZP-G. '
            'It is imported as a named result.',
            'Scope of import: I-KC imports K(x|y) and the coding theorem only. No other content from ZP-C is '
            'imported into ZP-G. The Kolmogorov complexity machinery is already present in ZP-C D1 '
            '(incompressibility threshold P<sub>0</sub>), so I-KC introduces no new external dependency into the overall '
            'Zero Paradox framework — it only introduces a dependency within ZP-G specifically.',
            'Computability note: K(x|y) is not computable in general (it is approximable from above by standard '
            'results). This is not a defect for the present purposes: the framework requires that K(x|y) be '
            'well-defined, not that it be computable. The ontological claims of ZP-G do not depend on computability.',
            'Status: This is an import, not a bridge axiom. A bridge axiom is a claim derivable '
            'from neither side, and so one that must be assumed. K(x|y) is a defined mathematical object with a complete '
            'internal theory. I-KC is a decision to use that object within ZP-G, not an assumption about it.',
        ]
    ))

    print('[build_zpg] Building Section VI: Categorical Information Theory...')
    # ── VI. CATEGORICAL INFORMATION THEORY [REBUILT IN v1.1] ─────────────────
    E.append(Paragraph('VI. Categorical Information Theory', S['h1']))
    E.append(Paragraph('6.1 Native Categorical Surprisal — Definition D7\'', S['h2']))
    E.append(body('Categorical surprisal is defined via conditional Kolmogorov complexity, imported '
                  'via I-KC (Definition D7\'), rather than the Shannon entropy functor H of BA-G1. '
                  'The definition is native to the morphism structure of C.'))

    E.append(def_box(
        'Definition D7\' — Native Categorical Surprisal',
        'Status: Definition — from D5, I-KC [replaces D7]',
        [
            'Let f: A → B be a morphism in C. Represent A and B as binary strings x<sub>A</sub> and x<sub>B</sub> '
            'via any injective encoding consistent with the morphism structure of C. The categorical surprisal of f is:',
            'I(f) = K(x<sub>B</sub> | x<sub>A</sub>)',
            'the conditional Kolmogorov complexity of the target given the source.',
            'Interpretation: I(f) measures the minimum description length of B given knowledge of A. It is the '
            'irreducible informational content added by the transition f: A → B, independent of any probability distribution.',
            'Well-definedness: K(x<sub>B</sub>|x<sub>A</sub>) depends on the encoding of objects as strings. Two computable '
            'encodings, each computable from the other, yield values differing by at most an additive constant c that '
            'depends on the pair of encodings, not on A or B (translate the strings before running the program). '
            'All claims in ZP-G are stated in terms of whether I(f) is finite, zero, or undefined — qualitative '
            'properties that are invariant under any additive constant. This invariance is a consequence of what '
            'ZP-G chooses to claim, not a general property of K-complexity (additive constants can matter '
            'for precise K-complexity comparisons in AIT).',
            'Relationship to D7: by the coding theorem (I-KC), K(x<sub>B</sub>|x<sub>A</sub>) &#8804; &#8722;log<sub>2</sub> P(x<sub>B</sub>|x<sub>A</sub>) + c<sub>P</sub> '
            'for a conditional measure P computable from both arguments, so D7\' is bounded above by D7 up to a constant that depends on P. '
            'The reverse bound fails for computable P in general (the example in I-KC), so D7\' and D7 are not equivalent; the '
            'two-sided relation holds for the conditional a priori probability m, which is not computable. The choice of D7\' over D7 changes what is measured.',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('6.2 Properties of the Native Surprisal', S['h2']))

    E.append(result_box(
        'Lemma T6-a — Surprisal of the Identity Morphism is Zero',
        'Status: Derived — from D7\' and I-KC',
        [
            'Claim: I(id<sub>A</sub>) = K(x<sub>A</sub>|x<sub>A</sub>) = 0 up to the additive constant c.',
            'Proof: The shortest program producing x<sub>A</sub> given x<sub>A</sub> is the empty program (output the input). '
            'Therefore K(x<sub>A</sub>|x<sub>A</sub>) = 0 up to c. The identity morphism adds no informational content. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Lemma T6-b — Surprisal is Non-Negative for Forward Morphisms',
        'Status: Derived — PDF-level (from D5, D7\', AX-G2); NOT Lean-verified — see Lean scope remark below',
        [
            'Claim: For any morphism f: A → B in a forward morphism chain from 0, I(f) ≥ 0 up to c, '
            'with strict inequality when A ≠ B.',
            'Proof: K(x<sub>B</sub>|x<sub>A</sub>) ≥ 0 by definition (program length is non-negative). Strict inequality holds '
            'when x<sub>B</sub> cannot be computed from x<sub>A</sub> by the empty program — i.e., when A and B are distinct objects '
            'encoding distinct states. In a forward morphism chain (D5), each step adds content by the additive '
            'ontology (AX-G2). ✓',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Proposition T6-c — Surprisal Accumulates Along Chains',
        'Status: Derived — PDF-level (from D5, T6-b, subadditivity of K); NOT Lean-verified — see Lean scope remark below',
        [
            'Claim: For a morphism chain 0 = X<sub>0</sub> → X<sub>1</sub> → ... → X<sub>n</sub>, the total surprisal '
            '&#8721; I(X<sub>k</sub> → X<sub>k+1</sub>) ≥ 0, with monotone accumulation as n increases.',
            'Proof: By subadditivity of Kolmogorov complexity: K(x<sub>n</sub>|x<sub>0</sub>) ≤ '
            '&#8721; K(x<sub>k+1</sub>|x<sub>k</sub>) + O(n&#183;c). Each term is ≥ 0 by T6-b. '
            'Adding distinct objects strictly increases the total. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark — Lean Scope of T6-b and T6-c',
        'Status: Scope note — T6-b and T6-c are NOT Lean-verified for their mathematical claims',
        [
            '<b>T6-b and T6-c are not Lean-verified.</b> The Category.lean proofs for these results compile '
            'without error, but they verify nothing about Kolmogorov complexity. The ZPSurprisal typeclass '
            'defines surp : hom &#8594; &#8469; (surprisal as a natural number) and the proofs reduce to '
            'Nat.zero_le _, which states that any natural number is &#8805; 0. This is trivially true by '
            'type for <i>any</i> &#8469;-valued function, regardless of its mathematical content. '
            'A compiling Lean proof here does not mean the K-theoretic claims have been verified.',
            'What the Lean proofs do NOT establish: (1) T6-b strict inequality — '
            'K(x<sub>B</sub>|x<sub>A</sub>) &gt; 0 when A &#8775; B (distinct objects cannot have zero description length). '
            '(2) T6-c subadditivity — K(x<sub>n</sub>|x<sub>0</sub>) &#8804; '
            '&#8721; K(x<sub>k+1</sub>|x<sub>k</sub>) + O(n&#183;c) (total surprisal along a chain). '
            'Plain and prefix complexity are in the build (plainK and KPPlain from kolmogorov-complexity-lean, '
            'via ZeroParadox/Information/BrudnoBridge.lean); T6-b and T6-c are not proved from them, and '
            'ZPSurprisal is not tied to them (scope note, § IV of ZeroParadox/Category/Category.lean).',
            'T6-a is assumed in Lean, not verified: zero identity surprisal is the class field surp_id of '
            'ZPSurprisal, which t6a_identity_surprisal returns unchanged, and surp := fun _ => 0 satisfies the class. '
            'What IS Lean-verified: T6 Part II (inward surprisal is undefined — from AX-G2 and the absence of morphisms to 0), '
            'and T7 insofar as it depends on Parts II, III, V, VI. T6 Part I (outward accumulation) '
            'and T7 Part IV rely on T6-b and T6-c and are therefore also PDF-level only.',
            'Readers citing "the Lean-verified ZP-G framework" should note this boundary. '
            'The PDF-level arguments for T6-b and T6-c are standard K-theoretic arguments. '
            'The gap is Lean scope, not mathematical correctness.',
        ]
    ))

    print('[build_zpg] Building Section VII: Informational Singularity...')
    # ── VII. THE INFORMATIONAL SINGULARITY OF 0 ─────────────────────────────
    E.append(Paragraph('VII. The Informational Singularity of 0', S['h1']))
    E.append(body('This is the central theorem of the information-theoretic section. It is proved from D7\' and AX-G2 alone, with I-KC as the only external dependency.'))

    E.append(result_box(
        'Theorem T6 — Informational Singularity of 0',
        'Status: Derived — from AX-G2, D7\', I-KC [OQ-G1 closed]',
        [
            'Setup: Let 0 be the initial object of C (AX-G1). Let I(f) = K(x<sub>B</sub>|x<sub>A</sub>) be the categorical '
            'surprisal (D7\'). Let I-KC provide the Kolmogorov framework.',
            'Part I — Outward surprisal accumulates (from T6-b, T6-c): For any morphism chain '
            '0 = X<sub>0</sub> → ... → X<sub>n</sub>, &#8721; I(X<sub>k</sub> → X<sub>k+1</sub>) ≥ 0, '
            'with strict accumulation as n increases. ✓',
            'Part II — Inward surprisal is undefined (from AX-G2): For any X not isomorphic to 0, hom(X, 0) = ∅ (AX-G2). '
            'Therefore D7\' cannot be applied to any morphism f: X → 0 from outside 0 — no such morphism '
            'exists. I(X → 0) is undefined not because K diverges to infinity, but because there is no morphism '
            'to apply D7\' to. ✓',
            'Part III — The singularity: 0 is the unique object in C for which outward surprisal is defined and '
            'accumulates (Part I) while inward surprisal is undefined by absence of morphisms (Part II). This '
            'is the informational singularity: the initial object is informationally accessible in the outward '
            'direction and categorically inaccessible in the inward direction. The singularity is structural, not '
            'numerical. It does not require K to diverge — it requires only AX-G2 and D7\'. ✓',
            'Comparison with ZP-C (to be reconciled in ZP-H T-H2): ZP-C establishes that the discrete surprisal '
            'DF diverges (numerically, to &#8734;) along infinite sequences approaching 0 in Q<sub>2</sub>. T6 Part II '
            'establishes that I(X → 0) is undefined (domain-absent) for any X not isomorphic to 0 in C. These are compatible: '
            'ZP-H T-H2 shows that the two hold together. Its proof pairs Lemma T3 (hom(X, 0) = ∅, the fact '
            'Part II rests on) with ZP-C Theorem T2, and uses neither to prove the other '
            '(th2_singularity_compatibility).',
            'Status: DERIVED. Depends on AX-G1, AX-G2, D3, D5, D7\', I-KC, T6-a, T6-b, T6-c. OQ-G1 is closed. '
            'BA-G1 is no longer a premise of T6. ✓',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('7.1 D7\' and Shannon Entropy — BA-G1 Demoted to Remark', S['h2']))

    E.append(remark_box(
        'Remark R-BA — D7\' and the Shannon Entropy Functor: a One-Sided Bound',
        'Status: Remark — BA-G1 demoted from Bridge Axiom to Remark',
        [
            'BA-G1 was originally introduced as a bridge axiom: it imported Leinster\'s categorical '
            'characterization of Shannon entropy (naturality, maximality, chain rule) to define the surprisal '
            'functor. BA-G1 was originally the only bridge axiom in ZP-G and the source of OQ-G1.',
            'BA-G1 is no longer a premise of any theorem, and it is not derived from D7\': the two are different '
            'quantities. The coding theorem (I-KC) gives one direction only, K(x<sub>B</sub>|x<sub>A</sub>) &#8804; '
            '&#8722;log<sub>2</sub> P(x<sub>B</sub>|x<sub>A</sub>) + c<sub>P</sub> for a computable conditional measure P, '
            'a bound on the surprisal of one outcome under P. No equation between D7\' and the Shannon functor of BA-G1 '
            'follows from it, so results derived from BA-G1 do not carry over to D7\' by this route, and BA-G1 is not an '
            'equivalent formulation of D7\'. It is retained as a remark on a related quantity. T6 and T7 do not use '
            'it: their dependency lists, above and below, do not include BA-G1.',
        ]
    ))

    print('[build_zpg] Building Section VIII: Categorical Zero Paradox...')
    # ── VIII. THE CATEGORICAL ZERO PARADOX — FORMAL STATEMENT ─────────────────
    E.append(Paragraph('VIII. The Categorical Zero Paradox — Formal Statement', S['h1']))
    E.append(body('Theorem T7 is the closing theorem of ZP-G. Part IV (informational singularity) rests on T6, which does not depend on BA-G1.'))

    E.append(result_box(
        'Theorem T7 — The Categorical Zero Paradox',
        'Status: Derived — Closing Theorem',
        [
            'Setup: Let C satisfy AX-G1 and AX-G2. Let I be the categorical surprisal from D7\'. '
            'Let I-KC provide the Kolmogorov framework.',
            'Part I — Universal Constituent (T2): &#8704;X ∈ ob(C), ∃! &#953;<sub>X</sub>: 0 → X. '
            'The initial object 0 is the universal categorical source.',
            'Part II — Unreachability (T3): for every X not isomorphic to 0, hom(X, 0) = ∅. No non-initial object reaches 0.',
            'Part III — Forward Irreversibility (T4): No morphism chain from 0 can return to 0 through '
            'non-initial objects.',
            'Part IV — Informational Singularity (T6, rebuilt): I(X → 0) is undefined for all X not isomorphic to 0 '
            '(no such morphism exists, AX-G2). Outward surprisal from 0 accumulates along any morphism '
            'chain (T6-b, T6-c). 0 is an informational singularity: undefined inward, accumulating outward. '
            'This part no longer depends on BA-G1.',
            'Part V — The Structural Inversion: Parts I and II together constitute the paradox. 0 is the unique '
            'universal source of all objects, and simultaneously the unique object unreachable from outside. '
            'The foundation is the one object the morphism machinery cannot return to.',
            'Part VI — Resolution: The paradox is not a logical contradiction. It is a structural inversion. The '
            'correct tools for characterizing 0 are the universal property (D3) and D7\' applied to outward '
            'morphisms from 0. Under these tools, 0 is fully characterized. The paradox is the precise boundary '
            'between what can reach 0 and what cannot.',
            'Status: DERIVED — Closing Theorem. Depends on D3, D5, D7\', AX-G1, AX-G2, I-KC, T2, T3, T4, '
            'T6. BA-G1 is not a dependency. ✓',
        ]
    ))

    print('[build_zpg] Building Section IX: Open Items Register...')
    # ── IX. OPEN ITEMS REGISTER FOR ZP-G v1.2 ────────────────────────────────
    E.append(Paragraph('IX. Open Items Register', S['h1']))

    oq_rows = [
        ['OQ-G1',
         'Closed — D7\', T6',
         'Native categorical derivation of surprisal without importing Shannon entropy. Closed by replacing D7 '
         'with D7\' (conditional Kolmogorov complexity K(B|A)). BA-G1 demoted from Bridge Axiom to '
         'Remark R-BA. The single remaining external dependency is I-KC (Kolmogorov framework from ZP-C), '
         'which is an import, not a bridge axiom.'],
        ['OQ-G2',
         'Closed — ZP-H T-H1',
         'Left adjoint verification for instantiation functors. Resolved in ZP-H v1.0 by direct universal '
         'property verification for each functor.'],
        ['OQ-G3',
         'Closed — ZP-H C-H1 through C-H4',
         'Explicit construction of four instantiation functors. Resolved in ZP-H v1.0.'],
        ['OQ-G4',
         'Closed — ZP-H T-H2',
         'Reconciliation of categorical and ZP-C singularity characterizations. Resolved in ZP-H v1.0. '
         'Undefined domain (ZP-G) and infinite accumulation (ZP-C) shown to hold together: the proof '
         'pairs ZP-G Lemma T3 with ZP-C Theorem T2 and uses neither to prove the other.'],
        ['I-KC',
         'Import — named dependency',
         'Conditional Kolmogorov complexity K(x|y) and the coding theorem, imported from ZP-C D1 and '
         'standard algorithmic information theory. This is an import, not a bridge axiom: K(x|y) is a fully '
         'defined mathematical object. ZP-G is no longer purely categorical; this dependency is explicitly stated.'],
        ['AX-G1',
         'Axiom — intentional',
         'Asymmetry: initial object 0, no terminal object. Foundational structural commitment. Not a gap.'],
        ['AX-G2',
         'Axiom — intentional',
         'Source asymmetry: hom(X, 0) = ∅ for X not isomorphic to 0. Foundational irreversibility commitment. Not a gap.'],
        ['R-BA',
         'Remark — BA-G1 demoted',
         'Leinster Shannon entropy characterization is now a remark, not a bridge axiom premise. '
         'Not derivable from D7\': the coding theorem gives a one-sided bound, not an equivalence. Not a gap.'],
    ]
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.10, TW*0.18, TW*0.72]
    ))

    print('[build_zpg] Building Section X: Validation Status...')
    # ── X. VALIDATION STATUS ──────────────────────────────────────────────────
    E.append(Paragraph('X. Validation Status', S['h1']))

    val_rows = [
        ['D1: Category',
         'Valid — Definition. Standard; foundational. Unchanged.'],
        ['D2: Uniqueness notation',
         'Valid — Definition. Unchanged.'],
        ['D3: Initial object',
         'Valid — Definition. Load-bearing for T2, T7. Unchanged.'],
        ['D4: Terminal object',
         'Valid — Definition. Defined for exclusion. AX-G1 prohibits it. Unchanged.'],
        ['D5: Morphism chain',
         'Valid — Definition. Native to C. Unchanged.'],
        ['D6: Functor',
         'Valid — Definition. Standard. Unchanged.'],
        ['D7\': Native categorical surprisal',
         'Valid — Definition. K(x<sub>B</sub>|x<sub>A</sub>) via I-KC. Replaces D7. '
         'Well-defined up to additive constant c. Structurally invariant.'],
        ['I-KC: Kolmogorov import',
         'Import — named. K(x|y) and coding theorem from ZP-C. '
         'Not a bridge axiom. Introduces explicit ZP-C dependency into ZP-G.'],
        ['AX-G1: Asymmetry Axiom',
         'Axiom — intentional. Unchanged.'],
        ['AX-G2: Source Asymmetry',
         'Axiom — intentional. Unchanged.'],
        ['R-BA: BA-G1 remark (one-sided bound)',
         'Remark — [BA-G1 demoted from Bridge Axiom]. Shannon entropy functor '
         'related to D7\', not equivalent: the coding theorem bounds D7\' above only. No longer a premise of any theorem.'],
        ['Proposition T1: Uniqueness of initial object',
         'Valid — Derived. Relabelled Proposition (subsidiary uniqueness result). Unchanged. ✓'],
        ['Lemma T2: Universal constituent',
         'Valid — Derived. Relabelled Lemma (stepping-stone result). Unchanged. ✓'],
        ['Lemma T3: Unreachability of 0',
         'Valid — Derived. Relabelled Lemma (stepping-stone result). Unchanged. ✓'],
        ['R1: Structural inversion',
         'Valid — Remark. Unchanged.'],
        ['R2: Categorical expression of self-containment',
         'Valid — Remark. Connects T2 + AX-G2 to ZP-A CC-2 (the Quine atom, a role). '
         'No new derivation; explanatory bridge note.'],
        ['Proposition T4: Chains are forward-only',
         'Valid — Derived. Relabelled Proposition. Unchanged. ✓'],
        ['Proposition T5: Functors preserve initial objects',
         'Valid — Conditional on ZP-H T-H1 (closed). Relabelled Proposition. Unchanged. ✓'],
        ['Lemma T6-a: Identity surprisal is zero',
         'Valid (PDF-level) — Derived. Relabelled Lemma. K(x<sub>A</sub>|x<sub>A</sub>) = 0 up to c. In Lean it is the '
         'class field surp_id, assumed, not verified. ✓'],
        ['Lemma T6-b: Non-negative outward surprisal',
         'Valid (PDF-level) — Derived from D5, D7\', AX-G2. K &#8805; 0; strict inequality for distinct objects. '
         'NOT Lean-verified: Lean proof reduces to Nat.zero_le _ (trivially true for any &#8469;-valued function; '
         'verifies nothing about K).'],
        ['Proposition T6-c: Surprisal accumulates along chains',
         'Valid (PDF-level) — Derived from D5, T6-b, subadditivity of K. '
         'NOT Lean-verified: Lean proof reduces to Nat.zero_le _. '
         'Subadditivity of K is a standard AIT result but requires a formalization of K, none located '
         'in the pinned Mathlib as of 2026-10-04 (the search is recorded in '
         'ZeroParadox/Information/Disjunctive.md).'],
        ['Theorem T6: Informational singularity',
         'Valid — Derived. Does not depend on BA-G1. '
         'Part II: undefined domain (AX-G2) — fully Lean-verified. '
         'Parts I, III: accumulation via T6-b, T6-c — PDF-level only (T6-b/T6-c not Lean-verified).'],
        ['Theorem T7: Categorical Zero Paradox',
         'Valid — Derived. All six parts derived. BA-G1 not a dependency. ✓'],
        ['OQ-G1: Native surprisal derivation',
         'Closed — D7\', T6. No bridge axiom remains as a theorem premise.'],
    ]
    E.append(data_table(
        ['Component', 'Status / Notes'],
        val_rows,
        [TW*0.38, TW*0.62]
    ))

    E += [
        sp(12),
        Paragraph(
            '<i>Zero Paradox ZP-G: Category Theory | '
            'T6-b and T6-c: PDF-level only; Lean proofs verify non-negativity by type only (Nat.zero_le _), '
            'not K-theoretic content | T6 Part II: Lean-verified</i>',
            S['endnote']),
    ]

    print(f'[build_zpg] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zpg] Written: {out_path}')


if __name__ == '__main__':
    build()
