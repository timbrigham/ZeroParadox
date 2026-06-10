"""
Zero Paradox — ZP-H Addendum: The Snap Floor in Native Categories
Version 1.0 | June 2026
v1.0: Initial release. Realizes the snap floor ⊥ inside each framework's own
      Mathlib category as a genuine CategoryTheory.Functor, replacing the ℕ-indexed
      depth-proxy categories of the main ZP-H document:
        F_B  fB_functor : ℕᵒᵖ ⥤ TopCat        — ⊥ = inverse limit ⋂ B(0,2⁻ⁿ) = {0}
        F_D  fD_functor : ℕ ⥤ ModuleCat ℂ      — ⊥ = StateSpace 0, the initial zero object
        F_C  fC_functor : ℕ ⥤ KleisliCat PMF    — ⊥ = Fin 0 initial; fC_no_return = AX-G2 as theorem
      Bundled witness: mc1_correspondence (ZPH_MC1.lean). Settles MC-1's correspondence
      half (each bottom is its category's categorical bottom, agreeing on the snap); the
      identity half (the four are numerically one object) remains a modeling commitment.
      Lean sources: ZPH_TopFunctor.lean, ZPH_HilbFunctor.lean, ZPH_InfoFunctor.lean, ZPH_MC1.lean.
      Axiom footprint: [propext, Classical.choice, Quot.sound] — Classical.choice inherited
      from Mathlib's topology / inner-product / PMF libraries (a library inheritance, not a
      new commitment).
Reads after ZP-H Categorical Bridge.
"""

import os
from zp_utils import *

VERSION = '1.0'

# ── fix() guard: route all bare Paragraph() text through Unicode-to-entity conversion ──
_Paragraph_orig = Paragraph
def Paragraph(text, style):
    return _Paragraph_orig(fix(text) if isinstance(text, str) else text, style)


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-H_Native_Categories_Addendum.pdf')
    print(f'[build_zph_native_addendum] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-H Native Categories Addendum',
                   'ZP-H Native Categories Addendum', 'Version ' + VERSION,
                   date_str='June 2026')
    E = []

    # ── Header banner ───────────────────────────────────────────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('ZP-H Addendum',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    print('[build_zph_native_addendum] Building title block...')
    E += [
        sp(4),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-H Addendum', S['title']),
        Paragraph('The Snap Floor in Native Categories', S['subtitle']),
        Paragraph('Version ' + VERSION + ' | June 2026', S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    # ── Preamble ────────────────────────────────────────────────────────────────
    print('[build_zph_native_addendum] Building preamble...')
    E.append(body(
        'ZP-H derives the Binary Snap across four mathematical frameworks and locates the '
        'snap floor &#8869; as the categorical bottom in each. In the main document that '
        'location is carried by three depth-index proxy categories &#8212; copies of &#8469; '
        'with the order &#8804; (Q<sub>2</sub>BallDepth, InfoDepth, HilbDimDepth), engineered '
        'so that depth 0 is the initial object. This addendum does the stronger thing: it '
        'drops the snap floor into each framework\'s own category, taken directly from '
        'Mathlib, where the floor appears in that field\'s native syntax. A topologist, a '
        'functional analyst, and a probabilist each meet the same bottom, each in their own '
        'category and their own language.'))
    E.append(body(
        'Three genuine Lean functors realize the snap chain inside the standard categories: '
        'F_B into TopCat (topological spaces), F_D into ModuleCat &#8450; (&#8450;-modules), '
        'and F_C into the Kleisli category of the probability monad PMF (stochastic maps). '
        'Each is sorry-free, and each carries the snap floor to its category\'s categorical '
        'bottom &#8212; an inverse limit in TopCat, an initial object in ModuleCat &#8450; '
        'and in the Kleisli category. The bundled witness is mc1_correspondence '
        '(ZPH_MC1.lean).'))
    E.append(body(
        'Two honesty boundaries hold throughout. <b>The realized claim is correspondence, '
        'not identity.</b> What is proved is that each bottom is its own category\'s '
        'categorical bottom, agreeing on the snap; that the four bottoms are <i>numerically '
        'one object</i> remains a modeling commitment, not a theorem. <b>The native '
        'categories are the honest target.</b> Mathlib has no bespoke category of p-adic '
        'spaces, Hilbert spaces, or information spaces, so the general-purpose categories '
        '&#8212; topological spaces, &#8450;-modules, stochastic maps &#8212; are where the '
        'floor genuinely lives.'))
    E.append(hr())

    # ── Section I ─────────────────────────────────────────────────────────────────
    print('[build_zph_native_addendum] Building Section I...')
    E += [
        Paragraph('Section I: From Depth Proxies to Native Categories', S['h1']),
        hr(),
    ]
    E.append(body(
        'The proxy categories of the main document are correct but indirect. '
        'Q<sub>2</sub>BallDepth, InfoDepth, and HilbDimDepth are each a copy of &#8469; with '
        'the order &#8804;, wrapped so that the bottom 0 satisfies the universal property of '
        'an initial object and the source-asymmetry condition AX-G2 (no morphism returns to '
        '0). They witness the snap floor\'s categorical role, but inside a structure built '
        'for the purpose rather than inside the domain itself.'))
    E.append(body(
        'The native categories are not built for the purpose, and that is the point '
        '&#8212; they also do not satisfy the ZP categorical axioms. A ZPCategory (ZP-G) '
        'requires that no terminal object exist (AX-G1): the snap has nowhere higher to go. '
        'TopCat and ModuleCat &#8450; both <i>have</i> a terminal object (the one-point '
        'space; the zero module). So the snap floor cannot be "the initial object of a '
        'ZPCategory" here. The honest statement is the one each category supports natively: '
        'in TopCat the floor is the limit of the shrinking system, and in ModuleCat &#8450; '
        'and the Kleisli category it is the genuine initial object. Each is stated below.'))
    E.append(sp(6))

    # ── Section II: F_B / TopCat ──────────────────────────────────────────────────
    print('[build_zph_native_addendum] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: F_B — The Snap Floor in TopCat', S['h1']),
        hr(),
    ]
    E.append(body(
        'The 2-adic snap floor is 0 &#8712; Q<sub>2</sub>. Around it sits the descending '
        'tower of clopen balls B(0, 2<sup>&#8722;n</sup>) &#8212; the unit ball, then radius '
        '1/2, then 1/4, and so on &#8212; each a genuine topological subspace of '
        'Q<sub>2</sub>. The inclusions B(0, 2<sup>&#8722;m</sup>) &#8838; B(0, '
        '2<sup>&#8722;n</sup>) for n &#8804; m are continuous, so the tower is a functor out '
        'of &#8469;<sup>op</sup> (the balls shrink as the index grows): a real diagram in '
        'TopCat.'))
    E.append(result_box(
        'Functor: fB_functor : ℕ^op → TopCat (ZPH_TopFunctor.lean)',
        [
            'Object  n &#8614; the clopen ball B(0, 2<sup>&#8722;n</sup>) &#8838; '
            'Q<sub>2</sub>, as a TopCat object.',
            'Morphism (n &#8804; m): the continuous inclusion of the smaller ball into the '
            'larger.',
            '',
            'fB_bottom_is_limit:   &#8745;<sub>n</sub> B(0, 2<sup>&#8722;n</sup>) = {0}',
            'The snap floor is the inverse limit of the tower &#8212; the one point common '
            'to every ball.',
            'Sorry-free. Purity [propext, Classical.choice, Quot.sound].',
        ]
    ))
    E.append(sp(4))
    E.append(body(
        'TopCat has both a terminal object (the one-point space) and an initial object (the '
        'empty space); the snap floor is neither. It is the <i>limit</i> of the ball tower '
        '&#8212; the categorical expression a topologist would expect for "the point '
        'everything converges to." This is the honest realization in a category that is not '
        'a ZPCategory: not an initial object, but a limit.'))
    E.append(sp(6))

    # ── Section III: F_D / ModuleCat ℂ ────────────────────────────────────────────
    print('[build_zph_native_addendum] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: F_D — The Snap Floor in ModuleCat ℂ', S['h1']),
        hr(),
    ]
    E.append(body(
        'The state layer represents the snap in a complex Hilbert space: StateSpace n is the '
        'n-dimensional space &#8450;<sup>n</sup>, with the snap an orthogonal shift between '
        'basis states (ZP-D). As &#8450;-modules, these spaces and the linear maps between '
        'them form a diagram in ModuleCat &#8450;.'))
    E.append(result_box(
        'Functor: fD_functor : ℕ → ModuleCat ℂ (ZPH_HilbFunctor.lean)',
        [
            'Object  n &#8614; StateSpace n = the &#8450;-module &#8450;<sup>n</sup>.',
            'Morphism (n &#8804; m): the isometric &#8450;-linear embedding that pads the '
            'extra coordinates with zero.',
            '',
            'fD_zero_isInitial:   StateSpace 0 is the initial object of ModuleCat &#8450;.',
            'The snap floor is the zero module &#8212; the one-element &#8450;-module {0}, '
            'which is the categorical zero object (both initial and terminal).',
            'fD_embed_inner:   the embeddings preserve the inner product (genuine '
            'isometries).',
            'Sorry-free. Purity [propext, Classical.choice, Quot.sound].',
        ]
    ))
    E.append(sp(4))
    E.append(body(
        'Here, unlike TopCat, the floor is the initial object outright: the zero object of '
        'ModuleCat &#8450; is StateSpace 0. The isometry lemma records what ModuleCat '
        '&#8450; forgets &#8212; that the embeddings are not merely linear but '
        'inner-product preserving &#8212; so the Hilbert-space structure travels alongside '
        'the functor rather than being discarded by the choice of category.'))
    E.append(sp(6))

    # ── Section IV: F_C / KleisliCat PMF ──────────────────────────────────────────
    print('[build_zph_native_addendum] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: F_C — The Snap Floor in KleisliCat PMF', S['h1']),
        hr(),
    ]
    E.append(body(
        'The information layer measures the snap as one bit of divergence between '
        'distributions (ZP-C, JSD = log 2). Its native category is the Kleisli category of '
        'the finite-distribution monad PMF: objects are finite types, and a morphism A '
        '&#8594; B is a stochastic map (a Markov kernel), assigning to each a &#8712; A a '
        'probability distribution on B. Mathlib supplies this category for free, since PMF '
        'is a lawful monad.'))
    E.append(result_box(
        'Functor: fC_functor : ℕ → KleisliCat PMF (ZPH_InfoFunctor.lean)',
        [
            'Object  n &#8614; Fin n, the type of n distinguishable outcomes.',
            'Morphism (n &#8804; m): the deterministic embedding (each outcome mapped to its '
            'image with certainty).',
            '',
            'fC_zero_isInitial:   Fin 0 (the empty type) is the initial object.',
            'fC_no_return:   for n &gt; 0 there is NO stochastic map Fin n &#8594; Fin 0.',
            'AX-G2 as a theorem: no probability distribution lives on the empty type, so '
            'nothing returns to the floor.',
            'Sorry-free. Purity [propext, Classical.choice, Quot.sound].',
        ]
    ))
    E.append(sp(4))
    E.append(body(
        'The empty type is the snap floor here, and it carries the snap\'s irreversibility '
        'for free. A stochastic map into Fin 0 would be a probability distribution on the '
        'empty type, and there is none. So while every object has a unique map <i>out</i> of '
        'Fin 0 (it is initial), no nonempty object has any map <i>back</i> &#8212; AX-G2 '
        '(source asymmetry) is not assumed but proved, as fC_no_return. Of the three native '
        'categories, this is the one where the framework\'s irreversibility axiom becomes a '
        'theorem of the ambient mathematics.'))
    E.append(sp(6))

    # ── Section V: MC-1 correspondence, scope, purity ─────────────────────────────
    print('[build_zph_native_addendum] Building Section V...')
    E += [
        hr(),
        Paragraph('Section V: The MC-1 Correspondence, Scope, and Purity', S['h1']),
        hr(),
    ]
    E.append(body(
        'The three functors, together with F_A (the join-semilattice &#8469; of the main '
        'document, where 0 is already the initial object), are bundled as a single witness.'))
    E.append(result_box(
        'Definition: mc1_correspondence : MC1Correspondence (ZPH_MC1.lean)',
        [
            'A record collecting the native-category realizations:',
            '&#8226;  F_D: StateSpace 0 is initial in ModuleCat &#8450;.',
            '&#8226;  F_C: Fin 0 is initial in KleisliCat PMF, with no return morphism.',
            '&#8226;  F_B: the clopen-ball tower has inverse limit {0} in TopCat.',
            'Sorry-free. Purity [propext, Classical.choice, Quot.sound].',
        ]
    ))
    E.append(sp(4))
    E.append(body(
        'This settles the <b>correspondence</b> half of MC-1: across the native categories, '
        'the snap floor is each category\'s own categorical bottom, and the four agree on '
        'the snap. It does not settle the <b>identity</b> half. That the algebraic &#8869;, '
        'the 2-adic 0, the zero module, and the empty type are numerically one object is a '
        'modeling commitment &#8212; a choice to read four categorical bottoms as a single '
        'thing &#8212; not a theorem proved here. The same fence stands as for the diagonal '
        'fixed point: the framework reads these as faces of one object; it proves each the '
        'categorical bottom of its own category, and leaves their literal identity as an '
        'interpretive commitment.'))
    E.append(label_box(
        'Scope and Purity',
        [
            'This is a formalisation milestone, not new category theory. TopCat, ModuleCat '
            '&#8450;, and the Kleisli category of PMF are standard Mathlib categories with '
            'standard universal properties. The contribution is realizing the ZP snap floor '
            'inside each as a genuine functor, in place of the &#8469;-indexed depth '
            'proxies of the main document.',
            'Purity: [propext, Classical.choice, Quot.sound]. Unlike the choice-free ZP-J '
            'results, these functors inherit Classical.choice from Mathlib\'s topology, '
            'inner-product, and PMF libraries. The dependency is a library inheritance, not '
            'a new commitment of the construction; whether it is structurally forced is the '
            'open question tracked under Classical.choice necessity (ZP-L / ZP-M).',
        ]
    ))
    E.append(sp(4))
    E.append(label_box(
        'Lean Source Files',
        [
            'ZPH_TopFunctor.lean  &#8212; fB_functor, fB_bottom_is_limit (F_B into TopCat).',
            'ZPH_HilbFunctor.lean &#8212; fD_functor, fD_zero_isInitial, fD_embed_inner '
            '(F_D into ModuleCat &#8450;).',
            'ZPH_InfoFunctor.lean &#8212; fC_functor, fC_zero_isInitial, fC_no_return '
            '(F_C into KleisliCat PMF).',
            'ZPH_MC1.lean         &#8212; mc1_correspondence (the bundled witness).',
            'All in ZeroParadox/ in the public repository.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph(
        'Endnote: This document is an addendum to ZP-H Categorical Bridge and reads after '
        'it. ZP-H locates the snap floor as the categorical bottom across four frameworks '
        'using depth-index proxy categories; this addendum realizes the same floor inside '
        'each framework\'s native Mathlib category &#8212; TopCat, ModuleCat &#8450;, and '
        'the Kleisli category of distributions. All results sorry-free in Lean 4 as of June '
        '2026, footprint [propext, Classical.choice, Quot.sound].',
        S['endnote']))

    print(f'[build_zph_native_addendum] Assembling document ({len(E)} elements)...')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
