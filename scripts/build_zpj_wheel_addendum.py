"""
Zero Paradox — ZP-J Wheel Addendum: The Wheel of Fractions is a Wheel
Version 1.7 | September 2026
v1.7: THE DEGENERATE OVERLAP IS RESTORED, AND THE TERM-LEVEL IDENTIFICATION WITH IT (two-pole audit, 2026-09-13, Tim's call). v1.6 deleted the sentence "the one overlap is degenerate, and is worth stating exactly rather than denying" together with the false "never the reverse", although 43116ba had recorded the decision that the overlap is stated rather than denied. Both charts are now on the page: beyond one element no carrier is a wheel whose /0 is 0 (Wheel.lean section V, by its binders), and the one-element algebra is both a wheel with infinity = bottom and a model of the meadow equations (a new rfl example in the same section, with Ref and Ril checked at arXiv:0901.0823 p. 2; the separation-axiom quote is the one v1.5 already used, 1406.6878 section 1 p. 2). The remark's "no pair of new elements available to identify" was element-level only; at the level of terms 0^-1 and 0*0^-1 both evaluate to 0, so the meadow does equate the two terms a wheel keeps apart.
v1.6: THE MEADOW REMARK'S IMPLICATION IS DELETED, NOT RESTATED. Five successive versions tried
      to state a SCOPED implication in unscoped prose and all five failed: v1.0-1.3 "a wheel in
      which ∞ = ⊥ is exactly a meadow" (false); v1.4 "neither kind of meadow is a wheel with
      ∞ = ⊥" (vacuous); v1.5 "no NON-TRIVIAL meadow of either kind is..." (vacuous again,
      independently); and v1.5's replacement "the implication runs meadow-equation to triviality,
      never the reverse" (FALSE — it dropped the binder). The Lean states it correctly because it
      HAS binders: `example {W : Type*} [Wheel W] (hm : winv 0 = 0) : ∀ x y : W, x = y` scopes the
      hypothesis to a wheel. Strip `[Wheel W]` and the sentence becomes a claim about meadows in
      general — false for ℚ and for every field, and contradicted by the Bergstra, Hirshfeld &
      Tucker definition quoted in the same box. The second clause was worse: "never the reverse"
      denied the sentence immediately before it, which had just asserted that the one-element wheel
      satisfies the meadow equations. (The Wheel.lean gloss it was truncated from reads "never the
      reverse — a one-element wheel need not have arisen this way", which makes it a claim about
      PROVENANCE; the PDF kept only the first half.) So no implication arrow about meadows survives
      in the rendered prose at all. Both directions are cited to the machine-checked examples in
      ZeroParadox/Algebra/Wheel.lean §V, where the binders carry the scope. The absence claim is
      now DATED and scoped to a named search set, and the Bergstra & Ponse null is attributed to
      COMMON meadows only, which is all they say.
      Also: inf_ne_bot relabelled Proposition (page 1 calls it "the companion result", and
      R-NAMING reserves Theorem for the primary result); `#print axioms` added for
      zpw_top_val_iff_inv_is_inf so the Axiom Footprint box's claim is reproducible from the file
      it cites; the endnote's sorry-free survey re-dated; docstring month corrected to match the
      rendered title block, which zp_utils.version_line() derives automatically.
v1.5: the v1.4 correction over-corrected, and its universal negative is false at every point of
      its domain. It read "So neither kind of meadow is a wheel with ∞ = ⊥, and neither arises by
      collapsing one." By Prop. 4.4 the ONLY wheel with ∞ = ⊥ is the one-element one, and that
      algebra IS a meadow of both kinds: the meadow axioms are purely equational, and Bergstra &
      Ponse state it in terms (1406.6878, §1 p. 2) — "we do not require a meadow to satisfy the
      separation axiom 0 ≠ 1." So the forward direction is VACUOUS, not false. Wheel.lean §V
      already carried the right qualifier ("NON-TRIVIAL involutive meadow") and the rendered prose
      had dropped it. Now quantified over non-trivial meadows, with the degenerate overlap stated
      rather than denied. "The originators say as much" also went: not-yet-found is not not-there,
      and the quote is Bergstra & Ponse's, who originated COMMON meadows, not meadows.
      Three more, folded in under the same bump:
      (1) THE ENDNOTE GENERALISED A SCOPED FOOTPRINT. It said "All results sorry-free in Lean 4
          as of June 2026, footprint [propext, Quot.sound]" while the Axiom Footprint box one page
          earlier already scopes that footprint to the headline results. Re-measured here:
          instWheel and inf_ne_bot are [propext, Quot.sound]; zpw_inf_ne_bot is [propext]; and
          zpw_inv_zero_eq_inf, zpw_zero_mul_inf_eq_bot and zpw_top_val_iff_inv_is_inf each carry
          Classical.choice — the last of them named one page earlier as "proved directly". The
          endnote now carries the box's scope and the measured exceptions.
      (2) "if S contains a zero divisor witness for 0" was garbled, and on its natural reading
          false: in Z/6, S = {1,2,4} is a submonoid of zero divisors with 0 ∉ S, so inf_ne_bot
          gives ∞ ≠ ⊥. The condition is 0 ∈ S, and the witnesses are now named (s = 0, s′ = 1).
      (3) "that degeneracy happens exactly when 0 ∈ S" implied a biconditional this corpus does
          not prove. Only 0 ∉ S → ∞ ≠ ⊥ is a declaration here; the converse is Carlström's own
          (p. 5) and is now cited to him rather than implied to be ours.
v1.4: wheel/meadow claim corrected (bedrock, prior-art gate). Struck "a wheel in which ∞ = ⊥ is
      exactly a meadow" and "a wheel collapses to a meadow": identifying the two forces the
      ONE-ELEMENT wheel (Carlström 2001:11 Prop. 4.4, p. 25), and a meadow (Bergstra & Tucker)
      adjoins no new element at all — it totalizes inverse by 0⁻¹ = 0, while a COMMON meadow
      adjoins one absorbing element and is non-involutive, so it fails W7. Bergstra & Ponse
      record that no structural connection between the two constructions is known.
      Credit corrected: the name and construction are Setzer's; Carlström generalizes them to
      any commutative SEMIRING.
v1.3: rendered Lean-file citations synced to post-reorg basenames (namespace de-scar); docstring changelog above kept as the historical record.
v1.1: WheelFrac.* citations updated to ZPJ_WheelFrac.* (Lean namespace standardization).
v1.0: Initial release. Presents the formal construction of the wheel of fractions
      ⊙_S A = (A × A)/≡_S for a commutative ring A and multiplicative submonoid S,
      and the machine-verified proof that it satisfies all of Carlström's Definition 1.1
      wheel axioms (his eight, unbundled into 14 equational fields), with the porthole
      ∞ ≠ ⊥ (wheel, not meadow) given 0 ∉ S.
      Lean source: ZPJ_WheelFrac.lean (parent: ZPJ_Wheel.lean for the Wheel typeclass).
      Axiom footprint: [propext, Quot.sound] — Classical.choice-free.
Reads after ZP-J Self-Reference.
"""

import os
from zp_utils import *
from reportlab.platypus import KeepTogether

VERSION = '1.7'
FIRST_RELEASED = 'June 2026'

# ── fix() guard: route all bare Paragraph() text through Unicode-to-entity conversion ──
# PDF Rendering Standards require fix() on all rendered text. Patch Paragraph so bare
# Paragraph(...) calls (title block, section headers) auto-convert raw unicode (⊙, ö, …)
# rather than relying on the font happening to cover the glyph. Box/body helpers already fix().
_Paragraph_orig = Paragraph
def Paragraph(text, style):
    return _Paragraph_orig(fix(text) if isinstance(text, str) else text, style)


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-J_Wheel_Addendum.pdf')
    print(f'[build_zpj_wheel_addendum] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-J Wheel Addendum',
                   'ZP-J Wheel Addendum', 'Version ' + VERSION)
    E = []

    # ── Header banner (matches addendum/companion template) ────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('ZP-J Wheel Addendum',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    print('[build_zpj_wheel_addendum] Building title block...')
    E += [
        sp(4),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-J Wheel Addendum', S['title']),
        Paragraph('The Wheel of Fractions is a Wheel', S['subtitle']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    # ── Preamble ───────────────────────────────────────────────────────────────
    print('[build_zpj_wheel_addendum] Building preamble...')
    E.append(body(
        'A wheel (Carlström 2001) is an algebraic structure that extends a commutative '
        'ring by making division a total operation: every element, including 0, has a '
        'reciprocal /x, so /0 becomes a defined first-class element rather than an error. '
        'The two elements this produces &#8212; &#8734; = /0 (the reciprocal of zero) and '
        '&#8869; = 0&#183;/0 (an absorbing "undefined" element) &#8212; are what distinguish '
        'a wheel from a field. ZP-J Self-Reference left open which of the two standard ways '
        'of totalising division the Zero Paradox porthole gives rise to: a <b>wheel</b>, which '
        'adjoins &#8734; and &#8869; as two distinct new elements, or a <b>meadow</b> (Bergstra '
        '&amp; Tucker), which adjoins nothing at all and instead declares 0<sup>&#8722;1</sup> = 0, '
        'staying inside the original number system. This addendum settles that question.'))
    E.append(body(
        'The main result is WheelFrac.instWheel (WheelFrac.lean): for any commutative '
        'ring A and any multiplicative submonoid S, the wheel of fractions '
        '&#8857;<sub>S</sub> A = (A &#215; A)/&#8801;<sub>S</sub> satisfies every axiom of '
        'Carlström\'s Definition 1.1. The companion result WheelFrac.inf_ne_bot shows that, '
        'whenever 0 &#8713; S, the two special elements stay distinct (&#8734; &#8800; '
        '&#8869;) &#8212; so the construction is a <i>non-trivial</i> wheel. The construction '
        'is Carlström\'s; the contribution here is a faithful, machine-verified encoding '
        'of it that is also free of the axiom of choice (footprint [propext, Quot.sound]), '
        'situated as the algebraic form of the ZP porthole.'))
    E.append(hr())

    # ── Section I: The Wheel typeclass ─────────────────────────────────────────
    print('[build_zpj_wheel_addendum] Building Section I...')
    E += [
        Paragraph('Section I: The Wheel Axioms (Carlström Definition 1.1)', S['h1']),
        hr(),
    ]
    E.append(body(
        'A wheel is a set W with two binary operations + and &#183;, a unary involution / '
        '(reciprocal), and two constants 0 and 1, subject to eight axioms. Carlström\'s '
        'Definition 1.1 packages the additive and multiplicative parts as commutative '
        'monoids; the ZP Wheel typeclass unbundles those two monoid axioms into their '
        'separate equational laws, giving 14 fields that are equivalent to Carlström\'s '
        'eight. The unbundling is bookkeeping only &#8212; no axiom is added, removed, or '
        'weakened.'))
    E.append(def_box(
        'Typeclass: Wheel (Wheel.lean)',
        [
            'class Wheel (W : Type*) where',
            '  wadd, wmul : W &#8594; W &#8594; W      -- + and &#183;',
            '  winv : W &#8594; W                  -- the involution /',
            '  wzero, wone : W                 -- 0 and 1',
            '  -- W1&#8211;W3:  (W, +, 0) commutative monoid     [Carlström (1)]',
            '  -- W4&#8211;W6:  (W, &#183;, 1) commutative monoid     [Carlström (2), monoid part]',
            '  -- W7:  /(/x) = x                            [Carlström (2), involution]',
            '  -- W8:  /(x&#183;y) = /x &#183; /y                   [Carlström (2), involution]',
            '  -- W9:  weakened distributivity              [Carlström (3)]',
            '  -- W10: (x&#183;/y + z) + 0&#183;y = (x + y&#183;z)&#183;/y      [Carlström (4)]',
            '  -- W11: 0&#183;0 = 0                              [Carlström (5)]',
            '  -- W12: (x + 0&#183;y)&#183;z = x&#183;z + 0&#183;y            [Carlström (6)]',
            '  -- W13: /(x + 0&#183;y) = /x + 0&#183;y              [Carlström (7)]',
            '  -- W14: x + 0&#183;/0 = 0&#183;/0                    [Carlström (8)]',
        ]
    ))
    E.append(sp(4))
    E.append(body(
        'The last group of axioms is what makes division total. W7 and W8 make / an '
        'involution that distributes over multiplication; W9&#8211;W14 govern how the two '
        'derived elements &#8734; = /0 and &#8869; = 0&#183;/0 interact with + and &#183;. '
        'Keeping those two apart is not a stylistic preference over some rival algebra: by '
        'Carlström\'s Proposition 4.4 (p. 25), if <i>any</i> two of 0, 1, /0 and 0/0 are equal '
        'in a wheel, the wheel is trivial &#8212; it has exactly one element. So &#8734; '
        '&#8800; &#8869; is the condition for the structure to have more than one element at '
        'all. The same statement is machine-checked over the Wheel typeclass in '
        'ZeroParadox/Algebra/Wheel.lean §V: identifying &#8734; with &#8869; proves '
        '&#8704; x y, x = y.'))
    E.append(sp(6))

    # ── Section II: The wheel of fractions construction ────────────────────────
    print('[build_zpj_wheel_addendum] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: The Wheel of Fractions ⊙_S A', S['h1']),
        hr(),
    ]
    E.append(body(
        'The wheel of fractions generalises the field-of-fractions construction so that it '
        'survives division by zero. Start from a commutative ring A and a multiplicative '
        'submonoid S &#8838; A (a set containing 1 and closed under multiplication). Form '
        'pairs (x, y) &#8712; A &#215; A &#8212; read as the formal fraction x/y &#8212; and '
        'quotient by the relation &#8801;<sub>S</sub> below.'))
    E.append(def_box(
        'Construction (Carlström 2001, pp. 4&#8211;5)',
        [
            '&#8857;<sub>S</sub> A = (A &#215; A) / &#8801;<sub>S</sub>',
            '',
            '(x, y) &#8801;<sub>S</sub> (x&#8242;, y&#8242;)   &#8660;   &#8707; s, s&#8242; &#8712; S,'
            '   s&#183;x = s&#8242;&#183;x&#8242;   &#8743;   s&#183;y = s&#8242;&#183;y&#8242;',
            '',
            '0 = [0, 1]      1 = [1, 1]',
            '[x,y] + [x&#8242;,y&#8242;] = [x&#183;y&#8242; + x&#8242;&#183;y,  y&#183;y&#8242;]',
            '[x,y] &#183; [x&#8242;,y&#8242;] = [x&#183;x&#8242;,  y&#183;y&#8242;]',
            '/[x,y] = [y, x]               (the involution is pair-swap)',
            '',
            'Then  /0 = [1,0] = &#8734;   and   0&#183;/0 = [0,0] = &#8869;.',
        ]
    ))
    E.append(sp(4))
    E.append(body(
        'The choice of relation matters. The naive cross-multiplication x&#183;y&#8242; = '
        'x&#8242;&#183;y &#8212; the one that defines equality of ordinary fractions &#8212; '
        'is <i>not</i> an equivalence relation on a general commutative ring: transitivity '
        'fails without a cancellation law. The submonoid-quotient relation '
        '&#8801;<sub>S</sub> repairs this by witnessing each identification with elements '
        'of S, and it is provably reflexive, symmetric, and transitive '
        '(WheelFrac.srel). Each of the five operations is then well-defined on the '
        'quotient &#8212; the proofs that they respect &#8801;<sub>S</sub> are the bulk of '
        'the formalisation.'))
    E.append(sp(6))

    # ── Section III: The main theorem ──────────────────────────────────────────
    print('[build_zpj_wheel_addendum] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: ⊙_S A is a Wheel', S['h1']),
        hr(),
    ]
    E.append(body(
        'With the operations shown well-defined, every one of the 14 typeclass fields '
        'is discharged. The additive and multiplicative monoid laws and the distributivity '
        'and porthole axioms all reduce, after lifting representatives, to ring identities '
        'in A closed by ring normalisation; the two involution laws (W7, W8) hold '
        'definitionally because pair-swap is its own inverse and commutes with the '
        'componentwise product.'))
    E.append(result_box(
        'Theorem: WheelFrac.instWheel (WheelFrac.lean)',
        [
            '&#8704; {A : Type*} [CommRing A] (S : Submonoid A),',
            '  Wheel (&#8857;<sub>S</sub> A)',
            '',
            'For every commutative ring A and multiplicative submonoid S, the wheel of '
            'fractions &#8857;<sub>S</sub> A satisfies all 14 fields of the ZP Wheel '
            'typeclass &#8212; equivalently, all eight axioms of Carlström\'s Definition '
            '1.1.',
            'Sorry-free. Lean purity: [propext, Quot.sound] &#8212; Classical.choice-free.',
        ]
    ))
    E.append(sp(6))

    # ── Section IV: The porthole — a non-trivial wheel, and not a meadow ───────
    print('[build_zpj_wheel_addendum] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: Wheel, Not Meadow', S['h1']),
        hr(),
    ]
    E.append(body(
        'A wheel whose two special elements coincide is the one-element wheel '
        '(Carlström, Proposition 4.4). For the wheel of fractions the trigger is exactly '
        '0 &#8712; S: taking s = 0 and s&#8242; = 1 as the witnesses identifies the fraction '
        '[1,0] with the fraction [0,0], and every other pair with them. What is proved below '
        'is one direction &#8212; 0 &#8713; S keeps them apart. The converse is Carlström\'s '
        'own observation that if 0 &#8712; S then the relation is improper and '
        '&#8857;<sub>S</sub> A is trivial (p. 5). The natural hypothesis 0 &#8713; S holds '
        'whenever S is the complement of a prime ideal, the usual case.'))
    E.append(result_box(
        'Proposition: WheelFrac.inf_ne_bot (WheelFrac.lean)',
        [
            '&#8704; {A : Type*} [CommRing A] (S : Submonoid A),',
            '  (0 : A) &#8713; S  &#8594;  &#8734; &#8800; &#8869;     in &#8857;<sub>S</sub> A',
            '',
            'When 0 &#8713; S, the reciprocal of zero (&#8734; = /0) and the absorbing '
            'element (&#8869; = 0&#183;/0) are distinct. The construction is therefore a '
            'non-trivial wheel.',
            'Proof: &#8734; = &#8869; would yield witnesses s, s&#8242; &#8712; S with '
            's&#183;1 = s&#8242;&#183;0, forcing s = 0 and hence 0 &#8712; S &#8212; '
            'contradicting the hypothesis.',
            'Sorry-free. Lean purity: [propext, Quot.sound] &#8212; Classical.choice-free.',
        ]
    ))
    E.append(sp(4))
    E.append(remark_box(
        'Remark &#8212; What a meadow actually is',
        [
            'A <b>meadow</b> answers the same question a different way, and it adjoins no '
            'element at all: Bergstra, Hirshfeld and Tucker define one as "a commutative ring '
            'with a total inverse operator satisfying two equations which imply '
            '0<sup>&#8722;1</sup> = 0." The carrier is unchanged, so there is no pair of new '
            'elements available to identify. At the level of terms the identification still happens: '
            '0<sup>&#8722;1</sup> and 0&#183;0<sup>&#8722;1</sup> both evaluate to the existing 0, so a '
            'meadow equates the two terms a wheel keeps apart. Bergstra and Ponse fix the default: "by default a '
            '\'meadow\' is assumed to be an involutive meadow", the involutive ones being '
            'exactly those with 0<sup>&#8722;1</sup> = 0.',
            'A <b>common meadow</b> is the other variant: it adjoins one element &#8212; an '
            'absorbing element, written <i>a</i>, serving as the inverse of zero. Bergstra and '
            'Ponse record what that costs the inverse operation: "the inverse function of a '
            'common meadow is not an involution because '
            '(0<sup>&#8722;1</sup>)<sup>&#8722;1</sup> = <i>a</i>," and, setting the two '
            'constructions side by side, "wheels are involutive whereas common meadows are '
            'non-involutive."',
            'Both directions of why no carrier is at once a non-trivial wheel and an involutive '
            'meadow are carried as machine-checked <i>example</i>s in '
            'ZeroParadox/Algebra/Wheel.lean §V, with controls showing both hypotheses are '
            'load-bearing. The statements are scoped there by their binders, which is why they '
            'are cited rather than restated here. The one overlap is degenerate, and it is stated '
            'rather than denied: the one-element algebra is a wheel in which &#8734; = &#8869; and also '
            'satisfies the meadow equations; Bergstra and Ponse "do not require a meadow to satisfy the '
            'separation axiom 0 &#8800; 1" (arXiv:1406.6878, &#167;1, p. 2). Both facts are examples in the '
            'same section. Searched 2026-09-13 over the sources listed '
            'below: no structural connection between the two constructions located; Bergstra '
            'and Ponse report not having found one for <b>common</b> meadows.',
            'Sources: J. A. Bergstra, Y. Hirshfeld and J. V. Tucker, "Meadows and the '
            'equational specification of division", arXiv:0901.0823 (abstract); J. A. Bergstra '
            'and A. Ponse, "Division by Zero in Common Meadows", arXiv:1406.6878v4, §1 (p. 2) '
            'and §4 (p. 14). The concept originates with J. A. Bergstra and J. V. Tucker, '
            '"The rational numbers as an abstract data type", JACM 54(2), 2007.',
        ]
    ))
    E.append(sp(4))
    E.append(remark_box(
        'Remark &#8212; The Porthole Connection',
        [
            'In ZP-J, the porthole is the point where val(&#8869;) = &#8734; and '
            '&#8869; = {&#8869;} coincide &#8212; the same structural fact written in the '
            '2-adic valuation (v&#8322;(0) = &#8734;) and in ZF+AFA (the Quine atom). The '
            'wheel of fractions is the algebraic face of that point: /0 is defined and '
            'distinct from the absorbing &#8869;, exactly the behaviour the porthole '
            'predicts. The concrete carrier ZPWheelElem (Wheel.lean §III&#8211;VI) '
            'makes this explicit on the rationals extended with &#8734; and &#8869;, where '
            'val(x) = &#8734; &#8660; /x = &#8734; is proved directly '
            '(zpw_top_val_iff_inv_is_inf). This addendum\'s headline result is the general '
            'construction over an arbitrary commutative ring; the concrete carrier is the '
            'illustrative special case.',
        ]
    ))
    E.append(sp(6))

    # ── Section V: Scope, purity, relationship to Carlström ────────────────────
    print('[build_zpj_wheel_addendum] Building Section V...')
    E += [
        hr(),
        Paragraph('Section V: Scope, Purity, and Relationship to Carlström', S['h1']),
        hr(),
    ]
    E.append(body(
        'Two scope boundaries are worth stating plainly. <b>This is a formalisation, not '
        'new mathematics.</b> The wheel of fractions and the theorem that it is a wheel are '
        'Carlström\'s. What is contributed here is a machine-checked encoding faithful to '
        'Definition 1.1, with a verified axiom footprint, placed in the ZP porthole '
        'context. <b>Ring structure is an input, not a conclusion.</b> The construction '
        'starts from a commutative ring and a submonoid; it does not derive wheel structure '
        'from the ZP lattice axioms alone. The bridge typeclass that would state such a '
        'derivation, WheelValuationStructure (Wheel.lean §VII), is defined but its '
        'porthole condition val(0) = &#8868; is an assumed axiom, motivated by the ZP '
        'argument rather than type-checked as necessary.'))
    E.append(label_box(
        'Lean Source Files',
        [
            'WheelFrac.lean &#8212; rel, srel, the five quotient operations '
            '(waddF, wmulF, winvF), instWheel, inf_ne_bot. The headline results of this '
            'addendum.',
            'Wheel.lean     &#8212; the Wheel typeclass (Carlström Def 1.1, 14 fields), '
            'the derived elements wheelInf / wheelBot, the concrete carrier ZPWheelElem, '
            'and the porthole correspondence zpw_top_val_iff_inv_is_inf.',
            'Both files in ZeroParadox/ in the public repository.',
        ]
    ))
    E.append(sp(4))
    E.append(label_box(
        'Axiom Footprint (headline results: instWheel, inf_ne_bot)',
        [
            '[propext, Quot.sound] &#8212; Classical.choice-free.',
            'propext    &#8212; propositional extensionality (standard in Lean 4)',
            'Quot.sound &#8212; quotient soundness (standard in Lean 4; the construction '
            'is a quotient, so this is expected and unavoidable)',
            'No Classical.choice. No Dependent Choice. No set-theoretic assumptions.',
            'This scope is the headline results, not the whole document. Measured against '
            'the corpus, the concrete-carrier theorems zpw_inv_zero_eq_inf, '
            'zpw_zero_mul_inf_eq_bot and zpw_top_val_iff_inv_is_inf each carry '
            'Classical.choice; zpw_inf_ne_bot is [propext].',
        ]
    ))
    E.append(sp(4))
    E.append(remark_box(
        'Remark R-J.W &#8212; Relationship to Carlström\'s Theorem',
        [
            'The name and the original construction are <b>Setzer\'s</b>, not Carlström\'s. '
            'Carlström records the lineage on his own p. 3: Edalat and Potts adjoined '
            '&#8734; = 1/0 and &#8869; = 0/0 to the reals; Martin-Löf proposed building them '
            'into the construction of the rationals from the integers; "such structures were '
            'called \'wheels\' (the term inspired by the topological picture &#8857; of the '
            'projective line together with an extra point 0/0) by Setzer [Set97], who showed '
            'how to modify the construction of fields of fractions from integral domains so '
            'that wheels are obtained instead of fields."',
            'Carlström is the <b>generalizer</b>: "in this paper, we generalize Setzer\'s '
            'construction, so that it applies not only to integral domains, but to any '
            'commutative semiring." That is Wheels &#8212; On Division by Zero (Research '
            'Reports in Mathematics No. 11, Department of Mathematics, Stockholm '
            'University, 2001; a Licentiate thesis), where Definition 1.1 (p. 5) gives the '
            'eight wheel axioms and the wheel of fractions is constructed (§1.2, §4.2). '
            'The work was later published as Wheels &#8212; on division by zero, '
            'Mathematical Structures in Computer Science 14(1):143&#8211;184, 2004. '
            'His theorem covers commutative <i>semirings</i>; the Lean encoding in '
            'ZeroParadox/Algebra/WheelFrac.lean is stated for commutative <i>rings</i>, so it '
            'is the narrower case of his result, '
            'not the same generality. The result here is that theorem, encoded in Lean 4 '
            'against a typeclass '
            'that reproduces his Definition 1.1 field for field, and discharged without '
            'the axiom of choice. The encoding is what is new: a third party can read the '
            '14 fields against Carlström\'s eight axioms and confirm the correspondence, '
            'and can read the axiom footprint to confirm the choice-free claim. Whether '
            'the porthole condition val(0) = &#8868; can be derived &#8212; rather than '
            'assumed &#8212; from upstream ZP structure remains the open question flagged '
            'in Wheel.lean §VII&#8211;VIII.',
        ]
    ))
    E.append(sp(6))

    # PIN: the endnote must never split across a page boundary. At v1.5 it broke mid-sentence
    # and orphaned three continuation lines, which is what took the document from five pages to
    # six. KeepTogether binds that to the CONTENT, so it holds whether the endnote grows or
    # shrinks; a hard PageBreak would instead force a sixth page even once the text fits on five.
    E.append(KeepTogether(Paragraph(
        'Endnote: This document is an addendum to ZP-J Self-Reference and reads after it. '
        'ZP-J established the porthole (val(&#8869;) = &#8734;, &#8869; = {&#8869;}); this '
        'document gives its algebraic form, the wheel of fractions, and the machine-verified '
        'proof that the construction is a wheel and a non-trivial one. All results sorry-free '
        'in Lean 4 as of September 2026. Footprints are per result, and [propext, Quot.sound] is '
        'the headline results\'; the Axiom Footprint box above gives the scope and the '
        'measured exceptions.',
        S['endnote'])))

    print(f'[build_zpj_wheel_addendum] Assembling document ({len(E)} elements)...')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
