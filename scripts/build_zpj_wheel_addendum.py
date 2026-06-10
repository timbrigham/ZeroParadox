"""
Zero Paradox — ZP-J Wheel Addendum: The Wheel of Fractions is a Wheel
Version 1.0 | June 2026
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

VERSION = '1.0'

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
                   'ZP-J Wheel Addendum', 'Version ' + VERSION,
                   date_str='June 2026')
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
        Paragraph('Version ' + VERSION + ' | June 2026', S['subtitle']),
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
        'a wheel from a field. ZP-J Self-Reference left open which structure the Zero Paradox '
        'porthole gives rise to: a wheel, in which &#8734; and &#8869; are distinct, or a '
        'meadow, in which they collapse. This addendum settles that question.'))
    E.append(body(
        'The main result is WheelFrac.instWheel (ZPJ_WheelFrac.lean): for any commutative '
        'ring A and any multiplicative submonoid S, the wheel of fractions '
        '&#8857;<sub>S</sub> A = (A &#215; A)/&#8801;<sub>S</sub> satisfies every axiom of '
        'Carlström\'s Definition 1.1. The companion result WheelFrac.inf_ne_bot shows that, '
        'whenever 0 &#8713; S, the two special elements stay distinct (&#8734; &#8800; '
        '&#8869;) &#8212; so the construction is a wheel, not a meadow. The construction '
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
        'Typeclass: Wheel (ZPJ_Wheel.lean)',
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
        'derived elements &#8734; = /0 and &#8869; = 0&#183;/0 interact with + and &#183;. A '
        'wheel in which &#8734; = &#8869; is exactly a meadow: the distinction between the '
        'two is the whole content of "wheel, not meadow."'))
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
        'Theorem: WheelFrac.instWheel (ZPJ_WheelFrac.lean)',
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

    # ── Section IV: The porthole — wheel, not meadow ───────────────────────────
    print('[build_zpj_wheel_addendum] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: Wheel, Not Meadow', S['h1']),
        hr(),
    ]
    E.append(body(
        'A wheel collapses to a meadow precisely when its two special elements coincide. '
        'For the wheel of fractions this collapse happens exactly when 0 &#8712; S: if S '
        'contains a zero divisor witness for 0, the fraction [1,0] and the fraction [0,0] '
        'become identified. The natural hypothesis 0 &#8713; S (which holds whenever S is '
        'the complement of a prime ideal, the usual case) keeps them apart.'))
    E.append(result_box(
        'Theorem: WheelFrac.inf_ne_bot (ZPJ_WheelFrac.lean)',
        [
            '&#8704; {A : Type*} [CommRing A] (S : Submonoid A),',
            '  (0 : A) &#8713; S  &#8594;  &#8734; &#8800; &#8869;     in &#8857;<sub>S</sub> A',
            '',
            'When 0 &#8713; S, the reciprocal of zero (&#8734; = /0) and the absorbing '
            'element (&#8869; = 0&#183;/0) are distinct. The construction is a genuine '
            'wheel, not a meadow.',
            'Proof: &#8734; = &#8869; would yield witnesses s, s&#8242; &#8712; S with '
            's&#183;1 = s&#8242;&#183;0, forcing s = 0 and hence 0 &#8712; S &#8212; '
            'contradicting the hypothesis.',
            'Sorry-free. Lean purity: [propext, Quot.sound] &#8212; Classical.choice-free.',
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
            'predicts. The concrete carrier ZPWheelElem (ZPJ_Wheel.lean §III&#8211;VI) '
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
        'derivation, WheelValuationStructure (ZPJ_Wheel.lean §VII), is defined but its '
        'porthole condition val(0) = &#8868; is an assumed axiom, motivated by the ZP '
        'argument rather than type-checked as necessary.'))
    E.append(label_box(
        'Lean Source Files',
        [
            'ZPJ_WheelFrac.lean &#8212; rel, srel, the five quotient operations '
            '(waddF, wmulF, winvF), instWheel, inf_ne_bot. The headline results of this '
            'addendum.',
            'ZPJ_Wheel.lean     &#8212; the Wheel typeclass (Carlström Def 1.1, 14 fields), '
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
        ]
    ))
    E.append(sp(4))
    E.append(remark_box(
        'Remark R-J.W &#8212; Relationship to Carlström\'s Theorem',
        [
            'Carlström introduced wheels in Wheels &#8212; On Division by Zero (Research '
            'Reports in Mathematics No. 11, Department of Mathematics, Stockholm '
            'University, 2001; a Licentiate thesis), where Definition 1.1 (p. 5) gives the '
            'eight wheel axioms and the wheel of fractions is constructed (§1.2, §4.2). '
            'The work was later published as Wheels &#8212; on division by zero, '
            'Mathematical Structures in Computer Science 14(1):143&#8211;184, 2004. '
            'Carlström proved there that the wheel of fractions of a commutative ring is a '
            'wheel. The result here is that theorem, encoded in Lean 4 against a typeclass '
            'that reproduces his Definition 1.1 field for field, and discharged without '
            'the axiom of choice. The encoding is what is new: a third party can read the '
            '14 fields against Carlström\'s eight axioms and confirm the correspondence, '
            'and can read the axiom footprint to confirm the choice-free claim. Whether '
            'the porthole condition val(0) = &#8868; can be derived &#8212; rather than '
            'assumed &#8212; from upstream ZP structure remains the open question flagged '
            'in ZPJ_Wheel.lean §VII&#8211;VIII.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph(
        'Endnote: This document is an addendum to ZP-J Self-Reference and reads after it. '
        'ZP-J established the porthole (val(&#8869;) = &#8734;, &#8869; = {&#8869;}); this '
        'document gives its algebraic form, the wheel of fractions, and the machine-verified '
        'proof that the construction is a wheel rather than a meadow. All results sorry-free '
        'in Lean 4 as of June 2026, footprint [propext, Quot.sound].',
        S['endnote']))

    print(f'[build_zpj_wheel_addendum] Assembling document ({len(E)} elements)...')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
