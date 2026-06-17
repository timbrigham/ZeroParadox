"""
Build ZP-J Wheel Illustrated Companion
Version 1.0 | June 2026
v1.0: Initial release. Plain-language companion to the ZP-J Wheel Addendum
      (ZPJ_Wheel.lean / ZPJ_WheelFrac.lean). Explains what a wheel is (division
      by zero made total), the two derived elements ∞ = /0 and ⊥ = 0·/0, the
      wheel-vs-meadow distinction, the wheel-of-fractions construction
      ⊙_S A = (A×A)/≡_S, the machine-verified result that it is a wheel
      (Carlström Def 1.1, choice-free [propext, Quot.sound]), and the porthole
      connection to ZP-J. One diagram: wheel vs meadow.
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Circle

VERSION = '1.0'


def wheel_vs_meadow_diagram():
    """Wheel: ∞ and ⊥ are two distinct new elements. Meadow: they collapse to one."""
    dw, dh = TW, 2.2 * inch  # 158 pts; content top ~144, bottom ~14
    d = Drawing(dw, dh)

    # LEFT panel — WHEEL: two distinct elements
    lx = dw * 0.27
    d.add(String(lx, 134, 'WHEEL', fontSize=10, fontName='DV-B',
                 fillColor=INDIGO, textAnchor='middle'))
    d.add(Circle(lx, 104, 16, fillColor=INDIGO_LITE, strokeColor=INDIGO, strokeWidth=1.3))
    d.add(String(lx, 99, '∞', fontSize=15, fontName='DV-B',
                 fillColor=INDIGO, textAnchor='middle'))
    d.add(Circle(lx, 56, 16, fillColor=INDIGO, strokeColor=INDIGO, strokeWidth=0))
    d.add(String(lx, 51, '⊥', fontSize=14, fontName='DV-B',
                 fillColor=WHITE, textAnchor='middle'))
    d.add(String(lx, 18, '∞ ≠ ⊥   (two elements)', fontSize=8,
                 fontName='DV-I', fillColor=GREY_TEXT, textAnchor='middle'))

    # divider
    d.add(Line(dw*0.5, 24, dw*0.5, 128, strokeColor=colors.HexColor('#CCCCCC'),
               strokeWidth=0.8))

    # RIGHT panel — MEADOW: they collapse
    rx = dw * 0.73
    d.add(String(rx, 134, 'MEADOW', fontSize=10, fontName='DV-B',
                 fillColor=GREY_TEXT, textAnchor='middle'))
    d.add(Circle(rx, 80, 17, fillColor=INDIGO_LITE, strokeColor=INDIGO, strokeWidth=1.3))
    d.add(String(rx, 75, '∞=⊥', fontSize=11, fontName='DV-B',
                 fillColor=INDIGO, textAnchor='middle'))
    d.add(String(rx, 18, '∞ = ⊥   (they collapse)', fontSize=8,
                 fontName='DV-I', fillColor=GREY_TEXT, textAnchor='middle'))
    return d


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-J_Wheel_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState(); canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-J Wheel Companion  |  Division by Zero  |  June 2026')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
                            title='ZP-J Wheel Illustrated Companion',
                            author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    hdr_ts = TableStyle([('BACKGROUND',(0,0),(-1,-1),COMP_BLUE),
                         ('TOPPADDING',(0,0),(-1,-1),8),('BOTTOMPADDING',(0,0),(-1,-1),8),
                         ('LEFTPADDING',(0,0),(-1,-1),10)])
    hdr = Table([[Paragraph('ZP-J Wheel Illustrated Companion',
                            ParagraphStyle('hdr',fontName='DV-B',fontSize=11,textColor=WHITE))]],
                colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E += [hdr, sp(6),
          Paragraph('Dividing by Zero', CS['title']),
          Paragraph('What a Wheel Is, and Why /0 Becomes a Real Element', CS['subtitle']),
          Paragraph('ZP Companion | Version ' + VERSION + ' | The Wheel of Fractions | June 2026',
                    CS['meta']),
          Paragraph(
              'This companion explains in plain language the ZP-J Wheel Addendum: the '
              'machine-verified proof that the "wheel of fractions" is a wheel - an '
              'algebraic structure (Carlstr&#246;m, 2001) in which dividing by zero is a '
              'defined operation rather than an error. Every formal claim here restates a '
              'theorem already proved in the technical document and its Lean source '
              '(ZPJ_Wheel.lean, ZPJ_WheelFrac.lean). Analogies are included to build '
              'intuition, not as proof claims. Consult the addendum for the authoritative '
              'mathematics.', CS['disc'])]

    # ── The Problem With Dividing by Zero ────────────────────────────────────
    E.append(Paragraph('The Problem With Dividing by Zero', CS['h1']))
    E.append(cbody(
        'In ordinary arithmetic, 1/0 is undefined. You cannot simply declare it equal to '
        'some number: every attempt breaks one of the laws of arithmetic. If 1/0 = &#8734; '
        'and you insist on the usual rules, you quickly derive contradictions like 1 = 2. '
        'So mathematics normally leaves division by zero out, and "/" stays a partial '
        'operation - defined for every input except one.'))
    E.append(cbody(
        'A <b>wheel</b> is a structure that makes division total instead. Every element, '
        'including 0, gets a reciprocal /x, so /0 becomes a first-class member of the '
        'system rather than an error. The trick is not to force /0 to be an ordinary '
        'number - it is to add new elements and adjust the laws so that nothing breaks. '
        'The name comes from the shape of the smallest example: a circle of values with '
        'the two new elements sitting on it.'))
    E.append(sp(4))

    # ── The Two New Elements ─────────────────────────────────────────────────
    E.append(Paragraph('The Two New Elements: &#8734; and &#8869;', CS['h1']))
    E.append(cbody(
        'Making division total introduces exactly two new elements:'))
    E.append(cbody(
        '<b>&#8734; = /0</b> (the reciprocal of zero). This is the "point at infinity" you '
        'may have met on the Riemann sphere, where 0 and &#8734; sit at opposite poles. A '
        'wheel goes one step further than the sphere - it adds the second element &#8869; '
        'below as well - and it makes &#8734; a genuine element you can compute with.'))
    E.append(cbody(
        '<b>&#8869; = 0&#183;/0</b> (zero times the reciprocal of zero). This is an '
        'absorbing "undefined" element: combine it with anything and you get &#8869; back. '
        'It is the wheel\'s honest answer to a genuinely meaningless expression - instead of '
        'crashing, the arithmetic returns a dedicated value that means "no information." '
        '(The wheel writes this element &#8869;, the same symbol the Zero Paradox uses for '
        'its bottom element - see the last section for why that is not a coincidence.)'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy  - The calculator that never crashes', [
        'A pocket calculator shows "Error" when you divide by zero, and then you have to '
        'clear it before you can do anything else. A wheel is like a calculator that, '
        'instead of locking up, returns a special "undefined" reading - and lets you keep '
        'computing. Any further operation on that reading just returns "undefined" again. '
        'Nothing is lost and nothing breaks; the error is absorbed into a value the system '
        'knows how to carry.',
    ]))
    E.append(sp(4))

    # ── Wheel vs Meadow ──────────────────────────────────────────────────────
    E.append(Paragraph('Wheel or Meadow? The Key Question', CS['h1']))
    E.append(cbody(
        'There is one decisive question about any such structure: are &#8734; and &#8869; '
        'two different elements, or do they turn out to be the same? Both answers give a '
        'consistent algebra, and they have different names:'))
    E.append(wheel_vs_meadow_diagram())
    E.append(ccaption(
        'A wheel keeps the reciprocal of zero (&#8734;) and the absorbing undefined element '
        '(&#8869;) distinct. A meadow is the variant in which they collapse into a single '
        'element. The whole content of "wheel, not meadow" is that these two stay apart.'))
    E.append(sp(4))

    # ── Building the Wheel of Fractions ──────────────────────────────────────
    E.append(Paragraph('Building It: Fractions as Pairs', CS['h1']))
    E.append(cbody(
        'The construction at the heart of the addendum is the <b>wheel of fractions</b>, '
        'written &#8857;<sub>S</sub> A. It generalises the way you build fractions from '
        'whole numbers, but it is designed to survive division by zero. Start with any '
        'commutative ring A (a number system with + and &#215;, like the integers) and a '
        'set S of "allowed denominators" closed under multiplication. Write each fraction '
        'as a pair (x, y), meaning x/y.'))
    E.append(cbody(
        'Reciprocal is just <b>swapping the pair</b>: /(x, y) = (y, x). That single move is '
        'what makes division total - and it is why /0 exists. The fraction 0 is (0, 1), so '
        '/0 swaps to (1, 0) = &#8734;, and 0&#183;/0 works out to (0, 0) = &#8869;. Nothing '
        'is forbidden; the pair (1, 0) is a perfectly good fraction in this system.'))
    E.append(cbody(
        'There is one genuine subtlety: when are two fractions equal? The schoolbook rule - '
        'cross-multiply, x&#183;y&#8242; = x&#8242;&#183;y - does not work on a general '
        'number system, because it fails to be transitive without a cancellation law (you '
        'cannot always divide out a common factor). The wheel of fractions fixes this by '
        'requiring a <i>witness</i> from S for every equality: two fractions count as equal '
        'only when elements of S certify it. Checking that this repaired notion of equality '
        'behaves - and that +, &#215;, and / are well defined on it - is the bulk of the '
        'formal proof.'))
    E.append(sp(4))

    # ── The Main Result ──────────────────────────────────────────────────────
    E.append(Paragraph('The Main Result', CS['h1']))
    E.append(cbody(
        'The headline theorem is that this construction always works. For <i>any</i> '
        'commutative ring A and <i>any</i> choice of allowed denominators S, the wheel of '
        'fractions &#8857;<sub>S</sub> A satisfies every wheel axiom - all eight of '
        'Carlstr&#246;m\'s Definition 1.1 (checked in Lean as 14 separate equational '
        'fields). It is a wheel, with no exceptions and no extra hypotheses.'))
    E.append(key_result_box(
        'WheelFrac.instWheel  (machine-verified, Lean 4)',
        'For every commutative ring A and every multiplicative submonoid S, the wheel of '
        'fractions &#8857;<sub>S</sub> A is a wheel - it satisfies all of Carlstr&#246;m\'s '
        'axioms. The proof is sorry-free and free of the axiom of choice: its only '
        'foundations are propositional extensionality and quotient soundness '
        '([propext, Quot.sound]), both standard in Lean 4.'))
    E.append(sp(4))

    # ── Wheel, Not Meadow ────────────────────────────────────────────────────
    E.append(Paragraph('Wheel, Not Meadow', CS['h1']))
    E.append(cbody(
        'Being a wheel is only half the story. The other half is that this construction is '
        'a <i>genuine</i> wheel - the one where &#8734; and &#8869; stay distinct - and not '
        'a meadow in disguise. The addendum proves exactly when that holds: as long as 0 is '
        'not one of the allowed denominators (0 &#8713; S), the reciprocal of zero and the '
        'absorbing element are different.'))
    E.append(cbody(
        'That condition is the normal situation: any sensible set of denominators excludes '
        '0. The nonzero elements of an integral domain, or the complement of a prime ideal '
        '(the usual choice when building fractions), all avoid 0 - so the two elements stay '
        'apart. You only collapse to a meadow if you deliberately allow 0 as a denominator.'))
    E.append(key_result_box(
        'WheelFrac.inf_ne_bot  (machine-verified, Lean 4)',
        'If 0 &#8713; S, then &#8734; &#8800; &#8869; in &#8857;<sub>S</sub> A. The '
        'construction is a genuine wheel, not a meadow. (If &#8734; and &#8869; were equal, '
        'the witnessing elements of S would force 0 itself into S, contradicting the '
        'hypothesis.) Also sorry-free and choice-free: [propext, Quot.sound].'))
    E.append(sp(4))

    # ── The Porthole Connection ──────────────────────────────────────────────
    E.append(Paragraph('Why This Belongs in the Zero Paradox', CS['h1']))
    E.append(cbody(
        'The Zero Paradox studies one structural fact about the bottom element &#8869;, '
        'written in several mathematical languages at once: in the 2-adic valuation it is '
        'v&#8322;(0) = &#8734;, and in non-well-founded set theory it is the Quine atom '
        '&#8869; = {&#8869;}. The wheel of fractions is the <b>algebraic</b> face of the '
        'same point. Where ZP-J says "the bottom is where measure runs to infinity," the '
        'wheel says "the bottom is where division by zero lives" - and it shows that this '
        'point is a defined, well-behaved element (&#8734; = /0), distinct - in the standard '
        'case where 0 &#8713; S - from the absorbing &#8869;. Same location, different '
        'vocabulary.'))
    E.append(cbody(
        'One honest limitation. The wheel is built <i>on top of</i> a ring you supply - the '
        'ring structure is an input, not something derived from the Zero Paradox\'s own '
        'axioms. Whether the defining property of the porthole can be <i>derived</i> from '
        'upstream ZP structure, rather than assumed, is an open question flagged in the '
        'Lean source (the bridge typeclass WheelValuationStructure states it, but its key '
        'condition is an assumed axiom). The wheel shows the algebraic face exists and is '
        'consistent; it does not claim to force it into being.'))
    E.append(sp(4))

    # ── What This Is and Isn't ───────────────────────────────────────────────
    E.append(Paragraph('What This Is, and What It Is Not', CS['h1']))
    E.append(remember_box(
        'The wheel of fractions and the theorem that it is a wheel are Carlstr&#246;m\'s, '
        'not new mathematics. What the Zero Paradox adds is a faithful, machine-checked '
        'encoding - readable field by field against Carlstr&#246;m\'s Definition 1.1, with '
        'a verified axiom footprint showing it needs no axiom of choice - placed in the '
        'context of the bottom element &#8869;. The takeaway: division by zero is not an '
        'error to be avoided but a defined element to be understood, and at exactly the '
        'point the rest of the framework already identifies as the bottom.'))
    E.append(sp(6))

    print(f'[build_zpj_wheel_companion] Assembling document ({len(E)} elements)...')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
