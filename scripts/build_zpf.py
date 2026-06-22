"""
Build ZP-F: The Counterexamples (v1.5)
v1.4: Vocabulary fix — "departure from the null state" → "departure from ⊥" in preamble. Palette rebuild.
v1.3: K-16 vocabulary fix — "topological isolation of zero" → "valuative gap at zero
(v_p(0) = +∞)" in §VI body prose.
v1.0: Initial release. Establishes formally that any linearly ordered field —
      notably ℝ and ℚ — is structurally incapable of hosting the Binary Snap.
      General case ([Field F] [LinearOrder F] [IsStrictOrderedRing F]) proved
      first; ℝ given as the canonical instance.
v1.1: Added §VI — philosophical note on why ℝ is the wrong setting: the
      inversion of richness, the Ostrowski forcing argument, and zero as limit
      point versus structural origin.
v1.2: §VI Remark: Dual Limit Condition extended — squeeze as structurally
      necessary (recurrence across ZPL/ZPM); surreal numbers as boundary test
      case; theorem development pathway noted. Vocabulary fix: 'topologically
      isolated' → 'valuatively distinguished' in §VI body.
"""

import os
from zp_utils import *

VERSION = '1.5'
FIRST_RELEASED = 'April 2026'

def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-F_The_Counterexamples.pdf')
    doc = make_doc(out_path, 'ZP-F: The Counterexamples', 'ZP-F', 'Version ' + VERSION)
    E = []

    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-F: The Counterexamples', S['subtitle']),
          Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
          sp(10),
          body('This document is self-contained within ordered field theory. No p-adic '
               'topology, no information theory, and no Hilbert space machinery is required. '
               'All results follow from the axioms of a linearly ordered field alone.'),
          body('<i>Illustrated Companion: A paired ZP-F Illustrated Companion provides '
               'plain-language explanation and motivation for the results here. '
               'Examples and intuitions are kept separate from the formal layers '
               'to distinguish illustrative material from proofs.</i>'),
          sp()]

    # ── I. Purpose and Scope ──────────────────────────────────────────────────
    E.append(Paragraph('I. Purpose and Scope', S['h1']))
    E.append(body(
        'The Zero Paradox framework requires a metric space in which a minimal first '
        'departure from &#8869; is structurally forced — the Binary Snap. '
        'This document establishes the negative result: no linearly ordered field can '
        'serve as that substrate. The real numbers &#8477; are the canonical and most '
        'familiar instance; the theorem applies to any field carrying a compatible '
        'linear order.'))
    E.append(body(
        'The blocking mechanism is elementary: in any such field, for any positive '
        'element &#949;, the element &#949;/2 exists, is positive, and is strictly '
        'smaller. There is no floor. The Binary Snap requires a floor. Therefore '
        'the snap is structurally impossible in any linearly ordered field.'))
    E.append(body(
        'This result contextualises the choice of Q&#8322; in ZP-B. Among all completions '
        'of &#8474;, Ostrowski\'s theorem identifies exactly two kinds: Archimedean completions '
        '(such as &#8477;, where zero is a limit point and density excludes any floor) and '
        'non-Archimedean completions (&#8474;<sub>p</sub>, where zero is valuatively distinguished '
        '(v<sub>p</sub>(0) = +&#8734;) from all nonzero elements). Q&#8322; is the non-Archimedean completion at p&#160;=&#160;2 — '
        'the minimum prime compatible with binary existence (AX-B1). '
        'The valuative gap at zero is not imposed from outside; it follows from the completion.'))
    E.append(sp(4))

    # ── II. The General Result ────────────────────────────────────────────────
    E.append(Paragraph('II. The General Result', S['h1']))
    E.append(body(
        'The following results hold for any type F carrying a field structure, a '
        'linear order, and the IsStrictOrderedRing property — the standard Mathlib '
        'replacement for the deprecated LinearOrderedField typeclass (deprecated '
        'October 2025). All proofs are machine-verified in Lean 4.'))
    E.append(sp(4))

    E.append(label_box('Theorem F-DENSITY', [
        '&#8704; &#949; : F,  0 < &#949;  &#8594;  0 < &#949;/2  &#8743;  &#949;/2 < &#949;',
        'For any positive element &#949; in a linearly ordered field F, the element '
        '&#949;/2 is also positive and strictly smaller than &#949;.',
        'Proof: half_pos gives 0 < &#949;/2; half_lt_self gives &#949;/2 < &#949;. '
        'Both follow from the ordered field axioms. Status: DERIVED. &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Theorem F-NO-MIN', [
        '&#172;&#8707; &#949; : F,  0 < &#949;  &#8743;  &#8704; &#948; : F,  0 < &#948;  &#8594;  &#949; &#8804; &#948;',
        'No linearly ordered field has a minimal positive element.',
        'Proof: Suppose such &#949; exists. By F-DENSITY, 0 < &#949;/2 < &#949;. '
        'Then &#949; &#8804; &#949;/2 (by minimality) contradicts &#949;/2 < &#949;. '
        'Status: DERIVED. &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Theorem F-SNAP-BLOCKED', [
        '&#8704; &#949;&#8320; : F,  0 < &#949;&#8320;  &#8594;  &#8707; &#948; : F,  0 < &#948;  &#8743;  &#948; < &#949;&#8320;',
        'Any candidate first step &#949;&#8320; > 0 from 0 in a linearly ordered field '
        'is blocked: &#949;&#8320;/2 is a smaller positive element, so &#949;&#8320; '
        'cannot be a genuine first step.',
        'Proof: Take &#948; = &#949;&#8320;/2. F-DENSITY gives 0 < &#948; < &#949;&#8320;. '
        'Status: DERIVED. &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Theorem F-SNAP-IMPOSSIBLE', [
        '&#172;&#8707; &#949;&#8320; : F,  0 < &#949;&#8320;  &#8743;  &#172;&#8707; &#948; : F,  0 < &#948;  &#8743;  &#948; < &#949;&#8320;',
        'The Binary Snap cannot occur in any linearly ordered field.',
        'A snap requires a minimal first departure from 0 with nothing below it. '
        'F-SNAP-BLOCKED shows such a floor never exists in a linearly ordered field.',
        'Proof: Direct from F-SNAP-BLOCKED. Status: DERIVED. &#10003;',
    ]))
    E.append(sp(4))

    # ── III. The Real Numbers — Canonical Instance ────────────────────────────
    E.append(Paragraph('III. The Real Numbers — Canonical Instance', S['h1']))
    E.append(body(
        'The following are corollaries of the general results above, instantiated '
        'at F = &#8477;. They are stated explicitly because &#8477; is the most '
        'familiar and intuitive case, and because the ZP-F companion document is '
        'written around &#8477; as its primary example.'))
    E.append(sp(4))

    E.append(label_box('Corollary R-DENSITY', [
        '&#8704; &#949; : &#8477;,  0 < &#949;  &#8594;  0 < &#949;/2  &#8743;  &#949;/2 < &#949;',
        'Density at zero for &#8477;. Follows from F-DENSITY at F = &#8477;. '
        'Status: DERIVED (corollary). &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Corollary R-NO-MIN', [
        '&#172;&#8707; &#949; : &#8477;,  0 < &#949;  &#8743;  &#8704; &#948; : &#8477;,  0 < &#948;  &#8594;  &#949; &#8804; &#948;',
        '&#8477; has no minimal positive element. Follows from F-NO-MIN at F = &#8477;. '
        'Status: DERIVED (corollary). &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Corollary R-SNAP-BLOCKED', [
        '&#8704; &#949;&#8320; : &#8477;,  0 < &#949;&#8320;  &#8594;  &#8707; &#948; : &#8477;,  0 < &#948;  &#8743;  &#948; < &#949;&#8320;',
        'Any candidate first step in &#8477; can be halved. '
        'Follows from F-SNAP-BLOCKED at F = &#8477;. Status: DERIVED (corollary). &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Corollary R-SNAP-IMPOSSIBLE', [
        '&#172;&#8707; &#949;&#8320; : &#8477;,  0 < &#949;&#8320;  &#8743;  &#172;&#8707; &#948; : &#8477;,  0 < &#948;  &#8743;  &#948; < &#949;&#8320;',
        'The Binary Snap cannot occur in &#8477;. '
        'Follows from F-SNAP-IMPOSSIBLE at F = &#8477;. Status: DERIVED (corollary). &#10003;',
    ]))
    E.append(sp(4))

    # ── IV. Axiom Profile ────────────────────────────────────────────────────
    E.append(Paragraph('IV. Axiom Profile', S['h1']))
    E.append(body(
        'All eight results (F-DENSITY, F-NO-MIN, F-SNAP-BLOCKED, F-SNAP-IMPOSSIBLE '
        'and their &#8477; corollaries) verify under #print axioms with the profile: '
        'propext, Classical.choice, Quot.sound. This is the standard profile for '
        'Mathlib field and order results. No snap-specific axioms are introduced.'))
    E.append(sp(4))

    # ── V. Relationship to the Framework ─────────────────────────────────────
    E.append(Paragraph('V. Relationship to the Framework', S['h1']))
    E.append(body(
        'ZP-F is self-contained and does not feed formally into any other layer. '
        'It is the negative complement to ZP-B: where ZP-B establishes that Q&#8322; '
        'can host the snap (via the 2-adic valuation and clopen ball structure), '
        'ZP-F establishes that &#8477; — and any linearly ordered field — cannot.'))
    E.append(body(
        'The dependency order of the framework places ZP-F as independent:'))
    E.append(data_table(
        ['Layer', 'Role', 'Dependency'],
        [['ZP-B', 'p-Adic topology — Q&#8322; hosts the snap', 'ZP-A'],
         ['ZP-F', 'Counterexample — &#8477; and ordered fields cannot host the snap', 'None (self-contained)'],
         ['ZP-G', 'Category theory', 'Self-contained; ZP-E conceptually']],
        [0.8*inch, 3.5*inch, 2.2*inch]
    ))
    E.append(sp(4))

    # ── VI. A Philosophical Note: The Wrong Setting ───────────────────────────
    E.append(Paragraph('VI. A Philosophical Note: The Wrong Setting', S['h1']))
    E.append(body(
        'The real numbers are the most natural and familiar number line precisely because '
        'they fill every gap. Density — the property established in F-DENSITY: for any '
        '&#949; > 0 there exists &#948; with 0 < &#948; < &#949; — is not a deficiency in '
        '&#8477;; it is one of &#8477;\'s defining virtues. The counterexample above shows '
        'that this virtue is exactly what disqualifies &#8477; as a host for the Binary Snap. '
        'The exclusion is not a matter of degree: density follows from the ordered field axioms, '
        'so every linearly ordered field is ruled out by exactly the same argument. '
        'Familiarity here misleads: the setting that feels most natural '
        'for foundational mathematics is precisely the wrong one.'))
    E.append(body(
        'The exclusion of &#8477; is not an isolated fact about one number system. '
        'F-SNAP-IMPOSSIBLE applies to any linearly ordered field. By Ostrowski\'s theorem, '
        'every completion of &#8474; falls into exactly one of two classes: Archimedean '
        '(including &#8477;) or non-Archimedean (the p-adic fields &#8474;<sub>p</sub>). '
        'The theorems of this document eliminate the entire Archimedean class. '
        'What remains is the non-Archimedean class. The framework\'s binary existence '
        'constraint (AX-B1) then selects p&#160;=&#160;2 as the minimum prime. '
        'Q&#8322; is not chosen against &#8477;; it is what remains after &#8477; — '
        'and every Archimedean completion — has been ruled out.'))
    E.append(body(
        'The structural difference that the Ostrowski classification makes precise can be '
        'stated directly. In any Archimedean completion, zero is a limit point: every '
        'neighbourhood of zero contains a smaller positive element. The snap requires zero '
        'to be something different — a structural origin from which the first departure is '
        'forced, with no smaller departure possible. In Q&#8322;, zero carries the infinite '
        '2-adic valuation; it is valuatively distinguished in exactly the sense required. '
        'The snap does not fail in &#8477; by accident. It fails because &#8477; and the '
        'snap require incompatible roles for zero: limit point versus structural origin.'))
    E.append(sp(4))

    E.append(remark_box(
        'Remark: The Dual Limit Condition',
        [
            'The results of §II–§III and ZP-L together admit an informal '
            'structural account of why the snap is domain-specific.',
            'In any dense ordered field, 0 has no nearest neighbour from above: for any '
            '&#949; > 0 there exists &#948; with 0 < &#948; < &#949; (F-DENSITY). Zero is '
            'a topological limit point from above with no minimum positive element. The snap '
            'requires a discrete first step above 0; density forbids it. This is the blocking '
            'condition established in this document.',
            '&#949;&#8320; (the snap threshold, established in ZP-L) is the least fixed '
            'point of &#945; &#8614; &#969;^&#945;: it is not reachable by any finite '
            'iteration of the &#969;^(&#183;) operation, only by the limit of the tower '
            '&#969;, &#969;^&#969;, &#969;^&#969;^&#969;, &#8230; The snap is possible '
            'at &#949;&#8320; precisely because it has no predecessor in the ordinal '
            'hierarchy: no ordinal &#945; satisfies &#945; + 1 = &#949;&#8320;.',
            'Both cases are limit-type conditions: the field case is a topological limit '
            'point with no minimum positive neighbour above 0; the ordinal case is a limit '
            'ordinal (specifically, the least fixed point of &#945; &#8614; &#969;^&#945;) '
            'with no predecessor below &#949;&#8320;. The analogy is structural &#8212; '
            'both describe a boundary approached but not reachable by finite steps on one '
            'side &#8212; but it is not a proved identification. The two structures live in '
            'different mathematical categories.',
            'A domain that can host the snap must satisfy two conditions simultaneously: '
            '(1) the boundary is a genuine limit (no nearest neighbour &#8212; what makes '
            'the threshold non-arbitrary) and (2) the crossing is discrete (a step, not a '
            'continuous transition). Dense ordered fields have condition (1) but density '
            'makes condition (2) impossible. In the non-standard naturals *&#8469; with '
            'the order topology, every element has an immediate predecessor, so there is '
            'no limit point at infinity in the order-topology sense; condition (1) fails '
            'informally. (This *&#8469; observation is informal &#8212; not a proved result '
            'of this document or ZP-L.)',
            'The tower encodings cnfToZp2(towerNONote n) converge to 0 in &#8484;&#8322; '
            'as n &#8594; &#8734; (proved in ZP-L), and &#949;&#8320; is the minimal '
            'snap threshold in the ordinal setting (proved in ZP-L). The structural '
            'identification of these two results &#8212; that &#8484;&#8322;\'s limit at 0 '
            'and the ordinal threshold at &#949;&#8320; reflect the same boundary &#8212; '
            'has a remaining gap: no type bridge between the ordinal and p-adic types '
            'is established in ZP-L (see ZP-L §V, Remaining Gap).',
            'This is an observation, not a proved theorem. The blocking result '
            '(F-SNAP-IMPOSSIBLE) is proved here; the threshold and convergence results '
            'are proved in ZP-L. The claim that both conditions reflect a common structural '
            'property is interpretive &#8212; it does not follow from their conjunction '
            'alone. The *&#8469; example above is informal.',
            'The dual-approach structure recurs across the ZP layers: in ZP-L, '
            '&#949;&#8320; is located from above as the least fixed point of '
            '&#945; &#8614; &#969;^&#945; and from below as the limit of the CNF tower; '
            'in ZP-M, the computability and ordinal fixed points are argued to converge to the '
            'same 2-adic limit. This recurrence is not coincidental. The snap is the point '
            'where a domain\'s own measurement framework exhausts itself; no single framework '
            'can locate it from inside because the framework runs out exactly there. '
            'This suggests a dual approach is required in each case: each framework reaches the '
            'boundary from its own direction, and the snap is the point they agree on. '
            'No general theorem to this effect is established here.',
            'The surreal numbers (No) satisfy both conditions &#8212; non-Archimedean '
            'structure (containing &#949;&#8320; as an ordinal) and genuine limit ordinals '
            '&#8212; and are the natural boundary test case for any duality theorem. Whether '
            'the surreals admit a snap-like result, or whether a third structural condition '
            'is required to exclude them, has not been determined. '
            '(Informal &#8212; not a result of this document.)',
            'Development path toward a formal theorem: prove the two conditions as '
            'independent Lean results (density impossibility established here; limit ordinal '
            'necessity established in ZP-L), then prove they agree on the same structural '
            'point. The surreal case is the critical test of whether two conditions are '
            'jointly sufficient.',
        ]
    ))
    E.append(sp(4))

    # ── VII. Validation Status ────────────────────────────────────────────────
    E.append(Paragraph('VII. Validation Status', S['h1']))
    E.append(data_table(
        ['Component', 'Status / Notes'],
        [['F-DENSITY', 'DERIVED — Lean-verified; general case'],
         ['F-NO-MIN', 'DERIVED — Lean-verified; general case'],
         ['F-SNAP-BLOCKED', 'DERIVED — Lean-verified; general case'],
         ['F-SNAP-IMPOSSIBLE', 'DERIVED — Lean-verified; general case'],
         ['R-DENSITY', 'DERIVED — Corollary of F-DENSITY at F = &#8477;'],
         ['R-NO-MIN', 'DERIVED — Corollary of F-NO-MIN at F = &#8477;'],
         ['R-SNAP-BLOCKED', 'DERIVED — Corollary of F-SNAP-BLOCKED at F = &#8477;'],
         ['R-SNAP-IMPOSSIBLE', 'DERIVED — Corollary of F-SNAP-IMPOSSIBLE at F = &#8477;']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print(f'Built: {out_path}  ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
