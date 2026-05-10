"""
Build ZP-F: The Counterexamples (v1.1)
v1.0: Initial release. Establishes formally that any linearly ordered field —
      notably ℝ and ℚ — is structurally incapable of hosting the Binary Snap.
      General case ([Field F] [LinearOrder F] [IsStrictOrderedRing F]) proved
      first; ℝ given as the canonical instance.
v1.1: Added §VI — philosophical note on why ℝ is the wrong setting: the
      inversion of richness, the Ostrowski forcing argument, and zero as limit
      point versus structural origin.
"""

import os
from zp_utils import *

VERSION = '1.1'

def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-F_The_Counterexamples_v1_1.pdf')
    doc = make_doc(out_path, 'ZP-F: The Counterexamples', 'ZP-F', 'Version ' + VERSION)
    E = []

    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-F: The Counterexamples', S['subtitle']),
          Paragraph('Version ' + VERSION + '  |  May 2026', S['subtitle']),
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
        'departure from the null state is structurally forced — the Binary Snap. '
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
        'non-Archimedean completions (&#8474;&#8346;, where zero is topologically isolated by '
        'the p-adic valuation). Q&#8322; is the non-Archimedean completion at p&#160;=&#160;2 — '
        'the minimum prime compatible with binary existence (AX-B1). '
        'The structural isolation of zero is not imposed from outside; it follows from the completion.'))
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
        'The richer the number line, the more completely it excludes the structural floor '
        'the snap requires. Familiarity here misleads: the setting that feels most natural '
        'for foundational mathematics is precisely the wrong one.'))
    E.append(body(
        'The exclusion of &#8477; is not an isolated fact about one number system. '
        'F-SNAP-IMPOSSIBLE applies to any linearly ordered field. By Ostrowski\'s theorem, '
        'every completion of &#8474; falls into exactly one of two classes: Archimedean '
        '(including &#8477;) or non-Archimedean (the p-adic fields &#8474;&#8346;). '
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
        '2-adic valuation; it is topologically isolated in exactly the sense required. '
        'The snap does not fail in &#8477; by accident. It fails because &#8477; and the '
        'snap require incompatible roles for zero: limit point versus structural origin.'))
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
