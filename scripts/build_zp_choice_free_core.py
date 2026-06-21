"""
Zero Paradox — ZP Addendum: The Choice-Free Core
Version 1.1 | June 2026
v1.1: WheelFrac.* citation updated to ZPJ_WheelFrac.* (Lean namespace standardization).
v1.0: Initial release. Surfaces the machine-verified fact that the conceptual core of the
      framework is free of the Axiom of Choice. The central theorem T-SNAP (the Binary Snap)
      depends on NO axioms at all; the lattice algebra (ZP-A) and the Quine-atom self-reference
      (ZP-J) are choice-free. Classical.choice appears only where the framework builds on Mathlib's
      classically-built analysis/order/computability libraries (the analytic realization layers).
      Anchored on the checkable artifact ZeroParadox/AxiomProfile.lean (a file of #print axioms
      commands). Honest fences throughout: not the whole framework is choice-free; choice is
      inherited from Mathlib in the analytic layers; whether it is *necessary* there is open (the
      one layer classified, ZPB_PadicTree, found it mostly incidental/routable).
Framework-wide note; reads after the Foreword.
"""

import os
from zp_utils import *

VERSION = '1.1'

# ── fix() guard ──
_Paragraph_orig = Paragraph
def Paragraph(text, style):
    return _Paragraph_orig(fix(text) if isinstance(text, str) else text, style)


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP_Choice_Free_Core_Addendum.pdf')
    print(f'[build_zp_choice_free_core] Output: {out_path}')
    doc = make_doc(out_path, 'ZP Addendum: The Choice-Free Core',
                   'ZP Addendum: The Choice-Free Core', 'Version ' + VERSION,
                   date_str='June 2026')
    E = []

    # ── Header banner ───────────────────────────────────────────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('ZP Addendum',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    print('[build_zp_choice_free_core] Building title block...')
    E += [
        sp(4),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP Addendum', S['title']),
        Paragraph('The Choice-Free Core', S['subtitle']),
        Paragraph('Version ' + VERSION + ' | June 2026', S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    # ── Preamble (artifact-first) ────────────────────────────────────────────────
    print('[build_zp_choice_free_core] Building preamble...')
    E.append(body(
        'Build the file ZeroParadox/AxiomProfile.lean and read the Lean kernel\'s output. It reports '
        'that the central theorem of this framework &#8212; the Binary Snap, T-SNAP, the forced '
        'transition &#8869; &#8594; &#949;<sub>0</sub> &#8212; depends on <b>no axioms at all</b>: not '
        'the Axiom of Choice, not even propositional extensionality. The lattice algebra (ZP-A) and '
        'the Quine-atom self-reference that is the framework\'s keystone (ZP-J) are likewise '
        'choice-free. This is a machine-checked fact, not a claim of the prose: anyone can run '
        '`lake build ZeroParadox.AxiomProfile` and see it.'))
    E.append(body(
        'Two boundaries are stated up front, because the claim is narrow and exact. <b>The framework '
        'as a whole is not choice-free.</b> Most of its theorems do depend on `Classical.choice`. '
        'But every place it appears is a place where the framework builds on Mathlib\'s '
        'classically-built analysis, order, and computability libraries &#8212; the layers that '
        '<i>realize</i> the snap inside standard analytic structures (p-adic topology, Hilbert space, '
        'ordinals, category theory), where the dependence is inherited from those libraries. It is '
        'not used by the core results above. <b>And dependence is not necessity:</b> that those '
        'realizations <i>use</i> choice as written does not show choice is <i>required</i> there '
        '(Section III).'))
    E.append(hr())

    # ── Section I ─────────────────────────────────────────────────────────────────
    print('[build_zp_choice_free_core] Building Section I...')
    E += [
        Paragraph('Section I: The Choice-Free Core', S['h1']),
        hr(),
    ]
    E.append(body(
        'The Lean kernel\'s `#print axioms` command reports the complete axiom dependency of any '
        'result. Run on the framework\'s central results, it returns the following. "Does not depend '
        'on any axioms" is the strongest possible report &#8212; stronger than "choice-free," since '
        'it uses not even propositional extensionality.'))
    E.append(result_box(
        'Verified axiom-free (does not depend on any axioms)',
        [
            'T-SNAP, the Binary Snap and its derivation (ZP-E):',
            '  t_snap_machine, t_snap_derived, t_snap_join, t_snap_irreversible,',
            '  da1_minimal_path, dp2_execution_distinguishability.',
            'The lattice algebra (ZP-A): bot_le, the order laws, cc1.',
            'The Quine-atom self-reference keystone (ZP-J): bot_is_quine_atom, cc1_derived,',
            '  t_exec, quine_atom_unique.',
        ]
    ))
    E.append(sp(4))
    E.append(body(
        'A second tier of results is choice-free but uses propositional extensionality and quotient '
        'soundness (`[propext, Quot.sound]`), both standard in Lean 4. These include the structural '
        'floor (ZPH_PowerSet.ps_structural_floor) and the wheel of fractions '
        '(ZPJ_WheelFrac.instWheel, inf_ne_bot). No `Classical.choice`.'))
    E.append(sp(6))

    # ── Section II ───────────────────────────────────────────────────────────────
    print('[build_zp_choice_free_core] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: Where Classical.choice Enters', S['h1']),
        hr(),
    ]
    E.append(body(
        'The honest contrast. `Classical.choice` does appear across the framework &#8212; in the '
        'majority of its theorems &#8212; and the same `#print axioms` artifact shows exactly where. '
        'Every occurrence is in a layer that realizes the snap floor inside a standard analytic '
        'structure, and inherits choice from the Mathlib library that builds that structure '
        'classically.'))
    E.append(result_box(
        'Carries Classical.choice (inherited from Mathlib), e.g.',
        [
            'ZP-B c3_irreversible &#8212; p-adic topology (metric / ultrametric library).',
            'ZP-D t4_snap_orthogonal &#8212; Hilbert space (inner-product library).',
            'ZP-H fB_functor / fD_functor / fC_functor &#8212; TopCat / ModuleCat &#8450; /',
            '  the Kleisli category of the probability monad.',
            'and the ordinal (ZP-L/M), information (ZP-C), and computability (ZP-K) layers.',
            'Footprint in each case: [propext, Classical.choice, Quot.sound].',
        ]
    ))
    E.append(sp(4))
    E.append(body(
        'The pattern is clean: the core <i>states</i> the result; the analytic layers <i>realize</i> '
        'it inside the standard frameworks, and that is where the library\'s classical foundations '
        'enter. The choice is in the plumbing, not in the claim.'))
    E.append(sp(6))

    # ── Section III ──────────────────────────────────────────────────────────────
    print('[build_zp_choice_free_core] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: Dependence Is Not Necessity', S['h1']),
        hr(),
    ]
    E.append(body(
        '`#print axioms` proves <i>dependence</i> &#8212; that the proof as written uses an axiom. It '
        'does not prove <i>necessity</i> &#8212; that no choice-free proof exists. The framework has '
        'no proven-necessity case anywhere: it has never shown, by a reversal, that any result '
        '<i>requires</i> choice. So the analytic-layer dependence may be removable.'))
    E.append(body(
        'One layer has been classified directly. In the "choice-probe" experiment, the '
        '`Classical.choice` in the 2-adic tree construction (ZPB_PadicTree) decomposed into three '
        'sources: incidental tactic artifacts (removed, leaving those results choice-free); Mathlib\'s '
        'classically-proved connectivity API (routable by a path-uniqueness reformulation); and '
        '`sInf` on a complete lattice (routable by a redefinition). The verdict for that layer was '
        '"mostly not structurally required." Whether this generalizes &#8212; and whether the snap '
        'geometry forces choice anywhere &#8212; is an open question, tracked for the constructive '
        'validation layer (ONote/NONote, future ZP-N).'))
    E.append(remark_box(
        'Remark &#8212; Why this matters',
        [
            'The Zero Paradox argues that the foundational axioms are not freely chosen but forced by '
            'the structure of the bottom element. It would be a tension if the framework\'s own '
            'central results leaned on the Axiom of Choice &#8212; the canonical free, non-constructive '
            'selection. They do not. T-SNAP is axiom-free; the keystone is choice-free. The '
            '"forced, not chosen" thesis is internally consistent at the level of what the framework '
            'actually asserts. Where choice appears, it is the supporting library\'s classical '
            'foundation showing through the realizations, not an assumption of the argument.',
        ]
    ))
    E.append(sp(6))

    # ── Scope / artifact ─────────────────────────────────────────────────────────
    print('[build_zp_choice_free_core] Building scope section...')
    E += [
        hr(),
        Paragraph('The Artifact', S['h1']),
        hr(),
    ]
    E.append(label_box(
        'Checkable evidence',
        [
            'ZeroParadox/AxiomProfile.lean &#8212; a file of `#print axioms` commands. Section I prints '
            'the choice-free core; Section II prints the analytic-realization results that carry '
            'choice, as an honest contrast. Build with `lake build ZeroParadox.AxiomProfile` and read '
            'the kernel\'s report. The per-theorem map is in the project repository.',
            'Choice-probe (the one-layer classification): branch `choice-probe`; the verdict and the '
            'three decomposed sources are recorded in the project notes.',
        ]
    ))
    E.append(sp(4))
    E.append(label_box(
        'Scope of the claim',
        [
            'The claim is exactly: the framework\'s central results &#8212; T-SNAP, the lattice, the '
            'Quine-atom self-reference &#8212; are choice-free, and T-SNAP is axiom-free. NOT claimed: '
            'that the whole framework is choice-free (it is not), nor that the analytic-layer choice '
            'is removable or necessary (open). The fact surfaced here is the verified one.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph(
        'Endnote: This is a framework-wide note, machine-verified as of June 2026. The central '
        'theorem T-SNAP depends on no axioms; the conceptual core is free of the Axiom of Choice; '
        '`Classical.choice` appears only where the framework builds on Mathlib\'s classical analysis, '
        'order, and computability libraries, and whether it is necessary there remains open. All of '
        'this is checkable in ZeroParadox/AxiomProfile.lean.',
        S['endnote']))

    print(f'[build_zp_choice_free_core] Assembling document ({len(E)} elements)...')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
