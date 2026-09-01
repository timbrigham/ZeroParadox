"""
Zero Paradox — ZP Addendum: The Choice-Free Core
Version 1.9 | August 2026
v1.9: the page-1 overview said Section III shows it "essential rather than INHERITED" while Section III itself says both cases are essential and one of them IS inherited - the same document, opposite framings, and the overview misdescribing the section it cites. Corrected to "essential rather than INCIDENTAL", which is the axis the sentence is actually on. Found by `check_paths.py --claim`, built this session as DC-24's mechanical half; it printed this site and the matching README one on its first real run.
v1.8: PROVENANCE AND NECESSITY ARE INDEPENDENT AXES, and v1.5-v1.7 collapsed them. The text said Section III locates two principles "where the choice is the framework's own and provably essential" - false for the second. `wem_of_fixedPointFree` reduces a principle whose choice IS the framework's own (a bare classical in Category/Lawvere.lean); `em_of_wellOrder_comparable` reduces well-order comparability, whose choice is MATHLIB's, spent in InitialSeg.total - and OrdinalChoiceEssential.lean states that Mathlib's use there is forced. So an INHERITED dependence can be essential, which is a STRONGER result than the one the prose was claiming, and it is why "inherited" never meant "removable". Found by the adversary gate keying on the POSITIVE assertion ("the framework's own") - four earlier rounds all keyed on the universal negative ("only ... Mathlib") and no search for that polarity could reach it.
v1.7: THE v1.6 FIX REACHED THE ENDNOTE AND MISSED THE FRONT MATTER. Section III has named both taboo reductions since v1.5; v1.6 corrected the endnote; the PREAMBLE on page 1 and the Section II opener still said choice appears in "every place ... where the framework builds on Mathlib's libraries" and listed CATEGORY THEORY as one of them - the exact case corrected everywhere else. Both prose gates returned FAIL-BEDROCK, independently, on the two places a skimmer lands FIRST. That is the fourth consecutive version of this document fixing one site of one claim: v1.5 fixed Section III and left the endnote, v1.6 fixed the endnote and left the preamble. Corrected here at all four rendered sites at once. Also struck a claim v1.6 INTRODUCED - that the axiom-free sibling shows the choice is "not forced by the shape of the result" - which is the inversion of what LawvereTaboo section III proves: the cost IS the generality over arbitrary types, and it disappears under [DecidableEq beta].
v1.6: THE ENDNOTE CONTRADICTED SECTION III. Section III has named both taboo reductions since v1.5 - `wem_of_fixedPointFree` and `em_of_wellOrder_comparable`, each choice-free (`[propext, Quot.sound]`), which is the only shape that can establish necessity. The endnote still said choice "appears only where the framework builds on Mathlib's ... libraries, and whether it is necessary there remains open" - both halves false, in the two places a skimmer lands. Measured: `fixedPointFree_of_nontrivial` carries choice from a bare `classical` in framework source (`Category/Lawvere.lean`), not from Mathlib, while its sibling `no_witness_of_fixedPointFree` is axiom-free - so the dependence is not inherited - the `classical` is the framework's own, and per LawvereTaboo section III the cost IS the generality over arbitrary types (it disappears under [DecidableEq beta]). Found by sweeping the CLAIM after both prose gates returned FAIL-BEDROCK on the same universal in README.
v1.5: BEDROCK - Section III asserted THE FRAMEWORK HAS NO PROVEN-NECESSITY CASE ANYWHERE, a universal
negative that is FALSE and was live in the published PDF. Two taboo reductions exist and are named in
CLAUDE.md: em_of_wellOrder_comparable (comparability of well-orders implies excluded middle; prior art
Kraus-Nordvall Forsberg-Xu arXiv:2104.02549 Thm 38(d)) and wem_of_fixedPointFree (the general
fixed-point-free principle implies WEAK excluded middle, on the keystone). Neither was named anywhere
in this document (0 rendered hits for either, 0 for taboo). A 2026-08-01 sweep recorded both universal
negatives as removed from the corpus - it grepped .lean and missed this Python build script, so the
claim survived in RENDERED PUBLIC PROSE. Found 2026-08-03 by the new modal-claim sweep. Section III now
states the reduction/measurement distinction and names both cases. Also: the type-vs-proof point added
(an axiom in a TYPE cannot be removed by any proof; removability there means changing the statement).
Docstring header said 1.3 while VERSION said 1.4 - corrected.
v1.4: FORCING OVERCLAIM RETRACTED. The document described the snap as a forced transition without ever hedging occurrence. T-SNAP fixes the transition's SHAPE; Order/Snap.lean's tsnap_holds_but_nothing_moves proves it holds in a model where nothing moves, so occurrence is a framework commitment. Prose only.
v1.3: rendered Lean-file citations synced to post-reorg basenames (namespace de-scar); docstring changelog above kept as the historical record.
v1.1: WheelFrac.* citation updated to ZPJ_WheelFrac.* (Lean namespace standardization).
v1.0: Initial release. Surfaces the machine-verified fact that the conceptual core of the
      framework is free of the Axiom of Choice. The central theorem T-SNAP (the Binary Snap)
      depends on NO axioms at all; the lattice algebra (ZP-A) and the Quine-atom self-reference
      (ZP-J) are choice-free. Classical.choice appears mostly where the framework builds on Mathlib's
      classically-built analysis/order/computability libraries (the analytic realization layers) - but
      NOT only there: the category-theory face carries the framework's own bare `classical`.
      Anchored on the checkable artifact ZeroParadox/AxiomProfile.lean (a file of #print axioms
      commands). Honest fences throughout: not the whole framework is choice-free; choice is
      mostly inherited from Mathlib in the analytic layers; whether the REMAINING dependence is
      *necessary* there is open (the one layer classified, ZPB_PadicTree, found it mostly
      incidental/routable) - but two taboo reductions already settle it for the principles they
      cover, and the rendered Section III has named them since v1.5.
Framework-wide note; reads after the Foreword.
"""

import os
from zp_utils import *

VERSION = '1.9'
FIRST_RELEASED = 'June 2026'

# ── fix() guard ──
_Paragraph_orig = Paragraph
def Paragraph(text, style):
    return _Paragraph_orig(fix(text) if isinstance(text, str) else text, style)


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP_Choice_Free_Core_Addendum.pdf')
    print(f'[build_zp_choice_free_core] Output: {out_path}')
    doc = make_doc(out_path, 'ZP Addendum: The Choice-Free Core',
                   'ZP Addendum: The Choice-Free Core', 'Version ' + VERSION)
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
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    # ── Preamble (artifact-first) ────────────────────────────────────────────────
    print('[build_zp_choice_free_core] Building preamble...')
    E.append(body(
        'Build the file ZeroParadox/AxiomProfile.lean and read the Lean kernel\'s output. It reports '
        'that the central theorem of this framework &#8212; the Binary Snap, T-SNAP, whose SHAPE is '
        'derived while its occurrence stays a framework commitment, the '
        'transition &#8869; &#8594; &#949;<sub>0</sub> &#8212; depends on <b>no axioms at all</b>: not '
        'the Axiom of Choice, not even propositional extensionality. The lattice algebra (ZP-A) and '
        'the Quine-atom self-reference that is the framework\'s keystone (ZP-J) are likewise '
        'choice-free. This is a machine-checked fact, not a claim of the prose: anyone can run '
        '`lake build ZeroParadox.AxiomProfile` and see it.'))
    E.append(body(
        'Two boundaries are stated up front, because the claim is narrow and exact. <b>The framework '
        'as a whole is not choice-free.</b> Most of its theorems do depend on `Classical.choice`. '
        'Most places it appears are places where the framework builds on Mathlib\'s '
        'classically-built analysis, order, and computability libraries &#8212; the layers that '
        '<i>realize</i> the snap inside standard analytic structures (p-adic topology, Hilbert space, '
        'ordinals), where the dependence is inherited from those libraries. The category-theory face '
        'is the exception: its choice is the framework\'s own bare classical, and Section III shows '
        'it essential rather than <i>incidental</i> &#8212; a separate axis from provenance, and one that Section III also settles for a dependence that IS inherited. It is '
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
        'floor (PowerSet.ps_structural_floor) and the wheel of fractions '
        '(WheelFrac.instWheel, inf_ne_bot). No `Classical.choice`.'))
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
        'Most occurrences are in a layer that realizes the snap floor inside a standard analytic '
        'structure, inheriting choice from the Mathlib library that builds that structure '
        'classically. The category-theory face is not one of them &#8212; see Section III.'))
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
        'enter. For those layers the choice is in the plumbing, not in the claim &#8212; but not '
        'for all of it: Section III locates two principles that are provably essential. Their '
        'provenance differs, and that is the point: one spends the framework\'s own bare classical, '
        'the other spends Mathlib\'s &#8212; and both are essential. Inherited never meant removable.'))
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
        'does not prove <i>necessity</i> &#8212; that no choice-free proof exists. Necessity has to be '
        'shown a different way, by a <i>reduction</i>: derive a recognised constructive taboo from the '
        'principle itself.'))
    E.append(body(
        '<b>Two such reductions do exist here, and they bound what this document claims.</b> '
        '`em_of_wellOrder_comparable` derives excluded middle from comparability of well-orders '
        '(prior art: Kraus, Nordvall Forsberg and Xu, arXiv:2104.02549, Thm 38(d)), and '
        '`wem_of_fixedPointFree` derives <i>weak</i> excluded middle from the general fixed-point-free '
        'principle &#8212; the latter sitting on the keystone rather than on an imported order '
        'instance. Each is a statement about the <b>principle</b>: re-proving it constructively would '
        'decide a taboo, so no choice-free re-proof exists. Neither is an independence result, and '
        'neither is established by a footprint measurement &#8212; which is precisely why the '
        'accidental side needs a measurement and the essential side needs a reduction.'))
    E.append(body(
        'So the analytic-layer dependence may be removable, and that is a different question from '
        'the two cases above. It is also not settled by measuring a proof: where an axiom sits in a '
        '<i>type</i> rather than a proof, no proof of any statement mentioning that type can be clean, '
        'and removability there means changing the statement, not cleaning the argument.'))
    E.append(body(
        'One layer has been classified directly. In the "choice-probe" experiment, the '
        '`Classical.choice` in the 2-adic tree construction (PadicTree) decomposed into three '
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
            'actually asserts. Where choice appears it is mostly the supporting library\'s classical '
            'foundation showing through the realizations rather than an assumption of the argument. '
            'Section III\'s two cases are the exception on a different axis: they are about '
            '<i>necessity</i>, not provenance. One of them is the framework\'s own and one is '
            'Mathlib\'s, and both are essential &#8212; so "inherited" is not a synonym for '
            '"removable", and neither case is absorbed into the generalization.',
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
        '`Classical.choice` appears mostly where the framework builds on Mathlib\'s classical analysis, '
        'order, and computability libraries, where whether it is necessary remains open. It is not '
        'only there, and not everywhere open: the category-theory face carries the framework\'s own '
        'bare classical, and Section III\'s two reductions settle necessity for the principles they '
        'cover. All of this is checkable in ZeroParadox/AxiomProfile.lean.',
        S['endnote']))

    print(f'[build_zp_choice_free_core] Assembling document ({len(E)} elements)...')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
