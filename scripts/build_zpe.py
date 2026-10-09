"""
Zero Paradox — ZP-E: Bridge Document PDF Builder
Version 3.54 | October 2026
Follows all rules in pdf rendering standards:
  - DejaVu fonts only
  - Checkmark always wrapped in <font name="DV">
  - All table cells are Paragraph objects
  - No unicode subscripts — use sub/super tags
  - US Letter, 1-inch margins, TW = 6.5 inch
"""

import os
from zp_utils import *

VERSION = '3.54'
FIRST_RELEASED = 'April 2026'

# ── Local overrides: ZP-E uses justified body text ────────────────────────────
S['body']    = ParagraphStyle('body',    fontName='DVS',   fontSize=10, leading=14, spaceAfter=6, alignment=4)
S['bodyI']   = ParagraphStyle('bodyI',   fontName='DVS-I', fontSize=10, leading=14, spaceAfter=6, alignment=4)
S['li']      = ParagraphStyle('li',      fontName='DVS',   fontSize=10, leading=14, leftIndent=18, spaceAfter=3, alignment=4)
S['derived'] = ParagraphStyle('derived', fontName='DVS-B', fontSize=10, leading=14, spaceAfter=6, textColor=GREEN_DARK, alignment=4)

bridge_box = remark_box  # SLATE header — ZP-E bridge document style


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-E_Bridge_Document.pdf')
    print(f'[build_zpe] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-E: Bridge Document', 'ZP-E: Bridge Document', 'Version ' + VERSION)
    E   = []

    print('[build_zpe] Building title block...')
    # ── TITLE BLOCK ───────────────────────────────────────────────────────────
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-E: Bridge Document', S['title']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'This document is the cross-framework synthesis layer of the Zero Paradox. It imports from '
        'ZP-A (lattice algebra), ZP-B (p-adic topology), ZP-C (information theory), and ZP-D (Hilbert '
        'space state layer). It provides three formal inserts: DA-1 (Instantiation as Execution), '
        'DA-2 (Instantiation Succession), and '
        'DA-3 (Perspective-Relative Cardinality). AX-1 (Binary Snap Causality) is retired. Its content was split in two: '
        'the shape of the snap is proved, as Theorem T-SNAP, and that the snap occurs is stated separately: it follows from '
        'the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2). '
        'tsnap_holds_but_nothing_moves shows T-SNAP does not carry it. With DA-2, the directed instantiation tree is formally licensed. With DA-3, '
        'cardinality is shown to be position-dependent within the instantiation structure.'))
    E.append(body(
        'Illustrated Companion: A paired ZP-E Illustrated Companion document provides accessible '
        'explanations and visual summaries of the bridge derivations in this document. Readers new '
        'to the framework are encouraged to start with the companion.',
        style='bodyI'))
    E.append(body(
        '<b>A note on framework scope.</b> The four layers (ZP-A through ZP-D) are not claimed to be '
        'the only mathematical domains in which the Zero Paradox structure appears. They are chosen '
        'because they cover the canonical mathematical languages for describing state: algebraic order '
        'structure (ZP-A), topology and metric geometry (ZP-B), information and complexity theory (ZP-C), '
        'and functional/Hilbert space analysis (ZP-D). What is claimed is that each of the four frameworks '
        'addressed here locates a structural limit at a floor of its own carrier, named with its carrier in the next paragraph and proved within that framework '
        'from that framework&#8217;s own premises, design commitments among them (ZP-C&#8217;s identification of c<sub>0</sub> with &#8869; is its CC-2, '
        'and ZP-D rests on its design premise DP-1); reading the four as '
        'one limit is the framework&#8217;s interpretation (MC-1, next paragraph), and these four are not claimed '
        'to be the only possible witnesses.'))
    E.append(body(
        'Each of the four layers finds a structural limit at a floor of its own carrier, and each names it in its own terms; ZP-A&#8217;s floor is the least element of its order, '
        'and in Q<sub>2</sub> the norm value 0 is least on the image of the 2-adic norm in the reals (q2_norm_floor_isLeast), not as an order-bottom of Q<sub>2</sub> itself, and {0} is the intersection of the nested clopen balls (fB_bottom_is_limit): ZP-A identifies &#8869;, the bottom of the ZP-A semilattice, as the global minimum, below which the lattice\'s ordering '
        'relation cannot descend; ZP-B finds the 2-adic valuation undefined (or +&#8734;) at 0 in Q<sub>2</sub>, where '
        'clopen separation is total — 0 and every nonzero element lie in disjoint clopen classes; '
        'ZP-C finds surprisal unbounded above at the limit point 0 &#8712; Q<sub>2</sub> of its binary ball hierarchy, to which the initial configuration c<sub>0</sub> corresponds (L-INF), so no finite '
        'external description can contain it; ZP-D maps the state 0 of its state layer to a basis vector e<sub>0</sub> orthogonal to '
        'every other basis vector (dp1_orthogonality), so the snap is an orthogonal shift (t4_snap_orthogonal); '
        'orthogonality is symmetric and does not make the shift one-way, which comes from ZP-A and ZP-B '
        '(T-SNAP Step 7). '
        'Reading these as one structural limit seen in four mathematical languages is the framework&#8217;s '
        'interpretation, the bottom family (MC-1): membership is proved domain by domain, and an identity across '
        'the layers is retired as ill-typed. ZP-C&#8217;s correspondence places c<sub>0</sub> at the 0 of Q<sub>2</sub>; ZP-M&#8217;s '
        'snapEmbed (&#167; VI) is a different map, sending c<sub>0</sub> to 1 and c<sub>1</sub> to 0 in &#8484;<sub>2</sub>, and the two '
        'are not composed here. DA-1&#8217;s own content is narrower (&#167; IV): given DP-2&#8217;s precondition, '
        'that the configuration reaching P<sub>0</sub> is a running machine&#8217;s current configuration (Sense B, &#167; II), '
        'the machine has moved from c<sub>0</sub> to c<sub>1</sub> by D7 (T-SNAP Step 3), and DP-2 and da1_minimal_path show that the two '
        'configurations are distinct while returning the same output value. That precondition is not derived: it is what the '
        'occurrence commitment asserts.'))
    E.append(hr())

    print('[build_zpe] Building DA-1...')
    # ── FORMAL INSERT DA-1 ────────────────────────────────────────────────────
    E += [
        Paragraph('Formal Insert DA-1: Derived Proposition — Instantiation as Execution', S['h1']),
        Paragraph('<i>DA-1 is a Derived Proposition: instantiation as execution, the first Lean '
                  'formalization of DA-1 (axiom-free, conditional on DP-2, Snap.lean &#167;VI), with '
                  'incompressibility read as self-description (ZP-C D1 + AIT) and CC-2/R3 as motivation for its precondition.</i>',
                  S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap at T-BUF Step 2', S['h2']))
    E.append(body('The T-BUF chain from ZP-C states three results:'))
    E += [
        li('L-RUN: The transition c<sub>0</sub> → c<sub>1</sub> is a nonzero state transition. (ZP-C — Derived)'),
        li('TQ-IH: No program outputs ⊥ without a nonzero intermediate configuration state. (ZP-C — Derived by L-RUN)'),
        li('T-BUF: At P<sub>0</sub>, the Binary Snap &#8869; &#8594; ε<sub>0</sub> is a structural consequence of execution: an executing configuration is non-null, and that state is ε<sub>0</sub> in the semilattice. (ZP-C — Candidate Theorem; its Step 2, that the configuration at P<sub>0</sub> is executing, is the occurrence commitment, below, not a derived step)'),
        sp(4),
    ]
    E.append(body(
        'T-BUF was labelled Candidate because Step 2 asserts that a configuration at P<sub>0</sub> is a '
        'live machine state — that instantiation at P<sub>0</sub> constitutes an execution event, not a static '
        'description. ZP-C L-INF supplies one mathematical premise: &#8869; at P<sub>0</sub> has unbounded '
        'surprisal — no finite external interpreter can hold it as a static description. ZP-A CC-2 '
        'supplies a second, structural basis: &#8869; = {&#8869;} is a self-containing object with no external '
        'interpreter by structure. Neither derives T-BUF Step 2: it is DP-2&#8217;s precondition, and it is what the '
        'occurrence commitment asserts (&#167; IV). DA-1 (&#167; IV below) consumes it and does not supply it: given it, '
        'D7 puts the machine at c<sub>1</sub> (T-SNAP Step 3), and DP-2 and da1_minimal_path show that c<sub>0</sub> and c<sub>1</sub> '
        'are distinct configurations returning the same output value.'))

    E.append(Paragraph('II. The Two Senses of a Configuration at P<sub>0</sub>', S['h2']))
    E += [
        Paragraph(
            fix('Sense A — Descriptive: x exists as a string — a finite syntactic object that has been written '
                'down or specified. The machine it describes has not necessarily been instantiated. P<sub>0</sub> is a '
                'property of the string. The string is inert.'),
            S['li']),
        sp(4),
        Paragraph(
            fix('Sense B — Instantiated: x exists as the current configuration of a running machine. The '
                'machine is executing. P<sub>0</sub> is a property of the live configuration. The configuration is active.'),
            S['li']),
        sp(6),
    ]

    E.append(Paragraph('III. Design Principle DP-2 — Execution Distinguishability', S['h2']))
    E.append(body(
        'The two senses of § II share the same output value (⊥) but differ in machine state. '
        'This separation — output value is not machine state — is made precise by Design Principle DP-2.'))
    E.append(bridge_box(
        'Design Principle DP-2 — Execution Distinguishability',
        [
            'Machine states carry execution history independently of output values. '
            'A machine in state c<sub>1</sub> can output ⊥ (the null value) while being in a configuration '
            'entirely distinct from a machine in state c<sub>0</sub>. The post-execution null and the '
            'pre-execution null are different instances — same output value, different machine state.',
            'Lean formalization (Snap.lean &#167;VI): TrackedOutput separates value : MachinePhase '
            'from state : MachinePhase. preInstantiation = &#10216;c<sub>0</sub>, c<sub>0</sub>&#10217;; '
            'postInstantiation = &#10216;c<sub>0</sub>, c<sub>1</sub>&#10217;. '
            'Theorem dp2_execution_distinguishability proves: '
            'preInstantiation.value = postInstantiation.value (same output) ∧ '
            'preInstantiation.state ≠ postInstantiation.state (distinct machine states). '
            'Proved axiom-free.',
        ]
    ))
    E += [
        sp(4),
        body(
            'Given DP-2, DA-1 is Lean-formalizable at the minimal-path level. '
            'Theorem da1_minimal_path (Snap.lean &#167;VI) establishes four conjuncts: '
            '(1) before and after instantiation, the output value is the same (⊥); '
            '(2) the machine states are distinct (c<sub>0</sub> ≠ c<sub>1</sub>); '
            '(3) the machine was at c<sub>0</sub> before; '
            '(4) the machine is at c<sub>1</sub> after. '
            'Proved axiom-free — no Kolmogorov complexity, no ZF+AFA required. '
            'The "return to null" after instantiation is postInstantiation (output ⊥, state c<sub>1</sub>) — '
            'not preInstantiation (output ⊥, state c<sub>0</sub>). '
            'On the machine-state component, no join from c<sub>1</sub> returns to c<sub>0</sub> (t_snap_irreversible, which holds for the join of every ZP semilattice, MachinePhase among them, '
            'and is not about TrackedOutput records; ZP-B C3 is its topological counterpart).'),
    ]

    E.append(Paragraph('IV. Proposition DA-1', S['h2']))
    E.append(bridge_box(
        'Proposition DA-1 — Instantiation as Execution',
        [
            'Claim: Given its precondition (below), instantiation at the incompressibility threshold '
            'P<sub>0</sub> is an execution event in the sense of L-RUN: one act of instantiation moves the machine from '
            'c<sub>0</sub> to c<sub>1</sub>, with the same output value before and after.',
            'Scope of the claim: it holds given DP-2 and DP-2&#8217;s precondition, that the configuration reaching '
            'P<sub>0</sub> is there in Sense B (&#167; II, a running machine&#8217;s current configuration) and not in '
            'Sense A (an inert string). That precondition is not derived: it is what the occurrence commitment asserts '
            '(instantiation occurs), and Paths 1 to 3 below argue for it. '
            'What follows from it is c<sub>0</sub> &#8594; c<sub>1</sub>: by D7 a running machine has left c<sub>0</sub>, and its first '
            'running configuration is c<sub>1</sub> (T-SNAP Step 3); DP-2 and da1_minimal_path (axiom-free) show that the two '
            'configurations are distinct while returning the same output value.',
            'Formal core (Lean): DP-2 (§III) — TrackedOutput separates output value from machine state. '
            'da1_minimal_path proves that the pre-instantiation configuration (state c<sub>0</sub>) and the post-instantiation '
            'configuration (state c<sub>1</sub>) are distinct while returning the same output value, so the output value cannot '
            'show whether the step was taken. It takes no hypothesis and does not carry that the step is taken '
            '(ZeroParadox/Order/SnapCannotBe.lean &#167; I). The returned ⊥ occupies the bottom role again; reading it as a NEW null rather than the prior c<sub>0</sub> is C-DA2, a modelling commitment. The axiom-free result is the role, not the novelty.',
            'Structural motivation (Paths 1 and 2 below): ZP-A CC-2 (⊥ = {⊥}) is a commitment: ZP-J t_exec_iff proves '
            '⊥ is the only occupant of the Quine-atom role, and that ⊥ of a ZPSemilattice is the AFA set Q = {Q}, its own singleton, is argued (R-AFA). '
            'ZP-A R3 reads off that a self-containing object admits no external interpreter position; that rules out an '
            'external executor, not an inert ⊥. ZP-C L-INF gives ⊥ unbounded surprisal, exceeding the capacity of any '
            'finite interpreter, and the step from there to executing is a bridge principle of its own (Path 2), which the '
            'framework does not adopt and which is not the occurrence commitment. Neither derives the precondition.',
        ]
    ))
    E += [
        sp(4),
        body('The three paths below are not parallel proofs of DA-1. Each argues for DA-1&#8217;s precondition, '
             'which is what the occurrence commitment asserts: that the configuration reaching P<sub>0</sub> is there '
             'in Sense B and not in Sense A, so that, by D7, the machine starting at c<sub>0</sub> (the bottom of '
             'MachinePhase) has fetched its first instruction. None derives it: '
             'Path 1 rules out an external executor, not an inert &#8869;; Path 2 does not derive it: the step from unbounded surprisal to executing is a bridge '
             'principle of its own, which the framework does not adopt and which '
             'is not the occurrence commitment; and Path 3 shows that executing is not derivable from incompressibility. '
             'Given that precondition, the step c<sub>0</sub> &#8594; c<sub>1</sub> is D7&#8217;s (T-SNAP Step 3), and '
             'DP-2 + da1_minimal_path (axiom-free) show the two configurations distinct while returning the same output value.'),
        body('Path 1 — Structural (Self-Execution, ZP-J T-EXEC): Nothing exists outside the null space. '
             '&#8869; is prior to all differentiation — there is no external state, no prior cause, no position '
             'from which something else could execute &#8869;. If &#8869; executes at all, the only possible '
             'executor is &#8869; itself. A thing that executes itself contains itself, and the framework reads this as its own sole member: '
             '&#8869; = {&#8869;}, so &#8869; &#8712; &#8869;. The argument is that this is forced by the impossibility of external '
             'execution, which makes it more than a free choice and less than a theorem. ZP-A R3 states the structural consequence: a self-containing object admits no external '
             'interpreter position. ZP-J T-EXEC proves that whatever fills the Quine-atom role is &#8869;: IsQuineAtom(q) &#8596; q = &#8869;, '
             'proved axiom-free in Lean 4 (ZeroParadox.t_exec_iff). AFA (ZF + AFA) is <i>a</i> consistent '
             'set-theoretic home for this structure, and the commitment is not the <i>adoption of AFA '
             'specifically</i>: it is a set of requirements on the host theory &#8212; that the bottom is a '
             'self-containing Quine atom (&#8869; = {&#8869;}), and that this atom is unique &#8212; of '
             'which AFA is the canonical example. '
             'ZP-A CC-2 (&#8869; = {&#8869;}) is a Forced Metatheoretic Commitment: on a lattice, T-EXEC proves that '
             'whatever fills the Quine-atom role is &#8869; (axiom-free, given the field bot_self_mem); in AFA set theory Q = {Q} is a theorem (Aczel 1988, Example 1.3), and that the occupant of the framework&#8217;s &#8869; role, &#8869; of a ZPSemilattice, is that set Q is the argued metatheoretic step (see Remark R-AFA).'),
        body('Path 2 — Informational (ZP-C L-INF): The surprisal I(n) = n at ball-hierarchy '
             'depth n is unbounded — for any finite M, ∃ depth n with I(n) > M. ⊥ corresponds '
             'to the limit point 0 ∈ Q<sub>2</sub>; its informational content exceeds every finite bound. '
             'Any finite external interpreter can hold only a finite informational bound; ⊥ exceeds every '
             'such bound. '
             'Note: Path 2 is motivational context, not a formal path to the conclusion. The step '
             '"exceeds every finite bound → therefore executing" is a bridge principle of its own, '
             'a missing principle and not a missing proof: the framework does not adopt it, and it is not the occurrence '
             'commitment, and it is not a premise of the Snap. It asks what it means for a mathematical structure to <i>instantiate</i> '
             'rather than merely <i>satisfy</i> conditions — a question no computability library answers. '
             'It is the implementation problem in the philosophy of computation, which owns the question: '
             'Putnam (<i>Representation and Reality</i>, 1988, appendix, pp. 120&#8211;125, as cited by '
             'Chalmers 1996) argued that every '
             'ordinary open system realizes every abstract finite automaton, and Chalmers (Synthese 108, 1996, '
             '309&#8211;333) answered with an account of implementation that requires causal structure. Cited, '
             'not claimed. This document states the question in the state chart, where a configuration is one '
             'fact and its running is a further fact; ZP-K Section III.II states it in two charts, the history '
             'chart reading a complete description of a run as the run, and denies neither.'),
        body('Path 3 — Computational: Incompressibility as Self-Description (ZP-C D1 + standard AIT): '
             'The preceding paths argue that ⊥ admits no external interpreter. This path argues from '
             'incompressibility toward the positive claim (executing). '
             'In the standard Turing model (D7), a machine configuration x is either executing or not executing, '
             'and those two are exhaustive. '
             '(B) Live execution — x is the current configuration of a running machine. '
             '(A) Static description — x is a string specified but not being executed, and some '
             'external program p (|p| &lt; |x|) generates x when run, so x is a description awaiting a '
             'separate execution event by an external generator. '
             '(A) and (B) are not exhaustive: (A) bundles not executing with having a shorter external generator. '
             'At P<sub>0</sub>, read at the length n of c<sub>1</sub> as in Step 1, K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1: c<sub>1</sub> is algorithmically incompressible. '
             'No external program p exists with |p| &lt; |c<sub>1</sub>| such that U(p, n) = c<sub>1</sub>. '
             'State (A) requires such a p, so state (A) is eliminated by the Kolmogorov condition. '
             'That rules out a shorter external generator, not an inert string: an incompressible string '
             'written down and never run has no shorter generator and is not executing. So incompressibility '
             'does not decide executing for configurations in general. '
             'Note: so Path 3 shows that executing is not derivable from incompressibility. What it bears on is one event, not '
             'configurations in general: that the configuration reaching P<sub>0</sub> is there in Sense B (&#167; II) '
             'and not in Sense A. That is the precondition DP-2 takes, and it is what the occurrence commitment asserts '
             '(instantiation occurs), not a further premise. DA-1 does '
             'not supply it; DA-1 consumes it: given it, the step c<sub>0</sub> &#8594; c<sub>1</sub> is D7&#8217;s (T-SNAP Step 3).'),
        body('The formal grounding (DP-2, §III) and the three paths above operate at distinct levels, '
             'not as alternatives to one another. The conditional sits at the '
             'level of machine-state representation: <i>if</i> the instantiation at P<sub>0</sub> is a first '
             'instruction fetch in the sense of D7 (the configuration reaching P<sub>0</sub> is in Sense B), <i>then</i> c<sub>0</sub> → c<sub>1</sub> follows '
             'by D7 itself, and DP-2 + da1_minimal_path (axiom-free, proved by construction) show the two configurations distinct while '
             'returning the same output value. The Lean statement takes no hypothesis; the conditional is in this reading of it. DP-2 is grounded in D7 itself (the standard '
             'computational distinction between before-first-instruction and after-first-instruction states), '
             'which is prior to and independent of DA-1. The three paths above operate one level down: they '
             'argue for why the precondition holds — why the instantiation at P<sub>0</sub> is a first '
             'instruction fetch at all — and none derives it. Path 1 (structural) argues that nothing external to &#8869; can '
             'execute &#8869;, so if &#8869; executes at all, the executor is &#8869; itself. That rules out an '
             'external executor, not an inert &#8869;: in MachinePhase the bottom c<sub>0</sub> is a Quine atom '
             '(da1_closed_concrete), and the sequence that stays at c<sub>0</sub> is a state sequence (Premises of '
             'T-SNAP). The self-executor reading argues for &#8869; = {&#8869;} as '
             'more than a free choice and less than a theorem (ZP-A CC-2, a Forced Metatheoretic Commitment); '
             'ZP-J T-EXEC proves, axiom-free, that whatever fills the Quine-atom role is &#8869;. Path 2 (informational) '
             'provides motivational context — unbounded surprisal as a pointer toward why static holding is '
             'incoherent — but the bridge from unbounded surprisal (L-INF) to execution is not a derived claim: it is a bridge principle of its own, '
             'which the framework does not adopt and which is not the occurrence commitment. Path 3 (AIT) argues that incompressibility eliminates a '
             'shorter external generator; that the configuration reaching P<sub>0</sub> is executing rather '
             'than inert is not derived from incompressibility: it is DP-2&#8217;s precondition, what the occurrence commitment asserts. '
             'Path 1&#8217;s Lean counterpart is da1_closed_concrete (ZP-K), which proves IsQuineAtom(&#8869; : MachinePhase) and nothing '
             'computational; Path 3&#8217;s Lean counterpart is the machinePhaseKleene instance&#8217;s botCode_is_quine field, a KleeneStructure '
             'requirement that constant codes also meet, not a witness of execution and not a second independent proof. The two are '
             'carried together by da1_paths_unified as a conjunction; that they name one structural fact is the framework&#8217;s reading. '
             'Path 2 identifies a missing principle. Path 2 is context.'),
        derived('Status: DERIVED PROPOSITION — primary formal grounding: DP-2 (§III, TrackedOutput construction). '
                'da1_minimal_path proved axiom-free in Lean (Snap.lean &#167;VI): the pre- and post-instantiation configurations, '
                'at c<sub>0</sub> and c<sub>1</sub>, are distinct while returning the same output value; it takes no hypothesis and '
                'does not carry that the step is taken. ✓ '
                'Path 1 (structural, ZP-J T-EXEC + ZP-K): rules out an external executor, not an inert &#8869;. Its Lean counterpart is da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase), proved in Kleene.lean, which proves nothing computational. '
                '(Under MachinePhase\'s selfMem x := x = &#8869;, this reduces to (&#8869; = &#8869;) &#8743; (&#8704; x, x = &#8869; &#8658; x = &#8869;) — structural closure enforced by typeclass design, not a set-theoretic derivation from ZF+AFA. See R-K.0.) '
                'Path 2 (informational, L-INF): UNADOPTED BRIDGE PRINCIPLE — a missing principle, not a missing proof, distinct from the occurrence commitment and not a premise of the Snap; Path 2 does not derive the precondition. '
                'Path 3 (computational, ZP-C D1 + AIT): bears on the precondition and shows that executing is not derivable from incompressibility — incompressibility rules out a shorter external generator, not an inert string; that the configuration reaching P<sub>0</sub> is in Sense B and not Sense A is DP-2&#8217;s precondition, what the occurrence commitment asserts, which DA-1 consumes and does not derive. Its Lean counterpart (ZP-K) is the machinePhaseKleene instance&#8217;s botCode_is_quine field — a KleeneStructure requirement that constant codes also meet, not a witness of execution and not a second independent proof; da1_paths_unified carries it with Path 1 as a conjunction. '
                'CC-1 (S<sub>0</sub> = &#8869;): restated — ZP-J cc1_derived with t_exec_iff makes a Quine-atom start and a &#8869; start the same condition (axiom-free, Lean) — and not forced: on a carrier with a second point a valid sequence starts elsewhere (ZeroParadox/Settheory/OntBridge.lean). '
                'CC-2 (&#8869; = {&#8869;}): ZP-J t_exec_iff proves &#8869; is the only occupant of the Quine-atom role (axiom-free); that &#8869; of a ZPSemilattice is the AFA set Q = {Q} is an argued metatheoretic commitment (see R-AFA). '
                'DP-2 (&#167;III) — explicit. '
                'T-SNAP&#8217;s premises, in its Lean form and in its prose argument, are stated under Premises of T-SNAP (DA-1 insert, &#167; V). '
                'AIT (Kolmogorov complexity) outside Lean scope; the Kleene structure is its in-scope counterpart, carried as a KleeneStructure requirement (botCode_is_quine), not a proof of the AIT claim.'),
    ]

    E.append(Paragraph('V. Theorem T-SNAP — Binary Snap Causality', S['h2']))
    E.append(bridge_box(
        'Theorem T-SNAP — Binary Snap Causality',
        [
            '&#8220;Causality&#8221; in this name refers to the shape of the step, not to its occurrence.',
            'Statement: The Binary Snap ⊥ → ε<sub>0</sub> is a derived consequence of P<sub>0</sub>, L-RUN, TQ-IH, '
            'DA-1, and ZP-A D2, among the results the seven steps below cite. It is not an axiom. '
            'What it rests on differs between its Lean form and its prose argument: see Premises of T-SNAP, directly below.',
        ]
    ))
    E += [
        sp(4),
        body('<b>Premises of T-SNAP, in two readings.</b> Both readings are true, and neither replaces the other. '
             'In Lean, two of the premises, CC-1 and occurrence at the first step, are the hypotheses of t_snap_given, named in (i).'),
        li('(i) <i>Lean form: the shape.</i> t_snap_derived : c&#8320; &#8800; c&#8321; &#8743; c&#8321; &#8800; c&#8320; &#8743; '
           'join c&#8320; c&#8321; = c&#8321; (ZeroParadox/Order/Snap.lean) takes no hypotheses, and &#35;print axioms reports no axioms. '
           'It is a fact about the fixed two-state type MachinePhase, with the initial phase c&#8320; as its bottom element &#8869; and the running phase c&#8321; above it: '
           'the two phases differ, and joining them gives c&#8321;. Nothing is passed to it as an argument; binary existence is '
           'built into the choice of that type, and the start at &#8869; into the statement&#8217;s choice of c&#8320;. It fixes the SHAPE of the transition, not that one occurs: tsnap_holds_but_nothing_moves proves '
           'the same statement in a dynamics where every phase is a fixed point. '
           'Two of the premises as hypotheses: t_snap_given (same file) holds over any join-semilattice with bottom, taking '
           'S&#8320; = &#8869; (hcc1, CC-1) and S&#8321; &#8800; S&#8320; (hocc, occurrence at the first step: the step at index 1 is taken) '
           'and giving the same shape at S&#8320;, S&#8321;. Its two inequalities restate hocc; only the join conjunct is derived, from A4. '
           't_snap_derived&#8217;s statement is its MachinePhase instance at the sequence c&#8320;, c&#8321;, c&#8321;, &#8230;, where hcc1 holds by rfl '
           'and hocc reduces to c&#8321; &#8800; c&#8320;. MachinePhase does not discharge occurrence: the sequence that stays at c&#8320; is a '
           'state sequence in the same type and fails hocc. With no '
           'dynamics given, dropping either hypothesis makes the conclusion fail (examples beside it). hocc forces at least two '
           'points and does not force exactly two; AX-B1&#8217;s discreteness is not in that signature.'),
        li('(ii) <i>Prose argument: the shape, then the occurrence.</i> The seven steps below read that shape as a statement about the '
           'framework&#8217;s own state sequence. That reading uses commitments, among them AX-B1 (binary existence, ZP-B, the framework&#8217;s one '
           'substantive modelling commitment) at Step 4, and CC-1 (S<sub>0</sub> = &#8869;, a ZP-A Conditional Claim) for the start at &#8869; in Steps 4 and 6. '
           'That the transition OCCURS rests further on the occurrence commitment: instantiation occurs, in Sense B (&#167; II), so the configuration '
           'reaching P&#8320; is a running machine&#8217;s current configuration and not an inert string. That is Step 2, and it is DP-2&#8217;s precondition. '
           'DA-1 does not supply Step 2; it consumes it. DA-1 is closed only given DP-2: once DP-2&#8217;s precondition is granted, '
           'c&#8320; &#8594; c&#8321; is D7&#8217;s (Step 3), and DP-2 with da1_minimal_path shows the two configurations distinct while returning '
           'the same output value; &#167; IV&#8217;s three paths argue for that precondition, none deriving it; Path 1 argues through '
           'ZP-A CC-2, itself a commitment. The occurrence commitment and DA-1 together give that the Snap occurs, which is not a theorem. Given CC-1, its first-step form is the hypothesis hocc of t_snap_given '
           '(a sequence that first moves at a later index fails hocc). ZP-C L-INF '
           'supplies unbounded surprisal; the step from there to executing is a bridge principle of its own (&#167; IV, Path 2), '
           'which the framework does not adopt, which is not the occurrence commitment, and which is not a premise of the Snap. '
           'ZP-C D1 makes c&#8321; incompressible, which rules out a shorter external generator and does not make the configuration '
           'reaching P&#8320; executing rather than inert (&#167; IV, Path 3).'),
        sp(4),
        body('Proof:'),
        body('<i>Note on Lean scope: the formal Lean proof of T-SNAP is a single term — '
             '&#10216;l_run, tq_ih, rfl&#10217; — l_run proves c&#8320; &#8800; c&#8321; by decide, tq_ih is its symmetric form, '
             'and rfl closes the join in the MachinePhase semilattice (t_snap_given obtains that conjunct from A4, bot_join). '
             'What follows is the informal motivation for the modelling choices that let that term '
             'be read as a statement about the framework&#8217;s own state sequence.</i>'),
        sp(4),
        li('Step 1 — P<sub>0</sub> identifies the incompressibility threshold. ZP-C &#167; I takes x to be a binary string of length n, so n = |x| and K(x|n)/n = K(x|n)/|x|. ZP-C D1 defines P<sub>0</sub> as the limit of K(x|n)/n as n grows, the algorithmic entropy rate of x, and the threshold is that rate at its maximum, 1. The steps below use the finite-string form ZP-C also uses (&#167; I), not the limit: K(x|n)/|x| = 1 for one configuration string x of length n, so x is algorithmically incompressible at its length. (ZP-C &#167; I, D1)'),
        li('Step 2 — The configuration reaching P<sub>0</sub> is in Sense B, not Sense A (the occurrence commitment): At P<sub>0</sub>, K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1 (Step 1 at x = c<sub>1</sub>) — c<sub>1</sub> is incompressible, so no shorter external generator exists. That rules out a shorter external generator, not an inert string; that the configuration reaching P<sub>0</sub> is a running machine&#8217;s current configuration (Sense B) and not an inert string (Sense A) is what the occurrence commitment asserts, not a derived step. Arguments for it, none deriving it: ⊥ = {&#8869;} (ZP-A CC-2/R3); unbounded surprisal (ZP-C L-INF); DA-1 Path 3. (The occurrence commitment, whose content is DP-2&#8217;s precondition. DA-1, closed given DP-2, consumes this step and does not supply it)'),
        li('Step 3 — Any instantiated execution passes through c<sub>1</sub>. (ZP-C D7 — definitional; c<sub>1</sub> is the first running configuration)'),
        li('Step 4 — c<sub>1</sub> ≠ ⊥. (ZP-C L-RUN — Derived; c<sub>1</sub> has gained execution context not present in c<sub>0</sub> = ⊥; by AX-B1 this is a distinct, nonzero state)'),
        li('Step 5 — No program that executes produces only ⊥ configuration states. (ZP-C TQ-IH — Derived; execution trace τ(p) contains c<sub>1</sub> for any executing program p)'),
        li('Step 6 — In (L, ∨, ⊥), c<sub>1</sub> is an element strictly above ⊥. By ZP-A D2, the transition ⊥ → c<sub>1</sub> is a valid state transition: c<sub>1</sub> = ⊥ ∨ ε<sub>0</sub> for some ε<sub>0</sub> ∈ L with ε<sub>0</sub> > ⊥. This transition is the Binary Snap.'),
        li('Step 7 — The transition is irreversible: algebraically, no join from c<sub>1</sub> returns to ⊥ (t_snap_irreversible, the no-return form of ZP-A R1; that the signature has no subtraction operator makes an inverse inexpressible, which is a different fact); topologically by ZP-B C3 (no continuous return path to 0 in Q<sub>2</sub>). These two grounds are sufficient. Conceptual correspondence: ZP-G AX-G2 (hom(X, 0) = ∅ for X ≠ 0) expresses the same irreversibility in categorical language — ZP-G is downstream of ZP-E and is not a formal dependency of this proof.'),
        sp(4),
        body('Conclusion: The Binary Snap is a derived consequence, given the commitments under Premises of T-SNAP. '
             'AX-1 (Binary Snap Causality) is retired. Its content was split in two: the shape of the snap is proved, '
             'as Theorem T-SNAP, and that the snap occurs is stated separately: it follows from the occurrence commitment '
             '(instantiation occurs) together with DA-1 (closed given DP-2). tsnap_holds_but_nothing_moves shows T-SNAP does not carry it. ✓'),
        derived('Status: DERIVED — Cross-Framework. Premises: in two readings, under Premises of T-SNAP above; the Lean form fixes the shape '
                'with no hypotheses, t_snap_given takes CC-1 and occurrence at the first step as hypotheses, and the prose argument&#8217;s shape and its '
                'occurrence rest on commitments, among them those named there. '
                'Dependencies cited in the steps: ZP-C D1, D7, L-RUN, TQ-IH; ZP-B C3; ZP-A D2, R1; ZP-E DA-1; ZP-J T-EXEC. '
                'CC-1 (S&#8320; = &#8869;): restated — a Quine-atom start and a &#8869; start are one condition (ZP-J cc1_derived, t_exec_iff; axiom-free) — and not forced, since on a carrier with a second point a valid sequence starts elsewhere. '
                'CC-2 (&#8869; = {&#8869;}): ZP-J t_exec_iff proves &#8869; is the only occupant of the Quine-atom role (axiom-free); that &#8869; of a ZPSemilattice is the AFA set Q = {Q} is argued metatheoretically (see R-AFA). '
                'Both remain commitments: CC-1 is a Conditional Claim, expressed through the Quine-atom role and not removed by it; CC-2 is a Forced Metatheoretic Commitment. '
                'Conceptual correspondence only: ZP-G AX-G2 (downstream of ZP-E; not a formal dependency).'),
    ]

    E += [
        sp(6),
        bridge_box(
            'Remark R-ε₀ — On the Symbol Choice for the Snap Displacement',
            [
                '<b>Note: this remark draws an informal structural analogy. No formal embedding of '
                'ZP\'s ε₀ into the ordinal ε₀ is claimed or established here.</b> '
                'The symbol ε₀ in Step 6 names the state the snap reaches from ⊥ (ε₀ = c₁, by A4); which '
                'of its properties are theorems, which the carrier supplies, and which remain commitments '
                'is recorded in ZeroParadox/Order/SnapCannotBe.lean. This symbol is chosen '
                'deliberately to coincide '
                'with ε₀, the proof-theoretic ordinal of Peano Arithmetic.',
                '<b>The ordinal ε₀ (Cantor 1897, Math. Ann. 49, §20, Satz B).</b> In ordinal arithmetic, ε₀ is the smallest fixed '
                'point of the map α → ω<sup>α</sup>: equivalently, ε₀ = sup{ω, ω<sup>ω</sup>, '
                'ω<sup>ω<sup>ω</sup></sup>, ...}. No finite ω-tower reaches it. Gentzen '
                'proved in 1936 that transfinite induction up to ε₀ is sufficient to prove Con(PA). '
                'Necessity — that no smaller ordinal would do — is the other direction, and it rests on '
                'different ground: the provability in PA of transfinite induction at every ordinal '
                'strictly below ε₀, which Gentzen reports as already known, crediting Hilbert-Bernays, '
                'together with G&#246;del\'s second incompleteness theorem, by which PA cannot prove '
                'Con(PA) from within. The '
                'ordinal ε₀ is therefore the minimum threshold at which finite arithmetic exhausts its own '
                'generative capacity.',
                '<b>The structural analogy.</b> ZP\'s ε₀ occupies an analogous position in the state '
                'lattice. At P₀, c₁ satisfies K(c₁|n)/|c₁| = 1, the finite-string form of T-SNAP Step 1: it is algorithmically '
                'incompressible. Just as the '
                'Cantor ε₀ cannot be reached from 0 by any finite ω-tower, ZP\'s ε₀ is reached from ⊥ '
                'by the snap, and no program shorter than c₁ outputs c₁ given its length n. Both name a structurally analogous object: a '
                'witness for a transition that exhausts the finite generative hierarchy below it.',
                '<b>The proof structures are analogous.</b> The proof-theoretic analysis locates the minimum '
                'ordinal up to which PA cannot prove transfinite induction. ZP locates a state '
                'displacement at which no external program can hold ⊥ as a static string — where unbounded '
                'surprisal (ZP-C L-INF) and self-containment (ZP-A CC-2, itself a commitment) together rule out an external '
                'interpreter position, which rules out an external executor, not an inert ⊥. In both cases the exhaustion of finite description is a structural '
                'feature, not a deficiency — and it does not make the snap mandatory '
                '(ZeroParadox/Order/SnapCannotBe.lean § I). That the system actually executes at ε₀ rests '
                'on the occurrence commitment and DA-1, under Premises of T-SNAP: a selection of where the '
                'step is taken, not a necessity.',
                '<b>What is not claimed.</b> ZP does not assert that L is an ordinal structure, or that '
                'ZP\'s ε₀ is literally the Cantor ordinal under a formal embedding into the p-adic/lattice '
                'framework. The analogy is motivational: both ε₀s mark a witness for '
                'incompressibility relative to a finite base. A formal embedding — showing that the Cantor '
                'ε₀ is order-isomorphic to or embeds into the p-adic completion of L at ⊥ — remains an '
                'open question and would constitute a strengthening of this claim.',
            ]
        ),
        sp(4),
        bridge_box(
            'Remark R-AFA — Why Foundation is Ruled Out; Non-Well-Foundedness Forced, AFA Adopted',
            [
                'CC-2 &#8212; the identification of &#8869; with the Quine atom &#8869; = {&#8869;} &#8212; '
                'is a set-theoretic step beyond ZP-A\'s algebra: it is not derived from A1&#8211;A4. What it '
                'entails is nonetheless not arbitrary, and the two halves separate. The membership structure '
                'the framework\'s bottom must have <i>forces</i> a non-well-founded host, which is what rules '
                'ZF + Foundation out. <i>Which</i> non-well-founded axiom to adopt is a further step that the '
                'forcing does not take: ZF + AFA is the host this framework adopts, as the canonical theory '
                'meeting the requirements, not the one theory the bottom selects.',
                '<b>Foundation rules out the bottom (structural).</b> The framework\'s bottom is the Quine '
                'atom &#8869; = {&#8869;}: it is a member of itself, &#8869; &#8712; &#8869;. ZF + Foundation '
                '(the Axiom of Regularity) forbids exactly this — under a well-founded membership relation no '
                'set lies on a membership cycle of any length, so in particular no set is a member of itself. '
                'This is a theorem of ZF + Foundation, not a framework-specific stipulation; it is '
                'machine-checked here as no_quine_atom / no_membership_cycle '
                '(ZeroParadox/Settheory/Wall.lean, footprint [propext, Quot.sound], choice-free). A '
                'Foundation-respecting universe therefore cannot host &#8869; at all.',
                '<b>The framework\'s readings of &#8869; support the premise that &#8869; is circular; the '
                'exclusion itself is a theorem.</b> R3 '
                '(ZP-A) &#8212; &#8869; = {&#8869;} has no describer position external to itself &#8212; and '
                'L-INF (ZP-C) &#8212; the 2-adic surprisal I(n) = n is unbounded, so no finite interpreter '
                'can hold &#8869; &#8212; each describe an object with no external vantage and unbounded '
                'self-referential depth. That is exactly the profile of a non-well-founded, self-membered '
                'set: the two readings motivate why &#8869; must be the circular object Foundation excludes, '
                'rather than serving as independent proofs of the exclusion.',
                '<b>Non-well-foundedness is forced; AFA is the canonical replacement.</b> The membership '
                'structure of &#8869; = {&#8869;} is circular '
                '(&#8869; &#8712; &#8869; &#8712; &#8869; &#8712; &#8230;), so &#8869; can live only in a '
                'non-well-founded '
                'metatheory. <b>That much is forced; the particular axiom is not.</b> Aczel records four '
                'anti-foundation axioms, and AFA, FAFA and SAFA each admit exactly one '
                'Quine atom &#8212; his own term is a <i>reflexive set</i> &#8212; while being pairwise '
                'incompatible (Aczel 1988, Corollary 4.28; Appendix A, p. 108). Supplying exactly one '
                'therefore does not single AFA out, so AFA is '
                '<i>adopted</i> as the canonical witness rather than selected by the membership structure.',
                '<b>What is machine-checked (the requirements framework).</b> The question of which host '
                'theory can admit &#8869; is reduced to the two requirements a host theory must supply '
                '&#8212; <b>(Y)</b> a Quine atom &#8869; = {&#8869;} and <b>(Z)</b> its uniqueness &#8212; '
                'and largely closed in the '
                'framework\'s set-theory layer (the QuineHost development, '
                'ZeroParadox/Settheory/QuineHost.lean). Proved '
                'there: the third property, <b>(X)</b> Foundation-freeness, is not assumed &#8212; it is '
                '<i>forced</i> by (Y) (quineHost_not_wellFounded, '
                'axiom-free); ZF + Foundation is excluded (zfSet_no_quine_bottom &#8212; no set is '
                'self-membered &#8212; not axiom-free: it inherits no_quine_atom\'s footprint '
                '[propext, Quot.sound], choice-free); and the requirements are '
                '<i>realizable</i> &#8212; a concrete one-atom model exhibits them (oneAtom_not_wellFounded, '
                'axiom-free). AFA is the canonical example, exhibited off the framework\'s own '
                'AFAStructure (afaStructure_isQuineHost) &#8212; a definition rather than a theorem about '
                'the set theory, and one every ZP-A lattice supplies trivially (the NO-GO gauge in '
                'ZeroParadox/Settheory/SetTheoryAFA.lean). So the reduction '
                'to requirements is not merely argued: the forcing and the realizability are settled '
                'results. What stays argued is which requirements to demand, below.',
                '<b>Boffa is set aside on a weaker warrant, and the cited half and the checked half are '
                'separate.</b> That '
                'Boffa\'s anti-foundation axiom admits a proper class of Quine atoms rather than one is '
                'a <i>cited</i> fact about that theory, and it reaches that axiom through a weaker one, '
                'in a direction worth stating. Boffa\'s axiom is equivalent to his earlier axiom '
                'BA<sub>1</sub> '
                'together with an extension condition, so it implies BA<sub>1</sub> (Aczel 1988, Exercise '
                '5.14(i) for the equivalence; p. 59, where the axiom is formulated as Boffa\'s strengthening '
                'of BA<sub>1</sub>); and BA<sub>1</sub> on its own already '
                'forces the reflexive sets &#8212; Aczel\'s term for Quine atoms &#8212; to form a '
                'proper class (Aczel 1988, Proposition 5.1). That permissiveness is therefore '
                'inherited from the weaker axiom rather than introduced by the strengthening. This '
                'development formalizes no part of either Boffa axiom. What is machine-checked is the '
                'mechanism behind it &#8212; that '
                'self-membership alone does not force uniqueness: in a two-element toy model where every '
                'element is self-membered, no element is <i>the</i> self-membered one '
                '(boffa_fails_unique, ZeroParadox/Settheory/QuineHost.lean, axiom-free). That is a '
                'counter-model separating the two requirements, and it blocks one direction only &#8212; a '
                'host supplying the Quine atom need not supply its uniqueness. Dropping uniqueness '
                'accordingly leaves a host theory no less consistent; what it leaves standing is the '
                'Quine-atom clause alone, and in that toy model every element satisfies that clause, so '
                'the surviving clause is <i>uninformative</i> as a pinning condition &#8212; every element is a '
                'witness, and none is pinned as the host\'s distinguished bottom. Neither half is an '
                'in-kernel result about Boffa\'s axiom itself.',
                '<b>What remains &#8212; a narrow Forced Metatheoretic Commitment.</b> With the forcing and '
                'realizability proved, one step is not a theorem: that a Quine atom and its uniqueness are '
                'the <i>right</i> two requirements to demand &#8212; the commitment to &#8869; = {&#8869;} '
                'as the minimal option consistent with A4\'s additive-identity role (it has exactly one '
                'member, itself, and introduces no internal differentiation; any extension '
                '&#8869; = {&#8869;, x} with x &#8800; &#8869; would add members carrying their own '
                'membership chains). This is a <b>Forced Metatheoretic Commitment</b> &#8212; stronger than '
                'a free choice, weaker than a theorem &#8212; not a Conditional Claim; the set-membership '
                'face &#8869; &#8712; &#8869; stays metatheoretic, while the occupant of the Quine-atom role '
                'is machine-checked to be &#8869; (t_exec, ZeroParadox/Settheory/SetTheoryAFA.lean, '
                'axiom-free, given the field bot_self_mem). The named falsifier is correspondingly narrow: a differently-motivated '
                'requirement set that hosts &#8869; without demanding a unique Quine atom would reopen this '
                'choice &#8212; it would not touch the forcing or the realizability, which are settled.',
            ]
        ),
        sp(4),
    ]

    E.append(Paragraph('VI. Effect of T-SNAP on Downstream Results', S['h2']))
    E.append(body(
        'Remark R-DA1: AX-1 is retired, and its content was split in two. Results in ZP-E that '
        'previously depended on AX-1 as an axiom now depend on T-SNAP, a derived theorem, for the shape, and, wherever they use that the Snap happens, on the '
        'occurrence commitment (instantiation occurs) together with DA-1. T5 (Iterative Forcing Theorem) depended on AX-1 and is restated below. T4 (Unified Snap '
        'Description) carried AX-1 as an axiom label on the causality component — that label is upgraded '
        'to Derived — T-SNAP for the shape, with occurrence still a commitment. DA-1 is additionally upgraded from Design Principle to Derived '
        'Proposition, closed given DP-2 (da1_minimal_path); ZP-A CC-2 (⊥ = {⊥}), R3 and ZP-C L-INF argue for its precondition, which is what the occurrence commitment asserts, and none derives it. '
        'The intentional axioms of the system are now: AX-B1 (binary existence), '
        'AX-G1 (initial object), AX-G2 (source asymmetry). AX-1 is retired: its shape is Theorem T-SNAP, and the occurrence '
        'commitment is not on this list because it is a commitment, not a named axiom. '
        'Additional structural commitments are carried as typeclass fields: A4 (bot_join, '
        'ZPSemilattice — standard semilattice algebra), AFAStructure.quine_unique and bot_self_mem '
        '(the Quine-atom role), KleeneStructure.botCode_is_quine (computational closure). Like named axioms these are '
        'assumptions, carried as hypotheses by every theorem that uses them; &#35;print axioms does not surface typeclass fields. '
        'Unlike named axioms they can be cheap to meet: every ZP-A lattice supplies AFAStructure trivially, and '
        'KleeneStructure&#8217;s botCode_is_quine is met by a constant code (the computable KleeneStructure '
        'MachinePhase example in ZeroParadox/Computability/Kleene.lean).'))
    E += [
        sp(4),
        bridge_box(
            'T5 (Iterative Forcing Theorem) — restated',
            [
                'T5 (restated). Selection. In the ordinal chart the next rung is the snap re-seeded one step past the current one '
                '(succession_succ), and none lies between two consecutive rungs (ZeroParadox/Ordinal/SnapSuccession.lean &#167; I). '
                'Carried into the two-state lattice by a monotone map &#966; that sends the tower&#8217;s stages to c<sub>0</sub> and '
                '&#949;<sub>0</sub> to c<sub>1</sub>, no ordinal below &#949;<sub>0</sub> is sent to c<sub>1</sub>, and every fixed point '
                'of &#945; &#8614; &#969;<super>&#945;</super> is (snap_unconditional, hfp_from_epsilon_zero). '
                'The two faces of &#949;<sub>0</sub> carry the two directions: as the supremum of the stages, every ordinal below '
                '&#949;<sub>0</sub> lies under one of them, so nothing below fires (fundamentalSeq_cofinal); as the least fixed point of '
                '&#945; &#8614; &#969;<super>&#945;</super> it lies below every other, so every fixed point of &#945; &#8614; &#969;<super>&#945;</super> fires '
                '(hfp_from_epsilon_zero, epsilon0_min_eq_max). The placement at &#949;<sub>0</sub> enters there as the alignment '
                'hypothesis h&#949;<sub>0</sub> (CLAIMS.md OQ-A1): &#966; &#949;<sub>0</sub> = c<sub>1</sub>; '
                'in the &#8484;<sub>2</sub> chart, snapEmbed (&#966; &#949;<sub>0</sub>) = 0, where snapEmbed is ZP-M&#8217;s map sending '
                'c<sub>0</sub> to 1 and c<sub>1</sub> to 0. It is the snap&#8217;s occurrence at &#949;<sub>0</sub>, '
                'taken as a hypothesis: of the infinitely many admissible firing points that monotonicity and tower alignment '
                '(every tower stage sent to c<sub>0</sub>) leave open, h&#949;<sub>0</sub> selects the least, and so fixes '
                '&#966; uniquely (ZeroParadox/Ordinal/Incompleteness.lean &#167; II). '
                'Whether Classical.choice is forced by the metric collapse is a separate open question '
                '(ZeroParadox/Ordinal/SyntacticCollapse.md). The rungs are the iterative bottoms; '
                'none of them is &#8869; (epsilon0_ne_bot; for every rung, Ordinal.epsilon_pos). On an arbitrary lattice no step is '
                'selected: 0, 2, 4, &#8230; on the natural numbers satisfies A1&#8211;A4 and AX-B1.',
                'Iteration. No step is guaranteed. A state sequence moves only upward (T3) and never returns (R1, t_snap_irreversible). '
                'Where the next increment is already absorbed (S<sub>n</sub> &#8744; &#945;<sub>n</sub> = S<sub>n</sub>), the state stays '
                'the same, which T-SNAP permits (tsnap_holds_but_nothing_moves); different runs need not reach the same height. If from '
                'some step x on every new increment is already absorbed, then S<sub>x</sub> is the supremum of the run: the value that run '
                'reaches in the limit. Short of a top, reaching it cannot be confirmed at any finite step; a run that reaches a top state '
                '(c<sub>1</sub> on the two-state carrier) is known there to stay.',
                'Reading: &#949;<sub>0</sub> is both at once for the ordinal tower: the least fixed point of &#945; &#8614; '
                '&#969;<super>&#945;</super> and the supremum of its stages (epsilon0_min_eq_max).',
                'The handle T5 is kept. &#8220;Forcing&#8221; names the shape of each step taken, not that any step is taken.',
            ]
        ),
    ]

    print('[build_zpe] Building DA-2...')
    # ── FORMAL INSERT DA-2 ────────────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Formal Insert DA-2: Instantiation Succession — The Multiple-&#8869; Result', S['h1']),
        Paragraph('<i>Formally licenses the directed instantiation tree</i>', S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-2 Closes', S['h2']))
    E.append(body('Given the premises stated under Premises of T-SNAP (DA-1 insert, &#167; V), DA-1 and T-SNAP give the Binary Snap on reaching P<sub>0</sub> '
                  'within an instantiation. Three questions remain open after DA-1:'))
    E += [
        li('CC-1 (ZP-A) posits S<sub>0</sub> = ⊥ — not derivable from A1–A4 alone (ZP-J restates it as '
           'an equivalence with starting at a Quine atom, cc1_derived and t_exec_iff, and does not force it). This leaves open whether ⊥ is unique across all instantiations or whether '
           'each instantiation carries its own ⊥.'),
        li('ZP-B R1 distinguishes universal structure from universe-contingent parameters. ε<sub>0</sub> is '
           'contingent per instantiation. Whether ⊥ is similarly contingent is not addressed in ZP-A through ZP-D.'),
        li('<b>Occurrence fence.</b> T-SNAP fixes the SHAPE of each step. It does not establish that any step is taken: tsnap_holds_but_nothing_moves exhibits a model in which T-SNAP holds and nothing moves. Every "fires" below narrates the commitment that instantiation occurs, not a consequence of the theorem.'),
        li('T-SNAP fires wherever P<sub>0</sub> conditions are met. If the terminal state of instantiation I<sub>n</sub> '
           'satisfies P<sub>0</sub> conditions, T-SNAP should apply — but this requires formally connecting that '
           'terminal state to a ⊥ role-occupant, read as a new ⊥ under C-DA2. DA-2 provides this connection.'),
        sp(4),
    ]

    E.append(Paragraph('II. Why ZP-B C3 is Not Violated', S['h2']))
    E += [
        body('C3 prohibits a continuous path from x ≠ 0 back to the same 0 in Q<sub>2</sub>. DA-2 does not require a '
             'return path. The irreversibility of C3 is preserved within each instantiation. What crosses the '
             'instantiation boundary is not a path in Q<sub>2</sub> — it is the generation of a new Q<sub>2</sub> with its own '
             'metric, its own ⊥, its own ε<sub>0</sub>. C3 quantifies only over paths within a single topological space '
             'and has nothing to say about the boundary between spaces.'),
        body('More precisely: C3 rules out a continuous return to 0 WITHIN one Q<sub>2</sub>. It does not '
             'follow that a recurrence of ⊥ must be a structurally distinct ⊥ — that step needs the '
             'separateness of the spaces, which is a modelling commitment (C-DA2) and not something the '
             'topology supplies. The topology does not enforce novelty; it is silent on it, and in the '
             '2-adic chart the arc reapproaches the same 0 (snap_arc_z2_loop).'),
    ]

    E.append(Paragraph('III. Definitional Alignment DA-2 — Instantiation Succession', S['h2']))
    E.append(bridge_box(
        'Definitional Alignment DA-2 — Instantiation Succession',
        [
            'Claim: A state S in instantiation I<sub>n</sub> satisfies the structural role of ⊥ for instantiation '
            'I<sub>n+1</sub> if and only if it satisfies A4 relative to all subsequent joins in I<sub>n+1</sub>:',
            'S ∨ x = x    for all x in the semilattice of I<sub>n+1</sub>.',
        ]
    ))
    E += [
        sp(4),
        body('Grounding: A4 is the load-bearing axiom of ZP-A — it defines ⊥ as the additive identity under '
             '∨, the element that contributes nothing to any join and is therefore present in everything '
             'above it. DA-2 does not redefine ⊥. It clarifies that the CC-1 identity condition (S<sub>0</sub> = ⊥) can be '
             'satisfied by any state meeting A4\'s algebraic conditions — not only by a cosmologically '
             'primitive ⊥. The identity condition is structural, not historical: what matters is the '
             'algebraic role a state plays in the subsequent semilattice, not where it came from.'),
        body('The terminal state of I<sub>n</sub> arrives at I<sub>n+1</sub> carrying the accumulated join of everything in I<sub>n</sub>\'s '
             'sequence. It is structurally ⊥ to I<sub>n+1</sub> — contributing nothing to subsequent joins — while '
             'being informationally rich relative to I<sub>n</sub>. This is the Zero Paradox instantiated at the '
             'inter-instantiation level: the terminal state is simultaneously a terminus and a foundation.'),
        derived('Status: DEFINITIONAL ALIGNMENT — no new axiom introduced. DA-2 is a clarification of '
                'the scope of CC-1 and A4. ✓'),
    ]

    E.append(Paragraph('IV. Conditional Claim C-DA2 — Novelty of Successive ⊥', S['h2']))
    E.append(bridge_box(
        'Conditional Claim C-DA2 — Novelty of Successive ⊥ (a modelling commitment)',
        [
            'Commitment: each instantiation carries its OWN topological space, so the ⊥ of '
            'I<sub>n+1</sub> is not an element of the Q<sub>2</sub> of I<sub>n</sub>. GIVEN that, no two '
            'instantiations share a ⊥, and succession is a chain (or tree) rather than a cycle.',
            'Status: CONDITIONAL, not derived. The commitment above is the separateness of the '
            'spaces; it is assumed, not obtained from C3. Formerly labelled a Corollary and marked '
            'derived — retracted, see the note below. The handle C-DA2 is unchanged.',
            'What IS proved: that anything occupying the bottom role IS the bottom of its own '
            'lattice (t_iz_limit_is_new_null). That is an identity with the bottom already '
            'present, not the production of a second one.',
        ]
    ))
    E += [
        sp(4),
        body('Why this is NOT a proof, stated plainly because it was published as one. The step '
             '"the ⊥ of I<sub>n+1</sub> is an element of a distinct topological space" is the CONCLUSION, '
             'not a consequence of C3. C3 quantifies over paths WITHIN a single space — it says no continuous '
             'path runs from any x ≠ 0 back to 0 inside one Q<sub>2</sub> — and has nothing to say about '
             'whether the next instantiation\'s space is a different one. Assuming separateness and then '
             'deriving distinctness from it is circular. DA-2 likewise fixes identity conditions WITHIN an '
             'instantiation; it does not compare across two.'),
        body('And the corpus measures against it where the question is concrete: in the 2-adic realization '
             'the arc returns to the SAME zero. snap_arc_z2_loop proves the tower&#8217;s 2-adic image starts at 0 '
             '(stage 0), that stage n is ≠ 0 for every n ≥ 1, and that it converges back to 0; tower_image_loops_to_seed states the '
             'limit IS the seed value. So in that chart novelty does not merely lack a proof — it fails. '
             'C-DA2 stands as a modelling commitment about instantiations, and must not be cited as derived, '
             'nor supported by T-IZ or by t_iz_limit_is_new_null.'),
    ]

    E.append(Paragraph('V. The Directed Instantiation Tree', S['h2']))
    E.append(body('With DA-2 and C-DA2 in place, the global structure of instantiations is a forward-directed '
                  'tree with no back edges:'))
    E += [
        li('Each node in the tree is a ⊥ — the bottom element of one instantiation and the foundation of all '
           'successor instantiations branching from it.'),
        li('Each edge within an instantiation is a step in a monotone state sequence (ZP-A T3). Edges are irreversible (ZP-B C3).'),
        li('Branching at each node: every distinct outbound vector from the terminal state of I<sub>n</sub> is a '
           'valid ε<sub>0</sub> for a distinct I<sub>n+1</sub>. T-SNAP does not select among branches. Because ⊥ = {⊥} '
           '(ZP-A CC-2) is the single self-containing ⊥ with no internal differentiation, every '
           'ε<sub>0</sub> that represents a first differentiation in any direction is a valid outcome. '
           'The work here is done by the undifferentiated ⊥ of CC-2, not by T-SNAP: given that '
           'instantiation occurs, no direction is privileged, so the structure branches rather than '
           'threading a line. T-SNAP fixes the shape of each step; it does not supply the occurrence.'),
        li('No back edges: C-DA2 COMMITS to no instantiation reaching the ⊥ of any ancestor. This is the commitment, not a theorem - in the 2-adic chart the arc returns to the same 0 (snap_arc_z2_loop).'),
        sp(4),
    ]
    E.append(body(
        'Remark R-DA2: T-SNAP fires wherever P<sub>0</sub> conditions are met. DA-2 establishes that the terminal '
        'state of I<sub>n</sub> satisfies those conditions for I<sub>n+1</sub>. T-SNAP therefore applies across instantiation '
        'boundaries without modification. No new axiom is required. The multiverse is not the claim that '
        'T-SNAP fires in all directions simultaneously: it is the claim that ⊥ = {⊥} (ZP-A CC-2) has no '
        'internal differentiation and therefore no preferred direction for ε<sub>0</sub>. The multiverse of '
        'instantiations is the full set of all minimal differentiations available from the single '
        'self-containing ⊥ — a structural consequence of CC-2 + T-SNAP + DA-2 jointly.'))


    E.append(Paragraph('VI. The Zero Paradox Iterated', S['h2']))
    E.append(body('The paradox of ⊥ — simultaneously contributing nothing and being present in everything — '
                  'propagates structurally at every branching node of the tree. Each node is:'))
    E += [
        li('Nothing to its successor instantiations: it acts as additive identity under ∨, contributing nothing to any subsequent join.'),
        li('Everything to its successor instantiations: every state in I<sub>n+1</sub> satisfies ⊥<sub>n+1</sub> ≤ S, so the node underlies everything that follows.'),
        sp(4),
    ]
    E += [
        body('The tree is the geometric shape of the Zero Paradox iterated across instantiations. The '
             'single-instantiation linear sequence was always a cross-section of a structure with this shape.'),
        body('The complete picture: The Zero Paradox describes a forward-directed infinite tree where '
             '⊥<sub>1</sub> → ... → S<sub>terminal</sub><sup>1</sup> ≡ ⊥<sub>2</sub> → ..., where ≡ means structurally satisfies the role of, '
             'not is identical to. Each arrow within an instantiation is monotone and irreversible. Each ≡ '
             'crossing is not a path — it is a new instantiation of the universal structure.'),
    ]

    E.append(Paragraph('VII. Implications Within the Framework', S['h2']))
    E += [
        body('<b>Structural Implication: Branching Tree Structure.</b> T-SNAP fixes the SHAPE of the Binary Snap — '
             'that if ⊥ transitions it goes to some ε₀ > ⊥, and that the step is one-way. It does not '
             'establish that the transition is taken: that the Snap occurs follows from the occurrence commitment (instantiation occurs) '
             'together with DA-1 (closed given DP-2), and the NO-GO '
             'gauge tsnap_holds_but_nothing_moves exhibits a model in which T-SNAP holds and nothing moves. '
             'DA-2 establishes that any terminal state satisfying P₀ '
             'conditions acts as ⊥ for a successor instantiation, generating a forward-directed branching '
             'tree. The branching comes from CC-2\'s undifferentiated ⊥ and the succession from DA-2, '
             'both conditional on instantiation occurring. Note: T-SNAP alone does '
             'not establish that it fires on all outbound vectors simultaneously — that universality is the '
             'scope of DA-2, not a direct consequence of the snap theorem itself.'),
        body('<b>Monotonicity and Path Irrecoverability.</b> Within an instantiation, state sequences are monotone — no state '
             'can be decreased (ZP-A R1). Every state change is a join operation: S<sub>n</sub> ∨ α for some increment α. '
             'The algebra constrains only that the sequence be monotone, not which monotone path is '
             'taken. A join either leaves the state unchanged (when the increment lies at or below the state) or moves it '
             'strictly up, and no join returns it below (t_snap_irreversible). What the resulting position records '
             'is stated under Causal structure, below.'),
        body('<b>Ordinal Direction of State Sequences.</b> What is defined is that every state change is a join '
             '(a state sequence, ZP-A); what is derived from that is the directional asymmetry: each state lies at or below '
             'its successor (ZP-A T3, state_sequence_monotone) and no join returns a state below it (t_snap_irreversible). '
             'Irreversibility is also C3 applied within an instantiation, topologically.'),
        body('<b>Causal structure.</b> The start and the history together determine the position: S<sub>n+1</sub> = '
             'S<sub>n</sub> ∨ α<sub>n</sub>, and ∨ is an operation, so the start S<sub>0</sub> and the increments fix '
             'every state. The position does not determine the history. ∨ is associative, commutative and '
             'idempotent (ZP-A A1&#8211;A3). Associativity makes S<sub>n</sub> the single join of S<sub>0</sub> with &#945;<sub>0</sub>, &#8230;, '
             '&#945;<sub>n&#8722;1</sub>, and the position records only that join. Commutativity and idempotence make the order of the '
             'increments and how often each arrived unrecoverable from it, and the join does not determine which '
             'increments arrived (only that each lies at or below it). An increment already at or below the state leaves no '
             'trace (a step changes nothing exactly when its increment is at or below the state: the example after '
             'state_sequence_monotone, ZeroParadox/Order/Lattice.lean). Distinct histories reaching the same element '
             'are indistinguishable in L. No effect without the join that produced it.'),
    ]

    print('[build_zpe] Building DA-3...')
    # ── FORMAL INSERT DA-3 ────────────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Formal Insert DA-3: Perspective-Relative Cardinality', S['h1']),
        Paragraph('<i>Cardinality as position-dependent measurement within the instantiation structure</i>', S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-3 Closes', S['h2']))
    E.append(body(
        'DA-2 establishes that instantiations form a directed tree and that branching at each ⊥ node '
        'produces multiple successor instantiations. This raises a question about the cardinality of '
        'branching: is the fan at each node countably or uncountably infinite? The answer, which DA-3 '
        'formalises, is that this question is perspective-dependent — and DA-3 further conjectures '
        '(Claim DA-3-C1, deferred to OQ-E2) that this perspective-dependence is the same structural feature '
        'underlying the major cardinality anomalies of classical set theory.'))

    E.append(Paragraph('II. Perspective-Dependence of Branching Cardinality', S['h2']))
    E.append(body(
        'From within instantiation I<sub>n</sub>, an observer occupies exactly one branch of I<sub>n+1</sub>. That the '
        'other branches of I<sub>n+1</sub> are not accessible from it is C-DA2&#8217;s separateness commitment, not C3: '
        'C3 is silent on the boundary between spaces (DA-2 &#167; II). Nor is it monotonicity, which forbids descending '
        'to a sibling&#8217;s starting state, while within one lattice any two states have a join above both, so a '
        'monotone sequence up one branch can reach states above another branch&#8217;s starting state. '
        'From inside, the branching factor is always 1: the observer sees one branch. From outside — '
        'from a meta-level view of the tree — the branching factor is the full fan of accessible outbound vectors.'))
    E.append(bridge_box(
        'Definition DA-3-D1 — Accessible Cardinality',
        [
            'The accessible cardinality of a position p in semilattice L is the cardinality of the set of '
            'states reachable from p by monotone sequences within the instantiation containing p.',
        ]
    ))
    E += [
        sp(4),
        body('The accessible cardinality from p is determined entirely by the structure of L above p. It is not '
             'an intrinsic property of a collection — it is a property of the relationship between a position '
             'and the states reachable from it. No position within any instantiation can access all '
             'cardinalities simultaneously. The meta-level view, which sees the full branching fan, is not a '
             'position any element of any instantiation can occupy.'),
        body('Remark R-DA3-1: To observe the full branching fan, one would need to occupy a position '
             'outside all instantiations. That position would itself be a state in some semilattice, subject to '
             'the same rules. The meta-view is either another instantiation (in which case the tree has no '
             'privileged outside view) or ⊥ itself (in which case ⊥ is the only position from which '
             'the full structure is visible — the state that contributes nothing and is present in everything). '
             'The Zero Paradox\'s name is more precise than it first appeared.'),
    ]

    E.append(Paragraph('III. The Cardinality Hierarchy as Perspective-Relative', S['h2']))
    E.append(body(
        'Cantor\'s theorem establishes that for any set S, |P(S)| > |S|, generating the hierarchy '
        'ℵ<sub>0</sub> &lt; 2<sup>ℵ<sub>0</sub></sup> &lt; 2<sup>2<sup>ℵ<sub>0</sub></sup></sup> &lt; ... '
        'DA-3 reframes this hierarchy not as a fixed ladder that mathematics climbs, but as a '
        'perspective-relative description of the branching structure of the instantiation tree, as seen '
        'from within different positions.'))
    E.append(bridge_box(
        'Claim DA-3-C1 — Perspective-Relative Absolute Cardinality',
        [
            'The appearance of absolute cardinality — cardinality as an intrinsic property independent of '
            'measuring position — is an artifact of treating the semilattice as having a view from outside. '
            'DA-2 and C-DA2 jointly prohibit such a view from within any instantiation.',
        ]
    ))
    E += [
        sp(4),
        body('The candidate claim (DA-3-C1) is that accessible cardinality from within any instantiation '
             'cannot replicate the view from outside. Whether specific independence results in classical '
             'set theory are formal expressions of this perspective-dependence is the conjecture that '
             'OQ-E2 is tasked with investigating.'),
        derived('Status: DEFINITIONAL ALIGNMENT + CANDIDATE CLAIM. DA-3-D1 and R-DA3-1 are '
                'definitional. DA-3-C1 is a candidate claim: structurally motivated within the framework; '
                'formal derivation of the connection between accessible cardinality and specific '
                'set-theoretic independence results is deferred to OQ-E2.'),
    ]

    print('[build_zpe] Building registers...')
    # ── UPDATED OPEN ITEMS REGISTER ───────────────────────────────────────────
    E += [hr(), Paragraph('Updated Open Items Register', S['h1'])]

    oq_rows = [
        ['AX-1: Binary Snap Causality',
         'RETIRED — shape proved as T-SNAP; the snap occurs given the occurrence commitment and DA-1',
         'Its content was split in two: the shape of the Snap is proved, as Theorem T-SNAP (from L-RUN, TQ-IH and the bottom law, with no Lean axioms), '
         'and that the Snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2). '
         'Premises under Premises of T-SNAP (DA-1 insert, &#167; V); given CC-1, the first-step form of the Snap occurring is the hypothesis hocc of t_snap_given.'],
        ['DA-1: Derived Proposition (DP-2 formal grounding)',
         'CLOSED given DP-2 — DP-2 (formal core); CC-2 + L-INF + AIT argue for the precondition, none deriving it',
         'Primary formal grounding: DP-2 (TrackedOutput, Snap.lean &#167;VI) — da1_minimal_path proved '
         'axiom-free. Given the precondition, the machine moves from c<sub>0</sub> to c<sub>1</sub> by D7 (T-SNAP Step 3); da1_minimal_path shows '
         'the two configurations return the same output value, so the output value cannot show whether execution occurred. '
         'Arguments for the precondition, which is what the occurrence commitment asserts, none deriving it: ZP-A CC-2 + R3 (structural); ZP-C L-INF (informational); AIT incompressibility (Path 3).'],
        ['DA-2: Instantiation Succession',
         'CLOSED — Definitional',
         'Terminal state of I<sub>n</sub> satisfies A4 role of ⊥ for I<sub>n+1</sub>. C-DA2 COMMITS to the novelty of each ⊥; it does not establish it.'],
        ['DA-3: Perspective-Relative Cardinality',
         'CLOSED (definitional) / CANDIDATE (DA-3-C1)',
         'DA-3-D1 establishes accessible cardinality is position-dependent within the instantiation structure. '
         'DA-3-C1 (candidate): no position within an instantiation can replicate the outside view. '
         'Whether this connects formally to specific set-theoretic independence results is deferred to OQ-E2.'],
        ['OQ-A1: Increment selection',
         'OQ-A1b CLOSED by A1&#8211;A4; OQ-A1a: no reason to restrict to join-irreducibles (well-founded carriers); placement in the ordinal tower, for a monotone map sending the tower&#8217;s stages to c<sub>0</sub>, conditional on the alignment hypothesis h&#949;<sub>0</sub> (&#949;<sub>0</sub> sent to c<sub>1</sub>)',
         'T5 (Iterative Forcing Theorem), restated in DA-1 insert &#167; VI. No step is guaranteed. On an arbitrary lattice no step is '
         'selected: 0, 2, 4, &#8230; on the natural numbers satisfies A1&#8211;A4 and AX-B1.'],
        ['OQ-B1: p = 2',
         'CLOSED — ZP-B T0',
         'Derived from AX-B1 and MP-1.'],
        ['OQ-C1: Non-conservatism of DF',
         'CLOSED — ZP-C T2',
         'Infinite sequence divergence proven. No postulates remain.'],
        ['S1: Distribution stipulation',
         'CLOSED — ZP-C T1',
         'Derived from AX-B1 and RP-1.'],
        ['OQ-E1: Sequence vs. tree',
         'CLOSED given the occurrence commitment — DA-2',
         'The structure is a forward-directed tree, not a linear sequence. Given that instantiation occurs — the '
         'occurrence commitment, not a consequence of T-SNAP — DA-2 supplies the succession and the '
         'branching follows. '
         'Countable vs. uncountable branching is perspective-dependent (DA-3).'],
        ['OQ-E2: Cardinality-semilattice correspondence',
         'OPEN',
         'Do specific semilattice structures correspond to specific cardinality regimes? Can the framework '
         'make predictions about which instantiations satisfy CH and which do not?'],
        ['Remaining axioms',
         'INTENTIONAL — AX-B1, AX-G1, AX-G2 (named); A4, quine_unique, bot_self_mem, botCode_is_quine (typeclass fields)',
         'Named commitments: AX-B1 (binary existence), AX-G1 (initial object), AX-G2 (source asymmetry). '
         'Structural commitments as typeclass fields: A4/bot_join (ZPSemilattice), '
         'AFAStructure.quine_unique and bot_self_mem (the Quine-atom role, which every ZP-A lattice supplies trivially), '
         'KleeneStructure.botCode_is_quine (computational closure, which a constant code meets). '
         'Typeclass fields are assumptions carried as hypotheses by the theorems that use them; &#35;print axioms does not surface them. Further commitments are not axioms, among them CC-1 (S<sub>0</sub> = &#8869;), a ZP-A Conditional Claim; T-SNAP&#8217;s are stated under Premises of T-SNAP (DA-1 insert, &#167; V).'],
        ['Temperature T in BA-1',
         'PARAMETER — intentional',
         'Universe-contingent. Physical predictions explicitly conditional on instantiation-specific T.'],
    ]
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.22, TW*0.20, TW*0.58]
    ))

    # ── UPDATED TRACEABILITY REGISTER ─────────────────────────────────────────
    E += [sp(8), hr(), Paragraph('Updated Traceability Register', S['h1'])]

    trace_rows = [
        ['Binary Snap causality',
         'Shape: ZP-C D1, L-RUN, TQ-IH; ZP-A D2; T-SNAP premises: DA-1 insert &#167; V. Occurrence: the occurrence commitment and DA-1',
         'None',
         'Derived for the shape — T-SNAP ✓; the snap occurs given the occurrence commitment and DA-1 (was: Axiomatic — AX-1)'],
        ['DA-1: Instantiation = execution',
         'DP-2 (TrackedOutput, Snap.lean &#167;VI); its precondition: the occurrence commitment; ZP-A CC-2, R3; ZP-C L-INF',
         'None',
         'Derived Proposition — primary: DP-2 (da1_minimal_path proved axiom-free in Lean). '
         'Arguments for its precondition, none deriving it: CC-2/R3 (structural), L-INF (informational), AIT incompressibility (Path 3). '
         'AIT+ZF+AFA outside Lean scope.'],
        ['DA-2: Instantiation succession',
         'ZP-A A4, CC-1; ZP-B C3, R1; T-SNAP',
         'None',
         'Definitional Alignment — clarification of CC-1 scope; no new axiom'],
        ['C-DA2: Novelty of ⊥ (conditional)',
         'DA-2, ZP-B C3',
         'None',
         'CONDITIONAL — a modelling commitment. NOT derived: the separateness of the spaces is assumed, not obtained from C3, and snap_arc_z2_loop returns to the same 0.'],
        ['DA-3: Perspective-relative cardinality',
         'DA-2, C-DA2, ZP-B R1',
         'None',
         'Definitional (DA-3-D1, R-DA3-1); Candidate (DA-3-C1: outside-view inaccessibility)'],
        ['T-SNAP: Snap shape is derived',
         'L-RUN, TQ-IH (the T-BUF chain&#8217;s lemmas); T-SNAP premises: DA-1 insert &#167; V. DA-1 bears on occurrence, not on the shape',
         'None',
         'Derived — Cross-Framework ✓'],
        ['AX-1 retirement',
         'T-SNAP proves the shape; the snap occurs given the occurrence commitment and DA-1',
         'N/A',
         'AX-1 is retired: T-SNAP proves the shape, and that the Snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2)'],
        ['Iterative Forcing T5 (restated)',
         'Selection: succession_succ, ZeroParadox/Ordinal/SnapSuccession.lean &#167; I; for a monotone map sending the tower&#8217;s stages to c<sub>0</sub>, given the alignment hypothesis h&#949;<sub>0</sub>, nothing below &#949;<sub>0</sub> fires (snap_unconditional). Iteration: T3, R1, t_snap_irreversible, tsnap_holds_but_nothing_moves',
         'None',
         'On an arbitrary lattice no step is selected. No step is guaranteed.'],
        ['Multiverse — structural implication',
         'T-SNAP + DA-2 jointly',
         'None',
         'Structural implication given the occurrence commitment — T-SNAP gives the snap\'s shape, CC-2\'s undifferentiated ⊥ the branching, DA-2 the succession'],
        ['OQ-E2: Cardinality correspondence',
         'DA-3',
         'N/A',
         'OPEN — formal derivation deferred'],
    ]
    E.append(data_table(
        ['Claim', 'Grounded In', 'Bridge Axiom?', 'Status'],
        trace_rows,
        [TW*0.22, TW*0.28, TW*0.12, TW*0.38]
    ))

    # ── VALIDATION STATUS ─────────────────────────────────────────────────────
    E += [sp(8), hr(), Paragraph('Validation Status', S['h1'])]

    val_rows = [
        ['DA-1: Derived Proposition, given DP-2',
         'Valid — DP-2 formal core: da1_minimal_path proved axiom-free in Lean (Snap.lean &#167;VI). '
         'TrackedOutput separates output value from machine state; pre- and post-instantiation states '
         'are provably distinct even when both produce &#8869;. ✓ '
         'ZP-K: da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase) proved in Kleene.lean. '
         'Path 1&#8217;s Lean counterpart is da1_closed_concrete, which proves nothing computational; Path 1 rules out an external executor, not an inert &#8869;. '
         'Path 3 (computational, ZP-C D1 + AIT): bears on the precondition and shows that executing is not derivable from incompressibility — incompressibility rules out a shorter external generator, not an inert string; that '
         'the configuration reaching P<sub>0</sub> is in Sense B and not Sense A is DP-2&#8217;s precondition, what the occurrence commitment asserts. Its Lean counterpart is the '
         'machinePhaseKleene instance&#8217;s botCode_is_quine field, a KleeneStructure requirement that constant codes also meet, not a witness of '
         'execution and not a second independent proof. '
         'da1_paths_unified carries the two Lean counterparts together as a conjunction; that they name one structural fact is the framework&#8217;s reading. '
         'Path 2 (informational bridge, L-INF): UNADOPTED BRIDGE PRINCIPLE — a missing principle, not a '
         'missing proof, distinct from the occurrence commitment and not a premise of the Snap; Path 2 does not derive the precondition. No computability library closes the gap between \'system at P₀\' and \'system is '
         'running.\' '
         'DA-1&#8217;s formal grounding (DP-2, da1_minimal_path) does not depend on Path 1, Path 2 or Path 3. '
         'CC-1 restated in ZP-J as an equivalence, and not forced (a valid sequence can start elsewhere on a carrier with a second point); CC-2 a Forced Metatheoretic Commitment whose Quine-atom role t_exec_iff shows only &#8869; fills.'],
        ['T-SNAP: Binary Snap derived',
         'Valid — Derived, in two readings. The Lean form (t_snap_derived) fixes the SHAPE with no hypotheses and no axioms. '
         'The seven-step prose argument uses commitments, and that the transition OCCURS is not established by T-SNAP (tsnap_holds_but_nothing_moves). '
         'Premises: DA-1 insert &#167; V, Premises of T-SNAP; two of them (CC-1 and occurrence at the first step) as hypotheses, t_snap_given. ✓'],
        ['AX-1 retirement',
         'Valid — AX-1 is retired, and its content was split in two. T-SNAP proves the shape, '
         'strengthened from assumed to derived. That the Snap occurs is stated separately: it follows from the occurrence commitment '
         '(instantiation occurs) together with DA-1 (closed given DP-2). Given CC-1, its first-step form is the hypothesis hocc in t_snap_given; '
         'tsnap_holds_but_nothing_moves shows T-SNAP does not carry it.'],
        ['DA-2: Instantiation Succession',
         'Valid — Definitional Alignment. Clarification of CC-1 scope. No new axiom. A4 role of ⊥ extended across instantiation boundaries. ✓'],
        ['C-DA2: Novelty of ⊥ (conditional commitment)',
         'CONDITIONAL — a modelling commitment. NOT derived: the separateness of the spaces is '
         'assumed, not obtained from C3, which quantifies only over paths WITHIN one space. '
         'snap_arc_z2_loop measures against it — the 2-adic arc returns to the same 0. Must not '
         'be cited as derived.'],
        ['Directed instantiation tree',
         'Valid given the occurrence commitment — structural consequence of T-SNAP + DA-2. Once instantiation is taken to occur, branching follows and is not optional. Forward edges only.'],
        ['Branching tree structure',
         'Valid given the occurrence commitment — T-SNAP + DA-2 jointly. T-SNAP fixes the snap’s SHAPE and does NOT establish that it occurs; DA-2 establishes the branching tree structure. Universality (all outbound vectors) is DA-2\'s scope, not T-SNAP alone.'],
        ['Monotonicity and path irrecoverability',
         'Valid — Structural consequence. Monotonicity (T3) constrains direction; additive ontology (R1) prohibits reduction. Path choice is undetermined by algebra.'],
        ['Ordinal direction of state sequences',
         'Valid — Derived from ZP-A T3 (monotonicity) and ZP-B C3 (irreversibility). Not assumed.'],
        ['DA-3: Perspective-Relative Cardinality',
         'Valid (definitional components: DA-3-D1, R-DA3-1). Candidate (DA-3-C1: connection to specific set-theoretic independence results). OQ-E2 open.'],
        ['DA-3-C1 — outside-view inaccessibility',
         'Candidate — no position within any instantiation can replicate the meta-level view of the branching structure. Formal derivation deferred to OQ-E2.'],
        ['Remaining axioms: AX-B1, AX-G1, AX-G2; typeclass fields A4, quine_unique, bot_self_mem, botCode_is_quine',
         'Named: AX-B1, AX-G1, AX-G2. Typeclass: A4/bot_join (ZPSemilattice), '
         'quine_unique + bot_self_mem (AFAStructure), botCode_is_quine (KleeneStructure). '
         'Assumptions carried as hypotheses by the theorems that use them; not surfaced by &#35;print axioms. CC-1 is a further commitment (ZP-A Conditional Claim).'],
        ['ZP-E results T1–T4, T6, T7',
         'Stated in an earlier version of this document (see the repository history) and not restated here. T5 is restated in DA-1 insert &#167; VI.'],
    ]
    E.append(data_table(
        ['Component', 'Status / Notes'],
        val_rows,
        [TW*0.32, TW*0.68]
    ))

    E += [
        sp(12),
        hr(),
        Paragraph(
            '<i>ZP-E carries three formal inserts (DA-1, DA-2, DA-3). T-SNAP is derived, with its premises stated in the DA-1 insert &#167; V and two of them (CC-1 and occurrence at the first step) as the hypotheses of t_snap_given; its irreversibility '
            'rests on ZP-A R1 and ZP-B C3, with ZP-G downstream. DA-1 is closed given DP-2 (da1_minimal_path, axiom-free). '
            'Path 1&#8217;s Lean counterpart is da1_closed_concrete (ZP-K), which proves IsQuineAtom(&#8869; : MachinePhase) and nothing '
            'computational; Path 3&#8217;s Lean counterpart is the machinePhaseKleene instance&#8217;s botCode_is_quine field, a KleeneStructure '
            'requirement, not a witness of execution; and '
            'the step from Path 2 to executing is a bridge principle of its own (a missing principle, not a missing proof), which the '
            'framework does not adopt and which is distinct from the occurrence commitment; and Path 3 bears on the precondition and shows that '
            'executing is not derivable from incompressibility: that the configuration reaching P<sub>0</sub> is in Sense B is what the occurrence '
            'commitment asserts, and DA-1 consumes it. Remark '
            'R-&#949;<sub>0</sub> justifies the &#949;<sub>0</sub> symbol as a structural analogy. Remark '
            'R-AFA rules Foundation out by the self-membership of &#8869; = {&#8869;} (Regularity, '
            'no_quine_atom): the forcing and realizability of the AFA requirements are machine-checked '
            '(QuineHost), and a narrow Forced Metatheoretic Commitment remains. Open question: OQ-E2. '
            'Remaining axioms: AX-B1, AX-G1, AX-G2.</i>',
            S['endnote']),
    ]

    print(f'[build_zpe] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zpe] Written: {out_path}')


if __name__ == '__main__':
    build()
