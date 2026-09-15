"""
v3.37: DECISION BATCH REMEDIATION AFTER GATE ROUND 3, SECOND PASS (Tim ruling, 2026-09-15): the DA-1 Status block said 'Kleene fixed-point is the in-scope formal counterpart' of AIT; it now says the Kleene structure is its in-scope counterpart, carried as a KleeneStructure requirement (botCode_is_quine), not a proof of the AIT claim.
v3.36: DECISION BATCH REMEDIATION AFTER GATE ROUND 3 (Tim rulings, 2026-09-15): T5 Selection credits each face of epsilon-0 with its own direction: a monotone map sending the tower's stages to c0 and epsilon-0 to c1 sends no ordinal below epsilon-0 to c1 (supremum face, fundamentalSeq_cofinal) and sends every fixed point of alpha -> omega^alpha to c1 (least-fixed-point face, hfp_from_epsilon_zero); it had said 'Both faces of epsilon-0 carry this' of the downward direction alone. Deriving h-eps0 is open 'from the 2-adic structure'. The Open Items OQ-A1 cell names the monotone map and the tower stages beside h-eps0. DA-1 PATH 3 (pre-existing bedrock, editorial round 3 B1): the DA-1 synthesis paragraph, the DA-1 Status block, the DA-1 validation row and the endnote said Paths 1 and 3 are formally closed / IN LEAN SCOPE and that DA-1 is grounded in them or closed in Lean via ZP-K. They now carry the CLAIMS.md DA-1 row: Path 1 is witnessed by da1_closed_concrete, which proves IsQuineAtom (bottom : MachinePhase) and nothing computational; Path 3's witness is the machinePhaseKleene botCode_is_quine field, a KleeneStructure requirement, not a second independent proof; da1_paths_unified carries them as a conjunction of witnesses, and that they name one structural fact is the framework's reading; DA-1 is closed given DP-2.
v3.35: ADVERSARY GATE ROUND 3 (bedrock, D1): the T5 traceability row said 'given the alignment hypothesis h-eps0, nothing below epsilon-0 fires', dropping two of snap_unconditional's three hypotheses (monotonicity, and the tower stages sent to c0); a monotone map with h-eps0 can fire at 1. The row now names the monotone map sending the tower's stages to c0, as the T5 box already did.
v3.34: DECISION BATCH REMEDIATION AFTER GATE ROUND 2, SECOND PASS (Tim ruling, 2026-09-15): the pointer for h-eps0 named OQ-E2, which in this document is the cardinality-semilattice correspondence, the wrong object. The T5 Selection text, the traceability row and the Open Items OQ-A1 cell now point at what ZeroParadox/Ordinal/Incompleteness.lean says: h-eps0 is the alignment hypothesis, and deriving it is open as the Classical.choice inversion conjecture. OQ-E2's own rows are unchanged.
v3.33: DECISION BATCH REMEDIATION AFTER GATE ROUND 2 (Tim rulings, 2026-09-15): T5 selection restated to what snap_unconditional proves: the placement at epsilon-0 is the hypothesis h-eps0 (the ordinal-lattice alignment, open as OQ-E2) and only minimality is derived, carried by both faces of epsilon-0 (supremum of the stages, fundamentalSeq_cofinal; least fixed point, epsilon0_min_eq_max). No rung is ⊥, cited for every rung (Ordinal.epsilon_pos). Iteration: the finite-step sentence is scoped short of a top. Reading gets an antecedent. T5 gloss: Forcing names the shape of each step taken. OQ-A1 short cell two-part; traceability row matches; SnapSuccession cited by full path; join written as vee.
v3.32: DECISION BATCH REMEDIATION ROUND 2 (Tim rulings, 2026-09-15): the OQ-E1 Open Items row called instantiation occurring 'a framework commitment'; it is the occurrence commitment.
v3.31: DECISION BATCH REMEDIATION (Tim, 2026-09-15): T5 box: the selection half ('if the step is taken it is the minimum viable one, alpha_n = eps(S_n), a Conditional Claim given AX-B1's discreteness at every state') is replaced by Tim's confirmed text (ordinal chart: succession_succ, SnapSuccession section I, snap_exactly_at_epsilon_zero, epsilon0_ne_bot; on an arbitrary lattice no step is selected), and the iteration half ('the occurrence commitment applied at each step') by 'No step is guaranteed' (T3, R1, t_snap_irreversible, tsnap_holds_but_nothing_moves) with its epsilon0_min_eq_max reading; the HasFirstStep-at-a-state bullet is removed. R-DA1 points at the box. The Open Items OQ-A1 row reads 'OQ-A1b CLOSED by A1-A4; OQ-A1a answered by crossing charts'; the T5 traceability row and the validation row are synced; 'restated in section VI' is 'DA-1 insert section VI'. The branching-tree implication says the Snap occurring follows from the occurrence commitment together with DA-1 (closed given DP-2).
v3.30: OCCURRENCE COMMITMENT DEFINED, T5 RESTATED, T-SNAP RESIDUE (Tim decision batch, 2026-09-14): the occurrence commitment is ONE commitment, instantiation occurs (a machine configuration reaches P0); DA-1 (closed given DP-2) says a configuration at P0 is executing; together they give that the Snap occurs, and T-SNAP fixes its shape. The canonical AX-1 sentence now reads 'that the snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2)' at the abstract, the Conclusion, R-DA1, the Open Items AX-1 row, the AX-1 traceability and validation rows; premises (ii) names the commitment and DA-1 separately, and hocc is the first-step form of the Snap occurring given CC-1, never of instantiation occurring. The abstract no longer routes the shape through DA-1 ('With DA-1 in place, AX-1 is retired'), and the Binary Snap causality and T-SNAP traceability rows put DA-1 on the occurrence side. T5 (Iterative Forcing Theorem), recovered from ZP-E v1.4, is restated in section VI split the way AX-1 was: selection (if the step from Sn is taken it is the minimum viable one, alpha_n = eps(Sn)) is a Conditional Claim given AX-B1's discreteness at every state, and iteration is the occurrence commitment applied at each step; OQ-A1 is 'closed given AX-B1 and the occurrence commitment', and the T5 traceability row matches. The validation row 'All other ZP-E theorems (T1-T7, T2-C) - Unaffected in content' was false (this document states none of them; T2-C appears nowhere else in it) and now says T1-T4, T6, T7 were stated in ZP-E v1.4 and are not restated here. T-SNAP's box glosses its readable name once: 'Causality' refers to the shape of the step, not to its occurrence. Open Items: 'with no axioms' is 'with no Lean kernel axioms'. The Note on Lean scope was re-checked against Snap.lean and Surprisal.lean and is unchanged. TIM PREVIEW (2026-09-14): the T1-T4, T6, T7 validation row cites an earlier version of this document without naming its version number.
v3.29: T-SNAP PREMISES POINT AT LEAN (Tim, 2026-09-14: pointers plus a small companion). The premises of T-SNAP now have a Lean home: t_snap_given (ZeroParadox/Order/Snap.lean) takes CC-1 (S0 = bottom) and occurrence (S1 != S0) as hypotheses over any join-semilattice with bottom, and t_snap_derived's statement is its MachinePhase instance. Premises of T-SNAP names it in reading (i) and the occurrence hypothesis in (ii); the Status block, Open Items AX-1 row, both traceability rows, the validation row and the endnote point there. CC-1 arc round-4 residue cleared: the section no longer claims to be 'the one place' every other site points to; 'rest on commitments named there' no longer reads as complete; (ii) calls the L-INF step a foundational commitment, as section IV does; the Lean-scope note no longer says 'two decide calls ... bot_join' (one decide, tq_ih its symmetric form, rfl for the join); Step 2 cites DA-1 section IV, not III; DA-2 section I no longer calls the snap 'a structural consequence of reaching P0'; pointers name the DA-1 insert, since DA-2 also has a section V. ROUND 1 GATES (FAIL-BEDROCK, D1) + TIM'S AX-1 SPLIT (Tim, 2026-09-14: 'Both: split it'): reading (i) said t_snap_derived's statement is the MachinePhase instance 'where both hypotheses hold inside the type', which put occurrence inside MachinePhase; the instance is at the chosen sequence c0, c1, c1, ... where hocc reduces to c1 != c0, and the sequence that stays at c0 is a state sequence in the same type that fails hocc. AX-1 bundled the SHAPE of the Snap with its OCCURRENCE: the shape half is Theorem T-SNAP, and the occurrence half was never retired and is the occurrence commitment; the opening, the Conclusion, R-DA1, the Open Items AX-1 row (now SPLIT), both AX-1 retirement rows (the validation row said 'No content lost') and the T5 row are scoped to that. hocc is named occurrence at the first step (a sequence first moving at a later index fails it); t_snap_given takes TWO of the premises, not all; the inequalities restate hocc and only the join is derived (A4); hocc forces at least two points, not exactly two. Also: DA-1 cited at section IV, not III, in section I; the traceability parentheticals attach to T-SNAP, not DA-1; 'NO-GO examples' is 'examples'; 'intended ontological meaning' restated as a reading about the framework's own state sequence. AX-1 WORDING CORRECTED (Tim, 2026-09-14): retired, split into T-SNAP (shape, proved) and the occurrence commitment (stated separately); the earlier 'occurrence half was never retired' was a paraphrase error. ROUND 2 GATES (Tim rulings: title, ZP-C label, DA-1 credit): the Open Items AX-1 row credited the shape to 'P0 + DA-1 + L-RUN + TQ-IH + ZP-A D2', putting DA-1 on the shape side while Premises (ii) puts it on the occurrence side; it now carries Tim's sentence: the shape is proved as T-SNAP from L-RUN, TQ-IH and the bottom law with no axioms, and occurrence is the occurrence commitment, which DA-1 argues for. That row and the AX-1 retirement validation row equated the occurrence commitment with hocc; both now say hocc is its first-step form, as (ii) does. Reading (i) said the start at bottom is built into the choice of the type MachinePhase; a state sequence in that type can start at c1, so the start comes from the statement's choice of c0, and only binary existence is in the type.
v3.28: CC-1 STATUS SYNC (Tim, 2026-09-13: everything in one arc). "CC-1 derived / closed / no longer a freestanding commitment" collapsed two readings: cc1_derived proves the CONDITIONAL (a state sequence starting at a Quine atom starts at bottom), and with t_exec_iff the converse holds, so the starting-point choice is RESTATED through the Quine-atom role, not forced; every ZP-A lattice carries AFAStructure trivially. Every site now keeps both halves, matching ZP-J v2.7. Also CC-2 no longer called 'a structural consequence' (bot_self_mem is a class FIELD T-EXEC consumes): it is ZP-A's Forced Metatheoretic Commitment, T-EXEC proves bottom the only occupant of the Quine-atom role, and in AFA set theory Q = {Q} is a theorem while bottom being that set is the argued step. DA-1 Path 1's 'bottom in bottom, i.e. bottom = {bottom}' reversed to the true direction and its 'not a commitment - forced' restated as argued (more than a free choice, less than a theorem); the iff is t_exec_iff. ADVERSARY ROUND 1 (FAIL-BEDROCK, D1): the T-SNAP Status block still dropped CC-1 from T-SNAP's givens ('derived given DA-1 and AX-B1') on the strength of 'neither freestanding', while the DA-1 Status block four paragraphs earlier lists 'DA-1, CC-1, and AX-B1'; the premise that dropped it was the retracted derivation, so CC-1 is restored to the givens and called a Conditional Claim. The DA-1 synthesis paragraph's 'establishing bottom = {bottom} as a structural consequence rather than a commitment (ZP-J T-EXEC)' was the CC-2 site this entry's sweep missed; it now matches Path 1. ROUND 1 (editorial + claim-review + adversary FAIL-BEDROCK; prior-art PASS): the sync first gave the wrong REASON for "not forced" ("every ZP-A lattice carries AFAStructure trivially, so ..."), which does not follow; the reason is that a valid state sequence can start above bottom (T2 fixes only bottom <= S0; an example on OntologicalStates in OntBridge.lean). Also R-AFA and Path 1 say T-EXEC proves the Quine-atom role's occupant is bottom, not that it 'formally verifies the structure' or checks 'the structural self-application fixed point'; Path 1's executes-itself step no longer jumps silently to 'its own sole member' (Aczel's 0* = {empty, 0*} contains itself without being its own singleton); Q = {Q} cited to Aczel 1988 Example 1.3. GATE ROUND 2 (ordinary, carried): the 'not forced' reason needs its scope - on a ONE-point lattice every sequence starts at bottom, so the countermodel is stated for a lattice with a second point, and the OntBridge.lean example now also shows the start is not a Quine atom. T-SNAP PREMISE LISTS RECONCILED (Tim: fold into this arc; ZPE-TSNAP-PREMISES): the informal argument uses AX-B1 at Step 4 and CC-1 for the start at bottom, while the box, the Status block and the validation row each listed a different subset; all now say derived given the commitments AX-B1 and CC-1, and CC-1 no longer shares 'the same logical status as named axioms'. The Lean t_snap_derived is unaffected: it takes no hypotheses and no axioms. CLAIM-REVIEW ROUND 3 (FAIL-BEDROCK, D1): the reconciled lists were each one short - the box's 'given two commitments', the Status block's 'Commitments: AX-B1; CC-1' and the validation row's 'Every other dependency is a closed theorem' omitted that Step 2 imports DA-1, closed only given DP-2, and that occurrence is a commitment (tsnap_holds_but_nothing_moves satisfies AX-B1 and CC-1 and never moves). No fourth hand list: the premises are now stated ONCE, as 'Premises of T-SNAP, in two readings' after the Theorem box - (i) the Lean form, no hypotheses, fixes the shape on MachinePhase; (ii) the prose argument uses AX-B1 and CC-1 among its commitments, and occurrence rests further on DA-1 given DP-2 and the occurrence commitment - and the box, both status blocks, the validation row and the Remaining-axioms row point there without a count.
v3.27: C-DA2 RETRACTION COMPLETED (bedrock). v3.26 downgraded the Corollary to a Conditional Claim and rewrote its section, but the Validation Status table's STATUS cell was never touched - it still shipped "Valid - Derived. Follows directly from DA-2 and ZP-B C3." four pages after the section saying the opposite, on the one page a reader opens specifically to check status. A half-applied fix to a self-consistent error manufactures a self-contradiction; the wording now matches the dependency table, which had it right at :786 all along.
Zero Paradox — ZP-E: Bridge Document PDF Builder
Version 3.26 | July 2026
v3.26: NOVELTY OVERCLAIM RETRACTED (bedrock) - C-DA2 DOWNGRADED FROM COROLLARY TO CONDITIONAL CLAIM. The document published "Corollary C-DA2 - Ontological Novelty of Successive bottom" with a status cell reading "Derived - Corollary of DA-2 and C3" and a written proof whose load-bearing step - "the bottom of I_{n+1} is an element of a distinct topological space" - IS the conclusion, not a consequence of C3. C3 quantifies over paths WITHIN one space; it is silent on whether the next instantiation's space is a different one, so assuming separateness to derive distinctness is circular. The handle C-DA2 is unchanged per R-NAMING; only its STATUS changes. Measured against: snap_arc_z2_loop proves the 2-adic tower starts at 0, every finite stage is nonzero, and it converges back to 0, and tower_image_loops_to_seed states the limit IS the seed - so in that chart novelty does not merely lack a proof, it fails. Also fenced at the TrackedOutput return, the DA-2 connection, the no-back-edges bullet, the DA-2 traceability row and both status tables. v3.25 retracted the OCCURRENCE overclaim and left NOVELTY standing beside it.
v3.25: FORCING OVERCLAIM RETRACTED. The document asserted that T-SNAP establishes the snap OCCURS. It does not: T-SNAP fixes the transition's shape, and Order/Snap.lean's NO-GO gauge tsnap_holds_but_nothing_moves proves T-SNAP holds in a model where nothing moves. Occurrence is a framework commitment (Information/Surprisal.lean's l_inf docstring is the designated honest stopping point). Prose only; no claim gains support and none is withdrawn beyond this one. Four sites: the branching-tree implication, the OQ-E1 row, and two claim-table validity grounds, all of which used occurrence as the ground. OQ-E1 is now 'closed given the occurrence commitment', matching CLAIMS.md and the DA-1 row's existing 'closed given DP-2' form.
v3.24: R-AFA false premise corrected (bedrock) — struck the invalid "well-founded ⟹ finite ∈-tree / finite ∈-rank ⟹ finitely interpretable" step (false: ω is well-founded and infinite). Foundation-incompatibility now rests on the self-membership of ⊥ = {⊥} (Regularity; no_quine_atom, choice-free), with R3/L-INF demoted from independent proofs to corroboration. Status brought current: forcing + realizability stated as machine-checked (QuineHost — quineHost_not_wellFounded, oneAtom_not_wellFounded, afaStructure_isQuineHost); CC-2 = Forced Metatheoretic Commitment, not Conditional Claim; named falsifier narrowed to the requirements-choice. Also CC-1 "modelling commitment" → "derived via ZP-J cc1_derived" (DA-2); DA-3 cardinality-anomaly link hedged to conjecture (DA-3-C1 / OQ-E2); closing endnote rewritten from editorial-history narration to a description of what the document is.
v3.23: rendered Lean citations synced to post-reorg files/namespaces the earlier passes missed (bare ZPx.lean / ZeroParadox.ZPx.* / ZPx.<decl>; SSOT-driven).
v3.21: FMC precision (sweep Step 4 remediation, against fmc.md) — R-AFA "the metatheoretic necessity of AFA is derived" → "argued, not proved (a metatheoretic squeeze, not a derivation)"; named falsifier added to R-AFA; CC-2 status lines now split the proved structural fixed point (T-EXEC, axiom-free) from the argued set-membership reading; "establish that Foundation is incompatible" → "make the case that".
v3.20: Rendered version refs removed — DA-2/DA-3 section notes ("New in v2.0") and endnote version (C1 sweep — no version changelogs in rendered PDF content).
v3.19: Version reference removed from T-BUF li() call (Gemini catch — build gate does not cover li()).
v3.18: Vocabulary fixes — "null state" → "⊥"; "non-null state" → "nonzero state" throughout body prose; version references (v1.4, v1.5, v2.7, v1.0) removed from body prose. Palette rebuild.
v3.17: K-22 vocabulary fix — "informational extremity" → "unbounded surprisal (L-INF)"
in DA-1 Section II bridge prose.
v3.16: Version numbers removed from three internal register section headers (Open Items,
Traceability, Validation Status) — version numbers belong in the title block only.
v3.15: DA-1 Path 2 forward reference to ZP-M R-M.1 added at three locations — retrospective
structural analysis of why the informational bridge resisted formalization.
v3.14: Adversary-review pass — "AX-1 is promoted" → "AX-1 is derived as" (two occurrences);
version history removed from opening paragraph (belongs in docstring); "[AX-1 Promoted to
Theorem]" bracket removed from theorem box title; "structural event" → "structural limit";
Section VII headers renamed from grand-scope vocabulary to mathematical descriptions:
"Multiverse as structural implication" → "Structural Implication: Branching Tree Structure";
"Free will and irreversibility" → "Monotonicity and Path Irrecoverability";
"Time's arrow" → "Ordinal Direction of State Sequences".
v3.13: Precision fix — "topological isolation is maximal" replaced with "clopen separation is
total — 0 and every nonzero element lie in disjoint clopen classes" (0 in ℚ₂ is not topologically
isolated; the correct property is clopen separation). "DA-1 unifies" replaced with "DA-1
establishes these as descriptions of the same structural event across four independent
mathematical languages."
v3.12: Framework scope and failure-mode framing added to preamble — "coverage not exhaustion"
paragraph addresses the "why these four?" question; cross-framework failure-mode paragraph names
the domain-specific limit at ⊥ for each layer (lattice minimum, p-adic isolation, unbounded
surprisal, orthogonal basis vector) and positions DA-1 as the unifying argument.
v3.11: T-SNAP Step 7 corrected — AX-G2 removed as formal dependency; now labelled as conceptual
correspondence only. ZP-G is downstream of ZP-E and cannot be a formal dependency of T-SNAP.
Irreversibility proof rests on ZP-A R1 and ZP-B C3 alone, which are sufficient.
v3.10: Forward references to "ZP-PQ" replaced throughout with "The Philosophical Question That Started This" — that document already contained the dissolution argument; ZP-PQ was always a placeholder label.
v3.9: R-ε₀ reframed — remark now leads with explicit informal-analogy disclaimer; "structural
correspondence" changed to "structural analogy" throughout R-ε₀. Reviewer feedback: hedge was
buried at end of remark; readers might miss it after several paragraphs of parallel-drawing.
v3.8: DA-1 Path 2 recharacterized — from "outside Lean scope (informational bridge)" to
"foundational commitment: a missing principle, not a missing proof." No computability library
closes the gap between 'system at P₀' and 'system is running.' Forward paths: new axiom,
Chalmers' implementation notion, or The Philosophical Question That Started This. That document already contains
the dissolution: the description-instantiation gap assumes a separability the framework dissolves.
v3.7: DA-1 formally closed via ZP-K — KleeneStructure MachinePhase instance proved in Lean 4.
da1_closed_concrete : IsQuineAtom (bot : MachinePhase). DA-1 Path 1 (structural/AFA) and
Path 3 (computational/Kleene) now in Lean scope. Path 2 (informational bridge) remains outside
Lean scope. "Outside Lean Scope" designation removed from ZPE.lean DA-1 section.
v3.6: DA-1 Path 1 rewritten — argument direction reversed. Previously: CC-2 (⊥ = {⊥}) asserted,
then "no external interpreter" derived. Now: "nothing external to ⊥ can execute ⊥" argued first,
⊥ = {⊥} derived as the only coherent structure, ZP-J T-EXEC cited as formal verification.
CC-1 and CC-2 status updated throughout — no longer freestanding commitments; both derived via ZP-J.
v3.5: Open Items Register DA-1 status updated — "CLOSED — DP-2 (formal core); CC-2 + L-INF + AIT
(corroboration of precondition)" now matches v3.3 path-hierarchy framing.
v3.4: R-AFA minimality argument made explicit — added one sentence to "What remains
conditional" stating that ⊥ = {⊥} is uniquely minimal among AFA non-well-founded sets:
exactly one member, no internal differentiation; any extension exceeds A4's constraint.
v3.3: DA-1 path hierarchy foregrounded — added explicit framing before Paths 1–3 stating
that the three informal paths are corroboration of the precondition DP-2 formalizes, not
parallel proofs of DA-1 itself. Shrinks attack surface on Angle 1 (DA-1 doing too much work).
v3.2: Remark R-AFA added — Foundation ruled out by R3 and ZP-C L-INF; AFA identified as the
forced metatheoretic replacement rather than an arbitrary choice; CC-2 status clarified.
v3.1: Remark R-ε₀ added — notation justification for ε₀ symbol choice; structural correspondence
with the Cantor-Gentzen proof-theoretic ordinal explained.
v3.0: DP-2 (Execution Distinguishability) added — DA-1 formally grounded in TrackedOutput construction
(ZPE.lean §VI); da1_minimal_path proved axiom-free in Lean. First Lean formalization of DA-1,
conditional on DP-2. Section III (DP-2) inserted in DA-1 insert; existing III/IV/V renumbered IV/V/VI.
v2.9: DA-1 Lean scope note added — functional role carried by ZPC.l_run/tq_ih; AIT+ZF+AFA bridge
outside Lean scope (same category as ZP-A CC-2). PDF status line updated to reflect Lean scope.
v2.8: DA-1 formal bridge added: incompressibility = self-description argument (ZP-C D1 + standard AIT).
At P0, K(c1|n)/|c1| = 1 means description and execution coincide; CC-2/R3 and L-INF become corroboration.
v2.7: DA-1 upgraded from Design Principle to Derived Proposition — grounded in ZP-A CC-2 and R3.
Follows all rules in pdf rendering standards:
  - DejaVu fonts only
  - Checkmark always wrapped in <font name="DV">
  - All table cells are Paragraph objects
  - No unicode subscripts — use sub/super tags
  - US Letter, 1-inch margins, TW = 6.5 inch
"""

import os
from zp_utils import *

VERSION = '3.37'
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
        'and functional/Hilbert space analysis (ZP-D). The claim is that the same structural '
        'limit appears across each of the four frameworks addressed here — not that these four '
        'are the only possible witnesses.'))
    E.append(body(
        'Across all four layers, the same structural limit appears at &#8869; — but each framework names '
        'it differently: ZP-A identifies &#8869; as the global minimum, below which the lattice\'s ordering '
        'relation cannot descend; ZP-B finds the p-adic valuation undefined (or +&#8734;) at 0, where '
        'clopen separation is total — 0 and every nonzero element lie in disjoint clopen classes; '
        'ZP-C finds surprisal unbounded above at &#8869;, so no finite '
        'external description can contain &#8869;; ZP-D maps 0 to a basis vector orthogonal to '
        'every nonzero state, from which no return is possible. DA-1 establishes these as descriptions '
        'of the same structural limit across four independent mathematical languages.'))
    E.append(hr())

    print('[build_zpe] Building DA-1...')
    # ── FORMAL INSERT DA-1 ────────────────────────────────────────────────────
    E += [
        Paragraph('Formal Insert DA-1: Derived Proposition — Instantiation as Execution', S['h1']),
        Paragraph('<i>DA-1 is a Derived Proposition: instantiation as execution, the first Lean '
                  'formalization of DA-1 (axiom-free, conditional on DP-2, Snap.lean &#167;VI), with '
                  'incompressibility read as self-description (ZP-C D1 + AIT) and CC-2/R3 grounding.</i>',
                  S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-1 Closes', S['h2']))
    E.append(body('The T-BUF chain from ZP-C established three results:'))
    E += [
        li('L-RUN: The transition c<sub>0</sub> → c<sub>1</sub> is a nonzero state transition. (ZP-C — Derived)'),
        li('TQ-IH: No program outputs ⊥ without a nonzero intermediate configuration state. (ZP-C — Derived by L-RUN)'),
        li('T-BUF: At P<sub>0</sub>, execution is structurally guaranteed; that execution state is ε<sub>0</sub> in the semilattice. (ZP-C — Candidate Theorem pending DA-1)'),
        sp(4),
    ]
    E.append(body(
        'T-BUF was labelled Candidate because Step 2 asserts that a configuration at P<sub>0</sub> is a '
        'live machine state — that instantiation at P<sub>0</sub> constitutes an execution event, not a static '
        'description. ZP-C L-INF supplies one mathematical premise: &#8869; at P<sub>0</sub> has unbounded '
        'surprisal — no finite external interpreter can hold it as a static description. ZP-A CC-2 '
        'supplies a second, structural basis: &#8869; = {&#8869;} is a self-containing object with no external '
        'interpreter by structure. DA-1 (&#167; IV below) provides the derived proposition that closes T-BUF Step 2.'))

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
            'Irreversibility (ZPB C3, ZPE t_snap_irreversible) blocks any path back to preInstantiation.'),
    ]

    E.append(Paragraph('IV. Proposition DA-1', S['h2']))
    E.append(bridge_box(
        'Proposition DA-1 — Instantiation as Execution',
        [
            'Claim: The instantiation of a machine configuration c<sub>1</sub> at the incompressibility threshold '
            'P<sub>0</sub> is an execution event in the sense of L-RUN. It is not a static description of a machine. '
            'It is a machine in state c<sub>1</sub>.',
            'Formal core (Lean): DP-2 (§III) — TrackedOutput separates output value from machine state. '
            'da1_minimal_path proves: one act of instantiation moves c<sub>0</sub> to c<sub>1</sub> regardless '
            'of output value. The returned ⊥ occupies the bottom role again; reading it as a NEW null rather than the prior c<sub>0</sub> is C-DA2, a modelling commitment. The axiom-free result is the role, not the novelty.',
            'Structural grounding: ZP-A CC-2 (⊥ = {⊥}) establishes ⊥ as a Quine atom under ZF + AFA — a set that is '
            'its own singleton, admitting no external interpreter. ZP-A R3 derives the immediate consequence: '
            'a self-containing object cannot be a static description awaiting external instantiation. '
            'ZP-C L-INF provides independent informational corroboration: ⊥ has unbounded surprisal, '
            'exceeding the capacity of any finite interpreter.',
        ]
    ))
    E += [
        sp(4),
        body('The three paths below are not parallel proofs of DA-1. Each argues independently for why '
             'the precondition DP-2 formalizes holds — why instantiation of &#8869; at P<sub>0</sub> '
             'necessarily constitutes a first instruction fetch rather than a static description. '
             'DP-2 + da1_minimal_path derive c<sub>0</sub> &#8594; c<sub>1</sub> axiom-free once that '
             'precondition is established. The paths are convergent corroboration of the precondition; '
             'the formal derivation is DP-2\'s.'),
        body('Path 1 — Structural (Self-Execution, ZP-J T-EXEC): Nothing exists outside the null space. '
             '&#8869; is prior to all differentiation — there is no external state, no prior cause, no position '
             'from which something else could execute &#8869;. If &#8869; executes at all, the only possible '
             'executor is &#8869; itself. A thing that executes itself contains itself, and the framework reads this as its own sole member: '
             '&#8869; = {&#8869;}, so &#8869; &#8712; &#8869;. The argument is that this is forced by the impossibility of external '
             'execution, which makes it more than a free choice and less than a theorem. ZP-A R3 states the structural consequence: a self-containing object admits no external '
             'interpreter position. ZP-J T-EXEC proves that whatever fills the Quine-atom role is &#8869;: IsQuineAtom(q) &#8596; q = &#8869;, '
             'proved axiom-free in Lean 4 (ZeroParadox.t_exec_iff). AFA (ZF + AFA) is the consistent '
             'set-theoretic home for this structure — chosen because the framework requires it, not the '
             'reverse. ZP-A CC-2 (&#8869; = {&#8869;}) is a Forced Metatheoretic Commitment: on a lattice, T-EXEC proves that '
             'whatever fills the Quine-atom role is &#8869; (axiom-free, given the field bot_self_mem); in AFA set theory Q = {Q} is a theorem (Aczel 1988, Example 1.3), and that the framework&#8217;s &#8869; is that set is the argued metatheoretic step (see Remark R-AFA).'),
        body('Path 2 — Informational (ZP-C L-INF): Independently, the surprisal I(n) = n at ball-hierarchy '
             'depth n is unbounded — for any finite M, ∃ depth n with I(n) > M. ⊥ corresponds '
             'to the limit point 0 ∈ Q<sub>2</sub>; its informational content exceeds every finite bound. '
             'Any finite external interpreter can hold only a finite informational bound; ⊥ exceeds every '
             'such bound. '
             'Note: Path 2 is motivational context, not a formal path to the conclusion. The step '
             '"exceeds every finite bound → therefore necessarily executing" is a foundational commitment, '
             'not a derivable claim. It asks what it means for a mathematical structure to <i>instantiate</i> '
             'rather than merely <i>satisfy</i> conditions — a question no computability library answers. '
             'Forward paths: (a) a new axiom explicitly committing to this bridge; (b) a connection to '
             'Chalmers\' notion of implementation; (c) the dissolution argument in The Philosophical Question That Started This — the separability '
             'of description and instantiation is the assumption the framework dissolves, not a gap it must '
             'close from the outside.'),
        body('Path 3 — Formal bridge: Incompressibility as Self-Description (ZP-C D1 + standard AIT): '
             'The preceding paths establish that ⊥ admits no external interpreter. This path provides '
             'the formal bridge from that negative claim to the positive claim (necessarily executing). '
             'In the standard Turing model (D7), a machine configuration x exists in one of two states: '
             '(A) Static description — x exists as a string specified but not yet being executed; some '
             'external program p (|p| &lt; |x|) generates x when run, so x is a description awaiting a '
             'separate execution event by an external generator. '
             '(B) Live execution — x is the current configuration of a running machine. '
             'These are exhaustive in the Turing model: either x has a shorter external generator, or it does not. '
             'At P<sub>0</sub>, ZP-C D1 gives K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1: c<sub>1</sub> is algorithmically incompressible. '
             'No external program p exists with |p| &lt; |c<sub>1</sub>| such that U(p, n) = c<sub>1</sub>. '
             'State (A) requires such a p — and no such p exists at P<sub>0</sub>. '
             'State (A) is therefore eliminated by the Kolmogorov condition. '
             'Since (A) and (B) are exhaustive and (A) is eliminated, c<sub>1</sub> is in state (B): it is executing. '
             'Instantiation at P<sub>0</sub> is not the placement of a description to be executed later — '
             'there is no shorter prior description to execute. Instantiation and execution are the same act.'),
        body('The formal grounding (DP-2, §III) and the three paths above operate at distinct levels, '
             'not as alternatives to one another. DP-2 + da1_minimal_path establish a conditional at the '
             'level of machine-state representation: <i>if</i> instantiation of ⊥ constitutes a first '
             'instruction fetch in the sense of D7, <i>then</i> c<sub>0</sub> → c<sub>1</sub> follows '
             'necessarily — axiom-free, proved by construction. DP-2 is grounded in D7 itself (the standard '
             'computational distinction between before-first-instruction and after-first-instruction states), '
             'which is prior to and independent of DA-1. The three paths above operate one level down: they '
             'argue for why the precondition holds — why instantiation of ⊥ necessarily constitutes a first '
             'instruction fetch at all. Path 1 (structural) argues that nothing external to &#8869; can '
             'execute &#8869; — therefore &#8869; must execute itself, which argues for &#8869; = {&#8869;} as '
             'more than a free choice and less than a theorem (ZP-A CC-2, a Forced Metatheoretic Commitment); '
             'ZP-J T-EXEC proves, axiom-free, that whatever fills the Quine-atom role is &#8869;. Path 2 (informational) '
             'provides motivational context — unbounded surprisal as a pointer toward why static holding is '
             'incoherent — but the bridge from unbounded surprisal (L-INF) to execution is a foundational '
             'commitment, not a derived claim. Path 3 (AIT) argues that incompressibility eliminates the '
             'static-description alternative. '
             'Path 1 is witnessed by da1_closed_concrete (ZP-K), which proves IsQuineAtom(&#8869; : MachinePhase) and nothing '
             'computational; Path 3&#8217;s witness is the machinePhaseKleene instance&#8217;s botCode_is_quine field, a KleeneStructure '
             'requirement, not a second independent proof. The two are carried together by da1_paths_unified as a conjunction of '
             'witnesses; that they name one structural fact is the framework&#8217;s reading. Path 2 identifies a missing principle; '
             'its forward resolution is in The Philosophical Question That Started This. Path 2 is context. '
             '(ZP-M R-M.1 provides a retrospective structural analysis of why the gap resisted formalization.)'),
        derived('Status: DERIVED PROPOSITION — primary formal grounding: DP-2 (§III, TrackedOutput construction). '
                'da1_minimal_path proved axiom-free in Lean (Snap.lean &#167;VI): instantiation moves c<sub>0</sub> '
                'to c<sub>1</sub> regardless of output value. ✓ '
                'Path 1 (structural, ZP-J T-EXEC + ZP-K): witnessed by da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase), proved in Kleene.lean, which proves nothing computational. '
                '(Under MachinePhase\'s selfMem x := x = &#8869;, this reduces to (&#8869; = &#8869;) &#8743; (&#8704; x, x = &#8869; &#8658; x = &#8869;) — structural closure enforced by typeclass design, not a set-theoretic derivation from ZF+AFA. See R-K.0.) '
                'Path 2 (informational, L-INF): FOUNDATIONAL COMMITMENT — a missing principle, not a missing proof. Forward: The Philosophical Question That Started This; ZP-M R-M.1 (retrospective structural analysis). '
                'Path 3 (computational, ZP-K Kleene): its witness is the machinePhaseKleene instance&#8217;s botCode_is_quine field — a KleeneStructure requirement, not a second independent proof; da1_paths_unified carries it with Path 1 as a conjunction of witnesses. '
                'CC-1 (S<sub>0</sub> = &#8869;): restated — ZP-J cc1_derived with t_exec_iff makes a Quine-atom start and a &#8869; start the same condition (axiom-free, Lean) — and not forced: on a carrier with a second point a valid sequence starts elsewhere (ZeroParadox/Settheory/OntBridge.lean). '
                'CC-2 (&#8869; = {&#8869;}): ZP-J t_exec_iff proves &#8869; is the only occupant of the Quine-atom role (axiom-free); that &#8869; is the AFA set Q = {Q} is an argued metatheoretic commitment (see R-AFA). '
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
           'That the transition OCCURS rests further on two things. The occurrence commitment: instantiation occurs (a machine configuration reaches P&#8320;). '
           'And Step 2, which imports DA-1: a configuration at P&#8320; is executing. DA-1 is closed only given DP-2: &#167; IV derives c&#8320; &#8594; c&#8321; from DP-2 '
           'once DP-2&#8217;s precondition is established, and calls its three paths convergent corroboration of that precondition; Path 1 argues through '
           'ZP-A CC-2, itself a commitment. Together they give that the Snap occurs, which is not a theorem. Given CC-1, its first-step form is the hypothesis hocc of t_snap_given '
           '(a sequence that first moves at a later index fails hocc). ZP-C L-INF '
           'supplies unbounded surprisal, and the step from there to forced execution is a foundational commitment (&#167; IV), not a '
           'mathematical consequence of L-INF alone.'),
        sp(4),
        body('Proof:'),
        body('<i>Note on Lean scope: the formal Lean proof of T-SNAP is a single term — '
             '&#10216;l_run, tq_ih, rfl&#10217; — l_run proves c&#8320; &#8800; c&#8321; by decide, tq_ih is its symmetric form, '
             'and rfl closes the join in the MachinePhase semilattice (t_snap_given obtains that conjunct from A4, bot_join). '
             'What follows is the informal motivation for the modelling choices that let that term '
             'be read as a statement about the framework&#8217;s own state sequence.</i>'),
        sp(4),
        li('Step 1 — P<sub>0</sub> identifies the incompressibility threshold. When K(x|n)/n = 1, the configuration string x is algorithmically random. (ZP-C D1)'),
        li('Step 2 — A configuration at P<sub>0</sub> is necessarily executing: At P<sub>0</sub>, K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1 (ZP-C D1) — c<sub>1</sub> is incompressible, its own minimal program. No shorter external generator exists; the static description state is eliminated; c<sub>1</sub> is in live execution (DA-1 Path 3 — from ZP-C D1 + AIT). Corroboration: ⊥ = {&#8869;} (ZP-A CC-2/R3); unbounded surprisal (ZP-C L-INF). (DA-1 &#167; IV — Derived Proposition)'),
        li('Step 3 — Any instantiated execution passes through c<sub>1</sub>. (ZP-C D7 — definitional; c<sub>1</sub> is the first running configuration)'),
        li('Step 4 — c<sub>1</sub> ≠ ⊥. (ZP-C L-RUN — Derived; c<sub>1</sub> has gained execution context not present in c<sub>0</sub> = ⊥; by AX-B1 this is a distinct, nonzero state)'),
        li('Step 5 — No program that executes produces only ⊥ configuration states. (ZP-C TQ-IH — Derived; execution trace τ(p) contains c<sub>1</sub> for any executing program p)'),
        li('Step 6 — In (L, ∨, ⊥), c<sub>1</sub> is an element strictly above ⊥. By ZP-A D2, the transition ⊥ → c<sub>1</sub> is a valid state transition: c<sub>1</sub> = ⊥ ∨ ε<sub>0</sub> for some ε<sub>0</sub> ∈ L with ε<sub>0</sub> > ⊥. This transition is the Binary Snap.'),
        li('Step 7 — The transition is irreversible: algebraically by ZP-A R1 (no subtraction operator); topologically by ZP-B C3 (no continuous return path to 0 in Q<sub>2</sub>). These two grounds are sufficient. Conceptual correspondence: ZP-G AX-G2 (hom(X, 0) = ∅ for X ≠ 0) expresses the same irreversibility in categorical language — ZP-G is downstream of ZP-E and is not a formal dependency of this proof.'),
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
                'CC-2 (&#8869; = {&#8869;}): ZP-J t_exec_iff proves &#8869; is the only occupant of the Quine-atom role (axiom-free); that &#8869; is the AFA set Q = {Q} is argued metatheoretically (see R-AFA). '
                'Both remain commitments: CC-1 is a Conditional Claim, expressed through the Quine-atom role and not removed by it; CC-2 is a Forced Metatheoretic Commitment. '
                'Conceptual correspondence only: ZP-G AX-G2 (downstream of ZP-E; not a formal dependency).'),
    ]

    E += [
        sp(6),
        bridge_box(
            'Remark R-ε₀ — On the Symbol Choice for the Minimum Snap Displacement',
            [
                '<b>Note: this remark draws an informal structural analogy. No formal embedding of '
                'ZP\'s ε₀ into the Cantor-Gentzen ordinal is claimed or established here.</b> '
                'The symbol ε₀ in Step 6 denotes the minimum element of L strictly above ⊥ — the least '
                'witness for the Binary Snap displacement. This symbol is chosen deliberately to coincide '
                'with the Cantor-Gentzen proof-theoretic ordinal.',
                '<b>The Cantor-Gentzen ordinal ε₀.</b> In ordinal arithmetic, ε₀ is the smallest fixed '
                'point of the map α → ω<sup>α</sup>: equivalently, ε₀ = sup{ω, ω<sup>ω</sup>, '
                'ω<sup>ω<sup>ω</sup></sup>, ...}. No finite ω-tower reaches it — it is the minimum ordinal '
                'that cannot be generated from 0 by any finite iteration of the base operation. Gentzen '
                'established that transfinite induction up to ε₀ is necessary and sufficient to prove '
                'Con(PA). By G&#246;del\'s incompleteness theorem, PA cannot prove this from within. The '
                'ordinal ε₀ is therefore the minimum threshold at which finite arithmetic exhausts its own '
                'generative capacity.',
                '<b>The structural analogy.</b> ZP\'s ε₀ occupies an analogous position in the state '
                'lattice. At P₀, c₁ satisfies K(c₁|n)/|c₁| = 1 (ZP-C D1): it is algorithmically '
                'incompressible — no finite external program shorter than c₁ generates it. Just as the '
                'Cantor ε₀ cannot be reached from 0 by any finite ω-tower, ZP\'s ε₀ cannot be reached '
                'from ⊥ by any finite external description. Both name a structurally analogous object: the '
                'minimum witness for a transition that exhausts the finite generative hierarchy below it.',
                '<b>The proof structures are parallel.</b> Gentzen locates the minimum ordinal strength at '
                'which PA cannot describe its own consistency from within. ZP locates the minimum state '
                'displacement at which no external program can hold ⊥ as a static string — where unbounded '
                'surprisal (ZP-C L-INF) and self-containment (ZP-A CC-2) together eliminate any external '
                'interpreter position. In both cases the exhaustion of finite description is not a '
                'deficiency but a structural consequence: the system is necessarily executing at ε₀.',
                '<b>What is not claimed.</b> ZP does not assert that L is an ordinal structure, or that '
                'ZP\'s ε₀ is literally the Cantor ordinal under a formal embedding into the p-adic/lattice '
                'framework. The analogy is motivational: both ε₀s mark the minimum witness for '
                'incompressibility relative to a finite base. A formal embedding — showing that the Cantor '
                'ε₀ is order-isomorphic to or embeds into the p-adic completion of L at ⊥ — remains an '
                'open question and would constitute a strengthening of this claim.',
            ]
        ),
        sp(4),
        bridge_box(
            'Remark R-AFA — Why Foundation is Ruled Out; AFA as Forced Replacement',
            [
                'CC-2 &#8212; the identification of &#8869; with the Quine atom &#8869; = {&#8869;} &#8212; '
                'is a set-theoretic step beyond ZP-A\'s algebra: it is not derived from A1&#8211;A4. The '
                'choice of ZF + AFA over ZF + Foundation that it entails is nonetheless not arbitrary: it is '
                'forced by the membership structure the framework\'s bottom must have.',
                '<b>Foundation rules out the bottom (structural).</b> The framework\'s bottom is the Quine '
                'atom &#8869; = {&#8869;}: it is a member of itself, &#8869; &#8712; &#8869;. ZF + Foundation '
                '(the Axiom of Regularity) forbids exactly this — under a well-founded membership relation no '
                'set lies on a membership cycle of any length, so in particular no set is a member of itself. '
                'This is a theorem of ZF + Foundation, not a framework-specific stipulation; it is '
                'machine-checked here as no_quine_atom / no_membership_cycle '
                '(ZeroParadox/Settheory/Wall.lean, footprint [propext, Quot.sound], choice-free). A '
                'Foundation-respecting universe therefore cannot host &#8869; at all.',
                '<b>The framework\'s readings of &#8869; corroborate this (they do not prove it).</b> R3 '
                '(ZP-A) &#8212; &#8869; = {&#8869;} has no describer position external to itself &#8212; and '
                'L-INF (ZP-C) &#8212; the 2-adic surprisal I(n) = n is unbounded, so no finite interpreter '
                'can hold &#8869; &#8212; each describe an object with no external vantage and unbounded '
                'self-referential depth. That is exactly the profile of a non-well-founded, self-membered '
                'set: the two readings motivate why &#8869; must be the circular object Foundation excludes, '
                'rather than serving as independent proofs of the exclusion.',
                '<b>AFA as the forced replacement.</b> Under ZF + AFA, Quine atoms (x = {x}) are the '
                'minimal non-well-founded objects: the membership structure of &#8869; = {&#8869;} is '
                'circular (&#8869; &#8712; &#8869; &#8712; &#8869; &#8712; &#8230;), so it lives in a '
                'non-well-founded metatheory, and AFA is the minimal such theory that supplies exactly one '
                'of them.',
                '<b>What is machine-checked (the requirements framework).</b> The question of which host '
                'theory can admit &#8869; is reduced to three requirements a host must supply &#8212; '
                'Foundation-freeness, a Quine atom, and its uniqueness &#8212; and largely closed in the '
                'framework\'s set-theory layer (the QuineHost development, '
                'ZeroParadox/Settheory/QuineHost.lean, formalized later in the ZP-J AFA layer). Proved '
                'there: Foundation-freeness is <i>forced</i> for any such host (quineHost_not_wellFounded, '
                'axiom-free); ZF + Foundation is excluded (zfSet_no_quine_bottom &#8212; no set is '
                'self-membered) and Boffa\'s anti-foundation axiom is excluded as too permissive, admitting '
                'a proper class of atoms rather than one (boffa_fails_unique); and the requirements are '
                '<i>realizable</i> &#8212; a concrete one-atom model exhibits them (oneAtom_not_wellFounded, '
                'axiom-free) and AFA is the canonical example (afaStructure_isQuineHost). So the AFA choice '
                'is not merely argued: the forcing and the realizability are settled results.',
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
                'axiom-free). The named falsifier is correspondingly narrow: a differently-motivated '
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
        'Proposition: grounded in ZP-A CC-2 (⊥ = {⊥}) and R3, with ZP-C L-INF as independent corroboration. '
        'The intentional axioms of the system are now: AX-B1 (binary existence), '
        'AX-G1 (initial object), AX-G2 (source asymmetry). AX-1 is retired: its shape is Theorem T-SNAP, and the occurrence '
        'commitment is not on this list because it is a commitment, not a named axiom. '
        'Additional structural commitments are carried as typeclass fields: A4 (bot_join, '
        'ZPSemilattice — standard semilattice algebra), AFAStructure.quine_unique and bot_self_mem '
        '(the Quine-atom role), KleeneStructure.botCode_is_quine (computational closure). Like named axioms these are '
        'assumptions, carried as hypotheses by every theorem that uses them; &#35;print axioms does not surface typeclass fields. '
        'Unlike named axioms they can be cheap to meet: every ZP-A lattice supplies AFAStructure trivially.'))
    E += [
        sp(4),
        bridge_box(
            'T5 (Iterative Forcing Theorem) — restated',
            [
                'T5 (restated). Selection. In the ordinal chart the next rung is the snap re-seeded one step past the current one '
                '(succession_succ), and none lies between two consecutive rungs (ZeroParadox/Ordinal/SnapSuccession.lean &#167; I). '
                'Carried into the two-state lattice by a monotone map that sends the tower&#8217;s stages to c<sub>0</sub> and '
                '&#949;<sub>0</sub> to c<sub>1</sub>, no ordinal below &#949;<sub>0</sub> is sent to c<sub>1</sub>, and every fixed point '
                'of &#945; &#8614; &#969;<super>&#945;</super> is (snap_unconditional, hfp_from_epsilon_zero). '
                'The two faces of &#949;<sub>0</sub> carry the two directions: as the supremum of the stages, every ordinal below '
                '&#949;<sub>0</sub> lies under one of them, so nothing below fires (fundamentalSeq_cofinal); as the least fixed point of '
                '&#945; &#8614; &#969;<super>&#945;</super> it lies below every other, so every landing from &#949;<sub>0</sub> up fires '
                '(epsilon0_min_eq_max). The placement at &#949;<sub>0</sub> is a hypothesis there '
                '(h&#949;<sub>0</sub>), which the Lean names the alignment hypothesis; deriving it from the 2-adic structure is open, as the Classical.choice '
                'inversion conjecture (ZeroParadox/Ordinal/Incompleteness.lean). The rungs are the iterative bottoms; '
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
             'the arc returns to the SAME zero. snap_arc_z2_loop proves the tower starts at 0, that every '
             'finite stage is ≠ 0, and that it converges back to 0; tower_image_loops_to_seed states the '
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
             'taken. Each join adds informational content irreversibly. States are permanently '
             'encoded in the element\'s position in L.'),
        body('<b>Ordinal Direction of State Sequences.</b> The monotone sequence (ZP-A T3) is a structural definition of '
             'directional asymmetry in state ordering. Irreversibility is C3 applied within an instantiation. The framework does not '
             'assume directional asymmetry — it derives it.'),
        body('<b>Causal structure.</b> Every state is fully determined by the joins that produced it. The causal '
             'history of any state is encoded in its position in L. No effect without the join that produced it.'),
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
        'From within instantiation I<sub>n</sub>, an observer occupies exactly one branch of I<sub>n+1</sub>. The other '
        'branches of I<sub>n+1</sub> are not accessible via any path — C3 and monotonicity jointly prohibit it. '
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
         'Its content was split in two: the shape of the Snap is proved, as Theorem T-SNAP (from L-RUN, TQ-IH and the bottom law, with no Lean kernel axioms), '
         'and that the Snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2). '
         'Premises under Premises of T-SNAP (DA-1 insert, &#167; V); given CC-1, the first-step form of the Snap occurring is the hypothesis hocc of t_snap_given.'],
        ['DA-1: Derived Proposition (DP-2 formal grounding)',
         'CLOSED — DP-2 (formal core); CC-2 + L-INF + AIT (corroboration of precondition)',
         'Primary formal grounding: DP-2 (TrackedOutput, Snap.lean &#167;VI) — da1_minimal_path proved '
         'axiom-free. Instantiation of &#8869; moves machine from c<sub>0</sub> to c<sub>1</sub>; output value is irrelevant '
         'to whether execution occurred. '
         'Informal corroboration: ZP-A CC-2 + R3 (structural); ZP-C L-INF (informational); AIT incompressibility (Path 3).'],
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
         'KleeneStructure.botCode_is_quine (computational closure). '
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
         'DP-2 (TrackedOutput, Snap.lean &#167;VI); ZP-A CC-2, R3; ZP-C L-INF',
         'None',
         'Derived Proposition — primary: DP-2 (da1_minimal_path proved axiom-free in Lean). '
         'Informal paths: CC-2/R3 (structural), L-INF (informational), AIT incompressibility (Path 3). '
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
        ['DA-1: Derived Proposition (Path 2 recharacterization)',
         'Valid — DP-2 formal core: da1_minimal_path proved axiom-free in Lean (Snap.lean &#167;VI). '
         'TrackedOutput separates output value from machine state; pre- and post-instantiation states '
         'are provably distinct even when both produce &#8869;. ✓ '
         'ZP-K: da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase) proved in Kleene.lean. '
         'Path 1 is witnessed by da1_closed_concrete, which proves nothing computational; Path 3&#8217;s witness is the '
         'machinePhaseKleene instance&#8217;s botCode_is_quine field, a KleeneStructure requirement, not a second independent proof. '
         'da1_paths_unified carries the two together as a conjunction of witnesses; that they name one structural fact is the framework&#8217;s reading. '
         'Path 2 (informational bridge, L-INF): FOUNDATIONAL COMMITMENT — a missing principle, not a '
         'missing proof. No computability library closes the gap between \'system at P₀\' and \'system is '
         'running.\' Forward paths: new axiom, Chalmers\' implementation notion, or '
         'The Philosophical Question That Started This. ZP-M R-M.1 provides a retrospective structural analysis of why the gap resisted formalization. '
         'DA-1 does not depend on Path 2. '
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
            'Path 1 is witnessed by da1_closed_concrete (ZP-K), which proves IsQuineAtom(&#8869; : MachinePhase) and nothing '
            'computational; Path 3&#8217;s witness is the machinePhaseKleene instance&#8217;s botCode_is_quine field, a KleeneStructure '
            'requirement, not a second independent proof; and '
            'Path 2 is a foundational commitment (a missing principle, not a missing proof). Remark '
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
