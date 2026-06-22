"""
Build ZP-K Illustrated Companion
Version 1.11 | May 2026
v1.10: four_way_diagram — removed the redundant internal caption String that overlapped the bottom "Computation (Kleene)" box (Diagram Rule 4; the external ccaption already captions the diagram).
v1.9: FMC precision (sweep Step 4) — DA-1 Path 1 line splits the axiom-free structural fixed point (what ZP-J proved) from the literal ⊥ = {⊥} (the ZF+AFA setting).
v1.8: Strip version number from companion footer.
v1.7: Fix four_way_diagram String() HTML entity encoding — raw Unicode for ⊥, ≤, ∨.
v1.6: Add "Self-Reference: Fixed Point vs. Oscillation" section — Gödel diagonal lemma, fixed-point vs. liar-type self-reference, ZPE irreversibility excludes oscillation.
v1.5: Strip version number from disclaimer cross-reference to ZP-K formal document.
v1.4: AR fix — "⊥ in every formal language" → "⊥ in the four formal languages of this
framework" — scopes the cross-framework identity claim to the four ZP languages.
v1.3: "IS the Turing machine" → "IS an instance of a Turing machine" — preserves the
direct comparison while distinguishing structural instantiation from literal identity.
v1.2: Disclaimer updated — "formal ontology" replaced with "formal document".
v1.0: Initial release. Covers T-COMP (four-way equivalence: Quine atom = bottom = join
identity = Kleene fixed point), the computational Quine, and da1_closed_concrete
(DA-1 formally closed — ⊥ instantiates a Turing machine in ground state).
v1.1: Added explicit note that Kleene's theorem is an existence proof, not a convergent
iteration — the halting question does not arise.
Formal doc: ZP-K Computational Grounding v1.0.
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Polygon
from reportlab.graphics import renderPDF


def four_way_diagram():
    """Diamond diagram: four descriptions of ⊥ as the same structural role."""
    dw, dh = TW, 3.2 * inch
    d = Drawing(dw, dh)

    cx, cy = dw / 2, dh / 2

    # Central circle
    cr = 38
    d.add(Circle(cx, cy, cr, fillColor=TEAL, strokeColor=TEAL, strokeWidth=0))
    d.add(String(cx - 22, cy + 5,  'The Null', fontSize=8.5, fontName='DV-B', fillColor=WHITE))
    d.add(String(cx - 18, cy - 8, 'Ground', fontSize=8.5, fontName='DV-B', fillColor=WHITE))
    d.add(String(cx - 12, cy - 20, '⊥', fontSize=10,  fontName='DV-B', fillColor=WHITE))

    bw, bh = 1.3 * inch, 0.72 * inch

    def node(bx, by, color, lite, label, sub1, sub2, ax1, ay1, ax2, ay2):
        d.add(Rect(bx, by, bw, bh, fillColor=lite, strokeColor=color, strokeWidth=1.5,
                   rx=4, ry=4))
        d.add(String(bx + 8, by + bh - 15, label,
                     fontSize=9, fontName='DV-B', fillColor=color))
        d.add(String(bx + 8, by + bh - 27, sub1,
                     fontSize=7.5, fontName='DV-I', fillColor=GREY_TEXT))
        d.add(String(bx + 8, by + bh - 38, sub2,
                     fontSize=7.5, fontName='DV-I', fillColor=GREY_TEXT))
        # Arrow toward center
        d.add(Line(ax1, ay1, ax2, ay2, strokeColor=color, strokeWidth=1.5))
        dx, dy = ax2 - ax1, ay2 - ay1
        ln = (dx*dx + dy*dy) ** 0.5
        if ln > 0:
            ux, uy = dx/ln, dy/ln
            px, py = -uy, ux
            hs = 6
            d.add(Line(ax2, ay2,
                       ax2 - hs*ux + hs*0.5*px, ay2 - hs*uy + hs*0.5*py,
                       strokeColor=color, strokeWidth=1.5))
            d.add(Line(ax2, ay2,
                       ax2 - hs*ux - hs*0.5*px, ay2 - hs*uy - hs*0.5*py,
                       strokeColor=color, strokeWidth=1.5))

    # Top: Set theory / AFA
    node(cx - bw/2, cy + cr + 10, INDIGO, INDIGO_LITE,
         'Set Theory (AFA)', '⊥ = {⊥}', 'Quine atom',
         cx, cy + cr + 10, cx, cy + cr + 2)

    # Bottom: Computation / Kleene
    node(cx - bw/2, cy - cr - 10 - bh, TEAL, TEAL_LITE,
         'Computation (Kleene)', 'eval c = f(c)', 'Fixed point',
         cx, cy - cr - 10, cx, cy - cr - 2)

    # Left: Order theory
    node(cx - cr - 14 - bw, cy - bh/2, COMP_BLUE, colors.HexColor('#E3F0FA'),
         'Order Theory', '⊥ ≤ x for all x', 'Minimum element',
         cx - cr - 14, cy, cx - cr - 2, cy)

    # Right: Algebra
    node(cx + cr + 14, cy - bh/2, COMP_AMBER, AMBER_LITE,
         'Algebra (A4)', '⊥ ∨ x = x', 'Join identity',
         cx + cr + 14, cy, cx + cr + 2, cy)

    return d

def four_way_table():
    """Table of the four descriptions."""
    hdr = [Paragraph('Language', CS['kr_hdr']),
           Paragraph('Property', CS['kr_hdr']),
           Paragraph('Intuition', CS['kr_hdr'])]
    rows = [
        ['Set theory (AFA)',
         '&#8869; = {&#8869;} — Quine atom',
         '⊥ is its own sole member; no external interpreter exists'],
        ['Order theory (ZP-A)',
         '&#8869; &#8804; x for all x — minimum',
         '⊥ is below everything; the universal starting point'],
        ['Algebra (ZP-A A4)',
         '&#8869; &#8744; x = x for all x — join identity',
         '⊥ contributes nothing to any join; the additive zero'],
        ['Computation (Kleene)',
         'eval botCode = selfApply botCode — fixed point',
         '⊥ is its own program; no shorter external generator exists'],
    ]
    data = [hdr] + [[Paragraph(fix(r[0]), CS['kr_body']),
                     Paragraph(fix(r[1]), CS['kr_body']),
                     Paragraph(fix(r[2]), CS['kr_body'])] for r in rows]
    ts = TableStyle([
        ('BACKGROUND',    (0,0),(-1,0),  TEAL),
        ('ROWBACKGROUNDS',(0,1),(-1,-1), [WHITE, TEAL_LITE]),
        ('BOX',           (0,0),(-1,-1), 0.5, TEAL),
        ('LINEBELOW',     (0,0),(-1,0),  0.5, TEAL),
        ('INNERGRID',     (0,1),(-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0),(-1,-1), 5), ('BOTTOMPADDING',(0,0),(-1,-1), 5),
        ('LEFTPADDING',   (0,0),(-1,-1), 6), ('RIGHTPADDING', (0,0),(-1,-1), 6),
        ('VALIGN',        (0,0),(-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW*0.22, TW*0.30, TW*0.48])
    t.setStyle(ts); return t

VERSION = '1.11'
FIRST_RELEASED = 'April 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT,
                            'ZP-K_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState(); canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-K Companion  |  Computational Grounding  |  ' + version_date())
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
                            title='ZP-K Illustrated Companion', author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    hdr_ts = TableStyle([('BACKGROUND',(0,0),(-1,-1),TEAL),
                         ('TOPPADDING',(0,0),(-1,-1),8),('BOTTOMPADDING',(0,0),(-1,-1),8),
                         ('LEFTPADDING',(0,0),(-1,-1),10)])
    hdr = Table([[Paragraph('ZP-K Illustrated Companion',
                            ParagraphStyle('hdr',fontName='DV-B',fontSize=11,textColor=WHITE))]],
                colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E += [hdr, sp(6),
          Paragraph('Four Languages, One Structure', CS['title']),
          Paragraph('The Computational Grounding of &#8869;', CS['subtitle']),
          Paragraph('ZP Companion | ' + version_line(FIRST_RELEASED, VERSION), CS['meta']),
          Paragraph(
              'This companion explains the ideas in plain language. It is not the formal '
              'document — every claim here restates a result already proved in the technical '
              'document ZP-K Computational Grounding. Consult that document for the '
              'authoritative mathematics.', CS['disc'])]

    # What Is ZP-K Doing?
    E.append(Paragraph('What Is ZP-K Doing?', CS['h1']))
    E.append(cbody(
        'ZP-J proved that the Quine atom (set-theoretic self-reference) and the bottom element '
        '(order-theoretic minimum) are the same object. ZP-K adds a fourth language: '
        'computability theory. It proves that there is a fourth description of ⊥, this time '
        'in terms of Turing machines and Kleene\'s second recursion theorem — and that all '
        'four descriptions name the same structural role.'))
    E.append(cbody(
        'The consequence for DA-1 is direct: ⊥ is not a description of a Turing machine. '
        '⊥ IS an instance of a Turing machine — specifically its ground state, serving as its own program. '
        'The "description vs. execution" gap that DA-1 had to close is structurally '
        'dissolved: there is no gap, because ⊥ in the four formal languages of this framework '
        'is shown to be the same structural object — and that structural identity is what dissolves the gap.'))
    E.append(sp(4))

    # What Is a Kleene Fixed Point?
    E.append(Paragraph('What Is a Kleene Fixed Point?', CS['h1']))
    E.append(cbody(
        'Kleene\'s second recursion theorem is a foundational result in computability theory. '
        'Informally, it says: for any way of transforming programs, there exists a program '
        'that is a fixed point of that transformation — a program whose behavior is the same '
        'before and after the transformation is applied.'))
    E.append(cbody(
        'A Kleene fixed point of self-application is called a computational Quine: a program c '
        'such that running c produces the same output as running c on its own source code. '
        'In other words, c\'s behavior is determined entirely by c itself — no external program '
        'shorter than c generates it. The program IS its own description.'))
    E.append(cbody(
        'This is not a running computation that might loop forever. Kleene\'s theorem is an '
        'existence proof — it guarantees the fixed point exists before any execution takes '
        'place, by a direct construction, not by iterating toward a limit. The question '
        '"will it halt?" does not arise: the fixed point is identified by the theorem '
        'itself, not discovered by running a potentially divergent process.'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy — A self-printing program', [
        'A Quine program in computer science is a program that, when run, outputs its own '
        'source code. It needs no external file to read — the source is baked in. '
        'Kleene\'s theorem guarantees that for any computable transformation, such a fixed '
        'point always exists. The computational Quine is the formal expression of ⊥ = {⊥} '
        'in the language of programs: c is its own program, just as ⊥ is its own member.',
    ]))
    E.append(sp(8))

    # The four-way equivalence
    E.append(Paragraph('T-COMP: The Four-Way Equivalence', CS['h1']))
    E.append(cbody(
        'ZP-K\'s central theorem, T-COMP (Computational Grounding), establishes that the '
        'four descriptions below are all equivalent — they all identify the same object:'))
    E.append(four_way_diagram())
    E.append(ccaption(
        'The null ground element ⊥ at the center, described in four formal languages. '
        'Each arrow represents a proved equivalence. T-COMP proves all four identify the same object.'))
    E.append(sp(4))
    E.append(four_way_table())
    E.append(sp(6))
    E.append(cbody(
        'The key insight is that the four descriptions are not independent convergences — '
        'they are projections of a single structural identity. The Kleene fixed-point property '
        'is not analogous to the AFA Quine atom property. They are the same property, stated '
        'in different mathematical vocabularies. ZP-K makes this explicit by constructing a '
        'KleeneStructure — a formal bridge connecting the set-theoretic (AFAStructure) '
        'and computational (Kleene fixed-point) descriptions.'))
    E.append(sp(4))
    E.append(remember_box(
        'Remember: T-COMP is not saying that set theory and computability theory are the same. '
        'It is saying that the specific structural role played by ⊥ — self-containment, '
        'minimality, join-identity — happens to be expressible in all four languages, '
        'and that the expressions are provably equivalent. The equivalence is local to this '
        'structural role, not a global identification of the frameworks.'))
    E.append(sp(8))

    # DA-1 Formally Closed
    E.append(Paragraph('DA-1 Formally Closed', CS['h1']))
    E.append(cbody(
        'DA-1 (Instantiation as Execution) had three informal argument paths in ZP-E:'))
    E.append(cbody(
        '<b>Path 1 (Structural — AFA):</b> Nothing external to ⊥ can execute ⊥. Therefore '
        '⊥ must execute itself. ZP-J proved axiom-free that ⊥ is the unique self-containing element (the structural fixed point); that this is the literal ⊥ = {⊥} holds in the ZF+AFA setting. '
        '<b>Now IN LEAN SCOPE via ZP-K:</b> the KleeneStructure instance for MachinePhase '
        'includes an AFAStructure instance (machinePhaseAFA). The AFA self-containment of ⊥ '
        'is not just argued — it is machine-checked.'))
    E.append(cbody(
        '<b>Path 2 (Informational — L-INF):</b> The surprisal of ⊥ is unbounded — no finite '
        'interpreter can hold it. This eliminates the static-description alternative. '
        '<b>Remains outside Lean scope:</b> "unbounded surprisal implies necessarily executing" '
        'is an ontological bridge claim that type theory cannot directly verify. It is a '
        'well-motivated philosophical argument, not a formal proof.'))
    E.append(cbody(
        '<b>Path 3 (Computational — Kleene):</b> No shorter program generates ⊥. Therefore '
        '⊥ is its own program — a Kleene fixed point of self-application. '
        '<b>Now IN LEAN SCOPE via ZP-K:</b> machinePhaseKleene provides botCode_is_quine — '
        'a concrete computational Quine whose existence is guaranteed by Kleene\'s second '
        'recursion theorem. The code IS its own program.'))
    E.append(sp(4))
    E.append(key_result_box(
        'da1_closed_concrete (ZPK.lean)',
        'IsQuineAtom(&#8869; : MachinePhase) — proved in Lean 4. '
        'The initial machine state c&#8320; is self-containing and self-executing — not a '
        'static description awaiting an external interpreter. '
        'DA-1 Paths 1 and 3: IN LEAN SCOPE. Path 2: outside Lean scope (ontological bridge). ✓'))
    E.append(sp(6))
    E.append(cbody(
        'What does it mean that ⊥ IS an instance of a Turing machine in its ground state? '
        'In ZP-C, the model distinguishes c₀ (the initial configuration, before any '
        'instruction executes) from c₁ (after the first instruction fetch). '
        'DP-2 (ZP-E) proved that these are distinct machine states even when both '
        'produce the same output value. The Kleene fixed-point result says: c₀ is not '
        'waiting for someone to press "run." It is already executing — the execution and '
        'the description are the same act. T-COMP makes this precise: in all four languages, '
        '⊥ satisfies the self-referential fixed-point condition that precludes any external '
        'initiating agent.'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy — The light that sees itself', [
        'Consider a camera that, instead of photographing external scenes, photographs only '
        'its own sensor. The image it produces is the state of the sensor; the sensor\'s '
        'state is the image. There is no external scene being captured — the camera IS '
        'the scene. ⊥ as a Kleene fixed point has exactly this structure: the program '
        'that runs is the program that describes what runs. Description and execution '
        'are the same act.',
    ]))
    E.append(sp(8))

    # Purity note
    E.append(Paragraph('A Note on Proof Purity', CS['h1']))
    E.append(cbody(
        'The computability machinery in ZP-K (Kleene\'s theorem, Roger\'s fixed-point theorem) '
        'requires classical logic — a standard dependency for any theorem that uses '
        'Mathlib\'s computability library, not a novel Zero Paradox commitment. '
        'The ZP-A, ZP-J, and core ZP-E results remain free of this dependency.'))
    E.append(cbody(
        'This is analogous to a proof that invokes the intermediate value theorem: IVT '
        'itself depends on completeness of the reals, which depends on choice. Using IVT '
        'does not make your proof "non-constructive" in any meaningful sense — it means '
        'you are working in the standard mathematical setting. ZP-K\'s classical footprint '
        'is of the same character.'))
    E.append(sp(4))
    E.append(remember_box(
        'Remember: ZP-K closes DA-1 Paths 1 and 3 formally. It does not claim to resolve '
        'the description-execution gap by philosophical argument. It proves, in machine-checked '
        'Lean 4, that the structural role ⊥ plays in the algebra is the same role it plays '
        'in AFA set theory and in computability theory. The gap was never a gap — '
        '⊥ in all three settings is the same self-referential fixed point.'))
    E.append(sp(8))

    # ── Fixed-Point vs. Oscillation ───────────────────────────────────────────
    E.append(Paragraph('Self-Reference: Fixed Point vs. Oscillation', CS['h1']))
    E.append(cbody(
        'Not all self-reference is the same. The liar paradox &#8212; "this sentence is '
        'false" &#8212; produces a statement x with the property x = NOT x. In Boolean '
        'logic this has no fixed point: the sequence true, false, true, false, &#8230; '
        'oscillates without resolving. This is the liar structure.'))
    E.append(cbody(
        'G&#246;del&#8217;s incompleteness proof (1931) uses a different kind of '
        'self-reference. Using the diagonal lemma &#8212; a fixed-point theorem for formal '
        'languages &#8212; he constructed a sentence G satisfying G &#8596; &#172;Prov(G): '
        '"this sentence is not provable in PA." The key move: he changed the predicate from '
        '"true" to "provable." Provability is asymmetric in a way truth is not, so G does '
        'not oscillate. In a consistent system, G is true in the standard model of arithmetic '
        'but unprovable in PA &#8212; a fixed point, not an oscillation.'))
    E.append(cbody(
        'ZP-K&#8217;s construction achieves the same structural form in the setting of &#8869;. '
        '&#8869; = {&#8869;} (the AFA Quine atom, proved via da1_closed_concrete) is '
        'self-containing, not self-negating: x = f(x) where f is set-membership, not '
        'x = NOT x. The Kleene fixed point gives the same structure computationally: '
        'a code whose behavior is determined entirely by itself. Both witnesses resolve '
        'at a fixed point. Neither oscillates.'))
    E.append(cbody(
        'ZP-E&#8217;s t_snap_irreversible goes further: it formally proves that the '
        'liar-type trajectory is structurally impossible in this framework, not merely '
        'absent. Once c&#8320; transitions to c&#8321;, the semilattice axioms guarantee '
        'no path returns. The sequence c&#8320; &#8594; c&#8321; &#8594; c&#8320; &#8594; &#8230; '
        'cannot occur &#8212; the algebra forbids it.'))
    E.append(sp(4))
    E.append(remember_box(
        'This is a structural observation, not a claim that ZP proves G&#246;del&#8217;s '
        'theorems. G&#246;del applied the diagonal lemma in formal arithmetic; '
        'ZP-K&#8217;s construction achieves the same structural form &#8212; '
        'x = f(x) rather than x = &#172;x &#8212; for the bottom element &#8869;. '
        'Both constructions use x = f(x) rather than x = &#172;x, and both yield '
        'a stable fixed point rather than an oscillating sequence.'))
    E.append(sp(8))

    E.append(key_result_box(
        'Key Result — ZP-K',
        'T-COMP: IsQuineAtom(q) ↔ q = &#8869; ∧ (∀ x, q &#8744; x = x). '
        'The four-way equivalence (AFA / order / algebra / Kleene) is proved. '
        'da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase). '
        'DA-1 Paths 1 and 3 IN LEAN SCOPE. ✓'))
    E.append(sp(6))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
