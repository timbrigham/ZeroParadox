"""
Build ZP-A Illustrated Companion (v1.3)
Covers: join-semilattice, partial order, Hasse diagram, one-directional transitions,
monotonicity (T3), bottom-as-constituent (T2), four concrete examples.
New in v1.3: CC-2 self-containment of ⊥ (Quine atom, ZF+AFA); R3 (DA-1 follows from CC-2).
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Circle
from reportlab.graphics import renderPDF

def hasse_diagram():
    """⊥ at bottom (amber), states in two rows above, lines showing the order."""
    dw, dh = TW, 3.2 * inch
    d = Drawing(dw, dh)
    r = 22

    y_bot = 0.55 * inch
    y_mid = 1.55 * inch
    y_top = 2.55 * inch
    cx    = dw / 2

    # Bottom: ⊥
    d.add(Circle(cx, y_bot, r, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(String(cx - 6, y_bot - 6, '⊥', fontSize=15, fontName='DV-B', fillColor=WHITE))

    # Middle: 3 states
    mxs = [cx - 1.55*inch, cx, cx + 1.55*inch]
    for mx in mxs:
        d.add(Line(cx, y_bot + r, mx, y_mid - r, strokeColor=GREY, strokeWidth=1))
        d.add(Circle(mx, y_mid, r, fillColor=COMP_BLUE, strokeColor=COMP_BLUE, strokeWidth=0))
        d.add(String(mx - 5, y_mid - 5, 'S', fontSize=12, fontName='DV-B', fillColor=WHITE))

    # Top: 4 states
    txs = [cx - 2.2*inch, cx - 0.72*inch, cx + 0.72*inch, cx + 2.2*inch]
    connections = [(0,[0,1]),(1,[0,1,2]),(2,[0,1,2]),(3,[1,2])]
    for ti, mi_list in connections:
        tx = txs[ti]
        for mi in mi_list:
            d.add(Line(mxs[mi], y_mid + r, tx, y_top - r, strokeColor=GREY, strokeWidth=1))
        d.add(Circle(tx, y_top, r, fillColor=COMP_BLUE, strokeColor=COMP_BLUE, strokeWidth=0))
        d.add(String(tx - 5, y_top - 5, 'S', fontSize=12, fontName='DV-B', fillColor=WHITE))
        d.add(String(tx - 5, y_top + r + 4, '...', fontSize=10, fontName='DV', fillColor=GREY))

    # Legend
    lx = dw - 1.7*inch; ly = 0.5 * inch
    d.add(Circle(lx, ly + 12, 9, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(String(lx + 14, ly + 7, '= bottom (additive identity)', fontSize=7.5,
                 fontName='DV', fillColor=BLACK))
    d.add(Circle(lx, ly - 6, 9, fillColor=COMP_BLUE, strokeColor=COMP_BLUE, strokeWidth=0))
    d.add(String(lx + 14, ly - 11, 'States in L', fontSize=7.5, fontName='DV', fillColor=BLACK))
    return d

def transition_diagram():
    """⊥ → S1 → S2 → S3 → ... with dashed no-return arrow below."""
    dw, dh = TW, 1.5 * inch
    d = Drawing(dw, dh)
    r = 24; cy = dh * 0.65; gap = 1.32 * inch; x0 = 0.42 * inch

    labels    = ['⊥', 'S1', 'S2', 'S3']
    fills     = [COMP_AMBER,  COMP_BLUE, COMP_BLUE, COMP_BLUE]
    xs        = [x0 + i * gap for i in range(4)]

    for i, (lbl, col, x) in enumerate(zip(labels, fills, xs)):
        d.add(Circle(x, cy, r, fillColor=col, strokeColor=col, strokeWidth=0))
        ox = x - (9 if lbl != '⊥' else 6)
        d.add(String(ox, cy - 5, lbl, fontSize=11, fontName='DV-B', fillColor=WHITE))
        if i < 3:
            nx = xs[i+1]
            ax1, ax2 = x + r, nx - r
            d.add(Line(ax1, cy, ax2, cy, strokeColor=BLACK, strokeWidth=1.8))
            d.add(Line(ax2-7, cy-4, ax2, cy, strokeColor=BLACK, strokeWidth=1.8))
            d.add(Line(ax2-7, cy+4, ax2, cy, strokeColor=BLACK, strokeWidth=1.8))

    d.add(String(xs[-1] + r + 10, cy - 5, '...', fontSize=14, fontName='DV', fillColor=GREY))

    # Dashed return line
    dy = cy - r - 18
    x1, x2 = xs[-1] + r + 8, xs[0] - r - 4
    cur = x1
    while cur > x2 + 10:
        d.add(Line(cur, dy, cur - 10, dy, strokeColor=RED, strokeWidth=1.5))
        cur -= 15
    d.add(Line(x2+8, dy-5, x2, dy, strokeColor=RED, strokeWidth=1.5))
    d.add(Line(x2+8, dy+5, x2, dy, strokeColor=RED, strokeWidth=1.5))

    mid = (x1 + x2) / 2
    d.add(String(mid - 46, dy - 14, '✗ No return path', fontSize=9,
                 fontName='DV-B', fillColor=RED))
    return d

def build():
    out_path = os.path.join(PROJECT_ROOT,
                            'ZP-A_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState(); canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-A Companion  |  Lattice Algebra  |  April 2026  |  v1.3')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
                            title='ZP-A Illustrated Companion', author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # Header banner
    hdr_ts = TableStyle([('BACKGROUND',(0,0),(-1,-1),COMP_BLUE),
                         ('TOPPADDING',(0,0),(-1,-1),8),('BOTTOMPADDING',(0,0),(-1,-1),8),
                         ('LEFTPADDING',(0,0),(-1,-1),10)])
    hdr = Table([[Paragraph('ZP-A Illustrated Companion',
                            ParagraphStyle('hdr',fontName='DV-B',fontSize=11,textColor=WHITE))]],
                colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E += [hdr, sp(6),
          Paragraph('How state accumulates without ever going backwards', CS['title']),
          Paragraph('Lattice Algebra | Version 1.3', CS['subtitle']),
          Paragraph('ZP Companion | April 2026', CS['meta']),
          Paragraph(
              'This companion explains the ideas in plain language with diagrams and real-world '
              'examples. It is not the formal ontology — every claim here restates a result '
              'already proven in the corresponding technical document. Consult that document for '
              'the authoritative mathematics.', CS['disc'])]

    # What Is ZP-A Doing?
    E.append(Paragraph('What Is ZP-A Doing?', CS['h1']))
    E.append(cbody(
        'ZP-A establishes the algebraic rules for how states behave in the Zero Paradox framework. '
        'It uses a structure called a <b>join-semilattice</b> — the simplest algebraic system '
        'that can describe accumulation without subtraction. Think of it as a ledger where entries '
        'can only be added, never erased.'))
    E.append(cbody(
        'The central object is the triple (L, ∨, ⊥): a set of states L, a joining '
        'operation ∨ that combines two states into a larger one, and a special '
        '<b>bottom element</b> ⊥ that represents the absolute starting point. Four axioms '
        '(A1–A4) say that joining is associative, commutative, idempotent, and that ⊥ '
        'is a neutral element.'))
    E.append(example_box('Real-world example — Bank ledger', [
        'Think of ⊥ as a brand-new account with zero balance. Every transaction adds to the '
        'ledger. There is no undo operation — once a deposit is recorded, the total can only '
        'stay the same or grow. The join-semilattice captures exactly this: accumulation without '
        'reversal.',
    ]))
    E.append(remember_box(
        'Remember: The bank account is just one way to picture it. The framework applies to any '
        'system where state can only accumulate — energy, information, or any other monotone '
        'quantity.'))
    E.append(sp(4))

    # Partial Order
    E.append(Paragraph('The Partial Order: States Have a Natural Height', CS['h1']))
    E.append(cbody(
        'From the four axioms, a <b>partial order</b> falls out automatically: state x is "below" '
        'y if joining x with y just gives y back — y already contains everything x does. '
        '⊥ is always at the very bottom.'))
    E.append(hasse_diagram())
    E.append(ccaption(
        'Hasse diagram: partial order on L. Arrows point upward. ⊥ (amber) is the universal '
        'minimum. Every state sits above ⊥.'))
    E.append(sp(4))
    E.append(example_box('Real-world example — Biological complexity', [
        'Think of ⊥ as the simplest possible organism. More complex life forms are "above" '
        'simpler ones: they contain everything the simpler form has, plus more. In this abstract '
        'sense, complexity only accumulates.',
    ]))
    E.append(sp(6))

    # No Subtraction
    E.append(Paragraph('No Subtraction', CS['h1']))
    E.append(cbody(
        'The join-semilattice deliberately omits subtraction. State content can only accumulate, '
        'never be removed. Every valid transition moves upward.'))
    E.append(transition_diagram())
    E.append(ccaption(
        'State transitions are one-directional. The red dashed line — a return path — '
        'does not exist in this algebra.'))
    E.append(sp(6))

    # Key Results
    E.append(key_result_box(
        'Key Result: Monotonicity is a Theorem — not an Assumption (T3)',
        'For any state sequence built by joining, S₀ ≤ S₁ ≤ S₂ ≤ '
        '… This is derived from the axioms, not assumed. The sequence can only go up.'))
    E.append(sp(6))
    E.append(key_result_box(
        'Key Result: ⊥ is a Constituent of Every State (T2)',
        '⊥ ≤ x for all x in L. ⊥ is not a void that states escape from — '
        'it is algebraically present in every state. Zero is not absence; it is the universal base.'))
    E.append(sp(6))
    E.append(example_box('Real-world example — Silence in music', [
        'Silence is not the absence of the piece — it is the baseline from which every note '
        'departs. Every musical state contains silence as its foundation. The join-semilattice '
        'captures this: ⊥ is a constituent of every state.',
    ]))
    E.append(sp(8))

    # More Examples
    E.append(Paragraph('More Examples of Join-Semilattices', CS['h1']))
    E.append(cbody(
        'A join-semilattice appears in many mathematical and everyday settings. Here are four '
        'concrete instantiations of (L, ∨, ⊥), each satisfying A1–A4.'))
    E.append(example_box('Example — Power set with union', [
        'Let X be any set. Take L = P(X) (the collection of all subsets of X), ∨ = ∪ '
        '(set union), and ⊥ = ∅ (the empty set). Union is associative, commutative, '
        'idempotent (A ∪ A = A), and the empty set is a neutral element (∅ ∪ A = A). '
        'The induced order is inclusion: A ≤ B iff A ∪ B = B, i.e. A ⊆ B. Every '
        'element of L sits above ∅.',
    ]))
    E.append(sp(4))
    E.append(example_box('Example — [0, ∞) with maximum', [
        'Take L = [0, ∞), ∨ = max (the larger of two values), and ⊥ = 0. Maximum '
        'is associative, commutative, idempotent (max(x, x) = x), and 0 is a neutral element '
        '(max(0, x) = x for x ≥ 0). The induced order is the usual ≤ on real numbers: '
        'x ≤ y iff max(x, y) = y. Note: addition would not work here — x + x = 2x '
        '≠ x, violating idempotency (A3).',
    ]))
    E.append(sp(4))
    E.append(example_box('Example — Functions with pointwise maximum', [
        'Let X be any set. Take L to be the set of all functions f: X → [0, ∞), '
        '∨ = pointwise maximum ((f ∨ g)(x) = max(f(x), g(x))), and ⊥ = the zero '
        'function. All four axioms hold pointwise. The induced order is f ≤ g iff f(x) '
        '≤ g(x) for all x ∈ X. This is a function-space version of the previous '
        'example — one level up in abstraction.',
    ]))
    E.append(sp(4))
    E.append(example_box('Example — Document edit history', [
        'Open a document and start making edits. Even hitting Backspace does not erase from the '
        'edit record — it adds a new deletion event to the history. Each saved state of the '
        'document sits above all states that preceded it. The history can only grow. The "join" '
        'of two document states is the later one (or the merge if branches exist). The ⊥ '
        'state is the empty document. No edit operation removes from the record.',
    ]))
    E.append(sp(8))
    # CC-2: Self-Containment of ⊥
    E.append(Paragraph('&#8869; Contains Itself (CC-2)', CS['h1']))
    E.append(cbody(
        'Every state sits above &#8869;. But what exactly <i>is</i> &#8869;? The standard '
        'answer: the additive identity, the algebraic zero, the starting point. ZP-A v1.6 '
        'adds a sharper answer: &#8869; is a <b>Quine atom</b> — a set that equals its '
        'own singleton.'))
    E.append(cbody(
        'Formally: &#8869; = {&#8869;}. The collection of all objects bearing the structural '
        'property of &#8869; is &#8869; itself. There is no multiplicity. Infinitely many '
        'indistinguishable &#8869; instances collapse, by set extensionality, into the '
        'single object &#8869;.'))
    E.append(example_box('Why this matters', [
        'Can there be two "copies" of &#8869; that are somehow different? A Quine atom '
        'says no. Any object identical to &#8869; in all structural respects IS &#8869;. '
        'There is nothing external to &#8869; by which to distinguish copies.',
        'A label requires a labeller outside it. &#8869; = {&#8869;} has no outside. '
        'This is what grounds the execution claim in ZP-E (DA-1): the snap at P&#8320; '
        'is not a description being read — it is the only thing that can happen to a '
        'self-containing object at the limit of its own description.',
    ]))
    E.append(remember_box(
        'Technical note (CC-2): the Quine atom property requires replacing the classical Axiom '
        'of Foundation (which rules out self-containing sets) with Aczel\'s Anti-Foundation Axiom '
        '(AFA). The Axiom of Choice is not assumed. This is a framework-level commitment — A1&#8211;A4 '
        'are unaffected, but it changes what &#8869; is allowed to be.'))
    E.append(sp(8))

    E.append(remember_box(
        'Remember: ZP-A makes no claims about topology, probability, or physics. It only '
        'establishes the algebraic skeleton. Everything it claims can be verified by a reader '
        'fluent in algebra without consulting any other document.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
