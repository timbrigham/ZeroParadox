# Axiom Profile — what the choice footprint actually says

Ride-along for `ZeroParadox/AxiomProfile.lean`. The `.lean` file is the checkable artifact — build it
and read the `#print axioms` output. This file carries the argument about how to read that output,
which is where the mistakes have been.

## The core is choice-free, and "choice-free" has two strengths

**The central theorem — the Binary Snap (T-SNAP) — depends on no axioms at all.** The lattice algebra
(ZP-A) and the Quine-atom self-reference keystone (ZP-J) are likewise choice-free.

Keep the two tiers apart:

* `does not depend on any axioms` — T-SNAP, the lattice, the Quine atom. Not even propositional
  extensionality.
* `[propext, Quot.sound]` — choice-free, but using propositional extensionality and quotient
  soundness, both Lean 4 standard.

## Where `Classical.choice` enters

It appears in the layers that *realize* these results inside standard analytic structures — p-adic
topology, Hilbert space, ordinals, computability, category theory — **mostly** inherited from
Mathlib's classically-built libraries, shown in § II for honest contrast.

⚠ **Not entirely inherited (measured), and on the premise in `ZeroParadox/Category/ChoiceCannotBe.lean`
§ IV not entirely removable (reduced).** The measurements below name the axioms each proof uses, and
reading the source settles where they come from; necessity rests on the two reductions, as the next
paragraphs say:

| measured | footprint |
|---|---|
| `no_witness_of_nontrivial` | `[propext, Classical.choice, Quot.sound]` |
| `no_witness_of_fixedPointFree` | *does not depend on any axioms* |
| `fixedPointFree_of_nontrivial` | `[propext, Classical.choice, Quot.sound]` |
| `wem_of_fixedPointFree` | `[propext, Quot.sound]` |
| `em_of_wellOrder_comparable` | `[propext, Quot.sound]` |

**Not inherited:** the category-theory face takes its choice from a bare `classical` written in
framework source (`ZeroParadox/Category/Lawvere.lean`), not from Mathlib.

⚠ **Do not read `no_witness_of_fixedPointFree`'s axiom-freedom as evidence the choice is avoidable.**
It is not a purer proof of the same statement — it *takes* a fixed-point-free map as a hypothesis,
where `fixedPointFree_of_nontrivial` *constructs* one. Purity of the consumer says nothing about the
supplier, and composing them returns `[propext, Classical.choice, Quot.sound]`. `LawvereTaboo.lean`
§ III reduces the general statement to weak excluded middle, so the `classical` there is
**essential** in the sense, and on the premise, of `ZeroParadox/Category/ChoiceCannotBe.lean` § IV.

**Reductions, not measurements:** `wem_of_fixedPointFree` and `em_of_wellOrder_comparable` reduce
two principles to taboos, and they are themselves choice-free — a reduction that used choice would
establish nothing. What they make essential, and the premise it rests on, is stated once in
`ZeroParadox/Category/ChoiceCannotBe.lean` § IV.

⚠⚠ **Provenance and necessity are independent axes.** The two reductions sit on *opposite* sides
of provenance: `fixedPointFree_of_nontrivial` spends the framework's own bare `classical`, while
well-order comparability spends **Mathlib's**, in `InitialSeg.total`. **So, on § IV's premise, an
inherited dependence can be essential**, and *inherited* is not a synonym for *removable*.

| | own | inherited |
|---|---|---|
| **essential** (on § IV's premise) | `fixedPointFree_of_nontrivial` | well-order comparability |
| **open** | — | the remaining analytic layers |

⚠ **A footprint measurement can never establish necessity.** `#print axioms` reports what a proof
used, not what a proof must use. The accidental side needs an **exhibited clean proof**; the essential
side needs a **reduction**. That asymmetry is why provenance ("not inherited") is settled by the
footprint table above read against the source, and the two reductions are the evidence on the
necessity side, which becomes "not removable" only on § IV's premise.

Whether the *remaining* analytic-layer dependence is removable is genuinely open — see the README
Question Register and the `choice-probe` experiment, which found it mostly incidental in the one layer
classified so far. None of it is load-bearing for any ZP *claim*: what the framework asserts is proved
without choice.
