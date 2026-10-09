# Double negation as the canonical predicated difference: Glivenko's core, and logic versus choice

Ride-along for `ZeroParadox/Category/DifferenceGeneratesSystem.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration docstrings; where the two overlap, the Lean
is authoritative.

The section below is the prose of that file's § "The canonical predicated difference", moved, with
edits at the attribution sites. In it, "below" and "this file" refer to
`ZeroParadox/Category/DifferenceGeneratesSystem.lean`.

## The canonical predicated difference — double negation generates the classical (Boolean) core

The sharpest instance of "a predicated difference generates a system": the difference is **double
negation** `a ↦ aᶜᶜ`, and the system it generates is the **classical (Boolean) core** of the constructive
base. On a Heyting algebra — the algebra of intuitionistic propositions — the double-negation map is a
closure (inflationary, `a ≤ aᶜᶜ`, and a reflection); its fixed points are the **regular** elements; and
those form a `BooleanAlgebra` (Mathlib's `Heyting.Regular`). That is the algebraic counterpart of
**Glivenko's theorem** ("the constructive base under the `¬¬` difference is classical") — the
`¬¬`-Boolean subtopos, textbook and cited here, not claimed.

**The honest fence (logic, not choice).** What this difference generates is classical *logic* (excluded
middle, the Boolean core), NOT the axiom of *choice*. **Choice implies excluded middle (Diaconescu 1975)**
— and in Lean's own kernel `Classical.em` is derived from `Classical.choice` (`Init/Classical.lean`,
whose docstring calls it "Diaconescu's theorem") by a two-predicate argument.
That **full** choice is strictly stronger than excluded middle is **Cohen 1963** / Fraenkel–Mostowski
independence, *not* Diaconescu, whose own theorem is an **equivalence** between two topos properties
(p. 176) and already concerns a two-point shape; the analogue in intuitionistic set theory is
Goodman–Myhill (1978), who state the restriction explicitly, choice "for sets B, C of at most two
elements" (p. 461). With unique choice into `Bool`, `ChoiceFragment` and `ExcludedMiddle` are
inter-derivable (the `example` after `em_of_choiceFragment` in
`ZeroParadox/Category/ExcludedMiddleBridge.lean`). So: double negation is the
difference that generates the classical core, and full choice sits above it. See
`ZeroParadox/Category/ChoiceCannotBe.lean` for the precise attributions. Stated below
with `example`s only (no new declarations) — this file *identifies*, it does not add a result.
