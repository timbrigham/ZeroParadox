# Building an abstract provability logic, and Gödel's second as a corollary

Argument, design and attribution for `ZeroParadox/Settheory/Loeb.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## The face

Löb (1955): in a system with a provability predicate `□` satisfying the Hilbert–Bernays–Löb derivability
conditions, `⊢ (□A → A)` implies `⊢ A`. This is the diagonal family's **provability-modal face** — the
self-referential fixed point of the map `p ↦ (□p → A)` (the Löb sentence). It is the ONLY sibling of the
four with no Mathlib support located as of 2026-08-17 (no modal / provability logic found in the pin),
so it is built from scratch
as an abstract provability logic.

## Placement in the family

Tarski is the TRUTH face (undefinable — the wall), Gödel/Löb the PROVABILITY face (definable but
self-constrained). Löb subsumes **Gödel's second incompleteness**: at `A = ⊥` it says a consistent system
cannot prove `□⊥ → ⊥` — its own consistency (`godel_two`). The Löb sentence `ψ ↔ (□ψ → A)` is a genuine
diagonal fixed point (ν: it exists, by the diagonal lemma), and Löb is what it forces.

## Design

`ProvabilityLogic` is a typeclass carrying sentences `S`, connective `imp`, modality `box`, and a
provability predicate `Thm`, with the minimal axioms Löb needs — the implicational Hilbert base (`ax_K`,
`ax_S`) with modus ponens (`mp`), and the three derivability conditions (`nec` = D1, `ax_D2` =
distribution, `ax_D3` = D3). The diagonal lemma is taken as a hypothesis (`hfix1`/`hfix2`), the standard
separation of concerns: Löb from the derivability conditions plus a diagonal.

## Honest delta

A genuinely new construction — no Mathlib modal/provability logic, and nothing like it in the repo.
Attribution: Löb (1955); Hilbert–Bernays–Löb derivability conditions; diagonal-family framing Lawvere
(1969), via Yanofsky (2003) § 1 p. 1. The classical Löb derivation is standard; the contribution is
the clean abstract typeclass and its placement as the provability face of ⊥'s diagonal.
