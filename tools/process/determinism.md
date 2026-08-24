# Determinism is the single recurring cost — the four sites and the `carry` counterexample

**Body for `CLAUDE.md` § `R-DETERMINISM`.** The rule is there; the four theorems that make
it, the trichotomy consequence, and the observable-vs-state separation are here.

---

## Determinism is the SINGLE recurring cost — name it, don't rediscover it

**Every "the bottom cannot move" result in this corpus is powered by SINGLE-VALUEDNESS, not by
self-reference.** This surfaced four separate ways in one session (2026-07-30) and was re-derived each
time, so it is written here rather than left to be found five sections into a file:

- `machine_snap_impossible` — nothing is both its own fixed point and departed from. `Occurrence.lean` § VI
  states the diagnosis: *"the obstruction of § III is the absence of fan-out, not the presence of a fixed
  point."*
- `deterministic_has_no_fanout` — a function `σ → Option σ` admits at most one successor. That is the
  whole obstruction.
- `nondeterministic_escapes_the_trap` — a **relation** can loop at `s` *and* reach elsewhere. That is the
  whole escape.
- `execution_requires_branching` — stated over a **relation** for exactly this reason.

**The consequence to carry into any prose about the trichotomy:** halted / self-looping / stepping-onward
are three distinct **states** under any dynamics, but under a **function** the first two share a **FATE** —
`loop_is_a_trap` and `eval_of_halted` each give a singleton reachable set. The trichotomy is genuinely
three-valued **only** in the non-deterministic setting; make the step single-valued and the self-loop is a
relabelled trap. So **"could it still move?" is a MODAL question, and the function-vs-relation choice is
how the framework encodes that modality WITHIN the trichotomy.**

⚠ **It is not the only encoding, and "nothing else" is too strong** — the corpus's own counterexample is
`carry` (§ VI-c, `ZeroParadox/Computability/Occurrence.lean`): a **function with no fixed point anywhere**
whose observable projection never changes. `LoopsInPlace` demands the state return to *itself*, so adding
any accumulating component leaves no fixed point at all and `machine_snap_impossible` does not apply —
yet nothing observable moves. The separation being made is **the state moving** versus **the observable
changing**, which is a question about a quotient rather than about determinism.

**Do not re-derive this, and do not attribute the obstruction to the fixed point.** The self-loop is not
what blocks departure; being a function is. Note also what it is NOT: this says nothing about whether the
bottom *does* move. Non-determinism buys the *possibility* and never the *occurrence* — see `l_inf`'s
docstring, and `tri_idle_never_starts`, where a perfectly well-formed third state sits inert forever.
