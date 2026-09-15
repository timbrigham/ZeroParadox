# The Gödel-number family: periods, constant codes, and the noncomputable marker

Argument and fences for § VI of `ZeroParadox/Computability/Kleene.lean`, moved here verbatim from that
section's module docstring (2026-09-15). The Lean file holds the declarations, the Engineer's Take and
the per-declaration docstrings.

## § VI. Function-Gödel-Number Correspondence

Every computational quine c has a Gödel number encode(c) that is not external
metadata — it is *a* period of the function computed by c in the selfApply sense. (Not
*the* period: nothing here shows it is the least one, and a constant code is periodic
with every period.)
The computational quines form an infinite family with distinct Gödel numbers. Within
that family a code is recovered from its Gödel number, since encoding is injective on
all of `Code`. That does not make the function and the index mutually determining: the
index is only *a* period of the function, and constant codes are periodic with every
period, so the function does not fix the index. Reading that family as the DA-2 instantiation
succession — one bottom element per instantiation, each with its own code — is the
framework's interpretation and is NOT what the theorems below establish; see the fence
immediately following for what actually witnesses the family.

**Honest fence on what "computational quine" does and does not pin.**
`IsComputationalQuine` is the *periodicity* condition eval c n = eval c (encode c + n).
A constant code satisfies it trivially — a constant ignores its input and is periodic
with every period — and the proof of `infinite_quine_family` below witnesses the family
with exactly those (`hconst_quine`, `Code.const k`). So the predicate is strictly weaker
than "self-referential": genuine Kleene fixed points satisfy it (`computational_quine_exists`,
via the second recursion theorem, and that witness is real), and so do constants. The
(function, index) pairing is therefore a signature of the *code*, and should not be read
on its own as a signature of self-reference.

**And on the shape of the family.** These fixed points are genuinely many and genuinely
distinct — `infinite_quine_family` and `quine_goedel_injective` prove it — while the
set-theoretic side has exactly one self-containing element (`quine_unique`). A unique
element and an infinite indexed family are different shapes, so the correspondence here
is between the *succession* of instantiations and the family, not an identification of
one element with one code. The framework's reading of that correspondence is in § II;
no theorem in this file identifies a `Code` with an element of a lattice, and the type
boundary makes such an identification unstatable.

**Prior art, and a distinction that must not be collapsed.** That a computational object
is named by many indices rather than one is standard: the **Padding Lemma** — every
partial recursive function has infinitely many indices — is its classical home, and an
external computability reader mentioned it as possibly related when asked about ZP-K.
It is the right reference for the direction it actually gives: **a function does not
determine an index**, since infinitely many indices compute it. (Stated as a named lemma
without individual attribution; it appears as a hypothesis of Rogers' isomorphism theorem
rather than as a result of his, so do not attach a name to it.)
It is **not** what `infinite_quine_family` proves, and the two must not be conflated:
padding supplies infinitely many indices for the *same* function, whereas this family is
witnessed by the constant codes, and `Code.const 0` and `Code.const 1` compute *different*
functions. So the family here is broad, not a padding orbit. Cite padding for the
index-multiplicity point; do not cite it for this theorem.

Three formal results capture this structure:
  (1) quine_period_is_goedel — the Gödel number IS a period (definitionally; not shown
      to be the least one)
  (2) self_halting_undecidable and isComputationalQuine_undecidable — the boundary
      between computation and self-reference is genuinely non-computable, not merely
      unimplemented; Classical.choose in machinePhaseKleene reflects this
  (3) infinite_quine_family — the quine family is infinite: unboundedly many distinct
      (function, index) pairs exist. Its witnesses are the constant codes, so it bounds
      the family from below without showing those members are instantiation bottoms

The noncomputable marker comes from this instance's choice of botCode; a computable
instance with a constant code also satisfies the class, so non-constructivity belongs
to the instance, not to DA-1's computational path.
