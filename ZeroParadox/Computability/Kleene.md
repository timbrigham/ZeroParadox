# The Gödel-number family, infinitely many fixed points, and a self-printing universal code

Ride-along for § VI and § VIII of `ZeroParadox/Computability/Kleene.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration docstrings.

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
      unimplemented; machinePhaseKleene's Classical.choose is this instance's choice of botCode; a
      computable instance with a constant code also satisfies the class (the example after
      machinePhaseKleene)
  (3) infinite_quine_family — the quine family is infinite: unboundedly many distinct
      (function, index) pairs exist. Its witnesses are the constant codes, so it bounds
      the family from below without showing those members are instantiation bottoms

The noncomputable marker comes from this instance's choice of botCode; a computable
instance with a constant code also satisfies the class, so the noncomputable marker belongs
to the instance, not to DA-1's computational path.

## § VIII. Infinitely many fixed points, padding, and a self-printing universal code

Fences and controls for § VIII of `ZeroParadox/Computability/Kleene.lean`.

**Many fixed points for every transformation.** `fixed_point₂_unbounded` strengthens Mathlib's
`Nat.Partrec.Code.fixed_point₂` (Kleene's second recursion theorem): for partial computable
`F`, a code `c` with `eval c = F c` exists above any bound on its Gödel number, so
`fixed_points_infinite` gives an infinite set of them. The proof applies `fixed_point₂` to a
modified `F'` that agrees with `F` above the bound and, at or below it, sends each code to a
constant code computing something different from it at input `0`; no fixed point of `F'` can
then sit at or below the bound. The arrow runs from the recursion theorem to the infinite
family, for every `F` at once. That a computable transformation has infinitely many fixed points is
the standard corollary of the recursion theorem; what is added here is its proof in Lean on
Mathlib's `Code`.

**Padding.** `padding` is `fixed_points_infinite` at an `F` that ignores the code: every
partial recursive function has infinitely many codes. This is the Padding Lemma of § VI's
prior-art note, the one that gives many indices for the SAME function. It is still not what
`infinite_quine_family` proves, whose witnesses compute different functions. In the Mathlib
pin, no lemma stating it was located as of 2026-10-04 (searched in
`Mathlib/Computability/` for `padd`, `Infinite`, `infinitely`, `unbounded`, `fixed_point`,
and across `Mathlib/` for `padding lemma`, `recursion theorem`, `infinitely many`, and
`Set.Infinite` with `Code`).

**A self-printing universal code.** Channel `k` of a code means its inputs `Nat.pair k n`, for
every `n`. `SelfPrints c` says `c` returns its own Gödel number on channel `0`; `Universal c` says
`c` agrees with the code numbered `e` on channel `e + 1`.
`selfref_universal_exists` and `selfref_universal_infinite` get both at once from fixed
points of `selfPrintOrDelegate`. These are statements about the partial function `eval c`,
equalities of `Part ℕ` values; they state presence and existence of such codes, and nothing
here says a code is run.

**Where `Classical.choice` enters `selfref_universal_exists`, measured 2026-10-04.** The choice
is not removed. The statement as written carries choice, so no proof of it is choice-free; a restated
form is choice-free, and no proof of that form without choice was found. Measured as follows,
by `#print axioms` in a scratch file importing this one.
- The statement carries choice. `SelfPrints` and `Universal` each measure
  `[propext, Classical.choice, Quot.sound]`. `Universal` names `Denumerable.ofNat Code`, which is
  `Nat.Partrec.Code.ofNatCode` by `rfl` (`ofNatCode_eq`); `ofNatCode` carries choice, and its
  well-founded recursion is justified by `Nat.unpair_left_le`, `Nat.unpair_right_le` and
  `Nat.div2_val`, each carrying it. `Nat.Partrec.Code.instDenumerable` carries it, while
  `encodeCode`, `eval`, `Nat.pair`, `Nat.unpair` and `Denumerable.ofNat` itself do not.
- A restated statement is choice-free: with `encodeCode` for the Gödel number and the channel
  of code `d` written `Nat.pair (encodeCode d + 1) n`, the predicate pair and the existence
  statement measure no axioms.
- No proof of it was found without choice. Mathlib's `fixed_point₂` carries choice in its
  statement: its hypothesis `Partrec₂ f` measures the triple, through `Primcodable.prod`, while
  `Partrec` measures `[propext]` and `Nat.Partrec` none. `fixed_point`, `exists_code`,
  `eval_part`, `eval_curry`, `primrec₂_curry` and `evaln` each carry it. Mathlib's other
  recursion theorem, `fixed_point : Computable f → ∃ c, eval (f c) = eval c` for
  `f : Code → Code`, avoids `Partrec₂` and still carries choice in its statement: that
  statement, restated as a `Prop`, measures the triple, because `Computable` at `Code`
  resolves through `Primcodable.ofDenumerable Code`, which measures the triple, while
  `Computable` itself measures `[propext]`. Not located as of 2026-10-04 by these
  measurements: a recursion theorem whose statement is choice-free, and a universal code whose
  correctness is proved without `eval_part`. Neither was attempted here. The footprint stays
  UNCLASSIFIED: a proof's footprint, not a theorem's necessity.

**Controls.** `universal_not_selfprints`: universality alone does not give self-printing.
The `example`s beside it: no constant code is universal, so the constant codes, which meet
`IsComputationalQuine` (`infinite_quine_family`), never meet `SelfPrints ∧ Universal`; and
`Code.zero` is self-printing, because its Gödel number is `0`, while not universal. Each half
of the conjunction is met by some code without the other.

**One code per behaviour, among self-printing codes.** `selfprints_behaviour_injective`: two
codes that are BOTH self-printing and have the same `eval` are equal, because channel `0` reads
the Gödel number back out of the behaviour and `Encodable.encode` is one-to-one. The hypothesis
is cheap: `Code.zero`, the constant-zero code, is self-printing (its Gödel number is `0`). So
the infinite family of self-printing universal codes is not one function reached by many codes:
any two of them differ on channel `0`. Contrast `padding`, where infinitely many codes share one
function. `Reading:` computational self-reference has a uniqueness, at the level of behaviour.

**Two self-printing universal codes differ only on channel `0`.**
`selfPrints_universal_address`: two self-printing universal codes give the same values on every
channel `e + 1`, the interpreter channels, and two distinct ones give different values on
channel `0`, which returns each code's own Gödel number; that second half is `Encodable.encode`
being one-to-one. As codes they may differ in any way; the statement is about their values. The
control beside it shows that `Universal` carries the first half: `Code.zero` is self-printing
and not universal, and it disagrees with a self-printing universal code on a channel `e + 1`.
`Reading:` replicas share everything but the address; the next instance adds only the address.
That is a claim about relative complexity, and it stays a reading while Kolmogorov complexity is
not in Lean (not located in the Mathlib pin as of 2026-10-04; search record in
`ZeroParadox/Information/Disjunctive.md`).

**Occurrence controls.** `Occurs` (`ZeroParadox/Computability/Occurrence.lean`) is
`(eval c n).Dom` by `occurs_iff_halts`. `selfprints_occurs` and `zero_occurs` show it holding
of every self-printing code on channel `0` and of `Code.zero` on every input: it is a static
property of a (code, input) pair and does not distinguish self-reference from a constant.
How occurrence is read, and that the identification is a modelling choice, is stated at
`occurs_iff_halts` and `da1_closed_concrete` in
`ZeroParadox/Computability/ComputationCannotBe.lean`.
