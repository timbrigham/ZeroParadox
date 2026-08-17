# Zero as a Wall — the failure-mode taxonomy

Ride-along documentation for [`ZeroParadox/Settheory/Wall.lean`](Wall.lean). The Lean file holds the
declarations and a statement per declaration; this file holds the argument, the prior art and the
fences. Where this file and the Lean file would overlap, **the Lean is authoritative** — a statement
here is a reading of a declaration, never a substitute for it.

**Name: "Zero as a Wall"** — ⊥/zero is the boundary self-reference cannot cross. Precise gloss (for
translation / external readers): *the metatheoretic boundary where ⊥'s self-reference cannot be
internalized.* ("Wall" is a flagged metaphor-nickname per the project idiom rule; the precise term is the
gloss.)

Across five separate pushes (fork unification, the Quine atom CC-2, MC-1, "realization is the choice",
the faithfulness criterion) the framework keeps landing on the SAME boundary: a structural shadow Lean's
well-founded kernel CAN host, plus a metatheoretic residue it CANNOT. The Lean file represents that
boundary as an **object-level theorem**, the honest in-kernel face of it.

## What the wall reduces to (the provable core)

The keystone (the diagonal fixed point) has two encodings:

- **The SHADOW** — `selfApp x = x`: a FUNCTION fixed point. Compatible with well-foundedness, hostable in
  Lean, proved choice-free (`AbstractSelfApp` / `selfMem_eq_singleton_bot`, [propext, Quot.sound]).
- **The LITERAL** — `x ∈ x` (= `r x x`): a RELATION self-loop. **Forbidden by well-foundedness.** This is
  the Quine atom ⊥={⊥}; it cannot live in a well-founded foundation.

So the wall is exactly: **a well-founded relation admits no self-loop.** That one theorem explains why the
shadow is hostable/choice-free and the literal is not — and why Lean's kernel (well-founded by
construction) can only ever realize the shadow. The set-theoretic instance is "no self-membered set under
Foundation," the in-kernel refutation of the literal Quine atom.

## Honest fences (do not overclaim)

- This does NOT prove "Lean cannot express the unification" — that is metatheoretic (a statement about
  the system, Gödel territory), not a Lean proposition. We prove the OBJECT-LEVEL refutation of the
  self-loop in well-founded settings.
- The "same role, not transferable" face is proved elsewhere and referenced, not re-proved here:
  `real_not_equiv_padic` and `categorical_fork_strict` (μ empty / ν inhabited — the two ends,
  provably distinct). ⚠ State `real_not_equiv_padic` as what it contains: `¬ real.IsEquiv (padic p)`,
  where both sides are absolute values **on ℚ** and `IsEquiv v w := ∀ x y, v x ≤ v y ↔ w x ≤ w y`.
  `ℚ_p` does not appear in the statement at all — the step to "the completions do not transfer" is
  one Ostrowski inference beyond the cited declaration, and is not part of it.
- The FORMAL SIGNATURE of the wall is the contrast: shadow realizable choice-free (proved upstream) ∧
  literal self-loop refuted under well-foundedness (proved in the Lean file). The wall is that pairing,
  not a claim that the residue is "closed."

## Prior art and library overlap (cite, do not reinvent)

- The diagonal-family unification — Cantor / Russell / Gödel / Turing / Tarski as one diagonal argument via
  a single fixed-point theorem — is **Lawvere (1969)**, "Diagonal Arguments and Cartesian Closed Categories"
  (LNM 92, pp. 134–145; TAC Reprint 15, 2006), and **Yanofsky (2003)**, "A Universal Approach to
  Self-Referential Paradoxes, Incompleteness and Fixed Points" (Bull. Symbolic Logic 9(3):362–386;
  arXiv:math/0305282). The unification is THEIRS; the Lean file formalizes it and links it to ⊥.
- The point-surjective theorem is already in **Mathlib**: `Function.exists_fixed_point_of_surjective` (its
  own docstring calls it an instance of Lawvere's fixed-point theorem), with `Function.cantor_surjective`
  for Cantor. `lawvere_fixedpoint` and `cantor_via_engine` are independent axiom-free re-derivations,
  kept for a self-contained family. The honest delta is the PRESENTATION — all four (Lawvere + Cantor +
  Russell + Turing) as corollaries off one named engine — not the theorems, which are not new.
- The **well-founded / membership / Bool / logical** re-proofs have exact library equivalents too,
  kept as self-contained hubs alongside the function-fixed-point ones: `wf_no_selfloop` is Mathlib's
  `WellFounded.irrefl` (`Mathlib/Order/WellFounded.lean`); `no_quine_atom` (`x ∉ x`) is
  `ZFSet.mem_irrefl` (`Mathlib/SetTheory/ZFC/Basic.lean`); `bool_not_no_fixedpoint` is
  `Bool.not_ne_self`; and `negation_no_fixedpoint` (`¬(p ↔ ¬p)`) is core Lean's `not_iff_self` /
  `iff_not_self`. The delta is again the PRESENTATION — one named engine with these as its faces — not
  the lemmas, which are standard.

### ⚠ Three stronger library forms, measured 2026-07-29. Read before re-proving anything in this family.

A gloss previously said "`Std.Irrefl r` unfolds to `¬ r x x`" — **it does not**; `Std.Irrefl` is a
*class with a field* (core `Init/Core.lean`, `Std.Irrefl`), so `WellFounded.irrefl h : Std.Irrefl r` and you
project `(WellFounded.irrefl h).irrefl x`. That matters, because Mathlib's form being class-valued is
what makes the following free:

- **`WellFounded.asymmetric`** (`Mathlib/Order/RelClasses.lean`) is **strictly stronger** than
  `wf_no_selfloop` — it forbids 2-cycles between *distinct* points, with `asymmetric₃` for 3-cycles. Irreflexivity is its `a := b` instance. So `wf_no_selfloop` is the weakest rung of a
  published chain; the Lean file states it deliberately as the one-cycle case, with `wf_no_cycle`
  covering cycles of any length.
- **Instance resolution already carries it.** `IsWellFounded → Std.Asymm` is registered
  (`Mathlib/Order/RelClasses.lean`), so `irrefl_of` / `asymm_of` fire on any type with the instance —
  and `ZFSet` has it (`Mathlib/SetTheory/ZFC/Basic.lean`, via `ZFSet.mem_wf`). Hand-rolled `∀`-form restatements get none
  of that machinery.
- **`wellFounded_iff_isEmpty_descending_chain`** (`Mathlib/Order/WellFounded.lean`) is a
  **biconditional**: `WellFounded r ↔ IsEmpty {f : ℕ → α // ∀ n, r (f (n+1)) (f n)}`. A self-loop is
  the *constant* descending chain, so it renders the non-well-founded side as **"the host contains an
  infinite ℕ-indexed descent."** That is the **INFINITE pole** the two-pole hard rule asks for, which
  the `r x x` form hides. **Now adopted** at `ZeroParadox/Multihomed/Boundary.lean` § I-b
  (`floor_descent_from_bot`, `bot_not_acc`, `floor_not_wellFounded_via_descent`).
  The **pointwise** form is `not_acc_iff_exists_descending_chain` —
  `¬ Acc r x ↔ ∃ f, f 0 = x ∧ ∀ n, r (f (n+1)) (f n)` — which is the one that locates the descent AT a
  given point. ⚠ Its *extract-a-chain* direction builds the sequence with `.choose_spec` and
  so carries `Classical.choice`. **⚠ The natural inference — "supply the witness yourself and use only
  the other direction to stay choice-free" — is FALSE, and was MEASURED false**: `#print axioms`
  follows the STATEMENT, so citing the biconditional at all pulls in the choice used by the direction
  you did not take. See `ZeroParadox/Multihomed/Boundary.lean` § I-b's purity block, where the one-line
  `mpr` version measured `[propext, Classical.choice, Quot.sound]` and only a HAND proof came back
  axiom-free. (Verified at source 2026-07-29. Line numbers deliberately omitted: a line number is a copy of
  a location and drifts — the lemma name is the stable anchor and is `#check`-able.)

## The wall as a failure-mode taxonomy (built one condition-set at a time)

The wall is not one theorem — its structure is the MAP from a held-fixed condition-set to the PRECISE
failure signature self-reference produces there. `wf_no_selfloop` is the well-founded-set entry; the rest
are proved in their own modules, each a checkable witness whose hypotheses ARE the conditions. Method:
hold one condition-set fixed, characterize the exact failure, then read the pattern across them (the same
experiment-style discipline that narrowed MC-1 and that EXTRACTED `wf_no_selfloop` itself).

**Reading the Footprint column:** it is the `#print axioms` result **of the theorem named on that
row**, measured, not inferred. Where a face has two witnesses with different footprints they get
their own rows rather than one stamp — the Turing face below is exactly that case, and collapsing it
was a defect caught 2026-08-17 by measuring rather than reading.

| Condition-set held fixed | Failure SIGNATURE | Theorem (module) | Footprint |
|---|---|---|---|
| logical / `Prop` (**the ENGINE**) | NEGATION HAS NO FIXED POINT (`¬(p↔¬p)`) | `negation_no_fixedpoint` (Wall.lean) | axiom-free |
| sets/functions, Cantor (**engine-linked ✓**) | no self-surjection onto predicates | `cantor_via_engine` (= engine at the diagonal) | axiom-free |
| naive comprehension, Russell (**engine-linked ✓**) | no membership realizes every predicate | `russell_via_engine` (via `lawvere_fixedpoint` + engine) | axiom-free |
| deciders, Turing (**engine-linked ✓**) | no self-surjection onto Bool-deciders (the halting diagonal) | `no_self_decider` (Lawvere + Bool engine) | axiom-free |
|  ↳ the same face with a real machine model | the halting problem, faithfully | `self_halting_undecidable` (`ZeroParadox/Computability/Kleene.lean`) | **choice** |
| any well-founded relation | NO CYCLE (any length) | `wf_no_cycle` (1-cycle: `wf_no_selfloop`) | axiom-free |
| set theory + Foundation | NO MEMBERSHIP CYCLE (any length) | `no_membership_cycle` (1-cycle: `no_quine_atom`) | choice-free |
| ordinal notation naming `<ε₀` | UNREACHABLE FROM BELOW | `omegaPow_no_fixedpoint` | choice-free |
| involutive fork whose pole is FIXED by the involution | THE POLES COINCIDE (the fork collapses) | `fixed_pole_forces_collapse` (`ZeroParadox/Algebra/WheelFrac.lean`) | axiom-free |
| metric completion of ℚ | NO TRANSFER (same role) | `real_not_equiv_padic` | choice |
| μ/ν coalgebra | DISTINCT ENDS | `categorical_fork_strict` | choice |
| computability (Kleene) | EXISTS-BUT-UNDECIDABLE | `infinite_quine_family` (∃, ∞-many) + `isComputationalQuine_undecidable` (¬ComputablePred) | choice |

**⚠ THE ROW'S SIGNATURE WAS ALSO WRONG, AND THAT MATTERED MORE THAN THE MISSING FILE. Corrected
2026-08-02 (adversary gate, bedrock).** It read
`| lightweight categorical typeclass | NO NON-VACUOUS UNIFIER | … | axiom-free |`. Against this table's
own rule — *each a checkable witness whose **hypotheses ARE the conditions*** — both columns were wrong:
the theorem's hypothesis is *the pole is fixed by the involution*, and its conclusion is *the poles
coincide*. **"No non-vacuous unifier exists" is a universal negative quantifying over all possible
typeclasses — not a Lean statement at all**, and it was carrying an "axiom-free" stamp in a witness
table. The row now states what the theorem proves. **The broader claim survives as a reasoned block
conclusion, labelled as one** in `ZeroParadox/Algebra/WheelFrac.lean` § "The involutive fork" — it is not
a theorem and has no witness. *(How it got in: the demotion note correctly described the theorem in its
NARROW form, and said "do not restore the citation without moving the declaration". The declaration was
moved and the citation restored — but nobody re-asked whether the narrow theorem supported the broad
signature.)*

The involutive-fork witnesses — `InvolutiveFork`, `collapsed_iff_fixed`, `wheelFork`,
`wheelFrac_fork_open`, `wheelFork_not_collapsed` and `fixed_pole_forces_collapse` — live in
`ZeroParadox/Algebra/WheelFrac.lean` § "The involutive fork". Footprints measured, not carried over:
`fixed_pole_forces_collapse` and `collapsed_iff_fixed` depend on no axioms; the two
wheel-of-fractions instances are `[propext, Quot.sound]`.

`lawvere_fixedpoint` (axiom-free) is the GENERAL theorem unifying the **diagonal family** — Cantor and
Russell are its corollaries, triggered by the engine (`Not` is fixed-point-free). Within the diagonal family
this is a real unification *theorem*, not the grand conjecture; the well-founded family is proved by a
different mechanism (induction), and whether it folds in too is the open one-root-or-two question.

## The μ/ν reframe (2026-07-29) — NOT a new result; every piece below is published

The engine's two regimes (μ = no fixed point / ν = a fixed point exists, see `negation_no_fixedpoint`) have
**standard names**, and so does the split the well-founded family performs on them:

- The ν direction is **"the Diagonal Theorem"**, credited to Lawvere & Schanuel — Yanofsky (2003), p. 5
  Remark 3 and p. 14 Theorem 3. (Yanofsky is already cited above; the *names* were not.)
- A host that permits ν is **"degenerate"** — Yanofsky p. 3: *"if there is a onto T → Y^T then Y must be
  'degenerate' i.e. every map from Y to Y must have a fixed point"*, and *"Paradoxes are ways of showing
  that if you permit one to violate a limitation, then you will get an inconsistent system."* Corroborated
  by nLab, *Lawvere's fixed point theorem* (fetched, not on disk — so treat that corroboration as
  weaker than the quoted primary sources). "Non-well-founded" is one concrete form of that degeneracy.
- In set theory the permit/refuse split **is** Foundation vs Anti-Foundation, in Aczel's own words
  (*Non-Well-Founded Sets*, 1988, p. 6): *"Non-well-founded sets exist… Of course we must relinquish the
  foundation axiom, but it will turn out that we need drop none of the other axioms of set theory."*
- The general categorical form is a **published theorem**: Adámek-Milius-Moss (2020, arXiv:1910.09401v2)
  **Theorem 7.6**, p. 30 — *"the only well-founded fixed point is the initial algebra"*. ⚠ **Quote the
  hypotheses with it**: the theorem is stated for *a complete and well-powered category with smooth
  monomorphisms*, and *for F preserving monomorphisms*. Example 7.5, immediately above it on the same
  page, is the counterexample showing what fails when the monomorphism condition is dropped. The bare
  gloss "a well-founded host admits no fixed point except the μ end" drops all four and overstates it. The standard name for the *axis* is the **well-founded part
  / the coreflection into well-founded coalgebras** (their Definition 5.1, p. 22, credited there to their
  own **[5]** — Adámek-Milius-Moss, *Fixed points of functors*, JLAMP 95, 2018 — and the coreflection to
  **[6]**, Adámek-Milius-Moss-Sousa, *Well-pointed coalgebras*, LMCS 9(2), 2014). **Taylor [27,28] is
  credited in that paper with introducing well-founded coalgebras for a general endofunctor and with the
  General Recursion Theorem — NOT with the well-founded part and NOT with the coreflection**; an earlier
  revision misattributed Definition 5.1 to him. (`CLAIMS.md`'s ledger row crediting Taylor
  with "well-founded ⟺ recursive" is correct and is a different claim.)
  What the Lean file proves is the **one-relation shadow** of that theorem, not the coalgebraic statement.

**So the framework's own narrow observation, stated without overclaim:** the theorems this taxonomy assigns
to the well-founded family are, on inspection, *refusals of the engine's own ν output* rather than an
independent root of self-reference — `wf_no_selfloop` instantiated per host (`no_quine_atom` where the host
is well-founded; `quineHost_not_wellFounded` / `floor_not_wellFounded` where it is not). That is a claim
about **this repo's taxonomy**, not about mathematics, and the literature above already presents the split
this way. Note the scope limit: it covers the **well-founded family only** — the ε₀ row
(`omegaPow_no_fixedpoint`) is ordinal arithmetic, *not* a self-loop instantiation, so "every row is a
ν-refusal" would be false. The narrow one-root question is still answered **no**: `wf_no_selfloop` is proved
by accessibility, not by the engine (`selfloop_permitted` / `engine_is_wf_free` stand).

The failure SIGNATURE changes with the conditions — distinct ways the one self-reference resists
internalization, not one failure repeated. The formal/metatheoretic frontier is itself part of the map:
`x∉x`, ε₀∉ONote, no-self-loop are in-kernel; the cross-category identity (MC-1's identity half) and the
literal AFA universe are metatheoretic-only.

**The computability row is the pivot (2026-06-27).** It is the ONLY framework where the fixed point is
NOT refuted/unreachable but provably EXISTS — `infinite_quine_family` gives infinitely many. ⚠ **Carry
the fence with the claim:** `IsComputationalQuine c` unfolds to `eval c = selfApply c`, which is a
**periodicity** condition, strictly weaker than self-reference — and the family is witnessed by
**constant** codes. `ZeroParadox/Computability/Kleene.lean` states this at the declaration
(`hconst_quine`, a `have` inside `infinite_quine_family`'s proof): constant codes satisfy the
predicate vacuously. So the family is broad rather than a padding orbit, and "the fixed point exists"
must not be read as "a self-referential object was constructed". Meanwhile the
failure migrates entirely to DECIDABILITY (`isComputationalQuine_undecidable`, `¬ComputablePred`). That is
"has all its attributes in theory (∃) but is incomputable (¬decidable)" stated as two theorems — the
exact premise of the incomputability-lever hypothesis below, now a confirmed real entry (footprint
[propext, Classical.choice, Quot.sound]; the choice is Mathlib classical-recursion-theory tooling).

## Working hypothesis (Tim, 2026-06-27) — incomputability as the lever, TO TEST not assert

The self-referential object "has all its attributes in theory" (well-defined / `Nonempty`) but is
INCOMPUTABLE — and that incomputability may be the ROOT the other signatures derive from, each framework
reporting "this witness isn't constructible here" in its own dialect. Formal hook:
`Classical.choice : Nonempty α → α` is the realize-from-existence bridge, non-computable exactly when the
witness is non-canonical — so "incomputable" ↔ "needs choice to realize" ↔ "exists but not
constructible." The open question the computability probe decides: is the EXISTS-BUT-UNDECIDABLE face the
GENERATOR of the others, or a co-equal face? Do not assert the hierarchy; let the per-condition probe
settle it.
