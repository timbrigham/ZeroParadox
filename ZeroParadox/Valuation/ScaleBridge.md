# Dropping the join, and a membership question settled exactly

Argument, NO-GO gauge and prior art for `ZeroParadox/Valuation/ScaleBridge.lean`. The Lean file holds
the declarations, the Engineer's Take and the per-declaration glosses.

## The question

`ZeroParadox/Valuation/Scale.lean` defines `ValuationStructure` over `[ZPSemilattice L]`, but the four
axioms (`scale_bot`, `val_bot`, `val_unique`, `val_scale`) only ever use `bot` — the join `⊔` never
appears. So `ZPSemilattice` is an over-strong constraint, and no `ValuationStructure` `ℤ_[2]` is
DEFINED even though all four axioms hold (proved as standalone theorems in
`ZeroParadox/Valuation/Scale.lean` § V).

⚠⚠ **Not defined is not the same as not possible, and here the difference decides the answer.**
`Nonempty (ValuationStructure ℤ_[2])` fails to elaborate only because no `ZPSemilattice ℤ_[2]`
INSTANCE is registered — a fact about the instance database. Supplied explicitly the proposition
is TRUE, and `ZeroParadox/Valuation/Scale.lean` now carries the witness: a semilattice with
bottom 0, over which all four axioms discharge. **The join is free.** The four axioms mention
only `bot` and never the join, so any associative, commutative, idempotent operation with 0 as
its identity serves; "the larger under some total order, unless one side is zero" is one.
What has NOT been located as of 2026-08-30 is a *natural* join arising from the ring operations —
searched: every registered `ZPSemilattice` instance in this corpus — none on `ℤ_[2]` itself, though
`instZPSemilatticeEnd` (`ZeroParadox/Valuation/PoleCompletion.lean`) equips the 2-adic digit
boundary, whose digit isomorphism that file's Honest fence leaves unformalized (it names ℚ₂) — and
`ZeroParadox/Valuation/Scale.lean` § V. That is a statement about what has been written down, not
about what exists. ⚠ On the separate question of choice-dependence, one reason subsumes all the others and closes
it: `ZPSemilattice ℤ_[2]` is choice-tainted *as a type*, so no inhabitant can report a
smaller footprint. `ZPSemilattice ℕ` is axiom-free by contrast, so it is the carrier and not the
class. It adds no new axiom: § V's own `q2Val_unique` and `q2Val_scale` already carry `Classical.choice`.
A choice-free join on this carrier IS ruled out under the `#print axioms` metric — the type is
already tainted — and that is measured, not assumed. Whether a constructively re-founded 2-adic
type would change the question is a separate matter, not addressed here.

This tests the conjecture that the constraint is an **encoding artefact, not a mathematical gap**. It
defines `ValBridge` — the same four axioms with `bot` a plain field rather than a `ZPSemilattice` bottom
— and builds a formal `ℤ_[2]` instance from the theorems already proved.

If the instance builds and the AFA content chain follows, the formal bridge is complete: `ℤ_[2]` carries
the LATTICE SHADOW of AFA content as a theorem of ZFC, rather than as an import from Aczel.

⚠ Read that with the fence `ZeroParadox/Computability/SelfApp.lean` applies to the same gloss: what is
proved is that the scale map has `bot` as its unique fixed point (`z2_selfMem_singleton`), the
one-relation shadow of the Quine atom — **NOT** literal set-membership `⊥ ∈ ⊥`, which is a statement of
the ZF+AFA metatheory.

## NO-GO gauge — what FAILS to be a `ValBridge`

A requirements class carries information only where something fails to be a member, so the failure
condition is recorded here rather than left to be rediscovered at a use site.

**The membership question is settled exactly** (`valBridge_nonempty_iff`):

> `Nonempty (ValBridge α) ↔ Infinite α ∨ (Nonempty α ∧ Subsingleton α)`

The forcing half is `valBridge_forces_infinite`: from any `x ≠ bot` the scale orbit `scale^[k] x` never
reaches `bot` and its valuation climbs by exactly one per step, so `k ↦ scale^[k] x` is injective. The
one-point carrier is a member because `val_scale` is guarded by `x ≠ bot` and is vacuous there
(`trivialValBridge`). Both converse directions are built: `nonempty_valBridge_of_infinite` places the
orbit along an ℕ-embedding, and `nonempty_valBridge_of_inhabited_subsingleton` is the degenerate case.

So the non-members are the finite carriers with two or more points, and also `Empty` — a subsingleton,
but `bot : L` is a field, so a carrier is always inhabited. `valBridge_bool_isEmpty` records the smallest
inhabited non-member.

⚠ **`[ValBridge L]` therefore constrains cardinality and nothing else.** It does not distinguish
`instZ2ValBridge` from arbitrary bookkeeping, because `nonempty_valBridge_of_infinite` equips *any*
infinite carrier. The substance of the `ℤ_[2]` instance is in its chosen `scale` and `val`, never in
membership — **do not cite membership as evidence that a witness is non-degenerate.**

## Prior art

**In this corpus, and it is the general form:** `orbit_dichotomy`
(`ZeroParadox/Order/OrbitDichotomy.lean`), whose file header already names the framework's scale map as
the checkable branch of exactly this argument. Cite that for the general pattern.

⚠ **`valBridge_forces_infinite` is NOT an instance of it.** That theorem assumes `Function.Injective s`;
`ValBridge` does not supply it — take `L = {bot} ⊎ (ℕ × Bool)` with `val (n, b) = n` and
`scale (n, b) = (n+1, false)`, which satisfies all four axioms and collapses `(0, true)` with
`(0, false)`. `val_scale` buys injectivity *along an orbit*, which is all the argument consumes.

The two-element case is older still: `ZeroParadox/Settheory/OntBridge.lean` records that
`OntologicalStates` admits no `ValuationStructure`, by `valuationStructure_forces_infinite` — the
obstruction transported across `toValBridge`, which is the direction that transfers. ⚠ The obstruction
is JOINT: `val_scale` alone holds on two elements (`val` everywhere `⊤`, `scale := id`, since
`⊤ + 1 = ⊤`), and it is `val_unique` that then fails.

**Outside the corpus**, the owning branch is valuation theory, whose statements use multiplicative
structure this class drops — **F.-V. Kuhlmann, *Valuation Theory*, Ch. 4, Corollary 4.13**: *"The only
fields which do not admit non-trivial places are precisely the algebraic extensions of finite fields."*
⚠ The *setting* here is more general; the *results* are incomparable, since `F̄_p` is infinite and this
says nothing about it. Credit points outward.

For the degenerate half: a trivial algebra satisfies every positive axiom, so only a negated atom
excludes it — Burris & Sankappanavar, *A Course in Universal Algebra*, p. 251. That is why a
non-degeneracy condition must be an inequation rather than a further equation. ⚠ Their neighbouring
"trivial algebras satisfy any quasi-identity" does **not** apply here: `val_scale`'s antecedent
`x ≠ bot` is a negated atom, and a quasi-identity admits only positive ones.

Standard names, for searching: `(L, scale)` is a **mono-unary algebra** (a **unar**), and the mechanism
exhibiting `ℕ ↪ L` is **Dedekind-infinite**.

`Reading:` **COINCIDENCE** — the characterisation has the same shape as
`infinitudeFloor_nonempty_iff_infinite` (`ZeroParadox/Valuation/InfinitudeFloor.lean`), which pins that
class to exactly `Infinite`; the valuation climbing without bound along the orbit and the floor carrying
the value ⊤ read as the framework's zero and infinity poles on one carrier. **A reading, carrying no
declaration and no import.** The membership transfer would be witnessed by an arbitrary ℕ-embedding
whose `floor` and `cx` are unrelated to `bot` and `val`, so it would not witness the coincidence it
names; the canonical witness — `member` the scale orbit, `cx` the valuation — would, and is not built.
