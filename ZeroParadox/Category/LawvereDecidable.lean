import ZeroParadox.Category.Lawvere

set_option maxHeartbeats 400000

/-!
# Lawvere's engine, priced: the same theorems over decidable equality

## What this file is

A **measurement**, and a deliberate duplication. `ZeroParadox/Category/Lawvere.lean` states the
framework's diagonal engine over an arbitrary `β : Type*`. This file restates the two results that
carry `Classical.choice` there, over `β` with `[DecidableEq β]`, and measures the difference. The
proof *bodies* are byte-identical; only the hypothesis changes.

The point is not that one file is better. It is that the price of stating the engine at full
generality is now **exhibited rather than asserted** — the two footprints sit side by side and the
reader can see exactly what the extra generality costs.

## The measured price

| Result | over `Type*` | over `Type*` with `[DecidableEq β]` |
| --- | --- | --- |
| `fixedPointFree_of_nontrivial` | `[propext, Classical.choice, Quot.sound]` | `[propext]` |
| `no_witness_of_nontrivial` | `[propext, Classical.choice, Quot.sound]` | `[propext]` |

Read the purity block at the bottom; those are its numbers, not numbers hoped for.

## Where the choice actually enters, and why the general version keeps it

The construction is the two-point swap `fun x => if x = b₀ then b₁ else b₀`. That `if` needs to
decide `x = b₀`. Over an arbitrary type there is no such decision procedure, so the general file
opens with `classical`, which supplies `Classical.propDecidable` — and that single tactic is the
**entire** classical footprint of `fixedPointFree_of_nontrivial`. Its consumer
`no_witness_of_fixedPointFree` is axiom-free; `fixedPoint_of_witness` reduces to Mathlib's
`Function.exists_fixed_point_of_surjective`.

So this is not a case of the mathematics needing choice. It is a case of the *statement* being made
about types where the construction is not computable. Given `[DecidableEq β]` the same construction
is computable and the same proof goes through untouched.

**This is the framework's own instance-versus-requirements pattern** — name the requirement
(decidable equality), exhibit an instance meeting it, state what it buys, and never claim the two
statements are the same statement. They are not: the general one is strictly more general, and the
decidable one is strictly cheaper.

### Lean's linter states the trade better than this docstring does

Building this file emits, on both theorems:

> `does not use the following hypothesis in its type: [DecidableEq β]`
> `Consider removing this hypothesis and using classical in the proof instead.`

That is **correct and deliberately left in place.** The instance is not used in the *statement* — it
is used in the *proof term*, to make the `if` a computation instead of a classical case split. And
the linter's suggested fix — remove the hypothesis, use `classical` — produces, exactly,
`ZeroParadox/Category/Lawvere.lean`'s version.

So Lean is describing the trade from the other side: by its house style the hypothesis is dead
weight, because the linter reasons about statements and this hypothesis is paid in footprint. That is
the entire content of this file, arrived at independently by a tool with no stake in it. The warning
is left unsuppressed for that reason; if it is ever silenced, silence it with a comment pointing
here.

## What this file does NOT claim

* **It does not deprecate or replace `Lawvere.lean`.** The general statement is the keystone and
  stays general. Narrowing the engine's hypothesis to buy purity would trade a real asset for a
  cosmetic one — the faces the framework routes through Lawvere (Cantor, Russell, Turing, Tarski,
  Curry) are not all over decidable-equality types.
* **It does not show the general version's choice is necessary.** `classical` is how the proof was
  written, and a footprint never reports necessity. What is shown is the converse and it is enough:
  the choice is not doing mathematical work, because adding decidability removes it without touching
  the argument.
* **It is not a new theorem.** Both statements are Lawvere's, reduced to Mathlib's
  `Function.exists_fixed_point_of_surjective` exactly as the general file does. Prior art is
  Lawvere (1969); the diagonal-across-domains reading is Yanofsky (2003). Nothing here is claimed as
  new mathematics, and the duplication is the deliverable.

## Engineer's Take

In the Lawvere file, for fixed point free of nontrivial, why not just create another file that covers
the decidable equality case. Being able to put them side by side and show the difference would be
pretty damn cool.

That is the same move as building something in this framework and then cross referencing it to the
more general category. It is an interface between constructive and choice based logic, and that is
valuable even if it means going single instance versus general. I think that is exactly how this
interface is going to have to work.
-/

namespace ZeroParadox

/-! ### The two-point swap, over decidable equality

The construction `fun x => if x = b₀ then b₁ else b₀`. With `[DecidableEq β]` the `if` is a real
computation rather than a classical case split, and the proof body below is character-for-character
the one in `ZeroParadox/Category/Lawvere.lean` — only the `classical` line is absent, because nothing
needs it. -/

/-- Any type with **decidable equality** and two distinct elements admits a fixed-point-free
    endofunction. The decidable-equality counterpart of `fixedPointFree_of_nontrivial`
    (`ZeroParadox/Category/Lawvere.lean`), which states the same thing over an arbitrary type and
    pays `Classical.choice` for the `if`. -/
theorem fixedPointFree_of_nontrivial_decidable {β : Type*} [DecidableEq β] {b₀ b₁ : β}
    (hne : b₀ ≠ b₁) : ∃ g : β → β, ∀ x, g x ≠ x := by
  refine ⟨fun x => if x = b₀ then b₁ else b₀, fun x => ?_⟩
  by_cases hx : x = b₀
  · subst hx; simpa using hne.symm
  · simp only [if_neg hx]; exact fun h => hx h.symm

/-- **Nontrivial decidable types carry no Lawvere witness** (Cantor). The decidable-equality
    counterpart of `no_witness_of_nontrivial` (`ZeroParadox/Category/Lawvere.lean`).

    The consumer is unchanged: `no_witness_of_fixedPointFree` is axiom-free in the general file and
    is reused here verbatim. Only the supplier of the fixed-point-free map changes, which is why the
    whole footprint difference is carried by the previous theorem. -/
theorem no_witness_of_nontrivial_decidable {β : Type*} [DecidableEq β] {b₀ b₁ : β}
    (hne : b₀ ≠ b₁) : ¬ HasLawvereWitness β := by
  obtain ⟨g, hg⟩ := fixedPointFree_of_nontrivial_decidable hne
  exact no_witness_of_fixedPointFree g hg

/-! ### The instance side — the requirement is cheap to meet in practice

`DecidableEq` is not an exotic hypothesis. Every finite type the framework actually routes through
the diagonal has it, and `Bool` is the canonical two-element witness. The example below is not a
result; it exists so the purity block can show that *using* the decidable version costs nothing
either. -/

/-- `Bool` carries no Lawvere witness. An application, not a new result — it exists to show the
    decidable route stays `[propext]` end to end. -/
theorem bool_no_witness : ¬ HasLawvereWitness Bool :=
  no_witness_of_nontrivial_decidable (b₀ := false) (b₁ := true) (by decide)

end ZeroParadox

/-! ## Axiom Purity Check

The comparison is the point. Read these next to the same four names in
`ZeroParadox/Category/Lawvere.lean`'s purity block: the general `fixedPointFree_of_nontrivial` and
`no_witness_of_nontrivial` carry `Classical.choice`; the decidable counterparts below do not.

`no_witness_of_fixedPointFree` is printed in both files deliberately — it is the shared consumer, it
is axiom-free, and printing it in both places shows the difference is entirely in the supplier. -/

section PurityCheck
open ZeroParadox

-- The decidable route. Expected [propext] throughout.
#print axioms fixedPointFree_of_nontrivial_decidable
#print axioms no_witness_of_nontrivial_decidable
#print axioms bool_no_witness

-- The shared, axiom-free consumer.
#print axioms no_witness_of_fixedPointFree

-- The general route, reprinted here so the contrast is visible in one place rather than
-- asserted across two files.
#print axioms fixedPointFree_of_nontrivial
#print axioms no_witness_of_nontrivial

end PurityCheck
