# The Minimal Core

*See the whole paradox in the smallest environment that can host it.*

[![Minimal Core](https://github.com/timbrigham/ZeroParadox/actions/workflows/minimal_core.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/minimal_core.yml) [![Complete Project](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml)

One self-contained Lean file - [`ZeroParadox/Miniature.lean`](ZeroParadox/Miniature.lean), about three hundred lines, importing only Mathlib - exhibits the entire **shape** the Zero Paradox is built on, on the smallest concrete objects that can carry it. Most steps are decided by computation or proved in a line or two: computed, not asserted.

The technique is standard: one abstract shape, several concrete instances, joined by a shared interface rather than by claiming the objects are equal.

This is the front door. The file it points to is the back door - the same thing, checkable.

---

## Two ways in

**If you just want the idea** - keep reading below.

**If you want to check it** - read [`Miniature.lean`](ZeroParadox/Miniature.lean) top to bottom, or run it yourself from the repository root:

```
lake env lean ZeroParadox/Miniature.lean
```

Nothing is left unproven (0 `sorry`). And you do not have to take anyone's word for it: the [Minimal Core CI gate](https://github.com/timbrigham/ZeroParadox/actions/workflows/minimal_core.yml) re-checks the file on every change with Lean - a proof assistant whose only job is to reject a false step - and writes a plain-language report of exactly what passed. The badge above is green when it does.

---

## What it shows

The framework's central claim is that one structure - a **diagonal fixed point** (the point that is its own image under a self-map; the home of the classical self-reference arguments, after Lawvere 1969) - sits at the bottom of several mathematical fields, and that a forced one-way transition off it - the **snap**, this project's shorthand - is a theorem. The minimal core puts that structure on minimal witnesses:

- **The engine** - Lawvere's diagonal: self-reference, once it closes, forces a fixed point (formally, a point-surjection forces every self-map to have one). Its seed - that negation has no fixed point - is the wall side, the same argument failing to close.
- **The wall and the floor** - a classifier, relative to whichever class of self-maps you admit, that sorts the two: where self-reference *cannot* close (the **wall** - Cantor, Russell, Turing, Tarski) and where it *does*, landing on a self-referential bottom element (the **floor**).
- **The pole** - the two-element `{0, ∞}`, its exactly four self-maps, and why the wall sits at the inversion `0 ↔ ∞` and the floor at a collapse.
- **The snap, in both directions** - it is at once a one-way collapse *and* an ascent to a limit that is itself a bottom. On the minimal chain, the top point is *simultaneously* the supremum of the climb (a limit) and the least fixed point of successor (the bottom of the fixed points) - which is exactly why the snap needs both directions and cannot be flattened to one.
- **The fan-out** - the branching field that the two-element pole is too small to hold.

A single capstone theorem bundles all of it: wall, floor, the collapse's irreversibility, the snap-limit that is both a limit and a bottom, and the fan-out - the whole shape on two points, a minimal chain, and a minimal branch.

---

## What the floor stands for

The minimal core represents the floor as bare fixed-point existence. In the full framework that fixed point is a *self-referential* object - the **Quine atom** (Quine; Aczel): the set that is its own only member, `⊥ = {⊥}`. It is one structural fact in several languages. Three of its faces are *proved* to be the same element within a single carrier, with no axioms - the Quine atom (set theory), the order-bottom `⊥`, and the algebraic identity element, shown to coincide by the framework's execution theorem (T-EXEC, the three-face form `t_exec_triple_iff`). The fourth, the Kleene quine (a program that prints itself, in computability), is *joined* to them by an explicit structural commitment: the framework names the computational fixed point as filling the same role, without asserting an identity across types, rather than deriving that coincidence.

**And that fourth commitment is the one to stop on** - it is where the whole thing starts to move. The other three faces are *static*: the order-bottom, the self-membered set, and the algebraic identity are timeless facts that simply hold, and nothing about them ever *happens*. The Kleene quine is the only one that *runs*. Anyone who writes software knows this in their hands: a program that is never run does nothing - it is inert text on disk; running it is the event, and execution is where the state changes, not the (often empty) output. ⊥ is the machine in its ground state, and the commitment is that even it must run itself. So committing that the self-contained bottom (`⊥ = {⊥}`) is the self-executing bottom is committing that **time enters the framework, as a state change**. That is the hinge, and it is the easiest thing here to walk past. It is what makes the framework dynamic at all: nothing static occurs on its own, so without that identification ⊥ would rest as a fixed point forever and the snap would never happen.

Two honest halves, kept separate here as everywhere: the *structural* self-application fixed point is Lean-proved and axiom-free; the *literal* set-membership `⊥ = {⊥}` is a metatheoretic modeling commitment (it needs a non-well-founded set theory, ZF+AFA, to host it), a theorem nowhere. The minimal core shows the structural half; the literal half is cited to its home, not rebuilt.

### Don't trust me - follow the reasoning

Every step above is either something a machine already checked, or a commitment I am naming out loud as a commitment. Here is exactly which is which, so you can walk the argument yourself and disagree in the right place. Run `#print axioms <name>` on any of them.

| The claim | What backs it | Status |
|---|---|---|
| Self-reference, once it closes, forces a fixed point - the engine | `lawvere` (Lawvere 1969 / Yanofsky 2003) | proved, no axioms |
| Three faces are one element: the Quine atom, the order-bottom, the join-identity | `t_exec_triple_iff` | proved, no axioms |
| The fourth face, the running program, does that same job - in time | the `KleeneStructure` typeclass | **a commitment, not a theorem** |
| The machine's before- and after-states are distinct (that execution *is* the state change is part of the model, not this theorem) | `l_run` (`c₀ ≠ c₁`) | proved |

**If you want to disagree, the place to do it is the commitment:** that the self-contained bottom and the self-executing program do the same job, one of them in time. Everything else above is either machine-checked or follows from it. The full claim-by-claim status, with every witness and its exact axiom footprint, is in the [Claims Ledger](CLAIMS.md).

---

## What this is - and is not

- **It is the shape, not the whole project.** The framework's substance is its domain *instances* - set theory and AFA, the 2-adic numbers, proof theory, the categorical bridges, the full bottom-element family - which are this shape worn by real mathematics. The minimal core stands *alongside* them as the most compact statement of what they are all instances of. It does not contain them.
- **The chain here is a shadow of the real thing.** The snap's true destination is the proof-theoretic ordinal ε₀; the minimal chain's top point is its smallest faithful shadow (a single fixed point where the real ε₀ has a whole hierarchy above it). The shape is faithful; the object is deliberately minimal.
- **Nothing is claimed to be one object across fields.** That the domain instances are numerically identical is *not* asserted - across distinct categories it is not even a well-formed statement, and the instances are provably distinct. The only thing they share is the shape.
- **The content is re-derived, not new.** The engine is Lawvere (1969) / Yanofsky (2003); the pieces exist across the framework's layers. The value here is the compression - the whole shape in one place, on the smallest witnesses, checkable in one command.

---

## Where to go next

- **The formal index** - [README](README.md): the document table, the full Lean verification, and the claim-by-claim [Claims Ledger](CLAIMS.md).
- **Plain language** - [Guide](GUIDE.md): illustrated companions and reading paths for every audience.
- **The object itself** - [The Bottom Element (⊥)](BOTTOMELEMENT.md) and [The Binary Snap (⊥ → ε₀)](SNAP.md): dictionaries and maps, most characterizations carrying a machine-checked Lean witness.
