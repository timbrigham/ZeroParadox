# The Minimal Core

*See the whole paradox in the smallest environment that can host it.*

[![Minimal Core](https://github.com/timbrigham/ZeroParadox/actions/workflows/minimal_core.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/minimal_core.yml) [![Complete Project](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml)

One self-contained Lean file - [`ZeroParadox/Miniature.lean`](ZeroParadox/Miniature.lean), under three hundred lines, importing only Mathlib - exhibits the entire **shape** the Zero Paradox is built on, on the smallest concrete objects that can carry it. Every step is decidable or one line: computed, not asserted.

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

- **The engine** - Lawvere's diagonal: self-reference, once it closes, forces a fixed point. Its seed - that negation has no fixed point - is the wall side, the same argument failing to close.
- **The wall and the floor** - a classifier that sorts the two on any domain: where self-reference *cannot* close (the **wall** - Cantor, Russell, Turing, Tarski) and where it *does*, landing on a self-referential bottom element (the **floor**).
- **The pole** - the two-element `{0, ∞}`, its exactly four self-maps, and why the wall sits at the inversion `0 ↔ ∞` and the floor at the collapse.
- **The snap, in both directions** - it is at once a one-way collapse *and* an ascent to a limit that is itself a bottom. On the minimal chain, the top point is *simultaneously* the supremum of the climb (a limit) and the least fixed point of successor (the bottom of the fixed points) - which is exactly why the snap needs both directions and cannot be flattened to one.
- **The fan-out** - the branching field that the two-element pole is too small to hold.

A single capstone theorem bundles all of it: wall, floor, the collapse's irreversibility, the snap-limit that is both a limit and a bottom, and the fan-out - the whole shape on two points, a minimal chain, and a minimal branch.

---

## What the floor stands for

The minimal core represents the floor as bare fixed-point existence. In the full framework that fixed point is a *self-referential* object - the **Quine atom** (Quine; Aczel): the set that is its own only member, `⊥ = {⊥}`. It is one structural fact in several languages. Three of its faces are *proved* to be the same element within a single domain, with no axioms - the Quine atom (set theory), the order-bottom `⊥`, and the algebraic identity element, shown to coincide by the framework's execution theorem (T-EXEC). The fourth, the Kleene quine (a program that prints itself, in computability), is *joined* to them by an explicit structural commitment - the framework names the computational fixed point as the same role rather than deriving that coincidence.

Two honest halves, kept separate here as everywhere: the *structural* self-application fixed point is Lean-proved and axiom-free; the *literal* set-membership `⊥ = {⊥}` is a metatheoretic modeling commitment (it needs a non-well-founded set theory, ZF+AFA, to host it), a theorem nowhere. The minimal core shows the structural half; the literal half is cited to its home, not rebuilt.

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
