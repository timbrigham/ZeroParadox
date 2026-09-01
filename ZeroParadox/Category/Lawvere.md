# Category-relative verdicts: what each face fails, and what the shared shape is not

Argument, the face table and its fences for `ZeroParadox/Category/Lawvere.lean`. The Lean file holds
the declarations, the Engineer's Take and the per-declaration glosses.

## The completeness verdict — the face table

| Face | self-map | In **Set** (all endos) | Status |
|---|---|---|---|
| lattice / abstract (`selfApp`) | `selfApp` | NO witness — posited | `nontrivial_lattice_no_witness` ✓ |
| set theory (Quine atom) | `x ↦ {x}` | (= lattice; metatheoretic literal) | via the lattice ✓ |
| 2-adic (`×2` in ℚ₂) | `x ↦ 2x` | NO witness — posited | `q2_no_witness` ✓ |
| computability (Kleene quine) | computable endo | **NO witness — same as the others** | `computability_face_fixedPoint` ✓ (genuine, in the effective category) |

⚠ **ALL FOUR FACES FAIL THE SET TEST IDENTICALLY**, and the computability row is not special in
that column. `Code` is a nontrivial total type, so `no_witness_of_nontrivial` forbids the witness
there exactly as for the lattice and the 2-adics — checkable in one line:

```lean
example : ¬ HasLawvereWitness Nat.Partrec.Code :=
  no_witness_of_nontrivial (b₀ := Code.zero) (b₁ := Code.succ) (by simp)
```

What distinguishes the computability row is not its Set verdict but the **second category** it also
lives in.

## The honest verdict

The test is **category-relative**. In **Set** — raw types, all endofunctions — **no** face is a
Lawvere fixed point: Cantor forbids the witness for every nontrivial total type (lattice and 2-adic
proven; set theory is the lattice case, its literal ⊥ = {⊥} metatheoretic).

The computability face is a **genuine** Lawvere/recursion fixed point in the **effective** category,
where the fixed-point-free **diagonal** `fun x => g (e x x)` is not ADMISSIBLE.

⚠ **That is NOT the claim that no fixed-point-free computable endomap exists.** One does:
`fun c => Code.pair c c` is total, computable, and returns its own input for no `c`. What fails is the
diagonal CONSTRUCTION, not the existence of fixed-point-free maps — and per
`ZeroParadox/Category/DiagonalWitness.lean`, removing the obstruction **does not by itself supply the
witness**; the implication runs one way, and the fixed point on that side is Rogers' theorem, cited
rather than derived.

### What the escape IS, and what it is not

The Set refutation of § IV runs a **diagonal built from a fixed-point-free map**. Effectively there is
no such map: `no_computable_evalFixedPointFree` (`ZeroParadox/Category/DiagonalWitness.lean`) shows no
computable self-map on codes is eval-fixed-point-free, so the diagonal has **no computable
representative**. It is not admissible here, and the obstruction cannot fire. **The restriction is on
MORPHISMS.**

⚠⚠ **NOT on codomains, and this file said otherwise until it was refuted by elaboration.** The claim
was that `eval` lands in `ℕ →. ℕ` rather than `Code → Code`, "so the Set refutation never applied".
One line kills it:

```lean
example : ¬ HasLawvereWitness (ℕ →. ℕ) :=
  no_witness_of_nontrivial (b₀ := fun _ => Part.some 0) (b₁ := fun _ => Part.none)
    (by intro h; have := congrFun h 0; exact Part.some_ne_none 0 this)
```

The partial-function type is nontrivial too, so the Set refutation lands on it exactly as on `Code` —
changing the codomain buys nothing. `eval_point_surjective` carries `Nat.Partrec f`, so the
point-surjection reaches only the **computable** partial functions; were it onto all of `ℕ →. ℕ`, that
example would contradict it.

**Prior art for the shape:** Lawvere (1969) § 2 p. 9 raises the recursive case as an open question
rather than deriving it; the derivation is Yanofsky (2003) Theorem 5, printed p. 18, which states it
in the up-to-`eval` form (φ_{h(n₀)} = φ_{n₀}) — the source itself carries this arc's qualifier.

## What the keystone unifies, and what it does not

The keystone unifies a **shape** — the diagonal — not a single mechanism. The total faces carry a
*posited* fixed point sharing the diagonal shape; the computability face carries one *genuinely
produced* by the diagonal, in its own category.

The cross-face identification is a shared **shape**, confirmed precise. It is:

- **NOT** a cross-category object identity — that reading is retired as ill-typed. MC-1 names the
  bottom family, and its members are provably distinct.
- **NOT** a single-mechanism theorem.
- and the lattice / 2-adic faces are **provably not** Set-level Lawvere instances.

This is the sharpened, partly-proven replacement for the bare Tier-6 conjecture.
