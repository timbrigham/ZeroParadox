# Which named bottom is a zero object: the per-bottom obstructions and the fence

Moved from `ZeroParadox/Category/SeamUniqueness.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise. One sentence was changed in the move: the `zpcategory_initial_not_zero` bullet paired the Carboni–Lack–Walters citation with AX-G1, and now pairs it with AX-G2 (PA-7).

## Formal Overview (AI-assisted)

`ZeroParadox/Category/TreeSeam.lean` established that node #5 (the Hilbert bottom `fD_functor.obj 0 = StateSpace 0`)
is a **zero object** of `ModuleCat ℂ` — the μ=ν seam node, initial ∧ terminal. The natural
follow-up (this file): **is #5 the only zero-object bottom among the framework
bottoms, or does another bottom also straddle?**

A zero object is one that is **both** initial **and** terminal. To rule a bottom *out* of being a
zero object it suffices to show it fails *one* of the two halves. We collect the four other bottoms
and show each fails — every one of them lands strictly on a single side of the μ/ν fork:

- `zpcategory_initial_not_zero` (ZP-G, generic) — in **any** `ZPCategory C`, the initial object
  `zpInitial` is **not** a zero object. The obstruction is structural and clean: a zero object is in
  particular *terminal* (`IsZero.isTerminal`), but `ZPCategory.ax_g1_no_terminal` (AX-G1) says the
  category has **no** terminal object at all, so its bottom can never be a zero object. Only AX-G1 is
  used; strict initiality (Carboni–Lack–Walters) is AX-G2, per `ZPCategory`'s docstring in
  `ZeroParadox/Category/Category.lean`. Specialized to the
  concrete instance `ForkObj` by `forkcat_initial_not_zero`.
- `zpa_bot_not_greatest` (ZP-A, generic) — in any ZP-A semilattice `HasNoTop L`, the bottom `⊥ₗ`
  is the **least** element (`bot_le`) but is **not** a greatest element: `¬ ∀ x, x ≼ ⊥ₗ`. The
  order-theoretic shadow of "initial but not terminal" — the poset-as-category bottom is the colimit
  end, not the limit end, exactly because there is no top.
- `kleisli_bottom_not_zero` (#4) — `fC_functor.obj 0 = Fin 0` is **not** a zero object: a zero
  object is terminal, but `kleisli_bottom_not_terminal` proves it is not terminal
  (`fC_no_return`: no stochastic map returns into the empty type). Strictly μ.
- `padic_bottom_not_zero` (#3) — the p-adic floor `{0} ⊆ Q₂` is **not** a zero object: a zero
  object is initial, but `padic_bottom_not_initial` proves it is not
  initial. Strictly ν.

`seam_unique_among_named` bundles all four negatives with the positive
`hilbert_bottom_isZero` into one statement: among {#3, #4, #5, the ZP-G initial,
the ZP-A bottom} only #5 is a zero object.

**Verdict witnessed: NO-GO on the GO conjecture.** The pre-registered GO conjecture was "another
zero-object bottom exists"; it is **refuted** for every bottom tested. The pre-registered NO-GO
obstruction — "#5 is the only zero-object bottom among those tested" — is the result.

**Honest fence.** This is NOT a uniqueness theorem quantified over *all* objects of *all* categories
(that would be false — every category with a zero object has one). The Lean content is exactly: of
the five **named framework bottoms**, #5 is a zero object and the other four are provably not. The
five live in five different categories, so "uniqueness" here means "of the named list," a finite
case check, not a universal claim. The seam reading (#5 is the diagonal-fixed-point keystone realized
at a node) remains the framework's interpretation, not a Lean claim.
