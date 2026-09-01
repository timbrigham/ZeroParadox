# Cantor normal form, the ε₀ ceiling, and the choice question

Ride-along documentation for [`ZeroParadox/Ordinal/SnapNucleusConstructive.lean`](SnapNucleusConstructive.lean). The Lean file holds the declarations and a statement per
declaration; this document holds the scope fences, the prior art and the choice analysis.
Where the two would overlap, **the Lean is authoritative**.

## What the Lean file is

An **obstruction result**. `ZeroParadox/Ordinal/SnapNucleus.lean` defines
`snapNucleus : Nucleus Ordinal` as `Ordinal.nfp (fun a => Ordinal.omega0 ^ a)`, with measured footprint
`[propext, Classical.choice, Quot.sound]`. The Lean file asks the ZP-N question of that object — can the
same content be had choice-free on the syntactic ordinal-notation substrate? — and answers **no**, with a
machine-checked impossibility rather than a failed attempt.

## What this does NOT establish

* **`snapNucleus` is not made choice-free here.** Nothing in the Lean file is a re-proof, replacement, or discharge
  of `snapNucleus`, `snapNucleus_bot`, or any result in `ZeroParadox/Ordinal/SnapNucleus.lean`. Those
  stand exactly as they are, with the footprint they have.
  **Correction of record (2026-07-19):** this bullet previously read "and cannot be," justified by
  "Mathlib's `Ordinal` is a quotient of well-ordered types; `Classical.choice` sits in the *type*." That
  is **false as measured** — `#print axioms Ordinal` reports `[propext, Quot.sound]`, no choice. Choice
  enters through the order instance and the operations (`Ordinal.instLinearOrder`, `Ordinal.nfp`,
  `Ordinal.omega0`, `Ordinal.epsilon`). The claim was reasoning from a quotient construction instead of
  measuring it, and the "cannot be" conclusion drawn from it does not stand. Whether `snapNucleus` is
  re-provable choice-free is **open, and untried in this corpus as of 2026-08-02**; its footprint
  is UNCLASSIFIED.
* **This is a different declaration on a different carrier.** Everything here lives on `ONote` (raw
  Cantor-normal-form syntax) and on `SynONote`, the type synonym carrying the comparator-derived
  order. `ONote` is not `Ordinal` and `SynONote` is not `Ordinal`. Exactly one theorem mentions
  `Ordinal` at all — `mathlib_ONote_order_not_antisymm`, which is a fact about *Mathlib's* order and
  is disclosed as choice-carrying. Nothing here transports a result across the two carriers.
* **It is not a proof that ε₀ requires choice.** The obstruction proved in the Lean file is about *notation
  systems of this shape* — Cantor normal form, whose terms name exactly the ordinals below ε₀. It says
  nothing about notation systems that extend past ε₀ (Veblen / Bachmann-Howard style), none of which
  is in this Mathlib pin as of 2026-08-02 (the pin's `Veblen.lean` is semantic, not a notation system
  — see the scope note below). Whether some richer constructive substrate supports a snap nucleus is
  open, and untouched in this corpus as of 2026-08-02.
* **The impossibility is not "no nucleus exists on `ONote`."** Nuclei on `SynONote` exist in
  abundance — `id` is one. What is proved impossible is the *snap property*: that a nucleus's closed
  points be ε-numbers.

## Prior art on the operator itself

**de Jong, Kraus, Nordvall Forsberg and Xu, "Constructive Ordinal Exponentiation"**
(arXiv:2501.14542) is the nearest specialist work on ordinal exponentiation. Its bearing here is a
**carrier** distinction. Stating it as "their taboo does not reach our operator" would be false:
their § 7 collects several taboos about ordinal exponentiation, including the **fixed-base** map
`β ↦ α^β` that `ω^·` is an instance of, as recorded below.

Their **Proposition 9**: an exponentiation operation satisfying the natural specification *"can be
shown to exist if and only if the law of excluded middle holds"* — a genuine taboo EQUIVALENCE, not
a footprint measurement. **But that is exponentiation in FULL generality**, and the restriction that
buys the construction is *not* nonzero-ness: Proposition 9's own counterexample base is `P + 1` for a
proposition `P`, which the authors note is obviously nonzero. What the base must have is a **least
element**. Their **Theorem 13** gives the abstract (suprema) construction under `α ≥ 1` — which they
gloss as α having a least element — and **Theorem 24** the concrete decreasing-lists construction
whenever the base has a **trichotomous** least element. **`ω` satisfies both**, so *that particular*
taboo is about the unrestricted operation and `ω^·` is one of the cases they construct.

**But the taboos do not stop at Proposition 9 (which is in their § 2), and their § 7 "Constructive
Taboos" holds several that do concern the fixed-base exponential.**
**Proposition 52**: exponentiation is monotone in the base iff LEM,
and LEM is already implied by weaker statements *"even when α and β are each assumed to have a
trichotomous least element"* — so a trichotomous least element is not a blanket constructivity
certificate. **Proposition 55 (iii)/(iv)**: `∀ β, β ≤ 2^β` and `∀ β, ∀ α > 1, β ≤ α^β` are each
**equivalent to LEM** — and (iv) at `α = ω` is a statement about this operator.
**Note what Proposition 55 (iii)/(iv) do and do not prove**: each is LEM-equivalent *as a quantified
statement*, (iii) at base `2`; the paper never separately shows the base-`ω` instance implies LEM.

**A further LEM equivalence sits in their § 8 (*Approximating Subtraction, Division and Logarithm
Operations*), not in the taboo section.** (Not "sharper" — all of these are mutually equivalent, being
equivalences with LEM.) **Proposition 60 (iii)**: that for every `α > 1`
and `β ≥ 1` there is a `γ ≤ β` greatest with `α^γ ≤ β` is equivalent to LEM. **What separates it from
the CONSTRUCTIVE Proposition 59 (iii) is the SCOPE OF MAXIMALITY, not the bound** — both carry
`γ ≤ β`. Proposition 59 gives a greatest `γ` satisfying the *conjunction* (`γ ≤ β ∧ α^γ ≤ β`);
Proposition 60 demands a `γ ≤ β` that is greatest with `α^γ ≤ β` *outright*. The paper says as much
at its Theorem 58 discussion, where Enderton's classical schema drops the bound entirely: *"excluded
middle is equivalent to the existence of `γ` such that `γ ≤ δ` and `γ` is the greatest ordinal such
that `t γ ≤ δ`"*.

**What actually keeps all of it off the obstruction is the CARRIER, not the operator.** Their
ordinals are the HoTT `Ord` — sets with a transitive, extensional, wellfounded order — quantified
over *arbitrary* such ordinals, with a concrete construction by decreasing lists, in Agda. The
obstruction is about `ONote`, and is about that system's expressive reach rather than about
excluded middle. **The load-bearing property is that `ONote` is a concrete inductive type**: every
LEM-derivation above — § 2's Proposition 9, § 7's and § 8's alike — builds an ordinal from an
arbitrary proposition (`3 + P`, `P + 1`, `1 + P`), and no `ONote` denotes one — its constructors are
`zero` and `oadd : ONote → ℕ+ → ONote → ONote`, neither of which takes a proposition. So a statement quantified over all HoTT ordinals does not transfer, and
none of this is a re-proof of anything on Mathlib's `Ordinal`.

**Adjacent and unexamined — flagged, not claimed.** Their **Theorem 58** gives, for an endofunction
`t : Ord → Ord` preserving suprema up to a binary join with some `δ₀`, and any `δ ≥ δ₀`, a *greatest*
`γ ≤ δ` with `t γ ≤ δ`; it lists `α^(−)` (with `δ₀ = 1`, for `α ≥ 1`) among its instances. That is a
greatest-**below** operator, so it is the **order dual** of the nucleus material in the Lean file
(`snapNucleus` is `nfp`, a least fixed point **above**), which is exactly why it is worth a prior-art
read before anything here is strengthened. No such read is on record as of 2026-08-03; this is a
pointer, not a result.
*(⚠ Do NOT describe this paper's carrier as `Cnf`/`Brw`: those names belong to the authors' *earlier*
arXiv:2104.02549, which this paper cites as previous work it compares itself against. And its § 7 does
not support the claim that the paper's taboos reach this operator.)*

## The obstruction, stated

ZP-N's `omegaPow_no_fixedpoint` proves that **no `ONote` is a fixed point of `α ↦ ω^α`**. A `Nucleus` is
by definition **idempotent**, so `j (j x) = j x` — every value in its image is one of its own closed
points, and since `ONote` is inhabited, closed points always exist. Requiring those closed points to be
ε-numbers therefore demands a fixed point of `ω^·` inside a system that provably has none.

That is `no_snap_closure` (for an arbitrary idempotent endomap, no order needed) and
`no_snap_nucleus` (the `Nucleus`-typed corollary). The two together are the answer: the failure is not
a Mathlib packaging artifact and not a missing lemma. It is that **ε₀ is exactly the ordinal Cantor
normal form cannot name** — it is the supremum of the notation system, not a member of it — so the
closure operator has nothing in the system to settle on.

The surrounding positive results make that precise rather than merely asserted:

* `cmp_lt_tower` / `tower_cofinal` — every notation is strictly below some ω-tower stage. The tower is
  **cofinal** in `ONote`.
* `tower_no_upper_bound` — consequently no notation bounds the tower. The suprema the snap-closure
  would have to land on is absent from the carrier, not merely hard to construct.

So the missing object is a *supremum of an unbounded chain*, and its absence is a theorem about the
carrier, not a limitation of the proof.

## Is the choice in `snapNucleus` accidental or structural?

Both halves are measured here, and they split:

* **Nothing in the reasoning here needs choice.** Every theorem in the constructive development —
  including the impossibility itself and the full `LinearOrder`/`SemilatticeInf` structure on
  `SynONote` — is choice-free. **The one exception is deliberate and disclosed:**
  `mathlib_ONote_order_not_antisymm` measures `[propext, Classical.choice, Quot.sound]` because it is a
  statement *about* Mathlib's `repr`-based order, not part of the constructive development.
  **This does NOT classify `snapNucleus`'s own footprint as accidental** — that would be
  an eliminability claim, and no re-proof of `snapNucleus` was located as of 2026-08-02. Its status is **UNCLASSIFIED**
  (`ZeroParadox/Ordinal/SnapNucleus.lean` records the same).
* **The counterpart route via this carrier is blocked — for a different reason than choice.** What
  blocks it is **expressive reach**: *this* carrier cannot name the object the closure produces.
  **Scope, narrowly:** the result is about `ONote`-shaped notation systems, not about constructive
  mathematics in general. A system extending past ε₀ (Veblen, Bachmann-Howard) is not ruled out here —
  it is open and untouched here. **Say which sense, because the pin does ship Veblen:**
  `Mathlib/SetTheory/Ordinal/Veblen.lean` defines `veblen`, `ε_` and `Γ_`, but *semantically* — they
  are `noncomputable` functions on `Ordinal`, not a computable **notation system** of the
  `ONote`/`NONote` kind this file's argument is about. **The ε₀ ceiling is a fact about the NOTATION
  SYSTEMS, not about those Veblen functions**: `Mathlib`'s `Notation.lean` scopes `ONote`/`NONote` to
  "below `ε₀`", while the Veblen functions reach far past it — the same pin proves `ε₀ < Γ_ o` for
  every `o` (`epsilon_zero_lt_gamma`). Read the ceiling as applying to `veblen`/`ε_`/`Γ_` and it is
  flatly false; it applies to `ONote`/`NONote`. **No notation system past ε₀ is in this Mathlib pin as
  of 2026-08-02**; Bachmann-Howard is absent in either sense. *(One caveat, because a reader
  grepping `notation` in `Veblen.lean` lands on it first: its docstring says composing
  `invVeblen₁` with `Ordinal.CNF` "yields a predicative ordinal notation up to `Γ₀`". That is a
  RECIPE, not a shipped system — and `invVeblen₁` is itself noncomputable, defined via `sInf`. The
  claim above is about what the pin CONTAINS, and stands.)* So this is **not** a proof that the snap nucleus is
  constructively impossible, and **not** a claim that ε₀ requires choice.

These are compatible and should not be conflated. "The proof needs no choice" and "the carrier cannot
hold the answer" are different failures, and only the second one bites here.

## Does `ONote` carry a choice-free `SemilatticeInf`? (measured: yes, but not Mathlib's)

Mathlib gives `ONote` only a `Preorder` (`Mathlib/SetTheory/Ordinal/Notation.lean`), defined as
`le x y := repr x ≤ repr y` — routed through `ONote.repr` into `Ordinal`'s classically-built order machinery. It is
also genuinely **not** a partial order: `mathlib_ONote_order_not_antisymm` below exhibits `1 + ω` and
`ω` as distinct notations with equal `repr`, so antisymmetry fails. Mathlib's order on `ONote` is
therefore unusable here on both counts, and both counts are proved rather than asserted.

A choice-free order **is** available, and is built below from the syntactic comparator `ONote.cmp`
directly. `SynONote` is a type synonym for `ONote` carrying `x ≤ y := ONote.cmp x y ≠ .gt`. The
comparator laws needed (`syn_cmp_refl`, `syn_cmp_swap`, `syn_cmp_trans_lt`) are proved here by
structural induction on the notation, never through `repr`; Mathlib's `ONote.cmp_compares` cannot be
reused because it requires the `NF` predicate, which is itself defined via `repr` and carries choice.
The result is a `LinearOrder SynONote`, hence a `SemilatticeInf`, hence `Nucleus SynONote` typechecks —
and every piece of it is `[propext]` or cleaner. That is what makes `no_snap_nucleus` a statement about
an actually-inhabitable type rather than a vacuous one.

## Triviality assessment

The impossibility itself is, as mathematics, nearly trivial: `no_snap_closure` is a two-line argument
once `omegaPow_no_fixedpoint` is in hand — an idempotent map has a closed point, ε-numbers do not
exist here, done. It should not be read as a deep theorem. Its value is entirely in *what it names*:
it converts "we tried to build the counterpart and it did not work" into "the counterpart cannot
exist, and here is the one-line reason." That is a difference in kind, not in depth.

`cmp_lt_tower` and `tower_cofinal` are elementary too — the same structural induction as
`SyntacticCollapse.le_synVal_of_tower_le`, run in the opposite direction.

The genuinely non-trivial engineering is the `LinearOrder SynONote` instance, and specifically
`syn_cmp_trans_lt`: Mathlib proves the corresponding fact only via `ONote.cmp_compares`, which
requires `NF`, which is defined through `repr` and carries choice. Getting transitivity by
lexicographic induction on raw syntax instead is what makes a choice-free `SemilatticeInf` — and
therefore the `Nucleus`-typed statement `no_snap_nucleus` — available at all. Without it, the
obstruction could only be stated for bare endomaps, and the connection to `Nucleus` would be
informal.

## Prior art

`ONote`, `ONote.cmp`, `eq_of_cmp_eq` and `linearOrderOfCompares` are Mathlib. The technique of staying
on the syntactic substrate to avoid inherited choice is ZP-N's
(`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`); `synVal` and its monotonicity are from
`ZeroParadox/Ordinal/SyntacticCollapse.lean`, reused here. Nuclei are Mathlib's `Order/Nucleus.lean`
(point-free Lawvere-Tierney). That Cantor normal form names exactly the ordinals below ε₀ is classical
proof theory, not a result proved in the Lean file.

**The closest specialist precedent, named.** Castéran and Contejean's *hydra-battles* development (Coq)
carries a CNF datatype `T1` for the ordinals **below** ε₀, constructive (axiom-free / intuitionistic
outside its Schütte module), with ε₀ as the notation system's **supremum** — and, per our own prior-art
survey of 2026-06-27, *not* phrased as a least fixed point and carrying no least-fixed-point theorem.
That is the same carrier and the same supremum as here. Grimm's Gaia development (INRIA RR-8407) builds a
comparable `T1 ≈ ε₀` and treats ε₀ as a fixed point of `ω^·`, but **explicitly uses excluded middle and
choice** — the classical comparison point.

**The order construction below is ALSO theirs, and the citation above does not by itself cover it.**
Read from source — `coq-community/hydra-battles`, `theories/ordinals/Epsilon0/T1.v` — hydra-battles already
carries the CNF datatype (`Inductive T1`), a structural lexicographic comparator `compare_T1`, the
derived `lt α β := compare α β = Lt`, transitivity `lt_trans` by the same structural induction, and the
strict-order bundle `t1_strorder` — all on raw terms, by the same stay-on-the-syntax technique used here
for `SynONote`. So `syn_cmp_trans_lt` and `instLinearOrderSynONote` are a **re-derivation in a different
proof assistant, not a new construction**, and the "genuinely non-trivial engineering" framing above is
about the effort in Lean, never about novelty. Cited here explicitly because scoping the credit only to
"the carrier and the supremum" would have left this uncredited — the failure mode where a theorem-backed
layer carries a distinctive construction with its own separate prior art.

**Two further hydra-battles constructions are cited here because a sibling file instantiates them.**
`ZeroParadox/Ordinal/PricedInterface.lean` adjoins a top to `SynONote` and maps the result into
Mathlib's `Ordinal`. Both moves are Castéran's, and the credit above does not reach them:
`theories/ordinals/OrdinalNotations/ON_plus.v` builds the **sum of two ordinal notation systems**
generically (`compare_plus`, `plus_comp`, `lt_wf`, `ON_plus`, and `lt_eq_lt_dec` proving that
decidability of comparison survives the adjunction), of which "notations plus one adjoined point" is the
one-point instance; and `ON_Generic.v`'s **`ON_correct`** is the canonical statement of "this notation
system correctly denotes into that classical ordinal" (denotes below the target, onto the segment,
comparator agrees with the semantic order), **already instantiated at ε₀** in
`Schutte/Correctness_E0.v` (`inject`, `inject_lt_epsilon0`, `embedding`, `Instance Epsilon0_correct`).
Recorded here so that the credit sits with the order construction it extends, rather than only in the
file that uses it.

**What is not theirs:** the impossibility statement itself, and the Lean realization. Mathlib has no
usable equivalent — its `ONote` order is `repr`-routed (hence choice-carrying) and its `cmp_compares` is
`NF`-conditional with `NF` itself `repr`-defined, which is why the order had to be rebuilt here at all.

**The delta against them**, stated narrowly: neither states the *impossibility*. They build the
constructive system and observe where it stops; the Lean file proves that no idempotent endomap of that
carrier can have the ε-numbers as its closed points, which is what converts "the system stops here" into
"a closure operator of this shape cannot exist here." Given `omegaPow_no_fixedpoint` that conversion is
two lines (see the triviality assessment) — the contribution is the statement and its placement, not
depth.
