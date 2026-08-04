import ZeroParadox.Ordinal.SyntacticCollapse
import Mathlib.Order.Nucleus

set_option maxHeartbeats 1000000

/-!
# No snap-shaped closure on the `ONote` carrier: a proved obstruction

## What this file is

An **obstruction result**. `ZeroParadox/Ordinal/SnapNucleus.lean` defines
`snapNucleus : Nucleus Ordinal` as `Ordinal.nfp (fun a => Ordinal.omega0 ^ a)`, with measured footprint
`[propext, Classical.choice, Quot.sound]`. This file asks the ZP-N question of that object — can the
same content be had choice-free on the syntactic ordinal-notation substrate? — and answers **no**, with a
machine-checked impossibility rather than a failed attempt.

## What this does NOT establish

* **`snapNucleus` is not made choice-free here.** Nothing below is a re-proof, replacement, or discharge
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
  Cantor-normal-form syntax) and on `SynONote`, the type synonym below carrying the comparator-derived
  order. `ONote` is not `Ordinal` and `SynONote` is not `Ordinal`. Exactly one theorem below mentions
  `Ordinal` at all — `mathlib_ONote_order_not_antisymm`, which is a fact about *Mathlib's* order and
  is disclosed as choice-carrying. Nothing here transports a result across the two carriers.
* **It is not a proof that ε₀ requires choice.** The obstruction proved below is about *notation
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
Taboos" holds several that do concern the fixed-base exponential.** **Proposition 52**: exponentiation is monotone in the base iff LEM,
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

**What actually keeps all of it off the obstruction below is the CARRIER, not the operator.** Their
ordinals are the HoTT `Ord` — sets with a transitive, extensional, wellfounded order — quantified
over *arbitrary* such ordinals, with a concrete construction by decreasing lists, in Agda. The
obstruction below is about `ONote`, and is about that system's expressive reach rather than about
excluded middle. **The load-bearing property is that `ONote` is a concrete inductive type**: every
LEM-derivation above — § 2's Proposition 9, § 7's and § 8's alike — builds an ordinal from an
arbitrary proposition
(`3 + P`, `P + 1`, `1 + P`), and
no `ONote` denotes one — its constructors are `zero` and `oadd : ONote → ℕ+ → ONote → ONote`, none of
which takes a proposition. So a statement quantified over all HoTT ordinals does not transfer, and
none of this is a re-proof of anything on Mathlib's `Ordinal`.

**Adjacent and unexamined — flagged, not claimed.** Their **Theorem 58** gives, for an endofunction
`t : Ord → Ord` preserving suprema up to a binary join with some `δ₀`, and any `δ ≥ δ₀`, a *greatest*
`γ ≤ δ` with `t γ ≤ δ`; it lists `α^(−)` (with `δ₀ = 1`, for `α ≥ 1`) among its instances. That is a
greatest-**below** operator, so it is the **order dual** of the nucleus material in this file
(`snapNucleus` is `nfp`, a least fixed point **above**), which is exactly why it is worth a prior-art
read before anything here is strengthened. No such read is on record as of 2026-08-03; this is a
pointer, not a result.
*(Their **Lemma 54** is separately cited in `ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`.
⚠ Do NOT describe this paper's carrier as `Cnf`/`Brw`: those names belong to the authors' *earlier*
arXiv:2104.02549, which this paper cites as previous work it compares itself against. Corrected
2026-08-02; the theorem numbers above were transposed until 2026-08-03, and until 2026-08-03 this
block asserted the paper's taboos did not reach this operator, which § 7 does not support.)*

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
proof theory, not a result of this file.

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
constructive system and observe where it stops; this file proves that no idempotent endomap of that
carrier can have the ε-numbers as its closed points, which is what converts "the system stops here" into
"a closure operator of this shape cannot exist here." Given `omegaPow_no_fixedpoint` that conversion is
two lines (see the triviality assessment) — the contribution is the statement and its placement, not
depth.

## Engineer's Take

Epsilon zero as a name means nothing specific on its own. What matters is that it is being used in the
same fashion. The relativity here is mapped very specifically, and it is relative to the framework it is
being used in.

It is interesting to think of epsilon zero as a constant like pi, specifically because of its filling a
role. That is literally what pi is doing. I simply never thought of it under those terms.
-/

namespace ZeroParadox

open ONote

/-! ### Laws of the syntactic comparator

Proved by structural induction on `ONote`. Nothing here touches `ONote.repr`, `NF`, or `Ordinal`, so
nothing inherits choice. Mathlib's `ONote.cmp_compares` proves the analogous facts but only under the
`NF` hypothesis, and `NF` is defined through `repr` — hence choice-carrying. These are the raw-syntax
replacements. -/

/-- Lexicographic decomposition of `Ordering.then` at `lt`. Both `Ordering` arguments range over a
three-element type, so this is decided outright. -/
theorem then_eq_lt_iff (o p : Ordering) :
    o.then p = Ordering.lt ↔ o = Ordering.lt ∨ (o = Ordering.eq ∧ p = Ordering.lt) := by
  cases o <;> cases p <;> decide

/-- `Ordering.swap` distributes over `Ordering.then`. -/
theorem swap_then (o p : Ordering) : (o.then p).swap = o.swap.then p.swap := by
  cases o <;> cases p <;> decide

/-- The syntactic comparator is reflexive. -/
theorem syn_cmp_refl : ∀ x : ONote, ONote.cmp x x = Ordering.eq
  | 0 => rfl
  | oadd e n a => by
      rw [ONote.cmp, syn_cmp_refl e, syn_cmp_refl a, cmp_self_eq_eq]
      rfl

/-- The syntactic comparator is antisymmetric as an orientation: swapping the arguments swaps the
`Ordering`. -/
theorem syn_cmp_swap : ∀ x y : ONote, (ONote.cmp x y).swap = ONote.cmp y x
  | 0, 0 => rfl
  | 0, oadd _ _ _ => rfl
  | oadd _ _ _, 0 => rfl
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂ => by
      rw [ONote.cmp, ONote.cmp, swap_then, swap_then, syn_cmp_swap e₁ e₂, syn_cmp_swap a₁ a₂,
        _root_.cmp_swap]

/-- `gt` in the syntactic comparator is `lt` reversed. -/
theorem syn_cmp_gt_iff_lt (x y : ONote) :
    ONote.cmp x y = Ordering.gt ↔ ONote.cmp y x = Ordering.lt := by
  constructor
  · intro h
    rw [← syn_cmp_swap x y, h]; rfl
  · intro h
    rw [← syn_cmp_swap y x, h]; rfl

/-- Transitivity of the strict syntactic order. Lexicographic induction on the notation structure. -/
theorem syn_cmp_trans_lt : ∀ (x y z : ONote),
    ONote.cmp x y = Ordering.lt → ONote.cmp y z = Ordering.lt → ONote.cmp x z = Ordering.lt
  | 0, 0, _, h₁, _ => Ordering.noConfusion h₁
  | oadd _ _ _, 0, _, h₁, _ => Ordering.noConfusion h₁
  | 0, oadd _ _ _, 0, _, h₂ => Ordering.noConfusion h₂
  | oadd _ _ _, oadd _ _ _, 0, _, h₂ => Ordering.noConfusion h₂
  | 0, oadd _ _ _, oadd _ _ _, _, _ => rfl
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, oadd e₃ n₃ a₃, h₁, h₂ => by
      rw [ONote.cmp, then_eq_lt_iff] at h₁ h₂
      rw [ONote.cmp, then_eq_lt_iff]
      rcases h₁ with he₁ | ⟨he₁, hr₁⟩ <;> rcases h₂ with he₂ | ⟨he₂, hr₂⟩
      · exact Or.inl (syn_cmp_trans_lt e₁ e₂ e₃ he₁ he₂)
      · obtain rfl := eq_of_cmp_eq he₂
        exact Or.inl he₁
      · obtain rfl := eq_of_cmp_eq he₁
        exact Or.inl he₂
      · obtain rfl := eq_of_cmp_eq he₁
        obtain rfl := eq_of_cmp_eq he₂
        refine Or.inr ⟨syn_cmp_refl _, ?_⟩
        rw [then_eq_lt_iff] at hr₁ hr₂
        rw [then_eq_lt_iff]
        rcases hr₁ with hn₁ | ⟨hn₁, ha₁⟩ <;> rcases hr₂ with hn₂ | ⟨hn₂, ha₂⟩
        · have p₁ : (n₁ : ℕ) < (n₂ : ℕ) := (cmp_eq_lt_iff (n₁ : ℕ) (n₂ : ℕ)).mp hn₁
          have p₂ : (n₂ : ℕ) < (n₃ : ℕ) := (cmp_eq_lt_iff (n₂ : ℕ) (n₃ : ℕ)).mp hn₂
          exact Or.inl ((cmp_eq_lt_iff (n₁ : ℕ) (n₃ : ℕ)).mpr (Nat.lt_trans p₁ p₂))
        · have hb : (n₂ : ℕ) = (n₃ : ℕ) := (cmp_eq_eq_iff (n₂ : ℕ) (n₃ : ℕ)).mp hn₂
          refine Or.inl ?_
          rw [← hb]; exact hn₁
        · have ha : (n₁ : ℕ) = (n₂ : ℕ) := (cmp_eq_eq_iff (n₁ : ℕ) (n₂ : ℕ)).mp hn₁
          refine Or.inl ?_
          rw [ha]; exact hn₂
        · have ha : (n₁ : ℕ) = (n₂ : ℕ) := (cmp_eq_eq_iff (n₁ : ℕ) (n₂ : ℕ)).mp hn₁
          have hb : (n₂ : ℕ) = (n₃ : ℕ) := (cmp_eq_eq_iff (n₂ : ℕ) (n₃ : ℕ)).mp hn₂
          refine Or.inr ⟨?_, syn_cmp_trans_lt a₁ a₂ a₃ ha₁ ha₂⟩
          rw [ha, hb]; exact cmp_self_eq_eq (n₃ : ℕ)

/-- Transitivity of the non-strict syntactic order. -/
theorem syn_cmp_trans_le {x y z : ONote} (h₁ : ONote.cmp x y ≠ Ordering.gt)
    (h₂ : ONote.cmp y z ≠ Ordering.gt) : ONote.cmp x z ≠ Ordering.gt := by
  cases hxy : ONote.cmp x y
  · cases hyz : ONote.cmp y z
    · rw [syn_cmp_trans_lt x y z hxy hyz]; decide
    · obtain rfl := eq_of_cmp_eq hyz
      rw [hxy]; decide
    · exact absurd hyz h₂
  · obtain rfl := eq_of_cmp_eq hxy
    exact h₂
  · exact absurd hxy h₁

/-! ### `SynONote`: the choice-free order on ordinal notations

A type synonym for `ONote` carrying the order *derived from the comparator* rather than Mathlib's
`repr`-based `Preorder`. This is what makes `Nucleus` typecheck on the notation side at all. -/

/-- `ONote` under the syntactic comparator order. A type synonym, so it does not pick up Mathlib's
`repr`-based (and therefore choice-carrying, and non-antisymmetric) `Preorder ONote`. -/
def SynONote : Type := ONote

/-- The identity map into the syntactically-ordered copy of `ONote`. -/
def toSyn (x : ONote) : SynONote := x

/-- The identity map out of the syntactically-ordered copy of `ONote`. -/
def ofSyn (x : SynONote) : ONote := x

@[simp] theorem ofSyn_toSyn (x : ONote) : ofSyn (toSyn x) = x := rfl
@[simp] theorem toSyn_ofSyn (x : SynONote) : toSyn (ofSyn x) = x := rfl

instance instPreorderSynONote : Preorder SynONote where
  le x y := ONote.cmp (ofSyn x) (ofSyn y) ≠ Ordering.gt
  lt x y := ONote.cmp (ofSyn x) (ofSyn y) = Ordering.lt
  le_refl x := by rw [syn_cmp_refl]; decide
  le_trans _ _ _ h₁ h₂ := syn_cmp_trans_le h₁ h₂
  lt_iff_le_not_ge x y := by
    constructor
    · intro h
      exact ⟨by rw [h]; decide, fun hc => hc ((syn_cmp_gt_iff_lt _ _).mpr h)⟩
    · rintro ⟨-, h2⟩
      cases hc : ONote.cmp (ofSyn y) (ofSyn x)
      · exact absurd (by rw [hc]; decide : ONote.cmp (ofSyn y) (ofSyn x) ≠ Ordering.gt) h2
      · exact absurd (by rw [hc]; decide : ONote.cmp (ofSyn y) (ofSyn x) ≠ Ordering.gt) h2
      · exact (syn_cmp_gt_iff_lt _ _).mp hc

/-- `SynONote` is linearly ordered by the syntactic comparator — choice-free, and computable. This is
the structure Mathlib's `Preorder ONote` cannot supply: that one is `repr`-based (choice) and not even
antisymmetric (distinct non-normal-form notations share a `repr`). -/
instance instLinearOrderSynONote : LinearOrder SynONote :=
  linearOrderOfCompares (fun x y => ONote.cmp (ofSyn x) (ofSyn y)) <| by
    intro a b
    show (ONote.cmp (ofSyn a) (ofSyn b)).Compares a b
    cases hc : ONote.cmp (ofSyn a) (ofSyn b)
    · exact hc
    · exact eq_of_cmp_eq hc
    · exact (syn_cmp_gt_iff_lt _ _).mp hc

/-! ### Why Mathlib's own order on `ONote` cannot be used here

Recorded separately from the constructive development above, because it is a statement *about* the
choice-carrying order rather than part of that development.

Mathlib declares `Preorder ONote` with `le x y := repr x ≤ repr y`, and declares it as a `Preorder`
and not a `PartialOrder` for a reason: antisymmetry genuinely fails, because notations that are not in
normal form can denote the same ordinal. `1 + ω` and `ω` are the smallest witness. Mathlib's positive
counterpart is `ONote.repr_inj`, and it requires `NF` on both arguments — the hypothesis this example
violates.

So Mathlib's order on `ONote` is unusable here on two independent counts: it routes through `repr`
into `Ordinal`'s classically-built order machinery, and it is not a partial order, let alone a `SemilatticeInf`. That
is why `SynONote` above builds its order from `ONote.cmp` instead. -/

/-- **Mathlib's `repr`-based order on `ONote` is not antisymmetric.** Two distinct notations —
`1 + ω` and `ω` — denote the same ordinal, so each is `≤` the other without being equal.

This is the one theorem in the file that touches `Ordinal`, and it therefore carries
`Classical.choice`, as disclosed in the purity check. That is expected: it is a fact about the
choice-carrying structure, not a constructive result. -/
theorem mathlib_ONote_order_not_antisymm :
    ∃ x y : ONote, x ≠ y ∧ ONote.repr x = ONote.repr y := by
  refine ⟨oadd 0 1 (oadd 1 1 0), oadd 1 1 0, by decide, ?_⟩
  have h : ONote.repr (oadd (1 : ONote) 1 0) = Ordinal.omega0 := by simp
  rw [ONote.repr, h]
  simp

/-! ### The tower is cofinal: the carrier has no home for the closure

These are the positive results that make the obstruction precise. `synVal` and its monotonicity come
from `ZeroParadox/Ordinal/SyntacticCollapse.lean`. -/

/-- **Every notation is strictly below a tower stage.** If a notation's syntactic valuation is below
`m`, the notation itself is strictly `cmp`-below `tower m`. Structural induction; the leading exponent
of `tower m` strictly dominates, so coefficients never matter. -/
theorem cmp_lt_tower : ∀ (x : ONote) (m : ℕ), synVal x < m → ONote.cmp x (tower m) = Ordering.lt
  | 0, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, (_ + 1), _ => rfl
  | oadd _ _ _, 0, h => absurd h (Nat.not_lt_zero _)
  | oadd e n a, (m + 1), h => by
      have he : synVal e < m := Nat.lt_of_succ_lt_succ h
      have hrec := cmp_lt_tower e m he
      show ONote.cmp (oadd e n a) (oadd (tower m) 1 0) = Ordering.lt
      rw [ONote.cmp, hrec]
      rfl

/-- **The ω-tower is cofinal in the notations.** Every notation is strictly below some tower stage —
so the notation system is exactly "the ordinals below the tower's limit", with nothing left over
above. -/
theorem tower_cofinal (x : ONote) : ∃ n : ℕ, ONote.cmp x (tower n) = Ordering.lt :=
  ⟨synVal x + 1, cmp_lt_tower x _ (Nat.lt_succ_self _)⟩

/-- **No notation is an upper bound for the tower.** The supremum the snap-closure would have to land
on (ε₀) is absent from the carrier — this is a theorem about `ONote`, not a gap in a construction. -/
theorem tower_no_upper_bound (x : ONote) : ∃ n : ℕ, ONote.cmp (tower n) x = Ordering.gt := by
  obtain ⟨n, hn⟩ := tower_cofinal x
  exact ⟨n, (syn_cmp_gt_iff_lt _ _).mpr hn⟩

/-! ### The obstruction -/

/-- **`ω^·` moves every notation.** The equational form of ZP-N's `omegaPow_no_fixedpoint`. -/
theorem omegaPow_ne_self (x : ONote) : omegaPow x ≠ x := by
  intro h
  have := omegaPow_no_fixedpoint x
  rw [h, syn_cmp_refl] at this
  exact Ordering.noConfusion this

/-- **No idempotent endomap of `ONote` has ε-number closed points.**

This is the obstruction in its sharpest, order-free form: idempotence alone is enough. An idempotent
`j` fixes everything in its image, and `ONote` is inhabited, so `j` has at least one closed point. If
every closed point had to be a fixed point of `ω^·`, that would exhibit a fixed point of `ω^·` among
the notations — and `omegaPow_ne_self` says there is none.

Note how little is assumed: no order, no monotonicity, no meet-preservation, no inflationarity. Any
*closure operator whatsoever* on this carrier fails the snap property. -/
theorem no_snap_closure (j : ONote → ONote) (hidem : ∀ x, j (j x) = j x) :
    ¬ ∀ x : ONote, j x = x → omegaPow x = x := by
  intro h
  exact omegaPow_ne_self (j 0) (h (j 0) (hidem 0))

/-- The biconditional form: no idempotent endomap has closed points *exactly* the ε-numbers. -/
theorem no_snap_closure_iff (j : ONote → ONote) (hidem : ∀ x, j (j x) = j x) :
    ¬ ∀ x : ONote, j x = x ↔ omegaPow x = x :=
  fun h => no_snap_closure j hidem fun x hx => (h x).mp hx

/-- **No nucleus on `SynONote` has ε-number closed points.**

The `Nucleus`-typed corollary of `no_snap_closure`, on the choice-free `SemilatticeInf` built above.
This is the direct counterpart-statement for `snapNucleus`: on `Ordinal`, the snap nucleus's closed
points are exactly the ε-numbers (`snapNucleus_epsilon0`); on the constructive carrier, no nucleus can
have that property at all.

The statement is not vacuous — `Nucleus SynONote` is inhabited (`id` is a nucleus). What fails is the
snap property, not the existence of nuclei. -/
theorem no_snap_nucleus (j : Nucleus SynONote) :
    ¬ ∀ x : SynONote, j x = x → omegaPow (ofSyn x) = ofSyn x :=
  fun h => no_snap_closure (fun x => ofSyn (j (toSyn x)))
    (fun x => congrArg ofSyn
      (le_antisymm (j.idempotent' (toSyn x)) (j.le_apply' (j (toSyn x)))))
    (fun x hx => h (toSyn x) hx)

/-- `Nucleus SynONote` is inhabited, so `no_snap_nucleus` is a real constraint rather than a vacuous
quantification over an empty type. -/
def idNucleus : Nucleus SynONote where
  toFun x := x
  map_inf' _ _ := rfl
  idempotent' _ := le_refl _
  le_apply' _ := le_refl _

end ZeroParadox

/-! ## Axiom Purity Check

Target: `[propext]` or cleaner on everything, including the `LinearOrder`/`SemilatticeInf` structure.
Contrast the measured `[propext, Classical.choice, Quot.sound]` on `snapNucleus` in
`ZeroParadox/Ordinal/SnapNucleus.lean`. That footprint is **UNCLASSIFIED, not irreducible** — an earlier
version of this line called it irreducible on the grounds that "choice is in the `Ordinal` type," which is
FALSE as measured: `Ordinal` is `[propext, Quot.sound]`. Choice enters via `Ordinal.instLinearOrder`,
`nfp`, `omega0` and `epsilon`. Whether it is removable is open; not attempted in this corpus as of 2026-08-02. -/

section PurityCheck
open ZeroParadox
#print axioms then_eq_lt_iff
#print axioms swap_then
#print axioms syn_cmp_refl
#print axioms syn_cmp_swap
#print axioms syn_cmp_gt_iff_lt
#print axioms syn_cmp_trans_lt
#print axioms syn_cmp_trans_le
#print axioms instPreorderSynONote
#print axioms instLinearOrderSynONote
-- The single deliberate exception: a statement *about* Mathlib's choice-carrying `repr`-based order,
-- not part of the constructive development. Expected to report `Classical.choice`.
#print axioms mathlib_ONote_order_not_antisymm
#print axioms cmp_lt_tower
#print axioms tower_cofinal
#print axioms tower_no_upper_bound
#print axioms omegaPow_ne_self
#print axioms no_snap_closure
#print axioms no_snap_closure_iff
#print axioms no_snap_nucleus
#print axioms idNucleus
end PurityCheck
