import Mathlib.SetTheory.ZFC.Basic

/-!
# Zero as a Wall — the metatheoretic boundary, as a failure-mode taxonomy (formal object)

**Name: "Zero as a Wall"** — ⊥/zero is the boundary self-reference cannot cross. Precise gloss (for
translation / external readers): *the metatheoretic boundary where ⊥'s self-reference cannot be
internalized.* ("Wall" is a flagged metaphor-nickname per the project idiom rule; the precise term is the
gloss.)

Across five separate pushes (fork unification, the Quine atom CC-2, MC-1, "realization is the choice",
the faithfulness criterion) the framework keeps landing on the SAME boundary: a structural shadow Lean's
well-founded kernel CAN host, plus a metatheoretic residue it CANNOT. This file represents that boundary
as an **object-level theorem**, the honest in-kernel face of it.

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
  `real_not_equiv_padic` (ℝ and ℚ_p are both completions of ℚ but no equivalence transfers
  one to the other) and `ZPP.categorical_fork_strict` (μ empty / ν inhabited — the two ends, provably
  distinct).
- The FORMAL SIGNATURE of the wall is the contrast: shadow realizable choice-free (proved upstream) ∧
  literal self-loop refuted under well-foundedness (proved here). The wall is that pairing, not a claim
  that the residue is "closed."

## Prior art and library overlap (cite, do not reinvent)
- The diagonal-family unification — Cantor / Russell / Gödel / Turing / Tarski as one diagonal argument via
  a single fixed-point theorem — is **Lawvere (1969)**, "Diagonal Arguments and Cartesian Closed Categories"
  (LNM 92, pp. 134–145; TAC Reprint 15, 2006), and **Yanofsky (2003)**, "A Universal Approach to
  Self-Referential Paradoxes, Incompleteness and Fixed Points" (Bull. Symbolic Logic 9(3):362–386;
  arXiv:math/0305282). The unification is THEIRS; this file formalizes it and links it to ⊥.
- The point-surjective theorem is already in **Mathlib**: `Function.exists_fixed_point_of_surjective` (its
  own docstring calls it an instance of Lawvere's fixed-point theorem), with `Function.cantor_surjective`
  for Cantor. `lawvere_fixedpoint` and `cantor_via_engine` below are independent axiom-free re-derivations,
  kept for a self-contained family. The honest delta is the PRESENTATION — all four (Lawvere + Cantor +
  Russell + Turing) as corollaries off one named engine — not the theorems, which are not new.
- The **well-founded / membership / Bool / logical** re-proofs below have exact library equivalents too,
  kept as self-contained hubs alongside the function-fixed-point ones: `wf_no_selfloop` is Mathlib's
  `WellFounded.irrefl` (`Mathlib/Order/WellFounded.lean:66`); `no_quine_atom` (`x ∉ x`) is
  `ZFSet.mem_irrefl` (`Mathlib/SetTheory/ZFC/Basic.lean:631`); `bool_not_no_fixedpoint` is
  `Bool.not_ne_self`; and `negation_no_fixedpoint` (`¬(p ↔ ¬p)`) is core Lean's `not_iff_self` /
  `iff_not_self`. The delta is again the PRESENTATION — one named engine with these as its faces — not
  the lemmas, which are standard.
- **⚠ Three stronger library forms, measured 2026-07-29. Read before re-proving anything in this family.**
  A gloss here previously said "`Std.Irrefl r` unfolds to `¬ r x x`" — **it does not**; `Std.Irrefl` is a
  *class with a field* (core `Init/Core.lean:2588`), so `WellFounded.irrefl h : Std.Irrefl r` and you
  project `(WellFounded.irrefl h).irrefl x`. That matters, because Mathlib's form being class-valued is
  what makes the following free:
  * **`WellFounded.asymmetric`** (`Mathlib/Order/RelClasses.lean:225`) is **strictly stronger** than
    `wf_no_selfloop` — it forbids 2-cycles between *distinct* points, with `asymmetric₃` (`:229`) for
    3-cycles. Irreflexivity is its `a := b` instance. So `wf_no_selfloop` is the weakest rung of a published chain; this file states it
    deliberately as the one-cycle case, with `wf_no_cycle` below covering cycles of any length.
  * **Instance resolution already carries it.** `IsWellFounded → Std.Asymm` is registered
    (`Mathlib/Order/RelClasses.lean:234`), so `irrefl_of` / `asymm_of` fire on any type with the instance — and `ZFSet`
    has it (`Mathlib/SetTheory/ZFC/Basic.lean:622`). Hand-rolled `∀`-form restatements get none of that machinery.
  * **`wellFounded_iff_isEmpty_descending_chain`** (`Mathlib/Order/WellFounded.lean:**51**`) is a
    **biconditional**: `WellFounded r ↔ IsEmpty {f : ℕ → α // ∀ n, r (f (n+1)) (f n)}`. A self-loop is
    the *constant* descending chain, so it renders the non-well-founded side as **"the host contains an
    infinite ℕ-indexed descent."** That is the **INFINITE pole** the two-pole hard rule asks for, which
    the `r x x` form hides. **Now adopted** at `Multihomed/Boundary.lean` § I-b
    (`floor_descent_from_bot`, `bot_not_acc`, `floor_not_wellFounded_via_descent`).
    The **pointwise** form is `not_acc_iff_exists_descending_chain` (`:34`) —
    `¬ Acc r x ↔ ∃ f, f 0 = x ∧ ∀ n, r (f (n+1)) (f n)` — which is the one that locates the descent AT a
    given point. ⚠ Its *extract-a-chain* direction (`:36-38`) builds the sequence with `.choose_spec` and
    so carries `Classical.choice`. **⚠ The natural inference — "supply the witness yourself and use only
    the other direction to stay choice-free" — is FALSE, and was MEASURED false**: `#print axioms`
    follows the STATEMENT, so citing the biconditional at all pulls in the choice used by the direction
    you did not take. See `Multihomed/Boundary.lean` § I-b's purity block, where the one-line `mpr`
    version measured `[propext, Classical.choice, Quot.sound]` and only a HAND proof came back
    axiom-free. (Line numbers verified at source 2026-07-29; an earlier revision of this bullet cited
    `:46`, which is a line inside `acc_iff_isEmpty_descending_chain`'s proof, not the lemma.)

## The wall as a failure-mode taxonomy (built one condition-set at a time)

The wall is not one theorem — its structure is the MAP from a held-fixed condition-set to the PRECISE
failure signature self-reference produces there. `wf_no_selfloop` is the well-founded-set entry; the rest
are proved in their own modules, each a checkable witness whose hypotheses ARE the conditions. Method:
hold one condition-set fixed, characterize the exact failure, then read the pattern across them (the same
experiment-style discipline that narrowed MC-1 and that EXTRACTED `wf_no_selfloop` itself).

| Condition-set held fixed | Failure SIGNATURE | Theorem (module) | Footprint |
|---|---|---|---|
| logical / `Prop` (**the ENGINE**) | NEGATION HAS NO FIXED POINT (`¬(p↔¬p)`) | `negation_no_fixedpoint` (here) | axiom-free |
| sets/functions, Cantor (**engine-linked ✓**) | no self-surjection onto predicates | `cantor_via_engine` (= engine at the diagonal) | axiom-free |
| naive comprehension, Russell (**engine-linked ✓**) | no membership realizes every predicate | `russell_via_engine` (via `lawvere_fixedpoint` + engine) | axiom-free |
| deciders, Turing (**engine-linked ✓**) | no self-surjection onto Bool-deciders (the halting diagonal) | `no_self_decider` (Lawvere + Bool engine); faithful: `ZPK.…undecidable` | axiom-free |
| any well-founded relation | NO CYCLE (any length) | `wf_no_cycle` (1-cycle: `wf_no_selfloop`) | axiom-free |
| set theory + Foundation | NO MEMBERSHIP CYCLE (any length) | `no_membership_cycle` (1-cycle: `no_quine_atom`) | choice-free |
| ordinal notation naming `<ε₀` | UNREACHABLE FROM BELOW | `ZPN.omegaPow_no_fixedpoint` | choice-free |
| lightweight categorical typeclass | NO NON-VACUOUS UNIFIER | `ZPP_DualityFork.fixed_pole_forces_collapse` | axiom-free |
| metric completion of ℚ | NO TRANSFER (same role) | `ZPP.real_not_equiv_padic` | choice |
| μ/ν coalgebra | DISTINCT ENDS | `ZPP.categorical_fork_strict` | choice |
| computability (Kleene) | EXISTS-BUT-UNDECIDABLE | `ZPK.infinite_quine_family` (∃, ∞-many) + `ZPK.isComputationalQuine_undecidable` (¬ComputablePred) | choice |

`lawvere_fixedpoint` (here, axiom-free) is the GENERAL theorem unifying the **diagonal family** — Cantor and
Russell are its corollaries, triggered by the engine (`Not` is fixed-point-free). Within the diagonal family
this is a real unification *theorem*, not the grand conjecture; the well-founded family (below) is proved by a
different mechanism (induction), and whether it folds in too is the open one-root-or-two question.

**Reframe of that question (2026-07-29) — and it is NOT a new result; every piece below is published.**
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
  **Theorem 7.6**, p. 30 — *"the only well-founded fixed point is the initial algebra"*: a well-founded
  host admits no fixed point except the μ end. The standard name for the *axis* is the **well-founded part
  / the coreflection into well-founded coalgebras** (their Definition 5.1, p. 22, credited there to their
  own **[5]** — Adámek-Milius-Moss, *Fixed points of functors*, JLAMP 95, 2018 — and the coreflection to
  **[6]**, Adámek-Milius-Moss-Sousa, *Well-pointed coalgebras*, LMCS 9(2), 2014). **Taylor [27,28] is
  credited in that paper with introducing well-founded coalgebras for a general endofunctor and with the
  General Recursion Theorem — NOT with the well-founded part and NOT with the coreflection**; an earlier
  revision of this bullet misattributed Definition 5.1 to him. (`CLAIMS.md`'s ledger row crediting Taylor
  with "well-founded ⟺ recursive" is correct and is a different claim.)
  What this file proves is the **one-relation shadow** of that theorem, not the coalgebraic statement.

**So the framework's own narrow observation, stated without overclaim:** the theorems this taxonomy assigns
to the well-founded family are, on inspection, *refusals of the engine's own ν output* rather than an
independent root of self-reference — `wf_no_selfloop` instantiated per host (`no_quine_atom` where the host
is well-founded; `quineHost_not_wellFounded` / `floor_not_wellFounded` where it is not). That is a claim
about **this repo's taxonomy**, not about mathematics, and the literature above already presents the split
this way. Note the scope limit: it covers the **well-founded family only** — the ε₀ row
(`ZPN.omegaPow_no_fixedpoint`) is ordinal arithmetic, *not* a self-loop instantiation, so "every row is a
ν-refusal" would be false. The narrow one-root question is still answered **no**: `wf_no_selfloop` is proved
by accessibility, not by the engine (`Wall_OneRoot.lean`'s `selfloop_permitted` / `engine_is_wf_free` stand).
Full development: `.claude-local/notes/wall_one_root_or_two_trinary_2026-07-29.md`.

The failure SIGNATURE changes with the conditions — distinct ways the one self-reference resists
internalization, not one failure repeated. The formal/metatheoretic frontier is itself part of the map:
`x∉x`, ε₀∉ONote, no-self-loop are in-kernel; the cross-category identity (MC-1's identity half) and the
literal AFA universe are metatheoretic-only.

**The computability row is the pivot (2026-06-27).** It is the ONLY framework where the fixed point is
NOT refuted/unreachable but provably EXISTS — `infinite_quine_family` gives infinitely many — while the
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
settle it. (See `.claude-local/notes/wall_as_failure_mode_taxonomy_2026-06-27.md`.)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

/-- **THE ENGINE — negation has no fixed point.** No proposition `p` satisfies `p ↔ ¬p` (a contradiction).
    This is the root every wall face descends from (Lawvere): the canonical fixed-point-free map is
    negation, and Lawvere's fixed-point theorem turns "negation has no fixed point" into "genuine
    self-reference cannot be internalized." Where this FAILS (a fixed point of negation exists) the system
    collapses. The μ/ν co-duality is exactly its two regimes — μ = no fixed point (this / the wall);
    ν = a fixed point exists (the self-referential object: Quine atom, Y combinator). -/
theorem negation_no_fixedpoint (p : Prop) : ¬ (p ↔ ¬ p) := fun h =>
  have hnp : ¬ p := fun hp => h.mp hp hp
  hnp (h.mpr hnp)

/-- **Lawvere grounding — Cantor IS the engine at the diagonal.** No `g : A → (A → Prop)` is surjective:
    if the diagonal predicate `fun a => ¬ g a a` were hit at some `a₀`, then `g a₀ a₀ ↔ ¬ g a₀ a₀`, refuted
    by `negation_no_fixedpoint`. This exhibits a wall face (Cantor / no self-surjection onto predicates) as
    a DIRECT instance of "negation has no fixed point" — the first step turning the "all faces are one
    phenomenon" convergence from picture into theorem. The diagonal here is exactly the diagonal-and-negate
    move shared by Cantor / Russell / Gödel / Turing. (Already in Mathlib as `Function.cantor_surjective`;
    re-proved here axiom-free off the shared engine.) -/
theorem cantor_via_engine {A : Type*} (g : A → (A → Prop)) : ¬ Function.Surjective g := by
  intro hsurj
  obtain ⟨a₀, ha₀⟩ := hsurj (fun a => ¬ g a a)
  exact negation_no_fixedpoint _ (iff_of_eq (congrFun ha₀ a₀))

/-- **Lawvere's fixed-point theorem — the general engine behind the whole diagonal family.** If some
    `e : A → (A → B)` is point-surjective, then EVERY `f : B → B` has a fixed point. The diagonal family
    (Cantor / Russell / Turing / Gödel / Tarski) is the contrapositive at a fixed-point-FREE `f` — namely
    negation, whose fixed-point-freeness is exactly `negation_no_fixedpoint`. So all of them are one
    theorem (this) triggered by the one engine. (This is Mathlib's
    `Function.exists_fixed_point_of_surjective`, curried `A → A → B`; re-proved here axiom-free as the hub of
    a self-contained family. Credit: Lawvere 1969, Yanofsky 2003 — see the header.) -/
theorem lawvere_fixedpoint {A : Type*} {B : Type*} (e : A → (A → B))
    (he : Function.Surjective e) (f : B → B) : ∃ b, f b = b := by
  obtain ⟨a, ha⟩ := he (fun x => f (e x x))
  exact ⟨e a a, (congrFun ha a).symm⟩

/-- **Russell — naive comprehension is impossible (a corollary of Lawvere + the engine).** No membership
    relation `mem : A → A → Prop` realizes every predicate: viewed as `A → (A → Prop)` it would be
    surjective, so Lawvere gives a fixed point of `Not` (an element with `mem r r ↔ ¬ mem r r`, the Russell
    set), refuted by `negation_no_fixedpoint`. Exhibits Russell as the same engine as Cantor, now routed
    through the general theorem. -/
theorem russell_via_engine {A : Type*} (mem : A → A → Prop) : ¬ Function.Surjective mem := by
  intro hmem
  obtain ⟨r, hr⟩ := lawvere_fixedpoint mem hmem Not
  exact negation_no_fixedpoint r (iff_of_eq hr).symm

/-- Boolean negation has no fixed point — the 2-valued form of the engine (the decider-flip behind
    Turing / the halting problem). -/
theorem bool_not_no_fixedpoint (b : Bool) : (!b) ≠ b := by cases b <;> decide

/-- **Turing / decider diagonal via Lawvere.** No `g : A → (A → Bool)` is surjective: Lawvere would force a
    fixed point of Boolean negation, which `bool_not_no_fixedpoint` forbids. This is the abstract skeleton
    of the halting argument — a decider is a map to `Bool`, and the diagonal input flips it. The faithful
    computability instance (with a real machine model, choice-laden) is
    `ZeroParadox.isComputationalQuine_undecidable`. -/
theorem no_self_decider {A : Type*} (g : A → (A → Bool)) : ¬ Function.Surjective g := by
  intro hg
  obtain ⟨b, hb⟩ := lawvere_fixedpoint g hg (fun b => !b)
  exact bool_not_no_fixedpoint b hb

/-- **THE WALL (general).** A well-founded relation admits no self-loop: no `x` with `r x x`. This is the
    object-level core the metatheoretic boundary reduces to — the literal self-referential fixed point
    (`x ∈ x`) cannot exist where the relation is well-founded. -/
theorem wf_no_selfloop {α : Type*} {r : α → α → Prop} (h : WellFounded r) (x : α) : ¬ r x x := by
  have key : ∀ a, Acc r a → ¬ r a a := by
    intro a acc
    induction acc with
    | intro y _ ih => exact fun hy => ih y hy hy
  exact key x (h.apply x)

/-- **Set-theoretic face.** Under Foundation (`∈` well-founded on `ZFSet`), no set is self-membered: the
    literal Quine atom `⊥ = {⊥}` (`x ∈ x`) is refuted in-kernel. The structural shadow of the same object
    IS realizable choice-free (`AbstractSelfApp`); only the literal membership self-loop is walled off. -/
theorem no_quine_atom (x : ZFSet) : x ∉ x :=
  wf_no_selfloop ZFSet.mem_wf x

/-- **The wall, full strength.** A well-founded relation has no cycle of ANY length: no `x` is reachable
    from itself by one-or-more `r`-steps (`Relation.TransGen r x x`). `wf_no_selfloop` is the n=1 case;
    this also rules out 2-cycles, n-cycles — every cyclic self-reference. Proof: the transitive closure of
    a well-founded relation is well-founded, so it too has no self-loop. -/
theorem wf_no_cycle {α : Type*} {r : α → α → Prop} (h : WellFounded r) (x : α) :
    ¬ Relation.TransGen r x x :=
  wf_no_selfloop h.transGen x

/-- **Set-theoretic face, full strength.** Under Foundation, no set lies on a membership cycle of any
    length (`x ∈ … ∈ x`) — not just `x ∉ x`. The genuine self-referential set is excluded in every cyclic
    form, so the wall is not a quirk of the 1-step case. -/
theorem no_membership_cycle (x : ZFSet) : ¬ Relation.TransGen (· ∈ ·) x x :=
  wf_no_cycle ZFSet.mem_wf x

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms negation_no_fixedpoint
#print axioms cantor_via_engine
#print axioms lawvere_fixedpoint
#print axioms russell_via_engine
#print axioms no_self_decider
#print axioms wf_no_selfloop
#print axioms no_quine_atom
#print axioms wf_no_cycle
#print axioms no_membership_cycle
end PurityCheck
