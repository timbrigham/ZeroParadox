import Mathlib.SetTheory.ZFC.Basic

/-!
# Zero as a Wall — the self-loop refutation and the diagonal engine (formal object)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

## Formal Overview
⊥/zero is the boundary self-reference cannot cross, and the provable core is one theorem:
**a well-founded relation admits no self-loop** (`wf_no_selfloop`), with the diagonal family hanging
off the engine `negation_no_fixedpoint`. ("Wall" is a flagged metaphor-nickname; the precise term is
*the metatheoretic boundary where ⊥'s self-reference cannot be internalized*.) The argument, the
prior art and the fences are in `ZeroParadox/Settheory/Wall.md`, beside this file.
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
    a self-contained family. Credit: Lawvere 1969; Yanofsky 2003 (Bull. Symbolic Logic 9(3):362–386).) -/
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
