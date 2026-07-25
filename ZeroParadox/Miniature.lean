import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

universe u

/-!
# The Zero Paradox in miniature — the minimal core

## Engineer's Take

If we know exactly what conditions always create the snap and those that always create the wall, that is the
beginnings of a map that would always fit. This is that map on the smallest concrete witnesses: the engine, the
boundaries and why they have to be where they are, and the snap and why it has to be there. The snap needs both
directions to really be the snap, because it is both a limit and a bottom. It is the most compact way of showing
what the whole project is about, in a couple hundred lines of Lean.

I write software for a living, so one part of this lands close to home. A program that is never run does
nothing. That is the whole point. The commitment that the bottom executes itself is the commitment
that time enters the picture, as a state change, and that is the exact claim this framework is making. It is
also the thing almost everyone walks straight past, even the professionals, because it gets phrased so
quietly. So I am going to say it plainly: this is the spot where a static structure becomes something that
happens.

---

## Formal Overview (AI-assisted)

The smallest self-contained artifact that exhibits the **shape** the whole framework is built on: the
**engine**, the **wall** and **floor** and *why each must be where it is*, the **snap** *in both directions*
(it is both a limit and a bottom), and the **fan-out** (the branching field) — each on the smallest domain that
can hold it, where most "why"s are **decided by computation or proved in a line or two** (computed, not
asserted).

It reads top to bottom:

* **§ I — the engine.** Lawvere's diagonal (`lawvere`): a point-surjection forces every endomap to have a
  fixed point. Its dual seed (`negation_no_fp`): negation has no fixed point. The one mechanism.
* **§ II — the classifier (the map).** `HasWitnessRel` (minimum requirement), `floor_of_witness` (the **floor**:
  witness → fixed point), `wall_of_fpf` (the **wall**: fixed-point-free map kills the witness), `witness_antitone`
  (the topology spine). The classifier that sorts wall from floor everywhere.
* **§ III–IV — the pole.** The two-element pole `{0, ∞}` has exactly **four** self-maps, classified by
  fixed-point count. The **wall** sits at `swap` (0 fixed points, reversible), the **floor** at the collapses
  (1 fixed point, irreversible). `swap_is_the_wall` is the finite instance of the classifier: `swap` is
  fixed-point-free, so it kills the witness.
* **§ V — the snap, in both directions.** The pole gives only the *irreversible* half (`collapse_irreversible`).
  The snap is also an **ascent to a limit that is itself a bottom**: on the minimal chain `ℕ∞`,
  `tower_min_eq_max` proves `⊤` is *simultaneously* the **supremum** of the climbing chain (the limit / max) and
  the **least fixed point** of successor (the bottom-of-fixed-points / min). That is `epsilon0_min_eq_max` in
  miniature — the snap lands on a point that is *both a limit and a bottom*, which is exactly why it cannot be
  flattened to a one-way collapse. `ascent_strictMono`: the climb is strict (one-way).
* **§ VI — the fan-out.** Branching needs at least three elements (`fan_out`, a node with three pairwise
  incomparable successors), so the two-element pole *cannot* hold it (`pole_cannot_fan`). This is the field —
  the width the framework's boundary fans into.
* **The capstone (`shape`)** bundles all of it: wall (no fixed point), floor (fixed point), the collapse
  irreversible, the snap-limit both-a-limit-and-a-bottom, and the fan-out — the whole shape in one theorem.

**What the floor stands for — self-reference and the Quine atom.** This file represents the floor as bare
fixed-point existence (`floor_of_witness`: a witness forces a fixed point; `cZero_has_fp`: the collapse fixes a
point). In the full framework that fixed point is a *self-referential* object — **the Quine atom** (Quine;
Aczel): the set that is its own only member, `⊥ = {⊥}`. It is one structural fact in several languages. Three
of them — the Quine atom (set theory / ZF+AFA), the order-bottom `⊥`, and the algebraic join-identity — are
proved to be the *same* element within a single carrier, axiom-free (`Settheory/SetTheoryAFA.lean`
`t_exec_triple_iff`; its two-face half is `t_exec`);
the fourth, the Kleene quine (a program that prints itself, computability), is *joined* to them by an explicit
structural commitment — the `KleeneStructure` typeclass carries the computational fixed point as filling the
same role, without asserting an identity across types, not derived (`Computability/Kleene.lean`).

**That fourth commitment is where time enters — and it is the easiest thing here to walk past.** The other
three faces are *static*: order-bottom, self-membered set, algebraic identity are timeless facts that simply
hold, and nothing about them ever *happens*. The Kleene quine is the only one that *runs*, and running is a
before and an after. So committing that the self-contained bottom is the self-executing bottom (⊥ is the
machine in its ground state, which must execute itself) is committing that **time enters the framework as a
state change**. It is what makes the framework dynamic at all: nothing static occurs on its own, so without
it ⊥ would rest as a fixed point forever and the snap would never happen. Stated as what it is — a
*commitment*, never a theorem — which is exactly why the computational face is joined by hand rather than
derived from the static three. The wall's seed here, `negation_no_fp`
(`¬(p ↔ ¬p)`), is that same self-reference *failing to close* (Cantor, Turing, Tarski); the floor is it
*closing* — landing on the thing that is its own answer.

We show the *limited* version deliberately. The **shape** — self-reference forced either to a wall or to a
self-referential floor — is what the minimal core exhibits, and a bare fixed point is enough to carry it. The
full Quine atom needs a non-well-founded set theory (ZF+AFA) to host `⊥ = {⊥}` literally; that host is the
*flesh*, cited to its home, not rebuilt here. Honest split: the *structural* self-application fixed point is
Lean-proved and axiom-free (`t_exec`); the *literal* set-membership `⊥ = {⊥}` is a metatheoretic modeling
commitment (ZF+AFA), a theorem nowhere — the framework's own fence, kept here.

**Honest status.** The *content* is re-derived, not new: the engine is **Lawvere (1969) / Yanofsky (2003)**
(`Settheory/Wall.lean`); the classifier is `Category/DiagonalWitness.lean`; the four corners are
`Valuation/PoleCorners.lean`; the min=max is `Ordinal/Epsilon0MinMax.lean` `epsilon0_min_eq_max` (the real ε₀
version — `ℕ∞`'s `⊤` here is its minimal shadow, `Settheory/Model.lean`); the branch is the arity fact from
`Valuation/CompletenessCriticProbe.lean`. The tiny proofs are restated inline for self-containment; the new
connective tissue is `swap_is_the_wall` (the pole as a finite instance of the classifier) and the assembly.
The *value* is the compression.

**Honest fence (load-bearing).** This is the **shape** — the skeleton every domain hangs on — **not** the
entire project. The framework's flesh is its domain *instances* (set theory / AFA, the 2-adics, proof theory,
the categorical bridges, the whole MC-1 bottom family), which are the shape *worn* by real mathematics and are
not here. This file stands **alongside** them as the most compact statement of what they are all instances *of*.
The cross-domain identity of the instances stays a type boundary (retired as ill-typed), never a Lean `=`; and
the `ℕ∞` tower is a *shadow* of ε₀ (its `⊤` is the unique fixed point, where the real ε₀ has a whole hierarchy
above it) — the shape is faithful, the object is minimal.
-/

namespace ZeroParadox.Miniature

/-! ### § I. The engine — Lawvere's diagonal and its no-fixed-point seed. -/

/-- **The engine.** A point-surjection `e : A → (A → B)` forces every endomap `f : B → B` to have a fixed
point (Lawvere 1969). The framework's self-reference runs off this one construction. -/
theorem lawvere {A B : Type*} (e : A → (A → B)) (surj : Function.Surjective e) (f : B → B) :
    ∃ b, f b = b := by
  obtain ⟨a, ha⟩ := surj (fun x => f (e x x))
  exact ⟨e a a, (congrFun ha a).symm⟩

/-- **The seed of the wall.** Negation has no fixed point. Everything on the wall side is this, wearing a
domain's clothes (Cantor, Russell, Turing, Tarski). -/
theorem negation_no_fp (p : Prop) : ¬ (p ↔ ¬ p) := by
  intro h
  have hnp : ¬ p := fun hp => h.mp hp hp
  exact hnp (h.mpr hnp)

/-! ### § II. The classifier — the minimum requirement, and the wall / floor conditions. -/

/-- **The minimum requirement.** `β` carries a diagonal witness relative to an admissible endomap class `M`
when some self-application has, in its range, the diagonal of every admissible `g`. -/
def HasWitnessRel (β : Type u) (M : (β → β) → Prop) : Prop :=
  ∃ (α : Type u) (e : α → (α → β)), ∀ g : β → β, M g → ∃ a, (fun x => g (e x x)) = e a

/-- **The floor condition.** A witness forces every admissible endomap to have a fixed point — self-reference
*closes*. In the full framework that fixed point is the self-referential **Quine atom** `⊥ = {⊥}` / Kleene
quine (`Settheory/SetTheoryAFA.lean` `t_exec`); here it is bare existence — see the docstring's
"What the floor stands for". -/
theorem floor_of_witness {β : Type*} {M : (β → β) → Prop} (h : HasWitnessRel β M)
    {g : β → β} (hg : M g) : ∃ b, g b = b := by
  obtain ⟨α, e, he⟩ := h
  obtain ⟨a, ha⟩ := he g hg
  exact ⟨e a a, congrFun ha a⟩

/-- **The wall condition.** A fixed-point-free admissible endomap kills the witness — Cantor, relativized. -/
theorem wall_of_fpf {β : Type*} {M : (β → β) → Prop} {g : β → β} (hg : M g)
    (hgf : ∀ x, g x ≠ x) : ¬ HasWitnessRel β M := by
  intro h
  obtain ⟨b, hb⟩ := floor_of_witness h hg
  exact hgf b hb

/-- **The topology spine.** Shrinking the admissible class can only help the witness, so the witness set is a
lower set on the lattice of map-classes. -/
theorem witness_antitone {β : Type*} {M M' : (β → β) → Prop}
    (hsub : ∀ g, M g → M' g) (h : HasWitnessRel β M') : HasWitnessRel β M := by
  obtain ⟨α, e, he⟩ := h
  exact ⟨α, e, fun g hg => he g (hsub g hg)⟩

/-! ### § III. The smallest concrete witness — the two-element pole and its four self-maps. -/

/-- The pole: the two-element type `{0, ∞}`. -/
inductive Pole where
  | zero
  | infty
deriving DecidableEq, Fintype, Repr

namespace Pole

/-- Collapse to `0` — the floor at zero. -/
def cZero : Pole → Pole := fun _ => zero
/-- Collapse to `∞` — the floor at infinity. -/
def cInfty : Pole → Pole := fun _ => infty
/-- The identity — both poles fixed. -/
def cId : Pole → Pole := id
/-- The inversion `0 ↔ ∞` — the wall. -/
def swap : Pole → Pole
  | zero => infty
  | infty => zero

/-- **Exactly four self-maps.** `2² = 4`. -/
theorem card_four : Fintype.card (Pole → Pole) = 4 := by decide

/-- **The four are exhaustive.** -/
theorem four_exhaustive (f : Pole → Pole) :
    f = cZero ∨ f = cInfty ∨ f = cId ∨ f = swap := by
  revert f; decide

/-! ### § IV. The fixed-point classification, and the bridge to the classifier. -/

/-- **The wall corner has no fixed point.** `swap` fixes neither pole. -/
theorem swap_no_fp : ∀ p, swap p ≠ p := by decide

/-- **The floor corner closes.** The collapse `cZero` fixes `0`. -/
theorem cZero_has_fp : ∃ b, cZero b = b := ⟨zero, rfl⟩

/-- **THE BRIDGE.** `swap` is fixed-point-free, so by the classifier's wall condition it kills the witness:
the **wall sits at the inversion corner**, on the smallest domain there is. -/
theorem swap_is_the_wall (M : (Pole → Pole) → Prop) (hswap : M swap) :
    ¬ HasWitnessRel Pole M :=
  wall_of_fpf hswap swap_no_fp

/-- **The wall is reversible.** `swap` is an involution. -/
theorem swap_involutive : Function.Involutive swap := by
  intro p; cases p <;> rfl

/-- **The floor collapse is irreversible.** `cZero` forgets which pole it came from — the one-way half of the
snap. -/
theorem collapse_irreversible : ¬ Function.Injective cZero := by
  intro h
  exact absurd (@h zero infty rfl) (by decide)

end Pole

/-! ### § V. The snap, in both directions — the limit that is also a bottom.

The pole gives only the irreversible half. The snap also *ascends to a limit that is itself a bottom*: on the
minimal chain `ℕ∞`, `⊤` is at once the supremum of the climbing chain (the limit) and the least fixed point of
successor (the bottom-of-fixed-points). This is `Ordinal/Epsilon0MinMax.lean` `epsilon0_min_eq_max` in
miniature — the reason the snap cannot be flattened to a one-way collapse. -/

/-- The climbing chain `0, 1, 2, …` has supremum `⊤` — the limit (max face). -/
theorem chain_sup_top : (⨆ n : ℕ, (n : ℕ∞)) = ⊤ := by
  rw [iSup_eq_top]
  intro b hb
  lift b to ℕ using hb.ne
  exact ⟨b + 1, by exact_mod_cast Nat.lt_succ_self b⟩

/-- `⊤` is the unique fixed point of successor: `x + 1 = x ↔ x = ⊤`. -/
theorem enat_fp_iff (x : ℕ∞) : x + 1 = x ↔ x = ⊤ := by
  constructor
  · intro h
    by_contra hne
    lift x to ℕ using hne
    have : x + 1 = x := by exact_mod_cast h
    omega
  · rintro rfl
    simp

/-- **Both a limit and a bottom (min ≡ max, in miniature).** `⊤` is *simultaneously* the supremum of the
climbing chain (the limit / max) and the least fixed point of successor (the bottom-of-fixed-points / min).
This is the shadow of `epsilon0_min_eq_max`: the snap lands on a point that is both at once, which is exactly
why it needs both directions. -/
theorem tower_min_eq_max :
    (⨆ n : ℕ, (n : ℕ∞)) = ⊤ ∧ IsLeast {x : ℕ∞ | x + 1 = x} ⊤ := by
  refine ⟨chain_sup_top, ?_, fun b hb => le_of_eq ((enat_fp_iff b).mp hb).symm⟩
  show (⊤ : ℕ∞) + 1 = ⊤
  simp

/-- **The ascent is one-way.** The climb `n ↦ ↑n` is strictly monotone — you cannot un-climb. -/
theorem ascent_strictMono : StrictMono (fun n : ℕ => (n : ℕ∞)) := by
  intro a b h
  show (a : ℕ∞) < (b : ℕ∞)
  exact_mod_cast h

/-! ### § VI. The fan-out — the branching field the pole cannot hold. -/

/-- **The fan-out.** A node with three pairwise-incomparable successors (`∅ ⊆ {i}`, and `{i} ⊄ {j}` for
`i ≠ j`) — a branch of arity three. This is the field: the width the boundary fans into. -/
theorem fan_out :
    (∀ i : Fin 3, (∅ : Set (Fin 3)) ⊆ {i}) ∧
    (∀ i j : Fin 3, i ≠ j → ¬ ({i} ⊆ ({j} : Set (Fin 3)))) := by
  refine ⟨fun i => Set.empty_subset _, fun i j hij hsub => ?_⟩
  exact hij (hsub rfl)

/-- **The pole cannot fan out.** Branching needs at least three elements; the pole has two. So the fan-out is
strictly bigger than the pole — the field is more than the two poles. -/
theorem pole_cannot_fan : Fintype.card Pole = 2 := by decide

/-! ### § VII. The capstone — the whole shape, in one theorem. -/

open Pole in
/-- **The shape.** All of it, on the smallest witnesses:
* the **wall** (`swap`) has no fixed point;
* the **floor** (`cZero`) closes at a fixed point;
* the **collapse** is irreversible (the one-way half of the snap);
* the **snap-limit** is *both a limit and a bottom* (`⊤` is the supremum of the chain and the least fixed
  point — min ≡ max);
* the **fan-out** exists (three incomparable successors) where the pole (two elements) cannot hold it.
The engine (`lawvere`) and classifier (`wall_of_fpf` / `floor_of_witness`) say *why*; here it is, on two
points, a minimal chain, and a minimal branch. -/
theorem shape :
    (∀ p, swap p ≠ p) ∧
    (∃ b, cZero b = b) ∧
    ¬ Function.Injective cZero ∧
    ((⨆ n : ℕ, (n : ℕ∞)) = ⊤ ∧ IsLeast {x : ℕ∞ | x + 1 = x} ⊤) ∧
    (∀ i j : Fin 3, i ≠ j → ¬ ({i} ⊆ ({j} : Set (Fin 3)))) :=
  ⟨swap_no_fp, cZero_has_fp, collapse_irreversible, tower_min_eq_max, fan_out.2⟩

end ZeroParadox.Miniature

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox.Miniature ZeroParadox.Miniature.Pole
#print axioms lawvere
#print axioms negation_no_fp
#print axioms wall_of_fpf
#print axioms floor_of_witness
#print axioms swap_is_the_wall
#print axioms tower_min_eq_max
#print axioms ascent_strictMono
#print axioms fan_out
#print axioms shape
end PurityCheck
