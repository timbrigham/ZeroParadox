import ZeroParadox.Settheory.Wall_OneRoot
import ZeroParadox.Multihomed.Boundary
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The host verdict — why "one root or two" is really THREE, and two of the three are the object

## Engineer's Take

TODO (Tim): <your take, in your own voice.>

---

## Formal Overview (AI-assisted)

`Settheory/Wall.lean` poses an open question — the **one-root-or-two** question (`Wall.lean:80-83`):
the negation engine (`negation_no_fixedpoint` → `lawvere_fixedpoint`) unifies the *diagonal family*
(Cantor / Russell / Turing) as a real theorem, while the well-founded family (`wf_no_selfloop`,
`no_quine_atom`) is proved by a **different mechanism** (accessibility), and whether it folds in too was
left open. `Wall_OneRoot.lean` argues **two roots** — honestly flagged there as a structural argument
from disjoint hypotheses, not a proved irreducibility.

This file records a **reading** that dissolves the tension without touching either result. The engine
already forks into two regimes (`Wall.lean:123-124`): **μ** — the map is fixed-point-free, so no object
forms (the wall); and **ν** — a fixed point exists (the self-referential object: Quine atom, Y
combinator). Counting the ν object as its own face gives **three**, and then the "second root" turns out
not to be a root of self-reference at all: **every** theorem assigned to it is `wf_no_selfloop`
instantiated at some host relation, deciding whether that host may carry ν.

- **μ — the wall.** No fixed point ever forms. `cantor_via_engine`, `russell_via_engine`,
  `no_self_decider` (engine-driven, axiom-free).
- **ν-hosted — the object lives.** The host carries the self-loop, so the host is **not** well-founded:
  `floor_not_wellFounded` (`Multihomed/Boundary.lean`), from ⊥'s `fixed_bot`.
- **ν-refused — the object is forbidden.** The host **is** well-founded, so no self-loop:
  `no_quine_atom` (`= wf_no_selfloop ZFSet.mem_wf x`).

**The load-bearing observation, and it is the whole content of this file:** the two ν faces are the
*same theorem* read in its two directions, at two different host relations. So well-foundedness is not a
third root — it is the **axis on which a host renders its verdict on ν**. What this file adds is
presentational: it names the hinge, exhibits both instantiations against it, and fences the result.

**What is NOT claimed (read this before citing anything here).**
1. **The narrow one-root question is still answered NO.** `wf_no_selfloop` is proved by accessibility,
   *not* by the negation engine, and nothing here derives it from the engine. Two *mechanisms* remain.
   The claim is only that one of the two was never a root of the self-reference phenomenon — it is a
   host-verdict applied to the engine's ν output. `selfloop_permitted` and `engine_is_wf_free`
   (`Wall_OneRoot.lean`) stand unmodified.
2. **The three faces are not one object.** `trinary_faces` below is a **CONJUNCTION**, never an
   identity. Its three components live at three different carriers (`A → (A → Prop)`, `L`, `ZFSet`) and
   `x = y` across them is not a well-formed proposition. "Both hold" is not "these are the same fact."
3. **No traversal, no dynamics.** Nothing here says the object *moves*, or that ν-hosted implies a first
   step is taken. That remains the framework's commitment (`l_inf`'s docstring is the honest statement
   of where the argument stops).
4. The shadow/literal distinction (`Wall.lean:17-21`) is **preserved**, not crossed: `floorRel` (the
   `selfApp` graph) and `ZFSet` membership are different relations. The hinge reaches both because it
   quantifies over *any* relation — it does not identify them.

## Structure

- § I    The hinge — well-foundedness and a self-loop are mutually exclusive (the axis)
- § II   The two ν faces, each an instantiation of the hinge
- § III  The verdict is not the engine's (the engine is blind to it)
- § IV   The trinary, bundled — a conjunction, with the fence

Prior art: the hinge is Mathlib's `WellFounded.irrefl` (`wf_no_selfloop`'s own header says so); the
μ-family unification is Lawvere (1969) / Yanofsky (2003), cited in `Wall.lean`. Nothing here is offered
as new mathematics — the contribution is the **carving**, and every component is an existing theorem.
-/

namespace ZeroParadox

variable {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]

/-! ## § I. The hinge — the host-verdict axis

One theorem carries both ν faces. `wf_no_selfloop` says a well-founded relation admits no self-loop;
read as a mutual exclusion it says: **no host is both well-founded and a carrier of the self-loop.**
That exclusion is the axis the ν object is sorted on. -/

/-- **THE AXIS.** No host relation is both well-founded and a carrier of a self-loop at `x`.
    `wf_no_selfloop` stated as a mutual exclusion — the form in which it is visibly a *verdict on a
    host* rather than a fact about one object. -/
theorem host_verdict_axis {α : Type*} (r : α → α → Prop) (x : α) :
    ¬ (WellFounded r ∧ r x x) := fun ⟨hwf, hloop⟩ => wf_no_selfloop hwf x hloop

/-- **ν-hosted, in hypothesis form.** IF the host carries the ν object — the self-loop — THEN the host
    is not well-founded. The hosting of ν is an explicit **hypothesis**, not bundled into a class, so
    the assumption is visible on the face of the statement (per the commitments-in-hypotheses rule). -/
theorem nu_hosted_forces_non_wf {α : Type*} (r : α → α → Prop) (x : α)
    (hnu : r x x) :          -- COMMITMENT: this host carries the self-referential object
    ¬ WellFounded r := fun hwf => host_verdict_axis r x ⟨hwf, hnu⟩

/-- **ν-refused, in hypothesis form.** IF the host is well-founded THEN it refuses ν at every point.
    The same hinge, the other direction. -/
theorem wf_host_refuses_nu {α : Type*} (r : α → α → Prop)
    (hwf : WellFounded r) :  -- COMMITMENT: this host is well-founded
    ∀ x, ¬ r x x := fun x hloop => host_verdict_axis r x ⟨hwf, hloop⟩

/-! ## § II. The two ν faces are the SAME hinge at two hosts

Neither theorem below is new — both already exist. They are restated here *against the hinge* so the
carving is checkable: the only difference between the framework's floor and a well-founded set theory is
**which side of § I's exclusion the host sits on.** -/

/-- **ν-hosted (the framework's floor).** `floorRel` carries ⊥'s self-loop (`fixed_bot`), so it is not
    well-founded. `Statement:` this is `floor_not_wellFounded`, re-derived through the hinge to exhibit
    it as the ν-hosted instantiation. -/
theorem nu_hosted_face : ¬ WellFounded (floorRel (L := L)) :=
  nu_hosted_forces_non_wf floorRel ZPSemilattice.bot AbstractSelfApp.fixed_bot

/-- **ν-refused (set theory under Foundation).** `ZFSet` membership is well-founded, so no set is
    self-membered. `Statement:` this is `no_quine_atom`, re-derived through the hinge to exhibit it as
    the ν-refused instantiation of the *same* theorem as `nu_hosted_face`. -/
theorem nu_refused_face (x : ZFSet) : x ∉ x :=
  wf_host_refuses_nu (· ∈ ·) ZFSet.mem_wf x

/-! ## § III. The verdict is not the engine's

Why the verdict is a *separate* mechanism, and why that does not make it a second root: the engine never
mentions well-foundedness, and by itself does not forbid a self-loop. So the engine delivers ν and is
**blind to its fate**; the host decides. (Both facts are `Wall_OneRoot.lean`'s, restated here as the
reason the carving is three-way rather than two-way.) -/

/-- **The engine is blind to the verdict.** Lawvere's conclusion holds with no well-foundedness
    hypothesis anywhere, while a self-loop is *permitted* absent well-foundedness. So the engine cannot
    supply the verdict, and the verdict cannot be read off the engine — they are about different things,
    which is precisely why the well-founded face is not a competing root. -/
theorem engine_blind_to_verdict {A B : Type*} (e : A → (A → B)) (he : Function.Surjective e)
    (f : B → B) :
    (∃ b, f b = b) ∧ (∃ (A' : Type) (r : A' → A' → Prop) (x : A'), r x x) :=
  ⟨lawvere_fixedpoint e he f, selfloop_permitted⟩

/-! ## § IV. The trinary, bundled

**FENCE — this is a CONJUNCTION, not an identity.** Three faces hold simultaneously, at three different
carriers. No equation between them is asserted, and none is well-formed. -/

/-- **THE TRINARY.** All three faces of the one engine's output, simultaneously:
    (1) **μ** — no object forms (Cantor, the diagonal at a fixed-point-free map);
    (2) **ν-hosted** — the object lives, and its host is not well-founded;
    (3) **ν-refused** — a well-founded host forbids the object.

    `Statement:` a conjunction of three independently-proved facts at three carriers.
    `Reading:` faces (2) and (3) are the *same* self-referential object seen hosted and seen refused,
    sorted by § I's axis; only (1) is the case where no object forms at all. That reading is the
    framework's carving of the one-root-or-two question — it is NOT asserted by this conjunction. -/
theorem trinary_faces {A : Type*} (g : A → (A → Prop)) :
    (¬ Function.Surjective g)
      ∧ (¬ WellFounded (floorRel (L := L)))
      ∧ (∀ x : ZFSet, x ∉ x) :=
  ⟨cantor_via_engine g, nu_hosted_face, nu_refused_face⟩

end ZeroParadox

/-! ## Axiom Purity Check -/

/-! Measured 2026-07-29, `lake build` clean, 3853 jobs, sorry-free:
    `host_verdict_axis`, `nu_hosted_forces_non_wf`, `wf_host_refuses_nu`, `nu_hosted_face`,
    `engine_blind_to_verdict` — **axiom-free**. `nu_refused_face` and `trinary_faces` —
    `[propext, Quot.sound]`, inherited from Mathlib's `ZFSet` / `ZFSet.mem_wf`; **choice-free**.
    So the axis and both ν faces are established without `Classical.choice`. -/

section PurityCheck
open ZeroParadox

#print axioms host_verdict_axis
#print axioms nu_hosted_forces_non_wf
#print axioms wf_host_refuses_nu
#print axioms nu_hosted_face
#print axioms nu_refused_face
#print axioms engine_blind_to_verdict
#print axioms trinary_faces

end PurityCheck
