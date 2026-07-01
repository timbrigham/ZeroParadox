import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Logic.Hydra
import ZeroParadox.Vendored.NaturalOps
import ZeroParadox.Vendored.NaturalOpsPow

set_option maxHeartbeats 800000

/-!
# Kirby–Paris hydra termination (the ε₀ gap) — proved

A hydra is a finite rooted tree; a Kirby–Paris cut removes a head (leaf) and, when the head's parent
is not the root, replicates the parent's remaining subtree finitely many times under the grandparent.
The battle always terminates. The classical proof assigns each hydra an ordinal (a leaf ↦ 0, a node ↦
the natural (Hessenberg) sum of `ω^(child ordinal)` — these land below ε₀, though we do not formalize
that bound) and shows every cut strictly decreases it; termination then follows from well-foundedness of
the ordinals. Mathlib has the abstract `CutExpand` well-foundedness (`Logic.Hydra`) but TODOs the
Kirby–Paris version.

This file proves it. The order-independent valuation needs the natural sum `♯`; that API was removed
from Mathlib (it lived in Combinatorial Game Theory, moved to an external repo), so it is recovered here
from a vendored Mathlib-v4.28 snapshot (`Vendored.NaturalOps`) plus the ω-power closure
`nadd_lt_omega0_opow` (`Vendored.NaturalOpsPow`, the CNF characterization that the snapshot left as a
TODO). See `.claude-local/notes/kirby_paris_nadd_absent_2026-06-29.md`.

What is proved:
* `Step` — the Kirby–Paris cut relation (a superset of the genuine battle moves; its well-foundedness
  implies KP termination a fortiori).
* `Step.val_lt` — every cut strictly decreases the natural-sum ordinal valuation.
* `kp_terminates : WellFounded (fun a b => Step b a)` — no infinite sequence of cuts. Unconditional.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.KirbyParis

open Ordinal NaturalOps

/-- A hydra: a finite rooted tree, given by its list of child hydras (a leaf is `node []`). -/
inductive Hydra where
  | node : List Hydra → Hydra

/-- Ordinal valuation `node cs ↦ ♯_c ω^(val c)` — the natural (Hessenberg) sum of `ω^(child)` over the
    child list. Natural sum is commutative and strictly monotone in each summand, so this is the genuine
    order-independent hydra ordinal (it lies below ε₀; that bound is not used here — only well-foundedness
    of `<` on the ordinals is). -/
noncomputable def Hydra.val : Hydra → Ordinal.{0}
  | .node cs => (cs.attach.map (fun c => omega0 ^ Hydra.val c.val)).foldr (· ♯ ·) 0
  decreasing_by
    simp_wf
    have := List.sizeOf_lt_of_mem c.property
    omega

/-- The valuation as a plain fold over the child list (no `attach`), for reasoning. -/
noncomputable def S (l : List Hydra) : Ordinal.{0} :=
  (l.map (fun c => omega0 ^ Hydra.val c)).foldr (· ♯ ·) 0

theorem val_node (cs : List Hydra) : (Hydra.node cs).val = S cs := by
  rw [Hydra.val, S, List.attach_map_val (l := cs) (f := fun c => omega0 ^ Hydra.val c)]

@[simp] theorem S_nil : S [] = 0 := rfl
@[simp] theorem S_cons (x : Hydra) (l : List Hydra) :
    S (x :: l) = omega0 ^ x.val ♯ S l := rfl

theorem S_append (l₁ l₂ : List Hydra) : S (l₁ ++ l₂) = S l₁ ♯ S l₂ := by
  induction l₁ with
  | nil => simp [Ordinal.zero_nadd]
  | cons a t ih => rw [List.cons_append, S_cons, S_cons, ih, Ordinal.nadd_assoc]

/-- The Kirby–Paris cut relation. `Step h h'` means `h'` is reachable from `h` by one cut.

  * `removeLeaf`: cut a leaf child (no regrowth — the head's parent is the root).
  * `grow`: grandparent replication — a grandchild-leaf's parent `node (preD ++ node [] :: postD)` is
    replaced by `n + 1` copies of `node (preD ++ postD)`.
  * `deeper`: the action happens inside one child.

  This relation contains every genuine Kirby–Paris cut, so its well-foundedness implies the battle
  terminates a fortiori. -/
inductive Step : Hydra → Hydra → Prop
  | removeLeaf (pre post : List Hydra) :
      Step (.node (pre ++ .node [] :: post)) (.node (pre ++ post))
  | grow (pre preD postD post : List Hydra) (n : ℕ) :
      Step (.node (pre ++ .node (preD ++ .node [] :: postD) :: post))
           (.node (pre ++ List.replicate (n + 1) (.node (preD ++ postD)) ++ post))
  | deeper (pre : List Hydra) (c c' : Hydra) (post : List Hydra) :
      Step c c' → Step (.node (pre ++ c :: post)) (.node (pre ++ c' :: post))

/-- **Every Kirby–Paris cut strictly decreases the valuation.** The grow case uses natural-sum
    monotonicity together with `ω`-power closure (`nadd_lt_omega0_opow`): replicating a child of value
    `β` finitely often produces a natural sum of `ω^β` terms, which stays below `ω^(β+1) = ω^(val of the
    parent)`. -/
theorem Step.val_lt : ∀ {h h' : Hydra}, Step h h' → h'.val < h.val := by
  intro h h' hstep
  induction hstep with
  | removeLeaf pre post =>
    have hh : (Hydra.node (pre ++ Hydra.node [] :: post)).val
        = S pre ♯ (1 ♯ S post) := by
      rw [val_node, S_append, S_cons]; congr 2; rw [val_node]; simp
    have hh' : (Hydra.node (pre ++ post)).val = S pre ♯ S post := by rw [val_node, S_append]
    rw [hh, hh']
    refine Ordinal.nadd_lt_nadd_left ?_ _
    calc S post = (0 : Ordinal) ♯ S post := (Ordinal.zero_nadd _).symm
      _ < 1 ♯ S post := Ordinal.nadd_lt_nadd_right (by norm_num) _
  | grow pre preD postD post n =>
    -- the parent's value is `β + 1` where `β = (node (preD ++ postD)).val`
    set β := (Hydra.node (preD ++ postD)).val with hβ
    have h0 : omega0 ^ (Hydra.node []).val = 1 := by rw [val_node]; simp
    have hparent : (Hydra.node (preD ++ Hydra.node [] :: postD)).val = β + 1 := by
      rw [val_node, S_append, S_cons, h0, Ordinal.nadd_comm 1 (S postD), ← Ordinal.nadd_assoc,
        ← S_append, hβ, val_node, Ordinal.nadd_one, ← Order.succ_eq_add_one]
    -- the replicated block's value stays below the parent's `ω`-power `ω^(β+1)`
    have hrep : S (List.replicate (n + 1) (Hydra.node (preD ++ postD))) < omega0 ^ (β + 1) := by
      induction n with
      | zero =>
        rw [zero_add, List.replicate_one, S_cons, ← hβ, S_nil, Ordinal.nadd_zero]
        exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 (Order.lt_succ β)
      | succ k ih =>
        rw [List.replicate_succ, S_cons, ← hβ]
        exact NaturalOpsPow.nadd_lt_omega0_opow
          ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 (Order.lt_succ β)) ih
    have hh : (Hydra.node (pre ++ Hydra.node (preD ++ Hydra.node [] :: postD) :: post)).val
        = S pre ♯ (omega0 ^ (β + 1) ♯ S post) := by
      rw [val_node, S_append, S_cons, hparent]
    have hh' : (Hydra.node (pre ++ List.replicate (n + 1) (Hydra.node (preD ++ postD)) ++ post)).val
        = S pre ♯ (S (List.replicate (n + 1) (Hydra.node (preD ++ postD))) ♯ S post) := by
      rw [val_node, List.append_assoc, S_append, S_append]
    rw [hh, hh']
    exact Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right hrep _) _
  | deeper pre c c' post _ ih =>
    have hh : (Hydra.node (pre ++ c :: post)).val = S pre ♯ (omega0 ^ c.val ♯ S post) := by
      rw [val_node, S_append, S_cons]
    have hh' : (Hydra.node (pre ++ c' :: post)).val = S pre ♯ (omega0 ^ c'.val ♯ S post) := by
      rw [val_node, S_append, S_cons]
    rw [hh, hh']
    refine Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right ?_ _) _
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 ih

/-- Termination of the hydra game: the cut relation is well-founded, so no infinite sequence of cuts
    exists. Unconditional — `Step.val_lt` discharges the strict decrease. -/
theorem kp_terminates : WellFounded (fun a b => Step b a) :=
  Subrelation.wf (fun {a b} (h : Step b a) => h.val_lt) (InvImage.wf Hydra.val Ordinal.lt_wf)

section PurityCheck
#print axioms Step.val_lt
#print axioms kp_terminates
end PurityCheck

end ZeroParadox.KirbyParis
