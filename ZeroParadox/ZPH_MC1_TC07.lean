-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPP_Goodstein
import ZeroParadox.ZPP_KirbyParis
import ZeroParadox.ZPP_Kruskal
import Mathlib.SetTheory.Ordinal.Basic

set_option maxHeartbeats 400000

/-!
# TC07 — Is the proof-theory bottom canonical across the depth campaign?

**Node under test:** #1, the proof-theory floor. Three independence/termination results in the campaign
each "descend": Goodstein (`ZPP_Goodstein.goodstein_terminates`), Kirby–Paris (`ZPP_KirbyParis`), and
Kruskal (`ZPP_Kruskal`). The campaign claim (TH7) is that all three "descend to the SAME ordinal floor
`0`."

**Pre-registered GO:** each terminates at / shares the floor `0`.
**Pre-registered NO-GO:** the three have *distinct* floors (or no common floor object).

## What the race actually finds (mixed verdict)

This is NOT a uniform GO. Racing both halves at the level of the *theorem statements* (not the
docstrings) yields:

* **GO for Goodstein and Kirby–Paris.** Both are genuine well-founded *descents* whose measure lives
  in `Ordinal` and bottoms at the *literally same* element `⊥ = 0 : Ordinal`:
  - Goodstein's terminal value is `gseq n k = 0 : ℕ`, whose ordinal measure `heval b 0 = 0 = ⊥`.
  - Kirby–Paris's minimal hydra is the leaf `node []`, with `Hydra.val (node []) = 0 = ⊥`, and every
    hydra value satisfies `⊥ ≤ Hydra.val h` (`bot_le`). So the descent bottoms at `⊥`.
  These two share one floor object, witnessed by `gk_share_floor`.

* **NO-GO for Kruskal.** Kruskal's theorem is *not* a descent to a floor — it is a well-quasi-order
  statement (`Set.PartiallyWellOrderedOn (TreeEmbeds r)`), a property of an order, not a terminating
  sequence with a least value. A WQO need carry no bottom element at all. So Kruskal does not "descend
  to floor `0`"; it does not descend to a floor in the first place. The honest witness `kruskal_is_wqo_not_descent`
  records that the Kruskal result inhabits the WQO predicate, a different shape from a well-founded
  descent measure.

So the canonical-floor claim holds for the two genuine *descents* (Goodstein, KP) and the
pre-registered NO-GO half fires for Kruskal: it is a different kind of theorem with no floor object.
The honest verdict is **SPLIT**: GO on the descent pair, NO-GO on the WQO member.

What is interpretation (not Lean): that `⊥ : Ordinal` is "the same diagonal fixed point" as the other
bottom-diagram nodes. Lean here proves only the intra-proof-theory identity of the Goodstein and KP
floors as the single element `⊥ : Ordinal`, and that Kruskal's conclusion is a WQO predicate, not a
descent.

## Formal Overview

`heval_floor_eq_bot` : the Goodstein ordinal measure at its ℕ-floor `0` is `⊥ : Ordinal`.
`kp_leaf_val_eq_bot` : the Kirby–Paris minimal hydra `node []` has valuation `⊥ : Ordinal`.
`kp_val_bot_le` : every hydra valuation is `≥ ⊥` (the descent cannot go below `⊥`).
`gk_share_floor` : Goodstein's and KP's ordinal floors are the *same* element `⊥ : Ordinal`, and
  Goodstein's ℕ-floor `0` casts to it. (The GO half.)
`kruskal_is_wqo_not_descent` : Kruskal's theorem inhabits the WQO predicate `PartiallyWellOrderedOn`
  for any WQO label alphabet — a property of an order, not a descent to a floor. (The NO-GO witness.)

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.MC1.TC07

open Ordinal

/-! ### Goodstein floor -/

/-- The Goodstein ordinal measure evaluated at its natural-number floor `0` is `⊥ : Ordinal`.
    Goodstein terminates at `gseq n k = 0`; this records that the descent measure bottoms at `⊥`. -/
theorem heval_floor_eq_bot (b : ℕ) :
    ZeroParadox.Goodstein.heval b 0 = (⊥ : Ordinal) := by
  rw [ZeroParadox.Goodstein.heval_zero, Ordinal.bot_eq_zero]

/-- Re-export: the Goodstein sequence reaches the ℕ floor `0`. -/
theorem goodstein_reaches_floor (n : ℕ) : ∃ k, ZeroParadox.Goodstein.gseq n k = 0 :=
  ZeroParadox.Goodstein.goodstein_terminates n

/-! ### Kirby–Paris floor -/

/-- The Kirby–Paris minimal hydra is the leaf `node []`; its ordinal valuation is `⊥ : Ordinal`. -/
theorem kp_leaf_val_eq_bot : (ZeroParadox.KirbyParis.Hydra.node []).val = (⊥ : Ordinal) := by
  rw [ZeroParadox.KirbyParis.val_node, ZeroParadox.KirbyParis.S_nil, Ordinal.bot_eq_zero]

/-- Every hydra valuation is `≥ ⊥` — the Kirby–Paris descent cannot go below the floor `⊥`. -/
theorem kp_val_bot_le (h : ZeroParadox.KirbyParis.Hydra) : (⊥ : Ordinal) ≤ h.val :=
  bot_le

/-! ### The GO half: Goodstein and Kirby–Paris share one ordinal floor -/

/-- **GO (descent pair).** Goodstein's and Kirby–Paris's descents bottom at the *same* ordinal
    element `⊥ : Ordinal`. The conjunction below is the load-bearing identity:
    * Goodstein's measure at its ℕ-floor `0` is `⊥`;
    * Kirby–Paris's minimal hydra has valuation `⊥`;
    * Goodstein's ℕ-floor `0` casts to that same ordinal `⊥`;
    * both measures land in the one ordered type `Ordinal`, whose `⊥` is unique.
    So the two genuine well-founded descents of the depth campaign share a single floor object. -/
theorem gk_share_floor :
    ZeroParadox.Goodstein.heval 2 0 = (⊥ : Ordinal) ∧
    (ZeroParadox.KirbyParis.Hydra.node []).val = (⊥ : Ordinal) ∧
    ((0 : ℕ) : Ordinal) = (⊥ : Ordinal) ∧
    ZeroParadox.Goodstein.heval 2 0 = (ZeroParadox.KirbyParis.Hydra.node []).val := by
  refine ⟨heval_floor_eq_bot 2, kp_leaf_val_eq_bot, ?_, ?_⟩
  · rw [Nat.cast_zero, Ordinal.bot_eq_zero]
  · rw [heval_floor_eq_bot 2, kp_leaf_val_eq_bot]

/-! ### The NO-GO half: Kruskal is a WQO, not a descent -/

/-- **NO-GO (Kruskal).** Kruskal's theorem is not a descent to a floor: it inhabits the well-quasi-order
    predicate `Set.PartiallyWellOrderedOn (TreeEmbeds r)` on the rose trees, whenever the label alphabet
    is itself a WQO. A WQO is a *property of an order*, not a terminating sequence with a least value —
    it need carry no bottom element. So Kruskal does not "descend to the floor `0`"; the canonical-floor
    claim of the depth campaign genuinely splits here. The statement *is* the Kruskal WQO conclusion,
    re-exported with its true shape (a `PartiallyWellOrderedOn`, not an `Ordinal`-valued descent). -/
theorem kruskal_is_wqo_not_descent
    {α : Type*} (r : α → α → Prop) [IsPreorder α r]
    (hr : (Set.univ : Set α).PartiallyWellOrderedOn r) :
    (Set.univ : Set (ZeroParadox.Kruskal.RoseTree α)).PartiallyWellOrderedOn
      (ZeroParadox.Kruskal.TreeEmbeds r) :=
  ZeroParadox.Kruskal.partiallyWellOrderedOn_treeEmbeds r hr

end ZeroParadox.MC1.TC07

section PurityCheck
open ZeroParadox.MC1.TC07
#print axioms heval_floor_eq_bot
#print axioms goodstein_reaches_floor
#print axioms kp_leaf_val_eq_bot
#print axioms kp_val_bot_le
#print axioms gk_share_floor
#print axioms kruskal_is_wqo_not_descent
end PurityCheck
