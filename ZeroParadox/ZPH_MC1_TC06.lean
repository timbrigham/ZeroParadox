-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.QPF.Univariate.Basic
import ZeroParadox.ZPP_Coalgebra

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC06 — the ZP-P W/M coalgebra fork places on the μ/ν root

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file is one go/no-go cycle of the bottom-diagram tree campaign
(`thread_obstruction_table_2026-06-29.md`). The node under test is the **ZP-P coalgebra fork**
(`ZPP_Coalgebra.lean`): the W-type `QPF.Fix F` and the M-type `QPF.Cofix F`. The pre-registered
**CLAIM** is that this fork *places consistently on the μ/ν root* — the W-type sits on the
**μ-side** (the least-fixed-point / inductive / well-founded carrier, with a recursor *out of* it)
and the M-type on the **ν-side** (the greatest-fixed-point / coinductive / non-well-founded carrier,
with a corecursor *into* it).

**Scope of what is proved here — the existence + commutation halves only, NOT initiality/finality.**
A full initial-algebra (resp. final-coalgebra) universal property requires *both* (a) existence of a
mediating map satisfying its commuting square *and* (b) uniqueness of that map. This file proves only
half (a) for each side: the recursor/corecursor exists and commutes. It does **not** discharge the
uniqueness halves (Mathlib supplies them via `Fix.rec_unique` and `Cofix.bisim`; they are
deliberately *not* invoked here). So the theorem names below say `rec_commutes` / `corec_commutes`,
not `initial_algebra` / `final_coalgebra`: an object can carry a commuting recursor without being
initial. The load-bearing, witnessed content is the *direction* the two mediators run.

**Why this is not a pure restatement of `ZPP_Coalgebra`.** That file proves, for the leaf-free
functor `idPF`, that `Fix idPF.Obj` is *empty* and `Cofix idPF.Obj` is *inhabited*. Empty/inhabited
is a cardinality fact about one functor; it does not, by itself, exhibit the *recursor/corecursor
directions*. The two commuting squares witnessed here hold for an *arbitrary* QPF `F`:

- **μ-side (W-type carries a commuting recursor).** `Fix.mk : F (Fix F) → Fix F` is an F-algebra
  whose structure map is invertible (`fix_isFixedPoint`: `Fix.mk ∘ Fix.dest = id` and vice versa —
  `Fix F` is a genuine fixed point), and `Fix.rec` provides, for *any* F-algebra `g : F α → α`, a
  mediating map *out of* `Fix F` that commutes with the algebra structure (`fix_rec_commutes`,
  `= Fix.rec_eq`). The mediating map runs `Fix F → α`: the direction characteristic of the least
  fixed point / μ side. (Existence + commutation; uniqueness — the other half of *initiality* — is
  not proved here.)

- **ν-side (M-type carries a commuting corecursor).** `Cofix.dest : Cofix F → F (Cofix F)` is an
  F-coalgebra, and `Cofix.corec` provides, for *any* F-coalgebra `g : α → F α`, a mediating map
  *into* `Cofix F` that commutes with the coalgebra structure (`cofix_corec_commutes`,
  `= Cofix.dest_corec`). The mediating map runs `α → Cofix F`: the *opposite* direction,
  characteristic of the greatest fixed point / ν side. (Again existence + commutation only; the
  *finality* uniqueness half is not proved here.)

The two commuting squares run in **opposite directions** (out of `Fix`, into `Cofix`) — that
opposition is the witnessed content of the μ/ν root cut.

`fork_places_on_root` bundles the two commuting squares as the single placement statement.
`coalgebra_fork_strict_on_idPF` then specializes back to the leaf-free `idPF` and bundles the
placement-direction facts *with* `ZPP_Coalgebra`'s strict empty/inhabited fork, so the GO verdict
records both that the carriers carry opposite-direction mediators *and* that on `idPF` the sides are
genuinely separated (μ empty, ν inhabited).

**Verdict: GO (directional placement), with a fenced caveat.** Both commuting squares hold for every
QPF `F`, in opposite directions; the pre-registered NO-GO (one carrier is a seam, or both mediators
run the same direction) does not occur — `Fix.rec` and `Cofix.corec` are not interchangeable. The GO
is on the *direction* of the mediators, which is what distinguishes μ from ν here. It is **not** a GO
on full initiality/finality, because the uniqueness halves are not discharged in this file.

**Honest scope / what is interpretation.** Lean proves the two *commuting squares* (`Fix.rec_eq`,
`Cofix.dest_corec`) and the fixed-point round-trips (`Fix.mk_dest`, `Fix.dest_mk`). It does **not**
prove the *uniqueness* halves, so it does not establish that `Fix F` is the *initial* F-algebra or
`Cofix F` the *final* F-coalgebra (Mathlib has `Fix.rec_unique` and `Cofix.bisim` for that; they are
not used here). The three universal-property-flavoured facts (`fix_isFixedPoint`, `fix_rec_commutes`,
`cofix_corec_commutes`) are *generic* QPF facts — true of every QPF, re-exported from Mathlib — not
ZP-specific content; the only ZP-specific non-trivial content is `ZPP_Coalgebra`'s strict
empty/inhabited fork on `idPF`, bundled in at the end. Naming this the "μ/ν root" of the framework's
bottom diagram, and identifying it with the diagonal fixed point of the other layers, is the
cross-instance modeling commitment (ZP-P hard fence), not a theorem.
-/

namespace ZeroParadox.ZPH_MC1_TC06

open QPF

variable {F : Type u → Type u} [QPF F]

/-! ### μ-side: the W-type `Fix F` carries a commuting recursor (mediator out of `Fix`). -/

/-- **`Fix F` is a genuine fixed point of `F`.** The algebra structure map `Fix.mk : F (Fix F) → Fix F`
    and the coalgebra structure map `Fix.dest : Fix F → F (Fix F)` are mutually inverse, so
    `F (Fix F) ≃ Fix F`. This is the carrier-level fixed-point fact. (Generic to every QPF.) -/
theorem fix_isFixedPoint :
    (∀ x : Fix F, Fix.mk (Fix.dest x) = x) ∧ (∀ y : F (Fix F), Fix.dest (Fix.mk y) = y) :=
  ⟨Fix.mk_dest, Fix.dest_mk⟩

/-- **μ-side recursor commuting square (existence, NOT initiality).** For *any* F-algebra
    `g : F α → α`, the recursor `Fix.rec g : Fix F → α` is a mediating map **out of** `Fix F` that
    commutes with the algebra structure: `Fix.rec g (Fix.mk x) = g (Fix.rec g <$> x)`. The mediating
    map runs `Fix F → α` — the direction characteristic of the μ side. This is the *existence +
    commutation* half only; the *uniqueness* half that would make `Fix F` the **initial** F-algebra
    (`Fix.rec_unique`) is deliberately not invoked here. (Generic to every QPF.) -/
theorem fix_rec_commutes {α : Type u} (g : F α → α) (x : F (Fix F)) :
    Fix.rec g (Fix.mk x) = g (Fix.rec g <$> x) :=
  Fix.rec_eq g x

/-! ### ν-side: the M-type `Cofix F` carries a commuting corecursor (mediator into `Cofix`). -/

/-- **ν-side corecursor commuting square (existence, NOT finality).** For *any* F-coalgebra
    `g : α → F α`, the corecursor `Cofix.corec g : α → Cofix F` is a mediating map **into** `Cofix F`
    that commutes with the coalgebra structure: `Cofix.dest (Cofix.corec g x) = Cofix.corec g <$> g x`.
    The mediating map runs `α → Cofix F` — the direction characteristic of the ν side, opposite to the
    μ side. This is the *existence + commutation* half only; the *uniqueness* half that would make
    `Cofix F` the **final** F-coalgebra (via `Cofix.bisim`) is deliberately not invoked here. (Generic
    to every QPF.) -/
theorem cofix_corec_commutes {α : Type u} (g : α → F α) (x : α) :
    Cofix.dest (Cofix.corec g x) = Cofix.corec g <$> g x :=
  Cofix.dest_corec g x

/-! ### The placement statement. -/

/-- **The fork places on the μ/ν root (by mediator direction).** For every QPF `F`: the W-type carries
    a commuting recursor whose mediating maps run *out of* `Fix F`, and the M-type carries a commuting
    corecursor whose mediating maps run *into* `Cofix F`. The two directions are opposite — that
    opposition is the witnessed content of the μ/ν root cut. The pre-registered NO-GO (same direction,
    or a seam) does not occur: `Fix.rec` and `Cofix.corec` are genuinely opposite-direction mediators.
    (Existence + commutation only; this does not assert initiality/finality — see file docstring.) -/
theorem fork_places_on_root :
    (∀ {α : Type u} (g : F α → α) (x : F (Fix F)), Fix.rec g (Fix.mk x) = g (Fix.rec g <$> x)) ∧
    (∀ {α : Type u} (g : α → F α) (x : α),
        Cofix.dest (Cofix.corec g x) = Cofix.corec g <$> g x) :=
  ⟨fun g x => fix_rec_commutes g x, fun g x => cofix_corec_commutes g x⟩

/-- **GO, the strict instance.** Specialize the placement to the leaf-free functor `idPF` and bundle
    it with `ZPP_Coalgebra`'s strict empty/inhabited fork. The W-type sits on the μ-side (recursor
    out of `Fix`) *and* is empty; the M-type sits on the ν-side (corecursor into `Cofix`) *and* is
    inhabited. So on `idPF` the two sides of the root are both *directionally* distinct (opposite
    mediator directions) and *cardinally* separated (μ empty, ν inhabited). The two commuting-square
    conjuncts are generic QPF facts; the empty/inhabited conjuncts are the ZP-specific content. This
    bundles existence + commutation + the strict fork — it does not assert initiality/finality. -/
theorem coalgebra_fork_strict_on_idPF :
    -- μ-side: recursor commuting square (mediating map out of Fix), and Fix is empty
    (∀ {α : Type} (g : (ZeroParadox.ZPP.idPF.Obj) α → α) (x : (ZeroParadox.ZPP.idPF.Obj) (Fix (ZeroParadox.ZPP.idPF.Obj))),
        Fix.rec g (Fix.mk x) = g (Fix.rec g <$> x)) ∧
    IsEmpty (Fix (ZeroParadox.ZPP.idPF.Obj)) ∧
    -- ν-side: corecursor commuting square (mediating map into Cofix), and Cofix is inhabited
    (∀ {α : Type} (g : α → (ZeroParadox.ZPP.idPF.Obj) α) (x : α),
        Cofix.dest (Cofix.corec g x) = Cofix.corec g <$> g x) ∧
    Nonempty (Cofix (ZeroParadox.ZPP.idPF.Obj)) :=
  ⟨fun g x => fix_rec_commutes g x,
   ZeroParadox.ZPP.fix_isEmpty,
   fun g x => cofix_corec_commutes g x,
   ZeroParadox.ZPP.cofix_nonempty⟩

/-! ## PurityCheck -/

section PurityCheck
-- Measured footprint (lake build, 2026-06-29) — the split is the same μ/ν discriminator as
-- ZPP_Coalgebra, and it tracks the placement:
--   fix_isFixedPoint     (μ, round-trips)          : [propext, Quot.sound]                    CHOICE-FREE
--   fix_rec_commutes     (μ, recursor square)      : [propext, Quot.sound]                    CHOICE-FREE
--   cofix_corec_commutes (ν, corecursor square)    : [propext, Classical.choice, Quot.sound]  choice-carrying
--   fork_places_on_root  / coalgebra_fork_strict_on_idPF : inherit Classical.choice from the ν leg.
-- The μ side is choice-free; choice enters exactly on the ν (Cofix) side, via Mathlib's M-type
-- machinery (Cofix.dest_corec / cofix_nonempty) — a library artifact, not a necessity (for a
-- polynomial functor the final coalgebra is constructible choice-free; Veltri, FSCD 2021). So the
-- placement (μ choice-free / ν choice-carrying) is also visible in the axiom profile, not just the
-- mediator direction.
#print axioms fix_isFixedPoint
#print axioms fix_rec_commutes
#print axioms cofix_corec_commutes
#print axioms fork_places_on_root
#print axioms coalgebra_fork_strict_on_idPF
end PurityCheck

end ZeroParadox.ZPH_MC1_TC06
