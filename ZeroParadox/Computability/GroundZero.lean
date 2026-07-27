import ZeroParadox.Computability.Occurrence
import ZeroParadox.Computability.NatListRegime

/-!
# Ground zero — the bottom as a behaviour, not a configuration

## Engineer's Take

This started as a thought in the shower. What if computability never actually reaches zero or
the bottom by definition, and what if it is asymptotic instead. My first guess was that this
would make epsilon-zero the smallest representation above zero. That is not where it landed,
and the reversal is the interesting part.

The bottom is not an unstarted state at all. It is already executing at ground zero by
definition. That corresponds with my view of how it would have to work.

I still honestly think the execution is forced here. I have been at a loss for how to represent
it, and this is the representation. My initial statement was that existence itself is a Turing
machine, and this is that statement with something underneath it.

---

## Formal Overview (AI-assisted)

This file connects two developments the project already had and had never wired together:
the operational model of § I-V of `Occurrence.lean` (`f : σ → Option σ`), and the coalgebra
for the functor `X ↦ 1 + X` in `NatListRegime.lean` (`natPF_NatListRegime`, `natInfinity`),
which is cited there to Jacobs & Rutten (EATCS Bulletin 62, 1997).

**What it establishes.** Reading a step function as a coalgebra, every configuration is a leaf
(halted) or a successor (stepping) — the head is `Bool`, so "exists but has not begun" is not
merely unproved, it is *not expressible* (§ I, axiom-free). And the behaviour that never reaches
a leaf is **unique**: it is `natInfinity` (§ II, `notEL_unique`). So the non-terminating bottom
is pinned by a purely negative description — by what it never does — with no element-hood in any
machine carrier assumed. A self-looping configuration unfolds to exactly that point (§ III).

**Why this shape matters.** The framework's other apophatic characterization with uniqueness is
set-theoretic (`quine_unique`). This is its computational counterpart, and unlike the ZP-K
identification it is a Lean `=` inside a single type, not a cross-type reading.

**Prior art — this is known, and the delta runs against us (recorded 2026-07-27).**
`notEL_unique` is **Escardó's `not-finite-is-∞'`** (TypeTopology, module
`TypeTopology.GenericConvergentSequence`), and his `CoNaturals.UniversalProperty` proves ℕ∞ is
the final coalgebra of `𝟙 + (−)` by the same bisimulation route. **His proof is `--safe
--without-K` from function extensionality alone**, where ours carries `Classical.choice` from
Mathlib's QPF quotient — so the standard version is not merely prior, it is purer, and that is
a live purity lead. The classical home is **Rutten, "Universal coalgebra: a theory of systems",
TCS 249 (2000)**: p. 16, *"∞ only takes a step to itself and hence never terminates"*; Ex.
10.2(4) p. 44 for `(ℕ̄, pred)` final; §12 pp. 51–52 running this exact bisimulation on this exact
carrier. Mathlib itself has no `Conat` and no such lemma, so the Lean formalization is a genuine
small addition — the mathematics is not.

**And the framework already had it, in another dress:** `Miniature.lean`'s
`enat_fp_iff : x + 1 = x ↔ x = ⊤` is this same fact in the `ℕ∞ = WithTop ℕ` presentation.

**What is NOT claimed.** That the framework's bottom *is* such a behaviour remains a modelling
commitment — the results here are conditional on non-termination, and say nothing about whether
the framework's bottom non-terminates. Nothing here makes the snap occur: occurrence is still
the halting problem (`occurs_iff_halts`, `occurrence_undecidable`). And the mathematics is not
new — the final coalgebra of `X ↦ 1 + X` being `ℕ ∪ {∞}` is standard (Jacobs, *Introduction to
Coalgebra*, Ex. 2.4.1 p. 66). **Note the scope of that citation:** Jacobs supports the *object*,
not the uniqueness *lemma*; for the lemma see Escardó and Rutten above. What is assembled here
is the bridge, not the coalgebra.

**Axiom footprint (measured, not quoted).** § I is axiom-free. § II and § III carry
`[propext, Classical.choice, Quot.sound]`, inherited from Mathlib's QPF machinery — so the
"already executing" half is free and the "is infinity" half is not.

## Structure

- § I   The head is `Bool` — there is no unstarted state (axiom-free)
- § II  The apophatic characterization, and its UNIQUENESS
- § III The bridge: a self-looping configuration unfolds to `natInfinity`
- § IV  NO-GO gauge: the forcing needs the binary split (a three-valued counter-model)
-/

namespace ZeroParadox

open QPF

variable {σ : Type} (f : σ → Option σ)

/-! ## § I. The head is `Bool` — already executing, by definition -/

/-- The step function read as a coalgebra for `X ↦ 1 + X`: halted is a leaf, stepping is a
    successor whose unique child is the next configuration. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: the connector between Mathlib's `StateTransition`-style step function `σ → Option σ` and the framework's own `natPF_NatListRegime` presentation of the `1 + X` functor. Mathlib carries both sides and no map between them; this is the bridge, and it is where the framework's operational and coalgebraic faces meet.
def stepCoalg : σ → natPF_NatListRegime.Obj σ :=
  fun s => match f s with
           | none    => ⟨false, fun e => e.elim⟩
           | some s' => ⟨true,  fun _ => s'⟩

/-- Every configuration is a leaf or a successor. The head is `Bool`, so there is no third case
    and in particular no "exists but has not begun" — that state is absent from the type, not
    ruled out by argument. The coalgebraic form of `no_unstarted_state`. -/
-- Prior art: this is Mathlib's `Bool.dichotomy` (`Data/Bool/Basic.lean`) at `(stepCoalg f s).1`.
theorem head_is_leaf_or_step (s : σ) :
    (stepCoalg f s).1 = false ∨ (stepCoalg f s).1 = true := by
  cases (stepCoalg f s).1
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A configuration that has not halted has head `true`: it is taking a step. Nothing starts it,
    because there is no prior state for it to start from. -/
theorem not_halted_is_stepping_head (s : σ) (h : f s ≠ none) :
    (stepCoalg f s).1 = true := by
  unfold stepCoalg
  cases hs : f s with
  | none => exact absurd hs h
  | some s' => rfl

/-! ## § II. The apophatic characterization — and it is unique -/

/-- **Never reaching a leaf, unpacked.** Such a behaviour is stepping right now, and its
    successor never reaches a leaf either: non-termination is hereditary along the unfolding.
    Stated as one destructor equation to keep the child cast-free (its type depends on the
    head). -/
theorem notEL_dest {x : Cofix natPF_NatListRegime.Obj} (h : ¬ EventuallyLeaf x) :
    ∃ c, Cofix.dest x = ⟨true, c⟩ ∧ ¬ EventuallyLeaf (c PUnit.unit) := by
  generalize hd : Cofix.dest x = d
  obtain ⟨b, c⟩ := d
  cases b with
  | false => exact absurd (EventuallyLeaf.leaf x c hd) h
  | true  => exact ⟨c, rfl, fun hc => h (EventuallyLeaf.step x c hd hc)⟩

/-- **UNIQUENESS.** Any behaviour that never reaches a leaf *is* `natInfinity`. A purely negative
    description — what it never does — pins a single point of the final coalgebra, with no
    element-hood in any machine carrier assumed.

    This is the computational counterpart of `quine_unique`, and unlike ZP-K's identification it
    is a Lean `=` within one type rather than a reading across types.

    **Prior art:** Escardó's `not-finite-is-∞'` (TypeTopology), proved there from function
    extensionality alone; Rutten, TCS 249 (2000) §12 pp. 51–52 for the same bisimulation on the
    same carrier. Also `Miniature.lean`'s `enat_fp_iff` in the `WithTop ℕ` presentation. Cited,
    not claimed. -/
theorem notEL_unique (x : Cofix natPF_NatListRegime.Obj) (h : ¬ EventuallyLeaf x) :
    x = natInfinity := by
  refine Cofix.bisim (fun a b => ¬ EventuallyLeaf a ∧ b = natInfinity) ?_ x natInfinity ⟨h, rfl⟩
  rintro a b ⟨ha, rfl⟩
  obtain ⟨c, hdest, hchild⟩ := notEL_dest ha
  rw [liftr_iff]
  exact ⟨true, c, (fun _ => natInfinity), hdest, natCofix_infinity_dest, fun _ => ⟨hchild, rfl⟩⟩

/-! ## § III. The bridge — a self-looping configuration unfolds to `natInfinity` -/

/-- A self-looping configuration unfolds to its own successor, satisfying the same destructor
    equation `natCofix_infinity_dest` records for `natInfinity`. -/
theorem loop_dest_is_own_successor (s : σ) (h : LoopsInPlace f s) :
    Cofix.dest (Cofix.corec (stepCoalg f) s)
      = ⟨true, fun _ => Cofix.corec (stepCoalg f) s⟩ := by
  rw [Cofix.dest_corec]
  unfold stepCoalg
  rw [h]
  rfl

/-- **The capstone.** The behaviour of a self-looping machine configuration IS `natInfinity` —
    an equality, in one type, by bisimulation.

    Read with `machine_snap_impossible`: a deterministic machine cannot host a configuration
    that both self-loops and is departed from. So the point this lands on is exactly the one the
    snap cannot leave from within a single machine, which is why the framework's departure is
    carried by instantiation succession (DA-2) rather than by the dynamics. -/
theorem loop_unfolds_to_infinity (s : σ) (h : LoopsInPlace f s) :
    Cofix.corec (stepCoalg f) s = natInfinity := by
  refine Cofix.bisim
    (fun a b => a = Cofix.corec (stepCoalg f) s ∧ b = natInfinity) ?_ _ _ ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  rw [liftr_iff]
  exact ⟨true, (fun _ => Cofix.corec (stepCoalg f) s), (fun _ => natInfinity),
    loop_dest_is_own_successor f s h, natCofix_infinity_dest, fun _ => ⟨rfl, rfl⟩⟩

/-! ## § IV. NO-GO gauge — the forcing needs the binary split

The results above are not facts about dynamics. They are facts about the head being two-valued.
This section supplies the counter-model that shows it, so the file carries its own falsifier. -/

/-- A three-valued step outcome: halted, stepping, or **idle** — present, not halted, and not
    taking a step. Exactly the state `σ → Option σ` cannot express.

    **Standard term first:** process algebra already separates these as *successful termination*
    versus *deadlock* — the defining ACP-versus-CCS distinction (Baeten & Weijland, *Process
    Algebra*, 1990). What is called `idle` here is what that literature calls **deadlock**; the
    framework reads the same state as *unstarted*. Same object, opposite valence. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: a deliberate counter-model, not a construction to build on. Mathlib has no three-valued step outcome because there is no reason to want one; this exists solely to be the carrier in which the forcing fails, and it should never be used as a framework object.
inductive TriStep (σ : Type) : Type
  | halted : TriStep σ
  | idle   : TriStep σ
  | step   : σ → TriStep σ
deriving DecidableEq

/-- "Halted" in the three-valued model. -/
def TriHalted {σ : Type} (g : σ → TriStep σ) (s : σ) : Prop := g s = TriStep.halted

/-- "Taking a step" in the three-valued model. -/
def TriStepping {σ : Type} (g : σ → TriStep σ) (s : σ) : Prop := ∃ s', g s = TriStep.step s'

/-- **The forcing fails with a third head value.** There is a configuration that is neither
    halted nor stepping — an unstarted state, expressible. `no_unstarted_state` proves this
    cannot happen when the head is two-valued; here it does. -/
theorem tri_unstarted_state_exists :
    ∃ (g : Unit → TriStep Unit) (s : Unit), ¬ TriHalted g s ∧ ¬ TriStepping g s := by
  refine ⟨fun _ => TriStep.idle, (), ?_, ?_⟩
  · simp [TriHalted]
  · simp [TriStepping]

/-- **And nothing starts it.** The idle machine stays idle. No dynamics forces it into motion,
    because being capable and being in motion have come apart. -/
theorem tri_idle_never_starts (s : Unit) :
    ∀ _n : ℕ, ¬ TriStepping (fun _ => (TriStep.idle : TriStep Unit)) s := by
  intro _ hstep
  simp [TriStepping] at hstep

/-- **The gauge, both halves in one statement.** Two-valued: the unstarted state is absent from
    the type. Three-valued: it is inhabited. So what makes execution forced is the CLEANNESS OF
    THE SPLIT, not the dynamics.

    **Reading (not a theorem):** the framework takes this to be a third encoding of AX-B1, its
    one substantive modelling commitment — beside the two-element carrier (`ax_b1_distinct`) and
    the order-theoretic predicate (`HasFirstStep`). That the three are *one* commitment is an
    interpretation in the manner of MC-1's bottom family: per-encoding membership is checkable,
    and no identity across them is claimed or well-formed. -/
theorem forcing_needs_the_binary_split :
    (∀ (σ : Type) (f : σ → Option σ) (s : σ), ¬ (f s ≠ none ∧ ¬ ∃ s', f s = some s')) ∧
    (∃ (g : Unit → TriStep Unit) (s : Unit), ¬ TriHalted g s ∧ ¬ TriStepping g s) :=
  ⟨fun _ f s => no_unstarted_state f s, tri_unstarted_state_exists⟩

end ZeroParadox

/-! ## Axiom Purity Check

§ I is axiom-free. § II and § III inherit `[propext, Classical.choice, Quot.sound]` from
Mathlib's QPF/`Cofix` machinery (bisimulation and the quotient construction), not from anything
the framework does. Measured, not quoted. -/

section PurityCheck
#print axioms ZeroParadox.head_is_leaf_or_step
#print axioms ZeroParadox.not_halted_is_stepping_head
#print axioms ZeroParadox.notEL_dest
#print axioms ZeroParadox.notEL_unique
#print axioms ZeroParadox.loop_dest_is_own_successor
#print axioms ZeroParadox.loop_unfolds_to_infinity
#print axioms ZeroParadox.tri_unstarted_state_exists
#print axioms ZeroParadox.forcing_needs_the_binary_split
end PurityCheck
