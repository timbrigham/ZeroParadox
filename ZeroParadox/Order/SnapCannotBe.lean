import ZeroParadox.Order.Snap
import ZeroParadox.Ordinal.CnfBridge
import ZeroParadox.Valuation.SemilatticeInstance
import ZeroParadox.Valuation.SnapDichotomy
import ZeroParadox.Reals.OrderedField
import ZeroParadox.Multihomed.BoundaryOrder
import ZeroParadox.Information.CrossingTrials
import ZeroParadox.Valuation.PolePassage
import ZeroParadox.Valuation.BallLine
import ZeroParadox.Reals.ConnectedNoFirstStep

/-!
# Machine-checked characterization index of the snap ⊥ → ε₀ — what the snap IS and IS NOT

The snap leg of the trio with `ZeroParadox/BottomCannotBe.lean` and
`ZeroParadox/Ordinal/Epsilon0CannotBe.lean`. `#check` lines plus anonymous `example`s, its only proofs;
every gloss is `Statement:` or `Reading:`. ⊥ and ε₀ are roles, each relative to a named structure.

Bedrock: shape **derived**, not an axiom (`t_snap_derived`; AX-1 is retired, and the snap occurs given the occurrence commitment and DA-1); **one-way** (`t_snap_irreversible`); returns to
a ⊥ read as a successor null, where **the novelty is a commitment** — the § IV glosses carry the fence.

## Engineer's Take

A canonical official representation of what the snap can and cannot be. Defined in Lean and referenced
by the proof assistant during development.
-/

section SnapCannotBeIndex

/-! ### § I. What the snap IS NOT — not an axiom, not reversible, not a return to the same `TrackedOutput` configuration -/
#check @ZeroParadox.t_snap_derived                    -- Statement: in `MachinePhase`, `c₀ ≠ c₁ ∧ c₁ ≠ c₀ ∧ join c₀ c₁ = c₁` — the shape (AX-1 is retired); that the snap occurs follows from the occurrence commitment together with DA-1, not from this line, and the next line is why
#check @ZeroParadox.tsnap_holds_but_nothing_moves     -- Statement: in `MachinePhase`, T-SNAP's statement holds together with a dynamics `stuckPhase` in which every phase is fixed, so T-SNAP is not an occurrence claim
-- `Statement:` a state sequence in `MachinePhase` that starts at its ⊥ `c₀` and never steps exists: the `example` in `ZeroParadox/Order/Snap.lean` stating that `MachinePhase` does not discharge `hocc` (`∃ S, S 0 = bot ∧ IsStateSequence S ∧ ∀ n, S (n + 1) = S n`).
#check @ZeroParadox.t_snap_irreversible              -- Statement: in any `ZPSemilattice`, for `le x y` and `x ≠ y`, no `z` has `join y z = x`. Reading: at `x := bot` and `y` any state above it (c₁ in `MachinePhase`, which the discrete chart names ε₀), no join from `y` returns to that semilattice's ⊥. The statement mentions neither ⊥ nor the snap
#check @ZeroParadox.dp2_execution_distinguishability  -- Statement: `preInstantiation` and `postInstantiation` share the output value and differ in machine state. Reading: the post-snap null and the pre-snap null are distinct instances in `TrackedOutput`; in the ℤ₂ chart the arc reapproaches the SAME 0 (`snap_arc_z2_loop`, § IV)
#check @ZeroParadox.da1_minimal_path                  -- Statement: the two configurations are DISTINCT while sharing an output value, with states `c₀` before and `c₁` after. It does NOT carry that the step is taken, and irrecoverability is not in it — see the fence in its home docstring

/-! ### § II. What the snap IS — the SHAPE of the join transition ⊥ → ε₀; that it occurs follows from the occurrence commitment and DA-1 -/
#check @ZeroParadox.t_snap_join                       -- Statement: in any `ZPSemilattice`, `join bot x = x` for every `x` (A4, `bot_join`); the binder is named ε₀. Reading: the algebraic core ⊥ ∨ ε₀ = ε₀
#check @ZeroParadox.t_snap_machine                    -- Statement: in `MachinePhase`, `join c₀ c₁ = c₁` (initial → running)
#check @ZeroParadox.t_snap_given                      -- Statement: over any ZPSemilattice, `S 0 = bot` (CC-1) and `S 1 ≠ S 0` (occurrence at the first step) give `t_snap_derived`'s shape at S 0, S 1; the inequalities restate `hocc`, and only the join comes from A4. No binder makes `S 1` an atom above `S 0`, and the step is assumed (`hocc`), not forced. Two commitments are the binders; `t_snap_derived` is its MachinePhase instance at a sequence chosen to move, and `MachinePhase` does not discharge `hocc`
-- Reading: CARRIER — the occurrence commitment, in two charts. Execution chart: instantiation occurs (Sense B,
--   a running configuration). Slot chart: the realized run has fired at least once, the hypothesis
--   `hw` of `t_snap_of_fires_once` (`ZeroParadox/Information/CrossingTrials.lean` § VIII).
#check @ZeroParadox.t_snap_of_fires_once             -- Statement: if `φ : Bool → L` sends `false` to ⊥ of `L` and `true` to a point other than ⊥ of `L`, and the tape `w` fires at some stage (`hw`), then `φ ∘ firedRun w hw` meets `t_snap_given`'s `hcc1` and `hocc` and is a state sequence; one way
#check @ZeroParadox.trials_fires_once                -- Statement: if `0 < p ≤ 1`, the tapes that fire at some stage have `trials p hp` measure one; it names no tape
-- `Statement:` CONTROL, a particular tape need not fire: the all-`false` tape fires at no stage.
example : ¬ ∃ k, (fun _ => false : ℕ → Bool) k = true := fun ⟨_, h⟩ => Bool.false_ne_true h
-- `Statement:` occurrence once: the slot chart's sequence steps at index 1 and stays, so it is not an
-- `IsStrictStateSequence` (ZP-A's proper ascent at every step).
example {L : Type*} [ZeroParadox.ZPSemilattice L] (φ : Bool → L) (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    ¬ ZeroParadox.ZPSemilattice.IsStrictStateSequence (φ ∘ ZeroParadox.firedRun w hw) := fun h => by
  have a : ZeroParadox.firedRun w hw 1 = true := (ZeroParadox.firedRun_spec w hw).2 0
  have b : ZeroParadox.firedRun w hw 2 = true := (ZeroParadox.firedRun_spec w hw).2 1
  exact h.2 1 (show φ (ZeroParadox.firedRun w hw 1) = φ (ZeroParadox.firedRun w hw 2) by rw [a, b])
-- Reading: CARRIER — the two charts correspond: a firing is read as an instantiation. That correspondence is
--   not proved; a firing is not shown to be an execution event.
-- Reading: CARRIER. "⊥ → ε₀" in the lines that use c₁ (`t_snap_derived`, `t_snap_machine`) is the
--   discrete-state chart, where ε₀ names the first state above ⊥ (c₁ in `MachinePhase`), and "atom above
--   ⊥" is a claim in that chart only. `t_snap_join`, `t_snap_irreversible` and
--   `t_snap_accessible_proper_subset` are generic: they hold at other points too, `t_snap_join` at ⊥
--   itself. The ordinal ε₀ is indexed in `ZeroParadox/Ordinal/Epsilon0CannotBe.lean`: the operator
--   α ↦ ω^α seeded at the base ⊥ (`epsilon0_eq_nfp_bot`), least fixed point AND tower supremum at once
--   (`epsilon0_min_eq_max`), never ⊥ (`epsilon0_ne_bot`). One order, restricted to two carriers, gives
--   two answers on covering. On all ordinals ⊥ ⋖ ε₀ is FALSE: 1 lies strictly between (first example).
--   On the carrier {0} ∪ {fixed points of α ↦ ω^α}, where 0 is adjoined by definition (`Or.inl`), ε₀
--   DOES cover ⊥, since no fixed point lies below it (`nothing_between_is_a_step`; last example).
example : ¬ ((⊥ : Ordinal) ⋖ Ordinal.epsilon 0) := fun h =>
  h.2 (show (⊥ : Ordinal) < 1 by rw [Ordinal.bot_eq_zero]; exact zero_lt_one)
    (lt_trans Ordinal.one_lt_omega0 (Ordinal.omega0_lt_epsilon 0))
-- `Statement:` ε₀ is a limit ordinal: it is not minimal (`Ordinal.epsilon_pos`) and covers no ordinal
-- at all (no `b` has `b ⋖ ε₀`).
example : Order.IsSuccLimit (Ordinal.epsilon 0) := by
  refine Order.IsSuccPrelimit.isSuccLimit_of_not_isMin ?_ (not_isMin_iff.2 ⟨0, Ordinal.epsilon_pos 0⟩)
  rw [Ordinal.isSuccPrelimit_iff_omega0_dvd, ← Ordinal.omega0_opow_epsilon 0]
  simpa only [Ordinal.opow_one] using
    Ordinal.opow_dvd_opow Ordinal.omega0 (Order.one_le_iff_pos.2 (Ordinal.epsilon_pos 0))
example : (⟨0, Or.inl rfl⟩ : {o : Ordinal | o = 0 ∨ Ordinal.omega0 ^ o = o}) ⋖
    ⟨Ordinal.epsilon 0, Or.inr ZeroParadox.epsilon0_is_fixedpoint⟩ := by
  refine ⟨Ordinal.epsilon_pos 0, ?_⟩
  rintro ⟨c, hc | hc⟩ h0 hε
  · exact (ne_of_gt (show (0 : Ordinal) < c from h0)) hc
  · exact ZeroParadox.nothing_between_is_a_step c hε hc
-- `Statement:` `t_snap_given`'s binders and AX-B1's `HasFirstStep` form do not supply the cover. On ℕ
-- (join `max`, ⊥ = 0) the run 0, 2, 2, … meets `hcc1`, `hocc` and `HasFirstStep 0`, and `S 1` does not
-- cover `S 0`: 1 lies between.
example : let S : ℕ → ℕ := fun n => if n = 0 then 0 else 2
    S 0 = ZeroParadox.ZPSemilattice.bot ∧ S 1 ≠ S 0 ∧ ZeroParadox.HasFirstStep (0 : ℕ) ∧
      ¬ (S 0 ⋖ S 1) :=
  ⟨rfl, by decide, ⟨1, Nat.lt_succ_self 0, fun c h1 h2 => by omega⟩,
    fun h => h.2 (c := 1) (by decide) (by decide)⟩
#check @ZeroParadox.t_snap_given_cover               -- Statement: `t_snap_given` with the cover as a third hypothesis `hcov`, in ZP-A's induced order (`zpSemilatticeSup`); concludes `t_snap_given`'s triple and `bot ⋖ S 1`, the latter `hcov` transported along `hcc1`, and `hocc` follows from `hcov`. The run above meets every binder but `hcov`
-- `Statement:` the run above, in that order: 2 does not cover 0. The order is passed with `@`, since
-- a `letI` loses to ℕ's own `<`.
example : ¬ @CovBy ℕ (ZeroParadox.zpSemilatticeSup ℕ).toLT 0 2 := fun h =>
  h.2 (c := 1) ⟨show ZeroParadox.ZPSemilattice.join 0 1 = 1 by decide,
      show ¬ ZeroParadox.ZPSemilattice.join 1 0 = 0 by decide⟩
    ⟨show ZeroParadox.ZPSemilattice.join 1 2 = 2 by decide,
      show ¬ ZeroParadox.ZPSemilattice.join 2 1 = 1 by decide⟩
-- `Statement:` on `Set Bool` (join `∪`, ⊥ = ∅) `∅` has two distinct covers in that order, with join
-- `Set.univ`, so `hcov` does not fix the target; on a carrier with its own linear order,
-- `axb1_gives_unique_target` fixes the cover in that order. Reading: prior art, Winskel, *Event
-- structures*, LNCS 255 (1987). `Set Bool` is, up to renaming events, the configuration domain of
-- Example 1.1.6 p. 328, concurrency, the "little square"; Example 1.1.5 p. 327, conflict, is the
-- contrast, two covers of ∅ with no join; within the class every pair has a join (next example), so
-- 1.1.5's shape does not arise.
example : letI : ZeroParadox.ZPSemilattice (Set Bool) :=
      ⟨(· ∪ ·), ∅, Set.union_assoc, Set.union_comm, Set.union_self, Set.empty_union⟩
    @CovBy (Set Bool) (ZeroParadox.zpSemilatticeSup (Set Bool)).toLT ∅ {true} ∧
      @CovBy (Set Bool) (ZeroParadox.zpSemilatticeSup (Set Bool)).toLT ∅ {false} ∧
      ({true} : Set Bool) ≠ {false} ∧ ({true} : Set Bool) ∪ {false} = Set.univ := by
  letI : ZeroParadox.ZPSemilattice (Set Bool) :=
    ⟨(· ∪ ·), ∅, Set.union_assoc, Set.union_comm, Set.union_self, Set.empty_union⟩
  have key : ∀ a b : Set Bool,
      @LT.lt (Set Bool) (ZeroParadox.zpSemilatticeSup (Set Bool)).toLT a b ↔ a ⊂ b := fun _ _ =>
    and_congr Set.union_eq_right (not_congr Set.union_eq_right)
  have cov : ∀ b : Bool, @CovBy (Set Bool) (ZeroParadox.zpSemilatticeSup (Set Bool)).toLT ∅ {b} :=
    fun b => ⟨(key _ _).2 (Set.empty_covBy_singleton b).1,
      fun _ h1 h2 => (Set.empty_covBy_singleton b).2 ((key _ _).1 h1) ((key _ _).1 h2)⟩
  exact ⟨cov true, cov false, fun h => absurd (h ▸ Set.mem_singleton true) (by simp),
    by ext b; cases b <;> simp⟩
-- `Statement:` in ZP-A's induced order any two states, so any two covers of `bot`, have `join a b` as
-- least upper bound: the join is total.
example {L : Type*} [ZeroParadox.ZPSemilattice L] (a b : L) :
    letI := ZeroParadox.zpSemilatticeSup L; IsLUB {a, b} (ZeroParadox.ZPSemilattice.join a b) := by
  letI := ZeroParadox.zpSemilatticeSup L; exact isLUB_pair
#check @Set.covBy_iff_exists_insert                   -- Statement: `s ⋖ t ↔ ∃ a ∉ s, insert a s = t`. Reading: the powerset form of Winskel's one-event characterisation of a cover (p. 336)
-- `Statement:` a two-state carrier does supply the cover: if every state is ⊥ or `a`, a step off ⊥ lands on `a`
-- and every state is `S 0` or `S 1`. `MachinePhase` is such a carrier, with `a = c₁`.
example {L : Type*} [ZeroParadox.ZPSemilattice L] (a : L)
    (h2 : ∀ x : L, x = ZeroParadox.ZPSemilattice.bot ∨ x = a) (S : ℕ → L)
    (hcc1 : S 0 = ZeroParadox.ZPSemilattice.bot) (hocc : S 1 ≠ S 0) :
    S 1 = a ∧ ∀ x : L, x = S 0 ∨ x = S 1 := by
  have h1 : S 1 = a := (h2 (S 1)).resolve_left fun h => hocc (h.trans hcc1.symm)
  exact ⟨h1, fun x => (h2 x).imp (fun h => h.trans hcc1.symm) (fun h => h.trans h1.symm)⟩
example : ∀ x : ZeroParadox.MachinePhase, x = ZeroParadox.ZPSemilattice.bot ∨ x = ZeroParadox.c₁ := by
  intro x; cases x; exacts [Or.inl rfl, Or.inr rfl]
#check @bot_covBy_iff                                 -- Statement: in any partial order with a least element ⊥ (`OrderBot`), `⊥ ⋖ a ↔ IsAtom a`; an atom's two halves are `a ≠ ⊥` and nothing strictly between, a different pair from the ordinal ε₀'s least fixed point and tower supremum
#check @covBy_iff_atom_Ici                            -- Statement: `a ⋖ b ↔ IsAtom ⟨b, _⟩ : Set.Ici a`; a cover is an atom measured from the bottom of `Set.Ici a`
-- `Statement:` the ℕ run's step 0 → 2 lands on an atom one rung up: 2 is not an atom of `Set.Ici 0`,
-- and it is an atom of `Set.Ici 1`.
example : ¬ @IsAtom (Set.Ici (0 : ℕ)) _ Set.Ici.orderBot ⟨2, Nat.zero_le 2⟩ ∧
    @IsAtom (Set.Ici (1 : ℕ)) _ Set.Ici.orderBot ⟨2, (by decide : (1 : ℕ) ≤ 2)⟩ := by
  have h02 : (0 : ℕ) ≤ 2 := Nat.zero_le 2
  have h12 : (1 : ℕ) ≤ 2 := by decide
  have c12 : (1 : ℕ) ⋖ 2 := ⟨by decide, fun c h1 h2 => by omega⟩
  exact ⟨fun h => ((covBy_iff_atom_Ici h02).2 h).2 (c := 1) (by decide) (by decide),
    (covBy_iff_atom_Ici h12).1 c12⟩

/-! ### § III. What the snap DOES — it narrows reachability, permanently -/
#check @ZeroParadox.t_snap_accessible_proper_subset   -- Statement: in any `ZPSemilattice`, for `bot ≠ ε₀` (any such element), the up-set of ε₀ is a proper subset of the up-set of `bot`. Reading: `bot` is not in the smaller set
#check @ZeroParadox.da2_bottom_characterization       -- Statement: the ⊥ role within one `ZPSemilattice`: `(∀ x, join S x = x) ↔ S = bot`
#check @ZeroParadox.da3_accessibleCardinality         -- Statement: a definition, the cardinality of the up-set `{x // le p x}` of `p`. Reading: reachable cardinality is position-relative

/-! ### § IV. The snap returns to a ⊥ (read as a successor null — a commitment); its 2-adic realization is a loop -/
#check @ZeroParadox.c_da2_novelty                     -- Statement: contrapositive of the role fact, in one `ZPSemilattice`: a state `≠ bot` cannot satisfy the join-identity. Reading: "distinct successor instantiation" is the reading, not the statement
#check @ZeroParadox.snap_arc_z2_loop                  -- Statement: the `cnfToZp2` image of tower stage 0 is ℤ_[2]'s 0, every stage `n ≥ 1` has a nonzero image, and the images tend to that same 0
#check @ZeroParadox.arc_q2Val                         -- Statement: read by `q2Val`, those images are ⊤ of `ℕ∞` at stage 0, `n` at every stage `n ≥ 1`, and tend to ⊤, which is `q2Val` of ℤ_[2]'s 0 (`q2Val_bot`; `ZeroParadox/Valuation/PolePassage.lean`)
#check @ZeroParadox.no_path_zero_infty                -- Statement: no continuous path in `Sphere` (`OnePoint ℚ_[2]`) runs from 0 of `ℚ_[2]` to ∞ of `Sphere`. Reading: the loop returns to 0 of `ℚ_[2]` without passing ∞ of `Sphere` (`arc_never_meets_infty`); its `rInv` image is the loop at ∞ (`rInv_arcS`)
#check @ZeroParadox.t_iz_limit_is_new_null            -- Statement: role half only, in any `ZPSemilattice`: (∀ x, join terminal x = x) → terminal = bot of that semilattice. Novelty is NOT in this statement; do not cite it as the novelty witness

/-! ### § V. WHERE the snap is RULED OUT — and what only removes the obstruction

Reading: CARRIER. These lines BOUND the snap; none supplies it. ZP-F rules it out in every ordered
field; ZP-B removes the topological obstruction in ℚ_p without replacing it. The first step is AX-B1,
a modelling commitment. Its conditional form is a property a carrier has or lacks: `Bool` and `ℕ` have
it, `ℝ` lacks it (the examples beside `HasFirstStep`, `ZeroParadox/Reals/OrderedField.lean`); the
commitment is that the framework's carrier has it. AX-B1 holds at every state with anything above it:
each has a first distinct state above it, with nothing strictly between. A state with nothing above it
owes no step. -/
#check @ZeroParadox.axb1_gives_unique_target          -- Statement: on a LINEAR order, AX-B1 at `bot` gives exactly one cover; the `Set Bool` control beside it in `ZeroParadox/Reals/OrderedField.lean` has two
#check @ZeroParadox.HasFirstStep                      -- Statement: an ORDER predicate — `∃ a, bot ⋖ a`, Mathlib's covering relation. ⚠ `LT ℚ_[2]` does not synthesize (probed at p = 2, the `#check_failure` in `ZeroParadox/BottomCannotBe.lean` § ROLE), so this is not statable of ℚ₂ until an order is supplied (the norm preorder of `ZeroParadox/BottomCannotBe.lean` § ROLE); the p-adic line below fences NORM values, a different predicate
#check @ZeroParadox.f_snap_blocked                    -- Statement: over `Field + LinearOrder + IsStrictOrderedRing`, every positive ε₀ admits a smaller positive δ; the binder ε₀ is any positive element of `F`, a candidate first step above `F`'s 0, not the ordinal
#check @ZeroParadox.f_snap_impossible                 -- Statement: hence no such field has a least positive element. No Archimedean hypothesis appears in the binders
#check @ZeroParadox.axb1_fails_in_ordered_field       -- Statement: `¬ HasFirstStep (0 : F)`. Reading: AX-B1 is what supplies the step; an ordered field lacks it, and that the framework's carrier has it is the commitment
#check @ZeroParadox.axb1_fails_everywhere_iff_dense   -- Statement: the obstruction CHARACTERIZED, over a bare `Preorder` with no field and no topology — `DenselyOrdered α ↔ ∀ bot, ¬ HasFirstStep bot`. `axb1_fails_in_ordered_field` directly above is an instance of its right-hand side; `f_snap_impossible` is the same fact in the halving vocabulary, not an instance of this statement. Density is what obstructs a first step — connectedness is a topological fence (`real_no_snap`); on a linear order with its order topology it implies this one (`no_firstStep_of_preconnected`), and not conversely
#check @ZeroParadox.no_firstStep_of_preconnected      -- Statement: on a linear order with its order topology, preconnected gives `¬ HasFirstStep bot` at every `bot`; Mathlib's `denselyOrdered_of_preconnectedSpace` in `HasFirstStep` form, at `[propext, Quot.sound]`. Reading: on one linearly ordered carrier the topological fence implies the order fence, not conversely (the ℚ control in `ZeroParadox/Reals/ConnectedNoFirstStep.lean`)
#check @ZeroParadox.preconnected_iff_no_firstStep     -- Statement: on a conditionally complete linear order with its order topology, `PreconnectedSpace α ↔ ∀ bot, ¬ HasFirstStep bot`; the completeness binder carries the backward direction (ℚ is dense and not preconnected)
#check @ZeroParadox.cover_at_zero_iff_not_dense      -- Statement: at one point, in a linearly ordered additive commutative group: `HasFirstStep 0` iff the order is not dense; no Archimedean hypothesis (`ZeroParadox/Valuation/PolePassage.lean` § VI)
#check @ZeroParadox.cover_at_zero_iff_int             -- Statement: with `[Archimedean G]` added, `HasFirstStep 0` iff `G ≃+o ℤ`
#check @ZeroParadox.hahnArc_loop                      -- Statement: CONTROL, on `HahnSeries ℚ ℚ`, value group ℚ (no first step at 0), `addVal` of `hahnArc` is ⊤ at stage 0, finite after, and eventually above every rational. Reading: CARRIER — density refuses the value group a first step and does not refuse the valuation loop ⊤ → finite → ⊤
#check @ZeroParadox.ballLine_covBy                    -- Statement: in `Set.range ballLine`, the closed balls of radius `2^(-n)` about 0 of `ℚ_[2]` under inclusion, `ballLine (n + 1) ⋖ ballLine n` (`ZeroParadox/Valuation/BallLine.lean`)
#check @ZeroParadox.end_bot_no_first_step             -- Statement: in `WithBot (WithTop ℤ)`, that line with both ends adjoined, ⊥ has no first step. Reading: CARRIER — the first step lives at the vertices, not at the ends
#check @ZeroParadox.end_top_covers_nothing            -- Statement: in `WithBot (WithTop ℤ)`, nothing is covered by ⊤
#check @ZeroParadox.radiusPath                        -- Statement: CONTROL, a path in `ℝ≥0∞` from 0 to ⊤; `ℝ≥0∞` is densely ordered, so 0 has no first step there (`axb1_fails_everywhere_iff_dense`). Reading: CARRIER — the radius order joins the ends and has no first step; read back as balls, a positive radius lands on a vertex (`closedBall_eq_ballLine`)
#check @ZeroParadox.real_no_snap                      -- Statement: CARRIER — ℝ is NOT totally disconnected
#check @ZeroParadox.padic_snaps                       -- Statement: CARRIER — ℚ_p IS totally disconnected. Reading: this removes the obstruction and supplies no first step — norms accumulate at 0 in ANY non-trivially normed field (Mathlib `NormedField.exists_norm_lt`), ℝ included, so that half is not p-adic
#check @ZeroParadox.snap_dichotomy                    -- Statement: every ℚ_p is totally disconnected and ℝ is not, and for NONTRIVIAL absolute values on ℚ, real and p-adic are exclusive and exhaustive (Ostrowski). ⚠ SCOPE: completions of ℚ only

/-! ### § VI. The up-and-over shape's climbing kind — OVER is a cover, UP is a closure; two orders on one boundary model -/
#check @ZeroParadox.UpAndOver                         -- Statement: a structure on a partial order: a closure operator `up`, a corner (a closed `y`, a cover `y ⋖ b`, `up b ≠ b`), and a cover at every non-maximal closed point
-- `Statement:` the `cover` field is `HasFirstStep`, asked at each non-maximal closed point of `up` (a landing).
example {α : Type} [PartialOrder α] (U : ZeroParadox.UpAndOver α) {y : α} (hy : U.up.IsClosed y)
    (hmax : ¬ IsMax y) : ZeroParadox.HasFirstStep y := U.cover y hy hmax
#check @ZeroParadox.UpAndOver.isEmpty_of_denselyOrdered -- Statement: no densely ordered carrier carries an `UpAndOver`; the corner's cover is refused. Reading: as § V refuses ℝ a first step
example : IsEmpty (ZeroParadox.UpAndOver ℝ) := ZeroParadox.UpAndOver.isEmpty_of_denselyOrdered
#check @ZeroParadox.ordinalUpAndOver                  -- Statement: `Ordinal` carries it: `up` is `nfp (ω^·)` (`snapNucleus`), covers by `Order.succ`, the corner at ε₀ and `succ ε₀`
#check @ZeroParadox.phase_floor_covBy_snap            -- Statement: floor-below order, `WithBot Ordinal`: its ⊥ (the boundary model's floor) is covered by the snap `↑0` (OVER)
#check @ZeroParadox.phaseUp_snap                      -- Statement: floor-below order: `phaseUpAndOver.up` sends `↑0` to `↑ε₀` (UP)
#check @ZeroParadox.phase_epsilon0_isLeast_landing_above_floor -- Statement: floor-below order: `↑ε₀` is the least closed point (landing) of that `up` strictly above ⊥ of `WithBot Ordinal`
#check @ZeroParadox.phase_floor_snap_epsilon0_ne      -- Statement: in `WithBot Ordinal`, the snap `↑0` ≠ `↑ε₀`, and its ⊥ differs from both
#check @ZeroParadox.phaseEquivWithTop_floor_covers_nothing -- Statement: floor-above order, `WithTop Ordinal`: the boundary model's floor is ⊤ and covers nothing
#check @ZeroParadox.phaseTop_epsilon0_isLeast_landing_above_snap -- Statement: floor-above order: the snap `↑0` is ⊥ of `WithTop Ordinal`, and `↑ε₀` is the least `snapNucleusTop`-closed point strictly above it
-- Reading: CARRIER. The two orders are a dichotomy over one boundary model, neither of them THE order.
--   In each, `↑ε₀` is the first closed point (landing) of the closure above that order's ⊥. On all of `Ordinal`, ⊥ ⋖ ε₀ is false
--   (§ II); in `WithBot Ordinal`, ⊥ to `↑ε₀` is one OVER (a cover) followed by one UP (the closure).

end SnapCannotBeIndex
