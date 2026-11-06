-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): a first step at ⊥ of a ZP-A semilattice and a typical tape, as two hypotheses giving the snap's cover and its occurrence. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Information.Disjunctive
import ZeroParadox.Reals.OrderedField
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Order.Filter.EventuallyConst
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Two requirements: a first step at ⊥ of `L`, and a typical tape

Two HYPOTHESES, neither discharged: `BotHasFirstStep L`, a cover of ⊥ of a `ZPSemilattice L` in
ZP-A's induced order (AX-B1's form), and a tape typical for `trials p hp`, in three strengths:
zero-block typical, Martin-Löf random, frequency of `true` tending to `p` (law of large numbers).
§ I–III: with `0 < p` they give `t_snap_given_cover`'s full conclusion. § IV: binary expansion
sends a tape to a dyadic rational iff the tape is eventually constant.
## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---
-/

namespace ZeroParadox

open MeasureTheory ProbabilityTheory Filter ZPSemilattice

/-! ## § I. Two hypotheses, one snap

`BotHasFirstStep` constrains the carrier `L`; `ZeroBlockTypical` constrains one tape. `φ : Bool → L`
is built from the cover's witness, and no map from ⊥ of `L` to a tape is claimed. -/

/-- `Statement:` ⊥ of `L` has a first step (a cover) in ZP-A's induced order, `zpSemilatticeSup`.
`Reading:` AX-B1's `HasFirstStep` form, carried as a hypothesis, never as a field. -/
def BotHasFirstStep (L : Type*) [ZPSemilattice L] : Prop :=
  letI := zpSemilatticeSup L; HasFirstStep (bot : L)

/-- `Statement:` the tape `w` avoids every zero-block test for `trials p hp` (`AvoidsTests`). -/
def ZeroBlockTypical (p : NNReal) (hp : p ≤ 1) (w : ℕ → Bool) : Prop :=
  AvoidsTests (ZeroBlockTest (trials p hp)) w

/-- `Statement:` a tape that fires infinitely often fires at some stage. -/
theorem fires_once_of_mem_limsup {w : ℕ → Bool} (h : w ∈ Filter.limsup fires Filter.atTop) :
    ∃ k, w k = true := by
  rw [mem_limsup_iff_frequently_mem] at h
  obtain ⟨k, -, hk⟩ := h.forall_exists_of_atTop 0
  exact ⟨k, hk⟩

/-- `Statement:` if ⊥ of `L` has a first step and the tape `w` fires at some stage (`hw`), some
`φ : Bool → L` makes `S := φ ∘ firedRun w hw` start at ⊥ of `L`, step at index 1, be a state
sequence, and carry `t_snap_given_cover`'s conclusion (the triple and `⊥ ⋖ S 1`). One way. The
cover `hcov` comes only through `φ true`, the cover's witness (`hcov_iff_phi_cover`). -/
theorem snap_of_firstStep_fires_once {L : Type*} [ZPSemilattice L] (hR1 : BotHasFirstStep L)
    (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    ∃ φ : Bool → L,
      let S := φ ∘ firedRun w hw
      (S 0 = bot ∧ S 1 ≠ S 0 ∧ IsStateSequence S) ∧
      ((S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ join (S 0) (S 1) = S 1) ∧
        letI := zpSemilatticeSup L; (bot : L) ⋖ S 1) := by
  obtain ⟨a, ha⟩ := hR1
  let φ : Bool → L := fun b => if b then a else bot
  have hφ1 : φ true ≠ bot := by
    letI := zpSemilatticeSup L
    exact fun h => ha.1.ne h.symm
  refine ⟨φ, ?_⟩
  intro S
  obtain ⟨hS0, hS1, hSeq, -⟩ := t_snap_of_fires_once φ rfl hφ1 w hw
  have hS1a : S 1 = a := by
    show φ (firedRun w hw 1) = a
    rw [(firedRun_spec w hw).2 0]; rfl
  have hcov : letI := zpSemilatticeSup L; S 0 ⋖ S 1 := by
    have e0 : S 0 = bot := hS0
    rw [e0, hS1a]; exact ha
  exact ⟨⟨hS0, hS1, hSeq⟩, t_snap_given_cover S hS0 hS1 hcov⟩

/-- `Statement:` if ⊥ of `L` has a first step and `w` is zero-block typical for `trials p hp` with
`0 < p`, then `w` fires (`hw`) and `snap_of_firstStep_fires_once`'s conclusion holds. One way.
`Reading:` CARRIER: the occurrence commitment's slot-chart hypothesis `hw` comes from typicality of
one tape, the cover from AX-B1's form on `L`; neither is discharged, and a firing is not proved to
be an execution event (`ZeroParadox/Order/Snap.lean`). -/
theorem snap_of_two_requirements {L : Type*} [ZPSemilattice L] (hR1 : BotHasFirstStep L)
    (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (w : ℕ → Bool) (hR2 : ZeroBlockTypical p hp w) :
    ∃ (φ : Bool → L) (hw : ∃ k, w k = true),
      let S := φ ∘ firedRun w hw
      (S 0 = bot ∧ S 1 ≠ S 0 ∧ IsStateSequence S) ∧
      ((S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ join (S 0) (S 1) = S 1) ∧
        letI := zpSemilatticeSup L; (bot : L) ⋖ S 1) := by
  obtain ⟨φ, h⟩ := snap_of_firstStep_fires_once hR1 w
    (fires_once_of_mem_limsup (fires_io_of_avoids p hp hp0 _ (fun _ h => h) w hR2))
  exact ⟨φ, _, h⟩

/-- `Statement:` for a FIXED `φ` with `φ false = ⊥`, the run's `hcov` holds iff `φ true` covers ⊥ of
`L`; both directions. -/
theorem hcov_iff_phi_cover {L : Type*} [ZPSemilattice L] (φ : Bool → L)
    (hφ0 : φ false = bot) (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    (letI := zpSemilatticeSup L; (φ ∘ firedRun w hw) 0 ⋖ (φ ∘ firedRun w hw) 1) ↔
      (letI := zpSemilatticeSup L; (bot : L) ⋖ φ true) := by
  have h0 : (φ ∘ firedRun w hw) 0 = bot := by simp [(firedRun_spec w hw).1, hφ0]
  have h1 : (φ ∘ firedRun w hw) 1 = φ true := by simp [(firedRun_spec w hw).2 0]
  rw [h0, h1]

/-- `Statement:` `BotHasFirstStep L` iff some `φ` has `φ false = ⊥` and `⊥ ⋖ φ true`. -/
theorem botHasFirstStep_iff_exists_phi {L : Type*} [ZPSemilattice L] :
    BotHasFirstStep L ↔
      ∃ φ : Bool → L, φ false = bot ∧ (letI := zpSemilatticeSup L; (bot : L) ⋖ φ true) := by
  constructor
  · rintro ⟨a, ha⟩; exact ⟨fun b => if b then a else bot, rfl, ha⟩
  · rintro ⟨φ, -, h⟩; exact ⟨φ true, h⟩

/-- `Statement:` `NNReal` with join `max` and ⊥ = 0 of `NNReal`; a definition, not an instance. -/
abbrev nnrealMaxZPS : ZPSemilattice NNReal where
  join := max
  bot := 0
  join_assoc := max_assoc
  join_comm := max_comm
  join_idem := max_self
  bot_join := fun x => max_eq_right (zero_le x)

/-- `Statement:` the zero-block typical tapes include the all-`true` tape at every `p ≤ 1`; the
`example` in `ZeroParadox/Information/CrossingTrials.lean` § VI, named. -/
theorem allTrue_zeroBlockTypical (p : NNReal) (hp : p ≤ 1) :
    ZeroBlockTypical p hp (fun _ => true) := by
  rintro U ⟨hμ, f, -, hf⟩ hmem
  have h1 := hμ 1
  rw [hf 1] at h1
  have hm : (fun _ => true : ℕ → Bool) ∈ zeroBlock (f 1).1 (f 1).2 := by
    rw [← hf 1]; exact Set.mem_iInter.1 hmem 1
  rcases Nat.eq_zero_or_pos (f 1).2 with h0 | hpos
  · have : zeroBlock (f 1).1 (f 1).2 = Set.univ := by
      ext w; simp [zeroBlock, h0]
    rw [this, measure_univ] at h1
    norm_num at h1
  · have := hm (f 1).1 (by simp [Finset.mem_Ico]; omega)
    simp at this

section NNRealControl

attribute [local instance] nnrealMaxZPS

/-- `Statement:` under `nnrealMaxZPS`, ZP-A's induced `<` is `NNReal`'s own `<`. -/
theorem nnreal_zp_lt_iff (x y : NNReal) :
    @LT.lt NNReal (zpSemilatticeSup NNReal).toLT x y ↔ x < y := by
  show (max x y = y ∧ ¬ max y x = x) ↔ x < y
  rw [max_eq_right_iff, max_eq_right_iff, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- `Statement:` CONTROL, drop the first step: ⊥ of `NNReal` under `max` has no cover. -/
theorem nnreal_not_botHasFirstStep : ¬ BotHasFirstStep NNReal := by
  rintro ⟨a, ha⟩
  have h0a : (0 : NNReal) < a := (nnreal_zp_lt_iff _ _).1 ha.1
  exact ha.2 ((nnreal_zp_lt_iff _ _).2 (half_pos h0a)) ((nnreal_zp_lt_iff _ _).2 (half_lt_self h0a))

-- Statement: CONTROL, drop the first step: on `NNReal` under `max` the all-`true` tape is zero-block
-- typical at `p = 1/2`, and for every `φ` and firing proof the run's `S 1` does not cover ⊥.
example : ZeroBlockTypical (1/2) (by norm_num) (fun _ => true) ∧
    ∀ (φ : Bool → NNReal) (hw : ∃ k, (fun _ => true : ℕ → Bool) k = true),
      ¬ @CovBy NNReal (zpSemilatticeSup NNReal).toLT bot ((φ ∘ firedRun (fun _ => true) hw) 1) :=
  ⟨allTrue_zeroBlockTypical _ _, fun _ _ h => nnreal_not_botHasFirstStep ⟨_, h⟩⟩

end NNRealControl

-- Statement: CONTROL, drop typicality: for `0 < p ≤ 1` the all-`false` tape is not zero-block
-- typical; it never fires, so no `hw` exists for it on any carrier.
example (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) : ¬ ZeroBlockTypical p hp (fun _ => false) := by
  obtain ⟨U, hU, hUeq⟩ := zeroBlockTest_silentFrom p hp hp0 0
  have hmem : (fun _ => false : ℕ → Bool) ∈ ⋂ m, U m := by
    rw [hUeq]; exact fun _ _ => rfl
  exact fun h => h U hU hmem

/-- `Statement:` `Bool` with join `||` and ⊥ = `false`; a definition, not an instance. -/
abbrev boolOrZPS : ZPSemilattice Bool where
  join := (· || ·)
  bot := false
  join_assoc := Bool.or_assoc
  join_comm := Bool.or_comm
  join_idem := Bool.or_self
  bot_join := Bool.false_or

section BoolControl

attribute [local instance] boolOrZPS

/-- `Statement:` CONTROL, the two-element carrier: under `boolOrZPS`, `true` covers ⊥ = `false`. -/
theorem bool_botHasFirstStep : BotHasFirstStep Bool :=
  ⟨true, ⟨⟨rfl, by decide⟩, fun c h1 h2 => by
    cases c
    · exact h1.2 rfl
    · exact h2.2 rfl⟩⟩

end BoolControl

-- Statement: CONTROL, `Unit`: under any `ZPSemilattice Unit`, ⊥ has no first step.
example [ZPSemilattice Unit] : ¬ BotHasFirstStep Unit := by
  rintro ⟨a, ha⟩
  letI := zpSemilatticeSup Unit
  exact @LT.lt.ne Unit (zpSemilatticeSup Unit).toPreorder _ _ ha.1 (Subsingleton.elim _ _)

/-! ## § II. Martin-Löf randomness, defined locally

Not located in the pinned Mathlib as of 2026-11-06 (grep of `.lake/packages/mathlib/Mathlib` for
`martin.?l`, `kurtz`, case-insensitive: no hit). A test's cylinders are listed by a computable `g`
with no access to `μ`, so for a non-computable `p` this is no stronger than randomness relative to
`p`. Martin-Löf random implies zero-block typical; the converse fails at the all-`true` tape. -/

/-- `Statement:` the tapes extending the finite word `l` (a prefix cylinder). -/
def prefixCyl (l : List Bool) : Set (ℕ → Bool) := {x | ∀ i (h : i < l.length), x i = l[i]}

/-- `Statement:` `U` is a Martin-Löf test for `μ`: level `m` has measure at most `2⁻ᵐ` and is the
union of the prefix cylinders a computable `g` lists at `(m, j)`, `none` skipped. -/
def MLTest (μ : Measure (ℕ → Bool)) (U : ℕ → Set (ℕ → Bool)) : Prop :=
  (∀ m, μ (U m) ≤ 2⁻¹ ^ m) ∧
    ∃ g : ℕ × ℕ → Option (List Bool), Computable g ∧ ∀ m, U m = ⋃ j, ⋃ l ∈ g (m, j), prefixCyl l

/-- `Statement:` `w` is Martin-Löf random for `μ`: it lies in no test's intersection. -/
def MLRandom (μ : Measure (ℕ → Bool)) (w : ℕ → Bool) : Prop := AvoidsTests (MLTest μ) w

/-- `Statement:` the tapes reading `b` at every stage in `[N, N + n)`. -/
def constBlock (b : Bool) (N n : ℕ) : Set (ℕ → Bool) :=
  {w | ∀ k ∈ Finset.Ico N (N + n), w k = b}

theorem zeroBlock_eq_constBlock (N n : ℕ) : zeroBlock N n = constBlock false N n := rfl

/-- `Statement:` the `j`-th word: the low `N` bits of `j`, then `n` copies of `b`. -/
def blockWord (b : Bool) (N n j : ℕ) : List Bool :=
  (List.range N).map (bitAt j) ++ (List.range n).map (fun _ => b)

theorem blockWord_length (b : Bool) (N n j : ℕ) : (blockWord b N n j).length = N + n := by
  simp [blockWord]

theorem blockWord_getElem (b : Bool) (N n j i : ℕ) (h : i < (blockWord b N n j).length) :
    (blockWord b N n j)[i] = if i < N then bitAt j i else b := by
  unfold blockWord
  rw [List.getElem_append]
  split_ifs with h1 h2 h2
  · simp
  · simp at h1; omega
  · simp at h1; omega
  · simp

/-- `Statement:` a constant block is the union over `j` of the cylinders of `blockWord b N n j`. -/
theorem constBlock_eq_iUnion (b : Bool) (N n : ℕ) :
    constBlock b N n = ⋃ j, prefixCyl (blockWord b N n j) := by
  ext x
  simp only [constBlock, Finset.mem_Ico, Set.mem_setOf_eq, Set.mem_iUnion, prefixCyl]
  constructor
  · intro hx
    refine ⟨ofBits N (fun i => x i), fun i hi => ?_⟩
    rw [blockWord_getElem]
    split_ifs with hN
    · exact (bitAt_ofBits N (fun i => x i) ⟨i, hN⟩).symm
    · rw [blockWord_length] at hi; exact hx i ⟨by omega, hi⟩
  · rintro ⟨j, hj⟩ k hk
    have hk' : k < (blockWord b N n j).length := by rw [blockWord_length]; exact hk.2
    rw [hj k hk', blockWord_getElem, if_neg (by omega)]

/-- `Statement:` `bitAt` is primitive recursive; the same proof sits inline in `champ_primrec`
(`ZeroParadox/Information/Disjunctive.lean`). -/
theorem bitAt_primrec : Primrec (fun p : ℕ × ℕ => bitAt p.1 p.2) := by
  have hit : Primrec (fun p : ℕ × ℕ => (fun m => m / 2)^[p.2] p.1) :=
    Primrec.nat_iterate Primrec.snd Primrec.fst
      (Primrec.nat_div.comp₂ Primrec₂.right (Primrec₂.const 2))
  exact (Primrec.beq.comp (Primrec.nat_mod.comp hit (Primrec.const 2)) (Primrec.const 1)).of_eq
    fun _ => rfl

theorem blockWord_primrec (b : Bool) :
    Primrec (fun q : ℕ × ℕ × ℕ => blockWord b q.1 q.2.1 q.2.2) := by
  have h1 : Primrec (fun q : ℕ × ℕ × ℕ => (List.range q.1).map (bitAt q.2.2)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst)
      (bitAt_primrec.comp (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)).to₂
  have h2 : Primrec (fun q : ℕ × ℕ × ℕ => (List.range q.2.1).map (fun _ => b)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd)) (Primrec₂.const b)
  exact (Primrec.list_append.comp h1 h2).of_eq fun _ => rfl

/-- `Statement:` a constant-block family indexed by a primitive recursive `f` is listed as unions
of prefix cylinders by a computable `g`. -/
theorem constBlock_presented (b : Bool) (f : ℕ → ℕ × ℕ) (hf : Primrec f) :
    ∃ g : ℕ × ℕ → Option (List Bool), Computable g ∧
      ∀ m, constBlock b (f m).1 (f m).2 = ⋃ j, ⋃ l ∈ g (m, j), prefixCyl l := by
  refine ⟨fun q => some (blockWord b (f q.1).1 (f q.1).2 q.2), ?_, fun m => ?_⟩
  · have hq : Primrec (fun q : ℕ × ℕ => ((f q.1).1, (f q.1).2, q.2)) :=
      Primrec.pair (Primrec.fst.comp (hf.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp (hf.comp Primrec.fst)) Primrec.snd)
    have hw : Primrec (fun q : ℕ × ℕ => blockWord b (f q.1).1 (f q.1).2 q.2) :=
      (blockWord_primrec b).comp hq
    have hs : Primrec (fun q : ℕ × ℕ => (some (blockWord b (f q.1).1 (f q.1).2 q.2) :
        Option (List Bool))) := Primrec.option_some.comp hw
    exact hs.to_comp
  · rw [constBlock_eq_iUnion]
    simp

/-- `Statement:` every zero-block test for `μ` is a Martin-Löf test for `μ`. -/
theorem zeroBlockTest_isMLTest {μ : Measure (ℕ → Bool)} {U : ℕ → Set (ℕ → Bool)}
    (hU : ZeroBlockTest μ U) : MLTest μ U := by
  obtain ⟨hμ, f, hf, hUf⟩ := hU
  obtain ⟨g, hg, hgf⟩ := constBlock_presented false f hf
  exact ⟨hμ, g, hg, fun m => by rw [hUf m, zeroBlock_eq_constBlock, hgf m]⟩

/-- `Statement:` Martin-Löf random for `trials p hp` implies zero-block typical. One way. -/
theorem zeroBlockTypical_of_MLRandom (p : NNReal) (hp : p ≤ 1) (w : ℕ → Bool)
    (h : MLRandom (trials p hp) w) : ZeroBlockTypical p hp w :=
  fun U hU => h U (zeroBlockTest_isMLTest hU)

/-- `Statement:` `snap_of_two_requirements` with zero-block typical replaced by Martin-Löf random
for `trials p hp`, `0 < p`. One way. `Reading:` the randomness is a hypothesis on one tape; no tape
is named, and ⊥ of `L` is not claimed random. -/
theorem snap_of_firstStep_MLRandom {L : Type*} [ZPSemilattice L] (hR1 : BotHasFirstStep L)
    (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (w : ℕ → Bool) (hML : MLRandom (trials p hp) w) :
    ∃ (φ : Bool → L) (hw : ∃ k, w k = true),
      let S := φ ∘ firedRun w hw
      (S 0 = bot ∧ S 1 ≠ S 0 ∧ IsStateSequence S) ∧
      ((S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ join (S 0) (S 1) = S 1) ∧
        letI := zpSemilatticeSup L; (bot : L) ⋖ S 1) :=
  snap_of_two_requirements hR1 p hp hp0 w (zeroBlockTypical_of_MLRandom p hp w hML)

/-- `Statement:` a constant block of length `n` has measure `p ^ n` if `b = true`, and
`(1 - p) ^ n` if `b = false`. -/
theorem trials_constBlock (p : NNReal) (hp : p ≤ 1) (b : Bool) (N n : ℕ) :
    trials p hp (constBlock b N n) =
      (if b then (p : ENNReal) else ((1 - p : NNReal) : ENNReal)) ^ n := by
  have : constBlock b N n = (↑(Finset.Ico N (N + n)) : Set ℕ).pi (fun _ => ({b} : Set Bool)) := by
    ext w; simp [constBlock]
  rw [this, trials, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton b)]
  cases b <;> simp [PMF.bernoulli]

-- Statement: CONTROL, the converse fails: at `p = 1/2` the all-`true` tape is zero-block typical and
-- not Martin-Löf random (level `m` the cylinder of `m` trues, measure `2⁻ᵐ`).
example : ZeroBlockTypical (1/2) (by norm_num) (fun _ => true) ∧
    ¬ MLRandom (trials (1/2) (by norm_num)) (fun _ => true) := by
  refine ⟨allTrue_zeroBlockTypical _ _, fun h => ?_⟩
  obtain ⟨g, hg, hgf⟩ := constBlock_presented true (fun m => (0, m))
    (Primrec.pair (Primrec.const 0) Primrec.id)
  refine h (fun m => constBlock true 0 m) ⟨fun m => ?_, g, hg, hgf⟩ ?_
  · rw [trials_constBlock]; simp
  · simp [constBlock]

/-- `Statement:` the level sets listed by `g`. -/
def levelOf (g : ℕ × ℕ → Option (List Bool)) (m : ℕ) : Set (ℕ → Bool) :=
  ⋃ j, ⋃ l ∈ g (m, j), prefixCyl l

/-- `Statement:` the computable listings `ℕ × ℕ → Option (List Bool)` form a countable type. -/
theorem countable_computable_enum :
    Countable {g : ℕ × ℕ → Option (List Bool) // Computable g} := by
  let F : {g : ℕ × ℕ → Option (List Bool) // Computable g} → {f : ℕ → ℕ // Computable f} :=
    fun g => ⟨fun n => Encodable.encode (g.1 (Denumerable.ofNat (ℕ × ℕ) n)),
      Computable.encode.comp (g.2.comp (Primrec.ofNat (ℕ × ℕ)).to_comp)⟩
  refine Function.Injective.countable (f := F) ?_
  rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
  apply Subtype.ext
  funext q
  have := congrFun (congrArg Subtype.val h) (Encodable.encode q)
  simp only [F, Denumerable.ofNat_encode] at this
  exact Encodable.encode_injective this

/-- `Statement:` if `μ (U m) ≤ 2⁻ᵐ` for every `m`, then `⋂ m, U m` is `μ`-null. -/
theorem measure_iInter_le_pow_zero (μ : Measure (ℕ → Bool)) (U : ℕ → Set (ℕ → Bool))
    (h : ∀ m, μ (U m) ≤ 2⁻¹ ^ m) : μ (⋂ m, U m) = 0 := by
  refine le_antisymm ?_ (zero_le _)
  have ht : Tendsto (fun m : ℕ => (2⁻¹ : ENNReal) ^ m) atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  exact ge_of_tendsto' ht fun m => (measure_mono (Set.iInter_subset _ m)).trans (h m)

/-- `Statement:` for every measure `μ` on tapes, `μ`-almost every tape is Martin-Löf random for `μ`:
the others lie in a countable union of null sets, one per computable listing. -/
theorem mlRandom_ae (μ : Measure (ℕ → Bool)) : ∀ᵐ w ∂μ, MLRandom μ w := by
  classical
  haveI := countable_computable_enum
  let bad : {g : ℕ × ℕ → Option (List Bool) // Computable g} → Set (ℕ → Bool) := fun g =>
    if ∀ m, μ (levelOf g.1 m) ≤ 2⁻¹ ^ m then ⋂ m, levelOf g.1 m else ∅
  have hnull : μ (⋃ g, bad g) = 0 := by
    refine measure_iUnion_null fun g => ?_
    simp only [bad]
    split_ifs with h
    · exact measure_iInter_le_pow_zero μ _ h
    · exact measure_empty
  rw [ae_iff]
  refine measure_mono_null (fun w hw => ?_) hnull
  simp only [MLRandom, AvoidsTests, Set.mem_setOf_eq, not_forall, not_not] at hw
  obtain ⟨U, ⟨hμ, g, hg, hU⟩, hmem⟩ := hw
  have hUl : U = levelOf g := funext hU
  subst hUl
  refine Set.mem_iUnion.2 ⟨⟨g, hg⟩, ?_⟩
  simp only [bad, if_pos hμ]
  exact hmem

/-- `Statement:` for every `p ≤ 1` some tape is Martin-Löf random for `trials p hp`; it names none. -/
theorem exists_MLRandom (p : NNReal) (hp : p ≤ 1) : ∃ w, MLRandom (trials p hp) w :=
  (mlRandom_ae (trials p hp)).exists

/-! ## § III. Frequency of `true` tending to `p` (the strong law of large numbers)

Per tape: the fraction of `true` among the first `n` stages tends to `p`. That a Martin-Löf random
tape has this property is not proved here. -/

section Frequency

open Finset

/-- `Statement:` the `ℝ`-valued indicator of `true` at stage `i`. -/
def tapeInd (w : ℕ → Bool) (i : ℕ) : ℝ := if w i then 1 else 0

/-- `Statement:` the frequency of `true` among the first `n` stages. -/
noncomputable def trueFreq (w : ℕ → Bool) (n : ℕ) : ℝ := (∑ i ∈ range n, tapeInd w i) / n

/-- `Statement:` the frequency of `true` on `w` tends to `p`. -/
def FreqBalanced (p : ℝ) (w : ℕ → Bool) : Prop := Tendsto (trueFreq w) atTop (nhds p)

theorem tapeInd_measurable (i : ℕ) : Measurable (fun w : ℕ → Bool => tapeInd w i) :=
  (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp (measurable_pi_apply i)

/-- `Statement:` `trials p hp`-almost every tape is `FreqBalanced p`: Mathlib's strong law
(`strong_law_ae_real`) on the coordinate indicators. -/
theorem freqBalanced_ae (p : NNReal) (hp : p ≤ 1) : ∀ᵐ w ∂(trials p hp), FreqBalanced p w := by
  let f : Bool → ℝ := fun b => if b then 1 else 0
  have hf : Measurable f := measurable_of_countable f
  let X : ℕ → (ℕ → Bool) → ℝ := fun i w => tapeInd w i
  have hXm : ∀ i, Measurable (X i) := tapeInd_measurable
  have hint : Integrable (X 0) (trials p hp) := by
    refine Integrable.of_bound (C := 1) (hXm 0).aestronglyMeasurable (Eventually.of_forall ?_)
    intro w; simp only [X, tapeInd]; split_ifs <;> simp
  have hind : iIndepFun X (trials p hp) := (coords_iIndep p hp).comp (fun _ => f) (fun _ => hf)
  have hmap : ∀ i, Measure.map (X i) (trials p hp) =
      Measure.map f (PMF.bernoulli p hp).toMeasure := by
    intro i
    have : X i = f ∘ (fun w : ℕ → Bool => w i) := rfl
    rw [this, ← Measure.map_map hf (measurable_pi_apply i), trials, Measure.infinitePi_map_eval]
  have hident : ∀ i, IdentDistrib (X i) (X 0) (trials p hp) (trials p hp) := fun i =>
    ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, by rw [hmap i, hmap 0]⟩
  have hE : ∫ w, X 0 w ∂(trials p hp) = p := by
    calc ∫ w, X 0 w ∂(trials p hp) = ∫ w, f (w 0) ∂(trials p hp) := rfl
      _ = ∫ b, f b ∂(Measure.map (fun w : ℕ → Bool => w 0) (trials p hp)) :=
          (integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable).symm
      _ = ∫ b, f b ∂((PMF.bernoulli p hp).toMeasure) := by
          rw [trials, Measure.infinitePi_map_eval]
      _ = p := by
          rw [integral_fintype (Integrable.of_finite)]
          simp [f, PMF.bernoulli, Measure.real]
  have := strong_law_ae_real X hint (fun i j hij => hind.indepFun hij) hident
  filter_upwards [this] with w hw
  rw [hE] at hw
  exact hw

/-- `Statement:` if `0 < p` and `w` is `FreqBalanced p`, then `w` fires infinitely often: a tape
silent from `N` has frequency at most `N / n`, which tends to 0. One way. -/
theorem fires_io_of_freqBalanced {p : ℝ} (hp0 : 0 < p) (w : ℕ → Bool) (hb : FreqBalanced p w) :
    w ∈ Filter.limsup fires Filter.atTop := by
  by_contra h
  obtain ⟨N, hN⟩ := (not_mem_limsup_fires_iff w).1 h
  have hle : ∀ n, ∑ i ∈ range n, tapeInd w i ≤ N := by
    intro n
    calc ∑ i ∈ range n, tapeInd w i ≤ ∑ i ∈ range n, (if i < N then (1 : ℝ) else 0) := by
          refine sum_le_sum fun i _ => ?_
          simp only [tapeInd]
          by_cases hi : i < N
          · rw [if_pos hi]; split_ifs <;> norm_num
          · rw [if_neg hi, hN i (not_lt.1 hi)]; simp
      _ = ((range n).filter (· < N)).card := by rw [sum_boole]
      _ ≤ N := by
          exact_mod_cast (card_le_card (fun i hi => by
            simp only [mem_filter] at hi; exact mem_range.2 hi.2)).trans (card_range N).le
  have hfreq : ∀ n, trueFreq w n ≤ (N : ℝ) / n := fun n =>
    div_le_div_of_nonneg_right (hle n) (Nat.cast_nonneg n)
  have h0 : Tendsto (fun n : ℕ => (N : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (N : ℝ)
  have : p ≤ 0 := le_of_tendsto_of_tendsto' hb h0 hfreq
  linarith

/-- `Statement:` `snap_of_two_requirements` with zero-block typical replaced by `FreqBalanced p`,
`0 < p`. One way. -/
theorem snap_of_firstStep_freqBalanced {L : Type*} [ZPSemilattice L] (hR1 : BotHasFirstStep L)
    {p : ℝ} (hp0 : 0 < p) (w : ℕ → Bool) (hb : FreqBalanced p w) :
    ∃ (φ : Bool → L) (hw : ∃ k, w k = true),
      let S := φ ∘ firedRun w hw
      (S 0 = bot ∧ S 1 ≠ S 0 ∧ IsStateSequence S) ∧
      ((S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ join (S 0) (S 1) = S 1) ∧
        letI := zpSemilatticeSup L; (bot : L) ⋖ S 1) := by
  obtain ⟨φ, h⟩ := snap_of_firstStep_fires_once hR1 w
    (fires_once_of_mem_limsup (fires_io_of_freqBalanced hp0 w hb))
  exact ⟨φ, _, h⟩

/-- `Statement:` the all-`true` tape has frequency 1 at every `n ≥ 1`. -/
theorem trueFreq_allTrue (n : ℕ) (hn : 0 < n) : trueFreq (fun _ => true) n = 1 := by
  simp only [trueFreq, tapeInd, if_true, sum_const, card_range, nsmul_eq_mul, mul_one]
  exact div_self (by exact_mod_cast hn.ne')

-- Statement: CONTROL, the all-`true` tape is `FreqBalanced p` for no `p < 1`.
example (p : ℝ) (hp : p < 1) : ¬ FreqBalanced p (fun _ => true) := by
  intro h
  have h1 : Tendsto (trueFreq (fun _ => true)) atTop (nhds 1) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn => (trueFreq_allTrue n hn).symm⟩)
  have := tendsto_nhds_unique h h1
  linarith

-- Statement: CONTROL, drop `0 < p`: the all-`false` tape is `FreqBalanced 0` and never fires.
example : FreqBalanced 0 (fun _ => false) ∧ ¬ ∃ k, (fun _ => false : ℕ → Bool) k = true := by
  refine ⟨?_, fun ⟨_, h⟩ => Bool.false_ne_true h⟩
  have : trueFreq (fun _ => false) = fun _ => 0 := by funext n; simp [trueFreq, tapeInd]
  rw [FreqBalanced, this]; exact tendsto_const_nhds

end Frequency

/-! ## § IV. Tape to real: binary expansion

`tapeReal w` is `0.w₀w₁w₂…` in base 2 (`Real.ofDigits`). How `trials p hp` pushes forward under it
is not stated here; `Mathlib/Analysis/Real/OfDigits.lean` has no measure statement (read 2026-11-06). -/

section TapeReal

open Finset

/-- `Statement:` bit `b` as a base-2 digit. -/
def bitDigit (b : Bool) : Fin 2 := if b then 1 else 0

/-- `Statement:` the real `0.w₀w₁w₂…` in base 2. -/
noncomputable def tapeReal (w : ℕ → Bool) : ℝ := Real.ofDigits (fun i => bitDigit (w i))

/-- `Statement:` the tape is eventually constant. -/
def EventuallyConstTape (w : ℕ → Bool) : Prop := ∃ N b, ∀ k, N ≤ k → w k = b

-- Statement: it is Mathlib's `Filter.EventuallyConst` at `atTop`.
example (w : ℕ → Bool) : EventuallyConstTape w ↔ Filter.EventuallyConst w Filter.atTop := by
  rw [Filter.eventuallyConst_atTop]
  constructor
  · rintro ⟨N, b, hb⟩; exact ⟨N, fun j hj => (hb j hj).trans (hb N le_rfl).symm⟩
  · rintro ⟨N, hN⟩; exact ⟨N, w N, hN⟩

/-- `Statement:` `x` is a non-negative dyadic rational `k / 2ⁿ`, `k n : ℕ`. -/
def IsDyadic (x : ℝ) : Prop := ∃ n k : ℕ, x = k / 2 ^ n

theorem fin2_val_le_one (d : Fin 2) : ((d : ℕ) : ℝ) ≤ 1 := by
  have := d.isLt; exact_mod_cast (by omega : (d : ℕ) ≤ 1)

/-- `Statement:` a base-2 expansion with a nonzero digit is positive. -/
theorem ofDigits_two_pos {d : ℕ → Fin 2} (h : ∃ i, d i ≠ 0) : 0 < Real.ofDigits d := by
  obtain ⟨i, hi⟩ := h
  have hdi : d i = 1 := by revert hi; generalize d i = x; fin_cases x <;> simp
  unfold Real.ofDigits
  refine Summable.tsum_pos Real.summable_ofDigitsTerm (fun _ => Real.ofDigitsTerm_nonneg) i ?_
  simp [Real.ofDigitsTerm, hdi]

/-- `Statement:` a base-2 expansion with a zero digit is less than 1. -/
theorem ofDigits_two_lt_one {d : ℕ → Fin 2} (h : ∃ i, d i = 0) : Real.ofDigits d < 1 := by
  obtain ⟨i, hi⟩ := h
  rw [← Real.ofDigits_const_last_eq_one 1]
  unfold Real.ofDigits
  refine Summable.tsum_lt_tsum (i := i) (fun j => ?_) ?_ Real.summable_ofDigitsTerm
    Real.summable_ofDigitsTerm
  · simp only [Real.ofDigitsTerm]
    gcongr
    simpa using fin2_val_le_one (d j)
  · simp [Real.ofDigitsTerm, hi]

/-- `Statement:` `2ⁿ` times the first `n` terms of a base-2 expansion is a natural number. -/
theorem ofDigits_two_partial_nat (d : ℕ → Fin 2) (n : ℕ) :
    ∃ m : ℕ, (2 : ℝ) ^ n * ∑ i ∈ range n, Real.ofDigitsTerm d i = m := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨2 * m + (d n : ℕ), ?_⟩
    rw [sum_range_succ, mul_add, pow_succ, mul_comm ((2 : ℝ) ^ n) 2, mul_assoc, hm]
    simp only [Real.ofDigitsTerm]
    push_cast
    have : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- `Statement:` a tape not eventually constant has, past every `n`, a `true` and a `false`. -/
theorem shift_of_not_eventuallyConst {w : ℕ → Bool} (h : ¬ EventuallyConstTape w) (n : ℕ) :
    (∃ i, bitDigit (w (i + n)) ≠ 0) ∧ (∃ i, bitDigit (w (i + n)) = 0) := by
  constructor
  · by_contra hc
    push Not at hc
    refine h ⟨n, false, fun k hk => ?_⟩
    have := hc (k - n)
    rw [Nat.sub_add_cancel hk] at this
    cases hw : w k <;> simp_all [bitDigit]
  · by_contra hc
    push Not at hc
    refine h ⟨n, true, fun k hk => ?_⟩
    have := hc (k - n)
    rw [Nat.sub_add_cancel hk] at this
    cases hw : w k <;> simp_all [bitDigit]

/-- `Statement:` a tape that is not eventually constant lands strictly inside (0, 1) at no dyadic
rational. The converse direction is `dyadic_of_eventuallyConst`. -/
theorem interior_of_not_eventuallyConst {w : ℕ → Bool} (h : ¬ EventuallyConstTape w) :
    0 < tapeReal w ∧ tapeReal w < 1 ∧ ¬ IsDyadic (tapeReal w) := by
  have h0 := shift_of_not_eventuallyConst h 0
  simp only [Nat.add_zero] at h0
  refine ⟨ofDigits_two_pos h0.1, ofDigits_two_lt_one h0.2, ?_⟩
  rintro ⟨n, k, hk⟩
  obtain ⟨m, hm⟩ := ofDigits_two_partial_nat (fun i => bitDigit (w i)) n
  have hn := shift_of_not_eventuallyConst h n
  have ht0 := ofDigits_two_pos hn.1
  have ht1 := ofDigits_two_lt_one hn.2
  have hdec := Real.ofDigits_eq_sum_add_ofDigits (fun i => bitDigit (w i)) n
  set t := Real.ofDigits (fun i => bitDigit (w (i + n)))
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hx : (2 : ℝ) ^ n * tapeReal w = m + t := by
    unfold tapeReal; rw [hdec, mul_add, hm]; push_cast
    rw [← mul_assoc, mul_inv_cancel₀ h2n.ne', one_mul]
  have hk' : (2 : ℝ) ^ n * tapeReal w = k := by rw [hk]; field_simp
  rw [hk'] at hx
  have a : (m : ℝ) < k := by linarith
  have b : (k : ℝ) < m + 1 := by linarith
  have a' : m < k := by exact_mod_cast a
  have b' : k < m + 1 := by exact_mod_cast b
  omega

/-- `Statement:` an eventually constant tape lands on a dyadic rational. -/
theorem dyadic_of_eventuallyConst {w : ℕ → Bool} (h : EventuallyConstTape w) :
    IsDyadic (tapeReal w) := by
  obtain ⟨N, b, hb⟩ := h
  obtain ⟨m, hm⟩ := ofDigits_two_partial_nat (fun i => bitDigit (w i)) N
  have hdec := Real.ofDigits_eq_sum_add_ofDigits (fun i => bitDigit (w i)) N
  have htail : Real.ofDigits (fun i => bitDigit (w (i + N))) = if b then 1 else 0 := by
    have hfun : (fun i => bitDigit (w (i + N))) = fun _ => bitDigit b :=
      funext fun i => by rw [hb (i + N) (Nat.le_add_left N i)]
    rw [hfun]
    cases b
    · simp [Real.ofDigits, Real.ofDigitsTerm, bitDigit]
    · exact Real.ofDigits_const_last_eq_one 1
  refine ⟨N, m + (if b then 1 else 0), ?_⟩
  have h2n : (0 : ℝ) < 2 ^ N := by positivity
  unfold tapeReal
  rw [hdec, htail]
  have hS : ∑ i ∈ range N, Real.ofDigitsTerm (fun i => bitDigit (w i)) i = m / 2 ^ N := by
    rw [eq_div_iff h2n.ne', mul_comm, hm]
  rw [hS]
  cases b <;> (push_cast; field_simp)

/-- `Statement:` `w` is not eventually constant iff `tapeReal w` is not a dyadic rational; both
directions. -/
theorem not_eventuallyConst_iff_not_dyadic (w : ℕ → Bool) :
    ¬ EventuallyConstTape w ↔ ¬ IsDyadic (tapeReal w) :=
  ⟨fun h => (interior_of_not_eventuallyConst h).2.2, fun h hc => h (dyadic_of_eventuallyConst hc)⟩

-- Reading: CARRIER. The tapes that settle land on the dyadic grid (a quantized set of values); the
-- tapes that never settle land off it, strictly inside (0, 1) of ℝ, where no point has a first step
-- (`no_firstStep_of_preconnected`). The first step of § I is asked of `L`, never of ℝ.

/-- `Statement:` for `0 < p < 1`, a Martin-Löf random tape for `trials p hp` is not eventually
constant: eventually `false` is caught by a zero-block test, eventually `true` by a one-block test. -/
theorem not_eventuallyConst_of_MLRandom (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (w : ℕ → Bool) (hML : MLRandom (trials p hp) w) : ¬ EventuallyConstTape w := by
  rintro ⟨N, b, hb⟩
  cases b with
  | false =>
    have hio := fires_io_of_avoids p hp hp0 _ (fun _ h => h) w
      (zeroBlockTypical_of_MLRandom p hp w hML)
    exact (not_mem_limsup_fires_iff w).2 ⟨N, hb⟩ hio
  | true =>
    have hq0 : 0 < (1 - p : NNReal) := tsub_pos_of_lt hp1
    obtain ⟨K, -, hK⟩ := exists_halving_block (1 - p) hq0
    rw [tsub_tsub_cancel_of_le hp] at hK
    obtain ⟨g, hg, hgf⟩ := constBlock_presented true (fun m => (N, K * m))
      (Primrec.pair (Primrec.const N) (Primrec.nat_mul.comp (Primrec.const K) Primrec.id))
    refine hML (fun m => constBlock true N (K * m)) ⟨fun m => ?_, g, hg, hgf⟩ ?_
    · rw [trials_constBlock, if_pos rfl, pow_mul]
      exact pow_le_pow_left₀ (zero_le _) hK m
    · simp only [Set.mem_iInter, constBlock, Set.mem_setOf_eq, Finset.mem_Ico]
      intro m k hk; exact hb k hk.1

/-- `Statement:` for `0 < p < 1`, a Martin-Löf random tape for `trials p hp` lands strictly inside
(0, 1), at no dyadic rational. -/
theorem interior_of_MLRandom (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (w : ℕ → Bool) (hML : MLRandom (trials p hp) w) :
    0 < tapeReal w ∧ tapeReal w < 1 ∧ ¬ IsDyadic (tapeReal w) :=
  interior_of_not_eventuallyConst (not_eventuallyConst_of_MLRandom p hp hp0 hp1 w hML)

-- Statement: CONTROL, the all-`false` and all-`true` tapes land on the endpoints 0 and 1.
example : tapeReal (fun _ => false) = 0 ∧ tapeReal (fun _ => true) = 1 := by
  refine ⟨by simp [tapeReal, Real.ofDigits, Real.ofDigitsTerm, bitDigit], ?_⟩
  exact Real.ofDigits_const_last_eq_one 1

-- Statement: CONTROL, `p < 1` is needed: at `p = 1` (the point mass on the all-`true` tape) the
-- all-`true` tape is Martin-Löf random for `trials 1`, eventually constant, and lands on 1.
example : MLRandom (trials 1 le_rfl) (fun _ => true) ∧ EventuallyConstTape (fun _ => true) ∧
    tapeReal (fun _ => true) = 1 := by
  refine ⟨?_, ⟨0, true, fun _ _ => rfl⟩, Real.ofDigits_const_last_eq_one 1⟩
  rintro U ⟨hμ, g, -, hU⟩ hmem
  have h1 : (fun _ => true : ℕ → Bool) ∈ U 1 := Set.mem_iInter.1 hmem 1
  rw [hU 1] at h1
  simp only [Set.mem_iUnion, exists_prop] at h1
  obtain ⟨j, l, hl, hx⟩ := h1
  have hsub : constBlock true 0 l.length ⊆ U 1 := by
    intro x hx'
    rw [hU 1]
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨j, l, hl, fun i hi => ?_⟩
    rw [← hx i hi]
    exact hx' i (by simp only [Finset.mem_Ico]; omega)
  have h2 := (measure_mono hsub).trans (hμ 1)
  rw [trials_constBlock, if_pos rfl] at h2
  norm_num at h2

-- Statement: CONTROL, inside (0, 1) and not dyadic does not need randomness: the computable
-- alternating tape lands there.
example : 0 < tapeReal (fun k => decide (k % 2 = 0)) ∧ tapeReal (fun k => decide (k % 2 = 0)) < 1 ∧
    ¬ IsDyadic (tapeReal (fun k => decide (k % 2 = 0))) := by
  refine interior_of_not_eventuallyConst ?_
  rintro ⟨N, b, hb⟩
  have h1 : decide ((2 * N) % 2 = 0) = b := hb (2 * N) (by omega)
  have h2 : decide ((2 * N + 1) % 2 = 0) = b := hb (2 * N + 1) (by omega)
  rw [decide_eq_true (by omega : (2 * N) % 2 = 0)] at h1
  rw [decide_eq_false (by omega : ¬ (2 * N + 1) % 2 = 0)] at h2
  exact Bool.false_ne_true (h2.trans h1.symm)

end TapeReal

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#print axioms BotHasFirstStep
#print axioms ZeroBlockTypical
#print axioms fires_once_of_mem_limsup
#print axioms snap_of_firstStep_fires_once
#print axioms snap_of_two_requirements
#print axioms hcov_iff_phi_cover
#print axioms botHasFirstStep_iff_exists_phi
#print axioms nnrealMaxZPS
#print axioms allTrue_zeroBlockTypical
#print axioms nnreal_zp_lt_iff
#print axioms nnreal_not_botHasFirstStep
#print axioms boolOrZPS
#print axioms bool_botHasFirstStep
#print axioms prefixCyl
#print axioms MLTest
#print axioms MLRandom
#print axioms constBlock
#print axioms zeroBlock_eq_constBlock
#print axioms blockWord
#print axioms blockWord_length
#print axioms blockWord_getElem
#print axioms constBlock_eq_iUnion
#print axioms bitAt_primrec
#print axioms blockWord_primrec
#print axioms constBlock_presented
#print axioms zeroBlockTest_isMLTest
#print axioms zeroBlockTypical_of_MLRandom
#print axioms snap_of_firstStep_MLRandom
#print axioms trials_constBlock
#print axioms levelOf
#print axioms countable_computable_enum
#print axioms measure_iInter_le_pow_zero
#print axioms mlRandom_ae
#print axioms exists_MLRandom
#print axioms tapeInd
#print axioms trueFreq
#print axioms FreqBalanced
#print axioms tapeInd_measurable
#print axioms freqBalanced_ae
#print axioms fires_io_of_freqBalanced
#print axioms snap_of_firstStep_freqBalanced
#print axioms trueFreq_allTrue
#print axioms bitDigit
#print axioms tapeReal
#print axioms EventuallyConstTape
#print axioms IsDyadic
#print axioms fin2_val_le_one
#print axioms ofDigits_two_pos
#print axioms ofDigits_two_lt_one
#print axioms ofDigits_two_partial_nat
#print axioms shift_of_not_eventuallyConst
#print axioms interior_of_not_eventuallyConst
#print axioms dyadic_of_eventuallyConst
#print axioms not_eventuallyConst_iff_not_dyadic
#print axioms not_eventuallyConst_of_MLRandom
#print axioms interior_of_MLRandom

end PurityCheck
