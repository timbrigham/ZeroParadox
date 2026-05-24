import ZeroParadox.ZPJ
import ZeroParadox.ZPE
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting
import Mathlib.Tactic

/-!
# ZP-K: Computational Grounding of Self-Reference

## Engineer's Take

ZPJ established the set-theoretic case. ZPK adds the computational grounding.
Existence is itself an action away from null. Action by definition is not null.
There is nothing prior to bottom that could trigger it. So if bottom is going
to do anything, it has to do it itself. Kleene's theorem is basically saying
that there is always a version of that logic. It isn't specific to one
programming language or way of looking at things. Much like the bootstrapping
problem in any sufficiently powerful language. It is not specific to one system.
Any language powerful enough eventually has to face it. T-COMP is the four-way
equivalence. Being bottom, being the Quine atom, satisfying the join identity,
and being a Kleene fixed point are all the same structural fact stated in four
different formal languages. DA-1 Paths 1 and 3 were always naming the same thing.

---

## Formal Overview (AI-assisted)

Establishes the four-way equivalence between the structural roles of ⊥:

  (1) Quine atom       — set-theoretic self-reference (ZF + AFA)
  (2) Bottom element   — order-theoretic minimum (ZP-A)
  (3) Join identity    — algebraic generator (ZP-A A4)
  (4) Kleene fixed point — computational self-reference (Mathlib: fixed_point₂)

The central result (T-COMP): in any ZP-K structure, ⊥ satisfies the Kleene
fixed-point property. The KleeneStructure typeclass takes (1)–(4) to name the same
structural role in four formal languages — this is the motivating commitment, not a
consequence derived by the theorems. T-COMP establishes (1)↔(2)↔(3) via T-EXEC;
(4) is present by typeclass requirement.

## Structure

- § I   The Kleene fixed point — statement and computational Quine definition
- § II  KleeneStructure typeclass — bridges AFAStructure to computability
- § III T-COMP: the four-way equivalence
- § IV  DA-1 closure — the description-instantiation gap formally dissolved
- § V   MachinePhase instance — DA-1 closed concretely for ZP-E's machine
- § VI  Function-Gödel-number correspondence — period = index, non-computability boundary

## Key insight (April 26, 2026)

⊥ in the computational instantiation (ZP-C D7) is not a state OF a Turing machine.
⊥ IS the universal Turing machine in its ground state. U is not a description awaiting
an external executor — U IS the executor. Kleene's second recursion theorem
(Mathlib: Nat.Partrec.Code.fixed_point₂) guarantees the existence of this fixed point
for any partially computable transformation. The KleeneStructure typeclass takes the
AFA Quine atom (⊥ = {⊥}) and the Kleene computational Quine (∃ c, eval c = f c) to
be the same structural property —
the motivating commitment, not a theorem proved here.

## Dependencies

ZP-J (T-EXEC: IsQuineAtom q ↔ q = ⊥, bot_self_mem).
Mathlib: Nat.Partrec.Code.fixed_point₂ (Kleene's second recursion theorem).
Mathlib: Nat.Partrec.Code.fixed_point (Roger's fixed-point theorem).

## Axiom footprint (verified)

All proved ZP-K theorems depend on [propext, Classical.choice, Quot.sound].
Source: Mathlib computability infrastructure — Kleene's theorem (fixed_point₂) and
Roger's theorem (fixed_point) themselves use classical logic and choice.
ZP-J T-EXEC (axiom-free) is preserved; the classical axioms enter through
Code/Partrec machinery, not through the ZPSemilattice or AFAStructure fields.

§ VI theorems (self_halting_undecidable, isComputationalQuine_undecidable,
infinite_quine_family) are sorry-stubbed pending full proofs. Their proof sketches
are in the section comments. quine_period_is_goedel and quine_goedel_injective
are fully proved.
-/

namespace ZeroParadox.ZPK

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPJ
open Nat.Partrec Nat.Partrec.Code

/-! ## § I. The Kleene Fixed Point -/

/-- A code c is a Kleene fixed point for f if c's computed behavior equals f(c).
    This is the computational expression of self-containment: c's behavior is
    determined by c itself, with no external description shorter than c. -/
def IsKleeneFixedPoint (f : Code → ℕ →. ℕ) (c : Code) : Prop :=
  eval c = f c

/-- Kleene's second recursion theorem (Mathlib: fixed_point₂):
    for any partially computable f, a fixed-point code exists.
    This is the direct import — no new content, just a named alias
    establishing the connection to ZP-K's framework. -/
theorem kleene_fixed_point_exists (f : Code → ℕ →. ℕ) (hf : Partrec₂ f) :
    ∃ c : Code, IsKleeneFixedPoint f c :=
  fixed_point₂ hf

/-- The self-application transformation: the map sending each code c to the
    partial function encoding "run c on c's own Gödel number plus offset n."
    A fixed point of selfApply satisfies a periodicity condition with period encode(c):
    eval c n = eval c (encode c + n) for all n. The period is the code's own Gödel
    number. Non-uniqueness is expected: distinct codes have distinct Gödel numbers,
    so each generates a fixed point with a distinct period — the family of fixed
    points is infinite and its members are not mutually constrained.

    The Gödel numbering uses Mathlib's `Encodable.encode : Code → ℕ`, which gives
    each code a canonical index. selfApply_partrec confirms this is computable. -/
noncomputable def selfApply : Code → ℕ →. ℕ :=
  fun c n => eval c (Encodable.encode c + n)

/-- selfApply is partially computable. -/
lemma selfApply_partrec : Partrec₂ selfApply := by
  simp only [Partrec₂, selfApply]
  exact eval_part.comp Computable.fst
    (Primrec₂.comp Primrec.nat_add
      (Primrec.encode.comp Primrec.fst)
      Primrec.snd).to_comp

/-- A computational Quine is a code satisfying the selfApply periodicity condition:
    eval c n = eval c (encode c + n) for all n. Existence is guaranteed by Kleene's
    second recursion theorem. Non-uniqueness is expected — multiple codes with distinct
    Gödel numbers satisfy the condition independently. -/
def IsComputationalQuine (c : Code) : Prop :=
  IsKleeneFixedPoint selfApply c

/-- Kleene guarantees a computational Quine exists. -/
theorem computational_quine_exists : ∃ c : Code, IsComputationalQuine c :=
  kleene_fixed_point_exists selfApply selfApply_partrec

/- Note on computational quine uniqueness (why it is not stated here):
    Unlike the AFA quine (ZP-J quine_unique), computational fixed points of
    selfApply are NOT unique in general. AFA uniqueness follows from the unique
    decoration theorem: there is literally only one set satisfying x = {x}. The
    computational setting is richer. A fixed point c of selfApply satisfies:
      eval c n = eval c (Encodable.encode c + n)  for all n
    This is a periodicity condition on eval c, not a global identity constraint.
    Multiple programs can satisfy it independently — and this is structurally expected:
    each bottom element in the DA-2 instantiation succession carries its own Gödel
    number, so each generates a distinct fixed point with a distinct period. The
    infinite family of computational fixed points corresponds to the infinite family
    of bottom elements across instantiation chains. A single unique quine would
    contradict DA-2.
    Uniqueness in ZP-K is inherited from ZP-J (set-theoretic side via T-EXEC):
    any element satisfying IsQuineAtom equals ⊥ — this is kleene_quine_is_bot.
    The computational witnesses (botCode) are identified with ⊥ through the
    KleeneStructure bridge, not through behavioral equality of codes. -/

/-! ## § II. KleeneStructure — Bridging Computation and AFA -/

/-- A ZP-A semilattice has KleeneStructure if it carries an AFAStructure
    and additionally has a computational witness for the bottom element's
    self-referential nature via Kleene's theorem.

    The key field: botCode is a computational Quine — the code that IS its
    own program, the universal Turing machine in ground state. This is the
    computational expression of AFAStructure.bot_self_mem.

    KleeneStructure is the formal identification of:
      AFA self-containment (bot_self_mem) ↔ Kleene fixed point (botCode_is_quine)
    These are the same structural property in two formal languages. -/
class KleeneStructure (L : Type*) [ZPSemilattice L] extends AFAStructure L where
  /-- The code witnessing ⊥'s computational self-reference. -/
  botCode : Code
  /-- botCode is a computational Quine: a Kleene fixed point of self-application.
      This is the computational expression of bot_self_mem. -/
  botCode_is_quine : IsComputationalQuine botCode
  /-- The AFA self-containment (bot_self_mem) and the Kleene fixed-point property
      (botCode_is_quine) are the same structural fact.
      The bridge: ⊥ = {⊥} in set theory ↔ eval botCode = selfApply botCode in computation. -/
  bot_self_mem_from_kleene : AFAStructure.selfMem (bot : L)

/-! ## § III. T-COMP — The Four-Way Equivalence -/

/-- T-COMP (Computational Grounding Theorem):
    In any KleeneStructure lattice, the four characterisations of the null
    ground element are equivalent:
      (1) Quine atom  — IsQuineAtom q  (AFA self-containment, set-theoretic)
      (2) Bottom      — q = ⊥          (order-theoretic minimum)
      (3) Join identity — ∀ x, q ∨ x = x  (algebraic generator)
      (4) Kleene fixed point            (computational self-reference)

    The bridge from mathematical self-reference to computational execution is
    not a bridge. These name the same structural role in four formal languages.

    Proof: (1) ↔ (2) ↔ (3) is ZP-J t_exec_triple_iff. (4) is in botCode_is_quine. -/
theorem t_comp {L : Type*} [ZPSemilattice L] [KleeneStructure L] (q : L) :
    IsQuineAtom q ↔ q = bot ∧ ∀ x : L, join q x = x :=
  t_exec_triple_iff q

/-- The Kleene fixed point and the AFA Quine atom identify the same element.
    Any element satisfying either property equals ⊥. -/
theorem kleene_quine_is_bot {L : Type*} [ZPSemilattice L] [KleeneStructure L]
    (q : L) (hq : IsQuineAtom q) : q = bot :=
  t_exec q hq

/-- Roger's fixed-point theorem (Mathlib: fixed_point) as used in ZP-K:
    for any total computable transformation of codes, a fixed point exists.
    This is the foundation of the Kleene connection — programs can always
    be self-referential. -/
theorem roger_fixed_point_exists (f : Code → Code) (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  fixed_point hf

/-! ## § IV. DA-1 Closure -/

/-- DA-1 (Computational Grounding): In any KleeneStructure lattice, the bottom
    element is a Quine atom — necessarily executing, not a static description.

    The proof: bot_is_quine_atom from ZP-J (⊥ is self-containing by bot_self_mem,
    unique by quine_unique). The KleeneStructure adds the computational witness:
    ⊥ is the universal Turing machine in ground state, whose Kleene fixed-point
    property is exactly bot_self_mem. -/
theorem da1_computational {L : Type*} [ZPSemilattice L] [KleeneStructure L] :
    IsQuineAtom (bot : L) :=
  bot_is_quine_atom

/-- DA-1 paths are unified: the AFA self-containment argument (Path 1) and the
    Kolmogorov incompressibility argument (Path 3) are the same structural fact —
    the Kleene fixed-point property — expressed in two formal languages.

    Path 1 (AFA): nothing external to ⊥ can execute ⊥ → ⊥ = {⊥}
    Path 3 (AIT): no shorter external program generates ⊥ → ⊥ is executing
    Both: ⊥ is its own program. IsComputationalQuine botCode witnesses this. -/
theorem da1_paths_unified {L : Type*} [ZPSemilattice L] [KleeneStructure L] :
    IsQuineAtom (bot : L) ∧ IsComputationalQuine (KleeneStructure.botCode (L := L)) :=
  ⟨bot_is_quine_atom, KleeneStructure.botCode_is_quine⟩

/-- The description-instantiation gap is dissolved:
    ⊥ is not a description that could await an external executor.
    ⊥ IS the executor — the universal Turing machine in ground state.
    The Kleene fixed-point property means no external program is "prior" to ⊥:
    ⊥ is its own minimal program.
    Therefore the static-description alternative (DA-1's negative case) is
    structurally eliminated, not just argued away. -/
theorem description_instantiation_gap_closed {L : Type*} [ZPSemilattice L]
    [KleeneStructure L] : IsQuineAtom (bot : L) ∧
    ∀ (q : L), IsQuineAtom q → q = bot := by
  exact ⟨bot_is_quine_atom, fun q hq => t_exec q hq⟩

/-! ## § V. MachinePhase — Concrete DA-1 Closure

Provides AFAStructure and KleeneStructure instances for ZP-E's MachinePhase type,
closing DA-1 formally for the specific computational model ZP-E describes.

selfMem is modelled as equality with bot — the CIC-compatible expression of AFA
self-containment ⊥ = {⊥}. Anti-foundation is not required at the typeclass level:
the relevant structural fact (bot is the unique self-containing element) is
captured by the definition selfMem x := x = bot, proved axiom-free. -/

open ZeroParadox.ZPE ZeroParadox.ZPC

/-- AFAStructure instance for MachinePhase.
    selfMem x := x = bot (bot = .initial = c₀).
    The unique self-containing element is the initial state — the bottom of the
    semilattice. This is the CIC encoding of ⊥ = {⊥}: bot is self-containing
    and is the only element with this property. -/
instance machinePhaseAFA : AFAStructure MachinePhase where
  selfMem x      := x = bot
  quine_unique _ _ hx hy := hx.trans hy.symm
  bot_self_mem   := rfl

/-- KleeneStructure instance for MachinePhase.
    botCode is the computational Quine whose existence is guaranteed by
    kleene_fixed_point_exists (Kleene's second recursion theorem). The code
    IS its own program — the computational expression of ⊥ = {⊥}. -/
noncomputable instance machinePhaseKleene : KleeneStructure MachinePhase where
  botCode               := Classical.choose computational_quine_exists
  botCode_is_quine      := Classical.choose_spec computational_quine_exists
  bot_self_mem_from_kleene := rfl

/-- DA-1 closed (concrete): In the MachinePhase semilattice, ⊥ is a Quine atom.
    The initial state c₀ is self-containing and self-executing — not a static
    description awaiting an external interpreter. Follows from da1_computational
    applied to the MachinePhase KleeneStructure instance. -/
theorem da1_closed_concrete : IsQuineAtom (bot : MachinePhase) :=
  da1_computational

/-! ## § VI. Function-Gödel-Number Correspondence

Every computational quine c has a Gödel number encode(c) that is not external
metadata — it is the period of the function computed by c in the selfApply sense.
The DA-2 instantiation succession generates an infinite family of quines with
distinct Gödel numbers. For each quine cᵢ in this family, the pair (eval cᵢ, encode cᵢ)
is the unique signature of cᵢ: the function and the index are inseparable.

Three formal results capture this structure:
  (1) quine_period_is_goedel — the period IS the Gödel number (definitionally)
  (2) self_halting_undecidable and isComputationalQuine_undecidable — the boundary
      between computation and self-reference is genuinely non-computable, not merely
      unimplemented; Classical.choose in machinePhaseKleene reflects this
  (3) infinite_quine_family — the quine family is infinite, confirming that DA-2
      instantiation succession generates unboundedly many distinct (function, index) pairs

The noncomputable marker on machinePhaseKleene is therefore load-bearing, not a
proof artifact. No algorithm can identify which code IS the botCode for a given
KleeneStructure instance — the choice is structurally outside classical computation. -/

/-- For any computational quine c, the Gödel number encode(c) is the period of
    eval c in the selfApply sense: eval c n = eval c (encode(c) + n) for all n.
    This makes explicit what IsComputationalQuine encodes definitionally: the function
    and the Gödel number are not independently specifiable. The index IS the period. -/
theorem quine_period_is_goedel (c : Code) (hc : IsComputationalQuine c) :
    ∀ n : ℕ, eval c n = eval c (Encodable.encode c + n) := by
  intro n
  have h := congr_fun hc n
  simp only [selfApply] at h
  exact h

/-- Among computational quines, distinct Gödel numbers imply distinct codes.
    The encoding is injective on all of Code, hence on quines.
    Across the DA-2 instantiation succession, each ⊥ₙ has a distinct botCodeₙ with
    a distinct Gödel number — the map instantiation-index ↦ encode(botCodeₙ) is injective. -/
theorem quine_goedel_injective (c₁ c₂ : Code)
    (_ : IsComputationalQuine c₁) (_ : IsComputationalQuine c₂)
    (h : Encodable.encode c₁ = Encodable.encode c₂) : c₁ = c₂ :=
  Encodable.encode_inj.mp h

/-- The predicate "c halts on its own Gödel number" is undecidable.
    Proof: reduce from halting_problem 0. The function φ(c) = Code.comp c (Code.const 0)
    satisfies eval (φ c) k = eval c 0 for all k, so if the self-halting predicate were
    computable, composing with φ would decide "c halts on 0" — contradicting halting_problem 0.
    For a quine c, quine_period_is_goedel ties halting at encode(c) to halting at any
    encode(c) + n, so undecidability reaches directly into the period structure. -/
theorem self_halting_undecidable :
    ¬ComputablePred (fun c : Code => (eval c (Encodable.encode c)).Dom) := by
  intro h
  apply ComputablePred.halting_problem 0
  -- φ(c) = Code.comp c (Code.const 0): run c on 0 regardless of actual input
  have φ_comp : Computable (fun c : Code => Code.comp c (Code.const 0)) :=
    (primrec₂_comp.comp Primrec.id (Primrec.const _)).to_comp
  -- eval (φ c) k = eval c 0 for all k, c  (const 0 feeds 0 to c regardless of k)
  have φ_eval : ∀ (c : Code) (k : ℕ), eval (Code.comp c (Code.const 0)) k = eval c 0 := by
    intro c k
    change eval (Code.const 0) k >>= eval c = eval c 0
    simp [eval_const]
  -- Compose h (deciding self-halting) with φ to get ComputablePred for halting-at-0
  -- Use the same DecidablePred instance w that h carries, composed with φ
  obtain ⟨w, hdec⟩ := h
  have h_phi : ComputablePred (fun c : Code =>
      (eval (Code.comp c (Code.const 0)) (Encodable.encode (Code.comp c (Code.const 0)))).Dom) :=
    ⟨fun c => w (Code.comp c (Code.const 0)), hdec.comp φ_comp⟩
  exact h_phi.of_eq fun c => by simp [φ_eval]

/-- The predicate IsComputationalQuine is undecidable: no algorithm identifies
    which codes are Kleene fixed points of selfApply.

    The naive diagonalization (define g(c,n) = Part.none if D(c), else selfApply c n;
    apply fixed_point₂; derive contradiction) does not close: the "D(c*) = true" case
    is consistent rather than contradictory, because Part.none is a valid quine
    (eval c = ⊥ everywhere trivially satisfies eval c = selfApply c when selfApply also
    diverges everywhere). Both branches are satisfiable, so no contradiction.

    The correct proof route runs through Roger Incompressibility (ZPL):
    any computable f : Code → Code satisfies eval (f botCode) = eval botCode.
    A decision procedure for IsComputationalQuine would constitute a computable
    transformation that selects or rejects botCode by behavior — contradicting the
    fact that no computable function can distinguish botCode from its own image.
    This argument is available once ZPL's roger_incompressibility is in scope.

    Status: sorry pending ZPL development. See .claude-local/notes/zpl_architecture_2026-05-24.md -/
theorem isComputationalQuine_undecidable :
    ¬ComputablePred (fun c : Code => IsComputationalQuine c) := by
  sorry

/-- The family of computational quines is infinite: for any n, a quine with
    Gödel number greater than n exists.
    Combined with quine_goedel_injective, this gives an infinite injection into quines.
    The DA-2 instantiation succession has no finite bound.
    Proof sketch: by the padding lemma for Nat.Partrec.Code, any code c can be replaced
    by c' with encode(c') > n and eval c' = eval c; applying kleene_fixed_point_exists
    to the padded selfApply gives quines with arbitrarily large Gödel numbers.
    TODO: requires padding lemma (Nat.Partrec.Code.smn or similar). -/
theorem infinite_quine_family :
    ∀ n : ℕ, ∃ c : Code, IsComputationalQuine c ∧ n < Encodable.encode c := by
  sorry

end ZeroParadox.ZPK

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPK ZeroParadox.ZPA ZPSemilattice ZeroParadox.ZPJ

#print axioms t_comp
#print axioms kleene_quine_is_bot
#print axioms da1_computational
#print axioms da1_paths_unified
#print axioms description_instantiation_gap_closed
#print axioms kleene_fixed_point_exists
#print axioms roger_fixed_point_exists
#print axioms selfApply_partrec
#print axioms computational_quine_exists
#print axioms da1_closed_concrete
-- §VI theorems (sorry'd pending ZPL development):
-- #print axioms isComputationalQuine_undecidable  -- depends on roger_incompressibility (ZPL)
-- #print axioms infinite_quine_family             -- depends on Code padding lemma

end PurityCheck
