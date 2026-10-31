import ZeroParadox.Computability.KleeneChoiceFree
import ZeroParadox.Computability.Kleene
import Mathlib.Computability.PartrecCode
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# A universal code for `Nat.Partrec.Code`, choice-free

## Engineer's Take

"a new dedicated question regarding the position of choice at a project-wide level for us" went up
as Discussion #142: is there a universal code for Mathlib's `Code` whose correctness proof needs no
`Classical.choice`? "I could see building that just as part of our research process", and this file
is that build. "The project has pivoted hard to being code first", and so the answer is a proof, not
a paragraph.

---

## Formal Overview (AI-assisted)
`Statement:` `universal_code_cf : ∃ u : Code, ∀ d n, eval u (Nat.pair (encodeCode d) n) = eval d n`,
with `u` not an explicit term; not the `Partrec₂` form `eval_part`. § IX: a code both self-printing
and universal, `selfref_universal_exists_cf`. Footprints: `PurityCheck`.
-/

namespace ZeroParadox

open Nat.Partrec Nat.Partrec.Code

/-! ## § I. A small-step machine for `Code`

Reading (cited, not claimed): the route is Kleene's normal form theorem, the textbook one. Mathlib
builds its universal function by the same theorem through fuelled evaluation `evaln`: Carneiro,
"Formalizing computability theory via partial recursive functions", ITP 2019, LIPIcs 141, paper 12,
doi 10.4230/LIPIcs.ITP.2019.12, § 5.2, p. 12:12, "This is Kleene's normal form theorem (in a
different language) – eval is a universal partial recursive function." Here the iterated function is
a one-step machine instead of `evaln`. -/

-- Reading (cited, not claimed): continuations plus a step on configurations is the design of
-- Mathlib's `Turing.ToPartrec` (`Mathlib/Computability/TuringMachine/Config.lean`: `Cont`, `Cfg`,
-- `stepNormal`, `stepRet`) for its list-valued `Code`; here an explicit `ev` state keeps `codeStep`
-- non-recursive. The whole route (a step machine encoded in ℕ, its step primitive recursive, then
-- iterated and searched) is F. J. Balbach, "Some classical results in inductive inference of
-- recursive functions", Archive of Formal Proofs (2020), entry `Inductive_Inference`
-- (https://www.isa-afp.org/entries/Inductive_Inference.html), theory `Universal`, § 1.5, in
-- classical Isabelle/HOL. Constructive universal functions exist in Coq, where no global choice
-- operator (no classical axiom) is available unless one is declared: Forster and Kunze, "A
-- certifying extraction with time bounds from Coq to call-by-value λ-calculus", arXiv 1904.11818,
-- a universal L-term extracted from a step-indexed self-interpreter. Carneiro, p. 12:15, on
-- Mathlib's development: "there was no particular reason to assume LEM except in Theorem 5".
-- This file adds the measurement on Mathlib's `Code`.

/-- `Statement:` continuations of the machine: halt, the two halves of `pair`, `comp`, a `prec`
loop with `r` steps left, an `rfind'` search at index `m`. -/
inductive CodeCont
  | halt
  | pairL (cg : Code) (n : ℕ) (k : CodeCont)
  | pairR (a : ℕ) (k : CodeCont)
  | compK (cf : Code) (k : CodeCont)
  | precK (cg : Code) (a y r : ℕ) (k : CodeCont)
  | rfindK (cf : Code) (a m : ℕ) (k : CodeCont)

/-- `Statement:` machine states: evaluate `c` on `n` under `k`, return `v` to `k`, or halted. -/
inductive CodeState
  | ev (c : Code) (n : ℕ) (k : CodeCont)
  | ret (v : ℕ) (k : CodeCont)
  | done (v : ℕ)

/-- `Statement:` one machine step; no case recurses. -/
def codeStep : CodeState → CodeState
  | .ev .zero _ k => .ret 0 k
  | .ev .succ n k => .ret (n + 1) k
  | .ev .left n k => .ret n.unpair.1 k
  | .ev .right n k => .ret n.unpair.2 k
  | .ev (.pair f g) n k => .ev f n (.pairL g n k)
  | .ev (.comp f g) n k => .ev g n (.compK f k)
  | .ev (.prec f g) n k => .ev f n.unpair.1 (.precK g n.unpair.1 0 n.unpair.2 k)
  | .ev (.rfind' f) n k =>
      .ev f (Nat.pair n.unpair.1 n.unpair.2) (.rfindK f n.unpair.1 n.unpair.2 k)
  | .ret v .halt => .done v
  | .ret v (.pairL g n k) => .ev g n (.pairR v k)
  | .ret v (.pairR a k) => .ret (Nat.pair a v) k
  | .ret v (.compK f k) => .ev f v k
  | .ret v (.precK _ _ _ 0 k) => .ret v k
  | .ret v (.precK g a y (r + 1) k) => .ev g (Nat.pair a (Nat.pair y v)) (.precK g a (y + 1) r k)
  | .ret 0 (.rfindK _ _ m k) => .ret m k
  | .ret (_ + 1) (.rfindK f a m k) => .ev f (Nat.pair a (m + 1)) (.rfindK f a (m + 1) k)
  | .done v => .done v

/-- `Statement:` `t` machine steps. -/
def codeRun : ℕ → CodeState → CodeState
  | 0, s => s
  | t + 1, s => codeRun t (codeStep s)

/-- `Statement:` running `t₁ + t₂` steps is running `t₁`, then `t₂`. -/
theorem codeRun_add (t₁ t₂ : ℕ) (s : CodeState) :
    codeRun (t₁ + t₂) s = codeRun t₂ (codeRun t₁ s) := by
  induction t₁ generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ t ih => rw [Nat.succ_add]; exact ih (codeStep s)

/-! ## § II. Meaning of a state, and soundness -/

/-- `Statement:` the remaining `r` iterations of a `prec` loop, from index `y` at value `i`. -/
def precLoopSem (g : Code) (a : ℕ) : ℕ → ℕ → ℕ → Part ℕ
  | 0, _, i => Part.some i
  | r + 1, y, i => eval g (Nat.pair a (Nat.pair y i)) >>= precLoopSem g a r (y + 1)

/-- `Statement:` the `rfind'` search from index `m`. -/
def rfindSem (f : Code) (a m : ℕ) : Part ℕ :=
  (Nat.rfind fun k => (fun x => decide (x = 0)) <$> eval f (Nat.pair a (k + m))).map (· + m)

/-- `Statement:` the meaning of a continuation applied to a value. -/
def codeContSem : CodeCont → ℕ → Part ℕ
  | .halt, v => Part.some v
  | .pairL g n k, v => eval g n >>= fun b => codeContSem k (Nat.pair v b)
  | .pairR a k, v => codeContSem k (Nat.pair a v)
  | .compK f k, v => eval f v >>= codeContSem k
  | .precK g a y r k, v => precLoopSem g a r y v >>= codeContSem k
  | .rfindK f a m k, v =>
      (Nat.casesOn v (Part.some m) fun _ => rfindSem f a (m + 1)) >>= codeContSem k

/-- `Statement:` the meaning of a state. -/
def codeSem : CodeState → Part ℕ
  | .ev c n k => eval c n >>= codeContSem k
  | .ret v k => codeContSem k v
  | .done v => Part.some v

/-- `Statement:` `eval (pair f g) n` bound to `C` binds `f`, then `g`, then `C` of the pair. -/
theorem eval_pair_bind_eq (f g : Code) (n : ℕ) (C : ℕ → Part ℕ) :
    eval (pair f g) n >>= C = eval f n >>= fun a => eval g n >>= fun b => C (Nat.pair a b) := by
  apply Part.ext
  intro x
  show x ∈ (Nat.pair <$> eval f n <*> eval g n).bind C ↔ _
  simp only [Seq.seq, Part.bind_eq_bind, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨_, ⟨g', ⟨a, ha, rfl⟩, b, hb, rfl⟩, hx⟩
    exact ⟨a, ha, b, hb, hx⟩
  · rintro ⟨a, ha, b, hb, hx⟩
    exact ⟨_, ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩, hx⟩

/-- `Statement:` the `prec` recursion to `y`, continued by `precLoopSem` for `r` more steps, is
the recursion to `y + r`. -/
theorem precLoopSem_rec (f g : Code) (a : ℕ) :
    ∀ r y, (y.rec (eval f a) fun y IH => IH >>= fun i => eval g (Nat.pair a (Nat.pair y i)) :
        Part ℕ) >>= precLoopSem g a r y =
      ((y + r).rec (eval f a) fun y IH => IH >>= fun i => eval g (Nat.pair a (Nat.pair y i)) :
        Part ℕ)
  | 0, y => by
    show _ >>= Part.some = _
    rw [Part.bind_eq_bind, Part.bind_some_right]; rfl
  | r + 1, y => by
    have ih := precLoopSem_rec f g a r (y + 1)
    rw [show y + (r + 1) = (y + 1) + r by omega, ← ih]
    show Part.bind _ (fun i => Part.bind (eval g (Nat.pair a (Nat.pair y i)))
      (precLoopSem g a r (y + 1))) = Part.bind (Part.bind _ _) _
    rw [Part.bind_assoc]

/-- `Statement:` `eval (prec f g) n` is the base, then a loop counting down from `n.unpair.2`. -/
theorem eval_prec_eq_precLoopSem (f g : Code) (n : ℕ) :
    eval (prec f g) n = eval f n.unpair.1 >>= precLoopSem g n.unpair.1 n.unpair.2 0 := by
  have h := precLoopSem_rec f g n.unpair.1 n.unpair.2 0
  rw [Nat.zero_add] at h
  exact h.symm

/-- `Statement:` `x ∈ rfindSem f a m` iff `x = k + m`, `f` returns `0` at index `k + m`, and a
successor at every earlier index. -/
theorem mem_rfindSem {f : Code} {a m x : ℕ} :
    x ∈ rfindSem f a m ↔ ∃ k, x = k + m ∧ 0 ∈ eval f (Nat.pair a (k + m)) ∧
      ∀ j, j < k → ∃ v, v + 1 ∈ eval f (Nat.pair a (j + m)) := by
  unfold rfindSem
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Nat.mem_rfind] at hk
    obtain ⟨h1, h2⟩ := hk
    rw [Part.map_eq_map, Part.mem_map_iff] at h1
    obtain ⟨v, hv, hv0⟩ := h1
    have : v = 0 := of_decide_eq_true hv0
    subst this
    refine ⟨k, rfl, hv, fun j hj => ?_⟩
    have h3 := h2 hj
    rw [Part.map_eq_map, Part.mem_map_iff] at h3
    obtain ⟨w, hw, hw0⟩ := h3
    cases w with
    | zero => exact absurd hw0 (by decide)
    | succ w => exact ⟨w, hw⟩
  · rintro ⟨k, rfl, h0, hlt⟩
    refine ⟨k, ?_, rfl⟩
    rw [Nat.mem_rfind]
    refine ⟨Part.mem_map_iff _ |>.2 ⟨0, h0, rfl⟩, fun {j} hj => ?_⟩
    obtain ⟨v, hv⟩ := hlt j hj
    exact Part.mem_map_iff _ |>.2 ⟨v + 1, hv, rfl⟩

/-- `Statement:` a value of `rfindSem f a m` is at least `m`. -/
theorem rfindSem_ge {f : Code} {a m x : ℕ} (h : x ∈ rfindSem f a m) : m ≤ x := by
  obtain ⟨k, rfl, _⟩ := mem_rfindSem.1 h
  exact Nat.le_add_left m k

/-- `Statement:` one step of the `rfind'` search: test index `m`, stop on `0`, else go to `m + 1`. -/
theorem rfindSem_unfold (f : Code) (a m : ℕ) :
    rfindSem f a m = eval f (Nat.pair a m) >>=
      fun v => Nat.casesOn v (Part.some m) fun _ => rfindSem f a (m + 1) := by
  apply Part.ext
  intro x
  rw [Part.bind_eq_bind, Part.mem_bind_iff, mem_rfindSem]
  constructor
  · rintro ⟨k, rfl, h0, hlt⟩
    cases k with
    | zero =>
      rw [Nat.zero_add] at h0 ⊢
      exact ⟨0, h0, Part.mem_some _⟩
    | succ k =>
      obtain ⟨v, hv⟩ := hlt 0 (Nat.succ_pos _)
      rw [Nat.zero_add] at hv
      refine ⟨v + 1, hv, ?_⟩
      show k + 1 + m ∈ rfindSem f a (m + 1)
      rw [mem_rfindSem]
      refine ⟨k, by omega, by rw [show k + (m + 1) = k + 1 + m by omega]; exact h0,
        fun j hj => ?_⟩
      obtain ⟨w, hw⟩ := hlt (j + 1) (Nat.succ_lt_succ hj)
      exact ⟨w, by rw [show j + (m + 1) = j + 1 + m by omega]; exact hw⟩
  · rintro ⟨v, hv, hx⟩
    cases v with
    | zero =>
      have : x = m := Part.mem_some_iff.1 hx
      subst this
      exact ⟨0, (Nat.zero_add _).symm, by rw [Nat.zero_add]; exact hv,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ v =>
      obtain ⟨k, rfl, h0, hlt⟩ := mem_rfindSem.1 (show x ∈ rfindSem f a (m + 1) from hx)
      refine ⟨k + 1, by omega, by rw [show k + 1 + m = k + (m + 1) by omega]; exact h0,
        fun j hj => ?_⟩
      cases j with
      | zero => exact ⟨v, by rw [Nat.zero_add]; exact hv⟩
      | succ j =>
        obtain ⟨w, hw⟩ := hlt j (Nat.lt_of_succ_lt_succ hj)
        exact ⟨w, by rw [show j + 1 + m = j + (m + 1) by omega]; exact hw⟩

/-- `Statement:` `eval (rfind' f) n` is `rfindSem f n.unpair.1 n.unpair.2`, by `rfl`. -/
theorem eval_rfind'_eq_rfindSem (f : Code) (n : ℕ) :
    eval (rfind' f) n = rfindSem f n.unpair.1 n.unpair.2 := rfl

/-- `Statement:` one machine step preserves the meaning of the state. -/
theorem codeStep_sem : ∀ s, codeSem (codeStep s) = codeSem s
  | .ev .zero n k => by
    show codeContSem k 0 = Part.some 0 >>= codeContSem k
    rw [Part.bind_eq_bind, Part.bind_some]
  | .ev .succ n k => by
    show codeContSem k (n + 1) = Part.some (n + 1) >>= codeContSem k
    rw [Part.bind_eq_bind, Part.bind_some]
  | .ev .left n k => by
    show codeContSem k n.unpair.1 = Part.some n.unpair.1 >>= codeContSem k
    rw [Part.bind_eq_bind, Part.bind_some]
  | .ev .right n k => by
    show codeContSem k n.unpair.2 = Part.some n.unpair.2 >>= codeContSem k
    rw [Part.bind_eq_bind, Part.bind_some]
  | .ev (.pair f g) n k => by
    show eval f n >>= codeContSem (.pairL g n k) = eval (pair f g) n >>= codeContSem k
    rw [eval_pair_bind_eq]; rfl
  | .ev (.comp f g) n k => by
    show eval g n >>= codeContSem (.compK f k) = (eval g n >>= eval f) >>= codeContSem k
    simp only [Part.bind_eq_bind]
    rw [Part.bind_assoc]; rfl
  | .ev (.prec f g) n k => by
    show eval f n.unpair.1 >>= codeContSem (.precK g n.unpair.1 0 n.unpair.2 k) =
      eval (prec f g) n >>= codeContSem k
    rw [eval_prec_eq_precLoopSem]
    simp only [Part.bind_eq_bind]
    rw [Part.bind_assoc]; rfl
  | .ev (.rfind' f) n k => by
    show eval f (Nat.pair n.unpair.1 n.unpair.2) >>=
        codeContSem (.rfindK f n.unpair.1 n.unpair.2 k) = eval (rfind' f) n >>= codeContSem k
    rw [eval_rfind'_eq_rfindSem, rfindSem_unfold]
    simp only [Part.bind_eq_bind]
    rw [Part.bind_assoc]; rfl
  | .ret v .halt => rfl
  | .ret v (.pairL g n k) => rfl
  | .ret v (.pairR a k) => rfl
  | .ret v (.compK f k) => rfl
  | .ret v (.precK g a y 0 k) => by
    show codeContSem k v = Part.some v >>= codeContSem k
    rw [Part.bind_eq_bind, Part.bind_some]
  | .ret v (.precK g a y (r + 1) k) => by
    show eval g (Nat.pair a (Nat.pair y v)) >>= codeContSem (.precK g a (y + 1) r k) =
      (eval g (Nat.pair a (Nat.pair y v)) >>= precLoopSem g a r (y + 1)) >>= codeContSem k
    simp only [Part.bind_eq_bind]
    rw [Part.bind_assoc]; rfl
  | .ret 0 (.rfindK f a m k) => by
    show codeContSem k m = Part.some m >>= codeContSem k
    rw [Part.bind_eq_bind, Part.bind_some]
  | .ret (v + 1) (.rfindK f a m k) => by
    show eval f (Nat.pair a (m + 1)) >>= codeContSem (.rfindK f a (m + 1) k) =
      rfindSem f a (m + 1) >>= codeContSem k
    rw [rfindSem_unfold f a (m + 1)]
    simp only [Part.bind_eq_bind]
    rw [Part.bind_assoc]; rfl
  | .done v => rfl

/-- `Statement:` `t` machine steps preserve the meaning of the state. -/
theorem codeRun_sem (t : ℕ) (s : CodeState) : codeSem (codeRun t s) = codeSem s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => exact (ih (codeStep s)).trans (codeStep_sem s)

/-- `Statement:` soundness: if the run from `ev c n halt` reaches `done x`, then
`eval c n = Part.some x`. -/
theorem codeRun_sound {c : Code} {n x t : ℕ} (h : codeRun t (.ev c n .halt) = .done x) :
    eval c n = Part.some x := by
  have := codeRun_sem t (.ev c n .halt)
  rw [h] at this
  have e : codeSem (.ev c n .halt) = eval c n := by
    show eval c n >>= Part.some = eval c n
    rw [Part.bind_eq_bind, Part.bind_some_right]
  rw [e] at this
  exact this.symm

/-! ## § III. Completeness -/

/-- `Statement:` `s'` is reached from `s` in some number of steps. -/
def CodeReaches (s s' : CodeState) : Prop := ∃ t, codeRun t s = s'

/-- `Statement:` every state reaches itself. -/
theorem CodeReaches.refl (s : CodeState) : CodeReaches s s := ⟨0, rfl⟩

/-- `Statement:` reaching is transitive. -/
theorem CodeReaches.trans {s₁ s₂ s₃ : CodeState} (h₁ : CodeReaches s₁ s₂)
    (h₂ : CodeReaches s₂ s₃) : CodeReaches s₁ s₃ := by
  obtain ⟨t₁, rfl⟩ := h₁; obtain ⟨t₂, rfl⟩ := h₂
  exact ⟨t₁ + t₂, codeRun_add _ _ _⟩

/-- `Statement:` what the next state reaches, the state reaches. -/
theorem CodeReaches.of_step {s s' : CodeState} (h : CodeReaches (codeStep s) s') :
    CodeReaches s s' := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t + 1, rfl⟩

/-- `Statement:` if `g` is complete, a `prec` loop frame reaches every value of `precLoopSem`. -/
theorem codeRun_prec_complete (g : Code) (a : ℕ) (k : CodeCont)
    (hg : ∀ n x, x ∈ eval g n → ∀ k, CodeReaches (.ev g n k) (.ret x k)) :
    ∀ r y i x, x ∈ precLoopSem g a r y i → CodeReaches (.ret i (.precK g a y r k)) (.ret x k)
  | 0, y, i, x, h => by
    have : x = i := Part.mem_some_iff.1 h
    subst this
    exact CodeReaches.of_step (CodeReaches.refl _)
  | r + 1, y, i, x, h => by
    rw [precLoopSem, Part.bind_eq_bind, Part.mem_bind_iff] at h
    obtain ⟨j, hj, hx⟩ := h
    exact CodeReaches.of_step ((hg _ _ hj _).trans (codeRun_prec_complete g a k hg r (y + 1) j x hx))

/-- `Statement:` if `f` is complete, an `rfind'` frame at `m` reaches every value of
`rfindSem f a m`, by induction on the distance `d = x - m`. -/
theorem codeRun_rfind_complete (f : Code) (a : ℕ) (k : CodeCont) (x : ℕ)
    (hf : ∀ n x, x ∈ eval f n → ∀ k, CodeReaches (.ev f n k) (.ret x k)) :
    ∀ d m, x = d + m → x ∈ rfindSem f a m →
      CodeReaches (.ev f (Nat.pair a m) (.rfindK f a m k)) (.ret x k)
  | 0, m, hd, h => by
    rw [rfindSem_unfold, Part.bind_eq_bind, Part.mem_bind_iff] at h
    obtain ⟨v, hv, hx⟩ := h
    refine (hf _ _ hv _).trans ?_
    cases v with
    | zero =>
      have : x = m := Part.mem_some_iff.1 hx
      subst this
      exact CodeReaches.of_step (CodeReaches.refl _)
    | succ v =>
      have := rfindSem_ge (show x ∈ rfindSem f a (m + 1) from hx)
      exfalso; omega
  | d + 1, m, hd, h => by
    rw [rfindSem_unfold, Part.bind_eq_bind, Part.mem_bind_iff] at h
    obtain ⟨v, hv, hx⟩ := h
    refine (hf _ _ hv _).trans ?_
    cases v with
    | zero =>
      have : x = m := Part.mem_some_iff.1 hx
      exfalso; omega
    | succ v =>
      exact CodeReaches.of_step (codeRun_rfind_complete f a k x hf d (m + 1) (by omega) hx)

/-- `Statement:` completeness: if `x ∈ eval c n`, then `ev c n k` reaches `ret x k`. -/
theorem codeRun_complete :
    ∀ (c : Code) (n x : ℕ), x ∈ eval c n → ∀ k, CodeReaches (.ev c n k) (.ret x k)
  | .zero, n, x, h, k => by
    have : x = 0 := Part.mem_some_iff.1 h
    subst this; exact CodeReaches.of_step (CodeReaches.refl _)
  | .succ, n, x, h, k => by
    have : x = n + 1 := Part.mem_some_iff.1 h
    subst this; exact CodeReaches.of_step (CodeReaches.refl _)
  | .left, n, x, h, k => by
    have : x = n.unpair.1 := Part.mem_some_iff.1 h
    subst this; exact CodeReaches.of_step (CodeReaches.refl _)
  | .right, n, x, h, k => by
    have : x = n.unpair.2 := Part.mem_some_iff.1 h
    subst this; exact CodeReaches.of_step (CodeReaches.refl _)
  | .pair f g, n, x, h, k => by
    have h' : x ∈ eval (pair f g) n >>= Part.some := by
      rw [Part.bind_eq_bind, Part.bind_some_right]; exact h
    rw [eval_pair_bind_eq] at h'
    simp only [Part.bind_eq_bind, Part.mem_bind_iff] at h'
    obtain ⟨a, ha, b, hb, hx⟩ := h'
    have : x = Nat.pair a b := Part.mem_some_iff.1 hx
    subst this
    exact CodeReaches.of_step ((codeRun_complete f n a ha _).trans (CodeReaches.of_step
      ((codeRun_complete g n b hb _).trans (CodeReaches.of_step (CodeReaches.refl _)))))
  | .comp f g, n, x, h, k => by
    have h' : x ∈ (eval g n).bind (eval f) := h
    rw [Part.mem_bind_iff] at h'
    obtain ⟨y, hy, hx⟩ := h'
    exact CodeReaches.of_step ((codeRun_complete g n y hy _).trans
      (CodeReaches.of_step (codeRun_complete f y x hx _)))
  | .prec f g, n, x, h, k => by
    rw [eval_prec_eq_precLoopSem, Part.bind_eq_bind, Part.mem_bind_iff] at h
    obtain ⟨i, hi, hx⟩ := h
    exact CodeReaches.of_step ((codeRun_complete f _ i hi _).trans
      (codeRun_prec_complete g _ k (codeRun_complete g) _ 0 i x hx))
  | .rfind' f, n, x, h, k => by
    rw [eval_rfind'_eq_rfindSem] at h
    have := rfindSem_ge h
    exact CodeReaches.of_step (codeRun_rfind_complete f _ k x (codeRun_complete f)
      (x - n.unpair.2) n.unpair.2 (by omega) h)

/-- `Statement:` the run from `ev c n halt` reaches `done x` iff `x ∈ eval c n`. -/
theorem codeRun_halts_iff (c : Code) (n x : ℕ) :
    (∃ t, codeRun t (.ev c n .halt) = .done x) ↔ x ∈ eval c n := by
  constructor
  · rintro ⟨t, ht⟩
    rw [codeRun_sound ht]; exact Part.mem_some x
  · intro h
    obtain ⟨t, ht⟩ := codeRun_complete c n x h .halt
    exact ⟨t + 1, by rw [codeRun_add, ht]; rfl⟩

/-! ## § IV. `Nat.Primrec` combinators -/

/-- `Statement:` `if t = 0 then a else b`, by `Nat.casesOn`. -/
def natSel (t a b : ℕ) : ℕ := Nat.casesOn (motive := fun _ => ℕ) t a fun _ => b

/-- `Statement:` `natSel 0 a b = a`. -/
theorem natSel_zero (a b : ℕ) : natSel 0 a b = a := rfl
/-- `Statement:` `natSel (t + 1) a b = b`. -/
theorem natSel_succ (t a b : ℕ) : natSel (t + 1) a b = b := rfl

/-- `Statement:` the identity is `Nat.Primrec`. -/
theorem natPrimrec_id : Nat.Primrec fun x => x :=
  (Nat.Primrec.left.pair Nat.Primrec.right).of_eq fun n => cf_pair_unpair n

/-- `Statement:` every constant is `Nat.Primrec`. -/
theorem natPrimrec_const : ∀ k : ℕ, Nat.Primrec fun _ => k
  | 0 => Nat.Primrec.zero
  | k + 1 => Nat.Primrec.succ.comp (natPrimrec_const k)

/-- `Statement:` `Nat.Primrec` is closed under `Nat.pair`. -/
theorem natPrimrec_pair {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec fun x => Nat.pair (f x) (g x) := hf.pair hg
/-- `Statement:` `Nat.Primrec` is closed under the first projection of `Nat.unpair`. -/
theorem natPrimrec_fst {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec fun x => (f x).unpair.1 :=
  Nat.Primrec.left.comp hf
/-- `Statement:` `Nat.Primrec` is closed under the second projection of `Nat.unpair`. -/
theorem natPrimrec_snd {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec fun x => (f x).unpair.2 :=
  Nat.Primrec.right.comp hf
/-- `Statement:` `Nat.Primrec` is closed under successor. -/
theorem natPrimrec_succ {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec fun x => f x + 1 :=
  Nat.Primrec.succ.comp hf

/-- `Statement:` same type as Mathlib's `Nat.Primrec.casesOn'`, choice-free proof. -/
theorem cf_primrec_casesOn' {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (Nat.unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair z y) :=
  (Nat.Primrec.prec hf (hg.comp (Nat.Primrec.pair Nat.Primrec.left
    (Nat.Primrec.left.comp Nat.Primrec.right)))).of_eq fun n => by
    simp only [Nat.unpaired]
    cases n.unpair.2 with
    | zero => rfl
    | succ y => simp only [cf_unpair_pair]

-- Statement: `cf_primrec_casesOn'` has exactly the type of Mathlib's `Nat.Primrec.casesOn'`.
example : type_of% @Nat.Primrec.casesOn' := @cf_primrec_casesOn'

/-- `Statement:` `Nat.Primrec` is closed under `natSel`. -/
theorem natPrimrec_sel {t a b : ℕ → ℕ} (ht : Nat.Primrec t) (ha : Nat.Primrec a)
    (hb : Nat.Primrec b) : Nat.Primrec fun x => natSel (t x) (a x) (b x) :=
  ((cf_primrec_casesOn' ha (hb.comp Nat.Primrec.left)).comp (natPrimrec_pair natPrimrec_id ht)).of_eq
    fun x => by
    simp only [Nat.unpaired, cf_unpair_pair]
    cases t x <;> rfl

/-- `Statement:` `Nat.pred` is `Nat.Primrec`. -/
theorem natPrimrec_pred_self : Nat.Primrec Nat.pred :=
  ((cf_primrec_casesOn' (natPrimrec_const 0) Nat.Primrec.right).comp
    (natPrimrec_pair (natPrimrec_const 0) natPrimrec_id)).of_eq fun n => by
    simp only [Nat.unpaired, cf_unpair_pair]
    cases n <;> rfl

/-- `Statement:` `Nat.Primrec` is closed under `Nat.pred`. -/
theorem natPrimrec_pred {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec fun x => (f x).pred :=
  natPrimrec_pred_self.comp hf

/-- `Statement:` `Nat.Primrec` is closed under subtracting a constant. -/
theorem natPrimrec_sub_const {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∀ k : ℕ, Nat.Primrec fun x => f x - k
  | 0 => hf
  | k + 1 => (natPrimrec_pred (natPrimrec_sub_const hf k)).of_eq fun _ => rfl

/-- `Statement:` `Nat.Primrec` is closed under addition. -/
theorem natPrimrec_add {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec fun x => f x + g x := by
  have h : Nat.Primrec (Nat.unpaired (· + ·)) :=
    (Nat.Primrec.prec natPrimrec_id ((Nat.Primrec.succ.comp Nat.Primrec.right).comp
      Nat.Primrec.right)).of_eq fun p => by
      simp only [Nat.unpaired]
      induction p.unpair.2 with
      | zero => rfl
      | succ m ih => simp only [cf_unpair_pair] at ih ⊢; rw [ih]; rfl
  exact (h.comp (natPrimrec_pair hf hg)).of_eq fun x => by simp only [Nat.unpaired, cf_unpair_pair]

/-- `Statement:` primitive recursion on `q.unpair.2` with parameter `q.unpair.1` is `Nat.Primrec`. -/
theorem natPrimrec_rec {f : ℕ → ℕ} {g : ℕ → ℕ → ℕ → ℕ} (hf : Nat.Primrec f)
    (hg : Nat.Primrec fun q => g q.unpair.1 q.unpair.2.unpair.1 q.unpair.2.unpair.2) :
    Nat.Primrec fun q => Nat.rec (motive := fun _ => ℕ) (f q.unpair.1)
      (fun y IH => g q.unpair.1 y IH) q.unpair.2 :=
  (Nat.Primrec.prec hf hg).of_eq fun q => by
    simp only [Nat.unpaired]
    induction q.unpair.2 with
    | zero => rfl
    | succ m ih => simp only [cf_unpair_pair] at ih ⊢

/-! ## § V. Parity, halving, and decoding a code number -/

/-- `Statement:` the low bit of `n`, by plain recursion. -/
def boddNat (n : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun _ b => natSel b 1 0) n
/-- `Statement:` `n / 2`, by plain recursion. -/
def div2Nat (n : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun y d => d + boddNat y) n

/-- `Statement:` `boddNat` is `Nat.Primrec`. -/
theorem natPrimrec_boddNat : Nat.Primrec boddNat := by
  have h := natPrimrec_rec (f := fun _ => 0) (g := fun _ _ b => natSel b 1 0) (natPrimrec_const 0)
    (natPrimrec_sel (natPrimrec_snd (natPrimrec_snd natPrimrec_id)) (natPrimrec_const 1)
      (natPrimrec_const 0))
  refine (h.comp (natPrimrec_pair (natPrimrec_const 0) natPrimrec_id)).of_eq fun n => ?_
  simp only [cf_unpair_pair]; rfl

/-- `Statement:` `Nat.Primrec` is closed under `boddNat`. -/
theorem natPrimrec_boddNat_comp {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.Primrec fun x => boddNat (f x) :=
  natPrimrec_boddNat.comp hf

/-- `Statement:` `div2Nat` is `Nat.Primrec`. -/
theorem natPrimrec_div2Nat : Nat.Primrec div2Nat := by
  have h := natPrimrec_rec (f := fun _ => 0) (g := fun _ y d => d + boddNat y) (natPrimrec_const 0)
    (natPrimrec_add (natPrimrec_snd (natPrimrec_snd natPrimrec_id))
      (natPrimrec_boddNat_comp (natPrimrec_fst (natPrimrec_snd natPrimrec_id))))
  refine (h.comp (natPrimrec_pair (natPrimrec_const 0) natPrimrec_id)).of_eq fun n => ?_
  simp only [cf_unpair_pair]; rfl

/-- `Statement:` `Nat.Primrec` is closed under `div2Nat`. -/
theorem natPrimrec_div2Nat_comp {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.Primrec fun x => div2Nat (f x) :=
  natPrimrec_div2Nat.comp hf

/-- `Statement:` `boddNat n = (Nat.bodd n).toNat`. -/
theorem boddNat_eq : ∀ n, boddNat n = (Nat.bodd n).toNat
  | 0 => rfl
  | n + 1 => by
    show natSel (boddNat n) 1 0 = _
    rw [boddNat_eq n, Nat.bodd_succ]
    cases Nat.bodd n <;> rfl

/-- `Statement:` `div2Nat n = Nat.div2 n`. -/
theorem div2Nat_eq : ∀ n, div2Nat n = Nat.div2 n
  | 0 => rfl
  | n + 1 => by
    show div2Nat n + boddNat n = _
    rw [div2Nat_eq n, boddNat_eq n, Nat.div2_succ]
    cases Nat.bodd n <;> rfl

/-- `Statement:` for `X = x.toNat + 2 * (y.toNat + 2 * P)`, `boddNat` and `div2Nat` read back
`x`, `y` and `P`. -/
theorem boddNat_div2Nat_eq {X P : ℕ} {x y : Bool} (h : X = x.toNat + 2 * (y.toNat + 2 * P)) :
    boddNat X = x.toNat ∧ boddNat (div2Nat X) = y.toNat ∧ div2Nat (div2Nat X) = P := by
  obtain ⟨h1, h2, h3⟩ := cf_bodd_div2_eq h
  simp only [boddNat_eq, div2Nat_eq]
  rw [h1, h2, h3]
  exact ⟨rfl, rfl, rfl⟩

/-- `Statement:` the constructor tag of a code number: `0..3` atoms, `4` pair, `5` comp,
`6` prec, `7` rfind'. -/
def codeTag (c : ℕ) : ℕ :=
  natSel c 0 (natSel (c - 1) 1 (natSel (c - 2) 2 (natSel (c - 3) 3
    (4 + (boddNat (c - 4) + boddNat (c - 4) + boddNat (div2Nat (c - 4)))))))
/-- `Statement:` the argument number of a composite code number. -/
def codeArg (c : ℕ) : ℕ := div2Nat (div2Nat (c - 4))

/-- `Statement:` `codeTag` is `Nat.Primrec`. -/
theorem natPrimrec_codeTag : Nat.Primrec codeTag :=
  natPrimrec_sel natPrimrec_id (natPrimrec_const 0) (natPrimrec_sel
    (natPrimrec_sub_const natPrimrec_id 1) (natPrimrec_const 1) (natPrimrec_sel
    (natPrimrec_sub_const natPrimrec_id 2) (natPrimrec_const 2) (natPrimrec_sel
    (natPrimrec_sub_const natPrimrec_id 3) (natPrimrec_const 3) (natPrimrec_add (natPrimrec_const 4)
    (natPrimrec_add (natPrimrec_add
      (natPrimrec_boddNat_comp (natPrimrec_sub_const natPrimrec_id 4))
      (natPrimrec_boddNat_comp (natPrimrec_sub_const natPrimrec_id 4)))
      (natPrimrec_boddNat_comp (natPrimrec_div2Nat_comp (natPrimrec_sub_const natPrimrec_id 4))))))))
/-- `Statement:` `codeArg` is `Nat.Primrec`. -/
theorem natPrimrec_codeArg : Nat.Primrec codeArg :=
  natPrimrec_div2Nat_comp (natPrimrec_div2Nat_comp (natPrimrec_sub_const natPrimrec_id 4))

/-- `Statement:` `codeTag (X + 4)` in terms of the two low bits of `X`, by `rfl`. -/
theorem codeTag_add_four (X : ℕ) :
    codeTag (X + 4) = 4 + (boddNat X + boddNat X + boddNat (div2Nat X)) := rfl
/-- `Statement:` `codeArg (X + 4) = div2Nat (div2Nat X)`, by `rfl`. -/
theorem codeArg_add_four (X : ℕ) : codeArg (X + 4) = div2Nat (div2Nat X) := rfl

/-- `Statement:` the number of `pair a b` has tag `4` and argument `Nat.pair` of the parts. -/
theorem codeTag_pair (a b : Code) : codeTag (encodeCode (pair a b)) = 4 ∧
    codeArg (encodeCode (pair a b)) = Nat.pair (encodeCode a) (encodeCode b) := by
  obtain ⟨h1, h2, h3⟩ := boddNat_div2Nat_eq (X := 2 * (2 * Nat.pair (encodeCode a) (encodeCode b)))
    (P := Nat.pair (encodeCode a) (encodeCode b))
    (x := false) (y := false) (by show _ = 0 + 2 * (0 + 2 * _); omega)
  refine ⟨?_, ?_⟩
  · show codeTag (2 * (2 * _) + 4) = 4
    rw [codeTag_add_four, h1, h2]; rfl
  · show codeArg (2 * (2 * _) + 4) = _
    rw [codeArg_add_four, h3]
/-- `Statement:` the number of `comp a b` has tag `5` and argument `Nat.pair` of the parts. -/
theorem codeTag_comp (a b : Code) : codeTag (encodeCode (comp a b)) = 5 ∧
    codeArg (encodeCode (comp a b)) = Nat.pair (encodeCode a) (encodeCode b) := by
  obtain ⟨h1, h2, h3⟩ := boddNat_div2Nat_eq
    (X := 2 * (2 * Nat.pair (encodeCode a) (encodeCode b) + 1))
    (P := Nat.pair (encodeCode a) (encodeCode b))
    (x := false) (y := true) (by show _ = 0 + 2 * (1 + 2 * _); omega)
  refine ⟨?_, ?_⟩
  · show codeTag (2 * (2 * _ + 1) + 4) = 5
    rw [codeTag_add_four, h1, h2]; rfl
  · show codeArg (2 * (2 * _ + 1) + 4) = _
    rw [codeArg_add_four, h3]
/-- `Statement:` the number of `prec a b` has tag `6` and argument `Nat.pair` of the parts. -/
theorem codeTag_prec (a b : Code) : codeTag (encodeCode (prec a b)) = 6 ∧
    codeArg (encodeCode (prec a b)) = Nat.pair (encodeCode a) (encodeCode b) := by
  obtain ⟨h1, h2, h3⟩ := boddNat_div2Nat_eq
    (X := 2 * (2 * Nat.pair (encodeCode a) (encodeCode b)) + 1)
    (P := Nat.pair (encodeCode a) (encodeCode b))
    (x := true) (y := false) (by show _ = 1 + 2 * (0 + 2 * _); omega)
  refine ⟨?_, ?_⟩
  · show codeTag ((2 * (2 * _) + 1) + 4) = 6
    rw [codeTag_add_four, h1, h2]; rfl
  · show codeArg ((2 * (2 * _) + 1) + 4) = _
    rw [codeArg_add_four, h3]
/-- `Statement:` the number of `rfind' a` has tag `7` and argument the number of `a`. -/
theorem codeTag_rfind' (a : Code) : codeTag (encodeCode (rfind' a)) = 7 ∧
    codeArg (encodeCode (rfind' a)) = encodeCode a := by
  obtain ⟨h1, h2, h3⟩ := boddNat_div2Nat_eq (X := 2 * (2 * encodeCode a + 1) + 1)
    (P := encodeCode a) (x := true) (y := true) (by show _ = 1 + 2 * (1 + 2 * _); omega)
  refine ⟨?_, ?_⟩
  · show codeTag ((2 * (2 * _ + 1) + 1) + 4) = 7
    rw [codeTag_add_four, h1, h2]; rfl
  · show codeArg ((2 * (2 * _ + 1) + 1) + 4) = _
    rw [codeArg_add_four, h3]

/-! ## § VI. The machine on ℕ -/

/-- `Statement:` a continuation as a number, by `Nat.pair` tags `0..5`. -/
def encCont : CodeCont → ℕ
  | .halt => Nat.pair 0 0
  | .pairL g n k => Nat.pair 1 (Nat.pair (encodeCode g) (Nat.pair n (encCont k)))
  | .pairR a k => Nat.pair 2 (Nat.pair a (encCont k))
  | .compK f k => Nat.pair 3 (Nat.pair (encodeCode f) (encCont k))
  | .precK g a y r k =>
      Nat.pair 4 (Nat.pair (encodeCode g) (Nat.pair a (Nat.pair y (Nat.pair r (encCont k)))))
  | .rfindK f a m k =>
      Nat.pair 5 (Nat.pair (encodeCode f) (Nat.pair a (Nat.pair m (encCont k))))

/-- `Statement:` the number of an `ev` state from the numbers of its parts. -/
abbrev encEv (c n k : ℕ) : ℕ := Nat.pair 0 (Nat.pair c (Nat.pair n k))
/-- `Statement:` the number of a `ret` state from the numbers of its parts. -/
abbrev encRet (v k : ℕ) : ℕ := Nat.pair 1 (Nat.pair v k)

/-- `Statement:` a state as a number, by `Nat.pair` tags `0..2`. -/
def encState : CodeState → ℕ
  | .ev c n k => encEv (encodeCode c) n (encCont k)
  | .ret v k => encRet v (encCont k)
  | .done v => Nat.pair 2 v

/-- `Statement:` a three-way case on `t`. -/
def natCase3 (t b0 b1 b2 : ℕ) : ℕ := natSel t b0 (natSel (t - 1) b1 b2)
/-- `Statement:` a six-way case on `t`. -/
def natCase6 (t b0 b1 b2 b3 b4 b5 : ℕ) : ℕ :=
  natSel t b0 (natSel (t - 1) b1 (natSel (t - 2) b2 (natSel (t - 3) b3 (natSel (t - 4) b4 b5))))
/-- `Statement:` an eight-way case on `t`. -/
def natCase8 (t b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : ℕ :=
  natSel t b0 (natSel (t - 1) b1 (natSel (t - 2) b2 (natSel (t - 3) b3 (natSel (t - 4) b4
    (natSel (t - 5) b5 (natSel (t - 6) b6 b7))))))

/-- `Statement:` `Nat.Primrec` is closed under `natCase3`. -/
theorem natPrimrec_natCase3 {t b0 b1 b2 : ℕ → ℕ} (ht : Nat.Primrec t) (h0 : Nat.Primrec b0)
    (h1 : Nat.Primrec b1) (h2 : Nat.Primrec b2) :
    Nat.Primrec fun x => natCase3 (t x) (b0 x) (b1 x) (b2 x) :=
  natPrimrec_sel ht h0 (natPrimrec_sel (natPrimrec_sub_const ht 1) h1 h2)
/-- `Statement:` `Nat.Primrec` is closed under `natCase6`. -/
theorem natPrimrec_natCase6 {t b0 b1 b2 b3 b4 b5 : ℕ → ℕ} (ht : Nat.Primrec t)
    (h0 : Nat.Primrec b0) (h1 : Nat.Primrec b1) (h2 : Nat.Primrec b2) (h3 : Nat.Primrec b3)
    (h4 : Nat.Primrec b4) (h5 : Nat.Primrec b5) :
    Nat.Primrec fun x => natCase6 (t x) (b0 x) (b1 x) (b2 x) (b3 x) (b4 x) (b5 x) :=
  natPrimrec_sel ht h0 (natPrimrec_sel (natPrimrec_sub_const ht 1) h1 (natPrimrec_sel
    (natPrimrec_sub_const ht 2) h2 (natPrimrec_sel (natPrimrec_sub_const ht 3) h3
    (natPrimrec_sel (natPrimrec_sub_const ht 4) h4 h5))))
/-- `Statement:` `Nat.Primrec` is closed under `natCase8`. -/
theorem natPrimrec_natCase8 {t b0 b1 b2 b3 b4 b5 b6 b7 : ℕ → ℕ} (ht : Nat.Primrec t)
    (h0 : Nat.Primrec b0) (h1 : Nat.Primrec b1) (h2 : Nat.Primrec b2) (h3 : Nat.Primrec b3)
    (h4 : Nat.Primrec b4) (h5 : Nat.Primrec b5) (h6 : Nat.Primrec b6) (h7 : Nat.Primrec b7) :
    Nat.Primrec fun x => natCase8 (t x) (b0 x) (b1 x) (b2 x) (b3 x) (b4 x) (b5 x) (b6 x) (b7 x) :=
  natPrimrec_sel ht h0 (natPrimrec_sel (natPrimrec_sub_const ht 1) h1 (natPrimrec_sel
    (natPrimrec_sub_const ht 2) h2 (natPrimrec_sel (natPrimrec_sub_const ht 3) h3
    (natPrimrec_sel (natPrimrec_sub_const ht 4) h4 (natPrimrec_sel (natPrimrec_sub_const ht 5) h5
    (natPrimrec_sel (natPrimrec_sub_const ht 6) h6 h7))))))

/-- `Statement:` one machine step on an encoded `ev` payload `Nat.pair c (Nat.pair n k)`. -/
def evStepNat (p : ℕ) : ℕ :=
  natCase8 (codeTag p.unpair.1)
    (encRet 0 p.unpair.2.unpair.2)
    (encRet (p.unpair.2.unpair.1 + 1) p.unpair.2.unpair.2)
    (encRet p.unpair.2.unpair.1.unpair.1 p.unpair.2.unpair.2)
    (encRet p.unpair.2.unpair.1.unpair.2 p.unpair.2.unpair.2)
    (encEv (codeArg p.unpair.1).unpair.1 p.unpair.2.unpair.1
      (Nat.pair 1 (Nat.pair (codeArg p.unpair.1).unpair.2
        (Nat.pair p.unpair.2.unpair.1 p.unpair.2.unpair.2))))
    (encEv (codeArg p.unpair.1).unpair.2 p.unpair.2.unpair.1
      (Nat.pair 3 (Nat.pair (codeArg p.unpair.1).unpair.1 p.unpair.2.unpair.2)))
    (encEv (codeArg p.unpair.1).unpair.1 p.unpair.2.unpair.1.unpair.1
      (Nat.pair 4 (Nat.pair (codeArg p.unpair.1).unpair.2 (Nat.pair p.unpair.2.unpair.1.unpair.1
        (Nat.pair 0 (Nat.pair p.unpair.2.unpair.1.unpair.2 p.unpair.2.unpair.2))))))
    (encEv (codeArg p.unpair.1)
      (Nat.pair p.unpair.2.unpair.1.unpair.1 p.unpair.2.unpair.1.unpair.2)
      (Nat.pair 5 (Nat.pair (codeArg p.unpair.1) (Nat.pair p.unpair.2.unpair.1.unpair.1
        (Nat.pair p.unpair.2.unpair.1.unpair.2 p.unpair.2.unpair.2)))))

/-- `Statement:` one machine step on an encoded `ret` payload `Nat.pair v k`. -/
def retStepNat (p : ℕ) : ℕ :=
  natCase6 p.unpair.2.unpair.1
    (Nat.pair 2 p.unpair.1)
    (encEv p.unpair.2.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2.unpair.1
      (Nat.pair 2 (Nat.pair p.unpair.1 p.unpair.2.unpair.2.unpair.2.unpair.2)))
    (encRet (Nat.pair p.unpair.2.unpair.2.unpair.1 p.unpair.1) p.unpair.2.unpair.2.unpair.2)
    (encEv p.unpair.2.unpair.2.unpair.1 p.unpair.1 p.unpair.2.unpair.2.unpair.2)
    (natSel p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1
      (encRet p.unpair.1 p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2)
      (encEv p.unpair.2.unpair.2.unpair.1
        (Nat.pair p.unpair.2.unpair.2.unpair.2.unpair.1
          (Nat.pair p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 p.unpair.1))
        (Nat.pair 4 (Nat.pair p.unpair.2.unpair.2.unpair.1
          (Nat.pair p.unpair.2.unpair.2.unpair.2.unpair.1
            (Nat.pair (p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 + 1)
              (Nat.pair (p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 - 1)
                p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2)))))))
    (natSel p.unpair.1
      (encRet p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1
        p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2)
      (encEv p.unpair.2.unpair.2.unpair.1
        (Nat.pair p.unpair.2.unpair.2.unpair.2.unpair.1
          (p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 + 1))
        (Nat.pair 5 (Nat.pair p.unpair.2.unpair.2.unpair.1
          (Nat.pair p.unpair.2.unpair.2.unpair.2.unpair.1
            (Nat.pair (p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 + 1)
              p.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2))))))

/-- `Statement:` one machine step on an encoded state. -/
def codeStepNat (s : ℕ) : ℕ :=
  natCase3 s.unpair.1 (evStepNat s.unpair.2) (retStepNat s.unpair.2) s

/-- `Statement:` a closure tactic for `Nat.Primrec` goals built from the combinators above. -/
local macro "nat_primrec_closure" : tactic => `(tactic| repeat' (first
  | exact natPrimrec_id | apply natPrimrec_pair | apply natPrimrec_fst | apply natPrimrec_snd
  | apply natPrimrec_succ | apply natPrimrec_add | apply natPrimrec_sel | apply natPrimrec_natCase3
  | apply natPrimrec_natCase6 | apply natPrimrec_natCase8 | apply natPrimrec_codeTag.comp
  | apply natPrimrec_codeArg.comp | apply natPrimrec_boddNat_comp | apply natPrimrec_div2Nat_comp
  | apply natPrimrec_sub_const | apply natPrimrec_const))

section PrimProofs
attribute [local irreducible] Nat.pair Nat.unpair natSel natCase3 natCase6 natCase8 codeTag codeArg
  boddNat div2Nat

/-- `Statement:` `evStepNat` is `Nat.Primrec`. -/
theorem natPrimrec_evStepNat : Nat.Primrec evStepNat := by
  unfold evStepNat; simp only [encRet, encEv]; nat_primrec_closure
/-- `Statement:` `retStepNat` is `Nat.Primrec`. -/
theorem natPrimrec_retStepNat : Nat.Primrec retStepNat := by
  unfold retStepNat; simp only [encRet, encEv]; nat_primrec_closure

end PrimProofs

/-- `Statement:` `codeStepNat` is `Nat.Primrec`. -/
theorem natPrimrec_codeStepNat : Nat.Primrec codeStepNat := by
  unfold codeStepNat
  exact natPrimrec_natCase3 (natPrimrec_fst natPrimrec_id)
    (natPrimrec_evStepNat.comp (natPrimrec_snd natPrimrec_id))
    (natPrimrec_retStepNat.comp (natPrimrec_snd natPrimrec_id)) natPrimrec_id

section Commute
attribute [local irreducible] Nat.pair Nat.unpair

/-- `Statement:` `natCase3` at `0`. -/
theorem natCase3_0 (a b c : ℕ) : natCase3 0 a b c = a := rfl
/-- `Statement:` `natCase3` at `1`. -/
theorem natCase3_1 (a b c : ℕ) : natCase3 1 a b c = b := rfl
/-- `Statement:` `natCase3` at `2`. -/
theorem natCase3_2 (a b c : ℕ) : natCase3 2 a b c = c := rfl
/-- `Statement:` `natCase6` at `0`. -/
theorem natCase6_0 (b0 b1 b2 b3 b4 b5 : ℕ) : natCase6 0 b0 b1 b2 b3 b4 b5 = b0 := rfl
/-- `Statement:` `natCase6` at `1`. -/
theorem natCase6_1 (b0 b1 b2 b3 b4 b5 : ℕ) : natCase6 1 b0 b1 b2 b3 b4 b5 = b1 := rfl
/-- `Statement:` `natCase6` at `2`. -/
theorem natCase6_2 (b0 b1 b2 b3 b4 b5 : ℕ) : natCase6 2 b0 b1 b2 b3 b4 b5 = b2 := rfl
/-- `Statement:` `natCase6` at `3`. -/
theorem natCase6_3 (b0 b1 b2 b3 b4 b5 : ℕ) : natCase6 3 b0 b1 b2 b3 b4 b5 = b3 := rfl
/-- `Statement:` `natCase6` at `4`. -/
theorem natCase6_4 (b0 b1 b2 b3 b4 b5 : ℕ) : natCase6 4 b0 b1 b2 b3 b4 b5 = b4 := rfl
/-- `Statement:` `natCase6` at `5`. -/
theorem natCase6_5 (b0 b1 b2 b3 b4 b5 : ℕ) : natCase6 5 b0 b1 b2 b3 b4 b5 = b5 := rfl
/-- `Statement:` `natCase8` at `0`. -/
theorem natCase8_0 (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : natCase8 0 b0 b1 b2 b3 b4 b5 b6 b7 = b0 := rfl
/-- `Statement:` `natCase8` at `1`. -/
theorem natCase8_1 (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : natCase8 1 b0 b1 b2 b3 b4 b5 b6 b7 = b1 := rfl
/-- `Statement:` `natCase8` at `2`. -/
theorem natCase8_2 (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : natCase8 2 b0 b1 b2 b3 b4 b5 b6 b7 = b2 := rfl
/-- `Statement:` `natCase8` at `3`. -/
theorem natCase8_3 (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : natCase8 3 b0 b1 b2 b3 b4 b5 b6 b7 = b3 := rfl
/-- `Statement:` `natCase8` at `4`. -/
theorem natCase8_4 (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : natCase8 4 b0 b1 b2 b3 b4 b5 b6 b7 = b4 := rfl
/-- `Statement:` `natCase8` at `5`. -/
theorem natCase8_5 (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : natCase8 5 b0 b1 b2 b3 b4 b5 b6 b7 = b5 := rfl
/-- `Statement:` `natCase8` at `6`. -/
theorem natCase8_6 (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : natCase8 6 b0 b1 b2 b3 b4 b5 b6 b7 = b6 := rfl
/-- `Statement:` `natCase8` at `7`. -/
theorem natCase8_7 (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : natCase8 7 b0 b1 b2 b3 b4 b5 b6 b7 = b7 := rfl
/-- `Statement:` the tag of `Code.zero` is `0`, by `rfl`. -/
theorem codeTag_zero : codeTag (encodeCode Code.zero) = 0 := rfl
/-- `Statement:` the tag of `Code.succ` is `1`, by `rfl`. -/
theorem codeTag_succ : codeTag (encodeCode Code.succ) = 1 := rfl
/-- `Statement:` the tag of `Code.left` is `2`, by `rfl`. -/
theorem codeTag_left : codeTag (encodeCode Code.left) = 2 := rfl
/-- `Statement:` the tag of `Code.right` is `3`, by `rfl`. -/
theorem codeTag_right : codeTag (encodeCode Code.right) = 3 := rfl
/-- `Statement:` `r + 1 - 1 = r`, by `rfl`. -/
theorem succ_sub_one_rfl (r : ℕ) : r + 1 - 1 = r := rfl

/-- `Statement:` the step on numbers commutes with the step on states:
`codeStepNat (encState s) = encState (codeStep s)`. -/
theorem codeStepNat_enc : ∀ s, codeStepNat (encState s) = encState (codeStep s)
  | .ev .zero n k => by
    simp only [codeStepNat, encState, evStepNat, codeStep, cf_unpair_pair, natCase3_0, codeTag_zero,
      natCase8_0]
  | .ev .succ n k => by
    simp only [codeStepNat, encState, evStepNat, codeStep, cf_unpair_pair, natCase3_0, codeTag_succ,
      natCase8_1]
  | .ev .left n k => by
    simp only [codeStepNat, encState, evStepNat, codeStep, cf_unpair_pair, natCase3_0, codeTag_left,
      natCase8_2]
  | .ev .right n k => by
    simp only [codeStepNat, encState, evStepNat, codeStep, cf_unpair_pair, natCase3_0,
      codeTag_right, natCase8_3]
  | .ev (.pair f g) n k => by
    obtain ⟨h1, h2⟩ := codeTag_pair f g
    simp only [codeStepNat, encState, encCont, evStepNat, codeStep, cf_unpair_pair, natCase3_0, h1,
      h2, natCase8_4]
  | .ev (.comp f g) n k => by
    obtain ⟨h1, h2⟩ := codeTag_comp f g
    simp only [codeStepNat, encState, encCont, evStepNat, codeStep, cf_unpair_pair, natCase3_0, h1,
      h2, natCase8_5]
  | .ev (.prec f g) n k => by
    obtain ⟨h1, h2⟩ := codeTag_prec f g
    simp only [codeStepNat, encState, encCont, evStepNat, codeStep, cf_unpair_pair, natCase3_0, h1,
      h2, natCase8_6]
  | .ev (.rfind' f) n k => by
    obtain ⟨h1, h2⟩ := codeTag_rfind' f
    simp only [codeStepNat, encState, encCont, evStepNat, codeStep, cf_unpair_pair, natCase3_0, h1,
      h2, natCase8_7]
  | .ret v .halt => by
    simp only [codeStepNat, encState, encCont, retStepNat, codeStep, cf_unpair_pair, natCase3_1,
      natCase6_0]
  | .ret v (.pairL g n k) => by
    simp only [codeStepNat, encState, encCont, retStepNat, codeStep, cf_unpair_pair, natCase3_1,
      natCase6_1]
  | .ret v (.pairR a k) => by
    simp only [codeStepNat, encState, encCont, retStepNat, codeStep, cf_unpair_pair, natCase3_1,
      natCase6_2]
  | .ret v (.compK f k) => by
    simp only [codeStepNat, encState, encCont, retStepNat, codeStep, cf_unpair_pair, natCase3_1,
      natCase6_3]
  | .ret v (.precK g a y 0 k) => by
    simp only [codeStepNat, encState, encCont, retStepNat, codeStep, cf_unpair_pair, natCase3_1,
      natCase6_4, natSel_zero]
  | .ret v (.precK g a y (r + 1) k) => by
    simp only [codeStepNat, encState, encCont, retStepNat, codeStep, cf_unpair_pair, natCase3_1,
      natCase6_4, natSel_succ, succ_sub_one_rfl]
  | .ret 0 (.rfindK f a m k) => by
    simp only [codeStepNat, encState, encCont, retStepNat, codeStep, cf_unpair_pair, natCase3_1,
      natCase6_5, natSel_zero]
  | .ret (v + 1) (.rfindK f a m k) => by
    simp only [codeStepNat, encState, encCont, retStepNat, codeStep, cf_unpair_pair, natCase3_1,
      natCase6_5, natSel_succ]
  | .done v => by simp only [codeStepNat, encState, codeStep, cf_unpair_pair, natCase3_2]

end Commute

/-! ## § VII. Iteration, search, and the universal function -/

/-- `Statement:` `t` steps of `codeStepNat` from `x`, by one primitive recursion. -/
def codeIterNat (x t : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) x (fun _ IH => codeStepNat IH) t

/-- `Statement:` `codeIterNat` is `Nat.Primrec` in the pair of its arguments. -/
theorem natPrimrec_codeIterNat : Nat.Primrec fun q => codeIterNat q.unpair.1 q.unpair.2 :=
  natPrimrec_rec (f := fun x => x) (g := fun _ _ IH => codeStepNat IH) natPrimrec_id
    (natPrimrec_codeStepNat.comp (natPrimrec_snd (natPrimrec_snd natPrimrec_id)))

/-- `Statement:` `codeIterNat (encState s) t = encState (codeRun t s)`. -/
theorem codeIterNat_enc (s : CodeState) : ∀ t, codeIterNat (encState s) t = encState (codeRun t s)
  | 0 => rfl
  | t + 1 => by
    show codeStepNat (codeIterNat (encState s) t) = _
    rw [codeIterNat_enc s t, codeStepNat_enc, codeRun_add t 1]; rfl

/-- `Statement:` on an encoded state, `0` exactly when it is halted (`doneTest_enc`). -/
def doneTest (x : ℕ) : ℕ := natCase3 x.unpair.1 1 1 0

/-- `Statement:` `doneTest (encState s) = 0` iff `s` is `done v` for some `v`. -/
theorem doneTest_enc (s : CodeState) : doneTest (encState s) = 0 ↔ ∃ v, s = .done v := by
  cases s with
  | ev c n k => simp only [doneTest, encState, cf_unpair_pair]; exact ⟨fun h => absurd h (by decide),
      fun ⟨_, h⟩ => CodeState.noConfusion h⟩
  | ret v k => simp only [doneTest, encState, cf_unpair_pair]; exact ⟨fun h => absurd h (by decide),
      fun ⟨_, h⟩ => CodeState.noConfusion h⟩
  | done v => exact ⟨fun _ => ⟨v, rfl⟩, fun _ => by simp only [doneTest, encState, cf_unpair_pair]; rfl⟩

/-- `Statement:` the encoded start state for input `a = Nat.pair e n`: run code `e` on `n`. -/
def initNat (a : ℕ) : ℕ := encEv a.unpair.1 a.unpair.2 (Nat.pair 0 0)

/-- `Statement:` `initNat a` encodes `ev (ofNatCodeCF a.unpair.1) a.unpair.2 halt`. -/
theorem initNat_eq (a : ℕ) :
    initNat a = encState (.ev (ofNatCodeCF a.unpair.1) a.unpair.2 .halt) := by
  simp only [initNat, encState, encCont, cf_encodeCode_ofNatCodeCF]

/-- `Statement:` on `Nat.pair a t`, `0` iff the run from `initNat a` has halted by step `t`. -/
def haltSearch (q : ℕ) : ℕ := doneTest (codeIterNat (initNat q.unpair.1) q.unpair.2)
/-- `Statement:` on `Nat.pair a t`, the payload of the state after `t` steps from `initNat a`. -/
def haltValue (q : ℕ) : ℕ := (codeIterNat (initNat q.unpair.1) q.unpair.2).unpair.2

/-- `Statement:` `initNat` is `Nat.Primrec`. -/
theorem natPrimrec_initNat : Nat.Primrec initNat := by
  unfold initNat; simp only [encEv]; nat_primrec_closure

/-- `Statement:` `q ↦ codeIterNat (initNat q.unpair.1) q.unpair.2` is `Nat.Primrec`. -/
theorem natPrimrec_iterInit : Nat.Primrec fun q => codeIterNat (initNat q.unpair.1) q.unpair.2 :=
  (natPrimrec_codeIterNat.comp (natPrimrec_pair (natPrimrec_initNat.comp (natPrimrec_fst
    natPrimrec_id)) (natPrimrec_snd natPrimrec_id))).of_eq fun q => by
    simp only [cf_unpair_pair]

/-- `Statement:` `haltSearch` is `Nat.Primrec`. -/
theorem natPrimrec_haltSearch : Nat.Primrec haltSearch :=
  (natPrimrec_natCase3 (natPrimrec_fst natPrimrec_iterInit) (natPrimrec_const 1)
    (natPrimrec_const 1) (natPrimrec_const 0)).of_eq fun _ => rfl

/-- `Statement:` `haltValue` is `Nat.Primrec`. -/
theorem natPrimrec_haltValue : Nat.Primrec haltValue :=
  (natPrimrec_snd natPrimrec_iterInit).of_eq fun _ => rfl

/-- `Statement:` the universal function in Kleene normal form, search then read, is `Nat.Partrec`. -/
theorem univ_natPartrec_raw : Nat.Partrec fun a =>
    (Nat.pair <$> (Part.some a) <*>
      Nat.rfind fun t => (fun m => decide (m = 0)) <$> (Part.some (haltSearch (Nat.pair a t)))) >>=
      fun q => Part.some (haltValue q) :=
  Nat.Partrec.comp (Nat.Partrec.of_primrec natPrimrec_haltValue)
    (Nat.Partrec.pair (Nat.Partrec.of_primrec natPrimrec_id)
      (Nat.Partrec.rfind (Nat.Partrec.of_primrec natPrimrec_haltSearch)))

/-- `Statement:` that normal form computes `eval (ofNatCodeCF a.unpair.1) a.unpair.2`. -/
theorem univ_value_eq (a : ℕ) :
    ((Nat.pair <$> (Part.some a) <*>
      Nat.rfind fun t => (fun m => decide (m = 0)) <$> (Part.some (haltSearch (Nat.pair a t)))) >>=
      fun q => Part.some (haltValue q)) = eval (ofNatCodeCF a.unpair.1) a.unpair.2 := by
  have hs : ∀ t, haltSearch (Nat.pair a t) = doneTest (encState (codeRun t
      (.ev (ofNatCodeCF a.unpair.1) a.unpair.2 .halt))) := fun t => by
    rw [haltSearch, cf_unpair_pair, initNat_eq, codeIterNat_enc]
  have he : ∀ t, haltValue (Nat.pair a t) = (encState (codeRun t
      (.ev (ofNatCodeCF a.unpair.1) a.unpair.2 .halt))).unpair.2 := fun t => by
    rw [haltValue, cf_unpair_pair, initNat_eq, codeIterNat_enc]
  have key : ∀ t, true ∈ ((fun m => decide (m = 0)) <$> (Part.some (haltSearch (Nat.pair a t))) :
      Part Bool) → haltValue (Nat.pair a t) ∈ eval (ofNatCodeCF a.unpair.1) a.unpair.2 := by
    intro t ht
    rw [Part.map_eq_map, Part.mem_map_iff] at ht
    obtain ⟨m, hm, hm0⟩ := ht
    have hm' : m = haltSearch (Nat.pair a t) := Part.mem_some_iff.1 hm
    have h0 : haltSearch (Nat.pair a t) = 0 := hm' ▸ of_decide_eq_true hm0
    rw [hs] at h0
    obtain ⟨v, hv⟩ := (doneTest_enc _).1 h0
    rw [he, hv]
    show (Nat.pair 2 v).unpair.2 ∈ _
    rw [cf_unpair_pair]
    exact (codeRun_halts_iff _ _ _).1 ⟨t, hv⟩
  apply Part.ext
  intro x
  simp only [Seq.seq, Part.bind_eq_bind, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨q, ⟨g, ⟨a', ha', rfl⟩, t, ht, rfl⟩, hx⟩
    have : a' = a := Part.mem_some_iff.1 ha'
    subst this
    have hx' : x = haltValue (Nat.pair a' t) := Part.mem_some_iff.1 hx
    rw [hx']
    exact key t (Nat.rfind_spec ht)
  · intro hx
    obtain ⟨t0, ht0⟩ := (codeRun_halts_iff _ _ _).2 hx
    have hdom : (Nat.rfind fun t => (fun m => decide (m = 0)) <$>
        (Part.some (haltSearch (Nat.pair a t)))).Dom := by
      rw [Nat.rfind_dom]
      refine ⟨t0, ?_, fun _ => trivial⟩
      rw [Part.map_eq_map, Part.mem_map_iff]
      refine ⟨0, ?_, rfl⟩
      rw [hs, ht0, (doneTest_enc _).2 ⟨x, rfl⟩]
      exact Part.mem_some _
    refine ⟨_, ⟨_, ⟨a, Part.mem_some a, rfl⟩, _, Part.get_mem hdom, rfl⟩, ?_⟩
    have hk := key _ (Nat.rfind_spec (Part.get_mem hdom))
    rw [Part.mem_unique hk hx]
    exact Part.mem_some _

/-- `Statement:` `x ↦ eval (ofNatCodeCF x.unpair.1) x.unpair.2` is `Nat.Partrec`. -/
theorem univ_natPartrec : Nat.Partrec fun x => eval (ofNatCodeCF x.unpair.1) x.unpair.2 :=
  univ_natPartrec_raw.of_eq univ_value_eq

/-! ## § VIII. The universal code -/

/-- `Statement:` the forward direction of Mathlib's `Nat.Partrec.Code.exists_code`: a
`Nat.Partrec` function has a code. -/
theorem cf_exists_code_mp {f : ℕ →. ℕ} (h : Nat.Partrec f) : ∃ c : Code, eval c = f := by
  induction h with
  | zero => exact ⟨zero, rfl⟩
  | succ => exact ⟨succ, rfl⟩
  | left => exact ⟨left, rfl⟩
  | right => exact ⟨right, rfl⟩
  | pair _ _ hf hg =>
    obtain ⟨cf, rfl⟩ := hf; obtain ⟨cg, rfl⟩ := hg
    exact ⟨pair cf cg, rfl⟩
  | comp _ _ hf hg =>
    obtain ⟨cf, rfl⟩ := hf; obtain ⟨cg, rfl⟩ := hg
    exact ⟨comp cf cg, rfl⟩
  | prec _ _ hf hg =>
    obtain ⟨cf, rfl⟩ := hf; obtain ⟨cg, rfl⟩ := hg
    exact ⟨prec cf cg, rfl⟩
  | rfind _ hf =>
    obtain ⟨cf, rfl⟩ := hf
    refine ⟨comp (rfind' cf) (pair Code.id zero), funext fun a => ?_⟩
    rw [cf_eval_comp (cf_eval_pair (cf_eval_id a) rfl)]
    show Nat.unpaired (fun a m => (Nat.rfind fun n => (fun m => m = 0) <$>
      eval cf (Nat.pair a (n + m))).map (· + m)) (Nat.pair a 0) = _
    simp only [Nat.unpaired, cf_unpair_pair]
    exact Part.map_id' (fun _ => rfl) _

-- Statement: `cf_exists_code_mp` has exactly the type of the forward direction of Mathlib's
-- `Nat.Partrec.Code.exists_code`.
example {f : ℕ →. ℕ} : (Nat.Partrec.Code.exists_code (f := f)).mp = cf_exists_code_mp := rfl

/-- `Statement:` a universal code: on `Nat.pair (encodeCode d) n` it computes `eval d n`. -/
theorem universal_code_cf :
    ∃ u : Code, ∀ d n, eval u (Nat.pair (encodeCode d) n) = eval d n := by
  obtain ⟨u, hu⟩ := cf_exists_code_mp univ_natPartrec
  refine ⟨u, fun d n => ?_⟩
  rw [hu]
  show eval (ofNatCodeCF (Nat.unpair (Nat.pair (encodeCode d) n)).1)
    (Nat.unpair (Nat.pair (encodeCode d) n)).2 = _
  rw [cf_unpair_pair, cf_ofNatCodeCF_encodeCode]

/-- `Statement:` the same over every number: on `Nat.pair e n` it computes `eval (ofNatCodeCF e) n`. -/
theorem universal_code_cf' :
    ∃ u : Code, ∀ e n, eval u (Nat.pair e n) = eval (ofNatCodeCF e) n := by
  obtain ⟨u, hu⟩ := cf_exists_code_mp univ_natPartrec
  refine ⟨u, fun e n => ?_⟩
  rw [hu]
  show eval (ofNatCodeCF (Nat.unpair (Nat.pair e n)).1) (Nat.unpair (Nat.pair e n)).2 = _
  rw [cf_unpair_pair]

/-- `Statement:` `universal_code_cf`, with every name fully qualified. -/
theorem discussion142_answer : ∃ u : Nat.Partrec.Code, ∀ d n,
    Nat.Partrec.Code.eval u (Nat.pair (Nat.Partrec.Code.encodeCode d) n) =
      Nat.Partrec.Code.eval d n :=
  universal_code_cf

/-- `Statement:` CONTROL: the constant code `Code.zero` is not universal. -/
theorem zero_not_universal :
    ¬ ∀ d n, eval Code.zero (Nat.pair (encodeCode d) n) = eval d n := by
  intro h
  have h1 := h Code.succ 0
  have : (Part.some 0 : Part ℕ) = Part.some 1 := h1
  exact absurd (Part.some_inj.1 this) (by decide)

-- Statement: in the bins of `ZeroParadox/Category/ChoiceCannotBe.md`, a proof of this statement
-- through Mathlib's `eval_part` carries `Classical.choice`, because `eval_part` does; the proof here
-- does not, so for this statement that choice is ACCIDENTAL. It says nothing about the `Partrec₂`
-- form, whose statement carries choice (`stmtPartrec₂Hyp`, `KleeneChoiceFree.lean` § V).

/-! ## § IX. A self-printing universal code

`SelfPrints` and `Universal` (`ZeroParadox/Computability/Kleene.lean`) restated with `encodeCode`
and `ofNatCodeCF`, the bridges to them, and a code meeting both: Kleene's ψ-form (`kleene_cf`)
applied to a total dispatcher followed by `universal_code_cf'`.

Reading (cited, not claimed): the textbook ψ-form corollary of the recursion theorem; in the framing
of Bonfante, Kaczmarek, Marion, "On abstract computer virology from a recursion-theoretic
perspective", J. Computer Virology 1(3-4), 2006, Def. 2 and Thm 3, such a code is a virus. -/

/-- `Statement:` `SelfPrints` with `encodeCode`: channel `0` returns the code's own number. -/
def SelfPrintsCF (c : Code) : Prop :=
  ∀ n, eval c (Nat.pair 0 n) = Part.some (encodeCode c)

/-- `Statement:` `Universal` with `ofNatCodeCF`: channel `e + 1` runs code `e`. -/
def UniversalCF (c : Code) : Prop :=
  ∀ e n, eval c (Nat.pair (e + 1) n) = eval (ofNatCodeCF e) n

/-- `Statement:` `Universal` with no decoder: channel `encodeCode d + 1` runs `d`. -/
def UniversalEnc (c : Code) : Prop :=
  ∀ d n, eval c (Nat.pair (encodeCode d + 1) n) = eval d n

/-- `Statement:` CONTROL: assumes `∃ c, SelfPrints c ∧ Universal c`, proves `True`. -/
theorem stmtSelfrefUniversal (_h : ∃ c : Code, SelfPrints c ∧ Universal c) : True := trivial
/-- `Statement:` CONTROL: assumes `∃ c, SelfPrintsCF c ∧ UniversalCF c`, proves `True`. -/
theorem stmtSelfrefUniversalCF (_h : ∃ c : Code, SelfPrintsCF c ∧ UniversalCF c) : True := trivial
/-- `Statement:` CONTROL: assumes `∃ c, SelfPrintsCF c ∧ UniversalEnc c`, proves `True`. -/
theorem stmtSelfrefUniversalEnc (_h : ∃ c : Code, SelfPrintsCF c ∧ UniversalEnc c) : True := trivial

/-- `Statement:` `SelfPrints c ↔ SelfPrintsCF c`. -/
theorem selfPrints_iff_cf (c : Code) : SelfPrints c ↔ SelfPrintsCF c := by
  unfold SelfPrints SelfPrintsCF
  rw [encodeCode_eq]

/-- `Statement:` `Universal c ↔ UniversalCF c`. -/
theorem universal_iff_cf (c : Code) : Universal c ↔ UniversalCF c := by
  unfold Universal UniversalCF
  rw [ofNatCode_eq, ofNatCodeCF_eq_ofNatCode]

/-- `Statement:` `UniversalCF c ↔ UniversalEnc c`. -/
theorem universalCF_iff_enc (c : Code) : UniversalCF c ↔ UniversalEnc c := by
  constructor
  · intro h d n
    have := h (encodeCode d) n
    rw [cf_ofNatCodeCF_encodeCode] at this
    exact this
  · intro h e n
    have := h (ofNatCodeCF e) n
    rw [cf_encodeCode_ofNatCodeCF] at this
    exact this

/-- `Statement:` the Gödel number of `Code.id`. -/
def codeIdIndex : ℕ := encodeCode Code.id

/-- `Statement:` the dispatcher's value: `⟨codeIdIndex, y⟩` at `0`, `⟨e, n⟩` at `e + 1`. -/
def selDValue (y n : ℕ) : ℕ → ℕ
  | 0 => Nat.pair codeIdIndex y
  | e + 1 => Nat.pair e n

/-- `Statement:` on `Nat.pair y n`, returns `Nat.pair codeIdIndex y`. -/
def selDBase : Code := pair (Code.const codeIdIndex) left
/-- `Statement:` on `Nat.pair (Nat.pair y n) (Nat.pair j i)`, returns `Nat.pair j n`. -/
def selDStep : Code := pair (comp left right) (comp right left)
/-- `Statement:` `Nat.pair y (Nat.pair k n)` to `Nat.pair (Nat.pair y n) k`. -/
def selDArg : Code := pair (pair left (comp right right)) (comp left right)
/-- `Statement:` the dispatcher, one `prec` on the channel `k`. -/
def selD : Code := comp (prec selDBase selDStep) selDArg

/-- `Statement:` `selD` on `Nat.pair y (Nat.pair k n)` returns `selDValue y n k`. -/
theorem eval_selD (y k n : ℕ) :
    eval selD (Nat.pair y (Nat.pair k n)) = Part.some (selDValue y n k) := by
  have hA : eval selDArg (Nat.pair y (Nat.pair k n)) = Part.some (Nat.pair (Nat.pair y n) k) :=
    cf_eval_pair (cf_eval_pair (cf_eval_left _ _)
      (cf_eval_comp_some (cf_eval_right _ _) (cf_eval_right _ _)))
      (cf_eval_comp_some (cf_eval_right _ _) (cf_eval_left _ _))
  unfold selD
  rw [cf_eval_comp hA]
  refine cf_eval_prec_total (a := Nat.pair y n) (selDValue y n) ?_ (fun j => ?_) k
  · exact cf_eval_pair (eval_const _ _) (cf_eval_left _ _)
  · exact cf_eval_pair (cf_eval_comp_some (cf_eval_right _ _) (cf_eval_left _ _))
      (cf_eval_comp_some (cf_eval_left _ _) (cf_eval_right _ _))

/-- `Statement:` `selD`, then `u`; `N` pads the number, not the behaviour. -/
def psiOf (u : Code) (N : ℕ) : Code := comp u (comp right (pair (Code.const N) selD))

/-- `Statement:` `psiOf u N` on `Nat.pair y (Nat.pair k n)` is `u` on `selDValue y n k`. -/
theorem eval_psiOf (u : Code) (N y k n : ℕ) :
    eval (psiOf u N) (Nat.pair y (Nat.pair k n)) = eval u (selDValue y n k) :=
  cf_eval_comp (cf_eval_comp_some (cf_eval_pair (eval_const _ _) (eval_selD y k n))
    (cf_eval_right _ _))

/-- `Statement:` the Kleene fixed point of `psiOf u N`. -/
def selfUniv (u : Code) (N : ℕ) : Code := fpCF (psiOf u N)

/-- `Statement:` for `u` as in `universal_code_cf'`, `selfUniv u N` meets both predicates. -/
theorem selfUniv_spec (u : Code) (hu : ∀ e n, eval u (Nat.pair e n) = eval (ofNatCodeCF e) n)
    (N : ℕ) : SelfPrintsCF (selfUniv u N) ∧ UniversalCF (selfUniv u N) := by
  refine ⟨fun n => ?_, fun e n => ?_⟩
  · rw [selfUniv, kleene_cf, eval_psiOf]
    show eval u (Nat.pair codeIdIndex (encodeCode (fpCF (psiOf u N)))) = _
    rw [hu, codeIdIndex, cf_ofNatCodeCF_encodeCode, cf_eval_id]
  · rw [selfUniv, kleene_cf, eval_psiOf]
    show eval u (Nat.pair e n) = _
    rw [hu]

/-- `Statement:` a code that is self-printing and universal, restated. -/
theorem selfref_universal_exists_cf : ∃ c : Code, SelfPrintsCF c ∧ UniversalCF c := by
  obtain ⟨u, hu⟩ := universal_code_cf'
  exact ⟨selfUniv u 0, selfUniv_spec u hu 0⟩

/-- `Statement:` the same, with `UniversalEnc`. -/
theorem selfref_universal_exists_enc : ∃ c : Code, SelfPrintsCF c ∧ UniversalEnc c := by
  obtain ⟨c, h1, h2⟩ := selfref_universal_exists_cf
  exact ⟨c, h1, (universalCF_iff_enc c).1 h2⟩

/-- `Statement:` the same, unfolded, every name fully qualified. -/
theorem selfref_universal_exists_verbatim : ∃ c : Nat.Partrec.Code,
    (∀ n, Nat.Partrec.Code.eval c (Nat.pair 0 n) = Part.some (Nat.Partrec.Code.encodeCode c)) ∧
    (∀ d n, Nat.Partrec.Code.eval c (Nat.pair (Nat.Partrec.Code.encodeCode d + 1) n) =
      Nat.Partrec.Code.eval d n) :=
  selfref_universal_exists_enc

/-- `Statement:` same type as Mathlib's `Nat.left_le_pair`, choice-free proof. -/
theorem cf_left_le_pair (a b : ℕ) : a ≤ Nat.pair a b := by
  unfold Nat.pair
  split
  · exact Nat.le_add_left a (b * b)
  · exact Nat.le_trans (Nat.le_add_left a (a * a)) (Nat.le_add_right _ b)

/-- `Statement:` same type as Mathlib's `Nat.right_le_pair`; both measure `[propext]`
(`PurityCheck`). -/
theorem cf_right_le_pair (a b : ℕ) : b ≤ Nat.pair a b := by
  unfold Nat.pair
  split
  · exact Nat.le_trans (Nat.le_mul_self b) (Nat.le_add_right _ a)
  · exact Nat.le_add_left b (a * a + a)

-- Statement: `cf_left_le_pair` and `cf_right_le_pair` have exactly the Mathlib lemmas' types.
example : type_of% @Nat.left_le_pair := @cf_left_le_pair
example : type_of% @Nat.right_le_pair := @cf_right_le_pair

/-- `Statement:` `encodeCode a < encodeCode (comp a b)`. -/
theorem encodeCode_lt_comp_left (a b : Code) : encodeCode a < encodeCode (comp a b) := by
  have h : encodeCode (comp a b) = 2 * (2 * Nat.pair (encodeCode a) (encodeCode b) + 1) + 4 := rfl
  have := cf_left_le_pair (encodeCode a) (encodeCode b)
  omega

/-- `Statement:` `encodeCode b < encodeCode (comp a b)`. -/
theorem encodeCode_lt_comp_right (a b : Code) : encodeCode b < encodeCode (comp a b) := by
  have h : encodeCode (comp a b) = 2 * (2 * Nat.pair (encodeCode a) (encodeCode b) + 1) + 4 := rfl
  have := cf_right_le_pair (encodeCode a) (encodeCode b)
  omega

/-- `Statement:` `encodeCode a < encodeCode (pair a b)`. -/
theorem encodeCode_lt_pair_left (a b : Code) : encodeCode a < encodeCode (pair a b) := by
  have h : encodeCode (pair a b) = 2 * (2 * Nat.pair (encodeCode a) (encodeCode b)) + 4 := rfl
  have := cf_left_le_pair (encodeCode a) (encodeCode b)
  omega

/-- `Statement:` `N < encodeCode (selfUniv u N)`. -/
theorem lt_encodeCode_selfUniv (u : Code) (N : ℕ) : N < encodeCode (selfUniv u N) := by
  have h1 := cf_le_encodeCode_const N
  have h2 := encodeCode_lt_pair_left (Code.const N) selD
  have h3 := encodeCode_lt_comp_right right (pair (Code.const N) selD)
  have h4 := encodeCode_lt_comp_right u (comp right (pair (Code.const N) selD))
  have h5 := encodeCode_lt_comp_left (psiOf u N) (pair (comp cfDiagIndex left) right)
  have h6 : encodeCode (selfUniv u N) =
      cfCurryIndex (encodeCode (cfDiag (psiOf u N))) (encodeCode (cfDiag (psiOf u N))) :=
    cf_encodeCode_curry _ _
  have h7 := cf_left_le_pair (encodeCode (cfDiag (psiOf u N)))
    (2 * (2 * Nat.pair (encodeCode (Code.const (encodeCode (cfDiag (psiOf u N)))))
      (encodeCode Code.id)) + 4)
  have e5 : cfDiag (psiOf u N) = comp (psiOf u N) (pair (comp cfDiagIndex left) right) := rfl
  have e4 : psiOf u N = comp u (comp right (pair (Code.const N) selD)) := rfl
  rw [← e5] at h5
  rw [← e4] at h4
  unfold cfCurryIndex at h6
  omega

/-- `Statement:` above every bound there is a self-printing universal code, restated. -/
theorem selfref_universal_unbounded_cf :
    ∀ N, ∃ c : Code, N < encodeCode c ∧ SelfPrintsCF c ∧ UniversalCF c := by
  obtain ⟨u, hu⟩ := universal_code_cf'
  exact fun N => ⟨selfUniv u N, lt_encodeCode_selfUniv u N, selfUniv_spec u hu N⟩

/-- `Statement:` the sum of the values of `f : Fin n → ℕ`. -/
def cfFinBound : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + cfFinBound n (fun i => f i.succ)

/-- `Statement:` every value of `f : Fin n → ℕ` is at most `cfFinBound n f`. -/
theorem cf_le_finBound : ∀ (n : ℕ) (f : Fin n → ℕ) (i : Fin n), f i ≤ cfFinBound n f
  | 0, _, i => i.elim0
  | n + 1, f, i => by
    show f i ≤ f 0 + cfFinBound n (fun i => f i.succ)
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (cf_le_finBound n (fun i => f i.succ) j) (Nat.le_add_left _ _)

/-- `Statement:` the self-printing universal codes, restated, form an infinite set. -/
theorem selfref_universal_infinite_cf :
    Set.Infinite {c : Code | SelfPrintsCF c ∧ UniversalCF c} := by
  intro hfin
  obtain ⟨e⟩ := hfin
  obtain ⟨c, hlt, h1, h2⟩ := selfref_universal_unbounded_cf
    (cfFinBound _ (fun i => encodeCode (e.symm i).1))
  have hle := cf_le_finBound _ (fun i => encodeCode (e.symm i).1) (e ⟨c, h1, h2⟩)
  simp only [Equiv.symm_apply_apply] at hle
  exact absurd (Nat.lt_of_lt_of_le hlt hle) (Nat.lt_irrefl _)

/-- `Statement:` CONTROL: `Code.zero` is self-printing and not universal. -/
theorem zero_selfPrints_not_universal : SelfPrintsCF Code.zero ∧ ¬ UniversalCF Code.zero := by
  refine ⟨fun _ => rfl, fun h => ?_⟩
  have h1 := h (encodeCode Code.succ) 0
  rw [cf_ofNatCodeCF_encodeCode] at h1
  have : (Part.some 0 : Part ℕ) = Part.some 1 := h1
  exact absurd (Part.some_inj.1 this) (by decide)

/-- `Statement:` CONTROL: some code is universal and not self-printing (`curry (psiOf u 0) 0`). -/
theorem universal_not_selfPrints_cf : ∃ c : Code, UniversalCF c ∧ ¬ SelfPrintsCF c := by
  obtain ⟨u, hu⟩ := universal_code_cf'
  refine ⟨curry (psiOf u 0) 0, fun e n => ?_, fun h => ?_⟩
  · rw [cf_eval_curry, eval_psiOf]
    show eval u (Nat.pair e n) = _
    rw [hu]
  · have h0 := h 0
    rw [cf_eval_curry, eval_psiOf] at h0
    have h0' : eval u (Nat.pair codeIdIndex 0) = _ := h0
    rw [hu, codeIdIndex, cf_ofNatCodeCF_encodeCode, cf_eval_id] at h0'
    have he := Part.some_inj.1 h0'
    have hc : encodeCode (curry (psiOf u 0) 0) = cfCurryIndex (encodeCode (psiOf u 0)) 0 :=
      cf_encodeCode_curry _ _
    unfold cfCurryIndex at hc
    omega

/-- `Statement:` CONTROL: no code self-prints on channel `0` and runs code `e` on every channel `e`. -/
theorem unshifted_incompatible :
    ¬ ∃ c : Code, (∀ e n, eval c (Nat.pair e n) = eval (ofNatCodeCF e) n) ∧ SelfPrintsCF c := by
  rintro ⟨c, hU, hS⟩
  have h0 := (hS 0).symm.trans (hU 0 0)
  have hz : ofNatCodeCF 0 = Code.zero := cf_ofNatCodeCF_encodeCode Code.zero
  rw [hz] at h0
  have he : encodeCode c = 0 := Part.some_inj.1 h0
  have hc : c = Code.zero := by
    have := cf_ofNatCodeCF_encodeCode c
    rw [he, hz] at this
    exact this.symm
  subst hc
  have h1 := hU (encodeCode Code.succ) 0
  rw [cf_ofNatCodeCF_encodeCode] at h1
  have : (Part.some 0 : Part ℕ) = Part.some 1 := h1
  exact absurd (Part.some_inj.1 this) (by decide)

-- Statement: `stmtSelfrefUniversal` carries `Classical.choice` and `stmtSelfrefUniversalCF` does
-- not (`PurityCheck`): in the bins of `ZeroParadox/Category/ChoiceCannotBe.md`,
-- `selfref_universal_exists` is STATEMENT-CARRIED, and its restatement, equivalent code by code
-- (`selfPrints_iff_cf`, `universal_iff_cf`), has a proof without it (`selfref_universal_exists_cf`).

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms CodeCont
#print axioms CodeState
#print axioms codeStep
#print axioms codeRun
#print axioms codeRun_add
#print axioms precLoopSem
#print axioms rfindSem
#print axioms codeContSem
#print axioms codeSem
#print axioms eval_pair_bind_eq
#print axioms precLoopSem_rec
#print axioms eval_prec_eq_precLoopSem
#print axioms mem_rfindSem
#print axioms rfindSem_ge
#print axioms rfindSem_unfold
#print axioms eval_rfind'_eq_rfindSem
#print axioms codeStep_sem
#print axioms codeRun_sem
#print axioms codeRun_sound
#print axioms CodeReaches
#print axioms CodeReaches.refl
#print axioms CodeReaches.trans
#print axioms CodeReaches.of_step
#print axioms codeRun_prec_complete
#print axioms codeRun_rfind_complete
#print axioms codeRun_complete
#print axioms codeRun_halts_iff
#print axioms natSel
#print axioms natSel_zero
#print axioms natSel_succ
#print axioms natPrimrec_id
#print axioms natPrimrec_const
#print axioms natPrimrec_pair
#print axioms natPrimrec_fst
#print axioms natPrimrec_snd
#print axioms natPrimrec_succ
#print axioms cf_primrec_casesOn'
#print axioms natPrimrec_sel
#print axioms natPrimrec_pred_self
#print axioms natPrimrec_pred
#print axioms natPrimrec_sub_const
#print axioms natPrimrec_add
#print axioms natPrimrec_rec
#print axioms boddNat
#print axioms div2Nat
#print axioms natPrimrec_boddNat
#print axioms natPrimrec_boddNat_comp
#print axioms natPrimrec_div2Nat
#print axioms natPrimrec_div2Nat_comp
#print axioms boddNat_eq
#print axioms div2Nat_eq
#print axioms boddNat_div2Nat_eq
#print axioms codeTag
#print axioms codeArg
#print axioms natPrimrec_codeTag
#print axioms natPrimrec_codeArg
#print axioms codeTag_add_four
#print axioms codeArg_add_four
#print axioms codeTag_pair
#print axioms codeTag_comp
#print axioms codeTag_prec
#print axioms codeTag_rfind'
#print axioms encCont
#print axioms encEv
#print axioms encRet
#print axioms encState
#print axioms natCase3
#print axioms natCase6
#print axioms natCase8
#print axioms natPrimrec_natCase3
#print axioms natPrimrec_natCase6
#print axioms natPrimrec_natCase8
#print axioms evStepNat
#print axioms retStepNat
#print axioms codeStepNat
#print axioms natPrimrec_evStepNat
#print axioms natPrimrec_retStepNat
#print axioms natPrimrec_codeStepNat
#print axioms natCase3_0
#print axioms natCase3_1
#print axioms natCase3_2
#print axioms natCase6_0
#print axioms natCase6_1
#print axioms natCase6_2
#print axioms natCase6_3
#print axioms natCase6_4
#print axioms natCase6_5
#print axioms natCase8_0
#print axioms natCase8_1
#print axioms natCase8_2
#print axioms natCase8_3
#print axioms natCase8_4
#print axioms natCase8_5
#print axioms natCase8_6
#print axioms natCase8_7
#print axioms codeTag_zero
#print axioms codeTag_succ
#print axioms codeTag_left
#print axioms codeTag_right
#print axioms succ_sub_one_rfl
#print axioms codeStepNat_enc
#print axioms codeIterNat
#print axioms natPrimrec_codeIterNat
#print axioms codeIterNat_enc
#print axioms doneTest
#print axioms doneTest_enc
#print axioms initNat
#print axioms initNat_eq
#print axioms haltSearch
#print axioms haltValue
#print axioms natPrimrec_initNat
#print axioms natPrimrec_iterInit
#print axioms natPrimrec_haltSearch
#print axioms natPrimrec_haltValue
#print axioms univ_natPartrec_raw
#print axioms univ_value_eq
#print axioms univ_natPartrec
#print axioms cf_exists_code_mp
#print axioms universal_code_cf
#print axioms universal_code_cf'
#print axioms discussion142_answer
#print axioms zero_not_universal
#print axioms SelfPrintsCF
#print axioms UniversalCF
#print axioms UniversalEnc
#print axioms stmtSelfrefUniversal
#print axioms stmtSelfrefUniversalCF
#print axioms stmtSelfrefUniversalEnc
#print axioms selfPrints_iff_cf
#print axioms universal_iff_cf
#print axioms universalCF_iff_enc
#print axioms codeIdIndex
#print axioms selDValue
#print axioms selDBase
#print axioms selDStep
#print axioms selDArg
#print axioms selD
#print axioms eval_selD
#print axioms psiOf
#print axioms eval_psiOf
#print axioms selfUniv
#print axioms selfUniv_spec
#print axioms selfref_universal_exists_cf
#print axioms selfref_universal_exists_enc
#print axioms selfref_universal_exists_verbatim
#print axioms cf_left_le_pair
#print axioms cf_right_le_pair
#print axioms encodeCode_lt_comp_left
#print axioms encodeCode_lt_comp_right
#print axioms encodeCode_lt_pair_left
#print axioms lt_encodeCode_selfUniv
#print axioms selfref_universal_unbounded_cf
#print axioms cfFinBound
#print axioms cf_le_finBound
#print axioms selfref_universal_infinite_cf
#print axioms zero_selfPrints_not_universal
#print axioms universal_not_selfPrints_cf
#print axioms unshifted_incompatible
-- Mathlib constants that entries above share a type with, then the corpus original
-- `selfref_universal_exists`.
#print axioms Nat.Primrec.casesOn'
#print axioms Nat.Partrec.Code.exists_code
#print axioms Nat.left_le_pair
#print axioms Nat.right_le_pair
#print axioms selfref_universal_exists

end PurityCheck
