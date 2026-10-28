import ZeroParadox.Computability.KleeneChoiceFree
import ZeroParadox.Computability.UniversalChoiceFree
import ZeroParadox.Vendored.CorpusAudit.Audit

/-!
# Axiom ledger: declared axiom profiles, checked on every build

## Engineer's Take

This file is a gate on what we claim about which axioms our proofs use. We make use of what Larsen Close built: his auditor sits in the vendored folder, because that is what the folder is for, third-party work, ported to a slightly newer version of Lean. That also lets us make edits locally and port them back to a copy of his repo, and if anything is worth submitting, open a pull request. I like having this as a dedicated CI gate, the same as the minimal core, so we can run it on illustrated.

---

`Statement:` elaborating this file fails unless every row below holds when recomputed by the
auditor of `GuardianEngineAI/corpus` (vendored in `ZeroParadox/Vendored/CorpusAudit/`), and unless
every theorem of `ZeroParadox/Computability/KleeneChoiceFree.lean`, of
`ZeroParadox/Computability/UniversalChoiceFree.lean` and of this file has a row.
-/

open Lean

namespace ZeroParadox.AxiomLedger

/-! ## The two halves of `cf_sqrt_isSqrt`, as theorems with the predecessors' types -/

/-- `Statement:` `Nat.sqrt n * Nat.sqrt n ≤ n`, the first half of `cf_sqrt_isSqrt`. -/
theorem cf_sqrt_le (n : ℕ) : Nat.sqrt n * Nat.sqrt n ≤ n := (ZeroParadox.cf_sqrt_isSqrt n).1

/-- `Statement:` `n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1)`, the second half of `cf_sqrt_isSqrt`. -/
theorem cf_lt_succ_sqrt (n : ℕ) : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) :=
  (ZeroParadox.cf_sqrt_isSqrt n).2

/-! ## Bridges: the entry's type, as hypothesis, gives the predecessor's -/

/-- `Statement:` `cf_unpair_pair`'s type implies `Nat.unpair_pair`'s. -/
theorem bridge_unpair_pair (new : type_of% @ZeroParadox.cf_unpair_pair) :
    type_of% @Nat.unpair_pair := new
/-- `Statement:` `cf_pair_unpair`'s type implies `Nat.pair_unpair`'s. -/
theorem bridge_pair_unpair (new : type_of% @ZeroParadox.cf_pair_unpair) :
    type_of% @Nat.pair_unpair := new
/-- `Statement:` `cf_sqrt_le`'s type implies `Nat.sqrt_le`'s. -/
theorem bridge_sqrt_le (new : type_of% @cf_sqrt_le) : type_of% @Nat.sqrt_le := new
/-- `Statement:` `cf_lt_succ_sqrt`'s type implies `Nat.lt_succ_sqrt`'s. -/
theorem bridge_lt_succ_sqrt (new : type_of% @cf_lt_succ_sqrt) :
    type_of% @Nat.lt_succ_sqrt := new
/-- `Statement:` `cf_sqrt_iter_sq_le`'s type implies `Nat.sqrt.iter_sq_le`'s. -/
theorem bridge_sqrt_iter_sq_le (new : type_of% @ZeroParadox.cf_sqrt_iter_sq_le) :
    type_of% @Nat.sqrt.iter_sq_le := new
/-- `Statement:` `cf_sqrt_lt_iter_succ_sq`'s type implies `Nat.sqrt.lt_iter_succ_sq`'s. -/
theorem bridge_sqrt_lt_iter_succ_sq (new : type_of% @ZeroParadox.cf_sqrt_lt_iter_succ_sq) :
    type_of% @Nat.sqrt.lt_iter_succ_sq := new
/-- `Statement:` `cf_sqrt_le_self`'s type implies `Nat.sqrt_le_self`'s. -/
theorem bridge_sqrt_le_self (new : type_of% @ZeroParadox.cf_sqrt_le_self) :
    type_of% @Nat.sqrt_le_self := new
/-- `Statement:` `cf_unpair_left_le`'s type implies `Nat.unpair_left_le`'s. -/
theorem bridge_unpair_left_le (new : type_of% @ZeroParadox.cf_unpair_left_le) :
    type_of% @Nat.unpair_left_le := new
/-- `Statement:` `cf_unpair_right_le`'s type implies `Nat.unpair_right_le`'s. -/
theorem bridge_unpair_right_le (new : type_of% @ZeroParadox.cf_unpair_right_le) :
    type_of% @Nat.unpair_right_le := new
/-- `Statement:` `cf_div2_val`'s type implies `Nat.div2_val`'s. -/
theorem bridge_div2_val (new : type_of% @ZeroParadox.cf_div2_val) :
    type_of% @Nat.div2_val := new
/-- `Statement:` `cf_eval_id`'s type implies `Nat.Partrec.Code.eval_id`'s. -/
theorem bridge_eval_id (new : type_of% @ZeroParadox.cf_eval_id) :
    type_of% @Nat.Partrec.Code.eval_id := new
/-- `Statement:` `cf_eval_curry`'s type implies `Nat.Partrec.Code.eval_curry`'s. -/
theorem bridge_eval_curry (new : type_of% @ZeroParadox.cf_eval_curry) :
    type_of% @Nat.Partrec.Code.eval_curry := new
/-- `Statement:` `cf_eval_prec_zero`'s type implies `Nat.Partrec.Code.eval_prec_zero`'s. -/
theorem bridge_eval_prec_zero (new : type_of% @ZeroParadox.cf_eval_prec_zero) :
    type_of% @Nat.Partrec.Code.eval_prec_zero := new
/-- `Statement:` `cf_eval_prec_succ`'s type implies `Nat.Partrec.Code.eval_prec_succ`'s. -/
theorem bridge_eval_prec_succ (new : type_of% @ZeroParadox.cf_eval_prec_succ) :
    type_of% @Nat.Partrec.Code.eval_prec_succ := new

/-! ## The ledger -/

/-- `Statement:` the replacement rows: entry declared `[Quot.sound, propext]`, bridge `[]`,
Mathlib predecessor `Corpus.Audit.stock`, i.e. `[Classical.choice, Quot.sound, propext]`. -/
def replacements : List Corpus.Audit.Row :=
  let rep (entry bridge predecessor : Name) : Corpus.Audit.Row :=
    { entry, entryProfile := ["Quot.sound", "propext"], bridge, bridgeProfile := [],
      predecessor, predecessorProfile := Corpus.Audit.stock }
  [ rep `ZeroParadox.cf_unpair_pair `ZeroParadox.AxiomLedger.bridge_unpair_pair `Nat.unpair_pair,
    rep `ZeroParadox.cf_pair_unpair `ZeroParadox.AxiomLedger.bridge_pair_unpair `Nat.pair_unpair,
    rep `ZeroParadox.AxiomLedger.cf_sqrt_le `ZeroParadox.AxiomLedger.bridge_sqrt_le `Nat.sqrt_le,
    rep `ZeroParadox.AxiomLedger.cf_lt_succ_sqrt `ZeroParadox.AxiomLedger.bridge_lt_succ_sqrt
      `Nat.lt_succ_sqrt,
    rep `ZeroParadox.cf_sqrt_iter_sq_le `ZeroParadox.AxiomLedger.bridge_sqrt_iter_sq_le
      `Nat.sqrt.iter_sq_le,
    rep `ZeroParadox.cf_sqrt_lt_iter_succ_sq `ZeroParadox.AxiomLedger.bridge_sqrt_lt_iter_succ_sq
      `Nat.sqrt.lt_iter_succ_sq,
    rep `ZeroParadox.cf_sqrt_le_self `ZeroParadox.AxiomLedger.bridge_sqrt_le_self
      `Nat.sqrt_le_self,
    rep `ZeroParadox.cf_unpair_left_le `ZeroParadox.AxiomLedger.bridge_unpair_left_le
      `Nat.unpair_left_le,
    rep `ZeroParadox.cf_unpair_right_le `ZeroParadox.AxiomLedger.bridge_unpair_right_le
      `Nat.unpair_right_le,
    rep `ZeroParadox.cf_div2_val `ZeroParadox.AxiomLedger.bridge_div2_val `Nat.div2_val,
    rep `ZeroParadox.cf_eval_id `ZeroParadox.AxiomLedger.bridge_eval_id
      `Nat.Partrec.Code.eval_id,
    rep `ZeroParadox.cf_eval_curry `ZeroParadox.AxiomLedger.bridge_eval_curry
      `Nat.Partrec.Code.eval_curry,
    rep `ZeroParadox.cf_eval_prec_zero `ZeroParadox.AxiomLedger.bridge_eval_prec_zero
      `Nat.Partrec.Code.eval_prec_zero,
    rep `ZeroParadox.cf_eval_prec_succ `ZeroParadox.AxiomLedger.bridge_eval_prec_succ
      `Nat.Partrec.Code.eval_prec_succ ]

-- Reading: a row compares two supplied proofs of one statement. It does not show that our
-- profile is the least possible, nor that the predecessor's statement needs `Classical.choice`.

/-- `Statement:` declared profiles for `fpCF`, every other theorem of `KleeneChoiceFree.lean`
that replaces no Mathlib lemma, and every theorem of `UniversalChoiceFree.lean`. -/
def profiles : List Corpus.Audit.ProfileRow :=
  let ours := ["Quot.sound", "propext"]
  [ ⟨`ZeroParadox.fpCF, []⟩,
    ⟨`ZeroParadox.kleene_cf, ours⟩,
    ⟨`ZeroParadox.kleene_cf_fixed₂, ours⟩,
    ⟨`ZeroParadox.quine_succ_cf, ours⟩,
    ⟨`ZeroParadox.const_not_quine_succ, ours⟩,
    ⟨`ZeroParadox.cf_amgm, ours⟩,
    ⟨`ZeroParadox.cf_sq_succ, ours⟩,
    ⟨`ZeroParadox.cf_sqrt_isSqrt, ours⟩,
    ⟨`ZeroParadox.cf_sqrt_eq_of, ours⟩,
    ⟨`ZeroParadox.cf_bodd_add_div2, ours⟩,
    ⟨`ZeroParadox.cf_eval_succ, []⟩,
    ⟨`ZeroParadox.cf_eval_left, ours⟩,
    ⟨`ZeroParadox.cf_eval_right, ours⟩,
    ⟨`ZeroParadox.cf_eval_pair, ours⟩,
    ⟨`ZeroParadox.cf_eval_comp, ours⟩,
    ⟨`ZeroParadox.cf_eval_comp_some, ours⟩,
    ⟨`ZeroParadox.cf_eval_prec_total, ours⟩,
    ⟨`ZeroParadox.cf_eval_unary, ours⟩,
    ⟨`ZeroParadox.cf_eval_add4, ours⟩,
    ⟨`ZeroParadox.cf_eval_double, ours⟩,
    ⟨`ZeroParadox.cf_encodeCode_const_succ, []⟩,
    ⟨`ZeroParadox.cf_eval_encConst, ours⟩,
    ⟨`ZeroParadox.cf_encodeCode_curry, []⟩,
    ⟨`ZeroParadox.cf_eval_diagIndex, ours⟩,
    ⟨`ZeroParadox.cf_eval_diag, ours⟩,
    ⟨`ZeroParadox.cf_le_encodeCode_const, ours⟩,
    ⟨`ZeroParadox.cf_div2_div2_lt, ours⟩,
    ⟨`ZeroParadox.ofNatCodeCF, ours⟩,
    ⟨`ZeroParadox.ofNatCodeCF.eq_1, ours⟩,
    ⟨`ZeroParadox.ofNatCodeCF.eq_2, ours⟩,
    ⟨`ZeroParadox.ofNatCodeCF.eq_3, ours⟩,
    ⟨`ZeroParadox.ofNatCodeCF.eq_4, ours⟩,
    ⟨`ZeroParadox.ofNatCodeCF.eq_5, ours⟩,
    ⟨`ZeroParadox.cf_encodeCode_ofNatCodeCF, ours⟩,
    ⟨`ZeroParadox.cf_bodd_div2_eq, ours⟩,
    ⟨`ZeroParadox.cf_ofNatCodeCF_step, ours⟩,
    ⟨`ZeroParadox.cf_ofNatCodeCF_encodeCode, ours⟩,
    ⟨`ZeroParadox.ofNatCodeCF_eq_ofNatCode, Corpus.Audit.stock⟩,
    ⟨`ZeroParadox.stmtOfNatCodeCFEq, Corpus.Audit.stock⟩,
    ⟨`ZeroParadox.boddNat_div2Nat_eq, ours⟩,
    ⟨`ZeroParadox.boddNat_eq, []⟩,
    ⟨`ZeroParadox.cf_exists_code_mp, ours⟩,
    ⟨`ZeroParadox.cf_primrec_casesOn', ours⟩,
    ⟨`ZeroParadox.codeArg_add_four, []⟩,
    ⟨`ZeroParadox.CodeCont.brecOn.eq, []⟩,
    ⟨`ZeroParadox.codeIterNat_enc, ours⟩,
    ⟨`ZeroParadox.CodeReaches.of_step, []⟩,
    ⟨`ZeroParadox.CodeReaches.refl, []⟩,
    ⟨`ZeroParadox.CodeReaches.trans, []⟩,
    ⟨`ZeroParadox.codeRun_add, []⟩,
    ⟨`ZeroParadox.codeRun_complete, ours⟩,
    ⟨`ZeroParadox.codeRun_halts_iff, ours⟩,
    ⟨`ZeroParadox.codeRun_prec_complete, ["propext"]⟩,
    ⟨`ZeroParadox.codeRun_rfind_complete, ours⟩,
    ⟨`ZeroParadox.codeRun_sem, ours⟩,
    ⟨`ZeroParadox.codeRun_sound, ours⟩,
    ⟨`ZeroParadox.codeStep.eq_1, []⟩,
    ⟨`ZeroParadox.codeStep.eq_10, []⟩,
    ⟨`ZeroParadox.codeStep.eq_11, []⟩,
    ⟨`ZeroParadox.codeStep.eq_12, []⟩,
    ⟨`ZeroParadox.codeStep.eq_13, []⟩,
    ⟨`ZeroParadox.codeStep.eq_14, []⟩,
    ⟨`ZeroParadox.codeStep.eq_15, []⟩,
    ⟨`ZeroParadox.codeStep.eq_16, []⟩,
    ⟨`ZeroParadox.codeStep.eq_17, []⟩,
    ⟨`ZeroParadox.codeStep.eq_2, []⟩,
    ⟨`ZeroParadox.codeStep.eq_3, []⟩,
    ⟨`ZeroParadox.codeStep.eq_4, []⟩,
    ⟨`ZeroParadox.codeStep.eq_5, []⟩,
    ⟨`ZeroParadox.codeStep.eq_6, []⟩,
    ⟨`ZeroParadox.codeStep.eq_7, []⟩,
    ⟨`ZeroParadox.codeStep.eq_8, []⟩,
    ⟨`ZeroParadox.codeStep.eq_9, []⟩,
    ⟨`ZeroParadox.codeStep_sem, ours⟩,
    ⟨`ZeroParadox.codeStepNat.eq_1, []⟩,
    ⟨`ZeroParadox.codeStepNat_enc, ours⟩,
    ⟨`ZeroParadox.codeTag_add_four, []⟩,
    ⟨`ZeroParadox.codeTag_comp, ours⟩,
    ⟨`ZeroParadox.codeTag_left, []⟩,
    ⟨`ZeroParadox.codeTag_pair, ours⟩,
    ⟨`ZeroParadox.codeTag_prec, ours⟩,
    ⟨`ZeroParadox.codeTag_rfind', ours⟩,
    ⟨`ZeroParadox.codeTag_right, []⟩,
    ⟨`ZeroParadox.codeTag_succ, []⟩,
    ⟨`ZeroParadox.codeTag_zero, []⟩,
    ⟨`ZeroParadox.discussion142_answer, ours⟩,
    ⟨`ZeroParadox.div2Nat_eq, ["propext"]⟩,
    ⟨`ZeroParadox.doneTest.eq_1, []⟩,
    ⟨`ZeroParadox.doneTest_enc, ours⟩,
    ⟨`ZeroParadox.encCont.eq_1, []⟩,
    ⟨`ZeroParadox.encCont.eq_2, []⟩,
    ⟨`ZeroParadox.encCont.eq_3, []⟩,
    ⟨`ZeroParadox.encCont.eq_4, []⟩,
    ⟨`ZeroParadox.encCont.eq_5, []⟩,
    ⟨`ZeroParadox.encCont.eq_6, []⟩,
    ⟨`ZeroParadox.encState.eq_1, []⟩,
    ⟨`ZeroParadox.encState.eq_2, []⟩,
    ⟨`ZeroParadox.encState.eq_3, []⟩,
    ⟨`ZeroParadox.eval_pair_bind_eq, ours⟩,
    ⟨`ZeroParadox.eval_prec_eq_precLoopSem, ours⟩,
    ⟨`ZeroParadox.eval_rfind'_eq_rfindSem, []⟩,
    ⟨`ZeroParadox.evStepNat.eq_1, []⟩,
    ⟨`ZeroParadox.haltSearch.eq_1, []⟩,
    ⟨`ZeroParadox.haltValue.eq_1, []⟩,
    ⟨`ZeroParadox.initNat.eq_1, []⟩,
    ⟨`ZeroParadox.initNat_eq, ours⟩,
    ⟨`ZeroParadox.mem_rfindSem, ["propext"]⟩,
    ⟨`ZeroParadox.natCase3_0, []⟩,
    ⟨`ZeroParadox.natCase3_1, []⟩,
    ⟨`ZeroParadox.natCase3_2, []⟩,
    ⟨`ZeroParadox.natCase6_0, []⟩,
    ⟨`ZeroParadox.natCase6_1, []⟩,
    ⟨`ZeroParadox.natCase6_2, []⟩,
    ⟨`ZeroParadox.natCase6_3, []⟩,
    ⟨`ZeroParadox.natCase6_4, []⟩,
    ⟨`ZeroParadox.natCase6_5, []⟩,
    ⟨`ZeroParadox.natCase8_0, []⟩,
    ⟨`ZeroParadox.natCase8_1, []⟩,
    ⟨`ZeroParadox.natCase8_2, []⟩,
    ⟨`ZeroParadox.natCase8_3, []⟩,
    ⟨`ZeroParadox.natCase8_4, []⟩,
    ⟨`ZeroParadox.natCase8_5, []⟩,
    ⟨`ZeroParadox.natCase8_6, []⟩,
    ⟨`ZeroParadox.natCase8_7, []⟩,
    ⟨`ZeroParadox.natPrimrec_add, ours⟩,
    ⟨`ZeroParadox.natPrimrec_boddNat, ours⟩,
    ⟨`ZeroParadox.natPrimrec_boddNat_comp, ours⟩,
    ⟨`ZeroParadox.natPrimrec_codeArg, ours⟩,
    ⟨`ZeroParadox.natPrimrec_codeIterNat, ours⟩,
    ⟨`ZeroParadox.natPrimrec_codeStepNat, ours⟩,
    ⟨`ZeroParadox.natPrimrec_codeTag, ours⟩,
    ⟨`ZeroParadox.natPrimrec_const, []⟩,
    ⟨`ZeroParadox.natPrimrec_div2Nat, ours⟩,
    ⟨`ZeroParadox.natPrimrec_div2Nat_comp, ours⟩,
    ⟨`ZeroParadox.natPrimrec_evStepNat, ours⟩,
    ⟨`ZeroParadox.natPrimrec_fst, []⟩,
    ⟨`ZeroParadox.natPrimrec_haltSearch, ours⟩,
    ⟨`ZeroParadox.natPrimrec_haltValue, ours⟩,
    ⟨`ZeroParadox.natPrimrec_id, ours⟩,
    ⟨`ZeroParadox.natPrimrec_initNat, ours⟩,
    ⟨`ZeroParadox.natPrimrec_iterInit, ours⟩,
    ⟨`ZeroParadox.natPrimrec_natCase3, ours⟩,
    ⟨`ZeroParadox.natPrimrec_natCase6, ours⟩,
    ⟨`ZeroParadox.natPrimrec_natCase8, ours⟩,
    ⟨`ZeroParadox.natPrimrec_pair, []⟩,
    ⟨`ZeroParadox.natPrimrec_pred, ours⟩,
    ⟨`ZeroParadox.natPrimrec_pred_self, ours⟩,
    ⟨`ZeroParadox.natPrimrec_rec, ours⟩,
    ⟨`ZeroParadox.natPrimrec_retStepNat, ours⟩,
    ⟨`ZeroParadox.natPrimrec_sel, ours⟩,
    ⟨`ZeroParadox.natPrimrec_snd, []⟩,
    ⟨`ZeroParadox.natPrimrec_sub_const, ours⟩,
    ⟨`ZeroParadox.natPrimrec_succ, []⟩,
    ⟨`ZeroParadox.natSel_succ, []⟩,
    ⟨`ZeroParadox.natSel_zero, []⟩,
    ⟨`ZeroParadox.precLoopSem.eq_1, []⟩,
    ⟨`ZeroParadox.precLoopSem.eq_2, []⟩,
    ⟨`ZeroParadox.precLoopSem_rec, ours⟩,
    ⟨`ZeroParadox.retStepNat.eq_1, []⟩,
    ⟨`ZeroParadox.rfindSem_ge, ["propext"]⟩,
    ⟨`ZeroParadox.rfindSem_unfold, ours⟩,
    ⟨`ZeroParadox.succ_sub_one_rfl, []⟩,
    ⟨`ZeroParadox.univ_natPartrec, ours⟩,
    ⟨`ZeroParadox.univ_natPartrec_raw, ours⟩,
    ⟨`ZeroParadox.univ_value_eq, ours⟩,
    ⟨`ZeroParadox.universal_code_cf, ours⟩,
    ⟨`ZeroParadox.universal_code_cf', ours⟩,
    ⟨`ZeroParadox.zero_not_universal, []⟩,
    ⟨`ZeroParadox.stmtSelfrefUniversal, Corpus.Audit.stock⟩,
    ⟨`ZeroParadox.stmtSelfrefUniversalCF, ours⟩,
    ⟨`ZeroParadox.stmtSelfrefUniversalEnc, []⟩,
    ⟨`ZeroParadox.selfPrints_iff_cf, Corpus.Audit.stock⟩,
    ⟨`ZeroParadox.universal_iff_cf, Corpus.Audit.stock⟩,
    ⟨`ZeroParadox.universalCF_iff_enc, ours⟩,
    ⟨`ZeroParadox.codeIdIndex.eq_1, []⟩,
    ⟨`ZeroParadox.selfUniv.eq_1, []⟩,
    ⟨`ZeroParadox.eval_selD, ours⟩,
    ⟨`ZeroParadox.eval_psiOf, ours⟩,
    ⟨`ZeroParadox.selfUniv_spec, ours⟩,
    ⟨`ZeroParadox.selfref_universal_exists_cf, ours⟩,
    ⟨`ZeroParadox.selfref_universal_exists_enc, ours⟩,
    ⟨`ZeroParadox.selfref_universal_exists_verbatim, ours⟩,
    ⟨`ZeroParadox.cf_left_le_pair, []⟩,
    ⟨`ZeroParadox.cf_right_le_pair, ["propext"]⟩,
    ⟨`ZeroParadox.encodeCode_lt_comp_left, ours⟩,
    ⟨`ZeroParadox.encodeCode_lt_comp_right, ours⟩,
    ⟨`ZeroParadox.encodeCode_lt_pair_left, ours⟩,
    ⟨`ZeroParadox.lt_encodeCode_selfUniv, ours⟩,
    ⟨`ZeroParadox.selfref_universal_unbounded_cf, ours⟩,
    ⟨`ZeroParadox.cf_le_finBound, ["propext"]⟩,
    ⟨`ZeroParadox.selfref_universal_infinite_cf, ours⟩,
    ⟨`ZeroParadox.zero_selfPrints_not_universal, ours⟩,
    ⟨`ZeroParadox.universal_not_selfPrints_cf, ours⟩,
    ⟨`ZeroParadox.unshifted_incompatible, ours⟩ ]

/-! ## The run

One tab-separated `LEDGER` line per row, for `scripts/axiom_ledger_report.py` to tabulate, then
the vendored audit, which throws on any failure. The verdict is the throw, never the table. -/

#eval show CoreM Unit from do
  let fmt := Corpus.Audit.fmt
  let line (cols : List String) : IO Unit := IO.println ("LEDGER\t" ++ "\t".intercalate cols)
  line ["kind", "source", "predecessor", "declared", "computed", "predecessor_computed", "verdict"]
  for r in replacements do
    let related ← try
        Corpus.Relation.check r.entry r.bridge r.predecessor
        pure true
      catch _ => pure false
    let e ← Corpus.Audit.profile r.entry
    let b ← Corpus.Audit.profile r.bridge
    let p ← Corpus.Audit.profile r.predecessor
    let combined := (e ++ b).eraseDups.mergeSort (· ≤ ·)
    let ok := related && e == r.entryProfile && b == r.bridgeProfile &&
      p == r.predecessorProfile && Corpus.Audit.strictlyBelow combined p &&
      !([e, b, p].any (·.contains "sorryAx"))
    line ["replacement", r.entry.toString, r.predecessor.toString, fmt r.entryProfile, fmt e,
      fmt p, if ok then "PASS" else "FAIL"]
  for r in profiles do
    let d ← if (← getEnv).contains r.decl then Corpus.Audit.profile r.decl else pure ["(unknown)"]
    let ok := d == r.declProfile && !d.contains "sorryAx"
    line ["profile", r.decl.toString, "-", fmt r.declProfile, fmt d, "-",
      if ok then "PASS" else "FAIL"]
  let cov ← Corpus.Audit.coverageModules replacements profiles
    [`ZeroParadox.Computability.KleeneChoiceFree, `ZeroParadox.Computability.UniversalChoiceFree]
  line ["coverage",
    "ZeroParadox.Computability.KleeneChoiceFree + UniversalChoiceFree + this file", "-",
    "every theorem", s!"{cov.length} unledgered", "-", if cov.isEmpty then "PASS" else "FAIL"]
  Corpus.Audit.auditModules replacements profiles
    [`ZeroParadox.Computability.KleeneChoiceFree, `ZeroParadox.Computability.UniversalChoiceFree]

end ZeroParadox.AxiomLedger

section PurityCheck
open ZeroParadox.AxiomLedger

#print axioms cf_sqrt_le
#print axioms cf_lt_succ_sqrt
#print axioms bridge_unpair_pair
#print axioms bridge_pair_unpair
#print axioms bridge_sqrt_le
#print axioms bridge_lt_succ_sqrt
#print axioms bridge_sqrt_iter_sq_le
#print axioms bridge_sqrt_lt_iter_succ_sq
#print axioms bridge_sqrt_le_self
#print axioms bridge_unpair_left_le
#print axioms bridge_unpair_right_le
#print axioms bridge_div2_val
#print axioms bridge_eval_id
#print axioms bridge_eval_curry
#print axioms bridge_eval_prec_zero
#print axioms bridge_eval_prec_succ
#print axioms replacements
#print axioms profiles

end PurityCheck
