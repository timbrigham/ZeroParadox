/-
================================================================================
VENDORED FROM GuardianEngineAI/corpus - provenance (Zero Paradox project)
================================================================================
Source      : Corpus/Relation.lean
Upstream    : https://github.com/GuardianEngineAI/corpus (branch main)
Commit      : 89d2876275ca7e9b935442b4cb20a0e1833225ea (blob 71dfda33, verified 2026-10-23)
Upstream pin: leanprover/lean4:v4.28.0; ported to this repository's v4.30.0-rc2
Author      : Larsen James Close
License     : Apache 2.0; full text in `LICENSE` beside this file

Why vendored, and the full list of changes: the provenance block of `Audit.lean` in this folder.
Changes to THIS file:
  1. The Apache-2.0 header below was added; upstream's copy of this file carries none, so it is
     copied from its siblings and the repository LICENSE. (local edit; candidate to offer upstream)
  The body below the header is upstream's, unchanged.
================================================================================
-/

/-
Copyright (c) 2026 Larsen James Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen James Close
-/
import Lean

/-!
# Same-statement replacement relations

This checker witnesses correspondence of theorem *types* in the loaded Lean
environment. It does not compare proof terms, prove axiom minimality, or certify
preservation of executable witnesses. Kernel probes are checked in a discarded
environment: no probe declaration or axiom enters the audited mathematics.
-/

open Lean

namespace Corpus.Relation

/-- An implication in a possibly open telescope. The new binder shifts every
loose variable in the conclusion, including references to shared parameters. -/
private def arrow (source target : Expr) : Expr :=
  .forallE .anonymous source (target.liftLooseBVars 0 1) .default

/-- Accept global `T → T` or a pointwise bridge under a prefix of T's explicit
forall telescope. No new parameter or hypothesis is inserted along that prefix. -/
private def bridgeTypes (type : Expr) : List Expr :=
  arrow type type :: match type with
  | .forallE n domain body bi =>
      (bridgeTypes body).map (Expr.forallE n domain · bi)
  | _ => []

private def theoremInfo (role : String) (name : Name) : CoreM TheoremVal := do
  match ← getConstInfo name with
  | .thmInfo info => return info
  | _ => throwError "same-statement {role} must be a theorem: {name}"

/-- Type-check a probe through the kernel, without changing the caller's
environment. A failure, including an exhausted kernel budget, never certifies. -/
private def kernelAccepts (levels : List Name) (type value : Expr) : CoreM Bool := do
  let name ← mkFreshUserName `Corpus.Relation.probe
  let decl := Declaration.thmDecl { name, levelParams := levels, type, value }
  let env := (← getEnv).toKernelEnv
  match env.addDeclCore 200000 decl none with
  | .ok _ => return true
  | .error (.declTypeMismatch ..) | .error (.exprTypeMismatch ..) |
      .error (.appTypeMismatch ..) => return false
  | .error error =>
      -- Exhaustion, interruption, or a broken environment is not evidence of
      -- different types. Preserve that failure rather than mislabeling it.
      ofExceptKernelException (.error error)

/-- Check the three named theorem interfaces before an audit may report a
`same-statement` relation. Universes stay universally quantified and positionally
aligned; they are never instantiated at a convenient common level. -/
def check (source bridge target : Name) : CoreM Unit := do
  let newInfo ← theoremInfo "source" source
  let oldInfo ← theoremInfo "target" target
  let bridgeInfo ← theoremInfo "bridge" bridge
  let levels := newInfo.levelParams
  unless oldInfo.levelParams.length == levels.length &&
      bridgeInfo.levelParams.length == levels.length do
    throwError "same-statement universe arity mismatch: {source}, {bridge}, {target}"
  let universeArgs := levels.map Level.param
  let oldType := oldInfo.type.instantiateLevelParams oldInfo.levelParams universeArgs
  let newType := newInfo.type
  -- Checking an identity FUNCTION between proposition types forces the kernel
  -- to check conversion of those types. Comparing their proof terms would not.
  let identity := Expr.lam `w newType (.bvar 0) .default
  unless ← kernelAccepts levels (arrow newType oldType) identity do
    throwError "same-statement theorem type mismatch: {source} and {target}"
  let bridgeValue := mkConst bridge universeArgs
  for expected in bridgeTypes newType do
    if ← kernelAccepts levels expected bridgeValue then return
  throwError "same-statement bridge endpoints mismatch: {bridge} for {source} and {target}"

/-- A checked report bound to the three declaration names in this environment.
The JSON is consumed only as upstream audit output, never as a submitter proof. -/
def report (source bridge target : Name) : CoreM Json := do
  check source bridge target
  return Json.mkObj [
    ("kind", toJson "same-statement"),
    ("source", toJson source.toString),
    ("target", toJson target.toString),
    ("bridge", toJson bridge.toString),
    ("checked", toJson true)]

end Corpus.Relation
