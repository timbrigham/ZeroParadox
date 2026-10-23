/-
================================================================================
VENDORED FROM GuardianEngineAI/corpus - provenance (Zero Paradox project)
================================================================================
Source      : Corpus/AuditChecks.lean
Upstream    : https://github.com/GuardianEngineAI/corpus (branch main)
Commit      : 89d2876275ca7e9b935442b4cb20a0e1833225ea (blob 1c5b78bc, verified 2026-10-23)
Upstream pin: leanprover/lean4:v4.28.0; ported to this repository's v4.30.0-rc2
Author      : Larsen James Close
License     : Apache 2.0 (unchanged; header retained verbatim below); full text in `LICENSE`

Why vendored, and the full list of changes: the provenance block of `Audit.lean` in this folder.
These are upstream's admission fixtures for the checker, so every build re-tests it: one valid
replacement must pass and four invalid ones must be rejected. The two `axiom`s below are
upstream's adversarial test inputs; nothing outside this file uses them.
Changes to THIS file:
  `import Corpus.Audit` renamed to this folder's path. (local edit; not for upstream)
  The body is otherwise upstream's, unchanged.
================================================================================
-/

/-
Copyright (c) 2026 Larsen James Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen James Close
-/
-- [ZP port] import path renamed.
import ZeroParadox.Vendored.CorpusAudit.Audit

/-!
# Admission boundary checks

These fixtures exercise the public audit with well-typed declarations and
accurately declared profiles. The two axioms below are adversarial test inputs,
not dependencies of the library or its admitted entries. This module is never
imported by `Corpus`.
-/

namespace Corpus.Audit.Checks

axiom predecessorFact : True
axiom additionalFact : True

theorem entry : True := True.intro
theorem predecessor : True := predecessorFact
theorem identityBridge (h : True) : True := h
theorem unrelatedPredecessor : True ∧ True := ⟨predecessorFact, predecessorFact⟩
theorem unrelatedBridge (h : False) : False := h
theorem retainsDebtBridge (_h : True) : True := predecessorFact
theorem addsDebtBridge (_h : True) : True := additionalFact

open Lean in
/-- Build an accurately disclosed fixture; wrong endpoints cannot hide behind
a deliberately incorrect profile declaration. -/
def row (entry bridge predecessor : Name) : CoreM Row := do
  return {
    entry, entryProfile := ← profile entry,
    bridge, bridgeProfile := ← profile bridge,
    predecessor, predecessorProfile := ← profile predecessor }

open Lean in
def checkAdmission : CoreM Unit := do
  let qualify (n : Name) := `Corpus.Audit.Checks ++ n
  let good ← row (qualify `entry) (qualify `identityBridge) (qualify `predecessor)
  let goodFailures ← checkRow good
  unless goodFailures.isEmpty do
    throwError "valid public replacement rejected: {goodFailures}"
  let bad : List (String × Name × Name) :=
    [ ("unrelated predecessor", `identityBridge, `unrelatedPredecessor),
      ("unrelated bridge", `unrelatedBridge, `predecessor),
      ("bridge retains predecessor debt", `retainsDebtBridge, `predecessor),
      ("bridge adds an axiom", `addsDebtBridge, `predecessor) ]
  let mut accepted : Array String := #[]
  for (label, bridge, target) in bad do
    let fixture ← row (qualify `entry) (qualify bridge) (qualify target)
    let passed ← try
      pure (← checkRow fixture).isEmpty
    catch error =>
      let message ← error.toMessageData.toString
      unless message.startsWith "same-statement " do throw error
      pure false
    if passed then accepted := accepted.push label
  unless accepted.isEmpty do
    throwError "invalid public replacements accepted: {accepted}"
  IO.println s!"public admission checks: 1 valid case accepted, {bad.length} invalid cases rejected"

#eval checkAdmission

end Corpus.Audit.Checks
