/-
================================================================================
VENDORED FROM GuardianEngineAI/corpus - provenance and rationale (Zero Paradox project)
================================================================================
Source      : Corpus/Audit.lean (this file); with Corpus/Relation.lean and
              Corpus/AuditChecks.lean, vendored beside it in this folder
Upstream    : https://github.com/GuardianEngineAI/corpus (branch main)
Commit      : 89d2876275ca7e9b935442b4cb20a0e1833225ea, 2026-09-08 (blob ids of all three
              files verified against that commit's tree, 2026-10-23)
Upstream pin: leanprover/lean4:v4.28.0, no package dependencies (core Lean only)
Ported to   : leanprover/lean4:v4.30.0-rc2 (this repository's pin)
Author      : Larsen James Close, 2026 (copyright header retained verbatim below)
License     : Apache 2.0 (unchanged); full text in `LICENSE` beside this file
Namespace   : upstream's `Corpus.*`, kept so a local edit diffs cleanly against upstream. No
              `Corpus` namespace exists in this corpus or in its Lake dependencies at the pin
              (searched 2026-10-23), and a later clash would fail the build, not pass silently.

WHY THIS FILE IS VENDORED
  It is the checking half of an axiom-profile ledger gate. For each ledger row it recomputes,
  with `Lean.collectAxioms`, the axioms a declaration reaches and compares them with the row's
  declared profile, and it has the kernel confirm that a replacement theorem states exactly
  what its predecessor states. `ZeroParadox/Meta/AxiomLedger.lean` holds our ledger and runs
  it, so a profile that drifts (on a Mathlib bump, say) fails the build instead of a comment
  going stale. Upstream hard-codes its own ledger into this module; the edits below separate
  the checker from the data so another library can supply its own.

CHANGES FROM UPSTREAM (port-probe numbering; marked inline with `-- [ZP port Pn]`)
  1. Relation.lean gains the Apache-2.0 header its siblings carry. (local edit; candidate to offer upstream)
  2. Data split from machinery: no `import Corpus`, no hard-coded `ledger`, no `#eval audit`. (local edit; candidate to offer upstream)
  3. Coverage scope is an argument (`inScope`, `inModulesOrMain`), not the `Corpus` prefix. (local edit; candidate to offer upstream)
  4. `ProfileRow`: a declared profile for a definition or a theorem that replaces nothing. (local edit; candidate to offer upstream)
  5. `coverageModules`: coverage over named modules' constants, 12 ms against 121 s for the whole-environment walk under Mathlib. (local edit; candidate to offer upstream)
  Observed and NOT changed here (each a candidate to raise upstream):
  6. Declared profiles compare as ordered lists: the right set in the wrong order fails.
  7. A failed relation check throws, so it hides every later row's findings.
  8. `isAux` exempts by spelling, so a hand-written `foo.proof_1` escapes coverage; upstream
     PR #7 replaces it.
  Local only, not for upstream: import paths renamed to this folder (`-- [ZP port]`).
  Upstream's v4.28.0 sources compiled and ran unchanged on v4.30.0-rc2 (probe, 2026-10-23).
  Full account: `.claude-local/notes/auditor_port_probe_2026-10-23.md` (private).
================================================================================
-/

/-
Copyright (c) 2026 Larsen James Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen James Close
-/
-- [ZP port P2] `import Corpus` dropped; [ZP port] import path renamed.
import ZeroParadox.Vendored.CorpusAudit.Relation
import Lean

/-!
# The replacement and axiom-profile audit

The second decisive gate (the first is `lake build`, the kernel). For every
ledger row this audit recomputes, from the kernel environment via
`Lean.collectAxioms`:

1. the entry's profile — must equal the declared profile exactly;
2. the bridge's profile — must equal its declared profile exactly;
3. the predecessor's profile — the recorded fact must still hold on this
   toolchain;
4. strict narrowing — the union of the entry's and bridge's profiles must be
   a *proper* subset of the predecessor's (an inherited or newly introduced
   axiom cannot be hidden in the bridge);
5. no `sorryAx` anywhere (the kernel-level no-sorry check, superseding any
   source grep).

Before comparing profiles, the kernel checks that the three names denote
theorems, that entry and predecessor have definitionally equal statement types
with their universes positionally aligned, and that the bridge has the required
endpoints. This establishes a same-statement replacement in the loaded
environment, not axiom minimality or preservation of computational proof data.

A coverage pass then asserts every non-auxiliary theorem in scope is
ledgered — an entry added to the library but not to the ledger fails the
audit rather than escaping it.
-/

open Lean

namespace Corpus.Audit

/-- One ledger row: an admitted entry, its bridge, the core predecessor it
replaces, and the three declared axiom profiles (sorted dotted names). -/
structure Row where
  entry : Name
  entryProfile : List String
  bridge : Name
  bridgeProfile : List String
  predecessor : Name
  predecessorProfile : List String

/-- The stock profile shared by every predecessor below. -/
def stock : List String := ["Classical.choice", "Quot.sound", "propext"]

-- [ZP port P2] upstream's hard-coded `ledger` stood here; the consumer supplies it.

/-- The kernel axiom closure of `n`, as sorted dotted names. -/
def profile (n : Name) : CoreM (List String) := do
  let ax ← collectAxioms n
  return (ax.toList.map (·.toString)).mergeSort (· ≤ ·)

def fmt (xs : List String) : String :=
  "[" ++ String.intercalate ", " xs ++ "]"

def subsetOf (a b : List String) : Bool := a.all b.contains

/-- `a` is a proper subset of `b` (as sets of names). -/
def strictlyBelow (a b : List String) : Bool :=
  subsetOf a b && !(subsetOf b a)

/-- All failures for one row (empty = green). -/
def checkRow (r : Row) : CoreM (List String) := do
  Corpus.Relation.check r.entry r.bridge r.predecessor
  let e ← profile r.entry
  let b ← profile r.bridge
  let p ← profile r.predecessor
  let combined := (e ++ b).eraseDups.mergeSort (· ≤ ·)
  let mut fails : List String := []
  if e ≠ r.entryProfile then
    fails := fails ++ [s!"{r.entry}: declared {fmt r.entryProfile} ≠ computed {fmt e}"]
  if b ≠ r.bridgeProfile then
    fails := fails ++ [s!"{r.bridge}: declared {fmt r.bridgeProfile} ≠ computed {fmt b}"]
  if p ≠ r.predecessorProfile then
    fails := fails ++ [s!"{r.predecessor}: recorded {fmt r.predecessorProfile} ≠ computed {fmt p}"]
  unless strictlyBelow combined p do
    fails := fails ++ [s!"{r.entry}: combined entry/bridge profile {fmt combined} is not a strict narrowing of {r.predecessor}'s {fmt p}"]
  for prof in [e, b, p] do
    if prof.contains "sorryAx" then
      fails := fails ++ [s!"{r.entry}: sorryAx reachable"]
  if fails.isEmpty then
    IO.println s!"OK {r.entry}: same-statement checked; combined profile {fmt combined} ⊂ {r.predecessor} {fmt p}"
  return fails

-- [ZP port P4] (extension)
/-- A declared profile for a declaration that replaces nothing — a definition
or a theorem with no predecessor. Checks declared = computed and no `sorryAx`;
asserts no relation and no narrowing. -/
structure ProfileRow where
  decl : Name
  declProfile : List String

-- [ZP port P4]
/-- All failures for one profile row (empty = green). -/
def checkProfileRow (r : ProfileRow) : CoreM (List String) := do
  unless (← getEnv).contains r.decl do
    return [s!"{r.decl}: unknown declaration"]
  let d ← profile r.decl
  let mut fails : List String := []
  if d ≠ r.declProfile then
    fails := fails ++ [s!"{r.decl}: declared {fmt r.declProfile} ≠ computed {fmt d}"]
  if d.contains "sorryAx" then
    fails := fails ++ [s!"{r.decl}: sorryAx reachable"]
  if fails.isEmpty then
    IO.println s!"OK {r.decl}: declared profile {fmt d} = computed"
  return fails

/-- Auxiliary declarations the coverage pass ignores (matchers, lifted
proofs, compiler-generated structure lemmas) — everything a human did not
name. -/
def isAux (n : Name) : Bool :=
  n.isInternal ||
    match n with
    | .str _ s =>
        s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_" ||
        s == "inj" || s == "injEq" || s == "sizeOf_spec" ||
        s == "noConfusion" || s == "noConfusionType" || s == "eq_def"
    | _ => true

-- [ZP port P2/P3] upstream's `coverage`, with the ledger and the scope as arguments.
/-- Every non-auxiliary theorem `inScope` must be a ledger row (entry or bridge)
or a profile row. -/
def coverageWith (ledger : List Row) (profiles : List ProfileRow)
    (inScope : Environment → Name → Bool) : CoreM (List String) := do
  let env ← getEnv
  let listed := ledger.map (·.entry) ++ ledger.map (·.bridge) ++ profiles.map (·.decl)
  let mut fails : List String := []
  for (n, ci) in env.constants.toList do
    if inScope env n && !isAux n then
      if let .thmInfo _ := ci then
        unless listed.contains n do
          fails := fails ++ [s!"unledgered theorem: {n}"]
  return fails

-- [ZP port P5]
/-- The same coverage obligation, enumerating only the named imported modules'
`constNames` plus the current file's own constants, instead of every constant of
the environment. A named module that is not imported is a failure. -/
def coverageModules (ledger : List Row) (profiles : List ProfileRow)
    (modules : List Name) : CoreM (List String) := do
  let env ← getEnv
  let listed := ledger.map (·.entry) ++ ledger.map (·.bridge) ++ profiles.map (·.decl)
  let mut names : Array Name := env.constants.foldStage2 (fun ns n _ => ns.push n) #[]
  let mut fails : List String := []
  for m in modules do
    match env.header.moduleNames.idxOf? m with
    | some i =>
        match env.header.moduleData[i]? with
        | some md => names := names ++ md.constNames
        | none => fails := fails ++ [s!"coverage: no module data for {m}"]
    | none => fails := fails ++ [s!"coverage: module not imported: {m}"]
  for n in names do
    if !isAux n then
      if let some (.thmInfo _) := env.find? n then
        unless listed.contains n do
          fails := fails ++ [s!"unledgered theorem: {n}"]
  return fails

-- [ZP port P2/P3] upstream's `audit`, with the ledger and the scope as arguments.
/-- Run every row and the coverage pass; throw on any failure. -/
def auditWith (ledger : List Row) (profiles : List ProfileRow)
    (inScope : Environment → Name → Bool) : CoreM Unit := do
  let mut fails : List String := []
  for r in ledger do
    fails := fails ++ (← checkRow r)
  for r in profiles do
    fails := fails ++ (← checkProfileRow r)
  fails := fails ++ (← coverageWith ledger profiles inScope)
  if fails.isEmpty then
    IO.println s!"audit green: {ledger.length} entries, {profiles.length} profile rows, every relation checked, every profile declared = computed, every combined narrowing strict, coverage total"
  else
    throwError ("audit FAILED:\n" ++ String.intercalate "\n" fails)

-- [ZP port P5]
/-- `auditWith`, with the module-enumerating coverage pass. -/
def auditModules (ledger : List Row) (profiles : List ProfileRow)
    (modules : List Name) : CoreM Unit := do
  let mut fails : List String := []
  for r in ledger do
    fails := fails ++ (← checkRow r)
  for r in profiles do
    fails := fails ++ (← checkProfileRow r)
  fails := fails ++ (← coverageModules ledger profiles modules)
  if fails.isEmpty then
    IO.println s!"audit green: {ledger.length} entries, {profiles.length} profile rows, every relation checked, every profile declared = computed, every combined narrowing strict, coverage total"
  else
    throwError ("audit FAILED:\n" ++ String.intercalate "\n" fails)

-- [ZP port P3]
/-- Scope: theorems originating in one of the modules `ms`, or in the file being
elaborated. -/
def inModulesOrMain (ms : List Name) (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => match env.header.moduleNames[idx.toNat]? with
    | some m => ms.contains m
    | none => false
  | none => true

-- [ZP port P2] upstream's `#eval audit` stood here; the consumer's ledger file runs the audit.

end Corpus.Audit
