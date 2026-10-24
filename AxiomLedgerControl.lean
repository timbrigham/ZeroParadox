import ZeroParadox.Meta.AxiomLedger

/-!
Deliberately wrong. CI requires this file to FAIL; if it ever passes, the gate is not failing closed.

It reruns the ledger's audit with exactly one row changed: `ZeroParadox.kleene_cf` declared `[]`,
where the kernel computes `[Quot.sound, propext]`. Every other row is the ledger's own. Lives
outside `ZeroParadox/`, so the default build never sees it; `.github/workflows/axiom_ledger.yml`
elaborates it and requires the audit's mismatch message for that row.
-/

open Lean

#eval show CoreM Unit from do
  let original := ZeroParadox.AxiomLedger.profiles
  -- If the row were ever renamed away, the change below would be a no-op and the audit would
  -- pass. CI would still go red on that, and this guard names the cause.
  unless original.any (·.decl == `ZeroParadox.kleene_cf) do
    throwError "control broken: no `ZeroParadox.kleene_cf` row in the ledger to corrupt"
  let wrong := original.map fun r =>
    if r.decl == `ZeroParadox.kleene_cf then { r with declProfile := [] } else r
  Corpus.Audit.auditModules ZeroParadox.AxiomLedger.replacements wrong
    [`ZeroParadox.Computability.KleeneChoiceFree]
