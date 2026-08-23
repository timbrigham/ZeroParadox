# Ledger→gitRobot gate: the test fixture

**Purpose: prove a push CANNOT pass while the ledger says the required keys for that exact hash are
not satisfied.** That property failed on 2026-08-23 and the failure was silent — see below.

⚠ **Every record here is seeded by hand through `mcp__verdictLedger__*`, with
`decided.how = "signature"`.** That is deliberate: the human-approved route needs no agreement
threshold (`min_passes: 3`) and no paid agent rounds, so the whole matrix can be replayed in seconds
without spending money. **It tests the GATE, not the checkers.**

---

## The failure this fixture exists to catch

| | |
|---|---|
| `gitRobot` push of `55f2d6a` | **ALLOWED** — 19 blocking checks green, preflight passed, audited, pushed |
| `verdictLedger` `inventory(ref=55f2d6a, action="push")` | **`REFUSED push 0/19 keys`**, `complete: false` |

Both components were behaving correctly. **Nothing in the push path ever asked the ledger.** The
push was subsequently reverted in full (`5475e28`, *"the gate passed it and should not have"*).

⚠ **A second failure surfaced from that revert and belongs in the matrix: the ledger's config lives
inside the repository it gates.** Reverting the repo deleted `policy.v1.json`, and the ledger went
`config_ok: false, policy_sha: null`. It refused to serve rather than reading a different copy —
correct, and worth keeping — but **a checkout can disarm the bar.** Case F covers it.

---

## The matrix

`R` = the fixture commit's hash. Seed records with `basis: {kind: "ref", value: R}` and
`decided: {how: "signature", who: "<name>", passes: 1, agreed: 1}`.

| # | seed | expected `inventory(R, "push")` | expected `push` |
|---|---|---|---|
| **A** | nothing | every admitted key `MISSING` | **REFUSE**, naming each |
| **B** | PASS for some admitted keys | `missing > 0` | **REFUSE**, naming only the gap |
| **C** | PASS for **all** admitted keys | `complete: true` | **ALLOW** |
| **D** | as C, then **edit a subject file** | that key flips `SATISFIED → STALE` | **REFUSE** — and STALE must not read as MISSING |
| **E** | as C, then **commit again** (hash moves to `R'`) | keys are bound to `R`, not `R'` | **REFUSE at `R'`** |
| **F** | as C, then remove `policy.v1.json` | `config_ok: false` | **REFUSE with `ledger_unreachable`**, never fall through |
| **G** | as C, plus a stale `*_cleared.txt` on disk, ledger stopped | — | **REFUSE.** The retired signal path must not resurrect |
| **H** | register a new type, run nothing for it | it is **NOT** in the admission set | **ALLOW**, and the allow line **NAMES it as not gating** |
| **I** | promote that type into `admission.v1.json`, run nothing | it is now admitted and `MISSING` | **REFUSE**, naming it |
| **J** | a `FAIL` record for an admitted key | `failed: 1` | **REFUSE** — a FAIL is not a MISSING |
| **K** | `sign` that FAIL (accept as debt) | the accept is the operative verdict | **ALLOW**, and the allow line shows `signature` in the `how` breakdown |

**H and I are the pair that proves the two lists are independent** — registering does not gate,
promoting does. **D, E and J are the three that must never collapse into "not satisfied"**: the
remedies are *re-run*, *re-verify at the new hash*, and *fix the finding*, and they cost wildly
different amounts.

**K is the "human approved this" route end to end** — it is also the only case where a push is
allowed while a required check is red, so the allow line must make that visible rather than
rendering identically to a clean pass.

---

## Replay

1. `mcp__verdictLedger__status` — confirm `config_ok: true` and note `policy_sha`.
2. `mcp__verdictLedger__requirements(action="push")` — the registry's answer.
3. `mcp__verdictLedger__inventory(ref=<R>, action="push")` — expect case A on a fresh hash.
4. Seed with `append` / `sign` per the matrix; re-run `inventory` between steps.
5. Attempt `mcp__gitRobot__push` and record what it did.

⚠ **Record the OBSERVED result, including where it disagrees with the expectation.** The 2026-08-23
failure was two components each behaving correctly and nobody comparing them. A matrix nobody runs
the last column of is the same defect wearing a table.

⚠ **Cases C and K are the dangerous ones to get wrong.** Everything else fails closed; those two are
the paths that let a push through, so they are where a fail-open would actually cost something.
