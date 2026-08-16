**SSOT tag-review pipeline (ZeroParadox ontology registry).** Three tiers: DeepSeek does the bulk review off-Claude; a cold informed Opus arbitrates only where DeepSeek contradicts the SSOT; THIS instance (orchestrator) reconciles and writes the changes through the application gate. Replaces the old Sonnet cold-panel-on-everything (which burned the billable window). Canonical spec: `.claude-local/tag_review_protocol.md`; rule base: `.claude-local/l2_rules.md`; runner + data: `.claude-local/deepseek/`.

`$ARGUMENTS` selects the work as a **registry query** against the live `ssot.json`: a domain (`domain=set-theory`), a role (`role=core`), `unscoped`, `object=bottom`, or an explicit decl-id / short-name list. The runner filters the live registry itself — there is **no fixed panel numbering** (the pre-reorg `1-50` index ranges are retired; they no longer map to HEAD). Default: ask what to review.

---

## Operating rules (hard)
- **Pin the hash.** Record `source_sha256` (sjv `verify_integrity`) at batch start. If it moves mid-batch, the batch is INVALID — re-pin and re-run. `validate` must be green before starting.
- **No sjv writes until sign-off.** This command PRODUCES a decision log and STOPS. CORRECT retags apply only after Tim approves, then: sjv `annotate` → re-run `ssot_l1_acceptance.py` (must exit 0) → re-pin → append the decision log. Never hand-edit registry JSON.
- **The arbiter is BLIND.** The cold Opus reviewer sees the full rules + the decl source, NEVER the SSOT tag or DeepSeek's vote. An anchored arbiter is a worse arbiter (falsifier-context-hygiene). The contradiction is used only in the orchestrator's reconciliation, never in the Opus prompt.
- **Judge the statement, not the story** (rule 11) — applies to docstrings AND to DeepSeek's justification. The arbiter cites the Lean statement.
- **Settled decls are not re-reviewed** (§10): key the decision log by `(decl-id + content-hash of signature+vocab-version)`; skip anything already logged unless its signature or the vocab changed.

## Tier 1 — DeepSeek bulk review (0 Claude tokens)
The runner is a **single self-contained, registry-driven script** — the current reference implementation is `.claude-local/deepseek/run_settheory.py` (grep-line-safe + `--emit-prompt`); copy it per audit and change the query filter. ⚠ **Never copy `run_unscoped.py`.** It was the earlier version and it trusts `old.line`, which the reorg made STALE, so it injects the wrong source window. Step 2 below said to copy it anyway until 2026-08-15 — three lines after this warning, which is exactly how far a caveat travels. It reads `ssot.json` directly, filters to the `$ARGUMENTS` query, and for each decl: takes the CURRENT identity (`new.file` / `new.short`), **greps the decl name in its current file to find the line** (`old.line` is STALE post-reorg — never trust it for source injection), injects the source window, and builds the prompt from `pp_scaffold/panel_001.txt` used **only as the yardstick template** (its intro + controlled-vocabulary + rules 0–13, sliced verbatim) plus a freshly-built `=== DECLARATION ===` block. It POSTs straight to the bridge (`http://127.0.0.1:8118/mcp`, `deepseek-v4-pro`, `response_schema`) and writes schema-validated votes **resumably** to a per-audit dir (`<audit>_votes/`), recording each decl's current tag (`cur_domain`/`cur_role`) alongside the blind vote for the diff. BLIND: the prompt never states the current tag.

1. Confirm the bridge is up (`initialize` returns 200) and pin the hash (`verify_integrity`; `validate` green).
2. Copy the CURRENT reference runner — `run_settheory.py`, per the paragraph above — to `run_<audit>.py`, set the query filter, and run it off-Claude in the background: `python .claude-local/deepseek/run_<audit>.py --model deepseek-v4-pro` (the bridge default is flash — ALWAYS pass `deepseek-v4-pro`; flash inflates). The `&`-launcher returns immediately; the Python keeps running — wait on the `===== DONE` marker in its log, not the launch notification.
3. Diff each vote's domain/role/object against the SSOT tag (the runner records `cur_domain`/`cur_role`):
   - **Agree → CONFIRM.** No arbiter, no write. Log it.
   - **Contradict → goes to Tier 2.**
   - Any schema-invalid, `no_fit:true`, or low confidence → Tier 2 as well (uncertainty is signal).

**Retired (pre-reorg — do NOT use):** the per-decl-panel prep — `ds_prep.py`, `l2_run_local.py`, `l2_gen_panel.py`, the `ds_votes/` dir, and the numbered `pp_scaffold/panel_NNN.txt` files (all pre-reorg; `panel_001.txt` survives ONLY as the yardstick template the runner slices). The current runner needs none of them — trying to regenerate per-decl panels is the trap that nearly reintroduced the stale method.

## Tier 2 — cold informed Opus arbiter (only on contradiction/uncertainty)

**⚠ SAME-YARDSTICK RULE (hard, non-negotiable).** DeepSeek and the Opus arbiter MUST be measured against byte-identical vocabulary + rules. The runner builds each DeepSeek prompt from `pp_scaffold/panel_001.txt`'s intro + controlled-vocabulary + rules 0–13 (sliced verbatim) plus that decl's freshly-built declaration block and injected source. So the arbiter's prompt = **the byte-identical prompt the runner POSTed to DeepSeek for that decl** — regenerate it with the same runner (`run_<audit>.py --emit-prompt <idx>`, which prints the exact `build_prompt` output), NEVER a hand-written summary or a stale numbered panel. NEVER paraphrase, condense, or re-order the vocab/rules — a different yardstick can manufacture or mask a contradiction and INVALIDATES the whole comparison. (This exact mistake was made and caught 2026-07-04.)

For each flagged decl: **regenerate its runner prompt yourself** (`--emit-prompt <idx>`) and spawn a fresh Agent (`model: opus`, `subagent_type` general-purpose, no session context) whose prompt is **that runner prompt verbatim**. It already carries the blind framing, full vocab, rules 0–13, the task, the output schema, and the injected source. Opus additionally has file tools, so it may follow cited defs into other ZeroParadox/Mathlib files (which DeepSeek could not). Do NOT paste the SSOT tag or DeepSeek's vote into the Agent, and do NOT let it read the runner's `<audit>_votes/` dir — the arbiter stays blind. **Batch these — one Agent per decl, in parallel; each isolated so the orchestrator context stays lean.** Collect each Agent's JSON vote.

## Tier 3 — orchestrator reconciles (this instance)
For each arbitrated decl, compare the three reads — **SSOT · DeepSeek · Opus** — and assign the verdict:

| Opus vs DeepSeek vs SSOT | verdict | action |
|---|---|---|
| Opus agrees with DeepSeek (both ≠ SSOT) | **CORRECT** | candidate retag to the Opus/DeepSeek value → route by lane (§6) |
| Opus agrees with SSOT (DeepSeek was noise) | **CONFIRM** | keep SSOT; log that DeepSeek over-flagged |
| Opus differs from both, or `no_fit`/low-conf, or a role/object SPLIT | **SPLIT** | flag; tag unchanged pending; route to Tim (CONVENTION) or an N=3 isolated-Opus escalation (reuse the arbiter's blind read + 2 fresh isolated Opus, majority per axis) |

**Corroboration, not vote-counting (all three axes are multi-value).** The two independent MODEL reads are DeepSeek + blind-Opus; the SSOT is the incumbent, not a vote. Write a value (union or replace, per axis) ONLY when both models name it against the SSOT. A value only one model proposed and the source doesn't support is the artifact the blind arbiter exists to FILTER — do NOT union it. A disagreement is never a union license: a novel single-read value or a mutually-exclusive-reading disagreement is a SPLIT → N=3 isolated-Opus escalation, never an auto-merge.

Route CORRECTs by the cited sources (§6): **FACT** (verifiable from the citation → apply after Tim confirms the citation) · **MATH-CONTENT** (domain/is-it-content → deeper read or escalate) · **CONVENTION** (what a vocab term means here → Tim decides once, write the ruling back into `l2_rules.md`).

## Output
Write a decision-log table (§10 schema: `decl · SSOT · deepseek · opus · verdict · lane · proposed-tag · confidence · date · source_sha256`) to `.claude-local/notes/tag_review_log.md`. Present the CORRECT/SPLIT list to Tim. **Stop. Apply nothing until he signs off.** On approval: `annotate` the approved CORRECTs → `ssot_l1_acceptance.py` exit 0 → re-pin the new hash → finalize the log → optionally refresh `tools/registry/registry_export.json`.

## Escalation / cost notes
- Opus fires on ~20% of items (contradiction rate), isolated context each — far cheaper than cold-reviewing everything, and no Sonnet.
- Known DeepSeek soft spots (from validation): it flattens ~40% of subtle non-scaffolding calls at HIGH confidence and can't self-panel (correlated errors at temp=0). This design tolerates that: DeepSeek only needs to *raise* contradictions; Opus (a different model) is the real judgment. The residual blind spot — where DeepSeek AND the SSOT agree wrongly — is caught only by an occasional deep-audit sample of CONFIRMs (optional backstop, Tim's call).
