# `/claude-md-maintenance` — edit `CLAUDE.md` under its shape contract

**Read `tools/process/claude-md-maintenance.md` and follow it.** That file is the protocol; this one
only says when to invoke it and what invoking it commits you to. `tools/verify/check_claude_md.py`
and `tools/verify/hooks.py` both resolve to that path, and the checker prints it as `body` in the
manifest banner — on a default run and under `--measure`, though not under `--selftest` or `--help`,
which return before the banner is built.

**Invoke this when** a new lesson has arrived and you are about to add it to `CLAUDE.md`, when an
entry has stopped firing, or when the file is over budget and needs a compression pass. **Do not
invoke it to look something up** — the protocol governs EDITS.

**The one consequence to know before you start.** An addition to `CLAUDE.md` is **paid for by a
removal**, not appended. The three sanctioned payments are mechanize, move and merge; deleting an
entry outright is Tim's call. If you are not prepared to name what comes out, you are not ready to
put something in.

⚠ **This command file is NOT gate-exempt, and the protocol it points at is.** `.claude/commands/**`
is the directory R-EXEMPT marks explicitly non-exempt — both prose gates fire on it — while
`tools/process/**` is exempt and routed to `/rely`. **The carve is a property of the directory, not
of the subject matter**, so editing this file owes an editorial and an adversary round even though
editing the body it points at does not. Measured 2026-08-24: a compression pass **edited one brief
under `.claude/commands/` and created a second** believing the exemption travelled with the pass;
the two gates returned FAIL-BEDROCK and FAIL between them, and one of the findings was that belief.
