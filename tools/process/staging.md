# Staging — why named paths, and why the escape hatch was removed

**Body for `CLAUDE.md` § `R-STAGE`.** The rule is there; the 2026-07-19 scratch-probe
incident and the `.claude-local` exemption are here.

---

## Staging — NAMED PATHS, never `-A`. ⭐ NOW MECHANICAL, not remembered. (2026-08-22.)

**Bulk staging takes whatever happens to be in the tree, including files this session did not create.**

**Measured 2026-07-19:** a background review agent wrote a scratch probe into `ZeroParadox/`, and the next
bulk add swept it into a commit unnoticed. It is in the permanent history now. Background agents run
*concurrently* with commits, so the working tree is not a stable snapshot of what you intended to change.

**The rule:** stage the specific paths you edited — `stage(paths=['a.lean','b.md'])`. Before committing,
`read(op='status', args=['--short'])` and confirm every staged path is one you meant to touch. If a path
appears that you did not edit, find out where it came from before committing it.

⭐ **THIS IS THE EIGHTH CONVENTION IN THIS FILE TO STOP BEING A DISCIPLINE AND START BEING A GATE, AND
IT IS THE ONE TO COPY.** `gitRobot.stage` has **no bulk form on the main repo** — `-A`, `.` and `-u` are
refused, with the reason and the alternative in the refusal text. There is nothing left to remember and
nothing to adjudicate. The old escape hatch (*"`-A` is acceptable when nothing has been spawned since the
last commit"*) is **gone**, and it should be: it was a judgement call at exactly the moment a session is
least able to make it.

⚠ **`.claude-local` is exempt and bulk staging is its documented flow** —
`stage(paths=['-A'], repo_mode='.claude-local')`. Different repo, different risk: nothing published, and
the failure mode there is losing notes rather than shipping a probe.
