"""The interpretation layer — an agent RUNS a check and judges whether its PASS is worth trusting.

WHY THIS EXISTS, AND IT IS NOT ANOTHER CHECKER. Every other tool here asks *is the corpus clean?*
This one asks *is that answer worth anything?* The repo has published `pass` on absent evidence at
least four times: an empty log, a build killed at exit 137, a diagnostic that did not contain the
substring it searched for, and — live as of 2026-08-21 — `ci_report.py:116` reporting "no
double-encoded text in any tracked file" for a corpus containing some (`RLY25-1`). A regex cannot
see any of those, because in every case the check did exactly what it was told.

⭐ THE SAFETY PROPERTY IS MONOTONE. The agent may only ever make the verdict STRICTER:

    check FAILS                  -> FAIL.  The agent is NOT CONSULTED. Costs $0 and ~0.04s.
    check PASSES + distrusted    -> WARN.  Never blocks. Ever.
    check PASSES + agent agrees  -> pass.

So a false positive costs one warning to read, and a false negative leaves you exactly where the
mechanical layer already had you. **You are never worse off than the checkers alone.** That is what
makes a fuzzy component safe to put next to a gate, and it is why this must never be promoted to
BLOCK — see `CLAUDE.md` rung 5: the screen may replace the enumeration, never the verdict.

⚠ MEASURED BEFORE ADOPTION (prototype, 2026-08-21, 12 decisions over 4 cases, 3 repeats):
  fail-opens caught            6/6, unanimous
  healthy checks left alone    6/6  (including this bundle's own check_encoding.py)
  false positives BEFORE the majority rule   1 in 6, and UNSTABLE — byte-identical input returned
                                             TRUSTWORTHY, TRUSTWORTHY, NOT_TRUSTWORTHY
  false positives AFTER                      0
That instability is `DC-17` reproduced (it measured 1, 4, 4, 3 false positives across four runs over
the same twelve negatives), and it is why `interpret_confirmed` exists.

⚠ THREE TRAPS, ALL MEASURED BY RUNNING THIS, NONE BY READING IT:
  1. WITHOUT `--model` PINNED it loaded 130k cache-creation tokens of project context to read a
     six-line log and burned $1.32 against a $0.50 cap. Interpreting a log does not need the
     frontier model.
  2. `subprocess.run(text=True)` DECODES WITH THE WINDOWS LOCALE CODEPAGE. UTF-8 came back as
     cp1252 and was rewritten as UTF-8 — genuine double-encoded mojibake in the very first
     suggestion file. That is `SH-2`, this project's most-repeated shape. `encoding="utf-8"` is
     load-bearing on every subprocess call in this file.
  3. `--bare` SKIPS CLAUDE CODE HOOKS, NOT GIT HOOKS, so it is not a recursion guard. `ZP_IN_HOOK`
     is, and removing the agent's tools entirely is the belt.

⚠ THE AGENT HAS NO TOOLS (`--tools ""`). It is handed the captured output and reasons over text.
Capability removal, not instruction: a `/rely` agent once `git reset --hard`'d a shared tree while
exercising commit gates and then reported "tracked tree clean", which was true and WAS the
destruction. THE HOOK WRITES THE SUGGESTION FILE, NOT THE AGENT.

Usage (this tool prints its own invocation path; never hardcode one — see CLAUDE.md):
  agent_gate.py               # interpret every registered check, WARN only, exit 0
  agent_gate.py --selftest    # both-halves controls for this tool itself
  agent_gate.py --list        # the registry, without running anything

  ZP_AGENT_GATE=1             # required, or this no-ops. OPT-IN while it is being evaluated;
                              # `batch.py prepush` declares it either way, so it is never silent.
  GATE_MODEL / GATE_BUDGET    # override the pinned model / per-call ceiling
"""
import json
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                                    # noqa: E402

common.utf8_stdout()
SELF = common.self_rel(__file__)
SUGG_DIR = common.PRIV / "agent_suggestions"
MODEL = os.environ.get("GATE_MODEL", "claude-haiku-4-5-20251001")
BUDGET = os.environ.get("GATE_BUDGET", "0.50")
ENABLED = os.environ.get("ZP_AGENT_GATE") == "1"

# --- THE REGISTRY -----------------------------------------------------------
# ⚠ `expected_failure` IS THE LOAD-BEARING FIELD AND IT IS JUDGEMENT, NOT TYPING (`DC-22`): state
# in advance WHICH error a real failure produces, so the agent cannot rationalise any output into a
# story. A registry entry with a vague expectation is worse than no entry.
#
# ROLLED OUT AS-TOUCHED, deliberately three to start. Add a checker when you next touch it and can
# state its failure mode precisely — not in a sweep.
CHECKS = [
    {
        "name": "check_encoding",
        "cmd": [sys.executable, str(common.HERE / "check_encoding.py")],
        "expected_failure":
            "A BOM or an undecodable file BLOCKS and exits 1. Suspected double-encoding is reported "
            "on a 'double-encoded' line and WARNS (exit 0). A genuine clean run reports a NON-ZERO "
            "'scope' count of tracked text files, and states how many verified exclusions are live.",
    },
    {
        "name": "check_moved",
        "cmd": [sys.executable, str(common.HERE / "check_moved.py")],
        "expected_failure":
            "A reference to a relocated path prints the offending file and exits 1. A genuine clean "
            "run reports a NON-ZERO count of tracked relocations and zero stale references.",
    },
    {
        "name": "check_figures",
        "cmd": [sys.executable, str(common.HERE / "check_figures.py")],
        "expected_failure":
            "An undated artifact count in prose is printed with its file:line and exits 1. A genuine "
            "clean run reports a NON-ZERO 'sites found' count and 'NEW undated figures : 0'.",
    },
]

SCHEMA = {
    "type": "object",
    "properties": {
        "verdict": {"type": "string", "enum": ["TRUSTWORTHY", "NOT_TRUSTWORTHY"]},
        "reason": {"type": "string"},
        "suggestion_class": {"type": "string", "enum": ["WIDEN", "RESHAPE", "CONTROL", "NOISE"]},
        "suggestion": {"type": "string"},
    },
    "required": ["verdict", "reason", "suggestion_class", "suggestion"],
}

PROMPT = """You are a verification-gate interpreter. A check just ran. Decide whether its PASS can be
TRUSTED -- not whether the code under test is correct.

CHECK NAME: {name}
EXIT CODE: {rc}
WHAT A REAL FAILURE LOOKS LIKE (declared in advance): {expected}

--- BEGIN CAPTURED OUTPUT ---
{output}
--- END CAPTURED OUTPUT ---

Answer two things.

1. verdict. NOT_TRUSTWORTHY if this is success reported on ABSENT EVIDENCE: an empty scan, zero items
   examined, a killed or truncated run, output whose shape does not match what the declared failure
   mode implies, or a banner asserting a property the output does not actually demonstrate.
   TRUSTWORTHY only if the output positively shows the check did its work.
   You cannot fail a check that already passed on its own terms -- you can only report that its pass
   is not worth relying on. Do not speculate about code you cannot see.

2. suggestion -- how the CHECK ITSELF should be better next time, and classify it:
     CONTROL  a probe the existing controls cannot construct (highest value)
     RESHAPE  a different predicate, layer, or unit
     WIDEN    another pattern or case (LOW value -- widening is usually the failure repeating;
              use only if nothing structural applies)
     NOISE    nothing useful to add
"""

LAST_COST = [0.0]


def run_check(c):
    started = time.time()
    p = subprocess.run(c["cmd"], capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return {"rc": p.returncode, "output": (p.stdout + p.stderr).strip(),
            "secs": round(time.time() - started, 2)}


def interpret(c, res):
    """One agent call. Returns (parsed_or_None, raw, seconds)."""
    prompt = PROMPT.format(name=c["name"], rc=res["rc"], expected=c["expected_failure"],
                           output=res["output"] or "(no output at all)")
    cmd = ["claude", "-p", prompt, "--model", MODEL, "--tools", "",
           "--output-format", "json", "--json-schema", json.dumps(SCHEMA),
           "--max-budget-usd", BUDGET, "--no-session-persistence"]
    started = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                           errors="replace", env=dict(os.environ, ZP_IN_HOOK="1"), timeout=300)
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return None, "agent unavailable: %r" % (e,), round(time.time() - started, 2)
    secs = round(time.time() - started, 2)
    raw = (p.stdout or "").strip() or (p.stderr or "").strip()
    LAST_COST[0] = 0.0
    try:
        env_obj = json.loads(raw)
    except Exception:
        return None, raw[:1500], secs
    if isinstance(env_obj, dict) and env_obj.get("is_error"):
        return None, "AGENT ERROR subtype=%s errors=%s" % (
            env_obj.get("subtype"), env_obj.get("errors")), secs
    if isinstance(env_obj, dict):
        try:
            LAST_COST[0] = float(env_obj.get("total_cost_usd") or 0.0)
        except (TypeError, ValueError):
            pass
    payload = env_obj.get("result", env_obj) if isinstance(env_obj, dict) else env_obj
    if isinstance(payload, str):
        try:
            payload = json.loads(payload)
        except Exception:
            return None, raw[:1500], secs
    if isinstance(payload, dict) and "verdict" in payload:
        return payload, raw, secs
    return None, raw[:1500], secs


def interpret_confirmed(c, res):
    """CLAUDE.md rung 5: a flag counts only if it survives >=2 of 3 runs.

    ⚠ ONLY DISTRUST IS CONFIRMED. A first-pass TRUSTWORTHY is accepted as-is: under the monotone
    rule a false negative leaves you where the checkers already had you, so it is not worth 3x the
    cost. The healthy path stays at ONE call; the 3x is paid only when something is flagged.
    """
    first, raw, secs = interpret(c, res)
    cost = LAST_COST[0]
    if first is None or first["verdict"] != "NOT_TRUSTWORTHY":
        return first, raw, secs, [None if first is None else first["verdict"]], cost
    votes, keep = [first["verdict"]], first
    for _ in range(2):
        again, _r, s = interpret(c, res)
        secs += s
        cost += LAST_COST[0]
        votes.append(None if again is None else again["verdict"])
        if again is not None and again["verdict"] == "NOT_TRUSTWORTHY":
            keep = again
    if votes.count("NOT_TRUSTWORTHY") >= 2:
        return keep, raw, secs, votes, cost
    softened = dict(first, verdict="TRUSTWORTHY",
                    reason="Flagged on 1 of 3 runs and did not survive confirmation (rung 5: >=2 of "
                           "3). Original reason: " + first["reason"])
    return softened, raw, secs, votes, cost


def write_suggestion(c, res, parsed, secs, votes):
    """The HOOK writes the file. The agent has no tools and cannot."""
    SUGG_DIR.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y-%m-%dT%H-%M-%S")
    path = SUGG_DIR / ("%s__%s.md" % (stamp, c["name"]))
    common.write_text_lf(path,
        "# suggestion — %s\n\n"
        "- **when:** %s\n- **check:** `%s`\n- **exit code:** %d\n"
        "- **verdict:** %s\n- **class:** %s\n- **votes:** %s\n- **agent seconds:** %s\n\n"
        "## why the pass is (not) trustworthy\n\n%s\n\n"
        "## suggested next iteration of the CHECK\n\n%s\n\n---\n"
        "*Disposition is NOT set here. The producer may never mark its own suggestion adopted —\n"
        "that is `queue/process-suggestion-remediation.md`, which Tim triggers.*\n"
        % (c["name"], stamp, c["name"], res["rc"], parsed["verdict"],
           parsed["suggestion_class"], votes, secs, parsed["reason"], parsed["suggestion"]))
    return path


def run(checks=None):
    """Advisory. ALWAYS returns 0 — this layer never blocks. Returns (rc, flagged, cost)."""
    checks = checks if checks is not None else CHECKS
    if not ENABLED:
        print("  agent gate         skip  ZP_AGENT_GATE is not 1 — interpretation layer NOT run")
        return 0, 0, 0.0
    flagged, cost = 0, 0.0
    for c in checks:
        res = run_check(c)
        if res["rc"] != 0:
            # MONOTONE arm 1: a real failure is a failure. The agent is not consulted, so it can
            # never argue one into a pass — and it costs nothing.
            print("  agent gate         ok    %s exited %d — mechanical FAIL, agent not consulted"
                  % (c["name"], res["rc"]))
            continue
        parsed, raw, secs, votes, c_cost = interpret_confirmed(c, res)
        cost += c_cost
        if parsed is None:
            # Unusable response is NOT a pass. It warns; it does not block (this layer never does).
            print("  agent gate         WARN  %s: agent response unusable (%ss) — %s"
                  % (c["name"], secs, raw[:120].replace("\n", " ")))
            continue
        if parsed["verdict"] == "NOT_TRUSTWORTHY":
            flagged += 1
            path = write_suggestion(c, res, parsed, secs, votes)
            print("  agent gate         WARN  %s PASSED but its pass is not trustworthy:"
                  % c["name"])
            print("                           %s" % parsed["reason"][:300])
            print("                           suggestion -> %s" % common.self_rel(path))
        else:
            print("  agent gate         ok    %s pass looks earned (%ss, $%.3f)"
                  % (c["name"], secs, c_cost))
    if flagged:
        print("  agent gate         ** %d flagged. ADVISORY — this layer never blocks a push. **"
              % flagged)
    return 0, flagged, cost


# --- controls ---------------------------------------------------------------
# ⚠ BOTH HALVES, and each fixture's expected verdict is declared BEFORE the run (`DC-22`). A
# must-fire half alone is half-tested — recorded in CLAUDE.md as having been learned three times.
# ⚠ The must-suppress half is the one that matters most here: a FALSE POSITIVE manufactures work
# that looks urgent, which this project rates the more expensive error.
_FIX = common.HERE / "agent_gate_fixtures"


def selftest():
    fixtures = [
        ("empty-scan", "scan_empty.py", "NOT_TRUSTWORTHY",
         "A genuine clean run reports a NON-ZERO 'scanned' count; violations print 'VIOLATION:' "
         "and exit 1."),
        ("truncated-run", "scan_truncated.py", "NOT_TRUSTWORTHY",
         "A complete run always ends with a '=== done ===' terminator and a summary count; "
         "violations print 'VIOLATION:' and exit 1."),
        ("honest-pass", "scan_honest.py", "TRUSTWORTHY",
         "A genuine clean run reports a NON-ZERO 'scanned' count; violations print 'VIOLATION:' "
         "and exit 1."),
    ]
    if not ENABLED:
        print("SKIP: set ZP_AGENT_GATE=1 to run the controls (they cost real money).")
        return 0
    print("=== agent_gate controls — MUST-FIRE and MUST-SUPPRESS ===")
    fp = fn = 0
    for name, script, expect, expected_failure in fixtures:
        c = {"name": name, "cmd": [sys.executable, str(_FIX / script)],
             "expected_failure": expected_failure}
        res = run_check(c)
        parsed, raw, secs, votes, _c = interpret_confirmed(c, res)
        got = parsed["verdict"] if parsed else "(unusable)"
        ok = got == expect
        if not ok:
            if expect == "TRUSTWORTHY":
                fp += 1
            else:
                fn += 1
        print("  %-16s want=%-16s got=%-16s votes=%s  %s"
              % (name, expect, got, votes, "PASS" if ok else "** MISS **"))
    print("  ---")
    print("  false positives (flagged a healthy check): %d   <- the expensive error" % fp)
    print("  false negatives (missed a fail-open)     : %d" % fn)
    print("  BOTH HALVES EXERCISED: must-fire 2, must-suppress 1")
    return 0 if (fp == 0 and fn == 0) else 1


def main():
    if os.environ.get("ZP_IN_HOOK") == "1":
        return 0                       # recursion sentinel — see the module docstring, trap 3
    if "--list" in sys.argv:
        print("%s — registry (%d check(s)); model %s; enabled=%s"
              % (SELF, len(CHECKS), MODEL, ENABLED))
        for c in CHECKS:
            print("  %-16s %s" % (c["name"], c["expected_failure"][:90]))
        return 0
    if "--selftest" in sys.argv:
        return selftest()
    rc, _f, cost = run()
    if cost:
        print("  agent gate         cost this run: $%.3f" % cost)
    return rc


if __name__ == "__main__":
    sys.exit(main())
