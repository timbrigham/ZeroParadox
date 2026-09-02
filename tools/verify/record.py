"""verdictLedger client for ZeroParadox checkers. STDLIB ONLY, NO RULES.

Install as `tools/verify/record.py` in the ZP repo. Every checker calls `emit`.

⚠⚠ THIS FILE HOLDS NO VALIDATION LOGIC. It serialises and posts; the rules live in
the server, in exactly one place. That is what makes the mirror defect
unrepresentable rather than avoided by discipline — there is no second
implementation to drift.

⚠ If the ledger is unreachable or refuses, `emit` returns None and THE CALLER
BLOCKS. Never a warning, never a pass, never a local fallback write — a local
fallback is the two-route design returning through the back door.

    rid = record.emit(...)
    if rid is None:
        print("UNDECIDED: ledger unavailable or record rejected"); sys.exit(2)

⚠ EXIT 2, NEVER 0, NEVER 1. Distinguish "the check failed" (1) from "the check
could not be recorded" (2), or the pipeline cannot tell a finding from an outage.

Measured 2026-08-22: streamable-HTTP MCP over urllib works — initialize,
notifications/initialized, tools/call; session id from the Mcp-Session-Id response
header; payload on the SSE `data:` line. No `mcp` dependency needed here.
"""

from __future__ import annotations

import json
import os
import sys
import time
import urllib.error
import urllib.request

URL = os.environ.get("ZPLEDGER_URL", "http://127.0.0.1:8011/mcp")
TIMEOUT = float(os.environ.get("ZPLEDGER_TIMEOUT", "45"))

# ⚠ RETRY IS MECHANICAL AND TYPED, NEVER A JUDGEMENT. Transport failures are
# transient (a supervisor restart mid-call) and retried boundedly. A VALIDATION
# refusal is terminal and never retried: if "could not take it" and "rejected it"
# look alike, a caller under pressure retries its way past a rule.
_TRANSPORT_TRIES = 3
_BACKOFF = 0.4

_HEADERS = {"Content-Type": "application/json",
            "Accept": "application/json, text/event-stream"}


def _post(payload, session=None):
    headers = dict(_HEADERS)
    if session:
        headers["Mcp-Session-Id"] = session
    req = urllib.request.Request(URL, data=json.dumps(payload).encode("utf-8"),
                                 headers=headers, method="POST")
    with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
        return resp.headers.get("Mcp-Session-Id"), resp.read().decode("utf-8")


def _parse(body):
    for line in body.splitlines():
        if line.startswith("data:"):
            return json.loads(line[5:].strip())
    return json.loads(body) if body.strip() else None


def _call(tool: str, arguments: dict):
    """One MCP round trip. Returns the parsed tool payload, or None."""
    sid, body = _post({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                       "params": {"protocolVersion": "2025-06-18", "capabilities": {},
                                  "clientInfo": {"name": "zp-record", "version": "1"}}})
    _post({"jsonrpc": "2.0", "method": "notifications/initialized"}, session=sid)
    _, body = _post({"jsonrpc": "2.0", "id": 2, "method": "tools/call",
                     "params": {"name": tool, "arguments": arguments}}, session=sid)
    res = _parse(body)
    if not res or "result" not in res:
        return None
    content = res["result"].get("content") or []
    if not content:
        return None
    try:
        return json.loads(content[0].get("text", ""))
    except (ValueError, AttributeError):
        return None


def stale_or_missing(ref, action='commit'):
    """Steps the ledger says need re-running at `ref`. Returns a set, or None if it cannot ask.

    ⚠⚠ ONE QUESTION, SERVER-SIDE — §12-0-alpha. The alternative is a second staleness predicate on
    this side, which would be the mirror defect at the exact point the split exists to protect: two
    implementations of "is this verdict still good", disagreeing silently.

    ⚠ `ref` MAY BE A TREE HASH, not just a commit — which is what makes this answerable BEFORE the
    commit exists. `git write-tree` turns the index into the tree the pending commit will carry, and
    the ledger resolves it. Measured 2026-08-23.

    ⚠ NO `admission` IS PASSED, DELIBERATELY. The admission set is gitRobot's, and asking for it here
    would drag policy into the consumer. This asks only which rows are STALE or MISSING; it never
    decides what GATES. A caller uses it to choose what to RE-RUN, nothing more.

    ⚠ RETURNS None, NOT AN EMPTY SET, WHEN THE LEDGER CANNOT BE REACHED. Empty means "nothing needs
    re-running" and would skip every checker — absence rendering as success, in the code that decides
    what runs. The caller must treat None as "run everything"."""
    try:
        out = _call('inventory', {'ref': ref, 'action': action})
    except (urllib.error.URLError, OSError, TimeoutError):
        return None
    if not out or not out.get('ok') or not isinstance(out.get('rows'), list):
        return None
    return {r.get('step') for r in out['rows']
            if r.get('status') in ('STALE', 'MISSING', 'LEGACY_IDENTITY', 'FAIL', 'UNDECIDED')}


def step_status(ref, action='commit'):
    """`{step: status}` for every registered step at `ref`. None if it cannot ask.

    ⚠⚠ THE POSITIVE FORM, AND IT EXISTS BECAUSE THE NEGATIVE ONE FAILED OPEN. `stale_or_missing`
    answers "which steps need re-running", and a caller that treats **absence from that set** as
    "recorded and current" has built a proxy: the implication runs one way only. Needing a re-run
    does imply not-current; NOT needing one does **not** imply recorded. `SATISFIED`,
    `NOT_APPLICABLE`, and *a step the registry has never heard of* all sit outside the re-run set and
    all rendered as an affirmative pass — so a typo in a caller's step list became a permanent green
    with a confident message (measured 2026-08-24 by a reliability trial, on `prior_art`, which is
    `NOT_APPLICABLE` with `record_id: null` and printed `ok REQUIRED`).

    ⚠ A step the ledger does not return is ABSENT from this map, and a caller must treat an absent
    key as a FAILURE to establish anything — never as a pass. That is the whole reason this returns
    statuses rather than a set."""
    try:
        out = _call('inventory', {'ref': ref, 'action': action})
    except (urllib.error.URLError, OSError, TimeoutError):
        return None
    if not out or not out.get('ok') or not isinstance(out.get('rows'), list):
        return None
    return {r.get('step'): r.get('status') for r in out['rows'] if r.get('step')}


def owing_paths(step, ref, action='push'):
    """Paths in `step`'s scope with NO passing verdict at `ref`'s content. None if it cannot ask.

    ⚠⚠ PER-PATH, BECAUSE THE STEP-LEVEL ANSWER CANNOT EXPRESS THE OBLIGATION. `step_status` says
    whether the STEP is satisfied, and a step is satisfied while most of its scope is unexamined —
    `check_pov` sits at 298/511 and reads SATISFIED, correctly, because narrowed coverage is
    REPORTED and does not block. So a caller asking "is this step green" learns nothing about
    whether THIS FILE was ever attributed, and for `prior_art` that is the entire question: the
    obligation is owed by the file that was EDITED, never by the corpus.

    ⚠ THE REGISTRY CANNOT EXPRESS IT AND THIS IS NOT A WORKAROUND. `scope` is a static glob, so it
    can say "all 218 .lean files" but not "the ones in this push" — a shape the registry's own
    `prior_art` entry names as the reason the gate was narrowed to discipline in the first place.
    The push RANGE is knowable only here (REL-1: `batch.py` had the working tree, which is empty
    post-commit), so the containment test belongs at the caller that has the range. The ledger
    stays the single source of what was VERDICTED; this only intersects that with what changed.

    ⚠ RETURNS None ON ANY FAILURE TO ASK, never an empty set — an unreachable ledger must not read
    as "nothing is owed", which is the absence-as-success shape this layer exists to remove."""
    try:
        out = _call('coverage_gap', {'ref': ref, 'action': action, 'step': step,
                                     'admission': [step], 'limit': 5000})
    except (urllib.error.URLError, OSError, TimeoutError):
        return None
    if not out or not out.get('ok') or not isinstance(out.get('steps'), list):
        return None
    for row in out['steps']:
        if row.get('step') != step:
            continue
        paths = row.get('paths')
        if not isinstance(paths, list):
            return None
        # ⚠ A TRUNCATED LIST IS NOT THE LIST. `limit` caps `paths` and reports the remainder in
        #   `truncated`; treating a capped list as complete would silently under-report what is
        #   owed, so refuse rather than answer with part of it.
        if row.get('truncated'):
            return None
        return sorted(str(p) for p in paths)
    return None


def read_ref(ref):
    """The ref to ASK the ledger about, with `INDEX` resolved exactly as WRITING resolves it.

    ⚠⚠ THE WRITE PATH RESOLVED THE SENTINEL AND THE READ PATH DID NOT, so the two disagreed about
    what `INDEX` MEANS. `common.ledger_basis` turns `INDEX` into a real tree via `write-tree` before
    recording; the readers passed the literal string `'INDEX'` straight through. The ledger has no
    such ref, so it answered about nothing — and answered `ok: true` while doing it.

    Measured 2026-08-25, same server, same moment: `ref='INDEX'` returned every step MISSING with
    `scope: 0`; `ref='da22ddfa…'` returned `rely` FAIL with 58 of 59 subjects covered. **A record
    was unreachable by its own consumer**, and the symptom was indistinguishable from "no record
    exists" — which is exactly the collapse this layer exists to prevent, arriving through the ref
    rather than through a verdict.

    It failed CLOSED, so nothing was let through; what it did instead was mask a real inversion
    underneath it. Fixed here rather than in `common.py` on purpose: evidence names the checker AND
    `common.py`, so touching that file stales every mechanical step at once, and this bug does not
    need that bill paid.

    ⚠ `common` is imported INSIDE the function, matching every other site here: `common` imports
    `record` for `module_evidence`, so a module-level import would be circular."""
    import common
    if ref == common.INDEX:
        return common.ledger_basis(common.INDEX)['value']
    return ref


def module_evidence(*paths, repo=None):
    """`[{path, git_blob_id}]` for the code that PRODUCED a verdict — V16's evidence field.

    ⚠⚠ NOT `inputs`, AND THE DISTINCTION IS ENFORCED SERVER-SIDE. `V4` requires every `inputs` entry
    to name a RECORD ALREADY IN THE STREAM (an aggregate naming what it aggregated), so a blob id
    there is refused by V4 before V16 ever reads it. Measured and pinned in the server's suite as
    `test_a_blob_id_in_inputs_is_refused_by_v4`, which asserts BOTH rules fire. Collapsing the two
    would also leave V4 unable to tell an aggregate's predecessor from a checker's own source.

    ⚠ NOT `subjects` either: `coverage()` reads subjects, so folding evidence in would have every
    checker certifying its own source file as reviewed corpus.

    ⚠⚠ HASHES THE WORKING-TREE FILE, NOT THE INDEX, ON PURPOSE — the bytes that RAN are the bytes on
    disk. A checker edited but not staged is a different checker, and a verdict it produced must say
    so. This is the one place in the bundle where the disk copy is the honest subject.

    ⚠ REPO-RELATIVE, FORWARD SLASHES. An absolute Windows path appends clean and then matches nothing
    for ever — the same shape as the `sha256`-named-blob-id defect, which made every record read
    STALE and the gate unsatisfiable rather than strict.

    **What this buys is not un-forgeability — it is EXPIRY.** Copying a blob id is easy and §2 rules
    out keys anyway. But the ledger indexes evidence like a switch, so editing the checker moves a
    blob the record names and the key goes STALE. **A forged mechanical PASS expires the next time the
    code it lied about changes.**"""
    import hashlib
    root = os.path.abspath(repo or os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                os.pardir, os.pardir))
    out = []
    for p in paths:
        if not p:
            continue
        ap = os.path.abspath(p)
        try:
            data = open(ap, "rb").read()
        except OSError:
            # ⚠⚠ A MISSING MODULE YIELDS NO ENTRY, AND AN EARLIER VERSION OF THIS EMITTED
            # `<ABSENT>` AS THE BLOB ID. That was wrong and would have failed confusingly: structural
            # validation requires 40 lowercase hex, so the server refuses with a message about hex
            # LENGTH — nonsense to anyone reading it, and it buries the actual fact (the producer is
            # gone) under a format complaint. Caught by the ledger's author before the flip, 2026-08-25.
            #
            # Omitting is the fail-CLOSED direction and it lands on a clearer message: with nothing
            # left to declare, `evidence` is empty and V16 refuses with ITS own error, which names
            # what to do. ⚠ The residual case — one of several modules absent, so evidence is short
            # but non-empty — is invisible to V16's weak form ("carry SOME evidence") and is caught
            # by the STRICT form, where the registry declares the module a type must name.
            continue
        blob = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
        out.append({"path": os.path.relpath(ap, root).replace("\\", "/"), "git_blob_id": blob})
    return out


def emit(step, tier, verdict, subjects, basis, reason=None,
         inputs=(), decided=None, cost=None, revision=0, evidence=(), outstanding=(),
         failing=()):
    """Append one record. Returns its id, or None if refused or unreachable.

    `subjects` is a list of {"path", "blob"} — WHAT THIS VERDICT IS ABOUT, not
    everything the step glanced at. A step that examined forty files and failed on
    one emits a PASS over the thirty-nine and a FAIL over the one; that is what
    keeps coverage exact and makes repeat-subject a lookup rather than a grep over
    prose.

    ⚠⚠ `blob` IS THE GIT BLOB ID, AND THE FIELD USED TO BE CALLED `sha256`. That was
    not a rename for tidiness: the validator accepted a 64-hex content hash while the
    comparator resolved a 40-hex blob id, so every record read STALE for ever and the
    gate was unsatisfiable rather than strict (measured 2026-08-23). A field named for
    something it does not hold is how two halves of one system disagree in silence.

    ⚠ A blob id is `sha1("blob " + bytelength + "\\0" + content)` — `sha1(file_bytes)`
    does NOT equal it. Do not compute one; read it from the index via
    `common.ledger_subjects`, which also fences the paths it is not safe to record.
    """
    record = {
        "schema": "zp.record.v1",
        "step": step, "tier": tier, "verdict": verdict,
        "reason": reason,
        "basis": basis,
        "subjects": list(subjects or []),
        "decided": decided or {"how": "mechanical", "passes": 1, "agreed": 1, "who": None},
        "inputs": list(inputs or []),
        "revision": revision,
        "cost": cost or {"seconds": None, "usd": 0.0},
        "run": {"id": os.environ.get("ZPLEDGER_RUN"), "started": None,
                "policy_sha": None, "env": {}},
    }
    # ⚠⚠ THE KEY IS OMITTED WHEN EMPTY, AND THAT IS WHAT MAKES THIS LANDABLE BEFORE THE SERVER MOVES.
    # `V7` rejects unknown top-level keys rather than ignoring them — measured 2026-08-25 against the
    # RUNNING server: a record carrying `evidence` came back
    # `V7: unknown top-level key(s) ['evidence'] — rejected, not ignored`.
    # So sending `"evidence": []` unconditionally would refuse EVERY mechanical record the moment
    # this file landed, before any restart. Adding the key only when there is something to say keeps
    # this version compatible with both servers, which is the only reason the two halves can be
    # landed in either order rather than needing an atomic cutover.
    if evidence:
        record["evidence"] = list(evidence)
    # ⚠⚠ `subjects` IS COVERAGE; `failing` IS INDICTMENT. They were ONE LIST until 2026-09-02
    # and that is `LED-10`: resolution is per `(step, path, blob)` with worst-verdict-wins, so a
    # FAIL naming all of its subjects condemns every file that merely sat BESIDE the bad one.
    # Measured that day -- `check_checkers` examined 24 files, failed on ONE, and its FAIL took
    # ownership of the 23 innocent blobs it shared with the passing tip record, condemning a
    # commit that PREDATED the offending file existing. Unclearable by any re-run, because a
    # later PASS cannot outrank a FAIL that owns the same content key.
    #
    # ⚠ THIS IS THE COVERAGE RULE SIGN-FLIPPED. `ledger_subjects` already refuses to attest to
    # bytes the checker did not read; condemnation is the same claim with the sign reversed and
    # had no such fence. `emit`'s own docstring specified the right shape all along -- a PASS
    # over the thirty-nine and a FAIL over the one -- which `V11` made unrepresentable as two
    # records. This expresses it as ONE record instead.
    #
    # ⚠ OMITTED WHEN EMPTY, for the reason the `evidence` block above gives. The server also
    # refuses `failing` on a non-FAIL verdict (stored and silently ignored = looks correct,
    # behaves otherwise) and refuses an EMPTY `failing` (it resolves to PASS at every path --
    # exoneration wearing a FAIL's costume). Absent `failing` still indicts every subject, so
    # no record written before this key existed is silently weakened.
    if failing:
        record["failing"] = sorted(set(failing))
    # ⚠⚠ V18: FINDINGS RIDE ON THE RECORD, NOT IN A REASON STRING. A gate that reaches its ORDINARY
    # cap under `R-LOOPCAP` is told to STOP AND PUSH — "reviewed, ordinary findings outstanding,
    # cap reached, proceed". That verdict ADMITS, so the findings must travel with it or they
    # evaporate at exactly the moment the work is allowed through.
    #
    # ⚠ A CLEAN PASS AND A CAPPED PASS ARE DIFFERENT FACTS. Both are SATISFIED downstream, so the
    # rendered line is the only place a reader can still tell them apart — it marks "⚠N
    # outstanding". Omitting this key is what a genuinely clean pass looks like; sending it empty
    # would claim findings exist and name none.
    #
    # ⚠ `outstanding` IS PART OF `payload()`, so re-recording the same verdict with findings
    # DROPPED is a V11 conflict rather than a silent dedupe. They cannot be edited away quietly.
    # And the server refuses `severity: bedrock` (or any word it does not know) on a PASS — the
    # severity split is the entire safety of this route and must never become a way to ship one.
    if outstanding:
        record["outstanding"] = list(outstanding)

    last_error = None
    for attempt in range(_TRANSPORT_TRIES):
        try:
            out = _call("append", {"record": record})
        except (urllib.error.URLError, OSError, TimeoutError) as exc:
            last_error = exc
            if attempt + 1 < _TRANSPORT_TRIES:
                time.sleep(_BACKOFF * (attempt + 1))
                continue
            print(f"UNDECIDED: verdictLedger unreachable at {URL} ({exc})")
            return None
        if out is None:
            print("UNDECIDED: verdictLedger returned no usable payload")
            return None
        if out.get("ok"):
            return out.get("id")
        # A refusal is TERMINAL. Do not retry it.
        errs = out.get("errors") or [out.get("error", "unknown")]
        print("UNDECIDED: record refused by verdictLedger:")
        for e in errs:
            print(f"  - {e}")
        return None
    print(f"UNDECIDED: verdictLedger unreachable ({last_error})")
    return None


# --------------------------------------------------------------------- the review-gate CLI
#
# ⚠⚠ WHY THIS EXISTS AND WHY IT IS SEPARATE FROM `common.record_if_asked`. Every mechanical checker
# emits through `common.emit_verdict`, which derives its own subjects and stamps
# `decided.how = "mechanical"` by default. A REVIEW gate cannot use that path: its subjects are the
# files a reviewer actually read (a decision, not a scan) and its verdict is a judgement. Until this
# existed there was NO way for `/editorial-review`, `/adversary-review`, `/prior-art-review` or
# `/rely` to record at all — they wrote `.claude-local/*_cleared.txt`, a file anyone could touch,
# keyed to a hash nothing content-addressed.
#
# ⚠⚠ `--how` IS REQUIRED AND HAS NO DEFAULT, DELIBERATELY. Defaulting it to "mechanical" would let a
# review gate silently claim a provenance it does not have, and defaulting it to anything else would
# be a guess about the ledger's schema. A missing `--how` REFUSES rather than picking one: the whole
# value of a review record is the answer to "who decided this, and how", and a wrong answer there is
# worse than no record, because it satisfies a gate that nothing actually reviewed.
#
# ⚠ SUBJECTS ARE READ FROM THE INDEX, NEVER HASHED HERE. `common.ledger_subjects` reads the blob id
# the index already stores and fences the paths that are not safe to record (untracked, outside the
# repo, differing from the index). A blob id is sha1("blob " + bytelength + "\0" + content) —
# computing one by hand is how the field that used to be called `sha256` made every record read
# STALE for ever, because the validator accepted a 64-hex digest while the comparator resolved a
# 40-hex object id.

def _cli(argv):
    import argparse
    import io
    # ⚠ IMPORTED BEFORE THE PARSER IS BUILT, so `--ref`'s default can be `common.INDEX` rather than
    # the literal "INDEX". A second spelling of a constant is the mirror defect at the smallest
    # possible scale, and this one decides what a verdict is ABOUT.
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import common
    ap = argparse.ArgumentParser(
        prog="record.py",
        description="Record a REVIEW gate's verdict in the ledger (mechanical checkers use "
                    "common.record_if_asked instead).")
    ap.add_argument("--step", required=True,
                    help="the registered step, e.g. editorial / adversary / prior_art / rely")
    ap.add_argument("--verdict", required=True, choices=["pass", "fail"],
                    help="the gate's verdict over the files it reviewed")
    ap.add_argument("--files", required=True, nargs="+",
                    help="repo-relative paths the review actually covered — its subjects")
    # ⚠ THE ENUMS ARE THE SERVER'S, MIRRORED HERE ONLY AS FAIL-FAST. The ledger refuses a bad value
    # either way — that is where the rule lives and this file holds no validation logic. Listing them
    # in `choices` turns a round trip into an immediate usage error, which matters for a gate brief
    # run by an agent that would otherwise read a refusal as "the ledger is down".
    ap.add_argument("--tier", required=True, choices=["A", "H"],
                    help="A = an agent gate actually ran; H = a human decided. 'M' is mechanical "
                         "and belongs to common.record_if_asked, not here.")
    ap.add_argument("--how", required=True,
                    choices=["delegated", "agreement", "signature", "override"],
                    help="delegated = ONE agent round, no consensus claimed (the normal route for "
                         "a gate brief); agreement = 3+ independent passes concurred and the round "
                         "RAN; signature = a PERSON accepted a verdict the round did not produce; "
                         "override = a regrade, the gate erred. 'mechanical' is REFUSED here.")
    # ⚠⚠ THE BRIEF, NOT THE AGENT — AND THIS IS WHY `delegated` NEEDED NO NEW MECHANISM.
    # Attribution is not authentication: `sign` already concedes that, and no key material exists
    # here, so "prove you are that agent" was never on the table. What IS checkable is WHICH
    # INSTRUCTIONS GOVERNED THE ROUND and whether they have since changed. So a delegated PASS
    # carries the brief's blob id, and **editing the brief stales the key and the gate re-runs**.
    # A delegated verdict cannot outlive its instructions. That is V16's machinery pointed at
    # review rather than at checkers.
    ap.add_argument("--evidence", nargs="+", default=None,
                    help="path(s) to the BRIEF this round ran under, e.g. "
                         ".claude/commands/adversary-review.md. REQUIRED for a delegated PASS. "
                         "Not the checker module — the instructions.")
    # ⚠ A FILE, NOT ARGV. Findings carry prose notes, and prose on a command line breaks on
    # length, quoting and encoding — the same reason `--reason-file` exists. JSON list of
    # {"severity": "ordinary", "note": "...", "path": "..."} ; `path` optional, `note` REQUIRED
    # (a finding nobody can read is lost, not carried).
    # ⚠⚠ SUPERSEDE, NOT OVERWRITE. V11 makes (step, basis, revision) unique, so a second,
    # different verdict about the SAME content is refused rather than silently replacing the
    # first — branching is unrepresentable, not merely detected. Raising the revision is the
    # sanctioned route the refusal itself names, and it is NOT a deletion: the original stays in
    # the append-only stream and `inventory` resolves the TIP only. That is what makes a regrade
    # auditable — you can always see what the verdict USED to be and that it changed.
    #
    # ⚠ Its absence was a real dead end: a /rely round hit V11, found no `--revision`, and
    # correctly stopped rather than retrying a rejected record. A refusal naming a remedy the
    # tool cannot perform is a remedy nobody can take (`LED-2`).
    ap.add_argument("--revision", type=int, default=0,
                    help="supersede an existing verdict at this basis (V11). The prior record "
                         "REMAINS in the stream; inventory resolves the tip. Use when a verdict "
                         "is genuinely being restated, never to retry a refusal.")
    ap.add_argument("--outstanding-file", default=None,
                    help="JSON file of findings to carry ON the record (V18). Use when the round "
                         "reached its ORDINARY cap and R-LOOPCAP says stop-and-push: the verdict "
                         "admits, and these ride with it so they do not evaporate. Only severity "
                         "'ordinary' may accompany a PASS.")
    ap.add_argument("--passes", type=int, default=1,
                    help="how many independent passes ran (agreement only)")
    ap.add_argument("--agreed", type=int, default=1,
                    help="how many of them concurred (agreement only)")
    ap.add_argument("--who", default=None, help="who decided it (agent id, or a person)")
    ap.add_argument("--reason", default=None, help="one line, recorded on a FAIL")
    # ⚠⚠ CONTENT NEVER TRAVELS ON A COMMAND LINE, AND HERE IT IS NOT A STYLE POINT. The PreToolUse
    # hook denies any command containing a word-boundary `git`, ARGUMENTS INCLUDED — so an honest
    # `--reason` describing a MIG-3 defect is blocked by the very token it has to name, and the
    # command reporting the finding cannot be run. Measured three times on 2026-08-24, by three
    # separate review agents. A file has no such edge.
    ap.add_argument("--reason-file", default=None,
                    help="path to a file holding the reason. Use this whenever the reason names a "
                         "denied token (`git`, `gh`) or contains quotes or non-ASCII.")
    # ⚠⚠ DEFAULT IS `INDEX`, NOT `HEAD`, AND THE OLD DEFAULT MADE THIS CLI UNUSABLE. Every review
    # brief says to STAGE the files it reviewed — and staging is precisely what makes content differ
    # from HEAD, so `ledger_subjects` fenced all of them and the run recorded NOTHING. Measured
    # 2026-08-24 on one five-file scope: `HEAD` -> 0 of 5 subjects, exit 2; `INDEX` -> 5 of 5.
    # A pre-commit gate's subject is the staged content, so that is what it records.
    ap.add_argument("--ref", default=common.INDEX,
                    help="basis ref (default INDEX = the staged content, which is what a "
                         "pre-commit review actually examined). Pass HEAD to record a review of "
                         "already-committed content.")
    # ⚠ V9 REFUSES A RECORD WITH NO RUN ID, and a spawned review gate has no pipeline to inherit one
    # from: `ZPLEDGER_RUN` is set by `batch.py precommit` and `hooks.py` only. Every brief mandates a
    # FRESH ISOLATED AGENT, so every review gate hit this and none could record. Naming the run
    # explicitly is not "the caller's imagination" — the gate invocation IS a run, and saying which
    # one is exactly what V9 asks for.
    ap.add_argument("--run", default=None,
                    help="run id for this gate invocation (V9). Required when ZPLEDGER_RUN is "
                         "unset. Use gate-<step>-<YYYY-MM-DD>.")
    a = ap.parse_args(argv)

    if a.reason_file:
        if a.reason:
            ap.error("pass --reason or --reason-file, not both")
        a.reason = io.open(a.reason_file, encoding="utf-8").read().strip()
    if a.run:
        os.environ["ZPLEDGER_RUN"] = a.run
    if not os.environ.get("ZPLEDGER_RUN"):
        ap.error("--run is required here: V9 refuses a record with no run id, and a spawned review "
                 "gate has no pipeline to inherit ZPLEDGER_RUN from. Pass --run "
                 "gate-%s-<YYYY-MM-DD>. Do NOT invent a pipeline run id to impersonate one."
                 % a.step)

    # ⚠ A SIGNATURE WITH NO SIGNATORY IS A `*_cleared.txt` WITH EXTRA STEPS. The file-based signals
    # this replaces could be created by anyone and recorded no author; if `who` may be null here, the
    # replacement inherits the defect it was built to remove. Required for the two human-authority
    # routes; an `agreement` record is authored by the passes themselves.
    if a.how in ("signature", "override") and not a.who:
        ap.error("--who is required with --how %s: a sign-off with no signatory records nothing "
                 "about who is accountable for it" % a.how)

    # ⚠⚠ THE `delegated` CONTRACT, AND IT EXISTS BECAUSE REVIEW HAD NO PASS ROUTE AT ALL.
    # Measured across the whole stream 2026-08-25: editorial 3xFAIL, adversary 3xFAIL, rely 3xFAIL —
    # **nine agent reviews, every one a FAIL, and no delegated review had ever recorded a PASS.**
    # Not once. `agreement` refuses a lone round (V3 wants 3 unanimous), `mechanical` is a lie about
    # a computation, and `signature` asserts a PERSON accepted it. A gate could report findings and
    # had no way to report success — so absence of a PASS meant nothing, which is the exact
    # ambiguity this ledger exists to remove, sitting inside the review layer the whole time.
    #
    # ⚠ `who` ON EVERY delegated RECORD, PASS OR FAIL. It names the GATE (e.g. "adversary"), not a
    # person and not a process — attribution, openly not authentication.
    if a.how == "delegated":
        if not a.who:
            ap.error("--who is required with --how delegated: name the GATE that ran "
                     "(e.g. --who adversary). It is attribution, not authentication.")
        if a.tier != "A":
            ap.error("--how delegated requires --tier A: it records that an AGENT gate actually "
                     "ran. 'H' claims a human decided, which is --how signature.")
        # ⚠ EVIDENCE ON THE PASS ONLY, AND THE ASYMMETRY IS DELIBERATE. A FAIL BLOCKS, so it cannot
        # fail-open; demanding the brief's blob from an agent that could not read the brief would
        # stop it reporting the finding at all. A PASS is what lets work through, so a PASS is what
        # must be pinned to the instructions that authorised it.
        if a.verdict == "pass" and not a.evidence:
            ap.error("--evidence is required for a delegated PASS: give the path to the BRIEF this "
                     "round ran under (e.g. .claude/commands/adversary-review.md). A PASS is what "
                     "lets work through, so it is pinned to the instructions that authorised it — "
                     "edit the brief and this key goes stale, and the gate re-runs. A FAIL needs "
                     "no evidence: it blocks, so it cannot fail-open.")
    elif a.evidence:
        ap.error("--evidence belongs to --how delegated. The other routes record a human decision "
                 "or a genuine multi-pass agreement, neither of which is pinned to one brief.")

    # ⚠ V3 IS MIRRORED HERE ONLY TO FAIL FAST, AND THE DEFAULT IS THE TRAP IT CLOSES. A PASS under
    # `agreement` needs `agreed == passes` AND `passes >= policy.agreement.min_passes` (3). The
    # natural default is one pass — a single agent round — which produces a record that is accepted
    # and then does NOT satisfy the gate, so the operator sees "recorded PASS" and the push still
    # refuses with nothing connecting the two. Refusing at parse time says which of the two routes
    # they actually want.
    # ⚠ AND THE ANSWER IS USUALLY THE OTHER ROUTE. Each review gate spawns ONE fresh agent, so an
    # honest single round is not `agreement` at all; a human accepting it is `signature`, which is
    # deliberately a different signal — an accept is corpus DEBT, where `override` is evidence the
    # step is defective. They must never share a code path.
    # ⚠⚠ CONDITIONED ON **PASS**, BECAUSE V3 IS. The server's rule is `verdict: PASS` + `how:
    # agreement` requires unanimity at or above the threshold. This mirror applied it to EVERY
    # verdict, which made it STRICTER THAN ITS OWN AUTHORITY and rejected a lone agent's FAIL.
    # ⚠ Live routing is `tools/process/review-gates.md` and the gate briefs: since 2026-08-25 an
    # agent records BOTH its FAIL and its PASS under `--how delegated`, and `agreement` stays the
    # stronger claim for a genuine three-pass round. The earlier "FAIL alone, PASS by unanimity or
    # signature" doctrine is RETIRED, and the file that stated it is not in this repository.
    # A single review agent that finds a real defect must be able to record it — withholding a FAIL
    # because one agent is not a quorum is absence-of-evidence rendering as success, which is the
    # defect this entire ledger exists to remove. Measured 2026-08-24: with the guard unconditional,
    # a lone gate had NO recordable verdict at all, and every review key stayed MISSING while seven
    # honest rounds wrote seven files nothing read.
    if a.verdict == "pass" and a.how == "agreement" and (a.passes < 3 or a.agreed != a.passes):
        ap.error("a PASS under --how agreement needs --passes >= 3 with --agreed equal to it (V3, "
                 "policy.agreement.min_passes = 3); got passes=%d agreed=%d. One agent round is "
                 "not an agreement - if a human is accepting it, use --how signature --who <name>. "
                 "A FAIL needs none of this: one agent's finding stands on its own."
                 % (a.passes, a.agreed))

    # ⚠⚠ NO CHECK CAN DECIDE WHETHER A NAME BELONGS TO A PERSON, SO IT IS STATED INSTEAD OF TESTED.
    # `agreement` refuses a single agent round, which makes the tempting fix `signature` with the
    # AGENT as `who` — and that is the anonymous-approval hole V5 closes, with a robot's name written
    # in it. `signature` asserts that a person accepted a verdict the round did not produce; an agent
    # cannot be accountable for that. The two honest shapes are: the agent produces findings and a
    # PERSON signs, or the gate genuinely runs three passes and records `agreement`.
    # ⚠ This prints on every signature rather than only on a suspicious one, because "suspicious"
    # would be a guess at a name, and a warning that fires selectively teaches people to read the
    # absence of it as approval.
    if a.how == "signature":
        print("  signature: recording that a PERSON accepted this - %s." % a.who)
        print("  If that is an agent, this record claims an accountability that does not exist;")
        print("  a single agent round is not a review anyone signed. Use 3 passes + --how agreement.")

    subjects, skipped = common.ledger_subjects(sorted(set(a.files)), a.ref)
    for rel, why in skipped:
        print("  not recorded: %-52s %s" % (rel, why))
    if not subjects:
        # ⚠ EXIT 2, NEVER 0. "nothing recordable" is not "the review passed" — a gate reporting
        # success while writing no key leaves the step MISSING and the operator believing it is done.
        print("  nothing recordable for %s at %s — the review certified no recordable file"
              % (a.step, a.ref))
        return 2
    # ⚠ `module_evidence` COMPOSES UNCHANGED — it hashes working-tree bytes to a repo-relative
    # path with forward slashes, which is exactly what the brief needs; only the TARGET differs
    # (the instructions, not the producing module). A brief that does not exist yields NO entry,
    # so the server refuses with its own message rather than accepting a fabricated blob id.
    # ⚠ MIRRORED HERE ONLY TO FAIL FAST. The server owns V18 and refuses either way; catching it
    # at parse time means a gate brief gets a usage error naming the rule, rather than a refusal
    # an agent might read as "the ledger is down".
    outstanding = ()
    if a.outstanding_file:
        outstanding = json.loads(io.open(a.outstanding_file, encoding="utf-8").read())
        if not isinstance(outstanding, list) or not outstanding:
            ap.error("--outstanding-file must hold a non-empty JSON list of findings; omit the "
                     "flag entirely for a genuinely clean pass")
        for f in outstanding:
            if not isinstance(f, dict) or not f.get("note"):
                ap.error("every outstanding finding needs a `note`: a finding nobody can read is "
                         "lost, not carried, and the record would assert findings exist while "
                         "saying nothing about them")
            if a.verdict == "pass" and f.get("severity") != "ordinary":
                ap.error("a PASS may only carry severity 'ordinary'; got %r. This route exists for "
                         "R-LOOPCAP's stop-and-push at the ORDINARY cap and must NEVER become a "
                         "way to ship a bedrock or blocking finding — BEDROCK gets 5 rounds and "
                         "must not ship. Record the FAIL instead." % f.get("severity"))
    ev = module_evidence(*a.evidence) if a.evidence else ()
    if a.evidence and len(ev) != len(set(a.evidence)):
        print("  WARNING: %d brief path(s) given, %d resolved — a brief that is absent or "
              "untracked contributes NO evidence, and the ledger will refuse the PASS rather "
              "than accept an unpinned one." % (len(set(a.evidence)), len(ev)))
    rid = emit(step=a.step, tier=a.tier, verdict=a.verdict.upper(), subjects=subjects,
               basis=common.ledger_basis(a.ref), reason=a.reason, evidence=ev,
               outstanding=outstanding, revision=a.revision,
               decided={"how": a.how, "passes": a.passes, "agreed": a.agreed, "who": a.who})
    if rid is None:
        return 2
    print("  recorded %-4s %4d subject(s)  %s" % (a.verdict.upper(), len(subjects), rid))
    return 0


if __name__ == "__main__":
    sys.exit(_cli(sys.argv[1:]))
