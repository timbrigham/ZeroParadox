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
import uuid
import urllib.error
import urllib.request

# ⚠⚠ THE REFUSAL EXPLANATION IS THE ONE OUTPUT THAT MUST SURVIVE A REDIRECT, AND IT DID NOT.
# `common.py:90` and `check_briefs.py:29` both reconfigure; this module — the only one that prints
# the SERVER's violation text — did not. Measured 2026-09-07: a dry run whose record the ledger
# refused died at `print("  - %s" % e)` with `UnicodeEncodeError: '⚠'`, because V-rule messages
# carry ⚠ and a redirected stdout is cp1252 on this platform. The caller saw a traceback and exit 1
# where the reason was already in hand and one print away.
# ⚠ `CLAUDE.md` R-TRUNC MANDATES REDIRECTION for every checker run, so the crashing configuration is
# the SANCTIONED one — the defect could only ever fire on the path the project tells you to use.
# `DC-21`, whose recorded instance is this failure in `check_paths.py` printing the same glyph.
# `errors='replace'` matches `check_briefs`: a mangled glyph is a legible message, a traceback is not.
sys.stdout.reconfigure(encoding="utf-8", errors="replace")

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


# ⚠⚠ A PER-PROCESS TRIPWIRE, NOT A CUMULATIVE COUNT — and the difference is not pedantry.
# `record.py` is a CLI that runs once and exits, so this list starts EMPTY in every process and
# can never total anything. It makes a firing IMPOSSIBLE TO MISS within a run (the NOTE in `_call`
# names the tool and prints), which is what stops the fallback becoming silently load-bearing.
# **It is NOT the measurement that the far side stopped prefixing.**
#
# ⛔ AN EARLIER COMMENT HERE CLAIMED IT WAS — "the count going to zero is the measurement that
# step 3 worked." FALSE, and self-flatteringly so: the count is zero at process start whether the
# world is healthy or on fire, so a zero proves nothing at all. Corrected 2026-09-06 after the
# peer's server-side tally (87 calls, 0 prefixed bodies) turned out to be the only thing actually
# measuring the property. **THE AUTHORITATIVE COUNT IS SERVER-SIDE**; when this repo's own call
# log lands, a durable count belongs there and this stays the loud local tripwire.
BRACE_FALLBACKS = []


def _call(tool: str, arguments: dict):
    """One MCP round trip. Returns the parsed tool payload, or None."""
    # ⚠⚠ A UUID, NOT A CONSTANT, AND IT IS THE JOIN KEY FOR TWO-SIDED LOGGING (2026-09-06).
    # JSON-RPC lets the CALLER choose `id`; it passes through the MCP layer untouched and needs no
    # header negotiation. The server logs it verbatim as `rpc_id`, so our record of what we SENT and
    # its record of what ARRIVED become joinable — the disagreement check applied to the transport.
    # This used to send `1` and `2`, and constant ids join nothing.
    # ⚠ `(tool, timestamp, byte count)` was the alternative and it very nearly works — one host, one
    # clock. It fails exactly where it is needed: a RETRY LOOP emits an identical tool name and an
    # identical byte count inside the same second, and retries against a refusal are the single most
    # interesting thing this log exists to catch. A key that goes ambiguous on the only question it
    # was built for is not a key.
    # ⚠ `notifications/initialized` carries no id BY SPEC and must not be given one; those rows join
    # on the session alone, which is correct — there is no response to compare either.
    init_id, call_id = str(uuid.uuid4()), str(uuid.uuid4())
    sid, body = _post({"jsonrpc": "2.0", "id": init_id, "method": "initialize",
                       "params": {"protocolVersion": "2025-06-18", "capabilities": {},
                                  "clientInfo": {"name": "zp-record", "version": "1"}}})
    _post({"jsonrpc": "2.0", "method": "notifications/initialized"}, session=sid)
    _, body = _post({"jsonrpc": "2.0", "id": call_id, "method": "tools/call",
                     "params": {"name": tool, "arguments": arguments}}, session=sid)
    res = _parse(body)
    if not res or "result" not in res:
        return None
    result = res["result"]
    content = result.get("content") or []
    if not content:
        return None
    text = content[0].get("text", "") if isinstance(content[0], dict) else ""

    # ⚠⚠ `isError` IS READ, AND TRUE IS TERMINAL — NEVER RETRIED. A `true` here means the server
    # DECIDED to refuse; re-sending cannot change a validation verdict, only mask it as an outage.
    #
    # ⚠ THIS COMMENT USED TO DESCRIBE THE SERVER'S CURRENT STATE AND WENT STALE IN TWENTY MINUTES.
    # It read "today every refusal, success and validation rejection returns `isError: false`" —
    # true when written, false by the time the flip landed the same afternoon (2026-09-06), in a
    # file on the recording path describing a system this repo cannot see. Caught by the peer that
    # changed it, not by us. **DESCRIBE WHAT THIS CODE DOES AND WHY, NEVER WHAT THE FAR SIDE
    # CURRENTLY DOES** — the far side's state is not ours to assert, and a comment that pins it
    # decays the moment they ship. The mechanism below is correct under either behaviour, which is
    # the property that actually matters and the reason nothing broke.
    is_error = bool(result.get("isError"))

    try:
        payload = json.loads(text)
    except (ValueError, AttributeError):
        # ⚠⚠ THE BELT, AND IT IS DELIBERATELY A BELT RATHER THAN THE CONTRACT. Raising `ToolError`
        # is the only route to `isError: true` under FastMCP, and the low-level server REWRITES the
        # content to `Error executing tool <name>: {json}` — which is not valid JSON, so a strict
        # parse collapses the whole structured refusal to None and we would silently lose
        # `error_type` and the `errors` list. That is precisely the information distinguishing a
        # validation refusal from an outage.
        # ⛔ DEPENDING ON THAT PREFIX IS PROSE-COUPLING at the transport, on the commit path — the
        # defect class this project spent two days filing (`DC-45`, `R-ZERONULL`). It is accepted
        # ONLY as an interim, and ONLY because it is instrumented: the destination is the server
        # dropping to the low-level tool API so `content[0].text` stays pure JSON, at which point
        # this branch becomes dead code. **A NON-ZERO COUNT AFTER THAT LANDS IS A DEFECT, NOT NOISE.**
        payload = None
        if isinstance(text, str):
            i, j = text.find("{"), text.rfind("}")
            if 0 <= i < j:
                try:
                    payload = json.loads(text[i:j + 1])
                    BRACE_FALLBACKS.append(tool)
                    print("  NOTE: structured payload recovered by brace-slice for %r (fallback #%d)"
                          " — the server prefixed its error body. This path is INTERIM; if it is "
                          "still firing after the low-level API change, that is a defect."
                          % (tool, len(BRACE_FALLBACKS)))
                except ValueError:
                    payload = None
        if payload is None:
            return None

    # ⚠ THE `None` FLOOR IS UNCHANGED AND STAYS. `emit` returning None makes the caller BLOCK and
    # exit 2; that is correct and it is the floor under everything above.
    if is_error and isinstance(payload, dict):
        payload.setdefault("ok", False)
        payload["_transport_is_error"] = True
    return payload


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


def reachable():
    """Does the ledger ANSWER right now? True or False — never a message, never None.

    ⚠⚠ THIS EXISTS TO SPLIT ONE EXIT CODE IN TWO, AND THAT IS ITS WHOLE JOB. `emit` returns `None`
    for two different facts — the ledger REFUSED the record, and the ledger could not be REACHED —
    and every caller downstream sees one value. So a `V8` refusal (the step is not registered) and
    an outage arrive at `hooks.py` as the same exit 2, and it printed "unreachable" for both.
    Measured 2026-09-06 (`B4`): `check_briefs` was unregistered, the ledger reached it and said so
    precisely, and the operator was told the ledger was down. **The exit-2 design exists to keep
    "could not decide" apart from "decided no"; collapsing refusal into outage re-creates the very
    conflation one layer up.**

    ⚠ IT ASKS, IT DOES NOT INFER. A refusal is only distinguishable by observing that the server
    answered something else a moment earlier, so this makes a real round trip rather than reading a
    cached flag. The residual is a genuine race — the ledger could fall over between the refused
    append and this call — which misreports a refusal as an outage. That direction is the safe one:
    both still BLOCK, and an outage is the diagnosis that gets re-run and discovers itself, where a
    false refusal would send someone editing a record that was fine.

    ⚠ `False` ON ANY FAILURE TO ASK, INCLUDING A MALFORMED ANSWER. "I could not tell" belongs with
    "unreachable" here, because the only claim this function is allowed to make is the positive one:
    the server spoke, so a refusal it issued was a decision.
    """
    try:
        out = _call("status", {})
    except (urllib.error.URLError, OSError, TimeoutError):
        return False
    return isinstance(out, dict) and bool(out.get("ok"))


def build_record(step, tier, verdict, subjects, basis, reason=None,
                 inputs=(), decided=None, cost=None, revision=0, evidence=(), outstanding=(),
                 failing=()):
    """The record dict, built once so `emit` and `check` post IDENTICAL bytes.

    ⚠⚠ ONE CONSTRUCTOR, BECAUSE A DRY RUN THAT BUILDS DIFFERENT BYTES CHECKS NOTHING.
    `--dry-run` answers "would the ledger take this record", and it can only answer that if what
    it validates is what `emit` would append — including the three keys OMITTED WHEN EMPTY
    (`evidence`, `failing`, `outstanding`), which is precisely where a second constructor would
    drift. This is the mirror defect the module docstring refuses at the RULES layer, applied to
    the PAYLOAD: there is no second implementation to disagree.

    `subjects` is a list of {"path", "git_blob_id"} — WHAT THIS VERDICT IS ABOUT, not
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
    # refuses `failing` on a NON-BLOCKING verdict (stored and silently ignored = looks correct,
    # behaves otherwise) and refuses an EMPTY `failing` (it resolves to PASS at every path --
    # exoneration wearing a blocking verdict's costume). Absent `failing` still indicts every
    # subject, so no record written before this key existed is silently weakened.
    #
    # ⚠⚠ "NON-BLOCKING" IS THE SERVER'S WORD AND IT IS NOT A SYNONYM FOR "NON-FAIL". This comment
    # said `non-FAIL` until 2026-09-06 and that was measurably wrong: `failing` validates on
    # UNDECIDED and is refused only on PASS. The set that BLOCKS is {FAIL, UNDECIDED}; the set that
    # ADMITS is {PASS}. Reading the first as "FAIL alone" is how a third verdict gets treated as an
    # abstention that lets work through.
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
    return record


def check(**kw):
    """VALIDATE a record without writing it. Returns `(ok, errors)`, or `None` if unreachable.

    ⚠⚠ THE THREE ANSWERS ARE THREE DIFFERENT VALUES, NOT THREE DIFFERENT MESSAGES (`R-ZERONULL`).
    `(True, [])` the ledger would accept it · `(False, [errors...])` it would refuse, and EVERY
    violation is named rather than only the first · `None` the ledger could not be ASKED.
    Collapsing the third into `(False, [])` is the exact shape this layer exists to remove: an
    outage would read as a refusal with nothing wrong in it, and a caller testing `errors` would
    find none and conclude the record was fine.

    ⚠ NO RETRY AND NO LOCAL FALLBACK. `validate` is pure server-side, so a refusal is terminal
    exactly as it is on `append`; a transport failure returns `None` and the caller must not
    proceed as though the record were good. There is deliberately no local copy of the rules to
    fall back to — that is the mirror defect, and it would be worst here, where the entire purpose
    is to ask the authority instead of guessing.
    """
    record = build_record(**kw)
    try:
        out = _call("validate", {"record": record})
    except (urllib.error.URLError, OSError, TimeoutError) as exc:
        print(f"UNDECIDED: verdictLedger unreachable at {URL} ({exc})")
        return None
    if not isinstance(out, dict) or "ok" not in out:
        print("UNDECIDED: verdictLedger returned no usable payload for validate")
        return None
    return bool(out.get("ok")), list(out.get("errors") or [])


def emit(step, tier, verdict, subjects, basis, reason=None,
         inputs=(), decided=None, cost=None, revision=0, evidence=(), outstanding=(),
         failing=()):
    """Append one record. Returns its id, or None if refused or unreachable.

    ⚠ The record is built by `build_record`; this function is the WRITE. The split is what lets
    `check` interrogate the identical payload without performing one.
    """
    record = build_record(step=step, tier=tier, verdict=verdict, subjects=subjects, basis=basis,
                          reason=reason, inputs=inputs, decided=decided, cost=cost,
                          revision=revision, evidence=evidence, outstanding=outstanding,
                          failing=failing)

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
    # ⚠⚠ `undecided` IS A THIRD VERDICT AND IT BLOCKS — IT IS NOT A SOFTER FAIL, AND THE BRIEFS
    # ASKED FOR IT BEFORE THE CLI COULD EMIT IT. `copy-editor.md` instructs recording UNDECIDED when
    # a round cannot decide, and until 2026-09-06 `choices` held two values, so the command the brief
    # printed was a usage error. A brief instructing an impossible command is a gate with no way to
    # record at all — the `check_briefs` defect class, pointed at the recorder itself (`B5`).
    #
    # ⚠ THE WIRE VALUE IS UPPERCASE AND THE SERVER MATCHES IT EXACTLY: the enum is
    # ('PASS', 'FAIL', 'UNDECIDED') and `'undecided'` is refused by name. `.upper()` at the `emit`
    # call below is the whole mechanism. ⚠ The OPPOSITE rule holds one call away — `find()` IS
    # case-insensitive and advertises it. Two entry points, two rules; do not generalise either.
    #
    # ⚠⚠ UNDECIDED BLOCKS, AND THAT IS MEASURED RATHER THAN ASSUMED. Against the running server
    # 2026-09-06: `failing` is ACCEPTED on FAIL and on UNDECIDED and REFUSED on PASS, with the
    # server's own message naming "a verdict that BLOCKS — FAIL or UNDECIDED"; and
    # `stale_or_missing` above already counts UNDECIDED among the steps needing a re-run. So an
    # UNDECIDED record satisfies nothing and admits nothing. **It says "this round produced no
    # decision", which is the one thing a two-valued enum forced a gate to lie about** — the
    # absence-rendering-as-something-else shape this whole ledger exists to remove.
    ap.add_argument("--verdict", required=True, choices=["pass", "fail", "undecided"],
                    help="the gate's verdict over the files it reviewed. `undecided` BLOCKS exactly "
                         "as `fail` does: use it when the round could not decide, NEVER to soften a "
                         "finding it did reach.")
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
    # ⚠⚠ `subjects` IS COVERAGE; `failing` IS INDICTMENT — AND UNTIL 2026-09-06 THIS CLI COULD ONLY
    # EXPRESS THE FIRST. `emit()` has taken `failing` since 2026-09-02 and `common.emit_verdict`
    # passes it, so every MECHANICAL step has named its indicted subset since 09-03. The review
    # gates never could: there was no flag. Measured on the live stream, and the number is the
    # tell — **118 of 118 tier-A blocking records carry no `failing`, and not one ever has.**
    # A gap that is CATEGORICAL rather than partial is almost never discipline; it is a missing
    # affordance, and this is the affordance.
    #
    # ⚠ WHY IT MATTERS, in one measured row: a `check_prose` FAIL from 2026-09-02 carries 218
    # subjects and a reason reading "1 failing subject(s)". The record KNOWS it indicts one file,
    # says so in prose, and condemns 218 — because absent `failing` means "indicts every subject".
    # The machine-readable half said all; the human-readable half said one; every consumer reads
    # the first.
    #
    # ⚠ A FILE, NOT ARGV, and for the same reason `--reason-file` exists one flag down: a list of
    # repo paths is exactly the payload that breaks on Windows argv length, on quoting, and on the
    # PreToolUse hook that denies any command containing a word-boundary denied token.
    ap.add_argument("--failing-file", default=None,
                    help="JSON file holding a non-empty list of repo-relative paths this verdict "
                         "actually INDICTS, a subset of --files. Required in spirit on any "
                         "blocking verdict: absent `failing` indicts EVERY subject, so omitting it "
                         "on a FAIL over 40 files condemns 39 that passed.")
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
    # ⚠⚠ THE LEDGER HAS ALWAYS EXPOSED `validate` — PURE, NO WRITE, EVERY VIOLATION AT ONCE — AND
    # THIS CLI MENTIONED IT ZERO TIMES. So the only way to ask "does this command work" was to run
    # it, and running it APPENDS. That is not a hypothetical cost: a `/rely` agent probing
    # `--failing-file` put a FAIL reading "probe reason - do not use" into the live stream, where it
    # is append-only, correctly keyed, about real content, and blocks a tag today. **The record is
    # not wrong; it should never have been produced**, and nothing existed to produce it any other
    # way. Same shape as `--failing-file` itself: the capability was there and no caller could
    # express it (`LED-2` — a refusal naming a remedy the tool cannot perform).
    #
    # ⚠ IT EXERCISES THE WHOLE CLIENT PATH, WHICH IS WHY IT IS A FLAG AND NOT A SEPARATE SCRIPT.
    # Every argparse guard, `ledger_subjects` fencing, `ledger_basis` resolution, `module_evidence`
    # hashing and `build_record`'s omit-when-empty keys all run exactly as they would on a real
    # record; only the final verb changes from `append` to `validate`. A dry run that skipped any of
    # that would be checking a different command from the one the brief prints.
    #
    # ⚠ THREE EXIT CODES, MATCHING THIS MODULE'S DOCTRINE: 0 the ledger would accept it · 1 it would
    # refuse, and every reason is printed · 2 the ledger could not be asked. Reading 2 as 1 turns an
    # outage into "your record is bad", which sends a gate off editing a record that was fine.
    # ⚠ DECLARED so it appears in `--help` and in `_actions` like any other flag, and handled
    # below before `parse_args`, which would otherwise demand a full record to answer it.
    ap.add_argument("--list-flags", action="store_true",
                    help="print one option string per line and exit — the PARSER's own list, for "
                         "a checker that needs to know what this program accepts without reading "
                         "its help prose.")
    ap.add_argument("--dry-run", action="store_true",
                    help="VALIDATE the record against the ledger and print what it would say, "
                         "WITHOUT appending. Use this to check a command — never the live stream. "
                         "Exit 0 = would be accepted, 1 = would be refused, 2 = ledger unreachable.")
    # ⚠⚠ THE PARSER'S OWN TRUTH, BECAUSE `--help` IS PROSE AND PROSE IS NOT AN INTERFACE.
    # `check_briefs` asks this program which flags exist, and it used to ask by scraping `--help`
    # for anything shaped like a flag. That reads DESCRIPTIONS as well as options, so a flag named
    # only inside a help string becomes ground truth and every brief may then cite a flag that does
    # not exist. Latent on 2026-09-06 — the two sets agreed exactly, 18 and 18 — and armed by one
    # prose edit. `B3`.
    #
    # ⚠ `_actions` IS PRIVATE AND IT IS STILL THE RIGHT SOURCE. argparse exposes no public accessor
    # for "what does this parser accept", and every public alternative is formatted text: usage
    # wraps, help interleaves descriptions. A private attribute that IS the answer beats a public
    # one that has to be parsed back out of English.
    #
    # ⚠ HANDLED BEFORE `parse_args`, because the required flags are required. Asking a program to
    # describe itself must not require a valid record first.
    if "--list-flags" in argv:
        for act in ap._actions:
            for opt in act.option_strings:
                if opt.startswith("--"):
                    print(opt)
        return 0
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
        #
        # ⛔⛔ BUT "A FAIL NEEDS NO EVIDENCE" IS FALSE ABOUT THE SERVER, AND THIS COMMENT ASSERTED IT
        # FOR DAYS (RLYB-3). Measured 2026-09-08: `--how delegated --verdict fail` with no
        # `--evidence` reaches the ledger and is REFUSED by V21, *"this verdict names no blob"* —
        # V21 exempts only `signature` and `override`. So the record is UNEMITTABLE, and on a real
        # emit the refusal returns exit 2, which every gate brief tells the agent to read as a
        # LEDGER OUTAGE rather than as a usage error. A true FAIL can be lost that way.
        # ⚠ THE PERMISSIVENESS BELOW IS STILL RIGHT and is deliberately not changed: a client guard
        # must never be the thing that stops a real FAIL from landing. **Only the comment was
        # wrong.** All five gate-brief templates already pass `--evidence` on FAIL, so nothing in
        # this repo takes the broken path today. The durable fix is the same shape as the
        # `agreement` branch one `elif` below — require it and say why — and it is deliberately
        # NOT taken tonight, because widening a refusal on the FAIL path is exactly the change that
        # could swallow a finding. Left as a stated bill, not a silent one.
        if a.verdict == "pass" and not a.evidence:
            ap.error("--evidence is required for a delegated PASS: give the path to the BRIEF this "
                     "round ran under (e.g. .claude/commands/adversary-review.md). A PASS is what "
                     "lets work through, so it is pinned to the instructions that authorised it — "
                     "edit the brief and this key goes stale, and the gate re-runs. A FAIL needs "
                     "no evidence: it blocks, so it cannot fail-open.")
    elif a.how == "agreement":
        # ⚠⚠ AGREEMENT CARRIES EVIDENCE, AND REFUSING IT HERE CLOSED THE ROUTE ENTIRELY.
        # Measured 2026-09-08, both halves: this client refused `--evidence` on `--how agreement`,
        # while the server's V21 refuses any verdict naming no blob and exempts only
        # signature/override. Client forbids the field, server requires the field, so an
        # agreement record was UNEMITTABLE — a documented route nobody could take. Neither half
        # was wrong alone; the route closed only in the conjunction, and neither owner was
        # looking at it. Verified by posting an agreement record WITH evidence straight to
        # `validate`, bypassing this file: V11 alone came back (a basis collision), no V21 and
        # no objection to the field.
        #
        # ⭐ THE PREMISE THE OLD MESSAGE GOT WRONG, and it is a real distinction rather than a
        # carve: THREE AGENTS FOLLOWING ONE BRIEF HAVE ONE PRODUCER. The brief is the artifact
        # that produced the verdict, exactly as for a delegated round; what differs is how many
        # agents read it, which is `passes`/`agreed` — headcount, not provenance. `signature`
        # and `override` are genuinely different in KIND: a human accept and a regrade have no
        # producing file at all. So the old sentence was true of those two and false of this one.
        #
        # REQUIRED rather than merely permitted, because V21 will refuse it downstream anyway and
        # a local refusal names the remedy; a server round trip spends a call to say the same thing.
        if not a.evidence:
            ap.error("--evidence is required for --how agreement: give the path to the BRIEF the "
                     "panel ran under. Three agents following one brief have ONE producer, so the "
                     "record is pinned to it exactly as a delegated round is — V21 refuses any "
                     "verdict that names no blob, because staleness is computed by watching a "
                     "named blob move. Only --how signature and --how override are exempt, and "
                     "they are exempt because a human decision has no producing file at all.")
    elif a.evidence:
        ap.error("--evidence belongs to --how delegated or --how agreement — both are produced by "
                 "a BRIEF, and a panel of three reading one brief still has one producer. "
                 "--how signature (a human accept) and --how override (a regrade) have no "
                 "producing file at all, which is a difference in KIND rather than headcount.")

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
    # ⚠⚠ VALIDATED AGAINST THE POST-FENCE `subjects`, NEVER AGAINST `--files`. `ledger_subjects`
    # DROPS paths absent from the ref or differing from the index, so `--files` is what the caller
    # asked for and `subjects` is what is actually being recorded. Indicting a path that was fenced
    # out would name something the record does not cover — coverage and indictment would disagree
    # inside one record, which is worse than either being wrong alone.
    failing = ()
    if a.failing_file:
        failing = json.loads(io.open(a.failing_file, encoding="utf-8").read())
        if not isinstance(failing, list) or not failing or \
                not all(isinstance(p, str) and p.strip() for p in failing):
            ap.error("--failing-file must hold a non-empty JSON list of repo-relative path "
                     "strings. ⚠ An EMPTY list is not 'nothing failed' — the server refuses it, "
                     "because it resolves to PASS at every path and is exoneration wearing a "
                     "FAIL's costume. Omit the flag entirely to indict every subject.")
        if a.verdict == "pass":
            ap.error("--failing-file is refused on a PASS: `failing` is an INDICTMENT and a PASS "
                     "indicts nothing. Stored on a PASS it would be silently ignored — looks "
                     "correct, behaves otherwise. Use --outstanding-file to carry findings on a "
                     "verdict that admits.")
        failing = sorted({p.strip().replace("\\", "/") for p in failing})
        covered = {s["path"] for s in subjects}
        stray = [p for p in failing if p not in covered]
        # ⛔⛔ THE PROPERTY IS *DOES THIS ELEMENT CLAIM TO BE ABOUT BYTES*, NOT *DOES IT LOOK LIKE A
        # PATH*. An element purporting to name CONTENT must name content this verdict EXAMINED —
        # that is the content-keying rule with the sign flipped: **condemnation needs the same proof
        # as coverage.** An element naming something that is NOT content cannot be keyed to bytes at
        # all, which is precisely why it cannot gate, so refusing it buys nothing and costs the one
        # honest case.
        #
        # ⚠⚠ THE TEST BELOW IS A **PROXY** FOR THAT PROPERTY AND IS DECLARED AS ONE. Do not extend
        # the extension list thinking you are tightening the rule — you are only widening the proxy.
        # `check_checkers` row 5 is `(roster)`, a property of a PAIR of files with no single path to
        # hang on; until 2026-09-07 this refusal blocked the exact indictment this bundle's own
        # checker emits, while `validate()` accepted it. Measured, CLI exit 2 against server ok.
        #
        # ⚠ TWO KNOWN MISFIRES, WRITTEN DOWN BECAUSE THE PROXY WILL HIT THEM:
        #   * a between-files finding spelled `tools/verify/batch.py <-> ship.py` contains a slash
        #     and `.py`, so it is REFUSED — the legitimate case this exception exists to permit.
        #   * a typo'd label `(rosetr)` is parenthesised and PERMITTED, warned but not caught.
        # The proxy catches typos in the path class and misses them in the label class. That is a
        # cost of the shape test, not an argument against it — the alternative is refusing the
        # honest case to catch a misspelling nothing acts on.
        PATHISH = (".py", ".md", ".lean", ".json", ".txt", ".ps1", ".toml", ".yml", ".yaml")
        claims_content = [p for p in stray if "/" in p or p.endswith(PATHISH)]
        label_only = [p for p in stray if p not in claims_content]
        if claims_content:
            ap.error("--failing-file names %d path(s) that are NOT among the recorded subjects: "
                     "%s. You cannot indict content this record does not claim to have examined — "
                     "condemnation needs the same proof as coverage. ⚠ A typo and a real-but-"
                     "unexamined path are different errors with the same remedy: either add them to "
                     "--files, or check whether they were fenced out above (`not recorded:` lines "
                     "name every drop and why)."
                     % (len(claims_content), ", ".join(claims_content[:5])))
        if label_only:
            # ⚠ PERMITTED AND DISCLOSED, never permitted silently. `inventory.py` builds `indicted`
            # by walking SUBJECTS, so an element that is not one is never iterated: it contributes
            # no entry, cannot block a commit, and cannot prevent `tip_green` forgiveness. Measured
            # by mcpdev 2026-09-07. Naming it keeps the finding in the record; the warning stops
            # anyone reading its presence as enforcement.
            print("  WARNING: --failing-file names %d element(s) that are not among the subjects "
                  "and do not name content: %s." % (len(label_only), ", ".join(label_only[:5])))
            print("           These are RECORDED but INERT — the gate builds its indictment by")
            print("           walking subjects, so a non-subject contributes nothing and will not")
            print("           block a commit or prevent tip_green forgiveness. Honest, not enforced.")
    elif a.verdict == "fail":
        # ⚠⚠ NOW A REFUSAL. This branch shipped 2026-09-06 as a WARNING with its own expiry written
        # into it — *"the server does not yet require `failing`; when it does, this becomes the usage
        # error"* — and that condition is being met: verdictLedger's V-rule requiring a non-empty
        # `failing` on a blocking verdict lands after this change. CLIENT FIRST, deliberately and in
        # that order: shipping the server rule while this still defaulted to `()` would refuse every
        # delegated agent verdict on its next FAIL, with no local message explaining why. Same
        # sequencing `isError` used, for the same reason.
        #
        # ⚠ WHY THE CLIENT RULE IS NOT SUFFICIENT ON ITS OWN, so nobody deletes the server half as
        # redundant: `LED-6` is open because a rule whose ONLY enforcing copy is a client is a rule
        # with no enforcement — an agent reaching `append` directly never passes through here. The
        # two halves are one rule and neither is decoration.
        #
        # ⚠ THE OTHER HALF OF THIS ASYMMETRY HAS BEEN ALONE SINCE THE FIELD LANDED: `--failing-file`
        # is already refused on a PASS, forty lines up, because "a PASS indicts nothing". A blocking
        # verdict with NO indictment is the same error inverted — it indicts EVERYTHING, silently.
        # One rule, written half at a time.
        #
        # ⛔⛔ FAIL ONLY — AND THIS REVERSES THE PARAGRAPH THAT STOOD HERE FOR TWENTY MINUTES, WHICH
        # ARGUED THE OPPOSITE AND WAS RIGHT ABOUT A WARNING AND WRONG ABOUT A REFUSAL.
        # It said: keyed on BLOCKS, not on the word "FAIL", because an UNDECIDED that omits `failing`
        # condemns files it never doubted. **That reasoning is still true and it is no longer
        # sufficient**, because a REFUSAL has a cost a warning does not: it stops the record being
        # written at all.
        # ⚠⚠ MEASURED ON THE SERVER SIDE, by verdictLedger's `test_v16b_does_not_stop_a_dying_checker
        # _recording_that_it_died`, which went RED against a V19 draft covering both verdicts:
        # **a crashed checker CANNOT name a subset.** Requiring one would stop it recording that it
        # died, and the step then renders MISSING rather than UNDECIDED — absence rendering as
        # NOTHING instead of as UNKNOWN, which is strictly worse and the exact inversion of what this
        # rule is for.
        # ⭐ THE LINE IS CAPABILITY, NOT SAFETY DIRECTION. A wide FAIL and a wide UNDECIDED are both
        # fail-CLOSED. The difference is that a FAIL always COULD have named its subset and withheld
        # it — `check_checkers` had `_bad` in a local variable — and a dead checker could not.
        # UNDECIDED keeps the WARNING below, which costs it nothing and still makes the width visible.
        ap.error(
            "--failing-file is REQUIRED for --verdict %s: absent, this record INDICTS ALL %d "
            "subject(s), and an unnarrowed block over N files condemns the N-1 that passed. "
            "Nothing downstream can tell 'the gate meant all of them' from 'the gate could not "
            "say'. ⚠ MEASURED (LED-10): a FAIL naming one bad file among 24 took ownership of 23 "
            "innocent content keys and condemned a commit that predated the offending file, with "
            "no re-run able to clear it — and the narrow set was sitting in a local variable at "
            "the call site. TWO WAYS TO SATISFY THIS, and they are different claims: give the "
            "SUBSET that actually failed, or pass the full --files list to state that you mean "
            "every one of them. Absence is not the second — it is the second happening silently."
            % (a.verdict, len(subjects)))

    elif a.verdict == "undecided":
        # ⚠ A WARNING, AND IT STAYS ONE. The width is real — absent `failing` indicts every subject
        # here exactly as it does on a FAIL — but the caller may be a checker that could not finish,
        # and refusing it would convert "I could not decide" into no record at all. Printing keeps
        # the width visible at zero cost to the case the exemption exists for. V19 draws the same
        # line server-side; `V16b` continues to govern this verdict.
        print("  WARNING: UNDECIDED recorded with no --failing-file, so this record INDICTS ALL %d "
              "subject(s)." % len(subjects))
        print("           If you were specific enough to name which files defeated you, name them —")
        print("           the exemption here is for a checker that could NOT, not for one that")
        print("           did not bother. An unnarrowed block over N files condemns the N-1 that")
        print("           passed, and nothing downstream can tell 'all of them' from 'could not say'.")

    ev = module_evidence(*a.evidence) if a.evidence else ()
    # ⚠⚠ EVIDENCE IS FENCED THE SAME WAY SUBJECTS ARE, AND IT WAS NOT UNTIL 2026-09-08 (RLYB-1).
    # `ledger_subjects` "fences the paths that are not safe to record (untracked, outside the repo,
    # differing from the index)" — this file says so at the top — but `module_evidence` hashes
    # WORKING-TREE bytes of anything readable, so `--evidence` accepted an untracked file, and an
    # absolute path OUTSIDE THE REPOSITORY, silently at exit 0. Measured: a brief written to the
    # session scratchpad was accepted and emitted as `../../Users/.../brief.md`.
    #
    # ⛔ WHY THAT IS NOT COSMETIC: every review brief rests on the sentence "editing the brief
    # stales the key and the gate re-runs". Staleness is computed by watching a NAMED BLOB MOVE, so
    # pinning to a blob git never tracks defeats it — the key never goes stale and the gate never
    # re-runs. A gate could pin to a file nobody will ever edit and be permanently green.
    #
    # ⚠ THE OLD GUARD BELOW CAUGHT ONLY NON-EXISTENCE (that case does fail closed: no entry, then
    # V21). An untracked file that EXISTS resolves fine, so the count matched and the warning was
    # dead prose — R-ZERONULL: the two states returned the same value and only the message differed.
    #
    # ⚠ THIS MAKES THE CLIENT STRICTER THAN THE SERVER, WHICH IS THE DIRECTION THAT HIDES THINGS —
    # a refusal here never reaches the ledger's call log. Accepted deliberately and NARROWLY: the
    # server's own staleness model requires a watchable blob, so a refusal here names a record the
    # ledger would keep but could never expire. The durable fix is server-side (V21 requiring the
    # blob be TRACKED, not merely present) and is reported to the verdictLedger session; this is the
    # fail-fast half, not a substitute for it.
    #
    # ⚠⚠ FENCE THE RESOLVED PATHS, NEVER `a.evidence`. The first version of this guard tested the
    # raw argv strings and was BYPASSABLE (RLYB-1r): `module_evidence` does `os.path.abspath` against
    # the PROCESS CWD and then relativises against a root derived from `__file__`, while
    # `ledger_subjects` is CWD-independent — TWO RESOLUTIONS OF ONE INPUT, and the guard checked the
    # one that is not recorded. Measured from a shifted CWD with a decoy `.claude/commands/rely.md`
    # in a scratchpad: guard silent, exit 0, and the blob recorded was the decoy's rather than the
    # brief's. `DC-44` — a true value read against the WRONG OBJECT; the check was right and its
    # subject was wrong. ⚠ `R-BRIEF` routes commit-needing agents into `worktree(action='add')`,
    # which is exactly a non-root CWD, so this was reachable and not hypothetical.
    #
    # ⭐ AND FENCING THE RESOLVED PATH IS ALSO WHAT ADMITS THE LEGITIMATE SPELLINGS. The argv version
    # REFUSED an absolute in-repo path, a `./`-prefixed path and a `..`-containing path to the same
    # staged brief, because `ledger_subjects` normalises backslashes and nothing else — a false
    # "not staged" on four correct inputs (RLYB-6). One object, one fence, nine cases measured green.
    if a.evidence:
        _ev_kept, _ev_fenced = common.ledger_subjects([e["path"] for e in ev], a.ref)
        if _ev_fenced:
            ap.error("--evidence must name a TRACKED file at %s, and %d did not:\n%s\n"
                     "Evidence is what makes this verdict go stale when its producer changes — the "
                     "ledger watches that blob move. A path git does not track has no blob to "
                     "watch, so the key would never expire and the gate would never re-run. Pin to "
                     "the BRIEF (a review round) or the CHECKER (a mechanical one), staged."
                     % (a.ref,
                        len(_ev_fenced),
                        "\n".join("    %-52s %s" % (rel, why) for rel, why in _ev_fenced)))
    if a.evidence and len(ev) != len(set(a.evidence)):
        print("  WARNING: %d brief path(s) given, %d resolved — a brief that is absent or "
              "untracked contributes NO evidence, and the ledger will refuse the PASS rather "
              "than accept an unpinned one." % (len(set(a.evidence)), len(ev)))
    # ⚠ ONE KWARGS DICT FEEDS BOTH VERBS. `check` and `emit` must be asked about the SAME record or
    # a dry run certifies a command nobody ran; building the arguments twice is where that drifts.
    kw = dict(step=a.step, tier=a.tier, verdict=a.verdict.upper(), subjects=subjects,
              basis=common.ledger_basis(a.ref), reason=a.reason, evidence=ev,
              outstanding=outstanding, revision=a.revision, failing=failing,
              decided={"how": a.how, "passes": a.passes, "agreed": a.agreed, "who": a.who})

    if a.dry_run:
        verdict = check(**kw)
        # ⚠⚠ `None` IS NOT `(False, [])`. Unreachable is exit 2 and prints nothing about the record's
        # quality, because nothing was learned about it. `check` already printed the outage line.
        if verdict is None:
            return 2
        ok, errors = verdict
        print("  DRY RUN — nothing was appended. %s %4d subject(s) at %s"
              % (a.verdict.upper(), len(subjects), a.ref))
        if ok:
            print("  the ledger WOULD ACCEPT this record.")
            return 0
        # ⚠ EVERY violation, not the first. That is the whole reason `validate` returns a list:
        # one rule per round trip is how a caller gives up and works around the thing.
        print("  the ledger WOULD REFUSE this record (%d violation(s)):" % len(errors))
        for e in errors:
            print("  - %s" % e)
        return 1

    rid = emit(**kw)
    if rid is None:
        return 2
    print("  recorded %-4s %4d subject(s)  %s" % (a.verdict.upper(), len(subjects), rid))
    return 0


if __name__ == "__main__":
    sys.exit(_cli(sys.argv[1:]))
