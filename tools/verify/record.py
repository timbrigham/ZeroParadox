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


# ⚠⚠ gitRobot'S ADDRESS IS A CONSTANT, NOT AN ENVIRONMENT VARIABLE. Subject identity comes from its
# `ledger_subjects`, which VERIFIES a reading against a ref. An address the environment could choose
# would let a loopback stub answer "verified" for bytes nobody read, and the record would then reach
# the REAL ledger carrying them — the forge `hooks.py` closed for `attest` (`/rely` 2026-10-03,
# BLOCKING-1), on the recording path this time. Controls substitute the transport through
# `_GITROBOT_SEAM`, a module attribute only in-process code can set.
GITROBOT_URL = "http://127.0.0.1:8010/mcp"
_GITROBOT_SEAM = None             # controls only: a callable(tool, arguments) -> payload
_NO_PROXY = urllib.request.build_opener(urllib.request.ProxyHandler({}))


def _post(payload, session=None, url=None, opener=None):
    headers = dict(_HEADERS)
    if session:
        headers["Mcp-Session-Id"] = session
    req = urllib.request.Request(url or URL, data=json.dumps(payload).encode("utf-8"),
                                 headers=headers, method="POST")
    with (opener.open if opener else urllib.request.urlopen)(req, timeout=TIMEOUT) as resp:
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
    """One MCP round trip to the LEDGER. Returns the parsed tool payload, or None."""
    return _rpc(URL, tool, arguments)


def gitrobot_call(tool: str, arguments: dict):
    """One MCP round trip to gitRobot, at its constant loopback address and through no proxy.
    Same handshake and the same parsing as `_call`; RAISES on a transport failure."""
    if _GITROBOT_SEAM is not None:
        return _GITROBOT_SEAM(tool, arguments)
    return _rpc(GITROBOT_URL, tool, arguments, opener=_NO_PROXY)


def _rpc(url, tool, arguments, opener=None):
    """One MCP round trip to `url`. Returns the parsed tool payload, or None."""
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
                                  "clientInfo": {"name": "zp-record", "version": "1"}}},
                      url=url, opener=opener)
    _post({"jsonrpc": "2.0", "method": "notifications/initialized"}, session=sid,
          url=url, opener=opener)
    _, body = _post({"jsonrpc": "2.0", "id": call_id, "method": "tools/call",
                     "params": {"name": tool, "arguments": arguments}}, session=sid,
                    url=url, opener=opener)
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


def verify_subjects(observed, ref):
    """`(subjects, skipped)` — gitRobot's `ledger_subjects` answer for a reading. RAISES
    `common.SubjectsUnverified` when there is no answer to give.

    `observed` is `{repo-relative path: the blob id of the bytes that were READ}`; `ref` is a resolved
    tree or commit id. The served tool VERIFIES that reading against `ref` and does not derive one,
    so the predicate — which paths may be subjects — lives there, and this function carries the
    reading over and the answer back. `skipped` is `[(path, why)]` with the server's own reason.

    ⚠ THE SHAPE CHECKS BELOW ARE TRANSPORT, NOT A SECOND PREDICATE. Each asks whether the answer is
    an answer to THIS question: every path sent comes back exactly once, as a subject or a skip, and
    a subject carries the blob that was sent. A reply that drops a path or names other bytes is not a
    verification of this reading, so it raises (`R-ZERONULL`) rather than recording a narrower set.
    """
    import common
    try:
        out = gitrobot_call("ledger_subjects", {"observed": dict(observed), "ref": ref})
    except (urllib.error.URLError, OSError, TimeoutError, ValueError) as exc:
        raise common.SubjectsUnverified(
            "subjects unverified: gitRobot ledger_subjects unreachable at %s (%s)"
            % (GITROBOT_URL, exc))
    if not isinstance(out, dict):
        raise common.SubjectsUnverified(
            "subjects unverified: gitRobot ledger_subjects returned no usable payload")
    if out.get("_transport_is_error") or out.get("ok") is not True:
        raise common.SubjectsUnverified(
            "subjects unverified: gitRobot ledger_subjects refused (%s)"
            % str(out.get("error") or out.get("errors") or out.get("reason") or out)[:400])
    subjects, skipped = out.get("subjects"), out.get("skipped")
    if not isinstance(subjects, list) or not isinstance(skipped, list):
        raise common.SubjectsUnverified(
            "subjects unverified: the answer carries no `subjects`/`skipped` lists")
    kept, fenced, seen = [], [], []
    for s in subjects:
        p = s.get("path") if isinstance(s, dict) else None
        b = s.get("git_blob_id") if isinstance(s, dict) else None
        if p not in observed or b != observed[p]:
            raise common.SubjectsUnverified(
                "subjects unverified: the answer names %r at %r, which is not the reading sent"
                % (p, b))
        kept.append({"path": p, "git_blob_id": b})
        seen.append(p)
    for k in skipped:
        if not isinstance(k, dict) or not isinstance(k.get("path"), str):
            raise common.SubjectsUnverified(
                "subjects unverified: a `skipped` entry is malformed (%r)" % (k,))
        fenced.append((k["path"], str(k.get("why") or "skipped by gitRobot ledger_subjects")))
        seen.append(k["path"])
    if sorted(seen) != sorted(observed):
        raise common.SubjectsUnverified(
            "subjects unverified: %d path(s) sent, %d answered; unanswered: %s"
            % (len(observed), len(seen), ", ".join(sorted(set(observed) - set(seen))[:5])))
    return sorted(kept, key=lambda s: s["path"]), fenced


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
    does NOT equal it. Subjects come from `common.ledger_subjects`, which has gitRobot
    verify the reading and returns the paths it would not certify.
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

    ⚠⚠ THIS SIGNATURE IS FROZEN AND IT CANNOT TELL A REFUSAL FROM AN OUTAGE. Every existing
    caller keeps working unchanged. Call `emit_ex` when you need to CHOOSE AN EXIT CODE — which
    is every caller that gates on the result — because 2 and 4 are not the same event.
    """
    return emit_ex(step, tier, verdict, subjects, basis, reason=reason, inputs=inputs,
                   decided=decided, cost=cost, revision=revision, evidence=evidence,
                   outstanding=outstanding, failing=failing)[0]


def emit_ex(step, tier, verdict, subjects, basis, reason=None,
            inputs=(), decided=None, cost=None, revision=0, evidence=(), outstanding=(),
            failing=()):
    """Append one record. Returns `(record_id, failure)`.

    `failure` is None on success, `"refused"` when the ledger DECIDED and said no, and
    `"unreachable"` when it was never asked. ⛔ THE TWO MAP ONTO EXIT 4 AND EXIT 2 AND MUST NEVER
    BE MERGED: a refusal is a RULE being applied, so the same call will be refused again, and
    retrying it is how a caller under pressure gets past a rule it should have obeyed. An outage
    decided nothing, so retrying it is the correct next move. Recommended caller shape:

        rid, failure = record.emit_ex(...)
        if failure == "refused":
            sys.exit(4)          # asked and REFUSED — terminal
        if failure:
            sys.exit(2)          # could not ask — retryable

    ⚠ WHY THIS EXISTS. `emit` ALREADY KNEW which failure it had — the refusal branch below has
    carried "A refusal is TERMINAL. Do not retry it." all along — and then returned the same
    `None` as a timeout. The information existed and was destroyed at the return, which is why
    `reachable()` (a SECOND network call) had to exist to recover a distinction the first call
    had already made. ⚠ `reachable()` and `check_briefs.classify_record_failure` are NOT retired
    here; retiring them touches callers and is a separate, deliberate step.
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
            return None, "unreachable"
        if out is None:
            print("UNDECIDED: verdictLedger returned no usable payload")
            return None, "unreachable"
        if out.get("ok"):
            return out.get("id"), None
        # A refusal is TERMINAL. Do not retry it.
        errs = out.get("errors") or [out.get("error", "unknown")]
        print("UNDECIDED: record refused by verdictLedger:")
        for e in errs:
            print(f"  - {e}")
        return None, "refused"
    print(f"UNDECIDED: verdictLedger unreachable ({last_error})")
    return None, "unreachable"


# --------------------------------------------------------------------- the review-gate CLI
#
# ⚠⚠ WHY THIS EXISTS AND WHY IT IS SEPARATE FROM `common.record_if_asked`. Every mechanical checker
# emits through `common.emit_verdict`, which takes its own reading and stamps
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
# ⚠ SUBJECTS ARE gitRobot's VERIFIED ANSWER ABOUT A READING. `common.ledger_subjects` sends the
# reading (`--observed-file`, or the working-tree blob ids taken now) to gitRobot's `ledger_subjects`,
# which checks it against the basis and returns every path it will not certify with its reason. A
# blob id is sha1("blob " + bytelength + "\0" + content) — the field that used to be called
# `sha256` made every record read STALE for ever, because the validator accepted a 64-hex digest
# while the comparator resolved a 40-hex object id.

# ⚠⚠ `panel` IS M-OF-N, AND BOTH NUMBERS ARE CONSTANTS BY RULING, NOT BY TASTE. Tim, 2026-10-14:
# all three readers must have RUN (R5a), and the threshold is fixed at 2 of 3 with no flag to choose
# it and no policy key to tune it (R5d). A threshold the caller supplies is a threshold the caller
# can lower; one written here can only be changed by a reviewed edit to this file.
# ⚠ THE SERVER'S FLOOR IS ALSO 2 (`policy.panel.min_threshold`, served default — `policy()` exposes
# no `panel` key, measured 2026-10-13). Equal today; if the server floor ever rises above this, V23
# refuses every panel record, loudly, which is the safe direction for the two to disagree in.
PANEL_PASSES = 3
PANEL_THRESHOLD = 2
# The two values a panel finding's `shift` may take (R5c). The FIELD NAME is shared with
# `.claude/commands/copy-editor.md`, which tells each reader to write it; renaming it here strands
# the brief. ⚠ The ledger stores the key without judging it (V18 reads `severity` only; validated
# 2026-10-14 with `shift: wording` on a PASS, `ok:true`), so THIS FILE is the only reader of it.
PANEL_SHIFTS = ("meaning", "wording")
# The two values a copy_editor finding's `vote` may take: the vote of the READER WHO MADE IT, copied
# as given. It is what lets this file see whether a panel PASS carries its dissent at all. ⚠ The
# ledger stores the key without judging it (validated 2026-10-14 with `vote` on a panel PASS,
# `ok:true`), so, like `shift`, THIS FILE is the only reader of it.
PANEL_VOTES = ("pass", "divergent")
# The one step `panel` belongs to (R5d puts the constant in the copy-editor path). The meaning /
# wording vocabulary is the copy-editor brief's; no other gate's readers are asked to write it.
PANEL_STEP = "copy_editor"


def decided_for(how, passes, agreed, who):
    """The `decided` dict, built in ONE place so `--selftest` can read its bytes.

    ⚠ `threshold` IS WRITTEN ONLY UNDER `panel`. V23 requires it ON a panel record (*"requires
    integer decided.passes, decided.agreed and decided.threshold"*), while every other route's
    record must stay byte-identical to what it was — an `agreement` record growing a key it never
    carried would be a new payload under V11 and conflict with its own earlier copy."""
    d = {"how": how, "passes": passes, "agreed": agreed, "who": who}
    if how == "panel":
        d["threshold"] = PANEL_THRESHOLD
    return d


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
    # ⚠⚠ THE READING IS THE REVIEWER'S, TAKEN WHEN IT READ (`SUBJ-1`, `D1-1`). Subjects are
    # gitRobot's verification of a reading against the basis. Without this file the reading is
    # taken at RECORD time from the working tree, minutes after the review read it, and a file that
    # changed and was staged in between verifies cleanly on bytes nobody examined. `--observe`
    # below produces the file at read time.
    ap.add_argument("--observed-file", default=None,
                    help="JSON object {repo-relative path: git blob id} of the bytes the review "
                         "actually READ, taken when it read them (`record.py --observe <paths>` "
                         "prints one). Every --files path needs an entry. Without it the reading "
                         "is taken now, from the working tree.")
    ap.add_argument("--observe", nargs="+", default=None, metavar="PATH",
                    help="print the JSON reading for these repo-relative paths (the blob id of "
                         "the bytes on disk now) and exit — run it when you READ, save the output, "
                         "and pass it later as --observed-file. Exit 2 if any path has no reading.")
    # ⚠ THE ENUMS ARE THE SERVER'S, MIRRORED HERE ONLY AS FAIL-FAST. The ledger refuses a bad value
    # either way — that is where the rule lives and this file holds no validation logic. Listing them
    # in `choices` turns a round trip into an immediate usage error, which matters for a gate brief
    # run by an agent that would otherwise read a refusal as "the ledger is down".
    ap.add_argument("--tier", required=True, choices=["A", "H"],
                    help="A = an agent gate actually ran; H = a human decided. 'M' is mechanical "
                         "and belongs to common.record_if_asked, not here.")
    ap.add_argument("--how", required=True,
                    choices=["delegated", "agreement", "panel", "signature", "override"],
                    help="delegated = ONE agent round, no consensus claimed (the normal route for "
                         "a gate brief); agreement = 3+ independent passes concurred and the round "
                         "RAN; panel = --step copy_editor only, exactly 3 passes ran and at least 2 "
                         "concurred, the dissent "
                         "CARRIED on the record and never outvoted when it is bedrock or says the "
                         "meaning moved; signature = a PERSON accepted a verdict the round did not "
                         "produce; override = a regrade, the gate erred. 'mechanical' is REFUSED here.")
    # ⚠⚠ THE BRIEF, NOT THE AGENT — AND THIS IS WHY `delegated` NEEDED NO NEW MECHANISM.
    # Attribution is not authentication: `sign` already concedes that, and no key material exists
    # here, so "prove you are that agent" was never on the table. What IS checkable is WHICH
    # INSTRUCTIONS GOVERNED THE ROUND and whether they have since changed. So a delegated PASS
    # carries the brief's blob id, and **editing the brief stales the key and the gate re-runs**.
    # A delegated verdict cannot outlive its instructions. That is V16's machinery pointed at
    # review rather than at checkers.
    ap.add_argument("--evidence", nargs="+", default=None,
                    help="path(s) to the BRIEF this round ran under, e.g. "
                         ".claude/commands/adversary-review.md. REQUIRED for a delegated PASS, "
                         "and for every agreement or panel verdict. "
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
                         "'ordinary' may accompany a PASS. Under --how panel it is REQUIRED on a "
                         "split PASS. On a --step copy_editor PASS under agreement or panel, every "
                         "finding needs `shift` set to 'meaning' or 'wording' ('meaning' is "
                         "refused) and `vote` set to 'pass' or 'divergent'; a panel PASS needs at "
                         "least one 'divergent' finding and an agreement PASS may carry none.")
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
                    help="how many independent passes ran (agreement: 3 or more; panel: exactly 3)")
    # ⚠ DEFAULT `None`, RESOLVED TO 1 BELOW FOR EVERY ROUTE EXCEPT `panel`. A panel's agreed count
    # IS its verdict, so it must be STATED; a default of 1 would let an omitted flag read as "one
    # reader concurred". Every other route still records 1 when the flag is absent, byte for byte.
    ap.add_argument("--agreed", type=int, default=None,
                    help="how many of them concurred (agreement: all of them; panel: REQUIRED, "
                         "at least 2 for a PASS)")
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
                    help="basis ref (default INDEX = the tree the staged content makes, which is "
                         "what a pre-commit review examined; with nothing staged it is the tree "
                         "HEAD carries). HEAD records against the COMMIT id instead of a tree, and "
                         "which basis decides an action is the ledger's answer (verdictLedger "
                         "`inventory` / `find`), so prefer the default for committed content too.")
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
    # ⚠ THREE EXIT CODES, MATCHING THIS MODULE'S DOCTRINE: 0 `validate` answered ok · 1 it returned
    # errors, every one printed · 2 a service could not be asked. Reading 2 as 1 turns an
    # outage into "your record is bad", which sends a gate off editing a record that was fine.
    # ⚠ DECLARED so it appears in `--help` and in `_actions` like any other flag, and handled
    # below before `parse_args`, which would otherwise demand a full record to answer it.
    ap.add_argument("--list-flags", action="store_true",
                    help="print one option string per line and exit — the PARSER's own list, for "
                         "a checker that needs to know what this program accepts without reading "
                         "its help prose.")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the basis and each verified subject's blob id, then verdictLedger "
                         "`validate`'s answer verbatim, WITHOUT appending. Use this to check a "
                         "command — never the live stream. Exit 0 = validate ok, 1 = validate "
                         "returned errors, 2 = a service could not be asked.")
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
    # ⚠ HANDLED BEFORE `parse_args` for the same reason: taking a reading must not require a record.
    if "--observe" in argv:
        op = argparse.ArgumentParser(prog="record.py --observe")
        op.add_argument("--observe", nargs="+", required=True, metavar="PATH")
        o = op.parse_args(argv)
        try:
            seen, unread = common.observe_blobs(o.observe)
        except common.SubjectsUnverified as e:
            print("UNDECIDED: no reading taken: %s" % e, file=sys.stderr)
            return 2
        print(json.dumps(seen, indent=1, sort_keys=True))
        for rel in unread:
            print("  NO READING: %s — not a readable repo-relative file under %s"
                  % (rel, common.REPO), file=sys.stderr)
        return 2 if unread else 0
    a = ap.parse_args(argv)
    # ⚠ `panel` IS THE COPY-EDITOR PANEL AND NOTHING ELSE (R5d). Its threshold, its passes and its
    # `shift` vocabulary were ruled for that gate's three readers; on another step the record would
    # claim a 2-of-3 vote no brief ever ran.
    if a.how == "panel" and a.step != PANEL_STEP:
        ap.error("--how panel is the copy-editor panel's route only (--step %s, R5d); got --step "
                 "%s. Another gate's single round is --how delegated, and three unanimous passes "
                 "are --how agreement." % (PANEL_STEP, a.step))
    # ⛔⛔ A COPY_EDITOR PASS MUST NOT BE RECORDABLE WITHOUT ITS DISSENT, AND THE GUARD IS ON THE
    # PROPERTY, SO EVERY `--how` IS ACCOUNTED FOR HERE:
    #   delegated  — one round, no headcount, no outstanding required: a 2-1 split with a MEANING
    #                dissent lands as a clean PASS. REFUSED below, on every verdict: the brief never
    #                records this way, and a delegated record at the panel's basis would also take
    #                revision 0 and leave the carrier's real record refused by V11.
    #   agreement  — PASS needs 3 of 3 (V3 mirror, below), and any finding it carries needs `shift`
    #                and `vote`, may not be 'meaning', and may not carry a 'divergent' vote
    #                (outstanding loop, below). A carrier who writes `--agreed 3` over a split and
    #                tags every finding 'pass' cannot be detected by any client; that is the residual.
    #   panel      — PASS needs 2 of 3, never 3, and an outstanding file whose every finding is
    #                tagged and ordinary wording, at least one with vote 'divergent'. Completeness
    #                and faithful copying of the tags are not checkable.
    #   signature, override — Tim's routes: a PERSON accepts or regrades. Left open by design.
    #   mechanical — not in `choices`; refused by argparse.
    if a.step == PANEL_STEP and a.how == "delegated":
        ap.error("--step %s refuses --how delegated: a single round records no headcount and no "
                 "dissent, so a 2-1 split would land as a clean verdict. The carrier records ONE "
                 "record for the three readers: --how agreement (3 of 3), --how panel (2 of 3, every "
                 "reader's findings on --outstanding-file), or --verdict undecided. See "
                 ".claude/commands/copy-editor.md." % PANEL_STEP)
    if a.agreed is None:
        if a.how == "panel":
            ap.error("--agreed is required with --how panel: how many of the %d readers concurred "
                     "IS the verdict, so it is stated, never defaulted. An omitted count would "
                     "record one concurring reader the round never reported." % PANEL_PASSES)
        a.agreed = 1

    # ⚠ EVERY INPUT FILE IS READ AS `utf-8-sig`, AND AN UNREADABLE ONE IS A USAGE ERROR (exit 2),
    # NEVER A TRACEBACK (`RECORD-PY-BOM-CRASH-1`). PowerShell 5.1 `Set-Content -Encoding utf8` writes
    # a BOM, and plain `utf-8` hands `json.loads` a leading U+FEFF it refuses — a traceback and exit
    # 1, which this layer reserves for a FINDING. One reader for every input flag, so no flag is the
    # one that was missed.
    def _read_input(flag, path, as_json):
        try:
            text = io.open(path, encoding="utf-8-sig").read()
            return json.loads(text) if as_json else text
        except (IOError, OSError, ValueError) as exc:
            ap.error("%s %r could not be read%s: %s"
                     % (flag, path, " as JSON" if as_json else "", exc))

    if a.reason_file:
        if a.reason:
            ap.error("pass --reason or --reason-file, not both")
        a.reason = _read_input("--reason-file", a.reason_file, False).strip()
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
    elif a.how == "panel":
        # ⚠⚠ THE `panel` CONTRACT (Tim's R5, 2026-10-03; follow-ups R5a-d, 2026-10-14). A 2-of-3
        # copy-editor split used to be recordable only as UNDECIDED, routed to his signature, and
        # wave 4 measured the price: two of his decisions re-asked and ~10 of 13 extra gate rounds
        # downstream of a split (`CARRYW4-X-1`). `panel` lets a split whose dissent is WORDING
        # admit, while a dissent that is bedrock or says the meaning moved still blocks.
        #
        # ⚠ EVERY REQUIREMENT HERE IS ON EVERY panel VERDICT, NOT ONLY THE PASS. V23 refuses a panel
        # record with no `who` and V21 one with no blob, PASS and UNDECIDED alike (measured
        # 2026-10-13); refusing locally names the remedy instead of spending a round trip on it.
        if not a.who:
            ap.error("--who is required with --how panel: name the GATE whose readers sat on the "
                     "panel (e.g. --who copy_editor). V23 refuses a panel record without it.")
        if a.tier != "A":
            ap.error("--how panel requires --tier A: it records that three AGENT readers actually "
                     "ran. 'H' claims a human decided, which is --how signature.")
        if not a.evidence:
            ap.error("--evidence is required for --how panel: give the path to the BRIEF the "
                     "readers ran under. Three readers following one brief have ONE producer, as "
                     "under --how agreement, and V21 refuses any verdict that names no blob.")
        # ⚠ R5a — ALL THREE READERS RAN. Not "at least 3": a panel of four with a 2-vote threshold
        # is a minority verdict, and the ruling fixed both numbers together.
        if a.passes != PANEL_PASSES:
            ap.error("--how panel requires --passes %d (R5a: all three readers must have run); got "
                     "passes=%d. A panel with a reader missing is not a 2-of-3 split — it is a "
                     "round that did not finish. Run the missing reader, or record --verdict "
                     "undecided under a route that does not claim a panel."
                     % (PANEL_PASSES, a.passes))
        if not 0 <= a.agreed <= a.passes:
            ap.error("--agreed must lie between 0 and --passes (%d); got %d. More readers cannot "
                     "concur than ran." % (a.passes, a.agreed))
    elif a.evidence:
        ap.error("--evidence belongs to --how delegated, agreement or panel — all are produced by "
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

    # ⚠⚠ THE panel PASS, AND THE V3 MIRROR ABOVE IS DELIBERATELY UNTOUCHED BY IT. `agreement` stays
    # unanimous; `panel` is a SEPARATE route with its own threshold, never a relaxed `agreement`.
    if a.verdict == "pass" and a.how == "panel":
        if a.agreed < PANEL_THRESHOLD:
            ap.error("a PASS under --how panel needs --agreed >= %d of %d (R5d, a constant in this "
                     "file, no flag and no policy key); got agreed=%d. A split below threshold is "
                     "recorded honestly as --verdict undecided, and goes to Tim."
                     % (PANEL_THRESHOLD, PANEL_PASSES, a.agreed))
        # ⚠ R-ZERONULL: A SPLIT MUST NOT RECORD THE VALUE A UNANIMOUS ROUND RECORDS. Unanimity has a
        # route already, the stronger one. Two spellings of one fact means a reader of the ledger
        # can no longer tell "all three concurred" from "two did and the third was carried".
        if a.agreed == a.passes:
            ap.error("all %d readers concurred, so this is --how agreement, not --how panel. "
                     "`panel` records a SPLIT; a unanimous round recorded under it would make a "
                     "split and a unanimous verdict indistinguishable in the ledger." % a.passes)
        # ⚠⚠ WHAT IS ENFORCED, AND WHAT CANNOT BE. Enforced here: a split PASS needs a non-empty
        # outstanding file; every finding on it has its `severity`, `shift` and `vote` checked; and
        # at least one finding must carry `vote: 'divergent'` (outstanding loop, below), so a file
        # holding only the PASS voters' findings is refused. NOT enforceable by any client: that the
        # list holds EVERY finding the dissenting reader wrote, and that each tag, `vote` included,
        # is the one the reader gave. This file never sees the readers' raw output, only what the
        # carrier copied, so a carrier who leaves out the one MEANING finding, relabels it
        # 'wording', or marks a PASS voter's finding 'divergent', is accepted. That half
        # rests on the brief's copy-verbatim instruction and on the raw outputs in the carrier's
        # report, which a human can audit against the record.
        # ⚠ THIS MAKES THE CLIENT STRICTER THAN THE SERVER, the direction that hides a refusal from
        # the ledger's call log; accepted for the same reason as the evidence fence below — the
        # ledger reads only what rides on the record, so it has no half that could see an absent one.
        if not a.outstanding_file:
            ap.error("a split PASS under --how panel (%d of %d) needs --outstanding-file carrying "
                     "every reader's findings, the dissenting reader's among them. The ledger can "
                     "refuse a bedrock dissent only if it rides on the record, so a dropped dissent "
                     "is an outvoted one that nothing could see. Carry each finding with its "
                     "reader's own severity, `shift` ('meaning' or 'wording') and `vote` ('pass' or "
                     "'divergent')." % (a.agreed, a.passes))

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

    observed = None
    if a.observed_file:
        observed = _read_input("--observed-file", a.observed_file, True)
        if not isinstance(observed, dict) or not all(
                isinstance(k, str) and isinstance(v, str) for k, v in observed.items()):
            ap.error("--observed-file must hold a JSON object {repo-relative path: blob id} — "
                     "the output of `record.py --observe <paths>` taken when the review read them")
    else:
        # ⚠ STATED ON EVERY RUN THAT TAKES THE READING NOW, so a record made this way is never
        # mistaken for one carrying the review's own reading.
        print("  reading: taken NOW from the working tree under %s — not the review's own. A file "
              "changed and staged since it was read would verify on bytes nobody examined; pass "
              "--observed-file (from `record.py --observe` at read time) to close that." % common.REPO)
    try:
        subjects, skipped = common.ledger_subjects(sorted(set(a.files)), a.ref, observed=observed)
    except common.BasisUnresolved as e:
        print("UNDECIDED: %s was NOT SENT: %s" % (a.step, e))
        return 2
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
        # ⚠ A USAGE ERROR, NOT A TRACEBACK: exit 1 is this layer's "finding" code, and a missing or
        # unparseable file is a mistake in the command, which argparse reports as exit 2.
        outstanding = _read_input("--outstanding-file", a.outstanding_file, True)
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
            # ⚠⚠ R5c — A "THE MEANING MOVED" DISSENT ALWAYS BLOCKS, WHATEVER ITS SEVERITY TAG. A panel
            # outvotes only wording and expression. The severity is the DISSENTING READER'S own grade
            # (R5b) and this file never rewrites it; it reads `shift` beside it instead, so a reader
            # who tags a meaning change 'ordinary' still cannot be outvoted on it. ⚠ The check above
            # already refuses a bedrock dissent on any PASS; this is the half V18 cannot see,
            # because the server reads `severity` and nothing else.
            # ⚠ ON BOTH AGENT ROUTES OF THE STEP, NOT ONLY `panel`: under the union rule a finding is
            # not owned by the vote it came with, so a MEANING finding from a reader who voted PASS
            # blocks a 3/3 `agreement` PASS too. `shift` and `vote` are REQUIRED on a PASS, or
            # omitting a key would walk a finding past the refusal it feeds. ⚠ ON A PASS ONLY: a
            # FAIL or UNDECIDED blocks whatever its findings say, and a client guard must never be
            # the thing that stops a real blocking verdict from landing. `signature` and `override`
            # are Tim's, and a person accepting a split may carry what he accepted.
            if a.step == PANEL_STEP and a.how in ("agreement", "panel") and a.verdict == "pass":
                if f.get("shift") not in PANEL_SHIFTS:
                    ap.error("every finding on a --step %s PASS under --how %s needs `shift` set "
                             "to one of %s; got %r. It is what decides whether a finding may ride "
                             "on a PASS at all (R5c), so an unmarked finding cannot be weighed — "
                             "ask the reader which it was, never guess."
                             % (PANEL_STEP, a.how, ", ".join(PANEL_SHIFTS), f.get("shift")))
                if f.get("vote") not in PANEL_VOTES:
                    ap.error("every finding on a --step %s PASS under --how %s needs `vote` set to "
                             "one of %s, the vote of the reader who made it, copied as given; got "
                             "%r. Without it nothing can show whether the dissent was carried."
                             % (PANEL_STEP, a.how, ", ".join(PANEL_VOTES), f.get("vote")))
                if f.get("shift") == "meaning":
                    ap.error("a %s PASS (--how %s) cannot carry a finding whose `shift` is "
                             "'meaning' (R5c): a \"the meaning moved\" finding from ANY reader "
                             "ALWAYS blocks, whatever its severity tag (here %r) and whatever its "
                             "reader voted. Record --verdict undecided; it goes to Tim."
                             % (PANEL_STEP, a.how, f.get("severity")))
        # ⚠⚠ THE DISSENT, READ OFF THE `vote` TAGS (every finding has one by now, checked above).
        # A panel PASS is a split, so its dissenting reader's findings must be on it; a file holding
        # only PASS voters' findings is a dropped dissent. An agreement PASS is unanimous, so a
        # 'divergent' finding on it contradicts its own headcount. Both read only the tags the
        # carrier copied; whether they were copied faithfully is not checkable here.
        if a.step == PANEL_STEP and a.verdict == "pass":
            votes = [f.get("vote") for f in outstanding]
            if a.how == "panel" and "divergent" not in votes:
                ap.error("a %s panel PASS must carry at least one finding with `vote` 'divergent': "
                         "the lone DIVERGENT reader's own findings. None is marked so, which means "
                         "the dissent was not carried, or it reported no findings (then the round "
                         "is UNDECIDED, never a panel PASS)." % PANEL_STEP)
            if a.how == "agreement" and "divergent" in votes:
                ap.error("a %s agreement PASS records three PASS votes, so it cannot carry a finding "
                         "with `vote` 'divergent'. A DIVERGENT reader means a split: --how panel "
                         "if its findings are all WORDING and ORDINARY, otherwise --verdict "
                         "undecided." % PANEL_STEP)
    # ⚠⚠ VALIDATED AGAINST THE POST-FENCE `subjects`, NEVER AGAINST `--files`. `ledger_subjects`
    # DROPS paths absent from the ref or differing from the index, so `--files` is what the caller
    # asked for and `subjects` is what is actually being recorded. Indicting a path that was fenced
    # out would name something the record does not cover — coverage and indictment would disagree
    # inside one record, which is worse than either being wrong alone.
    failing = ()
    if a.failing_file:
        failing = _read_input("--failing-file", a.failing_file, True)
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
        # ⚠ A FILE THAT EXISTS IN THE CHECKOUT CLAIMS CONTENT, wherever it sits (`RLY54-1`). Root
        # paths carry no slash, so a root `.pdf`, `.html` or `LICENSE` used to fall to the label
        # side and be warned "does not name content" while naming exactly that.
        claims_content = [p for p in stray if "/" in p or p.endswith(PATHISH)
                          or os.path.isfile(os.path.join(str(common.REPO), p))]
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

    # ⚠ A RELATIVE `--evidence` IS REPO-RELATIVE, like `--files` (`CARRYW2-24`). It resolved against
    # the PROCESS CWD, so a gate recording from a worktree with the brief's relative path was
    # refused, or — from a CWD holding a same-named decoy — pinned the decoy (`RLYB-1r`). One
    # resolution for every path this CLI takes: the checkout this `record.py` belongs to.
    ev_paths = [e if os.path.isabs(e) else os.path.join(str(common.REPO), e)
                for e in (a.evidence or ())]
    ev = module_evidence(*ev_paths) if ev_paths else ()
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
    # ⚠ The reading sent is the evidence blob ITSELF, so what gitRobot verifies is exactly the blob
    # this record will carry, not a second hash of the file.
    if a.evidence:
        try:
            _ev_kept, _ev_fenced = common.ledger_subjects(
                [e["path"] for e in ev], a.ref,
                observed={e["path"]: e["git_blob_id"] for e in ev})
        except common.BasisUnresolved as e:
            print("UNDECIDED: %s was NOT SENT: --evidence could not be verified: %s" % (a.step, e))
            return 2
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
    try:
        basis = common.ledger_basis(a.ref)
    except common.BasisUnresolved as e:
        print("UNDECIDED: %s was NOT SENT: %s" % (a.step, e))
        return 2
    kw = dict(step=a.step, tier=a.tier, verdict=a.verdict.upper(), subjects=subjects,
              basis=basis, reason=a.reason, evidence=ev,
              outstanding=outstanding, revision=a.revision, failing=failing,
              decided=decided_for(a.how, a.passes, a.agreed, a.who))

    if a.dry_run:
        # ⚠ PRINTED BEFORE THE LEDGER IS ASKED, so the bytes are readable even when it cannot be.
        # `decided` is the one field whose SHAPE differs by route (`threshold` under panel only),
        # and a dry run that hid it would certify a record nobody could inspect.
        print("  decided  %s" % json.dumps(kw["decided"]))
        verdict = check(**kw)
        # ⚠⚠ `None` IS NOT `(False, [])`. Unreachable is exit 2 and prints nothing about the record's
        # quality, because nothing was learned about it. `check` already printed the outage line.
        if verdict is None:
            return 2
        ok, errors = verdict
        # ⚠⚠ THE OBJECT FIRST, THEN THE SERVER'S ANSWER VERBATIM, AND NOTHING ELSE (`RECDRY-1`). This
        # printed "the ledger WOULD ACCEPT this record" — a sentence no service said, about bytes the
        # output never named, so an exit 0 read as "this is the right record" when `validate` judges
        # only the record's form. Subjects are gitRobot's verified answer and `validate` is the
        # ledger's; each is printed as given, with the blob ids, so a reader can see WHICH bytes.
        print("  DRY RUN — nothing was appended. %s at basis %s %s (from --ref %s), repo %s"
              % (a.verdict.upper(), basis.get("kind"), basis.get("value"), a.ref, common.REPO))
        for s in subjects:
            print("  subject  %s  %s" % (s["git_blob_id"], s["path"]))
        # ⚠ EVERY violation, not the first. That is the whole reason `validate` returns a list:
        # one rule per round trip is how a caller gives up and works around the thing.
        print("  verdictLedger validate -> %s" % json.dumps({"ok": ok, "errors": errors},
                                                            ensure_ascii=False))
        return 0 if ok else 1

    rid = emit(**kw)
    if rid is None:
        return 2
    print("  recorded %-4s %4d subject(s)  %s" % (a.verdict.upper(), len(subjects), rid))
    return 0


def selftest():
    """Controls for the review-gate CLI's input and dry-run paths. Returns 1 on any failure.

    Every gitRobot answer comes through `_GITROBOT_SEAM` and every `validate` through a stand-in
    for `check`, so nothing here reaches a service or appends. Run on the `record` MODULE (not
    `__main__`), because that is the object `common` imports and whose seam it reads."""
    import contextlib
    import io as _io
    import shutil
    import tempfile
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import common
    import record as R
    tmp = tempfile.mkdtemp(prefix="zp-record-selftest-")
    P = "README.md"
    seen_obs, seen_kw = [], []

    def echo(tool, args):
        seen_obs.append(dict(args["observed"]))
        return {"ok": True, "skipped": [],
                "subjects": [{"path": p, "git_blob_id": b} for p, b in args["observed"].items()]}

    def stub_check(**kw):
        seen_kw.append(kw)
        return True, []

    def write(name, data):
        p = os.path.join(tmp, name)
        with open(p, "wb") as fh:
            fh.write(data)
        return p

    base = ["--step", "editorial", "--tier", "A", "--how", "delegated", "--who", "editorial",
            "--run", "gate-selftest", "--evidence", ".claude/commands/editorial-review.md",
            "--dry-run", "--files", P]

    def run(argv):
        """`(exit code, stdout+stderr text)`; a usage error is its SystemExit code, never a crash."""
        del seen_obs[:], seen_kw[:]
        buf = _io.StringIO()
        saved = R._GITROBOT_SEAM, R.check
        R._GITROBOT_SEAM, R.check = echo, stub_check
        try:
            with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
                try:
                    rc = R._cli(argv)
                except SystemExit as e:
                    rc = e.code
        except Exception as e:                            # noqa: BLE001 — a crash is red
            rc = "CRASH %s: %s" % (type(e).__name__, e)
        finally:
            R._GITROBOT_SEAM, R.check = saved
        return rc, buf.getvalue()

    rows = []
    try:
        bom_fail = write("failing.json", b"\xef\xbb\xbf" + json.dumps([P]).encode())
        rc, out = run(["--verdict", "fail", "--failing-file", bom_fail] + base)
        rows.append(("a BOM --failing-file is read, not a traceback",
                     rc == 0 and seen_kw and seen_kw[0].get("failing") == [P]))
        bad_json = write("bad.json", b"\xef\xbb\xbf[not json")
        rc, out = run(["--verdict", "fail", "--failing-file", bad_json] + base)
        rows.append(("an unparseable --failing-file is exit 2 (usage)",
                     rc == 2 and "could not be read as JSON" in out))
        bom_reason = write("reason.txt", "﻿the reason".encode("utf-8"))
        rc, out = run(["--verdict", "fail", "--failing-file", bom_fail,
                       "--reason-file", bom_reason] + base)
        rows.append(("a BOM --reason-file loses its BOM",
                     rc == 0 and seen_kw and seen_kw[0].get("reason") == "the reason"))
        rc, out = run(["--verdict", "pass"] + base)
        rows.append(("the dry run prints validate's answer verbatim",
                     rc == 0 and 'validate -> {"ok": true, "errors": []}' in out
                     and "WOULD ACCEPT" not in out))
        rows.append(("the dry run names each subject's blob",
                     bool(seen_obs) and ("subject  %s  %s" % (seen_obs[0].get(P), P)) in out))
        rows.append(("without --observed-file the reading is stated",
                     "reading: taken NOW" in out))
        obs = write("observed.json", json.dumps({P: "a" * 40}).encode())
        rc, out = run(["--verdict", "pass", "--observed-file", obs] + base)
        rows.append(("--observed-file is the reading sent",
                     rc == 0 and seen_obs and seen_obs[0] == {P: "a" * 40}
                     and "reading: taken NOW" not in out))
        cwd = os.getcwd()
        os.chdir(tmp)
        try:
            rc, out = run(["--verdict", "pass"] + base)
        finally:
            os.chdir(cwd)
        rows.append(("relative --evidence resolves against the repo",
                     rc == 0 and seen_kw and [e["path"] for e in seen_kw[0]["evidence"]]
                     == [".claude/commands/editorial-review.md"]))
        # A real ROOT file whose name has no slash and no `PATHISH` extension — the shape `RLY54-1`
        # measured slipping through. Absent all three, the row fails rather than passing vacuously.
        root = next((n for n in ("lean-toolchain", "LICENSE", "CNAME")
                     if os.path.isfile(os.path.join(str(common.REPO), n))), "no-root-file-found")
        stray = write("stray.json", json.dumps([P, root]).encode())
        rc, out = run(["--verdict", "fail", "--failing-file", stray] + base)
        rows.append(("a root file not among subjects is refused (RLY54-1)",
                     rc == 2 and "NOT among the recorded subjects" in out))
        label = write("label.json", json.dumps([P, "(roster)"]).encode())
        rc, out = run(["--verdict", "fail", "--failing-file", label] + base)
        rows.append(("a non-content label is still permitted", rc == 0 and "INERT" in out))
        rc, out = run(["--observe", P, "nope/missing.md"])
        rows.append(("--observe prints the reading, exit 2 on an unreadable path",
                     rc == 2 and ('"%s"' % P) in out and "NO READING: nope/missing.md" in out))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    bad = 0
    print("RECORD CLI (inputs, reading, dry run)")
    for label_, ok in rows:
        print("  %-56s %s" % (label_, "ok" if ok else "*** FAILED ***"))
        bad += 0 if ok else 1
    print("\nselftest: %s" % ("PASS" if not bad else "FAIL (%d)" % bad))
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(selftest())
    sys.exit(_cli(sys.argv[1:]))
