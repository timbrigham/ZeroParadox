"""Merge N review batches into ONE set of `record.py` input files. It never records anything.

WHY. The verdict ledger refuses a second record at the same (step, basis, revision) (rule V11),
and a higher revision SUPERSEDES the lower one rather than adding to it. So when one gate ran as
several parallel batches, the single record that reaches the ledger must carry the UNION of their
subjects. Doing that by hand loses subjects or keeps stale indictments; this does it mechanically.

Each batch folder holds exactly these four inputs (all REQUIRED; a missing one is an error naming
the batch and the file, never an empty default - `R-ZERONULL`):

  observed.json     {repo-relative path: blob id}   - the reading the batch reviewed
  failing.json      [path, ...]                     - paths it indicts (may be `[]`)
  outstanding.json  [{"note": ..., "severity": ..., "path"?: ..., "id"?: ...}, ...] (may be `[]`)
  reason.txt        free text (may be empty; the merged reason then says so)

Merge rules, batches taken in the order given (LATER WINS):
  observed     per path, the last batch to read it owns it.
  failing      a path stays indicted only where its OWNING batch fails it; an indictment by an
               earlier batch whose path a later batch re-read is dropped and listed.
  outstanding  every finding carried, id prefixed `<batch>:`, its own severity untouched.
  reason       optional --reason-prefix line, then one `[<batch>] <reason>` line per batch.

Output folder must be absent or empty. `failing.json` / `outstanding.json` are written only when
non-empty, because `record.py` refuses an empty list for either flag; when one is not written the
run says so, and the empty folder requirement means a stale copy cannot stand in for it.
`files.txt` lists the merged subjects, one per line.

Usage:
  python tools/verify/union_inputs.py merge --out <dir> [--reason-prefix TEXT] <batch> [<batch> ...]
  python tools/verify/union_inputs.py selftest
"""
import argparse
import io
import json
import os
import shutil
import sys
import tempfile

INPUTS = ("observed.json", "failing.json", "outstanding.json", "reason.txt")


class UnionError(Exception):
    pass


def _read_text(path):
    raw = open(path, "rb").read()
    if raw.startswith(b"\xef\xbb\xbf"):
        raw = raw[3:]
    return raw.decode("utf-8")


def _write_text(path, text):
    with io.open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(text)


def _load_batch(folder):
    label = os.path.basename(os.path.normpath(folder))
    if not os.path.isdir(folder):
        raise UnionError("batch %s: folder not found: %s" % (label, folder))
    missing = [f for f in INPUTS if not os.path.isfile(os.path.join(folder, f))]
    if missing:
        raise UnionError("batch %s: missing %s (all four of %s are required)"
                         % (label, ", ".join(missing), ", ".join(INPUTS)))
    data = {}
    for f in INPUTS[:3]:
        try:
            data[f] = json.loads(_read_text(os.path.join(folder, f)))
        except (ValueError, UnicodeDecodeError) as e:
            raise UnionError("batch %s: %s is not valid UTF-8 JSON: %s" % (label, f, e))
    obs, fail, outs = data["observed.json"], data["failing.json"], data["outstanding.json"]
    if not isinstance(obs, dict) or not obs or not all(
            isinstance(k, str) and isinstance(v, str) for k, v in obs.items()):
        raise UnionError("batch %s: observed.json must be a NON-EMPTY object {path: blob id}" % label)
    if not isinstance(fail, list) or not all(isinstance(p, str) for p in fail):
        raise UnionError("batch %s: failing.json must be a list of paths" % label)
    stray = [p for p in fail if p not in obs]
    if stray:
        raise UnionError("batch %s: failing.json names path(s) the batch did not observe: %s"
                         % (label, ", ".join(stray)))
    if not isinstance(outs, list):
        raise UnionError("batch %s: outstanding.json must be a list of findings" % label)
    for i, item in enumerate(outs):
        if not isinstance(item, dict) or not item.get("note") or not item.get("severity"):
            raise UnionError("batch %s: outstanding.json finding #%d needs both `note` and "
                             "`severity` (severity is never defaulted)" % (label, i + 1))
    reason = " ".join(_read_text(os.path.join(folder, "reason.txt")).split())
    return label, obs, fail, outs, reason


def merge(batches, out, reason_prefix=None):
    """Write the merged inputs into `out`; return a list of report lines. Raises UnionError."""
    if not batches:
        raise UnionError("no batch folders given")
    if os.path.exists(out) and (not os.path.isdir(out) or os.listdir(out)):
        raise UnionError("output folder must be absent or empty: %s" % out)
    loaded = [_load_batch(b) for b in batches]
    labels = [b[0] for b in loaded]
    dup = sorted({x for x in labels if labels.count(x) > 1})
    if dup:
        raise UnionError("batch folder names must be distinct (they prefix ids): %s" % ", ".join(dup))

    observed, owner = {}, {}
    for label, obs, _f, _o, _r in loaded:
        for path, blob in obs.items():
            observed[path] = blob
            owner[path] = label
    failing, dropped, outstanding, superseded, reasons = [], [], [], 0, []
    if reason_prefix and reason_prefix.strip():
        reasons.append(" ".join(reason_prefix.split()))
    for label, _obs, fail, outs, reason in loaded:
        for p in fail:
            if owner[p] == label:
                if p not in failing:
                    failing.append(p)
            else:
                dropped.append((label, p, owner[p]))
        for i, item in enumerate(outs):
            item = dict(item)
            item["id"] = "%s:%s" % (label, item.get("id", i + 1))
            if item.get("path") and owner.get(item["path"], label) != label:
                superseded += 1
            outstanding.append(item)
        reasons.append("[%s] %s" % (label, reason if reason else "(reason.txt empty)"))

    os.makedirs(out, exist_ok=True)
    _write_text(os.path.join(out, "observed.json"),
                json.dumps(observed, indent=1, ensure_ascii=False) + "\n")
    _write_text(os.path.join(out, "files.txt"), "\n".join(sorted(observed)) + "\n")
    _write_text(os.path.join(out, "reason.txt"), "\n".join(reasons) + "\n")
    rep = ["batches (later wins): %s" % ", ".join(labels),
           "subjects: %d" % len(observed)]
    if failing:
        _write_text(os.path.join(out, "failing.json"),
                    json.dumps(failing, indent=1, ensure_ascii=False) + "\n")
        rep.append("failing: %d path(s) -> failing.json" % len(failing))
    else:
        rep.append("failing: NONE - failing.json NOT written; omit --failing-file")
    for label, p, own in dropped:
        rep.append("  dropped indictment: [%s] %s (re-read by later batch %s)" % (label, p, own))
    if outstanding:
        _write_text(os.path.join(out, "outstanding.json"),
                    json.dumps(outstanding, indent=1, ensure_ascii=False) + "\n")
        sev = {}
        for item in outstanding:
            sev[item["severity"]] = sev.get(item["severity"], 0) + 1
        rep.append("outstanding: %d finding(s) -> outstanding.json (%s)"
                   % (len(outstanding), ", ".join("%s %d" % kv for kv in sorted(sev.items()))))
        if superseded:
            rep.append("  WARNING: %d finding(s) name a path a LATER batch re-read; carried anyway"
                       % superseded)
    else:
        rep.append("outstanding: NONE - outstanding.json NOT written; omit --outstanding-file")
    return rep


# ----------------------------------------------------------------------------- controls
def selftest():
    root = tempfile.mkdtemp(prefix="union_inputs_selftest_")
    results = []

    def batch(name, obs, fail, outs, reason, bom=None, skip=None):
        d = os.path.join(root, name)
        os.makedirs(d)
        payload = {"observed.json": json.dumps(obs), "failing.json": json.dumps(fail),
                   "outstanding.json": json.dumps(outs), "reason.txt": reason}
        for f, text in payload.items():
            if f == skip:
                continue
            raw = text.encode("utf-8")
            open(os.path.join(d, f), "wb").write((b"\xef\xbb\xbf" + raw) if f == bom else raw)
        return d

    def out(name):
        return os.path.join(root, "out_" + name)

    def read_json(path):
        return json.loads(_read_text(path))

    def check(label, ok):
        results.append((label, bool(ok)))

    def refuses(label, fn, needle):
        try:
            fn()
            check(label, False)
        except UnionError as e:
            check(label, all(n in str(e) for n in needle))

    try:
        # MUST REFUSE: a missing input file, named with its batch
        m = batch("bm", {"a.lean": "1"}, [], [], "r", skip="failing.json")
        refuses("MUST REFUSE: a missing input file names batch and file",
                lambda: merge([m], out("m")), ["bm", "failing.json"])
        # MUST REFUSE: an outstanding finding with no severity (never defaulted)
        s = batch("bs", {"a.lean": "1"}, [], [{"note": "x"}], "r")
        refuses("MUST REFUSE: a finding with no severity", lambda: merge([s], out("s")),
                ["bs", "severity"])
        # MUST REFUSE: a non-empty output folder
        os.makedirs(out("busy"))
        open(os.path.join(out("busy"), "stale.json"), "w").write("[]")
        ok1 = batch("ok1", {"a.lean": "1"}, [], [], "r")
        refuses("MUST REFUSE: a non-empty output folder", lambda: merge([ok1], out("busy")),
                ["absent or empty"])
        # MUST PARSE: a BOM'd JSON file and a BOM'd reason
        bj = batch("bj", {"a.lean": "1"}, [], [], "r", bom="observed.json")
        br = batch("br", {"b.lean": "2"}, [], [], "plain reason", bom="reason.txt")
        merge([bj, br], out("bom"))
        check("MUST PARSE: BOM'd observed.json and reason.txt",
              read_json(os.path.join(out("bom"), "observed.json")) == {"a.lean": "1", "b.lean": "2"}
              and _read_text(os.path.join(out("bom"), "reason.txt")).startswith("[bj] r\n[br] plain"))
        # Later batch overrides; failing owned by a later PASSING batch is dropped; failing owned
        # by the failing batch is kept; outstanding prefixed with its own severity; prefix first.
        e1 = batch("e1", {"a.lean": "old", "b.lean": "b1"}, ["a.lean", "b.lean"],
                   [{"id": "F1", "severity": "bedrock", "note": "n"}], "first")
        e2 = batch("e2", {"a.lean": "new"}, [], [{"severity": "ordinary", "note": "m"}], "second")
        rep = merge([e1, e2], out("e"), reason_prefix="  prefix  line ")
        o = out("e")
        obs = read_json(os.path.join(o, "observed.json"))
        check("MUST OVERRIDE: the later batch's reading wins", obs["a.lean"] == "new")
        fail = read_json(os.path.join(o, "failing.json"))
        check("MUST DROP: a failing path re-read by a later passing batch", "a.lean" not in fail)
        check("MUST KEEP: a failing path its owning batch fails", fail == ["b.lean"])
        outs = read_json(os.path.join(o, "outstanding.json"))
        check("MUST KEEP: outstanding ids prefixed, severities untouched",
              [(f["id"], f["severity"]) for f in outs] == [("e1:F1", "bedrock"), ("e2:1", "ordinary")])
        check("MUST BUILD: reason = prefix then per-batch lines, nothing else",
              _read_text(os.path.join(o, "reason.txt")) == "prefix line\n[e1] first\n[e2] second\n")
        check("MUST LIST: files.txt carries the union",
              _read_text(os.path.join(o, "files.txt")) == "a.lean\nb.lean\n")
        check("MUST REPORT: the dropped indictment is named",
              any("dropped indictment: [e1] a.lean" in line for line in rep))
        # No failing, no outstanding: the files are NOT written, and the run says so
        rep = merge([ok1], out("none"))
        check("MUST OMIT: empty failing/outstanding are not written, and say so",
              not os.path.exists(os.path.join(out("none"), "failing.json"))
              and not os.path.exists(os.path.join(out("none"), "outstanding.json"))
              and any("failing.json NOT written" in line for line in rep))
        # Written without a BOM
        check("MUST WRITE: UTF-8 without a BOM",
              not open(os.path.join(o, "observed.json"), "rb").read().startswith(b"\xef\xbb\xbf"))
    finally:
        shutil.rmtree(root, ignore_errors=True)

    for label, ok in results:
        print("  %s  %s" % ("ok  " if ok else "FAIL", label))
    passed = sum(1 for _l, ok in results if ok)
    print("  selftest: %d/%d controls passed - %s"
          % (passed, len(results), "PASS" if passed == len(results) else "FAIL"))
    return 0 if passed == len(results) else 1


def main(argv):
    if argv[:1] in (["selftest"], ["--selftest"]):
        return selftest()
    ap = argparse.ArgumentParser(prog="union_inputs.py", description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd")
    mp = sub.add_parser("merge", help="merge batch folders into one set of record.py inputs")
    mp.add_argument("--out", required=True, help="output folder (absent or empty)")
    mp.add_argument("--reason-prefix", default=None, help="optional first line of the reason")
    mp.add_argument("batches", nargs="+", help="batch folders, in precedence order (last wins)")
    sub.add_parser("selftest", help="run the controls")
    a = ap.parse_args(argv)
    if a.cmd != "merge":
        ap.print_help()
        return 2
    try:
        for line in merge(a.batches, a.out, a.reason_prefix):
            print(line)
    except UnionError as e:
        print("REFUSED: %s" % e)
        return 2
    print("inputs written to %s - pass them to record.py yourself" % a.out)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
