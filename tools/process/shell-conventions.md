# Shell conventions on this workstation — and why content never travels on a command line

**Body for `CLAUDE.md` § `R-SHELL`.** The rule there is four lines; these are the measured failures
behind each of them.

*Created 2026-08-28 by migrating six private memories. `R-SHELL` had no `READ` pointer, so this
material was routed to no file in the repository and sat only in a memory index that spawned agents
never receive (`R-BRIEF`: "Memory BODIES never arrive at all"). Every incident below is measured on
this project.*

---

## PowerShell, not Bash with Unix commands

The OS is Windows 11. Bash is available and the dedicated tools (`Glob`, `Grep`, `Read`, `Write`,
`Edit`) are platform-agnostic and always preferred — reach for a shell only when they cannot do the
job, and when you do, reach for PowerShell.

**`find` hangs silently here** and has caused tool failures across multiple sessions. Use `Glob`. The
same applies to `ls` for a listing `Glob` can produce.

⚠ **NEVER prepend `cd C:\Workspace\ZeroParadox;`.** The working directory is already correct at
session start, and prepending `cd` builds a compound command string that **misses the allowlist**,
which triggers avoidable permission prompts and has caused repeated failures.

## Every external process gets `timeout: 300000`

Any call that runs an external process — a PDF build script, `lake build`, `python <script>` — takes
a five-minute timeout. **No exceptions, even for commands that look instant:** inconsistent
application has caused remote force-kills of the session.

**Why:** PDF and `lake` builds have hung indefinitely more than once, blocking a session for an hour
with no recovery. If it times out, **diagnose rather than retry blindly** — for a cold `lake build`
five minutes may genuinely be too short, and that is information, not a reason to loop.

## Allowlist matching, and the `&&` that does not exist

**The `*` wildcard in `settings.json` stops matching at shell metacharacters (`|`, `&`, `;`).** So
`PowerShell(lake build *)` does **not** match `lake build 2>&1 | Out-File ...`, because `2>&1`
contains `&`. For simple commands wildcards are fine; for compound ones, either add an exact entry or
split into separate calls.

⚠ **`&&` IS NOT VALID IN POWERSHELL 5.1.** It is a parser error — *"The token '&&' is not a valid
statement separator."* Use `;` to sequence unconditionally, or `A; if ($?) { B }` to run B only when A
succeeds. This is a bash-ism and it has been flagged repeatedly.

## Long scripts go to the scratchpad, then run by path

A multi-line script passed inline is too large for the allowlist pattern matcher and gets prompted or
rejected. Past roughly three or four lines, write the script to a file and invoke it by path.

⚠ **The destination is the SESSION SCRATCHPAD, never the repository tree.** An earlier version of
this convention said `.claude-local\`, which is inside the tree and therefore wrong under `R-BRIEF`'s
*"NO SCRATCH FILES IN THE REPO"*. A review agent's scratch probe reached permanent history exactly
that way.

---

## ⭐ THE GENERAL RULE (Tim, 2026-08-22): CONTENT NEVER TRAVELS ON A COMMAND LINE

> *"I would really rather that whatever you're writing not be passed on the command line — using a
> file as the transport is safe."*

**Any generated content — a prompt, a commit message, a patch, captured output — moves by FILE or
STDIN, never as an argv string.** Three independent hazards, and they fail differently:

1. **LENGTH.** Windows caps a command line at ~32,767 characters. Measured 2026-08-22: passing 848
   lines of checker output to `claude -p` died with `FileNotFoundError(2, 'The filename or extension
   is too long', ..., 206)` **before reaching the API** — $0.00, 0.0s. It fired exactly when the tool
   was most needed, and **no small fixture could ever have surfaced it.**
2. **QUOTING.** Real content carries quotes, backticks, newlines, `%`, `$` — each a metacharacter to
   some shell.
3. **ENCODING.** An argv string crosses a codepage boundary on Windows; a stream with an explicit
   `encoding="utf-8"` does not.

**How:** `subprocess.run(cmd, input=text, text=True, encoding="utf-8")`, or write a temp file and pass
its path. `gitRobot.commit` takes a `message_file` for exactly this reason.

⚠ **PowerShell's `Add-Content`/`Set-Content` default to the system ANSI codepage.** Writing non-ASCII
through them corrupts a file to *undecodable* — done on 2026-08-22 to a queue ticket, caught by
`check_encoding --block`, restored from the index. Pass `-Encoding utf8`, or use the Write/Edit tools.
See `tools/process/file-encoding.md`.

### Editing a file programmatically: one pattern, and three measured failures behind it

Write the script to the scratchpad, and inside it: read → build the string → `data =
s.encode("utf-8")` → write a temp file → `os.replace(tmp, path)`. **Assert every `old` substring
matches before replacing**, printing a loud `!! NOT MATCHED` rather than silently no-op'ing.

**Two of the three failures were SILENT:**

1. **`python -c "..."` in the Bash tool EATS BACKTICKS.** The shell expands them inside double quotes,
   so every `` `identifier` `` is stripped or command-substituted. **It exits 0 and prints a success
   message while writing corrupted content.** Hit twice in one session (2026-08-07) — once destroying
   a `DEFECTS.md` entry, once leaving a research note as prose with holes where every Lean
   declaration name had been. Markdown and Lean prose are backtick-dense, so this corrupts nearly
   every write of that kind.
2. **`io.open(path, "w")` TRUNCATES IMMEDIATELY.** If anything then throws during encode, the file is
   left at 0 bytes. This happened to a `.lean` file, and **`lake build` reported SUCCESS**, because an
   empty Lean file compiles trivially. Encoding *before* opening anything means the exception fires
   while the original is still intact — verified 2026-08-07, when a bad escape threw and the target
   was untouched.
3. **Malformed surrogate escapes throw at encode time.** An astral character written literally is not
   valid Python source; use the single escape (`\U0001D4DD`, `\U0001D4E7`). This is the exception that
   fires in (2).
