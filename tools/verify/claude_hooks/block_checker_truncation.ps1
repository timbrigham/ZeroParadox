# block_checker_truncation.ps1
# PreToolUse hook - DENIES any Bash/PowerShell call that RUNS a checker under tools/verify and
# pipes its output into a truncating or filtering consumer.
#
# WHY THIS EXISTS WHEN A RULE ALREADY SAID SO.
# CLAUDE.md R-TRUNC has said "never truncate a hook-running command" for weeks, and a memory says
# it again. On 2026-08-28 an agent typed
#       python tools/verify/check_encoding.py .claude-local/DEFECTS.md 2>&1 | Select-Object -Last 2
# roughly one hour after quoting R-TRUNC back at itself, and the two lines it kept were the tail of
# a remediation banner. The four double-encoding WARNINGS above them were invisible. Re-run whole,
# they were there.
#
# THE DIAGNOSIS IS THE TRIGGER, NOT THE WORDING (CLAUDE.md R-RECUR: an ACTION binds, a CATEGORY
# leaks). R-TRUNC is keyed to "a command that runs a GATE". A one-file encoding confirmation did not
# feel like a gate, so the category did not fire. The action does: you are putting a pipe after a
# tools/verify path. That is typeable, mechanical, and needs no judgement - which is the whole
# reason it is here rather than in a fourth paragraph of prose.
#
# WHAT IT IS PROTECTING. A checker's verdict is the WHOLE of its output. Exit 0 is not "clean" - it
# routinely means "no BLOCKING findings, and N warnings you have not read". Every early-exiting or
# filtering consumer removes exactly the part that was not the symptom you went looking for, which
# is where the finding lives. Worse, an early-exiting consumer can also destroy the EXIT STATUS: a
# push blocked bare exited 1 and the same push through `| head -5` exited 0, because the hook died
# of SIGPIPE before reaching its own `exit 1`.
#
# IT TESTS INVOCATION, NOT MENTION - deliberately. Reading, grepping and paging checker SOURCE stays
# allowed, because that is how a checker gets understood and it truncates nothing:
#       grep -n "check_poles" tools/verify/batch.py | head -20      <- ALLOWED, greps a file
#       python tools/verify/check_poles.py | head -20               <- DENIED, runs a checker
# The interpreter token has to govern the path. This is the same proxy-for-property care the sibling
# hook's header describes: match what RUNS, not where the string happens to point.
#
# THE build.log CARVE-OUT, and why it is not a hole. A sibling hook (enforce_log_read_limits.ps1)
# goes the OTHER way and REQUIRES a row limit on `Get-Content build.log*`, because a Lean build log
# is enormous and unbounded. Those two rules would deadlock on one command line. build.log is raw
# compiler output rather than a verdict, so a limited read of it is removed from the string before
# the truncator scan - the same residual technique block_git_gh.ps1 uses for `.git/` path reads.
#
# WHAT THIS DOES *NOT* CATCH, stated so nobody mistakes it for a seal:
#   - TWO SEPARATE TOOL CALLS. Run the checker in one call, narrowly grep the log in the next, and
#     each command string is clean. This is the sneakier form and the hook cannot see it; only
#     reading the file whole fixes that one.
#   - a wrapper script written to disk and then executed - its own command line carries no pipe.
#   - the Read tool with `offset`/`limit` against a saved log.
# The threat model is DRIFT, not malice: the failure being priced is an agent reaching for `| head`
# out of habit while believing it is being efficient.
#
# IT FAILS CLOSED, matching block_git_gh.ps1. An allow-on-error blocker is not a blocker; it is one
# with an undocumented bypass that opens precisely when something unexpected happens.
#
# Controls: tools\verify\claude_hooks\test_block_checker_truncation.ps1

$raw = [Console]::In.ReadToEnd()

function Deny([string]$reason) {
    $out = @{
        hookSpecificOutput = @{
            hookEventName            = 'PreToolUse'
            permissionDecision       = 'deny'
            permissionDecisionReason = $reason
        }
    }
    Write-Output ($out | ConvertTo-Json -Compress -Depth 5)
    exit 0
}

$GUIDANCE = @'
READ THE CHECKER OUTPUT WHOLE. Redirect it to a file, then open the file:

    python tools/verify/<checker>.py <args> > "$sp\out.log" 2>&1
    "EXIT=$LASTEXITCODE"
    Get-Content "$sp\out.log"

WHY, precisely:
  * A green exit is not "clean". These checkers routinely exit 0 while reporting warnings, counts
    and suppression totals, and the count IS the finding. check_poles is a COUNTER that gates
    nothing - a real bedrock defect shipped while it printed the site on every run.
  * An early-exiting consumer can destroy the EXIT STATUS as well as the text. The identical push
    exited 1 bare and 0 through `| head -5`: SIGPIPE killed the hook before its own `exit 1`.
  * The part you filter away is by construction the part you were not already looking for.

If the output is genuinely too large to read, that is worth saying out loud rather than sampling
silently - and it is a reason to fix the checker's reporting, not to keep the first twenty lines.

NOT AFFECTED: reading or grepping checker SOURCE (`grep -n x tools/verify/batch.py | head`), and a
limited read of build.log, which is raw compiler output and has its own hook requiring a row limit.
'@

if ([string]::IsNullOrWhiteSpace($raw)) {
    Deny "BLOCKED (fail-closed): the hook received empty input and cannot tell what was requested.`n`n$GUIDANCE"
}

try { $data = $raw | ConvertFrom-Json } catch {
    Deny "BLOCKED (fail-closed): the hook could not parse its input, so it cannot rule out a truncated checker run.`n`n$GUIDANCE"
}

$cmd = $data.tool_input.command
if ($null -eq $cmd) { exit 0 }   # not a command-bearing tool; nothing to inspect

# --- Does this command RUN something under tools/verify? --------------------
# An interpreter token must GOVERN the path, so that grepping or paging checker source stays clear.
# Flags between the interpreter and the script are allowed (`python -u tools/verify/x.py`).
# ⚠ THE LOOKBEHIND IS LOAD-BEARING, added 2026-08-29 after this hook blocked a command its own
# header promises to allow. `\bpy\b` matches the `py` of a `.py` EXTENSION, so grepping two checker
# sources at once - `grep -n x check_pov.py tools/verify/check_prose.py | head` - parsed as the `py`
# launcher running a checker. Excluding a preceding dot or word char keeps the real launcher and
# drops the extension.
$RUN_PY  = '(?i)(?<![\w.])(?:python3?|py)\b(?:\s+-\S+)*\s+["'']?[^"''|;]*tools[\\/]verify[\\/]\S+\.py'
$RUN_PS  = '(?i)(?:&|powershell(?:\s+-\S+)*\s+-File)\s+["'']?[^"''|;]*tools[\\/]verify[\\/]\S+\.ps1'
if (-not ($cmd -match $RUN_PY -or $cmd -match $RUN_PS)) { exit 0 }

# --- Remove limited build.log reads before scanning for truncators ----------
# Raw compiler output, not a verdict, and a sibling hook REQUIRES it be limited. Stripping the whole
# read (rather than allowlisting the flag) keeps `-Tail` meaningful everywhere else in the string.
$scan = [regex]::Replace($cmd, '(?i)Get-Content[^;|]*build\.log[^;|]*', '')

# --- Truncating or filtering consumers -------------------------------------
# Ordered most-specific first only for the reporting label; any one of them is a deny.
$TRUNCATORS = @(
    @{ label = '| head';                    rx = '(?i)\|\s*head\b' },
    @{ label = '| tail';                    rx = '(?i)\|\s*tail\b' },
    @{ label = '| more';                    rx = '(?i)\|\s*more\b' },
    @{ label = 'Select-Object -First/-Last'; rx = '(?i)\|\s*(?:Select-Object|select)\b[^|;]*-(?:First|Last)\b' },
    @{ label = '| grep';                    rx = '(?i)\|\s*grep\b' },
    @{ label = '| Select-String';           rx = '(?i)\|\s*(?:Select-String|sls)\b' },
    @{ label = '| findstr';                 rx = '(?i)\|\s*findstr\b' },
    # ⚠ ADDED 2026-08-28, the same day, after the author of this hook filtered a check_paths run
    # through `Out-String -Stream | Where-Object {...}` and it passed. Where-Object IS grep with a
    # PowerShell accent; omitting it left the native-idiom half of the hole open while the Unix half
    # was closed. Aliases `where` and `?` included - `?` needs no word boundary, being punctuation.
    @{ label = '| Where-Object';            rx = '(?i)\|\s*(?:Where-Object\b|where\b|\?)' },
    @{ label = '-TotalCount';               rx = '(?i)-TotalCount\b' },
    @{ label = '-Tail';                     rx = '(?i)-Tail\b' }
)

$hit = $null
foreach ($t in $TRUNCATORS) {
    if ($scan -match $t.rx) { $hit = $t.label; break }
}
if ($null -eq $hit) { exit 0 }

$snippet = $cmd.Trim()
if ($snippet.Length -gt 240) { $snippet = $snippet.Substring(0, 240) + ' ...' }

Deny @"
BLOCKED: this command runs a checker under tools/verify and truncates its output ($hit).

  $snippet

$GUIDANCE
"@
