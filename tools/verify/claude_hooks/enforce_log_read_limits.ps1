# enforce_log_read_limits.ps1
# PreToolUse hook - blocks unbounded PowerShell log reads that freeze sessions.
# Fires on: PowerShell(Get-Content build.log*)
# Blocks if: no Select-Object -First/-Last or -TotalCount/-Tail limit present.
#
# FAIL CLOSED ON BAD INPUT. Empty stdin and unparseable JSON now BLOCK, matching
# block_git_gh.ps1, which states the principle and has 24/24 on its own suite including
# both of these cases: "Unparseable input, empty stdin, a missing field -> DENY."
# This hook used to `exit 0` on both - allow-on-error. That exact shape was measured
# biting the retired gate-lock hook, where a path-normalisation throw hit its catch and
# the lock never fired. A hook that cannot read its input cannot rule out the thing it
# exists to stop, so it must not pretend the input was safe.
# A MISSING command field still allows, exactly as the sibling does: that means the tool
# is not command-bearing, which is a fact about the input, not a failure to read it.

function Block([string]$reason) {
    @{ continue = $false; stopReason = $reason } | ConvertTo-Json
    exit 0
}

$raw = [Console]::In.ReadToEnd()
if ([string]::IsNullOrWhiteSpace($raw)) {
    Block "Blocked (fail-closed): the log-read hook received empty input and cannot tell whether an unbounded log read was requested."
}

try { $data = $raw | ConvertFrom-Json } catch {
    Block "Blocked (fail-closed): the log-read hook could not parse its input, so it cannot rule out an unbounded log read."
}

$cmd = $data.tool_input.command
if (-not $cmd) { exit 0 }   # not a command-bearing tool; nothing to inspect

$isLogRead = $cmd -match 'Get-Content[^|]*\.log'
if (-not $isLogRead) { exit 0 }

$hasLimit = (
    $cmd -match 'Select-Object\s+-(First|Last)\s+\d' -or
    $cmd -match 'Get-Content\s+[^|]+-TotalCount\s+\d' -or
    $cmd -match 'Get-Content\s+[^|]+-Tail\s+\d'
)

if (-not $hasLimit) {
    @{
        continue   = $false
        stopReason = "Unbounded log read blocked (session freeze risk). Add '| Select-Object -First N' or '| Select-Object -Last N' to the pipeline before running."
    } | ConvertTo-Json
    exit 0
}

exit 0
