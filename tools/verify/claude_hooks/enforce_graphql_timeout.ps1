# enforce_graphql_timeout.ps1
# PreToolUse hook: forces a 30-second timeout on all gh api graphql calls.
# Reads the tool input from stdin, overrides the timeout field, and returns
# updatedInput so the caller cannot bypass the cap.
#
# FAIL CLOSED ON BAD INPUT. This hook's job is to APPLY a cap, so failing to read its
# input means the call would proceed UNCAPPED - the precise outcome it exists to prevent.
# It used to `exit 0` on empty or unparseable stdin, which is allow-on-error: the same
# shape that let the retired gate-lock hook never fire. block_git_gh.ps1 states the rule
# and has 24/24 on its own suite: "Unparseable input, empty stdin, a missing field -> DENY."
#
# NOTE: this hook is currently UNREACHABLE - block_git_gh.ps1 denies any command invoking
# `gh` before this one is consulted (RLY31-11). Fixed anyway: a control that is dead today
# and wrong is a trap for whoever makes it live again.

function Deny([string]$reason) {
    @{
        hookSpecificOutput = @{
            hookEventName            = 'PreToolUse'
            permissionDecision       = 'deny'
            permissionDecisionReason = $reason
        }
    } | ConvertTo-Json -Compress -Depth 5
    exit 0
}

$raw = [Console]::In.ReadToEnd()
if ([string]::IsNullOrWhiteSpace($raw)) {
    Deny "Blocked (fail-closed): the graphql timeout hook received empty input, so it cannot apply the 30s cap and cannot confirm the call is capped."
}

try {
    $j = $raw | ConvertFrom-Json
} catch {
    Deny "Blocked (fail-closed): the graphql timeout hook could not parse its input, so it cannot apply the 30s cap."
}

# NOTE: named $ti, not $input - `$input` is a PowerShell AUTOMATIC variable (the pipeline
# enumerator) and assigning to it is unsafe inside a function scope.
$ti = $j.tool_input
if ($null -eq $ti) { exit 0 }   # not a command-bearing tool; nothing to cap

# Override (or add) timeout - 30000 ms hard cap
$ti | Add-Member -NotePropertyName 'timeout' -NotePropertyValue 30000 -Force
@{
    hookSpecificOutput = @{
        hookEventName = "PreToolUse"
        updatedInput  = $ti
    }
} | ConvertTo-Json -Depth 5
