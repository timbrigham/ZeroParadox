# enforce_log_read_limits.ps1
# PreToolUse hook — blocks unbounded PowerShell log reads that freeze sessions.
# Fires on: PowerShell(Get-Content build.log*)
# Blocks if: no Select-Object -First/-Last or -TotalCount/-Tail limit present.

$raw = [Console]::In.ReadToEnd()
if (-not $raw) { exit 0 }

try { $data = $raw | ConvertFrom-Json } catch { exit 0 }

$cmd = $data.tool_input.command
if (-not $cmd) { exit 0 }

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
