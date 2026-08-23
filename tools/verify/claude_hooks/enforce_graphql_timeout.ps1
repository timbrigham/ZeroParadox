# enforce_graphql_timeout.ps1
# PreToolUse hook: forces a 30-second timeout on all gh api graphql calls.
# Reads the tool input from stdin, overrides the timeout field, and returns
# updatedInput so the caller cannot bypass the cap.
$raw = [Console]::In.ReadToEnd()
try {
    $j = $raw | ConvertFrom-Json
    $input = $j.tool_input
    # Override (or add) timeout — 30 000 ms hard cap
    $input | Add-Member -NotePropertyName 'timeout' -NotePropertyValue 30000 -Force
    @{
        hookSpecificOutput = @{
            hookEventName = "PreToolUse"
            updatedInput  = $input
        }
    } | ConvertTo-Json -Depth 5
} catch {
    exit 0
}
