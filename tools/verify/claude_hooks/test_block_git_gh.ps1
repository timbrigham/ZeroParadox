# test_block_git_gh.ps1 - the control for block_git_gh.ps1.
#
# WHY THIS FILE EXISTS. The hook's 21 original controls were run by hand before
# registration and then written down nowhere, so the next change to it - this one -
# had nothing to regress against. A control nobody has seen fail is a hypothesis;
# a control that exists only in a transcript is not even that.
#
# Run:  powershell -File tools\verify\claude_hooks\test_block_git_gh.ps1
# Exit: 0 all controls behaved, 1 otherwise. Prints every row, pass or fail,
#       because a silent green is the failure mode this project keeps measuring.

$ErrorActionPreference = 'Stop'
$hook = Join-Path $PSScriptRoot 'block_git_gh.ps1'
if (-not (Test-Path $hook)) { Write-Host "MISSING: $hook"; exit 1 }

function Invoke-Hook([string]$command) {
    $payload = @{ tool_name = 'PowerShell'; tool_input = @{ command = $command } } | ConvertTo-Json -Compress -Depth 5
    $out = $payload | powershell -NoProfile -File $hook 2>&1 | Out-String
    if ($out -match '"permissionDecision"\s*:\s*"deny"') { return 'DENY' }
    return 'ALLOW'
}

function Invoke-HookRaw([string]$payload) {
    $out = $payload | powershell -NoProfile -File $hook 2>&1 | Out-String
    if ($out -match '"permissionDecision"\s*:\s*"deny"') { return 'DENY' }
    return 'ALLOW'
}

$cases = @(
    # --- MUST DENY: git, every evasion shape the header claims to catch -------
    @{ want = 'DENY';  why = 'bare git';               cmd = 'git status' }
    @{ want = 'DENY';  why = 'cd-chained';             cmd = 'cd C:\Workspace\ZeroParadox; git add -A' }
    @{ want = 'DENY';  why = 'and-chained';            cmd = 'cd /c/repo && gh release create v9.9' }
    @{ want = 'DENY';  why = 'git -C';                 cmd = 'git -C .claude-local status' }
    @{ want = 'DENY';  why = 'absolute exe';           cmd = '& "C:\Program Files\Git\bin\git.exe" push' }
    @{ want = 'DENY';  why = 'shelled from python';    cmd = 'python -c "import subprocess; subprocess.run([''git'',''push''])"' }
    @{ want = 'DENY';  why = 'gh api delete';          cmd = 'gh api -X DELETE /repos/x/y' }
    @{ want = 'DENY';  why = 'gh pr merge';            cmd = 'gh pr merge 12' }
    @{ want = 'DENY';  why = 'both at once';           cmd = 'git log; gh pr list' }

    # --- MUST ALLOW: the word is inside another word, or is a .git/ path read --
    @{ want = 'ALLOW'; why = 'the digit is legitimate'; cmd = 'echo "the digit is legitimate"' }
    @{ want = 'ALLOW'; why = 'high enough through';     cmd = 'echo "high enough through"' }
    @{ want = 'ALLOW'; why = '.gitignore read';         cmd = 'Get-Content .gitignore' }
    @{ want = 'ALLOW'; why = '.git/ path read';         cmd = 'Get-Content .git/hooks/pre-push' }
    @{ want = 'ALLOW'; why = 'github.com URL';          cmd = 'echo https://github.com/timbrigham/x' }
    @{ want = 'ALLOW'; why = 'internal git via python'; cmd = 'python tools/verify/batch.py precommit' }

    # --- MUST DENY: the protected server projects (added 2026-08-23) ----------
    @{ want = 'DENY';  why = 'mcp-mayhem write';        cmd = 'Set-Content C:\Workspace\mcp-mayhem\gitRobot\core\engine.py "x"' }
    @{ want = 'DENY';  why = 'mcp-mayhem read';         cmd = 'Get-Content C:\Workspace\mcp-mayhem\verdictLedger\core\validate.py' }
    @{ want = 'DENY';  why = 'mcp-mayhem cd + run';     cmd = 'Set-Location C:\Workspace\mcp-mayhem\verdictLedger; python -m pytest' }
    @{ want = 'DENY';  why = 'supervisor config';       cmd = 'notepad C:\Workspace\mcp-mayhem\mcpSupervisor\mcp-servers.json' }
    @{ want = 'DENY';  why = 'case-insensitive';        cmd = 'echo C:\WORKSPACE\MCP-MAYHEM\gitRobot' }

    # --- MUST ALLOW: the approved two-hop interaction path -------------------
    @{ want = 'ALLOW'; why = 'C:\temp spec read';       cmd = 'Get-Content C:\temp\verdictLedger.md' }
    @{ want = 'ALLOW'; why = 'C:\temp spec write';      cmd = 'Set-Content C:\temp\notes.md "x"' }
)

$fails = 0
foreach ($c in $cases) {
    $got = Invoke-Hook $c.cmd
    $ok  = ($got -eq $c.want)
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  want={1,-5} got={2,-5}  {3}" -f $mark, $c.want, $got, $c.why | Write-Host
}

# --- fail-closed controls: the hook must DENY when it cannot tell -----------
foreach ($bad in @(@{ why = 'empty stdin'; p = '' }, @{ why = 'malformed json'; p = '{not json' })) {
    $got = Invoke-HookRaw $bad.p
    $ok = ($got -eq 'DENY')
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  want=DENY  got={1,-5}  fail-closed: {2}" -f $mark, $got, $bad.why | Write-Host
}

""
if ($fails -eq 0) { "ALL {0} CONTROLS BEHAVED" -f ($cases.Count + 2) | Write-Host; exit 0 }
"{0} CONTROL(S) MISBEHAVED" -f $fails | Write-Host
exit 1
