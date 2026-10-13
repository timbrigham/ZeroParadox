# test_block_dotnet_relative_write.ps1 - the control for block_dotnet_relative_write.ps1 (DC-71).
#
# Rows (1)-(4) are the four controls the DC-71 detector spec names, in its order. Row (3) is the
# OCCURRENCE SHAPE: a Set-Location into the worktree, then a relative .NET write that lands in the
# main checkout anyway. Row (5) is the other half of (4): a variable assigned from a rooted path in
# the SAME command must ALLOW, or the hook is just denying every variable and (4) proves nothing.
#
# THE MUTATION ROW removes the deny branch and requires control (2) to flip to ALLOW. It hashes the
# mutated copy first and reports FAIL if the hash did not move - a /rely reviewer once read an
# unperturbed hook as neutered because its `-replace` silently missed (test_block_corpus_edit.ps1).
#
# Run:  powershell -File tools\verify\claude_hooks\test_block_dotnet_relative_write.ps1
# Exit: 0 all controls behaved, 1 otherwise. Prints every row, pass or fail.

$ErrorActionPreference = 'Stop'
$hook = Join-Path $PSScriptRoot 'block_dotnet_relative_write.ps1'
if (-not (Test-Path $hook)) { Write-Host "MISSING: $hook"; exit 1 }

function Invoke-HookRawAt([string]$hookPath, [string]$payload) {
    $out = $payload | powershell -NoProfile -File $hookPath 2>&1 | Out-String
    if ($out -match '"permissionDecision"\s*:\s*"deny"') { return 'DENY' }
    return 'ALLOW'
}

function Get-Payload([string]$tool, [string]$command) {
    return (@{ tool_name = $tool; tool_input = @{ command = $command } } | ConvertTo-Json -Compress -Depth 5)
}

$cases = @(
    @{ id='DC71-1'; want='ALLOW'; tool='PowerShell'; why='absolute path'
       cmd='[IO.File]::WriteAllText("C:\abs\x.txt","y")' }
    @{ id='DC71-2'; want='DENY';  tool='PowerShell'; why='relative path'
       cmd='[IO.File]::WriteAllText("x.txt","y")' }
    @{ id='DC71-3'; want='DENY';  tool='PowerShell'; why='Set-Location then relative (the occurrence shape)'
       cmd='Set-Location C:\wt; [IO.File]::WriteAllText("x.txt","y")' }
    @{ id='DC71-4'; want='DENY';  tool='PowerShell'; why='Join-Path on an unresolvable variable'
       cmd='$p = Join-Path $wt x.txt; [IO.File]::WriteAllText($p,"y")' }
    @{ id='DC71-5'; want='ALLOW'; tool='PowerShell'; why='Join-Path on a variable rooted in the same command'
       cmd='$wt = ''C:\wt''; $p = Join-Path $wt x.txt; [IO.File]::WriteAllText($p,"y")' }
    @{ id='DC71-6'; want='DENY';  tool='Bash';       why='Bash tool, powershell -Command with escaped quotes'
       cmd='powershell -NoProfile -Command "[System.IO.File]::WriteAllText(\"x.txt\",\"y\")"' }
    @{ id='DC71-7'; want='DENY';  tool='PowerShell'; why='StreamWriter constructor, relative'
       cmd='$w = [System.IO.StreamWriter]::new("out\log.txt"); $w.Close()' }
    @{ id='DC71-8'; want='ALLOW'; tool='PowerShell'; why='a read, and no write call at all'
       cmd='[IO.File]::ReadAllText("x.txt"); Get-ChildItem' }
)

$fails = 0
foreach ($c in $cases) {
    $got = Invoke-HookRawAt $hook (Get-Payload $c.tool $c.cmd)
    $ok = ($got -eq $c.want)
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  {1}  want={2,-5} got={3,-5}  {4}" -f $mark, $c.id, $c.want, $got, $c.why | Write-Host
}

# --- fail-closed: the hook must DENY when it cannot tell ---------------------------------------
$closed = @(
    @{ id='DC71-FC1'; why='empty stdin';    p='' }
    @{ id='DC71-FC2'; why='malformed json'; p='{not json' }
)
foreach ($b in $closed) {
    $got = Invoke-HookRawAt $hook $b.p
    $ok = ($got -eq 'DENY')
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  {1}  want=DENY  got={2,-5}  fail-closed: {3}" -f $mark, $b.id, $got, $b.why | Write-Host
}

# --- MUTATION: remove the deny branch; control (2) must go ALLOW -------------------------------
""
$src = Get-Content $hook -Raw
$mutDir = Join-Path ([System.IO.Path]::GetTempPath()) ("zp-dc71-mut-" + [guid]::NewGuid().ToString('N').Substring(0, 8))
New-Item -ItemType Directory -Path $mutDir -Force | Out-Null
function Get-Sha([string]$path) { return (Get-FileHash -Algorithm SHA256 -Path $path).Hash }

$baseCopy = Join-Path $mutDir 'base.ps1'
Set-Content -Path $baseCopy -Value $src -Encoding UTF8 -NoNewline
$baseSha = Get-Sha $baseCopy

$mutPath = Join-Path $mutDir 'mut1.ps1'
Set-Content -Path $mutPath -Value ($src.Replace('if ($bad.Count -gt 0) {', 'if ($false) {')) -Encoding UTF8 -NoNewline
$mutSha = Get-Sha $mutPath
$probe = Get-Payload 'PowerShell' '[IO.File]::WriteAllText("x.txt","y")'
if ($mutSha -eq $baseSha) {
    $fails++
    "FAIL  DC71-MUT1  MUTATION DID NOT APPLY (sha unchanged {0}) - anchor not found" -f $baseSha.Substring(0, 12) | Write-Host
} else {
    $got = Invoke-HookRawAt $mutPath $probe
    $ok = ($got -eq 'ALLOW')
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  DC71-MUT1  sha {1}->{2}  want=ALLOW got={3,-5}  mutation: deny branch removed -> control (2) passes through" -f `
        $mark, $baseSha.Substring(0, 8), $mutSha.Substring(0, 8), $got | Write-Host
}

# The unmutated copy, same process, after the mutation: it must still deny (2).
$ctl = Invoke-HookRawAt $baseCopy $probe
$ctlOk = ($ctl -eq 'DENY')
if (-not $ctlOk) { $fails++ }
$mark = if ($ctlOk) { 'ok  ' } else { 'FAIL' }
"{0}  DC71-MUT0  want=DENY  got={1,-5}  unmutated copy, same process, after the mutation" -f $mark, $ctl | Write-Host

Remove-Item -Recurse -Force $mutDir

""
$total = $cases.Count + $closed.Count + 2
if ($fails -eq 0) { "ALL {0} CONTROLS BEHAVED" -f $total | Write-Host; exit 0 }
"{0} of {1} CONTROL(S) MISBEHAVED" -f $fails, $total | Write-Host
exit 1
