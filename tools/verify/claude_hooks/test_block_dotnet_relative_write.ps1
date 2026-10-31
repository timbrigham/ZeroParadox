# test_block_dotnet_relative_write.ps1 - the control for block_dotnet_relative_write.ps1 (DC-71).
#
# Rows (1)-(4) are the four controls the DC-71 detector spec names, in its order. Row (3) is the
# OCCURRENCE SHAPE: a Set-Location into the worktree, then a relative .NET write that lands in the
# main checkout anyway. Row (5) is the other half of (4): a variable assigned from a rooted path in
# the SAME command must ALLOW, or the hook is just denying every variable and (4) proves nothing.
#
# THE MUTATION ROWS each neuter one branch and require the named control to flip (MUT1: the deny
# branch, control (2); MUT2-7: the branches /rely asked to pin, 2026-10-13). Each hashes the
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

    # --- /rely 2026-10-13 O2: pin the branches that matter most. Each has a mutation below. ---
    @{ id='DC71-9';  want='DENY';  tool='PowerShell'; why='Copy with a relative DESTINATION'
       cmd='[IO.File]::Copy("C:\a.txt","b.txt")' }
    @{ id='DC71-10'; want='DENY';  tool='PowerShell'; why='unparseable argument list (fail-closed)'
       cmd='[IO.File]::WriteAllText("x.txt"' }
    @{ id='DC71-11'; want='DENY';  tool='PowerShell'; why='New-Object System.IO.StreamWriter, relative'
       cmd='$w = New-Object System.IO.StreamWriter("x.log"); $w.Close()' }
    # O1: the correct idioms agents already use - both lifted from a real transcript by /rely.
    @{ id='DC71-12'; want='ALLOW'; tool='PowerShell'; why='(Resolve-Path X).Path, the correct idiom'
       cmd='foreach ($f in $Files) { $p = (Resolve-Path $f).Path; [System.IO.File]::WriteAllText($p, "s") }' }
    @{ id='DC71-13'; want='ALLOW'; tool='PowerShell'; why='$_.FullName in a pipeline, the correct idiom'
       cmd='Get-ChildItem C:\x -Filter *.md | ForEach-Object { [IO.File]::WriteAllText($_.FullName, "s") }' }
    # The other side of O1: GetFullPath resolves against the PROCESS directory - the bug itself.
    @{ id='DC71-14'; want='DENY';  tool='PowerShell'; why='[IO.Path]::GetFullPath stays DENIED'
       cmd='[IO.File]::WriteAllText([IO.Path]::GetFullPath("x.txt"),"y")' }
    # O3: bash escapes `\"`, `\$`, `\\` must all be undone before the path is judged.
    @{ id='DC71-15'; want='ALLOW'; tool='Bash';       why='Bash -Command with \$env:TEMP\\x.txt'
       cmd='powershell -Command "[IO.File]::WriteAllText(\"\$env:TEMP\\x.txt\", ''y'')"' }
    # CARRYW3-13 r2 O1: `.FullName` of a FileInfo CONSTRUCTED from a relative string is the
    # process-directory path in disguise. Inline and through a variable, both constructor spellings.
    @{ id='DC71-16'; want='DENY';  tool='PowerShell'; why='FileInfo cast from a relative string, via a variable'
       cmd='$f = [IO.FileInfo]"fi1.txt"; [IO.File]::WriteAllText($f.FullName,"y")' }
    @{ id='DC71-17'; want='DENY';  tool='PowerShell'; why='FileInfo::new on a relative string, inline'
       cmd='[IO.File]::WriteAllText(([IO.FileInfo]::new("x.txt")).FullName,"y")' }
    @{ id='DC71-18'; want='DENY';  tool='PowerShell'; why='New-Object IO.FileInfo on a relative string, inline'
       cmd='[IO.File]::WriteAllText((New-Object IO.FileInfo "x.txt").FullName,"y")' }
    @{ id='DC71-19'; want='ALLOW'; tool='PowerShell'; why='FileInfo cast from an ABSOLUTE string'
       cmd='$f = [IO.FileInfo]''C:\x\a.txt''; [IO.File]::WriteAllText($f.FullName,"y")' }
    @{ id='DC71-20'; want='ALLOW'; tool='PowerShell'; why='(Get-Item ...).FullName, built by the provider'
       cmd='[IO.File]::WriteAllText((Get-Item C:\x\a.txt).FullName,"y")' }
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

# Each mutation neuters ONE branch and names the control it must turn red: the probe is that
# control's own command, and `want` is the OPPOSITE of the control's verdict. `.Replace()` is
# literal, and the SHA is compared so a missed anchor reports FAIL rather than a false pass.
# `@(...)` matters: a lone hashtable indexed with [0] looks up KEY 0 and returns $null.
function Find-Case([string]$id) { return @($cases | Where-Object { $_.id -eq $id })[0] }
$mutations = @(
    @{ id='DC71-MUT1'; ctl='DC71-2';  why='deny branch removed'
       find='if ($bad.Count -gt 0) {'; repl='if ($false) {' }
    @{ id='DC71-MUT2'; ctl='DC71-9';  why='Copy/Move judged on the source only'
       find='if ($member -match ''^(?i)(Copy|Move)$'') { $n = 2 }'; repl='' }
    @{ id='DC71-MUT3'; ctl='DC71-10'; why='unparseable argument list falls OPEN'
       find='$bad.Add("$label - its argument list could not be parsed (fail-closed)"); continue'; repl='continue' }
    @{ id='DC71-MUT4'; ctl='DC71-11'; why='New-Object StreamWriter alternative dropped from the matcher'
       find="'|(?i)New-Object\s+(?:-TypeName\s+)?(?:System\.)?IO\.(?<type>StreamWriter)\b(?<member>)'"; repl="''" }
    @{ id='DC71-MUT5'; ctl='DC71-12'; why='(Resolve-Path X).Path branch removed'
       find='if ($e -match ''^(?i)\(\s*Resolve-Path\b.*\)\.(Path|ProviderPath)$'') { return ''C:\__resolve_path__'' }'; repl='' }
    @{ id='DC71-MUT6'; ctl='DC71-13'; why='.FullName branch removed'
       find='if ($e -match ''^(?i)\S.*\.FullName$'') { return (Resolve-FullName $e $depth) }'; repl='' }
    @{ id='DC71-MUT8'; ctl='DC71-16'; why='FileInfo constructor no longer judged (the r2 O1 proxy)'
       find='    if ($null -eq $ctorArg) { return ''C:\__fullname__'' }'; repl='    return ''C:\__fullname__''' }
    @{ id='DC71-MUT7'; ctl='DC71-15'; why='Bash unescape reverted to \" only'
       find='$cmd = [regex]::Replace($cmd, ''\\(["$\\`])'', ''$1'')'; repl='$cmd = $cmd.Replace(''\"'', ''"'')' }
)
$mi = 0
foreach ($m in $mutations) {
    $mi++
    $c = Find-Case $m.ctl
    $want = if ($c.want -eq 'DENY') { 'ALLOW' } else { 'DENY' }
    $mutPath = Join-Path $mutDir ("mut$mi.ps1")
    Set-Content -Path $mutPath -Value ($src.Replace($m.find, $m.repl)) -Encoding UTF8 -NoNewline
    $mutSha = Get-Sha $mutPath
    if ($mutSha -eq $baseSha) {
        $fails++
        "FAIL  {0}  MUTATION DID NOT APPLY (sha unchanged {1}) - anchor not found: {2}" -f $m.id, $baseSha.Substring(0, 12), $m.why | Write-Host
        continue
    }
    $got = Invoke-HookRawAt $mutPath (Get-Payload $c.tool $c.cmd)
    $ok = ($got -eq $want)
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  {1}  sha {2}->{3}  want={4,-5} got={5,-5}  mutation: {6} -> {7} goes red" -f `
        $mark, $m.id, $baseSha.Substring(0, 8), $mutSha.Substring(0, 8), $want, $got, $m.why, $m.ctl | Write-Host
}
$probe = Get-Payload 'PowerShell' '[IO.File]::WriteAllText("x.txt","y")'

# The unmutated copy, same process, after the mutation: it must still deny (2).
$ctl = Invoke-HookRawAt $baseCopy $probe
$ctlOk = ($ctl -eq 'DENY')
if (-not $ctlOk) { $fails++ }
$mark = if ($ctlOk) { 'ok  ' } else { 'FAIL' }
"{0}  DC71-MUT0  want=DENY  got={1,-5}  unmutated copy, same process, after the mutation" -f $mark, $ctl | Write-Host

Remove-Item -Recurse -Force $mutDir

""
$total = $cases.Count + $closed.Count + $mutations.Count + 1
if ($fails -eq 0) { "ALL {0} CONTROLS BEHAVED" -f $total | Write-Host; exit 0 }
"{0} of {1} CONTROL(S) MISBEHAVED" -f $fails, $total | Write-Host
exit 1
