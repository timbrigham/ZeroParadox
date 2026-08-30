# test_block_checker_truncation.ps1 - the control for block_checker_truncation.ps1.
#
# The sibling hook's controls were written down only after a change had nothing to regress against.
# These exist from the first commit instead. Every row prints, pass or fail: a silent green is the
# failure mode this project keeps measuring.
#
# THE FIRST ROW IS THE REAL ONE. It is the exact command an agent typed on 2026-08-28, verbatim,
# which kept the last two lines of a banner and discarded four encoding warnings above them. A
# control taken from a transcript beats one invented to match the regex.
#
# Run:  powershell -File tools\verify\claude_hooks\test_block_checker_truncation.ps1
# Exit: 0 all controls behaved, 1 otherwise.

$ErrorActionPreference = 'Stop'
$hook = Join-Path $PSScriptRoot 'block_checker_truncation.ps1'
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
    # --- MUST DENY: a checker RUN whose output is cut ------------------------
    @{ want = 'DENY';  why = 'THE MEASURED FAILURE, verbatim';
       cmd = 'python tools/verify/check_encoding.py .claude-local/DEFECTS.md 2>&1 | Select-Object -Last 2' }
    @{ want = 'DENY';  why = 'pipe to head';            cmd = 'python tools/verify/batch.py prepush | head -5' }
    @{ want = 'DENY';  why = 'pipe to tail';            cmd = 'python tools/verify/check_pov.py | tail -3' }
    @{ want = 'DENY';  why = 'Select-Object -First';    cmd = 'python tools/verify/check_paths.py | Select-Object -First 20' }
    @{ want = 'DENY';  why = 'select alias';            cmd = 'python tools/verify/check_prose.py | select -Last 4' }
    @{ want = 'DENY';  why = 'pipe to grep';            cmd = 'python tools/verify/check_poles.py | grep FAIL' }
    @{ want = 'DENY';  why = 'grep -q swallows all';    cmd = 'python tools/verify/check_modal.py | grep -q PASS' }
    @{ want = 'DENY';  why = 'pipe to Select-String';   cmd = 'python tools/verify/check_poles.py --idioms | Select-String Idiom' }
    @{ want = 'DENY';  why = 'pipe to findstr';         cmd = 'python tools/verify/decls.py | findstr ERROR' }
    # The second measured failure, same day: the hook's own author filtered check_paths this way
    # and it passed. Where-Object is grep with a PowerShell accent.
    @{ want = 'DENY';  why = 'Where-Object, MEASURED';
       cmd = 'python tools/verify/check_paths.py > "$sp\p.log" 2>&1; Get-Content "$sp\p.log" | Out-String -Stream | Where-Object { $_ -match "resolve" }' }
    @{ want = 'DENY';  why = 'where alias';             cmd = 'python tools/verify/check_pov.py | where { $_ -match "FAIL" }' }
    @{ want = 'DENY';  why = '? alias';                 cmd = 'python tools/verify/check_prose.py | ? { $_ -match "cap" }' }
    @{ want = 'DENY';  why = 'backslash path';          cmd = 'python tools\verify\check_figures.py | head -10' }
    @{ want = 'DENY';  why = 'absolute path';           cmd = 'python C:\Workspace\ZeroParadox\tools\verify\guards.py | head' }
    @{ want = 'DENY';  why = 'interpreter flag first';  cmd = 'python -u tools/verify/check_hashes.py | head -2' }
    @{ want = 'DENY';  why = 'py launcher';             cmd = 'py tools/verify/check_moved.py | tail -1' }
    @{ want = 'DENY';  why = 'a ps1 checker via &';     cmd = '& tools\verify\claude_hooks\test_block_git_gh.ps1 | Select-Object -First 3' }
    @{ want = 'DENY';  why = 'redirect THEN cut, one call';
       cmd = 'python tools/verify/batch.py precommit > out.log 2>&1; Get-Content out.log -Tail 20' }
    @{ want = 'DENY';  why = 'TotalCount on the log';
       cmd = 'python tools/verify/check_pov.py > out.log 2>&1; Get-Content out.log -TotalCount 15' }

    # --- MUST ALLOW: the compliant shape -------------------------------------
    @{ want = 'ALLOW'; why = 'redirect and read whole';
       cmd = 'python tools/verify/batch.py precommit > "$sp\pc.log" 2>&1; "EXIT=$LASTEXITCODE"; Get-Content "$sp\pc.log"' }
    @{ want = 'ALLOW'; why = 'run with no pipe at all'; cmd = 'python tools/verify/check_encoding.py BOTTOMELEMENT.md' }
    @{ want = 'ALLOW'; why = 'selftest, read whole';    cmd = 'python tools/verify/check_poles.py --selftest' }
    @{ want = 'ALLOW'; why = 'Out-File is not a cut';   cmd = 'python tools/verify/check_prose.py 2>&1 | Out-File -FilePath x.log -Encoding utf8' }
    @{ want = 'ALLOW'; why = 'Select-Object w/o First'; cmd = 'python tools/verify/decls.py | Select-Object -Property Name' }

    # --- MUST ALLOW: reading or grepping checker SOURCE is not running it ----
    @{ want = 'ALLOW'; why = 'grep checker source';     cmd = 'grep -n "check_poles" tools/verify/batch.py | head -20' }
    # MEASURED false positive, 2026-08-29: `\bpy\b` matched the `py` of a `.py` EXTENSION, so
    # grepping two checker sources at once read as the `py` launcher. The header promises this case.
    @{ want = 'ALLOW'; why = 'grep TWO checker sources, MEASURED';
       cmd = 'grep -n "SCAN_EXT" tools/verify/check_pov.py tools/verify/check_prose.py | head -20' }
    @{ want = 'ALLOW'; why = 'three sources, no interpreter';
       cmd = 'grep -n html tools/verify/check_poles.py tools/verify/check_modal.py tools/verify/decls.py | head' }
    # ...and the real launcher must still be caught, so the fix cannot have opened a hole.
    @{ want = 'DENY';  why = 'py launcher still denied';  cmd = 'py tools/verify/check_pov.py | head -3' }
    @{ want = 'DENY';  why = 'python3 still denied';      cmd = 'python3 tools/verify/check_pov.py | grep FAIL' }
    @{ want = 'ALLOW'; why = 'page checker source';     cmd = 'Get-Content tools/verify/check_poles.py | Select-Object -First 40' }
    @{ want = 'ALLOW'; why = 'sed the source';          cmd = 'sed -n "1,60p" tools/verify/check_paths.py' }
    @{ want = 'ALLOW'; why = 'README under verify';     cmd = 'cat tools/verify/README.md | head -30' }

    # --- MUST ALLOW: build.log, which has a hook REQUIRING a row limit -------
    @{ want = 'ALLOW'; why = 'build.log limited read';
       cmd = 'python tools/verify/batch.py precommit; Get-Content build.log -Tail 50' }
    @{ want = 'ALLOW'; why = 'build.log TotalCount';
       cmd = 'python tools/verify/decls.py; Get-Content build.log -TotalCount 100' }

    # --- MUST ALLOW: nothing under tools/verify is being run ----------------
    @{ want = 'ALLOW'; why = 'unrelated pipeline';      cmd = 'Get-ChildItem scripts | Select-Object -First 5' }
    @{ want = 'ALLOW'; why = 'a scratchpad probe';      cmd = 'python "$sp\probe_poles.py" | head -5' }
    @{ want = 'ALLOW'; why = 'a build script';          cmd = 'python scripts/build_zpi.py | tail -20' }
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
