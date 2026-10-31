# test_block_checker_truncation.ps1 - the control for block_checker_truncation.ps1.
#
# Every row prints, pass or fail: a silent green is the failure mode this project keeps measuring.
# THE FIRST ROW IS THE REAL ONE - the exact command an agent typed on 2026-08-28, verbatim.
#
# The rows come in three groups, matching the hook's three properties:
#   - the INVERSION (RLY40-1): every consumer the denylist version let through is a must-DENY row
#     here, and the sinks are the must-ALLOW rows. A consumer added to no list is still denied.
#   - INVOCATION, NOT MENTION (RLY40-4): text that names a checker without running it - quoted, in a
#     here-string, in a heredoc, in a comment, or a limited read of an UNRELATED file - must ALLOW.
#   - FAIL-CLOSED: unreadable input, and shapes the tokeniser cannot attribute, must DENY.
#
# Run:  powershell -NoProfile -File tools\verify\claude_hooks\test_block_checker_truncation.ps1 [-HookPath <copy>]
#       -HookPath runs the rows against another copy of the hook (how a mutation is checked).
# Exit: 0 all controls behaved, 1 otherwise.
#
# The harness decides on the evidence production has: exit code, then stdout alone, then exactly
# one JSON document, then the decision field. Unreadable output is ERROR, never ALLOW (R-ZERONULL).

param([string]$HookPath = '')

$ErrorActionPreference = 'Stop'
$hook = if ($HookPath) { $HookPath } else { Join-Path $PSScriptRoot 'block_checker_truncation.ps1' }
if (-not (Test-Path -LiteralPath $hook)) { Write-Host "MISSING: $hook"; exit 1 }

$tmpDir = Join-Path ([IO.Path]::GetTempPath()) ("truncctl_" + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $tmpDir -Force | Out-Null
$utf8 = New-Object Text.UTF8Encoding($false)

function Invoke-HookScript([string]$ScriptPath, [string]$Payload) {
    $inFile  = Join-Path $tmpDir ("in_"  + [guid]::NewGuid().ToString('N') + '.json')
    $outFile = Join-Path $tmpDir ("out_" + [guid]::NewGuid().ToString('N') + '.txt')
    $errFile = Join-Path $tmpDir ("err_" + [guid]::NewGuid().ToString('N') + '.txt')
    [IO.File]::WriteAllText($inFile, $Payload, $utf8)
    $p = Start-Process -FilePath 'powershell.exe' -ArgumentList @('-NoProfile', '-File', $ScriptPath) `
            -RedirectStandardInput $inFile -RedirectStandardOutput $outFile `
            -RedirectStandardError $errFile -NoNewWindow -PassThru -Wait
    $stdout = if (Test-Path -LiteralPath $outFile) { [IO.File]::ReadAllText($outFile) } else { '' }
    $res = @{ Why = ''; Reason = '' }
    if ($p.ExitCode -ne 0) { $res.Verdict = 'ERROR'; $res.Why = "hook exited $($p.ExitCode)"; return $res }
    if ([string]::IsNullOrWhiteSpace($stdout)) { $res.Verdict = 'ALLOW'; return $res }
    try { $obj = $stdout | ConvertFrom-Json } catch { $res.Verdict = 'ERROR'; $res.Why = 'stdout is not JSON'; return $res }
    if ($obj -is [array]) { $res.Verdict = 'ERROR'; $res.Why = 'more than one JSON document'; return $res }
    $d = $null; if ($null -ne $obj.hookSpecificOutput) { $d = $obj.hookSpecificOutput.permissionDecision }
    switch ("$d") {
        'deny'  { $res.Verdict = 'DENY'; $res.Reason = "$($obj.hookSpecificOutput.permissionDecisionReason)" }
        'allow' { $res.Verdict = 'ALLOW' }
        default { $res.Verdict = 'ERROR'; $res.Why = "no usable permissionDecision ('$d')" }
    }
    return $res
}

function New-Payload([string]$command, [string]$tool) {
    return (@{ tool_name = $tool; tool_input = @{ command = $command } } | ConvertTo-Json -Compress -Depth 5)
}

$NL = "`n"
$cases = @(
    # --- MUST DENY: a checker RUN whose output is cut (the original rows) -----
    @{ want = 'DENY';  why = 'THE MEASURED FAILURE, verbatim';
       cmd = 'python tools/verify/check_encoding.py .claude-local/DEFECTS.md 2>&1 | Select-Object -Last 2' }
    @{ want = 'DENY';  why = 'pipe to head';            cmd = 'python tools/verify/batch.py prepush | head -5' }
    @{ want = 'DENY';  why = 'pipe to tail';            cmd = 'python tools/verify/check_pov.py | tail -3' }
    @{ want = 'DENY';  why = 'Select-Object -First';    cmd = 'python tools/verify/check_paths.py | Select-Object -First 20' }
    @{ want = 'DENY';  why = 'select alias';            cmd = 'python tools/verify/check_prose.py | select -Last 4' }
    @{ want = 'DENY';  why = 'pipe to grep';            cmd = 'python tools/verify/check_poles.py | grep FAIL' }
    @{ want = 'DENY';  why = 'grep -q swallows all';    cmd = 'python tools/verify/check_modal.py | grep -q PASS' }
    @{ want = 'DENY';  why = 'pipe to Select-String';   cmd = 'python tools/verify/check_poles.py --idioms | Select-String Idiom' }
    @{ want = 'DENY';  why = 'pipe to findstr';         cmd = 'python tools/verify/check_figures.py | findstr ERROR' }
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
    @{ want = 'DENY';  why = 'py launcher still denied';  cmd = 'py tools/verify/check_pov.py | head -3' }
    @{ want = 'DENY';  why = 'python3 still denied';      cmd = 'python3 tools/verify/check_pov.py | grep FAIL' }
    # FLIPPED by the inversion: Select-Object is a filter, not a sink, whatever its flags.
    @{ want = 'DENY';  why = 'Select-Object w/o First (inversion: not a sink)'; cmd = 'python tools/verify/check_figures.py | Select-Object -Property Name' }

    # --- MUST DENY: the consumers the DENYLIST let through (RLY40-1, measured 15 of 19) ---
    @{ want = 'DENY';  why = 'sed -n';                  cmd = 'python tools/verify/check_pov.py | sed -n "1,20p"' }
    @{ want = 'DENY';  why = 'awk';                     cmd = 'python tools/verify/check_pov.py | awk "{print $1}"'; tool = 'Bash' }
    @{ want = 'DENY';  why = 'wc -l';                   cmd = 'python tools/verify/check_pov.py | wc -l' }
    @{ want = 'DENY';  why = 'cut';                     cmd = 'python tools/verify/check_pov.py | cut -c1-40'; tool = 'Bash' }
    @{ want = 'DENY';  why = 'sort -u';                 cmd = 'python tools/verify/check_pov.py | sort -u' }
    @{ want = 'DENY';  why = 'uniq';                    cmd = 'python tools/verify/check_pov.py | uniq'; tool = 'Bash' }
    @{ want = 'DENY';  why = 'less';                    cmd = 'python tools/verify/check_pov.py | less' }
    @{ want = 'DENY';  why = 'ripgrep';                 cmd = 'python tools/verify/check_pov.py | rg FAIL' }
    @{ want = 'DENY';  why = 'ForEach-Object';          cmd = 'python tools/verify/check_pov.py | ForEach-Object { $_ }' }
    @{ want = 'DENY';  why = 'Measure-Object';          cmd = 'python tools/verify/check_pov.py | Measure-Object -Line' }
    @{ want = 'DENY';  why = 'Select-Object -Skip';     cmd = 'python tools/verify/check_pov.py | Select-Object -Skip 10' }
    @{ want = 'DENY';  why = 'Select-Object -Index';    cmd = 'python tools/verify/check_pov.py | Select-Object -Index 0' }
    @{ want = 'DENY';  why = 'a consumer nobody listed'; cmd = 'python tools/verify/check_pov.py | Get-Unique' }
    @{ want = 'DENY';  why = 'sink THEN a filter';      cmd = 'python tools/verify/check_pov.py | Out-String -Stream | Select-String FAIL' }
    @{ want = 'DENY';  why = 'Out-Null discards';       cmd = 'python tools/verify/check_pov.py | Out-Null' }
    @{ want = 'DENY';  why = 'redirect to $null';       cmd = 'python tools/verify/check_pov.py > $null' }
    @{ want = 'DENY';  why = 'redirect to /dev/null';   cmd = 'python tools/verify/check_pov.py > /dev/null 2>&1'; tool = 'Bash' }
    @{ want = 'DENY';  why = 'captured, then cut';      cmd = '$r = python tools/verify/check_pov.py; $r | Select-Object -Last 2' }
    @{ want = 'DENY';  why = 'captured, then indexed';  cmd = '$r = python tools/verify/check_pov.py; $r[0..3]' }
    @{ want = 'DENY';  why = 'group indexed';           cmd = '(python tools/verify/check_pov.py)[0..3]' }
    @{ want = 'DENY';  why = 'subexpression piped';     cmd = 'Write-Output $(python tools/verify/check_pov.py) | head' }
    @{ want = 'DENY';  why = 'script block piped';      cmd = '& { python tools/verify/check_pov.py } | Select-Object -First 1' }
    @{ want = 'DENY';  why = 'bash substitution cut';   cmd = 'echo "$(python tools/verify/check_pov.py | head -3)"'; tool = 'Bash' }
    @{ want = 'DENY';  why = 'tee then grep';           cmd = 'python tools/verify/check_pov.py | tee out.log | grep FAIL'; tool = 'Bash' }
    @{ want = 'DENY';  why = 'tail of the redirect, bash'; cmd = 'python tools/verify/check_pov.py > out.log 2>&1; tail -n 5 out.log'; tool = 'Bash' }
    @{ want = 'DENY';  why = 'grep of the redirect';    cmd = 'python tools/verify/check_pov.py > out.log 2>&1; grep FAIL out.log'; tool = 'Bash' }
    @{ want = 'DENY';  why = 'Select-String of the redirect'; cmd = 'python tools/verify/check_pov.py *> out.log; Select-String -Path out.log -Pattern FAIL' }
    @{ want = 'DENY';  why = 'Out-File then cut the file'; cmd = 'python tools/verify/check_pov.py | Out-File o.log; Get-Content o.log -Tail 3' }
    @{ want = 'DENY';  why = 'powershell -Command quoted'; cmd = 'powershell -NoProfile -Command "python tools/verify/check_pov.py | head -3"' }
    @{ want = 'DENY';  why = 'powershell -File then cut'; cmd = 'powershell -NoProfile -File tools\verify\claude_hooks\test_block_git_gh.ps1 | Select-Object -Last 3' }
    @{ want = 'DENY';  why = 'python -m module';         cmd = 'python -m tools.verify.check_pov | head' }
    @{ want = 'DENY';  why = 'bash -c quoted';           cmd = 'bash -c "python tools/verify/check_pov.py | head"'; tool = 'Bash' }
    @{ want = 'DENY';  why = 'chained after cd';         cmd = 'cd C:\x; python tools/verify/check_pov.py | head' }
    @{ want = 'DENY';  why = 'wrapper the parser skips'; cmd = 'xargs python tools/verify/check_pov.py | head'; tool = 'Bash' }

    # --- MUST ALLOW: the compliant shape and the sinks ------------------------
    @{ want = 'ALLOW'; why = 'redirect and read whole';
       cmd = 'python tools/verify/batch.py precommit > "$sp\pc.log" 2>&1; "EXIT=$LASTEXITCODE"; Get-Content "$sp\pc.log"' }
    @{ want = 'ALLOW'; why = 'run with no pipe at all'; cmd = 'python tools/verify/check_encoding.py BOTTOMELEMENT.md' }
    @{ want = 'ALLOW'; why = 'selftest, read whole';    cmd = 'python tools/verify/check_poles.py --selftest' }
    @{ want = 'ALLOW'; why = 'Out-File is not a cut';   cmd = 'python tools/verify/check_prose.py 2>&1 | Out-File -FilePath x.log -Encoding utf8' }
    @{ want = 'ALLOW'; why = 'Tee-Object is not a cut'; cmd = 'python tools/verify/check_prose.py 2>&1 | Tee-Object -FilePath x.log' }
    @{ want = 'ALLOW'; why = 'Out-String is not a cut'; cmd = 'python tools/verify/check_prose.py | Out-String' }
    @{ want = 'ALLOW'; why = 'bash tee then cat whole'; cmd = 'python tools/verify/check_pov.py 2>&1 | tee out.log; cat out.log'; tool = 'Bash' }
    @{ want = 'ALLOW'; why = 'read whole with -Raw';    cmd = 'python tools/verify/check_pov.py > out.log 2>&1; Get-Content out.log -Raw -Encoding utf8' }
    @{ want = 'ALLOW'; why = 'two checkers, one log';   cmd = 'python tools/verify/check_pov.py > out.log; python tools/verify/check_prose.py >> out.log; Get-Content out.log' }
    @{ want = 'ALLOW'; why = 'captured, used whole';    cmd = '$r = python tools/verify/check_pov.py; $r' }
    @{ want = 'ALLOW'; why = 'pipe INTO a checker';     cmd = 'Get-Content paths.txt | python tools/verify/check_encoding.py --stdin' }

    # --- MUST ALLOW: reading or grepping checker SOURCE is not running it -----
    @{ want = 'ALLOW'; why = 'grep checker source';     cmd = 'grep -n "check_poles" tools/verify/batch.py | head -20' }
    @{ want = 'ALLOW'; why = 'grep TWO checker sources, MEASURED';
       cmd = 'grep -n "SCAN_EXT" tools/verify/check_pov.py tools/verify/check_prose.py | head -20' }
    @{ want = 'ALLOW'; why = 'three sources, no interpreter';
       cmd = 'grep -n html tools/verify/check_poles.py tools/verify/check_modal.py tools/verify/check_figures.py | head' }
    @{ want = 'ALLOW'; why = 'page checker source';     cmd = 'Get-Content tools/verify/check_poles.py | Select-Object -First 40' }
    @{ want = 'ALLOW'; why = 'sed the source';          cmd = 'sed -n "1,60p" tools/verify/check_paths.py' }
    @{ want = 'ALLOW'; why = 'README under verify';     cmd = 'cat tools/verify/README.md | head -30' }

    # --- MUST ALLOW: MENTION, not invocation (RLY40-4) ------------------------
    @{ want = 'ALLOW'; why = 'quoted text names a run';  cmd = 'echo "never pipe python tools/verify/check_pov.py | head"' }
    @{ want = 'ALLOW'; why = 'single-quoted text';       cmd = "Write-Output 'python tools/verify/check_pov.py | Select-Object -Last 2'" }
    @{ want = 'ALLOW'; why = 'a here-string, MEASURED shape';
       cmd = ("@'" + $NL + 'Do not run python tools/verify/check_pov.py | head -5, or | Select-Object -Last 2.' + $NL + "'@ | Set-Content notes.md") }
    @{ want = 'ALLOW'; why = 'a bash heredoc';
       cmd = ("cat > notes.md <<'EOF'" + $NL + 'python tools/verify/check_pov.py | tail -3' + $NL + 'EOF'); tool = 'Bash' }
    @{ want = 'ALLOW'; why = 'a comment';                cmd = ('Get-Date  # python tools/verify/check_pov.py | head') }
    # FLIPPED by the O4 ruling: path matching fails CLOSED. In a command that runs a checker, a
    # row-limited read of ANY file but build.log is denied, because string equality cannot prove a
    # re-spelled path is a different file. Run the unrelated read as its own tool call.
    @{ want = 'DENY';  why = 'limited read of another file beside a checker (O4: fail closed)';
       cmd = 'python tools/verify/check_moved.py --selftest > "$sp\m.log" 2>&1; Get-Content other.txt -TotalCount 5' }
    @{ want = 'ALLOW'; why = 'limited read with NO checker in the command';  cmd = 'Get-Content other.txt -TotalCount 5' }

    # --- B1: bash `|&` is a pipe (stdout AND stderr), not a pipe then a background `&` ---
    # `reason` pins WHICH leg denies: the O4 post-pass also denies these, so without it the B1
    # fix could be reverted and the rows would stay green.
    @{ want = 'DENY';  why = 'B1 |& head';              cmd = 'python tools/verify/check_encoding.py x.md |& head -5'; tool = 'Bash'; reason = '\(\| head\)' }
    @{ want = 'DENY';  why = 'B1 2>&1 |& tail';         cmd = 'python tools/verify/check_encoding.py x.md 2>&1 |& tail -2'; tool = 'Bash'; reason = '\(\| tail\)' }
    @{ want = 'ALLOW'; why = 'B1 |& to a sink';         cmd = 'python tools/verify/check_encoding.py x.md |& tee out.log'; tool = 'Bash' }

    # --- B2: an index or member access on a group that READS tracked output ---
    @{ want = 'DENY';  why = 'B2 (Get-Content log)[-5..-1]'; cmd = 'python tools/verify/check_encoding.py x.md > o.log; (Get-Content o.log)[-5..-1]'; reason = 'index or member access' }
    @{ want = 'DENY';  why = 'B2 ($o)[-1]';             cmd = '$o = python tools/verify/check_encoding.py x.md; ($o)[-1]' }
    @{ want = 'DENY';  why = 'B2 (...).Substring';      cmd = 'python tools/verify/check_encoding.py x.md > o.log; (Get-Content o.log | Out-String).Substring(0,200)'; reason = 'index or member access' }
    @{ want = 'ALLOW'; why = 'B2 whole read in a group'; cmd = 'python tools/verify/check_encoding.py x.md > o.log; (Get-Content o.log -Raw)' }
    @{ want = 'ALLOW'; why = 'B2 indexing with no checker'; cmd = '(Get-Content other.txt)[0]' }

    # --- O4: a re-spelled redirect target still cannot be read row-limited ---
    @{ want = 'DENY';  why = 'O4 differently-cased log';   cmd = 'python tools/verify/check_encoding.py x.md > o.log; Get-Content O.LOG -Tail 3' }
    @{ want = 'DENY';  why = 'O4 wildcard spelling';       cmd = 'python tools/verify/check_encoding.py x.md > o.log; Get-Content o.lo? -Tail 3' }
    @{ want = 'DENY';  why = 'O4 absolute spelling';       cmd = 'python tools/verify/check_encoding.py x.md > "$sp\o.log"; Get-Content C:\sp\o.log -Tail 3' }
    @{ want = 'DENY';  why = 'O4 Select-Object -Last on a re-spelling'; cmd = 'python tools/verify/check_encoding.py x.md > o.log; Get-Content .\o.lo* | Select-Object -Last 3' }

    # --- MUST ALLOW: build.log, which has a hook REQUIRING a row limit --------
    @{ want = 'ALLOW'; why = 'build.log limited read';
       cmd = 'python tools/verify/batch.py precommit; Get-Content build.log -Tail 50' }
    @{ want = 'ALLOW'; why = 'build.log TotalCount';
       cmd = 'python tools/verify/check_figures.py; Get-Content build.log -TotalCount 100' }
    @{ want = 'DENY';  why = 'build.log written BY the checker, then cut';
       cmd = 'python tools/verify/check_figures.py > build.log 2>&1; Get-Content build.log -Tail 5' }

    # --- MUST ALLOW: nothing under tools/verify is being run ------------------
    @{ want = 'ALLOW'; why = 'unrelated pipeline';      cmd = 'Get-ChildItem scripts | Select-Object -First 5' }
    @{ want = 'ALLOW'; why = 'a scratchpad probe';      cmd = 'python "$sp\probe_poles.py" | head -5' }
    @{ want = 'ALLOW'; why = 'a build script';          cmd = 'python scripts/build_zpi.py | tail -20' }

    # --- FAIL-CLOSED: the tokeniser cannot read it, and a checker is named ----
    @{ want = 'DENY';  why = 'unbalanced quote near a checker'; cmd = 'python tools/verify/check_pov.py "unterminated | head' }
)

$script:fails = 0; $script:total = 0
function Report([bool]$ok, [string]$want, $res, [string]$why) {
    $script:total++
    if (-not $ok) { $script:fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    $note = if ($res.Why) { "  [$($res.Why)]" } else { '' }
    "{0}  want={1,-5} got={2,-5}  {3}{4}" -f $mark, $want, $res.Verdict, $why, $note | Write-Host
}

foreach ($c in $cases) {
    $tool = if ($c.tool) { $c.tool } else { 'PowerShell' }
    $res = Invoke-HookScript $hook (New-Payload $c.cmd $tool)
    $ok = ($res.Verdict -eq $c.want)
    # A DENY must be THIS hook's truncation deny, not some other refusal sharing the exit shape.
    if ($ok -and $c.want -eq 'DENY' -and $res.Reason -notmatch 'BLOCKED: this command runs a checker') { $ok = $false; $res.Why = 'deny text is not the truncation refusal' }
    if ($ok -and $c.reason -and $res.Reason -notmatch $c.reason) { $ok = $false; $res.Why = "denied by another leg, not '$($c.reason)'" }
    Report $ok $c.want $res $c.why
}

# --- fail-closed controls: the hook must DENY when it cannot tell -------------
$bad = @(
    @{ why = 'empty stdin';          p = '' }
    @{ why = 'malformed json';       p = '{not json' }
    @{ why = 'no command field';     p = '{"tool_name":"PowerShell","tool_input":{"description":"x"}}' }
    @{ why = 'command is an array';  p = '{"tool_name":"PowerShell","tool_input":{"command":["a"]}}' }
    # O8: a throw inside the analysis must DENY. Injected through the hook's test seam, because no
    # natural input is known to make the analysis throw.
    @{ why = 'analysis throws (test seam)'; p = '{"tool_name":"PowerShell","tool_input":{"command":"python tools/verify/check_pov.py","zp_selftest_throw":1}}' }
)
foreach ($b in $bad) {
    $res = Invoke-HookScript $hook $b.p
    Report ($res.Verdict -eq 'DENY' -and $res.Reason -match 'fail-closed') 'DENY' $res ("fail-closed: " + $b.why)
}

Remove-Item -LiteralPath $tmpDir -Recurse -Force -ErrorAction SilentlyContinue
""
if ($script:fails -eq 0) { "ALL {0} CONTROLS BEHAVED" -f $script:total | Write-Host; exit 0 }
"{0} of {1} CONTROL(S) MISBEHAVED" -f $script:fails, $script:total | Write-Host
exit 1
