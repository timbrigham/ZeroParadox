# test_require_search_record_in_questions.ps1 - the control for require_search_record_in_questions.ps1.
#
# Every row prints, pass or fail. Must-DENY rows reproduce the P2-RELAY-1 shape and its siblings;
# must-ALLOW rows pin the false-positive surface (ordinary options, pointers, a present search record,
# and words that merely CONTAIN a vocabulary token). ERROR is a third verdict, never folded into
# ALLOW (R-ZERONULL).
#
# Run:  powershell -NoProfile -File tools\verify\claude_hooks\test_require_search_record_in_questions.ps1 [-HookPath <copy>]
#       -HookPath runs the rows against another copy of the hook (mutation check).
# Exit: 0 every control behaved; 1 at least one misbehaved.

param([string]$HookPath = '')

$ErrorActionPreference = 'Stop'
$hook = if ($HookPath) { $HookPath } else { Join-Path $PSScriptRoot 'require_search_record_in_questions.ps1' }
if (-not (Test-Path -LiteralPath $hook)) { Write-Host "MISSING: $hook"; exit 1 }

$tmpDir = Join-Path ([IO.Path]::GetTempPath()) ("hookctl_q_" + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $tmpDir -Force | Out-Null
$utf8 = New-Object Text.UTF8Encoding($false)

function Invoke-Hook([string]$Payload) {
    $inFile  = Join-Path $tmpDir ("in_"  + [guid]::NewGuid().ToString('N') + '.json')
    $outFile = Join-Path $tmpDir ("out_" + [guid]::NewGuid().ToString('N') + '.txt')
    $errFile = Join-Path $tmpDir ("err_" + [guid]::NewGuid().ToString('N') + '.txt')
    [IO.File]::WriteAllText($inFile, $Payload, $utf8)
    $p = Start-Process -FilePath 'powershell.exe' -ArgumentList @('-NoProfile', '-File', $hook) `
        -RedirectStandardInput $inFile -RedirectStandardOutput $outFile -RedirectStandardError $errFile `
        -NoNewWindow -PassThru -Wait
    $stdout = if (Test-Path -LiteralPath $outFile) { [IO.File]::ReadAllText($outFile) } else { '' }
    if ($p.ExitCode -ne 0) { return "ERROR(exit $($p.ExitCode))" }
    if ([string]::IsNullOrWhiteSpace($stdout)) { return 'ALLOW' }
    try { $obj = $stdout | ConvertFrom-Json } catch { return 'ERROR(not json)' }
    $d = $obj.hookSpecificOutput.permissionDecision
    if ("$d" -eq 'deny') { return 'DENY' }
    if ("$d" -eq 'allow') { return 'ALLOW' }
    return "ERROR(decision '$d')"
}

function New-Q([string]$question, [object[]]$options) {
    $opts = @($options | ForEach-Object { @{ label = $_[0]; description = $_[1] } })
    $payload = @{ tool_name = 'AskUserQuestion'
                  tool_input = @{ questions = @(@{ question = $question; header = 'h'; multiSelect = $false; options = $opts }) } }
    return ($payload | ConvertTo-Json -Depth 8 -Compress)
}

$rows = @(
    # --- must DENY: the incident and its siblings ---
    @{ Id = 'Q01'; Want = 'DENY'; Why = 'the P2-RELAY-1 option, verbatim shape'
       P = (New-Q 'MODALW-14: what should ZP-F say?' @(@('Measure it first', 'R-REVALIDATE: AX-B1 selection of p = 2 is unmeasured; try to state it in Lean.'), @('Delete the clause', 'Drop it.'))) }
    @{ Id = 'Q02'; Want = 'DENY'; Why = 'absence in the QUESTION text'
       P = (New-Q 'Nothing proved derives p = 2 from AX-B1. What now?' @(@('A', 'one'), @('B', 'two'))) }
    @{ Id = 'Q03'; Want = 'DENY'; Why = 'not located'
       P = (New-Q 'Which?' @(@('Cite it', 'A choice-free leastness proof is not located; say so.'), @('B', 'two'))) }
    @{ Id = 'Q04'; Want = 'DENY'; Why = 'remains open'
       P = (New-Q 'Which?' @(@('Keep', 'The bridge remains open, so keep the sentence.'), @('B', 'two'))) }
    @{ Id = 'Q05'; Want = 'DENY'; Why = 'no theorem ... ties'
       P = (New-Q 'Which?' @(@('Restate', 'No theorem in the corpus ties the two states to p = 2.'), @('B', 'two'))) }
    @{ Id = 'Q06'; Want = 'DENY'; Why = 'not in Mathlib'
       P = (New-Q 'Which?' @(@('Build it', 'This lemma is not in Mathlib, so we write it.'), @('B', 'two'))) }
    @{ Id = 'Q07'; Want = 'DENY'; Why = 'search record in ANOTHER option does not cover this one'
       P = (New-Q 'Which?' @(@('A', 'It is unproved.'), @('B', 'searched: check_paths --claim "x", 0 hits'))) }
    # --- must ALLOW ---
    @{ Id = 'Q20'; Want = 'ALLOW'; Why = 'ordinary options, no absence wording'
       P = (New-Q 'Which ZP-F batch shape?' @(@('Next batch', 'After the push.'), @('Fold in now', 'Restart the gates.'))) }
    @{ Id = 'Q21'; Want = 'ALLOW'; Why = 'absence wording WITH a search record in the same option'
       P = (New-Q 'Which?' @(@('Say so', 'Not located as of 2026-10-17, searched: check_paths --claim "least fixed point", 0 hits in ZeroParadox/**.'), @('B', 'two'))) }
    @{ Id = 'Q22'; Want = 'ALLOW'; Why = 'a POINTER instead of an absence (the preferred fix)'
       P = (New-Q 'MODALW-14: what should ZP-F say?' @(@('Point at T0', 'One line: p = 2 is fixed by ZP-B T0 (ZeroParadox/Valuation/Padic.lean) from AX-B1 and MP-1.'), @('B', 'two'))) }
    @{ Id = 'Q23'; Want = 'ALLOW'; Why = 'word boundaries: opened / reopened / absentee are not hits'
       P = (New-Q 'The PR was opened; reopened later?' @(@('A', 'An absentee reviewer; openly stated.'), @('B', 'two'))) }
    @{ Id = 'Q24'; Want = 'ALLOW'; Why = 'search record keyword is case-insensitive'
       P = (New-Q 'Which?' @(@('A', 'Unmeasured. Searched: grep ZeroParadox/**/*.lean for t0_, 3 hits.'), @('B', 'two'))) }
    # --- fail closed ---
    @{ Id = 'Q90'; Want = 'DENY'; Why = 'empty stdin'; P = '' }
    @{ Id = 'Q91'; Want = 'DENY'; Why = 'unparseable stdin'; P = '{not json' }
    @{ Id = 'Q92'; Want = 'DENY'; Why = 'no questions array'; P = '{"tool_name":"AskUserQuestion","tool_input":{}}' }
)

$bad = 0
foreach ($r in $rows) {
    $got = Invoke-Hook $r.P
    $ok = ($got -eq $r.Want)
    if (-not $ok) { $bad++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    Write-Host ("{0} {1}  want {2,-5} got {3,-12} {4}" -f $mark, $r.Id, $r.Want, $got, $r.Why)
}
Remove-Item -LiteralPath $tmpDir -Recurse -Force -ErrorAction SilentlyContinue
if ($bad -eq 0) { Write-Host "ALL $($rows.Count) CONTROLS BEHAVED"; exit 0 }
Write-Host "$bad OF $($rows.Count) CONTROLS MISBEHAVED"; exit 1
