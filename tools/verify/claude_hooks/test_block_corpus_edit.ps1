# test_block_corpus_edit.ps1 - the control for block_corpus_edit.ps1.
#
# WHY THIS FILE EXISTS. Its sibling's header records the lesson: the git hook's 21 original
# controls were run by hand and written down nowhere, so the next change to it had nothing to
# regress against. A control that exists only in a transcript is not a control.
#
# THE CONTROL THAT MATTERS MOST IS THE WORKTREE ROW. This guard's entire design claim is that
# delegation passes automatically because a worktree lives OUTSIDE the checkout. If that row ever
# goes DENY, delegation is blocked and the guard has inverted its own purpose - it would be denying
# the behaviour it exists to require. Treat a failure there as a stop, not as a tuning problem.
#
# Run:  powershell -File tools\verify\claude_hooks\test_block_corpus_edit.ps1
# Exit: 0 all controls behaved, 1 otherwise. Prints every row, pass or fail.

$ErrorActionPreference = 'Stop'
$hook = Join-Path $PSScriptRoot 'block_corpus_edit.ps1'
if (-not (Test-Path $hook)) { Write-Host "MISSING: $hook"; exit 1 }

$repo = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path.TrimEnd('\')

function Invoke-Hook([string]$tool, [string]$key, [string]$path, [string]$cwd) {
    $ti = @{}
    $ti[$key] = $path
    $body = @{ tool_name = $tool; tool_input = $ti }
    if ($cwd) { $body['cwd'] = $cwd }
    $payload = $body | ConvertTo-Json -Compress -Depth 5
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
    # --- MUST DENY: the corpus and the published surfaces, in the shared checkout ---
    @{ want='DENY';  why='Lean corpus, Edit';        tool='Edit';  key='file_path'; path="$repo\ZeroParadox\Computability\Kleene.lean" }
    @{ want='DENY';  why='Lean index, Write';        tool='Write'; key='file_path'; path="$repo\ZeroParadox\BottomCannotBe.lean" }
    @{ want='DENY';  why='PDF build script';         tool='Edit';  key='file_path'; path="$repo\scripts\build_zpk.py" }
    @{ want='DENY';  why='root README';              tool='Edit';  key='file_path'; path="$repo\README.md" }
    @{ want='DENY';  why='the canonical register';   tool='Edit';  key='file_path'; path="$repo\register.md" }
    @{ want='DENY';  why='a rendered PDF';           tool='Write'; key='file_path'; path="$repo\ZP-K_Computational_Grounding.pdf" }
    @{ want='DENY';  why='published gate brief';     tool='Edit';  key='file_path'; path="$repo\.claude\commands\adversary-review.md" }
    @{ want='DENY';  why='notebook in the corpus';   tool='NotebookEdit'; key='notebook_path'; path="$repo\ZeroParadox\probe.ipynb" }

    # --- MUST DENY: the same targets wearing a different spelling ------------------
    @{ want='DENY';  why='file that does not exist yet'; tool='Write'; key='file_path'; path="$repo\ZeroParadox\Brand\New.lean" }
    @{ want='DENY';  why='forward slashes';          tool='Edit';  key='file_path'; path="$($repo -replace '\\','/')/scripts/build_zpl.py" }
    @{ want='DENY';  why='traversal through tools';  tool='Edit';  key='file_path'; path="$repo\tools\..\scripts\build_zpk.py" }
    @{ want='DENY';  why='case-insensitive';         tool='Edit';  key='file_path'; path="$repo\SCRIPTS\BUILD_ZPK.PY" }
    @{ want='DENY';  why='relative, cwd=repo root';  tool='Edit';  key='file_path'; path='scripts/build_zpm.py'; cwd=$repo }

    # --- MUST ALLOW: the worktree route. THE LOAD-BEARING ROW. --------------------
    @{ want='ALLOW'; why='WORKTREE outside the repo'; tool='Edit'; key='file_path'; path='C:\Users\timbr\AppData\Local\Temp\gitrobot-worktrees\zp-a1b2\ZeroParadox\Computability\Kleene.lean' }
    @{ want='ALLOW'; why='WORKTREE build script';     tool='Edit'; key='file_path'; path='C:\Users\timbr\AppData\Local\Temp\gitrobot-worktrees\zp-a1b2\scripts\build_zpk.py' }
    @{ want='ALLOW'; why='session scratchpad';        tool='Write'; key='file_path'; path='C:\Users\timbr\AppData\Local\Temp\claude\scratchpad\probe.lean' }

    # --- MUST ALLOW: what Tim ruled stays the main instance's ---------------------
    @{ want='ALLOW'; why='.claude-local note';       tool='Write'; key='file_path'; path="$repo\.claude-local\notes\x_2026-09-19.md" }
    @{ want='ALLOW'; why='.claude-local queue';      tool='Write'; key='file_path'; path="$repo\.claude-local\queue\x.md" }
    @{ want='ALLOW'; why='.claude-local DEFECTS';    tool='Edit';  key='file_path'; path="$repo\.claude-local\DEFECTS.md" }
    @{ want='ALLOW'; why='a checker under tools/';   tool='Edit';  key='file_path'; path="$repo\tools\verify\batch.py" }
    @{ want='ALLOW'; why='this hook itself';         tool='Edit';  key='file_path'; path="$repo\tools\verify\claude_hooks\block_corpus_edit.ps1" }
    @{ want='ALLOW'; why='CLAUDE.md (scope ruling)'; tool='Edit';  key='file_path'; path="$repo\CLAUDE.md" }

    # --- MUST ALLOW: nothing to inspect -------------------------------------------
    @{ want='ALLOW'; why='no path in tool_input';    tool='Bash';  key='command';   path='echo hello' }
)

$fails = 0
foreach ($c in $cases) {
    $got = Invoke-Hook $c.tool $c.key $c.path $c.cwd
    $ok  = ($got -eq $c.want)
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  want={1,-5} got={2,-5}  {3}" -f $mark, $c.want, $got, $c.why | Write-Host
}

# --- fail-closed controls: the hook must DENY when it cannot tell ----------------
$closed = @(
    @{ why = 'empty stdin';    p = '' }
    @{ why = 'malformed json'; p = '{not json' }
)
foreach ($bad in $closed) {
    $got = Invoke-HookRaw $bad.p
    $ok = ($got -eq 'DENY')
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  want=DENY  got={1,-5}  fail-closed: {2}" -f $mark, $got, $bad.why | Write-Host
}

""
$total = $cases.Count + $closed.Count
if ($fails -eq 0) { "ALL {0} CONTROLS BEHAVED" -f $total | Write-Host; exit 0 }
"{0} of {1} CONTROL(S) MISBEHAVED" -f $fails, $total | Write-Host
exit 1
