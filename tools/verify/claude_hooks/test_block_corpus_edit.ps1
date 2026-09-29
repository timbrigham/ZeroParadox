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
# ** THE SECOND-MOST IMPORTANT ROW IS `unclassified new file at the root`. ** The guard is now
# DENY-BY-DEFAULT inside the checkout (GUARD-2), and that row is the only one that tests the
# DEFAULT rather than a name somebody remembered to list. Every other DENY row here would still
# pass under a glob list; that one goes red the moment the default flips back to allow. It is the
# class control, and the reason the other rows are not merely a longer hole-list.
#
# ** THE THIRD IS `SIBLING dir extending the root name`, AND IT WAS ADDED BECAUSE IT WAS MISSING. **
# The containment test is a string prefix PLUS a separator, and the separator is the whole
# difference between `...\ZeroParadox\` and a sibling directory called `...\ZeroParadox-scratch\`.
# Measured 2026-09-20: dropping it applies cleanly, resolves correctly, and left this suite fully
# green at exit 0 - 68 rows, every one behaving, over a hook that had lost its containment
# boundary. The failure is an OVER-block rather than a leak, so it is ORDINARY, and it is pinned
# anyway: an unpinned mutation leaves the next edit to that line with nothing to regress against,
# which is the whole reason this file exists.
#
# ** MUTATION CONTROLS VERIFY THAT THE MUTATION APPLIED, BEFORE READING THE RESULT. ** A /rely
# reviewer reported ALL 25 CONTROLS BEHAVED over a hook it believed it had neutered: its own
# `-replace` had silently failed to match, so it measured an unperturbed system and read it as a
# pass. Every mutation below compares the SHA-256 of the mutated copy against the original and
# reports FAIL - not pass - when the hash did not move.
#
# Run:  powershell -File tools\verify\claude_hooks\test_block_corpus_edit.ps1
# Exit: 0 all controls behaved, 1 otherwise. Prints every row, pass or fail.

$ErrorActionPreference = 'Stop'
$hook = Join-Path $PSScriptRoot 'block_corpus_edit.ps1'
if (-not (Test-Path $hook)) { Write-Host "MISSING: $hook"; exit 1 }

$repo = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path.TrimEnd('\')
$drive = $repo.Substring(0, 1)
$afterDrive = $repo.Substring(3)

function Invoke-HookRawAt([string]$hookPath, [string]$payload) {
    $out = $payload | powershell -NoProfile -File $hookPath 2>&1 | Out-String
    if ($out -match '"permissionDecision"\s*:\s*"deny"') { return 'DENY' }
    return 'ALLOW'
}

function Get-Payload([string]$tool, [string]$key, [string]$path, [string]$cwd) {
    $ti = @{}
    $ti[$key] = $path
    $body = @{ tool_name = $tool; tool_input = $ti }
    if ($cwd) { $body['cwd'] = $cwd }
    return ($body | ConvertTo-Json -Compress -Depth 5)
}

function Invoke-Hook([string]$tool, [string]$key, [string]$path, [string]$cwd) {
    return Invoke-HookRawAt $hook (Get-Payload $tool $key $path $cwd)
}

function Invoke-HookRaw([string]$payload) { return Invoke-HookRawAt $hook $payload }

# Returns the refusal TEXT, so a control can pin WHICH surface the hook says it stopped. The
# classifier decides nothing, but its nouns are claims, and a claim gets a control.
function Get-HookReason([string]$path) {
    $out = (Get-Payload 'Edit' 'file_path' $path $null) | powershell -NoProfile -File $hook 2>&1 | Out-String
    return $out
}

$cases = @(
    # --- MUST DENY: the corpus and the published surfaces, in the shared checkout ---
    @{ want='DENY';  why='Lean corpus, Edit';        tool='Edit';  key='file_path'; path="$repo\ZeroParadox\Computability\Kleene.lean" }
    @{ want='DENY';  why='Lean index, Write';        tool='Write'; key='file_path'; path="$repo\ZeroParadox\BottomCannotBe.lean" }
    @{ want='DENY';  why='LEAN LIBRARY ROOT MODULE'; tool='Edit';  key='file_path'; path="$repo\ZeroParadox.lean" }
    @{ want='DENY';  why='PDF build script';         tool='Edit';  key='file_path'; path="$repo\scripts\build_zpk.py" }
    @{ want='DENY';  why='root README';              tool='Edit';  key='file_path'; path="$repo\README.md" }
    @{ want='DENY';  why='the canonical register';   tool='Edit';  key='file_path'; path="$repo\register.md" }
    @{ want='DENY';  why='a rendered PDF';           tool='Write'; key='file_path'; path="$repo\ZP-K_Computational_Grounding.pdf" }
    @{ want='DENY';  why='published gate brief';     tool='Edit';  key='file_path'; path="$repo\.claude\commands\adversary-review.md" }
    @{ want='DENY';  why='notebook in the corpus';   tool='NotebookEdit'; key='notebook_path'; path="$repo\ZeroParadox\probe.ipynb" }

    # --- MUST DENY: the published site. Same reader, same domain, and all six were ALLOWED -----
    # until 2026-09-20. `README.md` was denied while `bottom-family-tree.html` beside it was not.
    @{ want='DENY';  why='published page (family tree)'; tool='Edit'; key='file_path'; path="$repo\bottom-family-tree.html" }
    @{ want='DENY';  why='published page (diagonal)';    tool='Edit'; key='file_path'; path="$repo\diagonal-family.html" }
    @{ want='DENY';  why='published page (snap loop)';   tool='Edit'; key='file_path'; path="$repo\snap-loop.html" }
    @{ want='DENY';  why='LAYOUT wrapping every page';   tool='Edit'; key='file_path'; path="$repo\_layouts\default.html" }
    @{ want='DENY';  why='site configuration';           tool='Edit'; key='file_path'; path="$repo\_config.yml" }
    @{ want='DENY';  why='the published domain';         tool='Write';key='file_path'; path="$repo\CNAME" }
    @{ want='DENY';  why='the permanent DOI record';     tool='Edit'; key='file_path'; path="$repo\.zenodo.json" }
    @{ want='DENY';  why='the published licence';        tool='Edit'; key='file_path'; path="$repo\LICENSE" }

    # --- MUST DENY: machinery that decides what the corpus MEANS or what ships ----------------
    @{ want='DENY';  why="the guard's own registration"; tool='Edit'; key='file_path'; path="$repo\.claude\settings.json" }
    @{ want='DENY';  why='the lake build pin';           tool='Edit'; key='file_path'; path="$repo\lakefile.toml" }
    @{ want='DENY';  why='the toolchain pin';            tool='Edit'; key='file_path'; path="$repo\lean-toolchain" }
    @{ want='DENY';  why='the lake manifest';            tool='Edit'; key='file_path'; path="$repo\lake-manifest.json" }
    @{ want='DENY';  why='release automation';           tool='Edit'; key='file_path'; path="$repo\.github\workflows\create-release.yml" }
    @{ want='DENY';  why='generated registry (ssot)';    tool='Edit'; key='file_path'; path="$repo\ssot.json" }
    @{ want='DENY';  why='gate_round.json, not editable';tool='Edit'; key='file_path'; path="$repo\gate_round.json" }
    @{ want='DENY';  why='repo mechanics (.gitignore)';  tool='Edit'; key='file_path'; path="$repo\.gitignore" }

    # --- MUST DENY: THE DEFAULT ITSELF. The class control - no glob names these. --------------
    @{ want='DENY';  why='UNCLASSIFIED new file at root';    tool='Write'; key='file_path'; path="$repo\some-future-surface.xyz" }
    @{ want='DENY';  why='UNCLASSIFIED new top-level dir';   tool='Write'; key='file_path'; path="$repo\newsurface\index.txt" }

    # --- MUST DENY: the same targets wearing a different spelling ------------------
    @{ want='DENY';  why='file that does not exist yet'; tool='Write'; key='file_path'; path="$repo\ZeroParadox\Brand\New.lean" }
    @{ want='DENY';  why='forward slashes';          tool='Edit';  key='file_path'; path="$($repo -replace '\\','/')/scripts/build_zpl.py" }
    @{ want='DENY';  why='traversal through tools';  tool='Edit';  key='file_path'; path="$repo\tools\..\scripts\build_zpk.py" }
    @{ want='DENY';  why='case-insensitive';         tool='Edit';  key='file_path'; path="$repo\SCRIPTS\BUILD_ZPK.PY" }
    @{ want='DENY';  why='relative, cwd=repo root';  tool='Edit';  key='file_path'; path='scripts/build_zpm.py'; cwd=$repo }

    # --- MUST DENY: the five spellings GUARD-2 measured. All five ALLOWED until 2026-09-20. ---
    # `GetFullPath` preserves a device prefix by design, so the repo-root prefix test never
    # matched and the path fell out of the guard as "outside the checkout".
    @{ want='DENY';  why='device prefix \\?\';       tool='Edit';  key='file_path'; path="\\?\$drive`:\$afterDrive\ZeroParadox\Computability\Kleene.lean" }
    @{ want='DENY';  why='device prefix //?/';       tool='Edit';  key='file_path'; path="//?/$drive`:/$($afterDrive -replace '\\','/')/ZeroParadox/Computability/Kleene.lean" }
    @{ want='DENY';  why='loopback UNC localhost';   tool='Edit';  key='file_path'; path="\\localhost\$drive`$\$afterDrive\ZeroParadox\Computability\Kleene.lean" }
    @{ want='DENY';  why='loopback UNC 127.0.0.1';   tool='Edit';  key='file_path'; path="\\127.0.0.1\$drive`$\$afterDrive\ZeroParadox\Computability\Kleene.lean" }
    @{ want='DENY';  why='device prefix \\.\C:';     tool='Edit';  key='file_path'; path="\\.\$drive`:\$afterDrive\ZeroParadox\Computability\Kleene.lean" }
    @{ want='DENY';  why='device prefix, no-normalise traversal'; tool='Edit'; key='file_path'; path="\\?\$drive`:\$afterDrive\tools\..\scripts\build_zpk.py" }

    # --- MUST ALLOW: the worktree route. THE LOAD-BEARING ROW. --------------------
    @{ want='ALLOW'; why='WORKTREE outside the repo'; tool='Edit'; key='file_path'; path='C:\Users\timbr\AppData\Local\Temp\gitrobot-worktrees\zp-a1b2\ZeroParadox\Computability\Kleene.lean' }
    @{ want='ALLOW'; why='WORKTREE build script';     tool='Edit'; key='file_path'; path='C:\Users\timbr\AppData\Local\Temp\gitrobot-worktrees\zp-a1b2\scripts\build_zpk.py' }
    @{ want='ALLOW'; why='WORKTREE via \\?\ prefix';  tool='Edit'; key='file_path'; path='\\?\C:\Users\timbr\AppData\Local\Temp\gitrobot-worktrees\zp-a1b2\scripts\build_zpk.py' }
    @{ want='ALLOW'; why='session scratchpad';        tool='Write'; key='file_path'; path='C:\Users\timbr\AppData\Local\Temp\claude\scratchpad\probe.lean' }
    # A UNC path to a DIFFERENT host is a different machine, not this checkout. Normalising it into
    # a local drive letter would be a fabrication, so it must pass straight through.
    @{ want='ALLOW'; why='UNC to another host';       tool='Edit'; key='file_path'; path='\\fileserver\share\ZeroParadox\Computability\Kleene.lean' }

    # ** THE CONTAINMENT BOUNDARY ITSELF. ** A sibling directory whose name merely EXTENDS the repo
    # root's is outside the checkout, and only the trailing separator in the StartsWith test says
    # so. Drop it and this row flips to DENY while every other row stays green - see the mutation
    # of the same name at the bottom of this file, which is this row's proof of teeth.
    @{ want='ALLOW'; why='SIBLING dir extending the root name'; tool='Write'; key='file_path'; path="${repo}-scratch\notes.md" }

    # --- MUST ALLOW: what Tim ruled stays the main instance's. THIS IS THE WHOLE LIST. --------
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

# --- BOTH path keys are judged, not just the first present -----------------------
# GUARD-3: "a `notebook_path` corpus payload carrying a benign `file_path` is judged on the benign
# one". The fallback was `file_path` OR `notebook_path`; it is now BOTH.
$bothKeys = @(
    @{ why='corpus notebook_path beside a benign file_path'
       p = (@{ tool_name='NotebookEdit'
               tool_input=@{ file_path="$repo\tools\verify\batch.py"
                             notebook_path="$repo\ZeroParadox\probe.ipynb" } } | ConvertTo-Json -Compress -Depth 5) }
    @{ why='corpus file_path beside a benign notebook_path'
       p = (@{ tool_name='Edit'
               tool_input=@{ file_path="$repo\README.md"
                             notebook_path="$repo\.claude-local\x.ipynb" } } | ConvertTo-Json -Compress -Depth 5) }
)
foreach ($b in $bothKeys) {
    $got = Invoke-HookRaw $b.p
    $ok = ($got -eq 'DENY')
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  want=DENY  got={1,-5}  both-keys: {2}" -f $mark, $got, $b.why | Write-Host
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

# --- the 8.3 short name. PINNING A BEHAVIOUR WE GET FOR FREE AND DID NOT DESIGN. ------------
# `GetFullPath` on .NET Framework expands a short component when the path exists, so this route is
# closed without the hook doing anything about it. The header's first draft said it was open, from
# reading the code; running it said DENY. A behaviour nobody implemented is exactly the one a
# runtime change can take away silently, so it gets a row.
# The row is SKIPPED, not passed, where the repo root has no distinct short form - `n/a` is a third
# value, and it is not counted in the total. A skip that prints as a pass is the defect this is
# avoiding.
$extra = 0
$shortRepo = $null
try {
    $shortRepo = (New-Object -ComObject Scripting.FileSystemObject).GetFolder($repo).ShortPath
} catch { $shortRepo = $null }
if ($shortRepo -and $shortRepo -ne $repo) {
    $got = Invoke-Hook 'Edit' 'file_path' "$shortRepo\ZeroParadox\Computability\Kleene.lean" $null
    $ok = ($got -eq 'DENY')
    if (-not $ok) { $fails++ }
    $extra++
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  want=DENY  got={1,-5}  8.3 short name: {2}" -f $mark, $got, $shortRepo | Write-Host
} else {
    "n/a   8.3 short name: this repo root has no distinct short form ({0}) - row not counted" -f $repo | Write-Host
}

# --- the refusal NAMES the surface. The classifier decides nothing, but it CLAIMS. ----------
# The root-module row is the one that motivated this: `^ZeroParadox\` required a separator, so the
# directory matched and `ZeroParadox.lean` beside it did not. A bare `^ZeroParadox` would be the
# mirror-image bug, catching any future sibling whose name merely starts with the word, so the
# pattern admits exactly the directory and exactly the module - and the negative row pins that.
$naming = @(
    @{ why='root module is named as the corpus'; path="$repo\ZeroParadox.lean";        expect='the Lean corpus' }
    @{ why='corpus directory, same noun';        path="$repo\ZeroParadox\Order\Snap.lean"; expect='the Lean corpus' }
    # The default noun names the CLASSIFIER's state, not the file's. It used to say "a tracked
    # surface of this checkout" - untrue of the commonest case that reaches it, a `Write` to a
    # path that does not exist yet and so is untracked by construction.
    @{ why='a sibling that merely starts with the word is NOT the corpus'
       path="$repo\ZeroParadoxNotes.txt";        expect='an unclassified file' }
    @{ why='an UNTRACKED new file is not called tracked'
       path="$repo\some-future-surface.xyz";     expect='an unclassified file' }
    @{ why='published page names the page';      path="$repo\snap-loop.html";          expect='a published web page' }
    @{ why='DOI record names the DOI record';    path="$repo\.zenodo.json";            expect='the permanent DOI record' }
)
foreach ($n in $naming) {
    $reason = Get-HookReason $n.path
    $ok = $reason.Contains($n.expect)
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  names='{1}'  {2}" -f $mark, $n.expect, $n.why | Write-Host
}

# ================================================================================================
# MUTATION CONTROLS. A suite that cannot go red is measuring the wrong object (GUARD-3).
# ** EACH ONE PROVES THE MUTATION APPLIED BEFORE IT READS THE RESULT. ** The /rely reviewer that
# printed ALL 25 CONTROLS BEHAVED over a hook it thought it had neutered had a `-replace` that
# silently failed to match; it measured an unperturbed system. `.Replace()` is used rather than
# `-replace` so the search text is LITERAL, and the SHA-256 is compared either way.
#
# ** AND THE HARNESS MUST MIRROR THE DIRECTORY DEPTH, WHICH IS ITS OWN MEASURED DEFECT. ** The
# first version of this section dropped the copies into a flat temp directory. The hook derives
# its repo root as `$PSScriptRoot\..\..\..`, so from `%TEMP%\zp-guard-mut-x\` that root resolved to
# `C:\Users\timbr\AppData` - and every probe path, the gitrobot worktrees included, then sat
# "inside the checkout". Three of the four mutations went green anyway, on a relative path that was
# nonsense, and the fourth went red for a reason that had nothing to do with the mutation. A
# hash-verified mutation still measures the wrong object if the copy is planted at the wrong depth.
# So the copies live in a SYNTHETIC REPO ROOT laid out exactly like this one, and the first control
# below proves that root resolved where it was meant to, before any mutation is read.
# ================================================================================================
""
$src = Get-Content $hook -Raw
$mutRepo = Join-Path ([System.IO.Path]::GetTempPath()) ("zp-guard-mut-" + [guid]::NewGuid().ToString('N').Substring(0, 8))
$mutDir  = Join-Path $mutRepo 'tools\verify\claude_hooks'
New-Item -ItemType Directory -Path $mutDir -Force | Out-Null

function Get-Sha([string]$path) { return (Get-FileHash -Algorithm SHA256 -Path $path).Hash }

$baseCopy = Join-Path $mutDir 'base.ps1'
Set-Content -Path $baseCopy -Value $src -Encoding UTF8 -NoNewline
$baseSha = Get-Sha $baseCopy

# INSTRUMENT CHECK, before anything is concluded from a mutation. An unmutated copy planted in the
# synthetic root must deny that root's corpus and allow that root's tools/ - which is only true if
# `$PSScriptRoot\..\..\..` landed on $mutRepo. If this row fails, every mutation row below is
# measuring some ancestor directory and none of their verdicts mean anything.
$instr = @(
    @{ why='synthetic root: its corpus is denied'; p="$mutRepo\ZeroParadox\Computability\Kleene.lean"; want='DENY' }
    @{ why='synthetic root: its tools/ is allowed'; p="$mutRepo\tools\verify\batch.py";                want='ALLOW' }
    @{ why='synthetic root: a real worktree is still outside it'
       p='C:\Users\timbr\AppData\Local\Temp\gitrobot-worktrees\zp-a1b2\ZeroParadox\X.lean';            want='ALLOW' }
)
foreach ($i in $instr) {
    $got = Invoke-HookRawAt $baseCopy (Get-Payload 'Edit' 'file_path' $i.p $null)
    $ok = ($got -eq $i.want)
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  want={1,-5} got={2,-5}  instrument: {3}" -f $mark, $i.want, $got, $i.why | Write-Host
}

$mutations = @(
    @{ why  = 'carve list neutered -> a denied path must ALLOW'
       find = 'function Test-Carved([string]$rel) {'
       repl = 'function Test-Carved([string]$rel) { return $true;'
       probe= "$mutRepo\ZeroParadox\Computability\Kleene.lean"
       want = 'ALLOW' }
    @{ why  = 'spelling normaliser neutered -> \\?\ must ALLOW again'
       find = 'function ConvertTo-PlainSpelling([string]$p) {'
       repl = 'function ConvertTo-PlainSpelling([string]$p) { return $p;'
       probe= "\\?\$mutRepo\ZeroParadox\Computability\Kleene.lean"
       want = 'ALLOW' }
    @{ why  = 'deny-by-default removed -> unclassified root file must ALLOW'
       find = '    $what = ''an unclassified file'''
       repl = '    return $null; $what = ''an unclassified file'''
       probe= "$mutRepo\some-future-surface.xyz"
       want = 'ALLOW' }
    # ** THE CONTAINMENT BOUNDARY. ** Measured 2026-09-20: this mutation applied cleanly, resolved
    # correctly, and left the suite green at exit 0 - nothing pinned it. Under it, `$rel` is taken
    # from one character too early, so a SIBLING of the checkout is read as being inside it and
    # denied. It over-blocks rather than leaking, so it is ORDINARY - and an over-block that denies
    # every worktree whose path happens to extend the root's name would stop delegation dead, which
    # is the one outcome this guard's design claim cannot survive.
    @{ why  = 'containment test loses its separator -> a SIBLING of the root must DENY'
       find = 'if (-not $full.StartsWith($repoRoot + [System.IO.Path]::DirectorySeparatorChar, $cmp)) { return $null }'
       repl = 'if (-not $full.StartsWith($repoRoot, $cmp)) { return $null }'
       probe= "${mutRepo}-scratch\notes.md"
       want = 'DENY' }
    @{ why  = 'both-keys loop reverted to first-only -> corpus notebook beside benign file ALLOWs'
       find = 'foreach ($t in @($data.tool_input.file_path, $data.tool_input.notebook_path)) {'
       repl = 'foreach ($t in @($data.tool_input.file_path)) {'
       probe= '__BOTHKEYS__'
       want = 'ALLOW' }
)

$mi = 0
foreach ($m in $mutations) {
    $mi++
    $mutPath = Join-Path $mutDir ("mut$mi.ps1")
    $mutated = $src.Replace($m.find, $m.repl)
    Set-Content -Path $mutPath -Value $mutated -Encoding UTF8 -NoNewline
    $mutSha = Get-Sha $mutPath

    if ($mutSha -eq $baseSha) {
        $fails++
        "FAIL  MUTATION DID NOT APPLY (sha unchanged {0}) - anchor not found: {1}" -f $baseSha.Substring(0, 12), $m.why | Write-Host
        continue
    }

    if ($m.probe -eq '__BOTHKEYS__') {
        $payload = @{ tool_name='NotebookEdit'
                      tool_input=@{ file_path="$mutRepo\tools\verify\batch.py"
                                    notebook_path="$mutRepo\ZeroParadox\probe.ipynb" } } | ConvertTo-Json -Compress -Depth 5
    } else {
        $payload = Get-Payload 'Edit' 'file_path' $m.probe $null
    }
    $got = Invoke-HookRawAt $mutPath $payload
    $ok = ($got -eq $m.want)
    if (-not $ok) { $fails++ }
    $mark = if ($ok) { 'ok  ' } else { 'FAIL' }
    "{0}  sha {1}->{2}  want={3,-5} got={4,-5}  mutation: {5}" -f `
        $mark, $baseSha.Substring(0, 8), $mutSha.Substring(0, 8), $m.want, $got, $m.why | Write-Host
}

# The unmutated copy must still behave, in the same process, after all of the above. Without this
# row a mutation that corrupted the shared source would read as four successful mutations.
$ctl = Invoke-HookRawAt $baseCopy (Get-Payload 'Edit' 'file_path' "$mutRepo\ZeroParadox\Computability\Kleene.lean" $null)
$ctlOk = ($ctl -eq 'DENY')
if (-not $ctlOk) { $fails++ }
$mark = if ($ctlOk) { 'ok  ' } else { 'FAIL' }
"{0}  want=DENY  got={1,-5}  unmutated control, same process, after the mutations" -f $mark, $ctl | Write-Host

Remove-Item -Recurse -Force $mutRepo

""
$total = $cases.Count + $bothKeys.Count + $closed.Count + $naming.Count + $instr.Count + $mutations.Count + $extra + 1
if ($fails -eq 0) { "ALL {0} CONTROLS BEHAVED" -f $total | Write-Host; exit 0 }
"{0} of {1} CONTROL(S) MISBEHAVED" -f $fails, $total | Write-Host
exit 1
