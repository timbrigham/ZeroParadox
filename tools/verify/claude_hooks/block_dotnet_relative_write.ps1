# block_dotnet_relative_write.ps1
# PreToolUse hook (Bash, PowerShell) - DENIES a .NET file-system WRITE whose path argument is not
# fully qualified, or is a variable this hook cannot resolve to a fully qualified path.
# Class DC-71 (.claude-local/DEFECT_CLASSES.md). Built on Tim's approval, 2026-10-13.
#
# THE DEFECT. `Set-Location <worktree>` moves the PowerShell LOCATION. It does NOT move the .NET
# PROCESS current directory, and every `[IO.File]::*` / `[IO.Directory]::*` / `StreamWriter` call
# resolves a relative path against the process directory - which, for an agent, is the MAIN
# checkout. So a worktree agent writing `[IO.File]::WriteAllText("x.txt", ...)` silently dirties
# the shared checkout and sees success. Three occurrences (2026-10-04 twice, 2026-10-08). The
# lane brief said "Set-Location per command", which is exactly the instruction .NET ignores, so
# R-RECUR's third rung applied: the trigger was wrong, and a remembered rule cannot fix it.
#
# WHAT IT MATCHES (the common shapes a drifting agent produces, not a variant matrix - Tim's
# proportionality ruling, 2026-10-10):
#   [IO.File]::M(...)  [System.IO.File]::M(...)  [IO.Directory]::M(...)  [System.IO.Directory]::M(...)
#     where M is Write*, Append*, Create*, Copy, Move, Delete, Replace, Open, OpenWrite
#   [IO.StreamWriter]::new(...)  [System.IO.StreamWriter]::new(...)  New-Object [System.]IO.StreamWriter
# Path arguments judged: the first; the first two for Copy/Move; the first three for Replace
# (whose backup argument may be `$null`).
#
# WHAT COUNTS AS SAFE: a FULLY QUALIFIED path - `C:\...`, `C:/...`, or UNC `\\...`. Deliberately
# stricter than IsPathRooted, which also accepts `\foo` (current DRIVE) and `C:foo` (current
# directory ON drive C) - both still resolve against process state. A variable is followed through
# assignments made EARLIER IN THE SAME COMMAND (`$p = 'C:\x'`, `$p = Join-Path $wt x`,
# `[IO.Path]::Combine(...)`), `$env:NAME`, `$HOME` and `$PWD` (the PowerShell location, which is
# rooted - writing "$PWD\x" is the CORRECT fix, so it must pass). Two further idioms are ALLOWED
# because they resolve against the PowerShell LOCATION and always yield a full path (measured by
# /rely, 2026-10-13, O1 - both were lifted from real transcripts and were being falsely denied):
# `(Resolve-Path X).Path` / `.ProviderPath`, and an expression ending in `.FullName`
# (`$_.FullName`, `$f.FullName`, `(Get-Item x).FullName` - a FileSystemInfo the provider built has an
# absolute FullName). EXCEPT a FileInfo/DirectoryInfo CONSTRUCTED from a string (`[IO.FileInfo]"x"`,
# `[IO.FileInfo]::new("x")`, `New-Object IO.FileInfo x`, inline or via a variable): .NET resolves
# that string against the process directory, so its argument is judged like any path argument.
#
# NOT followed, on purpose: `[IO.Path]::GetFullPath("x")` resolves against the SAME process
# directory and is the same bug - it stays DENIED. Also `$(...)` subexpressions, function
# parameters and anything assigned in an earlier tool call. All are UNRESOLVED, and unresolved DENIES.
#
# IT FAILS CLOSED, matching block_git_gh.ps1 and block_corpus_edit.ps1. Empty stdin, unparseable
# JSON, an argument list with no closing parenthesis, or a variable it cannot follow -> DENY. The
# deny is a `permissionDecision: deny` VALUE, never a warning string (R-ZERONULL).
#
# WHAT THIS DOES *NOT* CATCH, stated so nobody mistakes it for a seal:
#   - a script written to disk and executed second; its command line carries no .NET call.
#   - python / node / other runtimes writing relative paths (they honour their own cwd, which in a
#     PowerShell tool call IS the process directory - same hazard, different spelling).
#   - Set-Content / Out-File with a relative path. Those honour the PowerShell LOCATION, so after a
#     Set-Location they land correctly; they are not this defect.
#   - type names reached through a variable (`$t = [IO.File]; $t::WriteAllText(...)`), `-EncodedCommand`.
# The threat model is DRIFT, not malice.
#
# Controls: tools\verify\claude_hooks\test_block_dotnet_relative_write.ps1

$raw = [Console]::In.ReadToEnd()

function Deny([string]$reason) {
    $out = @{
        hookSpecificOutput = @{
            hookEventName            = 'PreToolUse'
            permissionDecision       = 'deny'
            permissionDecisionReason = $reason
        }
    }
    Write-Output ($out | ConvertTo-Json -Compress -Depth 5)
    exit 0
}

$GUIDANCE = @'
.NET FILE CALLS IGNORE Set-Location. `[IO.File]::*`, `[IO.Directory]::*` and `StreamWriter` resolve a
relative path against the PROCESS directory, which is the MAIN checkout - not your worktree, not
the PowerShell location. Three agents have dirtied the shared checkout this way (class DC-71).

DO INSTEAD, any one of:
  * pass a FULLY QUALIFIED path:   [IO.File]::WriteAllText('C:\...\wt\x.txt', $s)
  * resolve it against your PowerShell location first:
        $p = (Resolve-Path x.txt).Path; [IO.File]::WriteAllText($p, $s)
  * use `.FullName` from Get-ChildItem / Get-Item:
        Get-ChildItem *.md | ForEach-Object { [IO.File]::WriteAllText($_.FullName, $s) }
  * build it from a rooted base in the SAME command:
        $wt = 'C:\...\wt'; [IO.File]::WriteAllText((Join-Path $wt 'x.txt'), $s)
  * use the Write / Edit tools, or `Set-Content -LiteralPath <absolute>`.

NOT a fix: `[IO.Path]::GetFullPath('x')` resolves against the same PROCESS directory - same bug.
A variable this hook cannot follow (assigned in an earlier call, a function parameter, a
`$(...)` subexpression) is DENIED, because it cannot tell where the write lands.
'@

if ([string]::IsNullOrWhiteSpace($raw)) {
    Deny "BLOCKED (fail-closed): the hook received empty input and cannot tell what was requested.`n`n$GUIDANCE"
}

try { $data = $raw | ConvertFrom-Json } catch {
    Deny "BLOCKED (fail-closed): the hook could not parse its input, so it cannot rule out a relative-path .NET write.`n`n$GUIDANCE"
}

$cmd = $data.tool_input.command
if ($null -eq $cmd) { exit 0 }   # not a command-bearing tool; nothing to inspect
$cmd = [string]$cmd

# Fast path: almost every command never names these types.
if ($cmd -notmatch '(?i)IO\.(File|Directory|StreamWriter)\b') { exit 0 }

# A Bash tool call usually carries the PowerShell as `powershell -Command "...\"x.txt\"..."`.
# Undo bash's double-quote escapes - `\"`, `\$`, `\\`, `` \` `` - in ONE pass, so `\"\$env:TEMP\\x\"`
# becomes `"$env:TEMP\x"`. (Only `\"` was undone before, which left `\$env:TEMP` resolving to
# `\C:\...` and falsely denied: /rely O3, 2026-10-13.)
if ($data.tool_name -eq 'Bash') { $cmd = [regex]::Replace($cmd, '\\(["$\\`])', '$1') }

# ---------------------------------------------------------------------------------------------
# Split a parenthesised argument list starting at $open (the index of '('). Returns the argument
# strings, or $null when there is no matching ')' - which the caller treats as DENY.
function Split-Args([string]$s, [int]$open) {
    $args2 = New-Object System.Collections.Generic.List[string]
    $depth = 0; $q = [char]0; $start = $open + 1
    for ($i = $open; $i -lt $s.Length; $i++) {
        $c = $s[$i]
        if ($q -ne [char]0) { if ($c -eq $q) { $q = [char]0 }; continue }
        if ($c -eq "'" -or $c -eq '"') { $q = $c; continue }
        if ($c -eq '(' -or $c -eq '[' -or $c -eq '{') { $depth++; continue }
        if ($c -eq ')' -or $c -eq ']' -or $c -eq '}') {
            $depth--
            if ($depth -eq 0) { $args2.Add($s.Substring($start, $i - $start)); return ,$args2.ToArray() }
            continue
        }
        if ($c -eq ',' -and $depth -eq 1) { $args2.Add($s.Substring($start, $i - $start)); $start = $i + 1 }
    }
    return $null
}

# Whitespace tokenizer respecting quotes and parentheses (for Join-Path's arguments).
function Split-Words([string]$s) {
    $out = New-Object System.Collections.Generic.List[string]
    $buf = ''; $q = [char]0; $depth = 0
    foreach ($c in $s.ToCharArray()) {
        if ($q -ne [char]0) { $buf += $c; if ($c -eq $q) { $q = [char]0 }; continue }
        if ($c -eq "'" -or $c -eq '"') { $q = $c; $buf += $c; continue }
        if ($c -eq '(') { $depth++ } elseif ($c -eq ')') { $depth-- }
        if ([char]::IsWhiteSpace($c) -and $depth -eq 0) { if ($buf) { $out.Add($buf); $buf = '' }; continue }
        $buf += $c
    }
    if ($buf) { $out.Add($buf) }
    return ,$out.ToArray()
}

function Test-FullyQualified([string]$p) {
    if ($null -eq $p) { return $false }
    return ($p -match '^[A-Za-z]:[\\/]' -or $p -match '^[\\/]{2}[^\\/]')
}

$VARS = @{}   # name -> raw right-hand side, from assignments before the call being judged
$script:failed = $false   # set by the interpolation evaluator when a "$var" will not resolve

function Resolve-VarName([string]$name, [int]$depth) {
    if ($name -match '^(?i)env:(\w+)$') { return [Environment]::GetEnvironmentVariable($Matches[1]) }
    if ($name -ieq 'PWD')  { return 'C:\__powershell_location__' }   # rooted by construction
    if ($name -ieq 'HOME') { return $env:USERPROFILE }
    if ($name -ieq 'null') { return $null }
    if ($VARS.ContainsKey($name.ToLower())) { return Resolve-Expr $VARS[$name.ToLower()] ($depth + 1) }
    return $null
}

# Returns the resolved path string, or $null when it cannot be resolved (which DENIES).
function Resolve-Expr([string]$e, [int]$depth) {
    if ($depth -gt 8 -or $null -eq $e) { return $null }
    $e = $e.Trim()
    if ($e.Length -eq 0) { return $null }
    while ($e.StartsWith('(') -and $e.EndsWith(')')) {
        $inner = Split-Args $e 0
        # Strip only when the FIRST '(' closes at the LAST character - `(a) + (b)` is not wrapped.
        if ($null -eq $inner -or $inner.Count -ne 1 -or ($inner[0].Length + 2) -ne $e.Length) { break }
        $e = $inner[0].Trim()
    }
    # O1: these resolve against the PowerShell LOCATION and always yield a full path.
    if ($e -match '^(?i)\(\s*Resolve-Path\b.*\)\.(Path|ProviderPath)$') { return 'C:\__resolve_path__' }
    if ($e -match '^(?i)\S.*\.FullName$') { return (Resolve-FullName $e $depth) }
    if ($e -match "^'((?:[^']|'')*)'$") { return $Matches[1].Replace("''", "'") }
    if ($e -match '^"([^"]*)"$') {
        $body = $Matches[1]
        if ($body.Contains('$(')) { return $null }
        $failed = $false
        $expanded = [regex]::Replace($body, '\$\{?((?:env:)?\w+)\}?', {
            param($m)
            $v = Resolve-VarName $m.Groups[1].Value $depth
            if ($null -eq $v) { $script:failed = $true; return '' }
            return $v
        })
        if ($script:failed) { $script:failed = $false; return $null }
        return $expanded
    }
    if ($e -match '^\$\{?((?:env:)?\w+)\}?$') { return Resolve-VarName $Matches[1] $depth }
    if ($e -match '^(?i)Join-Path\s+(.*)$') {
        # Assign first: Split-Words returns its array wrapped (`,`), so piping it straight into
        # Where-Object would hand the filter ONE element - the whole array.
        $all = Split-Words $Matches[1]
        $words = @($all | Where-Object { $_ -notmatch '^(?i)-(Path|ChildPath|Resolve)$' })
        if ($words.Count -lt 2) { return $null }
        $a = Resolve-Expr $words[0] ($depth + 1)
        $b = Resolve-Expr $words[1] ($depth + 1)
        if ($null -eq $a -or $null -eq $b) { return $null }
        return ($a.TrimEnd('\', '/') + '\' + $b)
    }
    if ($e -match '^(?i)\[(System\.)?IO\.Path\]::Combine\s*\(') {
        $parts = Split-Args $e $e.IndexOf('(')
        if ($null -eq $parts) { return $null }
        $acc = ''
        foreach ($p in $parts) {
            $r = Resolve-Expr $p ($depth + 1)
            if ($null -eq $r) { return $null }
            if (Test-FullyQualified $r) { $acc = $r } elseif ($acc) { $acc = $acc.TrimEnd('\', '/') + '\' + $r } else { $acc = $r }
        }
        return $acc
    }
    if ($e -match '^[\w.\-\\/:]+$') { return $e }   # a bareword path, e.g. x.txt or C:\x
    return $null
}

# `<x>.FullName` is absolute for a FileSystemInfo that came from the file system (Get-Item,
# Get-ChildItem, `$_`), because the provider built it against the PowerShell location. A FileInfo or
# DirectoryInfo CONSTRUCTED from a string is the exception (CARRYW3-13 r2 O1): .NET resolves that
# string against the PROCESS directory, so `([IO.FileInfo]"x.txt").FullName` is the DC-71 path in
# disguise. So the constructor's argument is judged exactly like a direct path argument - inline,
# or through a variable assigned earlier in the same command.
function Resolve-FullName([string]$e, [int]$depth) {
    $base = $e.Substring(0, $e.Length - '.FullName'.Length).Trim()
    while ($base.StartsWith('(') -and $base.EndsWith(')')) {
        $inner = Split-Args $base 0
        if ($null -eq $inner -or $inner.Count -ne 1 -or ($inner[0].Length + 2) -ne $base.Length) { break }
        $base = $inner[0].Trim()
    }
    if ($base -match '^\$(\w+)$' -and $VARS.ContainsKey($Matches[1].ToLower())) { $base = $VARS[$Matches[1].ToLower()].Trim() }
    $ctorArg = $null
    if ($base -match '^(?i)\[(System\.)?IO\.(File|Directory)Info\]::new\s*\(') {
        $parts = Split-Args $base $base.IndexOf('(')
        if ($null -eq $parts -or $parts.Count -lt 1) { return $null }
        $ctorArg = $parts[0]
    } elseif ($base -match '^(?i)\[(System\.)?IO\.(File|Directory)Info\]\s*(.+)$') {
        $ctorArg = $Matches[3]
    } elseif ($base -match '^(?i)New-Object\s+(?:-TypeName\s+)?(?:System\.)?IO\.(?:File|Directory)Info\s+(?:-ArgumentList\s+)?(.+)$') {
        $ctorArg = $Matches[1]
    }
    if ($null -eq $ctorArg) { return 'C:\__fullname__' }
    return (Resolve-Expr $ctorArg ($depth + 1))
}

# Collect `$name = <rhs>` assignments that appear BEFORE $limit, in order (later wins).
function Get-Assignments([string]$s, [int]$limit) {
    $VARS.Clear()
    foreach ($m in [regex]::Matches($s.Substring(0, $limit), '\$(\w+)\s*=(?!=)\s*([^;\r\n]+)')) {
        $VARS[$m.Groups[1].Value.ToLower()] = $m.Groups[2].Value
    }
}

# ---------------------------------------------------------------------------------------------
$CALL = '(?i)\[(?:System\.)?IO\.(?<type>File|Directory|StreamWriter)\]::(?<member>\w+)\s*\(' +
        '|(?i)New-Object\s+(?:-TypeName\s+)?(?:System\.)?IO\.(?<type>StreamWriter)\b(?<member>)'
$WRITE = '^(?i)(Write\w*|Append\w*|Create\w*|Copy|Move|Delete|Replace|Open|OpenWrite|new)$'

$bad = New-Object System.Collections.Generic.List[string]
foreach ($m in [regex]::Matches($cmd, $CALL)) {
    $type = $m.Groups['type'].Value
    $member = $m.Groups['member'].Value
    if ($type -ieq 'StreamWriter') {
        if ($member -and $member -ine 'new') { continue }
    } elseif ($member -notmatch $WRITE -or $member -ieq 'new') { continue }

    $label = if ($member) { "[IO.$type]::$member" } else { "New-Object IO.$type" }
    Get-Assignments $cmd $m.Index

    if ($member) {
        $args3 = Split-Args $cmd ($m.Index + $m.Length - 1)
    } else {
        $rest = $cmd.Substring($m.Index + $m.Length).TrimStart()
        $rest = $rest -replace '^(?i)-ArgumentList\s*', ''
        if ($rest.StartsWith('(')) { $args3 = Split-Args $rest 0 }
        else { $args3 = @(($rest -split '[;|\r\n]')[0] -split ',') }
    }
    if ($null -eq $args3 -or $args3.Count -eq 0) {
        $bad.Add("$label - its argument list could not be parsed (fail-closed)"); continue
    }

    $n = 1
    if ($member -match '^(?i)(Copy|Move)$') { $n = 2 }
    if ($member -ieq 'Replace') { $n = 3 }
    for ($k = 0; $k -lt [Math]::Min($n, $args3.Count); $k++) {
        $arg = $args3[$k].Trim()
        if ($member -ieq 'Replace' -and $k -eq 2 -and $arg -ieq '$null') { continue }
        $resolved = Resolve-Expr $arg 0
        if ($null -eq $resolved) {
            $bad.Add("$label argument $($k + 1) '$arg' - not resolvable to a fully qualified path in this command")
        } elseif (-not (Test-FullyQualified $resolved)) {
            $bad.Add("$label argument $($k + 1) '$arg' - relative ('$resolved'); .NET resolves it against the process directory")
        }
    }
}

if ($bad.Count -gt 0) {
    $list = ($bad | ForEach-Object { "  - $_" }) -join "`n"
    Deny @"
BLOCKED: a .NET file-system write with a path that is not fully qualified (class DC-71).

$list

$GUIDANCE
"@
}

exit 0
