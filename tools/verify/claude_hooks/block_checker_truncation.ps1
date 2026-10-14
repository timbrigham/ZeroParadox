# block_checker_truncation.ps1
# PreToolUse hook - DENIES any Bash/PowerShell call that RUNS a checker under tools/verify and sends
# its output anywhere except WHOLE: to a file, to the terminal, or to a pass-through sink.
#
# WHY THIS EXISTS WHEN A RULE ALREADY SAID SO.
# CLAUDE.md R-TRUNC said "never truncate a hook-running command", and on 2026-08-28 an agent typed
#       python tools/verify/check_encoding.py .claude-local/DEFECTS.md 2>&1 | Select-Object -Last 2
# an hour after quoting R-TRUNC back at itself. The two lines it kept were the tail of a banner; the
# four double-encoding WARNINGS above them were invisible. An ACTION binds, a CATEGORY leaks: the
# action here is "a pipe after a tools/verify invocation", which is typeable and needs no judgement.
#
# WHAT IT IS PROTECTING. A checker's verdict is the WHOLE of its output. Exit 0 routinely means "no
# BLOCKING findings, and N warnings you have not read". A filtering consumer removes exactly the part
# that was not the symptom you went looking for; an early-exiting one can also destroy the EXIT
# STATUS (a push blocked bare exited 1 and exited 0 through `| head -5`: SIGPIPE).
#
# ** THE RULE IS AN ALLOW-LIST OF SINKS, NOT A DENYLIST OF CONSUMERS (RLY40-1). ** A list of
# truncators is porous by construction: fed 19 filters, the first version let 15 through (sed, awk,
# sort, uniq, cut, wc, rg, ForEach-Object, Measure-Object, Select-Object -Skip/-Index ...). So:
#   - a pipe after a checker invocation is DENIED unless every later stage is a SINK - Out-File,
#     Set-Content, Add-Content, Tee-Object, tee, Out-String, Out-Host, Out-Default, Write-Output,
#     Write-Host. A consumer nobody listed is denied on arrival.
#   - a redirect of the checker's output to a FILE is the compliant shape, and that file is then
#     TRACKED: a later statement in the same call that names it must read it WHOLE (Get-Content /
#     cat / type with no row-limiting flag, piped only to sinks). `> out.log; Get-Content out.log
#     -Tail 20` is the same cut in two statements.
#   - a redirect to $null / /dev/null / NUL, or capturing the output into a variable and then using
#     it in any way but whole, or indexing a captured `(...)` result, is denied the same way.
#
# ** IT TESTS INVOCATION, NOT MENTION (RLY40-4). ** The command is TOKENISED - quotes, PowerShell
# here-strings, bash heredocs and comments are recognised - and a checker counts as run only when it
# is the COMMAND WORD of a pipeline stage: after an interpreter (python/py, powershell -File/-Command,
# bash -c, Invoke-Expression), a call operator, or as the path itself. So these are allowed:
#       grep -n "check_poles" tools/verify/batch.py | head -20      <- greps a file
#       echo "never pipe python tools/verify/x.py | head"           <- quoted text
#       @' ... python tools/verify/x.py | head ... '@ | Set-Content n.md   <- a here-string
#       python tools/verify/x.py > a.log; Get-Content other.txt -TotalCount 5  <- an unrelated file
# ** AND IT STAYS FAIL-CLOSED WHERE THE TOKENISER COULD BE WRONG. ** The pre-tokeniser regex (an
# interpreter governing a tools/verify path) still runs, over the text with quotes, comments and
# heredoc bodies blanked out. If it finds an invocation the parser did not attribute, the strict
# reading applies: any later non-sink pipe or row-limiting flag is denied. An unbalanced bracket in a
# command that mentions a checker is denied outright. A mis-parse can therefore cost a false DENY,
# never a silent pass.
#
# THE build.log CASE. enforce_log_read_limits.ps1 REQUIRES a row limit on `Get-Content build.log*`.
# build.log is not a redirect target of a checker in the same call, so a limited read of it is an
# unrelated read and passes - unless the call itself redirected a checker INTO build.log.
#
# WHAT THIS DOES *NOT* CATCH, stated so nobody mistakes it for a seal:
#   - TWO SEPARATE TOOL CALLS. Run the checker in one call, narrowly read its log in the next, and
#     each command string is clean. Only reading the file whole fixes that one.
#   - a wrapper script on disk, a python -c that reads the log, a copy of the log under another name,
#     or the Read tool with offset/limit against a saved log.
# The threat model is DRIFT, not malice: an agent reaching for `| head` out of habit.
#
# IT FAILS CLOSED: empty, unparseable or command-less input is DENIED.
#
# Controls: tools\verify\claude_hooks\test_block_checker_truncation.ps1

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
READ THE CHECKER OUTPUT WHOLE. Redirect it to a file, then open the file whole:

    python tools/verify/<checker>.py <args> > "$sp\out.log" 2>&1
    "EXIT=$LASTEXITCODE"
    Get-Content "$sp\out.log"

WHY, precisely:
  * A green exit is not "clean". These checkers routinely exit 0 while reporting warnings, counts
    and suppression totals, and the count IS the finding.
  * An early-exiting consumer can destroy the EXIT STATUS as well as the text. The identical push
    exited 1 bare and 0 through `| head -5`: SIGPIPE killed the hook before its own `exit 1`.
  * The part you filter away is by construction the part you were not already looking for.

ALLOWED after a checker: a file redirect, or a pipe to Out-File / Set-Content / Add-Content /
Tee-Object / tee / Out-String / Out-Host / Write-Output. Anything else is denied, including
consumers nobody thought to list. If the output is genuinely too large to read, say so out loud -
that is a reason to fix the checker's reporting, not to keep the first twenty lines.

NOT AFFECTED: reading or grepping checker SOURCE (`grep -n x tools/verify/batch.py | head`), text
that merely MENTIONS a checker (quoted, a here-string, a comment), and a limited read of a file the
checker did not write in this call, such as build.log.
'@

if ([string]::IsNullOrWhiteSpace($raw)) {
    Deny "BLOCKED (fail-closed): the hook received empty input and cannot tell what was requested.`n`n$GUIDANCE"
}
try { $data = $raw | ConvertFrom-Json } catch {
    Deny "BLOCKED (fail-closed): the hook could not parse its input, so it cannot rule out a truncated checker run.`n`n$GUIDANCE"
}
$cmd = $null
if ($null -ne $data -and $null -ne $data.tool_input) { $cmd = $data.tool_input.command }
if (-not ($cmd -is [string]) -or [string]::IsNullOrWhiteSpace($cmd)) {
    Deny "BLOCKED (fail-closed): the hook found no command string in tool_input.command, so it cannot rule out a truncated checker run.`n`n$GUIDANCE"
}
$KIND = if ("$($data.tool_name)" -eq 'Bash') { 'bash' } else { 'ps' }

# The pre-tokeniser invocation pattern: an interpreter token GOVERNING a tools/verify path. The
# lookbehind keeps the `py` of a `.py` extension from reading as the launcher.
$RUN_PY = '(?i)(?<![\w.])(?:python3?|py)\b(?:\s+-\S+)*\s+["'']?[^"''|;]*tools[\\/]verify[\\/]\S+\.py'
$RUN_PS = '(?i)(?:&|powershell(?:\s+-\S+)*\s+-File|pwsh(?:\s+-\S+)*\s+-File)\s+["'']?[^"''|;]*tools[\\/]verify[\\/]\S+\.ps1'
# Cheap exit: a command that never mentions tools/verify cannot run a checker from there.
if ($cmd -notmatch '(?i)tools[\\/.]verify') { exit 0 }

$SINKS   = @('out-file', 'set-content', 'add-content', 'tee-object', 'tee', 'out-string', 'out-host',
             'out-default', 'write-output', 'write-host')
$WHOLE_READERS = @('get-content', 'gc', 'cat', 'type')
$READERS = @('get-content', 'gc', 'cat', 'type', 'head', 'tail', 'select-string', 'sls', 'grep', 'rg',
             'sed', 'awk', 'more', 'less', 'findstr', 'select-object', 'select')
$LIMIT_FLAG = '(?i)^-(Tail|TotalCount|Head|First|Last|Skip|Index|ReadCount|Wait)$'
$NULL_TARGET = '(?i)^(\$null|/dev/null|nul)$'

$script:invokeCount = 0
$script:unparsed    = $false
$script:taintFiles  = New-Object System.Collections.Generic.List[string]
$script:taintVars   = New-Object System.Collections.Generic.List[string]
$script:taintUnknown = $false
$script:denyLabel   = $null
$script:limitedReads = New-Object System.Collections.Generic.List[object]
$LIMIT_READERS = @('get-content', 'gc', 'cat', 'type', 'head', 'tail')

# ---------------------------------------------------------------------------
# TOKENISER. Returns a list of tokens: W (word, .V unquoted value, .Q quoted-anywhere), G (a
# bracketed group, .V inner text, .Adj true when `[` or `.` follows the close at once), OP (; && ||
# |), RD (a redirect operator, its target is the next W). .Subs carries `$(...)` / backtick text
# found inside double quotes - those EXECUTE, so they are analysed as commands of their own.
# ---------------------------------------------------------------------------
function Find-Close([string]$s, [int]$i, [char]$open, [char]$close) {
    # $i is the index just past the opening bracket. Returns the index of the matching close, or -1.
    $depth = 1; $n = $s.Length
    while ($i -lt $n) {
        $c = $s[$i]
        if ($c -eq "'") { $j = $s.IndexOf("'", $i + 1); if ($j -lt 0) { return -1 }; $i = $j + 1; continue }
        if ($c -eq '"') {
            $j = $i + 1
            while ($j -lt $n -and $s[$j] -ne '"') { if ($s[$j] -eq '`' -or $s[$j] -eq '\') { $j++ }; $j++ }
            if ($j -ge $n) { return -1 }; $i = $j + 1; continue
        }
        if ($c -eq $open) { $depth++ }
        elseif ($c -eq $close) { $depth--; if ($depth -eq 0) { return $i } }
        $i++
    }
    return -1
}

function New-Tok($t, $v, $p) { return @{ T = $t; V = $v; P = $p; Q = $false; Adj = $false; Subs = @() } }

function Get-Tokens([string]$s, [string]$kind) {
    $toks = New-Object System.Collections.Generic.List[object]
    $n = $s.Length; $i = 0
    $buf = New-Object System.Text.StringBuilder; $bufStart = -1; $bufQ = $false; $subs = @()
    $flush = {
        if ($bufStart -ge 0) {
            $t = New-Tok 'W' $buf.ToString() $bufStart; $t.Q = $bufQ; $t.Subs = $subs
            $toks.Add($t)
        }
        [void]$buf.Clear()
    }
    while ($i -lt $n) {
        $c = $s[$i]
        $atStart = ($bufStart -lt 0)
        if ($c -eq ' ' -or $c -eq "`t" -or $c -eq "`r") {
            if (-not $atStart) { & $flush; $bufStart = -1; $bufQ = $false; $subs = @() }; $i++; continue
        }
        if ($c -eq "`n" -or $c -eq ';') {
            if (-not $atStart) { & $flush; $bufStart = -1; $bufQ = $false; $subs = @() }
            $toks.Add((New-Tok 'OP' ';' $i)); $i++; continue
        }
        if ($c -eq '#' -and $atStart) {
            $j = $s.IndexOf("`n", $i); if ($j -lt 0) { $j = $n }; $i = $j; continue
        }
        if ($kind -eq 'ps' -and $c -eq '<' -and $i + 1 -lt $n -and $s[$i + 1] -eq '#') {
            $j = $s.IndexOf('#>', $i + 2); if ($j -lt 0) { $script:unparsed = $true; $j = $n - 2 }; $i = $j + 2; continue
        }
        # PowerShell here-strings: @' / @" then end of line; closed by '@ / "@ at the start of a line.
        if ($kind -eq 'ps' -and $c -eq '@' -and $i + 1 -lt $n -and ($s[$i + 1] -eq "'" -or $s[$i + 1] -eq '"')) {
            $q = $s[$i + 1]
            $m = [regex]::Match($s.Substring($i + 2), '^[ \t]*\r?\n')
            if ($m.Success) {
                $bodyStart = $i + 2 + $m.Length
                $endM = [regex]::Match($s.Substring($bodyStart), "(?m)^" + [regex]::Escape("$q@"))
                if (-not $endM.Success) { $script:unparsed = $true; $i = $n; continue }
                $body = $s.Substring($bodyStart, $endM.Index)
                if ($atStart) { $bufStart = $i }
                [void]$buf.Append($body); $bufQ = $true
                if ($q -eq '"') { $subs += @(Get-DoubleQuoteSubs $body $kind) }
                $i = $bodyStart + $endM.Index + 2; continue
            }
        }
        if ($c -eq "'") {
            if ($atStart) { $bufStart = $i }
            $j = $i + 1; $sb = New-Object System.Text.StringBuilder
            while ($true) {
                $k = $s.IndexOf("'", $j)
                if ($k -lt 0) { $script:unparsed = $true; [void]$sb.Append($s.Substring($j)); $j = $n; break }
                [void]$sb.Append($s.Substring($j, $k - $j))
                if ($kind -eq 'ps' -and $k + 1 -lt $n -and $s[$k + 1] -eq "'") { [void]$sb.Append("'"); $j = $k + 2; continue }
                $j = $k + 1; break
            }
            [void]$buf.Append($sb.ToString()); $bufQ = $true; $i = $j; continue
        }
        if ($c -eq '"') {
            if ($atStart) { $bufStart = $i }
            $j = $i + 1; $sb = New-Object System.Text.StringBuilder
            $closed = $false
            while ($j -lt $n) {
                $d = $s[$j]
                if (($kind -eq 'ps' -and $d -eq '`') -or ($kind -eq 'bash' -and $d -eq '\')) {
                    if ($j + 1 -lt $n) { [void]$sb.Append($s[$j + 1]) }; $j += 2; continue
                }
                if ($d -eq '"') {
                    if ($kind -eq 'ps' -and $j + 1 -lt $n -and $s[$j + 1] -eq '"') { [void]$sb.Append('"'); $j += 2; continue }
                    $closed = $true; $j++; break
                }
                [void]$sb.Append($d); $j++
            }
            if (-not $closed) { $script:unparsed = $true }
            $text = $sb.ToString()
            [void]$buf.Append($text); $bufQ = $true
            $subs += @(Get-DoubleQuoteSubs $text $kind)
            $i = $j; continue
        }
        if ($kind -eq 'ps' -and $c -eq '`') {
            if ($atStart) { $bufStart = $i }
            if ($i + 1 -lt $n -and $s[$i + 1] -ne "`n" -and $s[$i + 1] -ne "`r") { [void]$buf.Append($s[$i + 1]) }
            $i += 2; continue
        }
        if ($kind -eq 'bash' -and $c -eq '\') {
            if ($atStart) { $bufStart = $i }
            if ($i + 1 -lt $n -and $s[$i + 1] -ne "`n") { [void]$buf.Append($s[$i + 1]) }
            $i += 2; continue
        }
        if ($kind -eq 'bash' -and $c -eq '`') {
            if (-not $atStart) { & $flush; $bufStart = -1; $bufQ = $false; $subs = @() }
            $j = $s.IndexOf('`', $i + 1)
            if ($j -lt 0) { $script:unparsed = $true; $j = $n }
            $t = New-Tok 'G' $s.Substring($i + 1, [Math]::Max(0, $j - $i - 1)) $i; $toks.Add($t)
            $i = $j + 1; continue
        }
        $isSub = (($c -eq '$' -or $c -eq '@') -and $i + 1 -lt $n -and $s[$i + 1] -eq '(')
        if ($isSub -or $c -eq '(' -or ($c -eq '{' -and -not ($buf.Length -gt 0 -and $buf.ToString().EndsWith('$')))) {
            if (-not $atStart) { & $flush; $bufStart = -1; $bufQ = $false; $subs = @() }
            $openAt = if ($isSub) { $i + 1 } else { $i }
            $open = $s[$openAt]; $close = if ($open -eq '{') { [char]'}' } else { [char]')' }
            $j = Find-Close $s ($openAt + 1) $open $close
            if ($j -lt 0) { $script:unparsed = $true; $j = $n }
            $t = New-Tok 'G' $s.Substring($openAt + 1, [Math]::Max(0, [Math]::Min($j, $n) - $openAt - 1)) $i
            if ($j + 1 -lt $n -and ($s[$j + 1] -eq '[' -or $s[$j + 1] -eq '.')) { $t.Adj = $true }
            $toks.Add($t); $i = $j + 1; continue
        }
        if ($c -eq '{') {   # `${name}` - a variable, not a block
            $j = $s.IndexOf('}', $i); if ($j -lt 0) { $script:unparsed = $true; $j = $n - 1 }
            [void]$buf.Append($s.Substring($i, $j - $i + 1)); $i = $j + 1; continue
        }
        if ($c -eq ')' -or $c -eq '}') { $script:unparsed = $true; $i++; continue }
        if ($c -eq '|') {
            if (-not $atStart) { & $flush; $bufStart = -1; $bufQ = $false; $subs = @() }
            if ($i + 1 -lt $n -and $s[$i + 1] -eq '|') { $toks.Add((New-Tok 'OP' ';' $i)); $i += 2 }
            # bash `|&` is a PIPE of stdout AND stderr - never a pipe followed by a background `&`.
            elseif ($i + 1 -lt $n -and $s[$i + 1] -eq '&') { $toks.Add((New-Tok 'OP' '|' $i)); $i += 2 }
            else { $toks.Add((New-Tok 'OP' '|' $i)); $i++ }
            continue
        }
        if ($c -eq '&') {
            if ($i + 1 -lt $n -and $s[$i + 1] -eq '&') {
                if (-not $atStart) { & $flush; $bufStart = -1; $bufQ = $false; $subs = @() }
                $toks.Add((New-Tok 'OP' ';' $i)); $i += 2; continue
            }
            if ($kind -eq 'bash' -and $i + 1 -lt $n -and $s[$i + 1] -eq '>') {
                if (-not $atStart) { & $flush; $bufStart = -1; $bufQ = $false; $subs = @() }
                $op = '&>'; $i += 2; if ($i -lt $n -and $s[$i] -eq '>') { $op = '&>>'; $i++ }
                $toks.Add((New-Tok 'RD' $op $i)); continue
            }
            if (-not $atStart) { & $flush; $bufStart = -1; $bufQ = $false; $subs = @() }
            if ($kind -eq 'bash') { $toks.Add((New-Tok 'OP' ';' $i)) } else { $toks.Add((New-Tok 'W' '&' $i)) }
            $i++; continue
        }
        if ($c -eq '>' -or $c -eq '<') {
            $prefix = ''
            if (-not $atStart -and $buf.ToString() -match '^[0-9*]$') { $prefix = $buf.ToString(); [void]$buf.Clear(); $bufStart = -1; $bufQ = $false; $subs = @() }
            elseif (-not $atStart) { & $flush; $bufStart = -1; $bufQ = $false; $subs = @() }
            $op = $prefix + $c; $i++
            if ($i -lt $n -and $s[$i] -eq $c) { $op += $c; $i++ }
            if ($c -eq '>' -and $i + 1 -lt $n -and $s[$i] -eq '&' -and [char]::IsDigit($s[$i + 1])) {
                $toks.Add((New-Tok 'RD' ($op + '&') $i)); $i += 2; continue   # 2>&1 - a stream merge, no file
            }
            $toks.Add((New-Tok 'RD' $op $i)); continue
        }
        if ($atStart) { $bufStart = $i }
        [void]$buf.Append($c); $i++
    }
    if ($bufStart -ge 0) { & $flush }
    return ,$toks
}

function Get-DoubleQuoteSubs([string]$text, [string]$kind) {
    $out = @(); $i = 0
    while ($i -lt $text.Length) {
        if ($text[$i] -eq '$' -and $i + 1 -lt $text.Length -and $text[$i + 1] -eq '(') {
            $j = Find-Close $text ($i + 2) '(' ')'
            if ($j -lt 0) { $script:unparsed = $true; $j = $text.Length }
            $out += $text.Substring($i + 2, [Math]::Max(0, $j - $i - 2)); $i = $j + 1; continue
        }
        if ($kind -eq 'bash' -and $text[$i] -eq '`') {
            $j = $text.IndexOf('`', $i + 1); if ($j -lt 0) { $script:unparsed = $true; $j = $text.Length }
            $out += $text.Substring($i + 1, [Math]::Max(0, $j - $i - 1)); $i = $j + 1; continue
        }
        $i++
    }
    return $out
}

# Bash heredoc bodies are blanked (same length, newlines kept) before tokenising; an UNQUOTED
# delimiter expands `$(...)` in the body, so that text is returned for analysis.
function Remove-Heredocs([string]$s, [ref]$expanding) {
    $rx = [regex]'<<-?[ \t]*([''"]?)([A-Za-z_][A-Za-z0-9_]*)\1'
    $pos = 0; $result = $s; $list = @()
    while ($true) {
        $m = $rx.Match($result, $pos)
        if (-not $m.Success) { break }
        $nl = $result.IndexOf("`n", $m.Index + $m.Length)
        if ($nl -lt 0) { break }
        $endM = [regex]::Match($result.Substring($nl + 1), "(?m)^\t*" + [regex]::Escape($m.Groups[2].Value) + "[ \t]*\r?$")
        if (-not $endM.Success) { $script:unparsed = $true; break }
        $bodyStart = $nl + 1; $bodyLen = $endM.Index + $endM.Length
        $body = $result.Substring($bodyStart, $bodyLen)
        if ($m.Groups[1].Value -eq '') { $list += @(Get-DoubleQuoteSubs $body 'bash') }
        $blank = -join ($body.ToCharArray() | ForEach-Object { if ($_ -eq "`n") { "`n" } else { ' ' } })
        $result = $result.Substring(0, $bodyStart) + $blank + $result.Substring($bodyStart + $bodyLen)
        $pos = $bodyStart + $bodyLen
    }
    $expanding.Value = $list
    return $result
}

function Get-Leaf([string]$w) {
    $l = ($w -split '[\\/]')[-1].ToLowerInvariant()
    if ($l.EndsWith('.exe')) { $l = $l.Substring(0, $l.Length - 4) }
    return $l
}
function Test-CheckerPath([string]$w) { return ($w -match '(?i)(^|[\\/])tools[\\/]verify[\\/].+\.(py|ps1)$') }
function Get-Norm([string]$w) {
    $x = $w.Trim().ToLowerInvariant() -replace '/', '\'
    while ($x.StartsWith('.\')) { $x = $x.Substring(2) }
    return $x
}

# Is this sequence of items (W/G tokens, the stage's command portion) a checker invocation?
function Test-Invocation($items, [string]$kind, [int]$depth) {
    $words = @($items)
    $k = 0
    # skip wrappers and bash env assignments
    while ($k -lt $words.Count -and $words[$k].T -eq 'W' -and -not $words[$k].Q) {
        $v = $words[$k].V
        if ($v -match '^[A-Za-z_]\w*=' -or $v -in @('time', 'nohup', 'env', 'nice', 'command', 'exec')) { $k++; continue }
        if ($v -eq 'timeout' -and $k + 1 -lt $words.Count) { $k += 2; continue }
        break
    }
    if ($k -ge $words.Count -or $words[$k].T -ne 'W') { return $false }
    $h = $words[$k].V
    if ($h -eq '&' -or $h -eq '.') {
        if ($k + 1 -ge $words.Count -or $words[$k + 1].T -ne 'W') { return $false }
        if (Test-CheckerPath $words[$k + 1].V) { return $true }
        return (Test-Invocation $words[($k + 1)..($words.Count - 1)] $kind $depth)
    }
    $leaf = Get-Leaf $h
    $rest = @(); if ($k + 1 -lt $words.Count) { $rest = @($words[($k + 1)..($words.Count - 1)]) }
    if ($leaf -match '^(python[0-9.]*|py|pythonw)$') {
        for ($a = 0; $a -lt $rest.Count; $a++) {
            if ($rest[$a].T -ne 'W') { return $false }
            $v = $rest[$a].V
            if ($v -eq '-m') { return ($a + 1 -lt $rest.Count -and $rest[$a + 1].V -match '(?i)^tools\.verify\.') }
            if ($v -eq '-c') { return ($a + 1 -lt $rest.Count -and $rest[$a + 1].V -match '(?i)tools[\\/.]verify') }
            if ($v -in @('-X', '-W')) { $a++; continue }
            if ($v.StartsWith('-')) { continue }
            return (Test-CheckerPath $v)
        }
        return $false
    }
    if ($leaf -in @('powershell', 'pwsh')) {
        for ($a = 0; $a -lt $rest.Count; $a++) {
            $v = "$($rest[$a].V)"
            if ($v -match '(?i)^-(File|f)$' -and $a + 1 -lt $rest.Count) { return (Test-CheckerPath $rest[$a + 1].V) }
            if ($v -match '(?i)^-(Command|c)$' -and $a + 1 -lt $rest.Count) {
                $text = ($rest[($a + 1)..($rest.Count - 1)] | ForEach-Object { if ($_.T -eq 'G') { '(' + $_.V + ')' } else { $_.V } }) -join ' '
                return (Invoke-Analysis $text 'ps' ($depth + 1))
            }
        }
        return $false
    }
    if ($leaf -in @('bash', 'sh', 'cmd')) {
        for ($a = 0; $a -lt $rest.Count; $a++) {
            if ("$($rest[$a].V)" -match '(?i)^(-c|/c)$' -and $a + 1 -lt $rest.Count) {
                $text = ($rest[($a + 1)..($rest.Count - 1)] | ForEach-Object { $_.V }) -join ' '
                return (Invoke-Analysis $text 'bash' ($depth + 1))
            }
        }
        return $false
    }
    if ($leaf -in @('iex', 'invoke-expression')) {
        if ($rest.Count -ge 1) {
            $text = ($rest | ForEach-Object { if ($_.T -eq 'G') { $_.V } else { $_.V } }) -join ' '
            return (Invoke-Analysis $text 'ps' ($depth + 1))
        }
        return $false
    }
    return (Test-CheckerPath $h)
}

function Get-SinkTarget($stage) {
    # What a sink stage writes: @{ Kind = 'file' | 'var' | 'none' | 'unknown'; V = ... }.
    # 'unknown' is a file-writing sink whose target this parser could not find - tracked as such.
    $w = @($stage.Words)
    $leaf = Get-Leaf $w[0].V
    $writes = $leaf -in @('out-file', 'set-content', 'add-content', 'tee-object', 'tee')
    for ($a = 1; $a -lt $w.Count; $a++) {
        $v = "$($w[$a].V)"
        if ($v -match '(?i)^-Variable$' -and $a + 1 -lt $w.Count) { return @{ Kind = 'var'; V = $w[$a + 1].V.TrimStart('$') } }
        if ($v -match '(?i)^-(FilePath|Path|LiteralPath)$' -and $a + 1 -lt $w.Count) { return @{ Kind = 'file'; V = $w[$a + 1].V } }
        if ($v -match '(?i)^-(FilePath|Path|LiteralPath):(.+)$') { return @{ Kind = 'file'; V = $Matches[2] } }
        if ($v.StartsWith('-')) { if ($v -match '(?i)^-(Encoding|Width|InputObject|Value)$') { $a++ }; continue }
        if ($writes) { return @{ Kind = 'file'; V = $v } }
        return @{ Kind = 'none' }
    }
    if ($writes) { return @{ Kind = 'unknown' } }
    return @{ Kind = 'none' }
}

function Test-Mentions($stage) {
    # Words only: a redirect TARGET is written, not read (`python a.py > x.log; python b.py > x.log`).
    foreach ($t in @($stage.Words)) {
        if ($null -eq $t) { continue }
        $v = "$($t.V)"; $nv = Get-Norm $v
        if ($nv -match '^-[\w]+:(.+)$') { $nv = Get-Norm $Matches[1] }
        foreach ($f in $script:taintFiles) { if ($nv -eq $f) { return $true } }
        foreach ($vn in $script:taintVars) { if ($v -match ('(?i)\$\{?' + [regex]::Escape($vn) + '\b')) { return $true } }
    }
    if ($script:taintUnknown -and $stage.Words.Count -gt 0 -and (Get-Leaf $stage.Words[0].V) -in $READERS) { return $true }
    return $false
}

function Test-WholeRead($stage) {
    $w = @($stage.Words)
    if ($w.Count -eq 0) { return $false }
    $leaf = Get-Leaf $w[0].V
    if ($leaf -in @('test-path', 'remove-item', 'rm', 'del')) { return $true }
    if ($w.Count -le 2 -and $leaf -in @('write-output', 'write-host', 'echo') -or ($w.Count -eq 1 -and $w[0].V -match '^\$')) {
        foreach ($vn in $script:taintVars) { if ($w[-1].V -match ('(?i)^\$\{?' + [regex]::Escape($vn) + '\}?$')) { return $true } }
    }
    if ($leaf -notin $WHOLE_READERS) { return $false }
    for ($a = 1; $a -lt $w.Count; $a++) {
        $v = "$($w[$a].V)"
        if ($v -match '(?i)^-(Raw)$') { continue }
        if ($v -match '(?i)^-(Encoding|Path|LiteralPath)$') { $a++; continue }
        if ($v.StartsWith('-')) { return $false }
    }
    return $true
}

function Set-Deny([string]$label) { if ($null -eq $script:denyLabel) { $script:denyLabel = $label } }

# Does a piece of command text name tracked output - a tracked file as a word, a tracked variable
# anywhere, or (when a sink's target was unknown) any reader at all?
function Test-TextMentions([string]$text, [string]$kind) {
    foreach ($vn in $script:taintVars) { if ($text -match ('(?i)\$\{?' + [regex]::Escape($vn) + '\b')) { return $true } }
    foreach ($t in (Get-Tokens $text $kind)) {
        if ($t.T -ne 'W') { continue }
        $nv = Get-Norm "$($t.V)"
        foreach ($f in $script:taintFiles) { if ($nv -eq $f) { return $true } }
        if ($script:taintUnknown -and (Get-Leaf $t.V) -in $READERS) { return $true }
    }
    return $false
}

# The file a reader stage reads: -Path/-LiteralPath, else the first positional word.
function Get-ReadPath($words) {
    $w = @($words)
    for ($a = 1; $a -lt $w.Count; $a++) {
        $v = "$($w[$a].V)"
        if ($v -match '(?i)^-(Path|LiteralPath)$' -and $a + 1 -lt $w.Count) { return "$($w[$a + 1].V)" }
        if ($v -match '(?i)^-(Tail|TotalCount|Head|First|Last|Encoding|ReadCount|Delimiter|n|c)$') { $a++; continue }
        if ($v.StartsWith('-')) { continue }
        return $v
    }
    return ''
}

# Analyses a command text. Returns $true when any stage in it produces checker output.
function Invoke-Analysis([string]$text, [string]$kind, [int]$depth) {
    if ($depth -gt 8) { $script:unparsed = $true; return $true }
    $expanding = @()
    if ($kind -eq 'bash') { $text = Remove-Heredocs $text ([ref]$expanding) }
    $produces = $false
    foreach ($e in $expanding) { if (Invoke-Analysis $e 'bash' ($depth + 1)) { $produces = $true } }
    $toks = Get-Tokens $text $kind

    # statements -> pipelines -> stages
    $pipelines = New-Object System.Collections.Generic.List[object]
    $cur = New-Object System.Collections.Generic.List[object]
    $stage = @{ Items = (New-Object System.Collections.Generic.List[object]); Redirs = (New-Object System.Collections.Generic.List[object]) }
    $pendingRd = $null
    foreach ($t in $toks) {
        if ($t.T -eq 'OP') {
            if ($null -ne $pendingRd) { $stage.Redirs.Add(@{ Op = $pendingRd.V; Target = $null }); $pendingRd = $null }
            $cur.Add($stage)
            $stage = @{ Items = (New-Object System.Collections.Generic.List[object]); Redirs = (New-Object System.Collections.Generic.List[object]) }
            if ($t.V -eq ';') { $pipelines.Add($cur); $cur = New-Object System.Collections.Generic.List[object] }
            continue
        }
        if ($t.T -eq 'RD') {
            if ($null -ne $pendingRd) { $stage.Redirs.Add(@{ Op = $pendingRd.V; Target = $null }) }
            if ($t.V.EndsWith('&') -or $t.V.StartsWith('<')) { $stage.Redirs.Add(@{ Op = $t.V; Target = $null; Merge = $true }); $pendingRd = $null }
            else { $pendingRd = $t }
            continue
        }
        if ($null -ne $pendingRd) { $stage.Redirs.Add(@{ Op = $pendingRd.V; Target = $t }); $pendingRd = $null; continue }
        $stage.Items.Add($t)
    }
    if ($null -ne $pendingRd) { $stage.Redirs.Add(@{ Op = $pendingRd.V; Target = $null }) }
    $cur.Add($stage); $pipelines.Add($cur)

    foreach ($pl in $pipelines) {
        $outFlows = $false   # checker output is flowing down this pipeline
        for ($si = 0; $si -lt $pl.Count; $si++) {
            $st = $pl[$si]
            $items = $st.Items.ToArray()
            $words = @($items | Where-Object { $_.T -eq 'W' })
            $st.Words = $words
            $st.Targets = @($st.Redirs.ToArray() | ForEach-Object { $_.Target } | Where-Object { $null -ne $_ })
            if ($items.Count -eq 0 -and $st.Redirs.Count -eq 0) { continue }

            # 1. groups and expanding quote text inside this stage are commands of their own
            $groupProduces = $false; $adjacentIndex = $false
            foreach ($it in $items) {
                if ($it.T -eq 'G') {
                    if (Invoke-Analysis $it.V $kind ($depth + 1)) { $groupProduces = $true; if ($it.Adj) { $adjacentIndex = $true } }
                    if ($it.Adj) {
                        # B2: an index or member access on a group that READS tracked output is the
                        # same cut - `(Get-Content o.log)[-5..-1]`, `($o)[-1]`, `(...).Substring(0,200)`.
                        if (Test-TextMentions $it.V $kind) { Set-Deny "an index or member access on the checker's captured output" }
                        $inner = @((Get-Tokens $it.V $kind) | Where-Object { $_.T -eq 'W' })
                        if ($inner.Count -gt 0 -and (Get-Leaf $inner[0].V) -in $LIMIT_READERS) {
                            $script:limitedReads.Add(@{ Path = (Get-ReadPath $inner); Label = "($($inner[0].V) ...)[index]" })
                        }
                    }
                }
                foreach ($sub in @($it.Subs)) { if ($sub -and (Invoke-Analysis $sub $kind ($depth + 1))) { $groupProduces = $true } }
            }

            # 2. an assignment prefix: `$x = ...` (PowerShell) / `x=$(...)` (bash)
            $assignVar = $null; $cmdItems = $items
            if ($items.Count -ge 2 -and $items[0].T -eq 'W' -and $items[0].V -match '^\$([\w:]+)$' -and $items[1].T -eq 'W' -and $items[1].V -in @('=', '+=')) {
                $assignVar = $Matches[1]; $cmdItems = @(); if ($items.Count -gt 2) { $cmdItems = @($items[2..($items.Count - 1)]) }
            } elseif ($items.Count -ge 1 -and $items[0].T -eq 'W' -and $items[0].V -match '^\$([\w:]+)\+?=$') {
                $assignVar = $Matches[1]; $cmdItems = @(); if ($items.Count -gt 1) { $cmdItems = @($items[1..($items.Count - 1)]) }
            } elseif ($items.Count -ge 1 -and $items[0].T -eq 'W' -and $items[0].V -match '^([A-Za-z_]\w*)=$' -and $kind -eq 'bash') {
                $assignVar = $Matches[1]
            }

            # 3. this stage against output already tracked (a later read of the checker's file/var)
            if (-not $outFlows -and (Test-Mentions $st)) {
                if (-not (Test-WholeRead $st)) { Set-Deny ("a partial read of the checker's captured output (" + $(if ($words.Count) { $words[0].V } else { '?' }) + ')') }
                for ($sj = $si + 1; $sj -lt $pl.Count; $sj++) {
                    $nx = @($pl[$sj].Items.ToArray() | Where-Object { $_.T -eq 'W' })
                    if ($nx.Count -eq 0 -or (Get-Leaf $nx[0].V) -notin $SINKS) {
                        Set-Deny ("| " + $(if ($nx.Count) { $nx[0].V } else { '?' }) + " after reading the checker's captured output"); break
                    }
                }
            }

            # 3b. a row-limited READ of any file, recorded for the post-pass (O4: a path spelled
            # differently from the tracked redirect must not escape - path matching fails closed).
            if (-not $outFlows -and $words.Count -gt 0 -and (Get-Leaf $words[0].V) -in $LIMIT_READERS) {
                $lim = (Get-Leaf $words[0].V) -in @('head', 'tail')
                foreach ($w in $words) { if ("$($w.V)" -match '(?i)^-(Tail|TotalCount|Head|First|Last)$') { $lim = $true } }
                if ($si + 1 -lt $pl.Count) {
                    $nx = @($pl[$si + 1].Items.ToArray() | Where-Object { $_.T -eq 'W' })
                    if ($nx.Count -gt 0 -and (Get-Leaf $nx[0].V) -in @('select-object', 'select') -and
                        @($nx | Where-Object { "$($_.V)" -match '(?i)^-(First|Last|Skip|Index)$' }).Count -gt 0) { $lim = $true }
                }
                if ($lim) { $script:limitedReads.Add(@{ Path = (Get-ReadPath $words); Label = $words[0].V }) }
            }

            # 4. does this stage produce checker output?
            $direct = $false
            if ($cmdItems.Count -gt 0) { $direct = Test-Invocation $cmdItems $kind $depth }
            if ($direct) { $script:invokeCount++ }
            $stageProduces = $direct -or $groupProduces
            if ($outFlows -and $si -gt 0) {
                if ($words.Count -eq 0 -or (Get-Leaf $words[0].V) -notin $SINKS) {
                    Set-Deny ("| " + $(if ($words.Count) { $words[0].V } else { '(...)' }))
                } else {
                    $tg = Get-SinkTarget $st
                    switch ($tg.Kind) {
                        'unknown' { $script:taintUnknown = $true }
                        'var'     { $script:taintVars.Add($tg.V) }
                        'file'    {
                            if ($tg.V -match $NULL_TARGET) { Set-Deny 'a sink that DISCARDS the checker output' }
                            $script:taintFiles.Add((Get-Norm $tg.V))
                        }
                    }
                }
            }
            if ($stageProduces) {
                $produces = $true
                if ($adjacentIndex) { Set-Deny 'an index or member access on the checker output' }
                if ($null -ne $assignVar) { $script:taintVars.Add($assignVar) }
                foreach ($rd in $st.Redirs) {
                    if ($rd.Merge) { continue }
                    if ($rd.Op -match '^(\d|\*|&)?>>?$' -or $rd.Op -match '^&>>?$') {
                        if ($null -eq $rd.Target) { $script:taintUnknown = $true; continue }
                        if ($rd.Target.V -match $NULL_TARGET) { Set-Deny 'a redirect that DISCARDS the checker output' }
                        $script:taintFiles.Add((Get-Norm $rd.Target.V))
                    }
                }
                $outFlows = $true
            }
        }
        if ($outFlows) { $produces = $true }
    }
    return $produces
}

# A throw anywhere in the analysis is an unreadable command, and it is DENIED - never a pass.
$ErrorActionPreference = 'Stop'
try {
    # TEST SEAM (O8): the control suite injects a throw to observe this branch. It can only ever
    # produce a DENY, so it opens nothing.
    if ($null -ne $data.tool_input.zp_selftest_throw) { throw 'selftest seam' }
    $null = Invoke-Analysis $cmd $KIND 0
} catch {
    Deny "BLOCKED (fail-closed): the hook could not analyse this command ($($_.Exception.Message)), so it cannot rule out a truncated checker run.`n`n$GUIDANCE"
}

# --- FAIL-CLOSED cross-check: the pre-tokeniser pattern over the MASKED text -----------------
# Quotes, here-strings, heredoc bodies and comments are blanked; an interpreter still visibly
# governing a tools/verify path that the parser did not attribute gets the strict reading.
$masked = $cmd
if ($KIND -eq 'bash') { $ignored = @(); $masked = Remove-Heredocs $masked ([ref]$ignored) }
$masked = [regex]::Replace($masked, "(?ms)@'\s*\r?\n.*?^'@", { param($m) ' ' * $m.Length })
$masked = [regex]::Replace($masked, '(?ms)@"\s*\r?\n.*?^"@', { param($m) ' ' * $m.Length })
$masked = [regex]::Replace($masked, "'[^']*'", { param($m) ' ' * $m.Length })
$masked = [regex]::Replace($masked, '"(?:[^"`\\]|[`\\].)*"', { param($m) ' ' * $m.Length })
$masked = [regex]::Replace($masked, '(?m)(^|\s)#.*$', { param($m) ' ' * $m.Length })
$regexHits = [regex]::Matches($masked, $RUN_PY).Count + [regex]::Matches($masked, $RUN_PS).Count
if ($regexHits -gt $script:invokeCount) {
    $first = [regex]::Match($masked, $RUN_PY); if (-not $first.Success) { $first = [regex]::Match($masked, $RUN_PS) }
    $tail = $masked.Substring($first.Index + $first.Length)
    foreach ($pm in [regex]::Matches($tail, '\|\s*([^\s|;&]+)')) {
        if ((Get-Leaf $pm.Groups[1].Value) -notin $SINKS) { Set-Deny ("| " + $pm.Groups[1].Value + ' (strict reading: an invocation the tokeniser did not attribute)'); break }
    }
    if ($tail -match '(?i)(^|\s)-(Tail|TotalCount|Head|First|Last|Skip|Index)\b') { Set-Deny ('-' + $Matches[2] + ' (strict reading)') }
}
# O4, FAIL-CLOSED ON PATH MATCHING: in a command that runs a checker, a row-limited read of ANY
# file is denied - a tracked redirect can be re-spelled (case, absolute, wildcard), and string
# equality cannot prove two spellings name different files. The one exception is build.log, which
# enforce_log_read_limits.ps1 REQUIRES be limited - unless this command redirected a checker into it.
if ($script:invokeCount -gt 0 -or $regexHits -gt 0) {
    foreach ($lr in $script:limitedReads) {
        $p = "$($lr.Path)"
        if ((Get-Leaf $p) -match '^build\.log' -and $p -notmatch '[*?]' -and -not $script:taintFiles.Contains((Get-Norm $p))) { continue }
        Set-Deny ("a row-limited read ($($lr.Label) $p) in a command that runs a checker")
        break
    }
}
if ($script:unparsed -and ($cmd -match $RUN_PY -or $cmd -match $RUN_PS)) {
    Set-Deny 'an unbalanced quote or bracket in a command that names a checker - the hook cannot tell where its output goes'
}

if ($null -eq $script:denyLabel) { exit 0 }

$snippet = $cmd.Trim()
if ($snippet.Length -gt 240) { $snippet = $snippet.Substring(0, 240) + ' ...' }
Deny @"
BLOCKED: this command runs a checker under tools/verify and does not keep its output whole ($($script:denyLabel)).

  $snippet

$GUIDANCE
"@
