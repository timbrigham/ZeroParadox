# block_git_gh.ps1
# PreToolUse hook - DENIES any Bash/PowerShell call that invokes `git` OR `gh`, and any call that
# reaches OUTSIDE this repository toward the MCP server projects.
#
# THE PROPERTY, stated once so every leg below can be checked against it:
#     an agent's shell command cannot reach raw git/gh, or the MCP server projects' source.
# Every leg is a ROUTE to that property. Controls: test_block_git_gh.ps1, one row per route,
# must-deny and must-allow.
#
# WHY THIS EXISTS ALONGSIDE THE DENY RULE.
# `permissions.deny` matches on the command PREFIX, so `Bash(git:*)` catches `git push` and misses
# every chained or prefixed form:
#       cd C:\Workspace\ZeroParadox; git add -A
#       Set-Location x; git reset --hard
#       cd /c/repo && gh release create v9.9
#       python -c "import subprocess; subprocess.run(['git','push'])"
# The matcher tests where the string STARTS; the property is whether the tool RUNS. This hook sees
# the whole command string.
#
# WHY `gh` AND NOT ONLY `git` (Tim, 2026-08-22: "potentially dangerous like git").
#   gh release create   -> mints a PERMANENT Zenodo DOI. Deposited files can never be withdrawn.
#   gh pr merge         -> lands code on main
#   gh api              -> arbitrary REST/GraphQL, including DELETE
#   gh issue/pr create, gh discussion comment -> public, outward-facing, governed by the Adversary
#                          Review Gate, which is a human decision and not a hook's
# Read access survives via mcp__github__* with no loss of sight.
#
# !! IT FAILS CLOSED. Unparseable input, empty stdin, a missing or non-string `command` field, a
# repo root that will not resolve -> DENY. An allow-on-error blocker is one with an undocumented
# bypass that opens exactly when something unexpected happens. This hook is registered on the Bash
# and PowerShell matchers only, and both tools always carry `tool_input.command`, so a payload
# without one is a shape this hook was never written for - which is the case fail-closed exists for.
#
# THE ROUTES, in the order they are tested:
#   1. CONTAINER legs - the command names a place ABOVE the repository. Not a list of protected
#      children: a list only closes the routes its author thought of, and a sibling added later
#      would arrive unprotected. Each leg is a property:
#        (a) protected literal  - names the server projects' directory outright
#        (b) ancestor           - after removing every in-repo `<parent>\<repo>` reference, a bare
#                                 `\<parent>` path segment remains. Checked for the parent of the
#                                 repo this script sits in (DERIVED from $PSScriptRoot, so a moved
#                                 repository still protects its own container - unless that repo
#                                 is a linked worktree, whose parent is the worktree area) AND for
#                                 the main checkout's known parent (a worktree copy of this script
#                                 sits under a different parent, and must still guard the real one).
#        (c) climb              - a `..` segment, the same property stated relatively.
#        (d) drive root         - `C:\`, `C:`, `/`, `\`, `$env:SystemDrive`, or a wildcard at the
#                                 first level below a drive root. A recursive sweep from a root
#                                 reaches the container without naming it, which is the RLY55-1
#                                 shape one level further up.
#   2. git/gh tokens - word-boundary `git` / `gh` anywhere in the string.
#   3. CARVE: arguments to one of this repo's own checkers are DATA. A command that is exactly one
#      `python tools/verify/<x>.py ...` invocation, with no shell operator outside quotes and no
#      expansion inside them, cannot run what its arguments spell; the checker receives the text.
#      This is the R-NOTINLIB sweep (`check_paths.py --claim "not in git"`), which the rule file
#      REQUIRES and this hook used to refuse. Checkers that use git internally are already allowed.
#   4. CARVE: the `.git` DIRECTORY. A reference to it is not an invocation, and reading it is not
#      raw git - but WRITING it is (a ref, a hook, the config). So a `.git` reference is allowed only
#      in a READ-ONLY SHAPE: one read verb, optionally piped to display-only consumers, no other
#      operator. Test-Path and Get-Content get the same answer.
#
# !! WHAT THIS DOES *NOT* CATCH, stated so nobody mistakes it for a seal:
#   - indirection:      $g = 'g' + 'it'; & $g push
#   - a script on disk: a .ps1/.py written first, then executed (its own command line is clean)
#   - encoded commands: powershell -EncodedCommand <base64>
#   - a path spelled without its ancestor: 8.3 short names, a substituted drive, a UNC share, a
#     junction. Each needs an actor to CONSTRUCT a spelling nobody types by accident.
#   - the Read / Glob / Grep TOOLS: they take a path, not a command, and this hook never sees them.
#     The Edit / Write / NotebookEdit half is block_corpus_edit.ps1's.
#   - the github MCP WRITE tools - a permissions decision, not a hook one.
#   - a registration that never loads this file. The hook is registered by a RELATIVE path, so it
#     resolves against the session's cwd; from a cwd with no tools\verify\claude_hooks beneath it
#     the registration exits 1 and the tool call proceeds. test_block_git_gh.ps1 measures that
#     separately and reports it as its own exit status.
# The threat model is DRIFT, not malice (Tim, 2026-09-09): a bypass needing deliberate effort is out
# of scope; a route taken WITHOUT intending to evade is in it.
#
# !! INTERNAL USE IS UNAFFECTED AND THAT IS DELIBERATE. `python tools/verify/batch.py precommit`
# shells out to git internally, but the COMMAND STRING contains no `git`, so it passes.

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

function Get-Snippet([string]$s) {
    $t = $s.Trim()
    if ($t.Length -gt 200) { $t = $t.Substring(0, 200) + ' ...' }
    return $t
}

$GUIDANCE = @'
DIRECT `git` AND `gh` ARE BLOCKED for agents in this repository.

WHAT TO USE INSTEAD:
  - git           -> the gitRobot MCP server (mcp__gitRobot__*), which mediates all git for this
                     tree: destructive ops refused, mutating ops gated and audited, reads passed
                     through. `mcp__gitRobot__read(op=...)` for any read.
  - GitHub reads  -> the github MCP tools (mcp__github__*) are registered and still available.
  - a release     -> Tim. Releases are permanent; that is a human decision, not an agent one.

If gitRobot is not yet running, git is unavailable to you. That is intentional, not a fault.
Do NOT work around this - no aliases, no wrapper scripts, no shelling out from python. If you
believe you genuinely need it, say so and let Tim decide.

Note: tools that use git INTERNALLY are unaffected. `python tools/verify/batch.py precommit`,
the checkers and the build scripts all still work, and text passed AS AN ARGUMENT to one of
those checkers (e.g. `check_paths.py --claim "..."`) is data, not an invocation.

WHY, AND WHAT WOULD REOPEN EACH BLOCK:
  mcp__gitRobot__requirements(action='push') - served by the server itself, callable from a
  spawned agent: the routing map and the exclusion rationale.
  docs://gitrobot/readme - the same server's design notes, for a session that can read resources.
'@

if ([string]::IsNullOrWhiteSpace($raw)) {
    Deny "BLOCKED (fail-closed): the hook received empty input and cannot tell what was requested.`n`n$GUIDANCE"
}

try { $data = $raw | ConvertFrom-Json } catch {
    Deny "BLOCKED (fail-closed): the hook could not parse its input, so it cannot rule out a git/gh call.`n`n$GUIDANCE"
}

# RLY-HOOKNUL-1: a missing, non-string or blank command is DENIED, never waved through. The
# registered matchers (Bash, PowerShell) always carry one, so its absence is the unknown case.
$cmd = $null
if ($null -ne $data -and $null -ne $data.tool_input) { $cmd = $data.tool_input.command }
if (-not ($cmd -is [string]) -or [string]::IsNullOrWhiteSpace($cmd)) {
    Deny "BLOCKED (fail-closed): the hook found no command string in tool_input.command, so it cannot rule out a git/gh call.`n`n$GUIDANCE"
}

# ---------------------------------------------------------------------------
# 1. CONTAINER legs.
# ---------------------------------------------------------------------------
$PROTECTED_PATH = 'mcp-mayhem'   # the server projects' directory, beside the main checkout
# (parent leaf, repo leaf) pairs. The main checkout's is known; this copy's own is DERIVED, so a
# moved repository or a worktree copy still guards the directory it actually sits in (RLY55-9).
$pairs = @(@{ Parent = 'Workspace'; Repo = 'ZeroParadox' })
try {
    $repoRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..\..') -ErrorAction Stop).Path.TrimEnd('\')
    $derivedRepo   = Split-Path -Leaf $repoRoot
    $derivedParent = Split-Path -Leaf (Split-Path -Parent $repoRoot)
    if ([string]::IsNullOrWhiteSpace($derivedRepo) -or [string]::IsNullOrWhiteSpace($derivedParent)) { throw 'empty leaf' }
} catch {
    Deny "BLOCKED (fail-closed): the hook could not derive the repository root from its own location, so it cannot tell what lies outside it.`n`n$GUIDANCE"
}
# A linked WORKTREE carries `.git` as a FILE (a gitdir pointer); its parent is the worktree area,
# which holds other checkouts, not the server projects. Only a checkout whose `.git` is not a file
# guards its own parent - a missing `.git` errs toward guarding.
$isWorktree = Test-Path -LiteralPath (Join-Path $repoRoot '.git') -PathType Leaf
if (-not $isWorktree -and -not ($derivedParent -eq 'Workspace' -and $derivedRepo -eq 'ZeroParadox')) {
    $pairs += @{ Parent = $derivedParent; Repo = $derivedRepo }
}

$END = '(?=[/\\"''\s;|&),]|$)'   # the end of a path segment
$leg = $null
if ($cmd -match [regex]::Escape($PROTECTED_PATH)) {
    $leg = "it names the protected tree ($PROTECTED_PATH)"
}
if ($null -eq $leg) {
    foreach ($pr in $pairs) {
        $p = [regex]::Escape($pr.Parent); $r = [regex]::Escape($pr.Repo)
        $residual = [regex]::Replace($cmd, "$p[/\\]+$r$END", '', 'IgnoreCase')
        if ($residual -match "[/\\]$p(?![A-Za-z0-9_-])") {
            $leg = "it references $($pr.Parent), the directory ABOVE this repository"; break
        }
    }
}
# A `..` path token, WHATEVER FOLLOWS it (B3: `cd ..; ...`, `cd ..&& ...`, `(cd ..)`, `.., x`).
# The test names what makes it a NON-climb - a word char or a dot on either side (`...`, `x..`,
# PowerShell's `1..5`, `..foo`) - rather than listing what may come after one.
if ($null -eq $leg -and $cmd -match '(?<![A-Za-z0-9_.])\.\.(?![A-Za-z0-9_.])') {
    $leg = "it climbs above the current directory with a '..' segment"
}
if ($null -eq $leg) {
    $ROOT_END = '(?=\s*$|\s*[;&|)<>,]|\s+-|["''])'
    if ($cmd -match "(?<![\w])[A-Za-z]:[\\/]*\*?$ROOT_END" -or
        $cmd -match '(?<![\w])[A-Za-z]:[\\/]+[^\\/\s"'';|&()]*[*?]' -or
        # A bare `/` or `\` (or `/c/`) as a whole WORD - preceded by whitespace or the start, and
        # never quote-delimited, so `-replace '\\', '/'` and `-split '/'` stay clear.
        $cmd -match '(?:^|(?<=\s))[/\\](?:[A-Za-z][/\\]?)?\*?(?=\s*$|\s*[;&|)<>]|\s+-)' -or
        $cmd -match '\$env:(SystemDrive|HOMEDRIVE)\b(?![\\/]+[\w.-])') {
        $leg = 'it names a DRIVE ROOT, and a sweep from there reaches the directory above this repository'
    }
}
if ($null -ne $leg) {
    $snip = Get-Snippet $cmd
    Deny @"
BLOCKED: this command reaches OUTSIDE the repository - $leg.

  $snip

The directory above this repo also holds the MCP SERVER PROJECTS. They hold the enforcement code
that constrains you - gitRobot mediates every git action, verdictLedger holds the verdicts that
gate a commit. An agent able to edit them can switch off its own guard, so a ZeroParadox session
stays inside ZeroParadox. The guard denies the CONTAINER rather than a list of names, because a
list only ever closes the routes its author thought of.

WHAT TO USE INSTEAD:
  - to USE the servers    -> mcp__gitRobot__* and mcp__verdictLedger__*
  - to READ their design  -> mcp__gitRobot__requirements / mcp__verdictLedger__requirements, or
                             docs://gitrobot/readme and docs://verdictledger/readme
  - to CHANGE them        -> an MCP-development session, which is scoped to that work. Not this one.
  - a path outside the repo for an ordinary reason -> spell it absolutely, from a directory that is
                             not an ancestor of this repo (the scratchpad, a worktree); never climb
                             with '..' and never sweep from a drive root.

If you believe a task genuinely requires it, STOP and say so - do not route around this with a
script on disk, an alias, or an encoded command.
"@
}

# ---------------------------------------------------------------------------
# 2. git / gh tokens. Word-boundary, so ordinary words are not false positives:
#   .gitignore / .gitattributes / github -> `git` followed by a word char, no match
#   digit / legitimate / logit           -> `git` preceded by a word char, no match
#   high / enough / through              -> `gh` has a word char on one side, no match
#   git / git.exe / gh / gh.exe / 'gh'   -> MATCH
# ---------------------------------------------------------------------------
$hitGit = $cmd -match '\bgit\b'
$hitGh  = $cmd -match '\bgh\b'
if (-not ($hitGit -or $hitGh)) { exit 0 }

# ---------------------------------------------------------------------------
# 3. CARVE: the text is an ARGUMENT to one of this repo's checkers (RLY55-4).
# The whole command must be: [Set-Location <arg>;] python <flags> <...>tools/verify/<x>.py <args>
# [redirects]. An <arg> is single-quoted (no expansion in either shell), double-quoted with no `$`,
# backtick or backslash (so nothing inside it expands or escapes), or a bare word with no shell
# operator. Spaces and tabs only between words - a newline would start a second statement.
# ---------------------------------------------------------------------------
$ARG = '(?:''[^'']*''|"[^"$`\\]*"|[^\s;&|`$()<>''"{}]+)'
$WS  = '[ \t]'
# A redirect TARGET may also name a variable (`> "$sp\out.log"`), never a subexpression or a block.
$RARG = '(?:''[^'']*''|"(?:[^"$`(){}]|\$\w+)*"|\$?[^\s;&|`$()<>''"{}]+)'
# The script must be THIS repository's checker: relative (`tools/...`, `./tools/...`) or under the
# main checkout or this copy's own root - never a `tools\verify` directory anywhere else on disk.
function ConvertTo-RootPattern([string]$root) { return ([regex]::Escape($root.TrimEnd('\')) -replace '\\\\', '[\\/]') + '[\\/]' }
$PATH_PREFIX  = '(?:\.[\\/]|' + (ConvertTo-RootPattern 'C:\Workspace\ZeroParadox') + '|' + (ConvertTo-RootPattern $repoRoot) + ')?'
$CHECKER_ONLY = '^' + $WS + '*(?:(?:Set-Location|cd)' + $WS + '+' + $ARG + $WS + '*;' + $WS + '*)?' +
                # interpreter flags, but never -c (inline code runs instead of the checker)
                '(?:python3?|py)(?:\.exe)?(?:' + $WS + '+-(?![cC])[A-Za-z]\w*)*' + $WS + '+' +
                '(?:' + $PATH_PREFIX + 'tools[\\/]verify[\\/][\w.\\/-]+\.py' +
                '|''' + $PATH_PREFIX + 'tools[\\/]verify[\\/][\w.\\/-]+\.py''' +
                '|"' + $PATH_PREFIX + 'tools[\\/]verify[\\/][\w.\\/-]+\.py")' +
                '(?:' + $WS + '+' + $ARG + ')*' +
                '(?:' + $WS + '*(?:[12*]?>>?)' + $WS + '*' + $RARG + ')*' +
                '(?:' + $WS + '*2>&1)?' + $WS + '*$'
# O1: never for a command that names the .git directory - a redirect target or an `--out` argument
# there would WRITE it, which carve 4 below exists to refuse.
if ($cmd -match $CHECKER_ONLY -and $cmd -notmatch "\.git$END") { exit 0 }

# ---------------------------------------------------------------------------
# 4. CARVE: the .git DIRECTORY, in a READ-ONLY SHAPE only (RLY55-5).
# Remove every `.git` directory reference; if no git/gh token is left, the command touches the
# directory without invoking anything - allowed when it is one read verb, optionally piped to
# display-only consumers, and nothing else. A write into .git (a hook, a ref, the config) is raw
# git by another name and is denied.
# ---------------------------------------------------------------------------
$residual = [regex]::Replace($cmd, "\.git$END", '', 'IgnoreCase')
if ($residual -notmatch '\bgit\b' -and $residual -notmatch '\bgh\b') {
    $READ_VERB = '(?:Get-Content|gc|cat|type|Test-Path|Get-ChildItem|gci|ls|dir|Get-Item|Select-String|sls|head|tail|Resolve-Path|rg|grep|Get-FileHash)'
    # No `sort`: in bash that is GNU sort, and `sort -o <file>` WRITES (O2). Sort-Object stays.
    $VIEW_SINK = '(?:Select-Object|select|Select-String|sls|Measure-Object|measure|Format-List|Format-Table|fl|ft|Out-String|Sort-Object|head|tail|grep|rg|wc|Out-Host)'
    $SEG = '[^;&|`$()<>{}\r\n]*'
    $READ_ONLY = "^\s*$READ_VERB(?![\w-])$SEG(?:\|\s*$VIEW_SINK(?![\w-])$SEG)*$"
    if ($cmd -match $READ_ONLY) { exit 0 }
    $snip = Get-Snippet $cmd
    Deny @"
BLOCKED: this command touches the .git directory in a form this hook cannot confirm is a READ.

  $snip

Reading .git is allowed in a read-only shape - one read verb (Get-Content, Test-Path,
Get-ChildItem, Select-String, ...), optionally piped to display-only consumers. Writing it - a
hook, a ref, the config - is raw git by another name: it can disarm the pre-push gate or move a
branch without gitRobot seeing it.

$GUIDANCE
"@
}

$which = if ($hitGit -and $hitGh) { 'git and gh' } elseif ($hitGit) { 'git' } else { 'gh' }
$snippet = Get-Snippet $cmd
Deny "BLOCKED: this command invokes $which.`n`n  $snippet`n`n$GUIDANCE"
