# block_git_gh.ps1
# PreToolUse hook - DENIES any Bash/PowerShell call that invokes `git` OR `gh`, anywhere in the
# command string. (Renamed from block_git.ps1 on 2026-08-22 when `gh` was added; the old name
# would have been a lie, and a stale name is how a guard stops being read.)
#
# WHY THIS EXISTS ALONGSIDE THE DENY RULE.
# `permissions.deny` matches on the command PREFIX, so `Bash(git:*)` catches `git push` and misses
# every chained or prefixed form:
#       cd C:\Workspace\ZeroParadox; git add -A
#       Set-Location x; git reset --hard
#       cd /c/repo && gh release create v9.9
#       python -c "import subprocess; subprocess.run(['git','push'])"
# Same proxy-for-property defect this project keeps measuring: the matcher tests where the string
# STARTS, the property is whether the tool RUNS. This hook sees the whole command string.
#
# WHY `gh` AND NOT ONLY `git` (Tim, 2026-08-22: "potentially dangerous like git").
# `gh` reaches further than `git push` does, and reaches things that cannot be undone:
#   gh release create   -> mints a PERMANENT Zenodo DOI. Deposited files can never be withdrawn.
#   gh pr merge         -> lands code on main
#   gh api              -> arbitrary REST/GraphQL, including DELETE
#   gh issue/pr create, gh discussion comment -> public, outward-facing, and governed by the
#                          Adversary Review Gate, which is a human decision and not a hook's
# Blocking `gh` is CHEAP here in a way blocking git was not: the github MCP server is already
# registered for this project, so read access survives via mcp__github__* with no loss of sight.
#
# ⚠ IT FAILS CLOSED, AND THAT INVERTS THE CONVENTION OF EVERY OTHER HOOK HERE ON PURPOSE.
# The others are `catch { exit 0 }` - allow on error. That was measured biting the retired
# gate-lock hook: a path-normalisation throw hit its catch and "the lock never fired." An allow-on-error
# blocker is not a blocker; it is one with an undocumented bypass that opens exactly when something
# unexpected happens. Unparseable input, empty stdin, a missing field -> DENY.
#
# ⚠ WHAT THIS DOES *NOT* CATCH, stated so nobody mistakes it for a seal:
#   - indirection:      $g = 'g' + 'it'; & $g push
#   - a script on disk: a .ps1/.py written first, then executed (its own command line is clean)
#   - encoded commands: powershell -EncodedCommand <base64>
#   - the github MCP WRITE tools (create_pull_request, push_files, create_or_update_file,
#     merge_pull_request, issue_write, discussion_comment_write) - those bypass this hook AND the
#     git gate entirely by writing straight to the remote. Closing that is a permissions decision,
#     not a hook one. SEE THE NOTE IN C:\temp\gitRobot.md.
# The threat model is DRIFT, not malice. Against that this works; against an agent deciding to route
# around it, it does not. The only sound layer remains remote (branch protection + required status
# checks), and `illustrated` currently has none. This is defence in depth, not a seal.
#
# ⚠ INTERNAL USE IS UNAFFECTED AND THAT IS DELIBERATE. `python tools/verify/batch.py precommit`
# shells out to git internally, but the COMMAND STRING contains no `git`, so it passes. Checkers,
# hooks and build scripts keep working. Only an agent typing git/gh directly is stopped.

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
DIRECT `git` AND `gh` ARE BLOCKED for agents in this repository.

git was denied because a pre-push hook is the only gate on publication and one flag disables it,
and because `git reset --hard`, `checkout -- .`, `clean` and `stash` fire no hook at all - one of
those silently destroyed an uncommitted edit here and then reported success.

gh was denied because it reaches further and less reversibly: `gh release create` mints a PERMANENT
Zenodo DOI, `gh pr merge` lands code on main, and `gh api` is arbitrary REST including DELETE.
Public-facing actions are also governed by the Adversary Review Gate, which is Tim's decision.

WHAT TO USE INSTEAD:
  - GitHub reads  -> the github MCP tools (mcp__github__*) are registered and still available.
  - git           -> the gitRobot MCP server (mcp__gitRobot__*), which mediates all git for this
                     tree: destructive ops refused, mutating ops gated and audited, reads passed
                     through. Definition: C:\temp\gitRobot.md
  - a release     -> Tim. Releases are permanent; that is a human decision, not an agent one.

If gitRobot is not yet running, git is unavailable to you. That is intentional, not a fault.
Do NOT work around this - no aliases, no wrapper scripts, no shelling out from python. If you
believe you genuinely need it, say so and let Tim decide.

WHY EACH THING IS DENIED, AND WHAT WOULD REOPEN IT:
  .claude-local/notes/access_controls_2026-08-22.md  (private working folder; absent from a public
  clone - the method is public, some of the material it operates on is not)
Read it before arguing the block is wrong - several of these are provisional, not permanent.

Note: tools that use git INTERNALLY are unaffected. `python tools/verify/batch.py precommit`,
the checkers and the build scripts all still work.
'@

if ([string]::IsNullOrWhiteSpace($raw)) {
    Deny "BLOCKED (fail-closed): the hook received empty input and cannot tell what was requested.`n`n$GUIDANCE"
}

try { $data = $raw | ConvertFrom-Json } catch {
    Deny "BLOCKED (fail-closed): the hook could not parse its input, so it cannot rule out a git/gh call.`n`n$GUIDANCE"
}

$cmd = $data.tool_input.command
if ($null -eq $cmd) { exit 0 }   # not a command-bearing tool; nothing to inspect

# ---------------------------------------------------------------------------
# PROTECTED SERVER PROJECTS (added 2026-08-23, Tim)
#
# An agent that can WRITE under `mcp-mayhem` can edit gitRobot's or
# verdictLedger's source and neuter the guard that constrains it. That is the
# bypass this whole layer exists to prevent, and until today the folder was
# protected only by nobody mentioning it - which failed: a sweep found 14
# pointers toward it in files a session reads, most of them written the same day
# by the instance that was being constrained.
#
# ⚠ DENY THE WHOLE PATH, NOT A LIST OF WRITE-VERBS. Enumerating Set-Content /
# Out-File / > / Add-Content / Move-Item / Remove-Item / a python one-liner is
# the proxy-for-property defect this file's own header already describes: the
# matcher would test HOW the string writes, the property is WHETHER the tree can
# be reached. Same reasoning that denies the `git` verb rather than its
# subcommands.
#
# ⚠ WHAT THIS DOES NOT COVER, stated so nobody mistakes it for a seal:
#   - the Read / Edit / Write / NotebookEdit TOOLS. This hook is registered on
#     Bash and PowerShell and only ever sees `tool_input.command`; covering
#     file_path-bearing tools needs a second registration, which is a settings
#     change and Tim's to make. THE WRITE HALF IS THE ONE THAT MATTERS - a
#     shell block alone still leaves Edit/Write able to reach the same files.
#   - reading is deliberately not the target. Use the Read tool; the specs in
#     C:\temp are the approved interaction path and are NOT blocked here.
$PROTECTED_PATH = '(?i)mcp-mayhem'
if ($cmd -match $PROTECTED_PATH) {
    $snip = $cmd.Trim()
    if ($snip.Length -gt 200) { $snip = $snip.Substring(0, 200) + ' ...' }
    Deny @"
BLOCKED: this command reaches the MCP SERVER PROJECTS.

  $snip

Those projects hold the enforcement code that constrains you - gitRobot mediates
every git action, verdictLedger holds the verdicts that gate a commit. An agent
able to edit them can switch off its own guard, so a ZeroParadox session does not
go there.

WHAT TO USE INSTEAD:
  - to USE the servers    -> mcp__gitRobot__* and mcp__verdictLedger__*
  - to READ their design  -> C:\temp\gitRobot.md and C:\temp\verdictLedger.md.
                             That two-hop is the APPROVED interaction path.
  - to CHANGE them        -> an MCP-development session, which is scoped to that
                             work. Not this one.

If you believe a task genuinely requires it, STOP and say so - do not route
around this with a script on disk, an alias, or an encoded command.
"@
}

# Word-boundary match, so ordinary words are not false positives:
#   .gitignore / .gitattributes / github -> `git` followed by a word char, no match
#   digit / legitimate / logit           -> `git` preceded by a word char, no match
#   high / enough / through              -> `gh` has a word char on one side, no match
#   git / git.exe / gh / gh.exe / 'gh'   -> MATCH, which is what we want
$hitGit = $cmd -match '(?i)\bgit\b'
$hitGh  = $cmd -match '(?i)\bgh\b'
if (-not ($hitGit -or $hitGh)) { exit 0 }

# A bare reference to the .git DIRECTORY is a read, not an invocation - e.g.
#   Get-Content .git/hooks/pre-push
# Allow it ONLY when removing every such reference leaves no bare token behind.
if ($hitGit -and -not $hitGh) {
    $residual = [regex]::Replace($cmd, '(?i)\.git[/\\]', '')
    if ($residual -notmatch '(?i)\bgit\b') { exit 0 }
}

$which = if ($hitGit -and $hitGh) { 'git and gh' } elseif ($hitGit) { 'git' } else { 'gh' }
$snippet = $cmd.Trim()
if ($snippet.Length -gt 200) { $snippet = $snippet.Substring(0, 200) + ' ...' }

Deny "BLOCKED: this command invokes $which.`n`n  $snippet`n`n$GUIDANCE"
