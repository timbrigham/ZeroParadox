# block_corpus_edit.ps1
# PreToolUse hook - DENIES Edit / Write / NotebookEdit against the CORPUS AND PUBLISHED SURFACES
# inside the SHARED CHECKOUT. Ruled by Tim, 2026-09-19.
#
# WHY THIS EXISTS.
# Tim, 2026-09-19: "Edits should no longer be made by the main instance right, that should be a
# delegated responsibility??? That's the whole idea of the git worktree." Then, when told it had
# happened again immediately after a deliberate fresh clear: "This is a standing problem in the
# workflow."
#
# The diagnosis was NOT a forgotten rule. There is no such rule in CLAUDE.md - 45 sections, and
# `orchestrat|delegat|worktree|main instance|author` returns only R-BRIEF, whose TRIGGER is "you are
# delegating to a spawned agent" (it fires AFTER the decision, so it cannot cause one) and whose
# worktree line binds the spawned agent rather than the caller. The discipline lived in three places
# and all three missed:
#   1. .claude/commands/copy-editor.md - the CARRIER role, scoped to multi-agent REVIEWS.
#   2. a memory whose own description scopes it to "a multi-agent review". R-BRIEF's cost line:
#      memory BODIES never arrive, only the index - one line among a hundred.
#   3. queue/HOW_THIS_WORKS.md's `## Protocol` block, which states outright that "the main instance
#      is the only actor here that gets none [no brief]" and that the TICKET closes that gap.
#      It was absent, because the handoff routed to work that HAS NO TICKET.
# So the actor behaved like one with no brief, because it was one. A fourth prose rule would have
# been the "say it louder" move R-RECUR forbids. This is the R-ROBOT pattern instead: make it
# structural, the way direct `git` was made structural rather than discouraged.
#
# ** THE DISCRIMINATOR IS THE PATH, NOT THE ACTOR - AND THAT IS THE WHOLE DESIGN. **
# `mcp__gitRobot__worktree(action='add')` hands out a detached checkout in a scratch area OUTSIDE the
# repository, with its own HEAD, index and working tree. So a DELEGATED agent editing its worktree
# writes to a path that is not under the main checkout at all, and passes this hook untouched, with
# no flag to set and nothing to detect. Delegation is not merely permitted by this guard; it is the
# path of least resistance through it. That is why no subagent-detection is attempted here: there is
# no reliable field for it, and keying on one would be a proxy for the property that actually
# matters, which is WHICH TREE IS BEING MUTATED.
#
# Corollary, and it is intended: a subagent that edits the SHARED checkout is denied too. That
# already matches the written rules - R-BRIEF says an agent needing commits works in a worktree
# "never the shared checkout", and review gates are read-only on the working tree.
#
# ** IT FAILS CLOSED, matching block_git_gh.ps1 and inverting the other hooks here on purpose. **
# Unparseable input, empty stdin, a path that will not resolve -> DENY. An allow-on-error blocker is
# not a blocker; it is one with an undocumented bypass that opens exactly when something unexpected
# happens. That was measured biting the retired gate-lock hook.
#
# ** WHAT IS DELIBERATELY NOT COVERED - stated so nobody mistakes this for a seal. **
#   - tools/** and CLAUDE.md are NOT denied. Tim was offered a wider scope that added "the rule file
#     and the checkers" and declined it, choosing "Corpus + published surfaces only".
#     ** RESIDUAL, NAMED RATHER THAN HIDDEN: this hook lives under tools/, so the scope chosen leaves
#     the guard editable by the actor it constrains. ** That is the same shape as the mcp-mayhem
#     carve in block_git_gh.ps1, and the honest statement is that this is defence against DRIFT, not
#     against an agent deciding to route around it. Reopening it is a one-line change to
#     $PROTECTED below plus a settings entry; it is Tim's call, not a hook's.
#   - .claude-local/** is NOT denied. Ruled explicitly: notes, tickets, DEFECTS.md and the handoff
#     stay the main instance's to write.
#   - the SHELL. Set-Content / Out-File / a python one-liner reach these same files and are not seen
#     here; this hook only ever inspects tool_input paths. block_git_gh.ps1's header records the
#     mirror-image gap from the other side. Closing the shell half means a path matcher on
#     Bash/PowerShell, which is a separate change with its own false-positive surface.
#   - indirection, an encoded command, or a script written first and executed second.
# The threat model is DRIFT, not malice.

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
CORPUS AND PUBLISHED-SURFACE EDITS ARE DELEGATED WORK in this repository. The main instance
orchestrates; it does not author here.

WHAT TO DO INSTEAD:
  1. `mcp__gitRobot__worktree(action='add')` - a private detached checkout OUTSIDE this repo.
  2. Spawn an agent with a brief carrying its rules VERBATIM (R-BRIEF), pointed at that worktree.
     A ticket in .claude-local/queue/ with a `## Protocol` block IS that brief - see
     queue/HOW_THIS_WORKS.md.
  3. Carry back ARTIFACTS - the worktree path, the commit SHA, the diff. Never a summary of them.
     A carrier that paraphrases has rebuilt the translation step the role exists to delete.
  4. Run the gates (/editorial-review, /adversary-review) as FRESH agents on that diff.
  5. Merge the worktree's SHA: `mcp__gitRobot__merge(branch=<sha>, reason=...)`.

WHY: the main instance is the only actor in this workflow that receives no brief - every spawned
agent gets one, and the ambient CLAUDE.md is the "only in memory" condition R-BRIEF declares
insufficient. Editing from here is the one act with no independent reader in front of it.

WHAT IS STILL YOURS, and is not affected by this hook:
  - .claude-local/**  - notes, queue tickets, DEFECTS.md, DEFECT_CLASSES.md, the handoff
  - tools/**          - the checkers and hooks
  - CLAUDE.md         - the rule file
  - the session scratchpad, and ANY path outside this checkout (which is where worktrees live)

If a task genuinely needs a direct edit here - a one-character fix you have been asked for by name -
STOP and say so, and let Tim decide. Do not route around this with the shell, a script on disk, or
by writing the file from python.
'@

if ([string]::IsNullOrWhiteSpace($raw)) {
    Deny "BLOCKED (fail-closed): the hook received empty input and cannot tell what was requested.`n`n$GUIDANCE"
}

try { $data = $raw | ConvertFrom-Json } catch {
    Deny "BLOCKED (fail-closed): the hook could not parse its input, so it cannot rule out a corpus edit.`n`n$GUIDANCE"
}

# Edit and Write carry `file_path`; NotebookEdit carries `notebook_path`. Both are documented
# absolute. A call bearing neither is not a file mutation this hook has any business inspecting.
$target = $data.tool_input.file_path
if ([string]::IsNullOrWhiteSpace($target)) { $target = $data.tool_input.notebook_path }
if ([string]::IsNullOrWhiteSpace($target)) { exit 0 }

# The repo root is this script's own location, three levels up - derived, never hard-coded, so a
# clone or a move cannot leave the guard pointing at a directory that no longer exists.
$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path.TrimEnd('\')

# Normalise WITHOUT requiring existence: a Write to a new file must be judged the same as an Edit to
# an existing one. Resolve-Path throws on a missing leaf, so it cannot be used here.
try {
    if ([System.IO.Path]::IsPathRooted($target)) {
        $full = [System.IO.Path]::GetFullPath($target)
    } else {
        $cwd = $data.cwd
        if ([string]::IsNullOrWhiteSpace($cwd)) { $cwd = $repoRoot }
        $full = [System.IO.Path]::GetFullPath((Join-Path $cwd $target))
    }
} catch {
    Deny "BLOCKED (fail-closed): the hook could not resolve the target path '$target', so it cannot tell whether it is in the corpus.`n`n$GUIDANCE"
}

# OUTSIDE the shared checkout -> allow. This is the worktree route, and the scratchpad, and is the
# single most important line in the file: it is what makes delegation pass automatically.
$cmp = [StringComparison]::OrdinalIgnoreCase
if (-not $full.StartsWith($repoRoot + [System.IO.Path]::DirectorySeparatorChar, $cmp)) { exit 0 }

$rel = $full.Substring($repoRoot.Length + 1)

# Explicit carves, evaluated BEFORE the protected set so their precedence is visible rather than
# emergent from regex ordering.
if ($rel.StartsWith('.claude-local\', $cmp)) { exit 0 }
if ($rel.StartsWith('tools\',         $cmp)) { exit 0 }
if ($rel.Equals('CLAUDE.md',          $cmp)) { exit 0 }

# The protected set. Each entry is a SURFACE A READER CAN REACH, which is the property; the globs
# are the proxy, so keep them boring and overlapping rather than clever.
$PROTECTED = @(
    @{ Pattern = '^ZeroParadox\\';       What = 'the Lean corpus' }
    @{ Pattern = '^scripts\\';           What = 'a PDF build script' }
    @{ Pattern = '^[^\\]+\.md$';         What = 'a root-level published document' }
    @{ Pattern = '\.pdf$';               What = 'a rendered PDF' }
    # R-EXEMPT names these explicitly as NOT exempt: "the gate briefs are published deliberately,
    # as the artifact showing how this project reviews itself, so both gates fire on them." A
    # published surface is exactly what this hook protects, so they belong here. Note the regex
    # requires a backslash straight after `claude`, so `.claude-local\` cannot match it.
    @{ Pattern = '^\.claude\\commands\\'; What = 'a published gate brief' }
)

foreach ($p in $PROTECTED) {
    if ($rel -match ('(?i)' + $p.Pattern)) {
        Deny @"
BLOCKED: this would edit $($p.What) directly in the shared checkout.

  $rel

$GUIDANCE
"@
    }
}

exit 0
