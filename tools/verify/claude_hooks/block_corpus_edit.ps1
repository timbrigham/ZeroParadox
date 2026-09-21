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
# ================================================================================================
# ** THE LIST IS INVERTED. INSIDE THE CHECKOUT, DENY IS THE DEFAULT. ** (GUARD-2, 2026-09-20.)
# ================================================================================================
# This file used to carry a list of PROTECTED globs, with its own comment admitting the globs were
# "the proxy" for a property it stated as "a SURFACE A READER CAN REACH". The proxy and the property
# came apart, and the measurement is the reason this section is written the way it is: feeding every
# tracked reader-served path through the LIVE hook returned **23 ALLOW against 11 DENY over 34
# paths**, and only three of those 23 were carves anybody had ruled. Allowed, and unnamed anywhere in
# this header: the three published `.html` pages served at zeroparadox.org, `_layouts/default.html`
# which wraps every rendered `.md` page, `_config.yml`, `CNAME`, `.zenodo.json` (the permanent DOI
# record), `.claude/settings.json` (this guard's own registration), `gate_round.json`, `ssot.json`,
# the lake build pins, `.github/**`, `LICENSE` - and `ZeroParadox.lean`, THE ROOT MODULE OF THE LEAN
# LIBRARY, because `^ZeroParadox\` demands a separator after the name so it matched the directory and
# not the file beside it. `README.md` was denied while `bottom-family-tree.html`, served to the same
# reader from the same domain, was allowed.
#
# ** A GLOB LIST IS A DENYLIST, AND A DENYLIST IS POROUS BY CONSTRUCTION: every fix closes the cut
# its author thought of, and every file added to the repository afterwards arrives UNPROTECTED and
# INVISIBLE. ** That is R-TRUNC's recorded ruling on block_checker_truncation.ps1, in the same
# directory, after 15 of 19 filters walked through its list - "THE FIX IS TO INVERT". It is also
# check_paths.py's, which replaced a hand-written root list with `git ls-files` and wrote down why:
# "a directory that is tracked is a directory whose references must resolve ... Adding a top-level
# directory now extends coverage by itself - which is the difference between a guard and the
# hole-list this was."
#
# So the rule here is now: **a path inside the shared checkout is DENIED unless it is one of the
# three carves Tim ruled.** The classifier below only picks the noun for the refusal message; it
# does not decide anything, so a surface it fails to recognise is still denied, and a file added to
# this repository tomorrow is protected on arrival without anyone editing this hook.
#
# ** THE SCOPE QUESTION THIS RAISES IS TIM'S, AND IT IS NAMED RATHER THAN ASSUMED. ** Tim ruled
# "Corpus + published surfaces only" and declined a wider scope adding "the rule file and the
# checkers". Those two are still carved, exactly as ruled. What inversion changes is the DEFAULT for
# files nobody classified - repo mechanics (`.gitignore`, `.gitattributes`), CI (`.github/**`), the
# lake build pins, the generated registries, and `.claude/settings.json`. Each is argued in the
# residual section below. If any of them should be the main instance's to edit, the remedy is one
# more line in the carve list, and it is Tim's line to write, not this hook's to assume.
#
# ** WHAT IS DELIBERATELY NOT COVERED - stated so nobody mistakes this for a seal. **
#   - tools/** and CLAUDE.md are NOT denied. Tim was offered a wider scope that added "the rule file
#     and the checkers" and declined it, choosing "Corpus + published surfaces only".
#     ** RESIDUAL, NAMED RATHER THAN HIDDEN: this hook lives under tools/, so the scope chosen leaves
#     the guard editable by the actor it constrains. ** That is the same shape as the mcp-mayhem
#     carve in block_git_gh.ps1, and the honest statement is that this is defence against DRIFT, not
#     against an agent deciding to route around it. Reopening it is a one-line change to the carve
#     list below plus a settings entry; it is Tim's call, not a hook's.
#   - .claude-local/** is NOT denied. Ruled explicitly: notes, tickets, DEFECTS.md and the handoff
#     stay the main instance's to write. It is also a SEPARATE REPOSITORY that this one only ignores,
#     so it is not a surface of this publication at all.
#   - the SHELL. Set-Content / Out-File / a python one-liner reach these same files and are not seen
#     here; this hook only ever inspects tool_input paths. block_git_gh.ps1's header records the
#     mirror-image gap from the other side. Closing the shell half means a path matcher on
#     Bash/PowerShell, which is a separate change with its own false-positive surface.
#   - indirection, an encoded command, or a script written first and executed second.
#   - ** SPELLINGS THAT NEED THE FILESYSTEM TO UNMASK. ** The five device and loopback-UNC spellings
#     GUARD-2 measured - `\\?\C:\`, `//?/C:/`, `\\localhost\C$\`, `\\127.0.0.1\C$\`, `\\.\C:\` - are
#     now normalised away before the comparison, and each has a control. What is NOT closed: 8.3
#     short names (`TIMBR~1`), a directory junction or symlink pointing into the checkout from
#     outside it, and a `subst` drive. All three are the same shape - a different NAME for the same
#     bytes - and unmasking them needs the file to EXIST, while a `Write` to a new file must be
#     judged exactly like an `Edit` to an existing one. Comparing normalised strings is therefore the
#     deliberate choice, and its residual is written here rather than implied.
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

WHAT IS STILL YOURS, and is not affected by this hook - this is the WHOLE list, because inside
this checkout everything else is denied by default:
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
# absolute. ** BOTH ARE JUDGED, not the first one present. ** The earlier form fell back to
# `notebook_path` only when `file_path` was blank, so a payload carrying a benign `file_path`
# ALONGSIDE a corpus `notebook_path` was ruled on the benign one - GUARD-3, "judged on the benign
# one". A payload bearing neither is not a file mutation this hook has any business inspecting.
$targets = @()
foreach ($t in @($data.tool_input.file_path, $data.tool_input.notebook_path)) {
    if (-not [string]::IsNullOrWhiteSpace($t)) { $targets += $t }
}
if ($targets.Count -eq 0) { exit 0 }

# The repo root is this script's own location, three levels up - derived, never hard-coded, so a
# clone or a move cannot leave the guard pointing at a directory that no longer exists.
$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path.TrimEnd('\')
$cmp = [StringComparison]::OrdinalIgnoreCase

# ** FIVE NAMES FOR ONE FILE, MEASURED (GUARD-2). ** `GetFullPath` PRESERVES the `\\?\` and `\\.\`
# device prefixes by design - that is what they mean - so a prefixed corpus path never started with
# the repo root and fell out of the guard as "outside the checkout". The loopback administrative
# shares are the same defect in UNC clothing: `\\localhost\C$\...` and `\\127.0.0.1\C$\...` open the
# identical bytes. All five are rewritten to the plain drive form HERE, before any resolution,
# because `\\?\` also suppresses `..` normalisation and the traversal control depends on it.
# A UNC path to any OTHER host is left exactly as it is - it is a different machine, it is not this
# checkout, and rewriting it into a local drive letter would be a fabrication.
function ConvertTo-PlainSpelling([string]$p) {
    $s = $p -replace '/', '\'
    if ($s -match '^\\\\[?.]\\UNC\\(.+)$')            { $s = '\\' + $Matches[1] }
    elseif ($s -match '^\\\\[?.]\\([A-Za-z]:\\.*)$')  { $s = $Matches[1] }
    if ($s -match '^\\\\(localhost|127\.0\.0\.1|\.)\\([A-Za-z])\$\\(.*)$') {
        $s = $Matches[2] + ':\' + $Matches[3]
    }
    return $s
}

# The CARVES. ** THIS IS THE WHOLE ALLOW-LIST, and it is the only exit from this function for a
# path inside the checkout. ** Each one is a ruling that was written down, not an inference:
#   .claude-local\  - Tim, 2026-09-19, explicitly. Also its own repository, which this one ignores.
#   tools\          - Tim, 2026-09-19, declining the wider scope. R-EXEMPT prices this on /rely
#                     still BLOCKING on executable logic in tools/verify and tools/process.
#   CLAUDE.md       - same ruling.
# R-EXEMPT: "Each carve is WRITTEN DOWN; do not extend one to a further directory by analogy - write
# the next one, or it is not exempt." Adding a fourth line here is a scope change and Tim's to make.
function Test-Carved([string]$rel) {
    if ($rel.StartsWith('.claude-local\', $cmp)) { return $true }
    if ($rel.StartsWith('tools\',         $cmp)) { return $true }
    if ($rel.Equals('CLAUDE.md',          $cmp)) { return $true }
    return $false
}

# NAMES ONLY. This table picks the noun for the refusal message so the block says what it stopped;
# it decides NOTHING. A path that matches no row is still denied, as "a tracked surface", which is
# the property this file now enforces directly rather than through a proxy.
#
# `^ZeroParadox(\\|\.lean$)` is the root-module fix, and it is written to avoid the mirror-image
# bug. The old `^ZeroParadox\\` required a separator, so the DIRECTORY matched and `ZeroParadox.lean`
# beside it did not. A bare `^ZeroParadox` would have over-reached onto any future sibling whose name
# merely starts with the word; the alternation admits exactly the directory and exactly the module.
$CLASSIFY = @(
    @{ Pattern = '^ZeroParadox(\\|\.lean$)';   What = 'the Lean corpus' }
    @{ Pattern = '^scripts\\';                 What = 'a PDF build script' }
    @{ Pattern = '\.pdf$';                     What = 'a rendered PDF' }
    @{ Pattern = '^_layouts\\';                What = 'the site layout that wraps every rendered page' }
    @{ Pattern = '^_config\.yml$';             What = 'the published site configuration' }
    @{ Pattern = '^CNAME$';                    What = 'the published domain' }
    @{ Pattern = '^\.zenodo\.json$';           What = 'the permanent DOI record' }
    @{ Pattern = '^LICENSE$';                  What = 'the published licence' }
    @{ Pattern = '^[^\\]+\.html$';             What = 'a published web page' }
    @{ Pattern = '^[^\\]+\.md$';               What = 'a root-level published document' }
    # R-EXEMPT names these explicitly as NOT exempt: "the gate briefs are published deliberately,
    # as the artifact showing how this project reviews itself, so both gates fire on them."
    @{ Pattern = '^\.claude\\commands\\';      What = 'a published gate brief' }
    @{ Pattern = '^\.claude\\settings\.json$'; What = "this guard's own registration" }
    @{ Pattern = '^\.github\\';                What = 'the CI and release automation' }
    @{ Pattern = '^(lakefile\.toml|lean-toolchain|lake-manifest\.json)$'
                                               What = 'the build pin every axiom profile is relative to' }
    @{ Pattern = '^(ssot\.json|gate_round\.json)$'
                                               What = 'a generated registry, written by tooling rather than by hand' }
)

# Returns $null to allow, or the refusal text to deny.
function Get-Refusal([string]$target) {
    $spelled = ConvertTo-PlainSpelling $target

    # Normalise WITHOUT requiring existence: a Write to a new file must be judged the same as an Edit
    # to an existing one. Resolve-Path throws on a missing leaf, so it cannot be used here.
    try {
        if ([System.IO.Path]::IsPathRooted($spelled)) {
            $full = [System.IO.Path]::GetFullPath($spelled)
        } else {
            $cwd = $data.cwd
            if ([string]::IsNullOrWhiteSpace($cwd)) { $cwd = $repoRoot }
            $full = [System.IO.Path]::GetFullPath((Join-Path $cwd $spelled))
        }
    } catch {
        return "BLOCKED (fail-closed): the hook could not resolve the target path '$target', so it cannot tell whether it is in the corpus.`n`n$GUIDANCE"
    }

    # OUTSIDE the shared checkout -> allow. This is the worktree route, and the scratchpad, and is
    # the single most important line in the file: it is what makes delegation pass automatically.
    if (-not $full.StartsWith($repoRoot + [System.IO.Path]::DirectorySeparatorChar, $cmp)) { return $null }

    $rel = $full.Substring($repoRoot.Length + 1)
    if (Test-Carved $rel) { return $null }

    $what = 'a tracked surface of this checkout'
    foreach ($p in $CLASSIFY) {
        if ($rel -match ('(?i)' + $p.Pattern)) { $what = $p.What; break }
    }

    return @"
BLOCKED: this would edit $what directly in the shared checkout.

  $rel

$GUIDANCE
"@
}

foreach ($t in $targets) {
    $refusal = Get-Refusal $t
    if ($refusal) { Deny $refusal }
}

exit 0
