# require_search_record_in_questions.ps1
# PreToolUse hook on AskUserQuestion - DENIES a question to Tim whose text, or any option's label or
# description, asserts an ABSENCE or an OPEN status ("unmeasured", "not proved", "nothing derives",
# "not located", "remains open", ...) without carrying a SEARCH RECORD ("searched: <how>, <result>")
# in that same field. Ruled by Tim, 2026-10-17 ("Hook on questions to you").
#
# WHY THIS EXISTS (DEFECTS.md `P2-RELAY-1`; memory `feedback-verify-pointer-status`, 6th occurrence).
# A ledger row called "AX-B1 selects p = 2" an "unmeasured selection claim". The main instance
# checked that the SENTENCE sat at its sites (a grep scoped to one document's build scripts), took
# that as checking the ROW, told Tim "nothing proved derives it", and offered "Measure it first".
# Tim chose it on that framing, then reversed it himself: ZP-B Theorem T0
# (ZeroParadox/Valuation/Padic.lean, `t0_no_prime_below_two` / `t0_two_is_prime` / `t0_redundancy`)
# already fixes p = 2 from AX-B1 + MP-1. An unscoped grep for "minimum prime|MP-1" returns 11 files.
# R-NOTINLIB fires on WRITING an absence; this one was INHERITED and relayed, so it never fired, and
# the memory rule ("an option I write is a claim") had failed five times before. R-RECUR's ladder at
# 4th+ is a checker, and this binds the ACTION at the one surface where the claim becomes Tim's
# ruling: the question.
#
# WHAT IT REQUIRES. In any field that matches the vocabulary below, the SAME field must contain
# `searched:` followed by something. The intended content is the unscoped claim sweep and its result:
#     searched: check_paths --claim "minimum prime", 11 files incl. ZeroParadox/Valuation/Padic.lean
# A field with no absence vocabulary passes untouched. A question that instead POINTS at the Lean
# home (R-TOLEAN step 1) does not need the vocabulary at all, which is the preferred fix.
#
# WHAT IT DOES *NOT* CATCH - stated so nobody mistakes it for a seal.
#   - The vocabulary is a DENYLIST of absence and open-status wordings, so it is porous by
#     construction (R-NOTINLIB says the same of its own trigger list). A paraphrase it does not list
#     ("there is no result tying ...") passes. Best-effort per Tim's proportional-tooling ruling
#     (2026-10-10): the commonest shapes, not an exhaustive matrix.
#   - It checks that a search record is PRESENT, not that the search was RUN or was unscoped. It
#     forces the question "what did I search?" to be answered in writing where Tim can read it; it
#     cannot audit the answer. That is the honest scope of a text hook.
#   - Absence claims in chat text, DEFECTS rows, briefs and commit messages are not seen. Only the
#     AskUserQuestion tool input is.
#   - It fires on absence wording about anything, tooling included. A false DENY costs one line
#     ("searched: ...") or a rewording; that trade is deliberate.
#
# FAILS CLOSED, like block_git_gh.ps1 and block_corpus_edit.ps1: empty or unparseable input DENIES.
# Keep this file ASCII-only (R-GATED: no non-ASCII in .ps1 source).

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
A question to Tim is relayed authority: the option he picks becomes his ruling. An absence or
open-status claim in it ("unmeasured", "not proved", "nothing derives it", "not located", "open")
must carry how it was checked, IN THE SAME OPTION, as `searched: <how>, <result>`.

DO THIS FIRST:
  1. Run the claim sweep UNSCOPED, on the key phrase AND on the name of the result you think is missing:
       python tools/verify/check_paths.py --claim "<key phrase>" > <scratch log> 2>&1   (then read it whole)
     plus a grep over ZeroParadox/**/*.lean for the identifiers. Never narrow it to one document.
  2. If the answer EXISTS (the usual outcome): drop the absence wording and POINT at the Lean home
     (R-TOLEAN step 1) - the option then needs no search record at all.
  3. If it is genuinely not located: write "not located as of <date>, searched: <command>, <result>"
     in that option, so Tim can see the scope of the search he is ruling on.

Do not satisfy this hook with a search you did not run. DEFECTS.md P2-RELAY-1 is why it exists.
'@

if ([string]::IsNullOrWhiteSpace($raw)) {
    Deny "BLOCKED (fail-closed): the hook received empty input and cannot read the question.`n`n$GUIDANCE"
}
try { $data = $raw | ConvertFrom-Json } catch {
    Deny "BLOCKED (fail-closed): the hook could not parse its input, so it cannot read the question.`n`n$GUIDANCE"
}

# The vocabulary. Each alternative is an ABSENCE or OPEN-STATUS assertion. Word boundaries keep
# "open" from matching "opened"/"openly" and "absent" from matching "absentee"; "open item" and
# "is open" are listed as phrases because bare "open" is too common in option text.
$ABSENCE = '(?i)\b(' + (@(
    'unmeasured',
    'not\s+(yet\s+)?measured',
    'never\s+measured',
    'not\s+(yet\s+)?proved',
    'not\s+(yet\s+)?proven',
    'unproved',
    'unproven',
    'no\s+proof',
    'nothing\s+(\w+\s+){0,3}(proves|derives|states|shows)',
    'no\s+(lean\s+|corpus\s+|mathlib\s+)?(theorem|lemma|declaration|result)\s+(\w+\s+){0,3}(proves|derives|states|shows|ties|for)',
    'not\s+(located|found|stated)',
    'not\s+in\s+(lean|the\s+corpus|mathlib)',
    'is\s+(still\s+)?open',
    'remains\s+open',
    'still\s+open',
    'open\s+item',
    'absent'
) -join '|') + ')\b'

$RECORD = '(?i)\bsearched\s*:\s*\S'

function Test-Field([string]$text) {
    if ([string]::IsNullOrWhiteSpace($text)) { return $null }
    $m = [regex]::Match($text, $ABSENCE)
    if (-not $m.Success) { return $null }
    if ($text -match $RECORD) { return $null }
    return $m.Value
}

$qs = $data.tool_input.questions
if ($null -eq $qs) {
    # AskUserQuestion always carries `questions`; one arriving without it is the unknown case
    # (R-ZERONULL: "nothing to read" must not answer like "read it and it was fine").
    Deny "BLOCKED (fail-closed): an AskUserQuestion call arrived with no questions array.`n`n$GUIDANCE"
}

$hits = @()
$qi = 0
foreach ($q in @($qs)) {
    $qi++
    $hit = Test-Field "$($q.question)"
    if ($hit) { $hits += "question $qi text: '$hit'" }
    $oi = 0
    foreach ($o in @($q.options)) {
        $oi++
        $field = "$($o.label)`n$($o.description)"
        $hit = Test-Field $field
        if ($hit) { $hits += "question $qi option $oi ('$($o.label)'): '$hit'" }
    }
}

if ($hits.Count -gt 0) {
    $list = ($hits | ForEach-Object { "  - $_" }) -join "`n"
    Deny "BLOCKED: absence / open-status wording with no search record in the same field:`n$list`n`n$GUIDANCE"
}

exit 0
