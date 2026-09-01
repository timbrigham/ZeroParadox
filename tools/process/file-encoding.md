# File encoding — why files get corrupted here, and how to write one safely

**Routed from `CLAUDE.md` § *THE GATE-ENFORCED CONVENTIONS*.** Checker:
`python tools/verify/check_encoding.py` — pass a path after writing a file, or run it bare to scan
every tracked text file.

## The thing that makes this non-obvious

**"Is the file UTF-8?" returns PASS on the defect this exists to catch.** Measured 2026-08-20: a
splice script wrote `CLAUDE.md` with a six-character sequence beginning `Ã` where `📖 —` belonged.
That file was **valid UTF-8 at every byte**. `open(p, encoding='utf-8')` succeeded. A decodability
test is green. The bytes are a perfectly legal encoding of the wrong characters.

**You recognise the shape on sight once you know it:** a run of two or three characters starting
with `Ã`, `Â`, `â€` or `ð` where one character belongs. This page deliberately does **not** print
complete examples — `check_encoding.py` scans every tracked file including this one, and a document
containing real mojibake would fail the gate it is documenting. The checker has the same constraint
for the same reason; see the note on `_mangle()` in its header.

What actually happened is one level up: text that was already UTF-8 got **decoded as cp1252** and
then **re-encoded as UTF-8**. Every original non-ASCII character became two or three characters, and
the result is well-formed. So the test that matters is not *does this decode* but *does this decode
into something that was never typed*.

`check_encoding.py` answers that with a round trip rather than a list of known-bad bigrams — take
each run of adjacent non-ASCII characters and ask whether it reads back as cp1252 bytes forming
valid UTF-8. Double-encoded text does, by construction. A genuine `ü` or `á` does not, because one
byte is not a multi-byte sequence. A genuine `⊥` does not, because it has no cp1252 encoding at all.

## Where the corruption enters, measured

**⚠ IT IS USUALLY NOT THE WRITE. IT IS THE PARSE, ONE STEP EARLIER.** This is why "use a correct
writer" is insufficient advice and why the failure keeps recurring among people who know the rule.

**PowerShell 5.1 reads a `.ps1` file as the system ANSI codepage unless the script itself carries a
BOM.** So a script whose source contains `—` or `📖`, saved as clean UTF-8 by a correct editor, is
*parsed* into mojibake before a single line executes. The writer can then be flawless — `.NET`
`UTF8Encoding($false)`, everything correct — and it faithfully writes the corrupted string. The
author sees the right characters in their editor and the wrong ones on disk.

Secondary sources, all real on this system:

| mechanism | behaviour |
|---|---|
| `Set-Content` / `Add-Content` | default to the system ANSI codepage — pass `-Encoding utf8` explicitly |
| `Out-File`, `>`, `>>` | UTF-8 **with BOM** in 5.1; the BOM then shows as a whole-file diff |
| `python -c "..."` in PowerShell | backticks are eaten by the shell before Python sees them |
| a console at cp1252 | `print('⊥')` raises, and the crash reads like a checker finding |

## How to write a file safely

**Prefer the editing tools.** The `Write` and `Edit` tools write UTF-8 directly with no shell in the
path, so they cannot hit the parse trap. For a file with any non-ASCII content, this is the default.

**If a script must do it, write the script in Python**, with encodings named explicitly at both ends:

```python
open(path, 'w', encoding='utf-8', newline='\n').write(text)   # or common.write_text_lf
```

**If it must be PowerShell, keep every non-ASCII character out of the `.ps1` source.** Read the
payload from a separate UTF-8 file, or build it in Python. Do not rely on remembering to save the
script with a BOM — that is a discipline, and this whole class is here because discipline failed
nine times.

**Then verify, because none of the above is self-checking:**

```
python tools/verify/check_encoding.py <the file you just wrote>
```

## Repairing a file that is already corrupted

**⚠ DO NOT HAND-REPAIR CHARACTER BY CHARACTER.** You will fix the ones you can see. The corruption
is uniform across every non-ASCII character in whatever text passed through the bad decode, and some
of them are invisible in a terminal that is itself displaying through a codepage.

The repair is the exact inverse — `text.encode('cp1252').decode('utf-8')` — but apply it **only to
the runs the checker flags**, never to the whole file, unless you have proved the file is uniformly
corrupted.

**⚠ MIXED FILES ARE THE NORMAL CASE AND A WHOLE-FILE INVERSE DESTROYS THEM.** Measured 2026-08-20 on
`tools/verify/check_classes.py`: 24 corrupted runs sitting alongside genuine `⚠` characters added by
later edits. A whole-file inverse refused, correctly, on the first genuine character it could not
encode. Had it not refused, it would have destroyed every good glyph in the file while repairing the
bad ones — a repair that makes the checker's count go to zero and the file worse.

Any repair script must therefore (a) drive off the checker's own detector, so the repair set is
exactly the finding set, (b) rewrite right-to-left so offsets stay valid, and (c) assert the ASCII
skeleton is byte-identical afterwards. A pure re-decode changes non-ASCII characters and nothing
else; if any ASCII moved, the transform was not what you thought it was.
