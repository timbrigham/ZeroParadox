#!/usr/bin/env python3
"""Generator for "The Bottom Element (⊥) - Dictionary and Map".

SSOT: MAP data from `build_bottom_matrix.py` (CELLS/SLOTS); apophatic entries + glosses below. Witness
theorem names are RESOLVED against the actual Lean source (`ZeroParadox/**/*.lean`) at generation time:
each resolvable name becomes a relative link `ZeroParadox/File.lean`; names that do not resolve are printed
as a warning. So the page cannot link a witness the Lean does not contain.

Assumes the output .md lives at the REPO ROOT (relative links point into `ZeroParadox/`).

MAP data (CELLS/SLOTS) is imported from build_bottom_matrix.py, an internal companion generator kept in
the private working folder and not mirrored to scripts/; this file is the one that emits the public page.

Run:  python .claude-local/build_dictionary_map.py   (active copy; also mirrored read-only to scripts/)
Out:  BOTTOMELEMENT.md at the repo root   (Mermaid + relative links render on GitHub)
"""
import sys, os, re
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")
sys.path.insert(0, os.path.dirname(__file__))
from build_bottom_matrix import CELLS, SLOTS, classify, GLYPH, dyn_glyph

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO_ROOT, "BOTTOMELEMENT.md")  # front-door reference at repo root (relative links resolve from here)

# --- Resolver: name -> (path, KIND), both scanned from the actual Lean source ---
# The KIND is DERIVED, never asserted.  A witness is not always a theorem: a property a structure
# is DEFINED BY is carried by a class field, which the class ASSUMES and each instance discharges.
# That used to be invisible - the legend said "witness theorem", the one field-witness was
# hand-linked through an override table, and its kind survived only as a Python comment - so a
# reader checking the witness against the legend found a mismatch that was not actually an error.
# Now the scanner reports the KEYWORD it found and the page prints exactly that.
# ⚠ The keyword is a SYNTACTIC proxy. Do not infer the type's universe from it anywhere in this
# file: `def` and `instance` inhabit `Prop` as freely as `Type`. See `witness_note`.
_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|local\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
# ⚠ The name pattern must ALLOW DOTS, matching `_scan_external`. Forbidding them truncated
# `def Ordinal.toNatOrdinal` to a phantom `Ordinal` in a vendored file, which then outranked
# Mathlib's real `Ordinal` on a single hit - no ambiguity, so the multi-hit guard never fired.
# That guard closes ONE ROUTE (two candidates); this closes the other (one WRONG candidate).
# A field inside a `class`/`structure ... where` body: indented `name :` (never `:=`, which is a
# value, and never a tactic line, which is excluded by requiring the block context).
_FIELD = re.compile(r"^[ \t]{1,6}([A-Za-z][A-Za-z0-9_']*)\s*:(?!=)")
_BLOCK_OPEN = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|local\s+)*"
    r"(?:class|structure)\s+([A-Za-z0-9_']+)")

def type_head(rest):
    """The head symbol of a declaration's TYPE, from the text following its name.

    Finds the first `:` at bracket depth 0 (so binders `{X : C}` / `(h : P)` / `[Inst]` are
    skipped) and returns the first identifier after it. Returns None when the declaration gives
    no explicit type (e.g. `abbrev IsInitial (X : C) := …`), which is itself informative: a
    declaration with no stated type is not a stated proposition."""
    depth = 0
    for i, ch in enumerate(rest):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            if rest[i + 1:i + 2] == "=":        # `:=`, the value, not a type ascription
                return None
            m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_'.]*)", rest[i + 1:])
            return m.group(1) if m else None
    return None

_COMMENT_OPEN = re.compile(r"/-")
_COMMENT_CLOSE = re.compile(r"-/")
_NS_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
_NS_END = re.compile(r"^\s*end\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")

def _ns_track(line, stack):
    """Maintain the enclosing `namespace` stack so a declaration can be FULLY QUALIFIED.

    Without this the index keys on the bare declared name, and two unrelated declarations sharing
    one name are indistinguishable - which is exactly the `IsInitial` collision (category theory
    vs set theory) and the `IsZero` mis-resolution. `section Foo` is deliberately NOT tracked:
    a named section scopes but does not prefix, so only `namespace` contributes to the name."""
    m = _NS_OPEN.match(line)
    if m:
        stack.extend(m.group(1).split("."))
        return stack
    m = _NS_END.match(line)
    if m:
        parts = m.group(1).split(".")
        if stack[-len(parts):] == parts:      # matches a namespace; a section `end` will not
            del stack[-len(parts):]
    return stack

def scan_declarations():
    """name -> LIST of (repo-relative path, kind, type head). A list, not a single entry, so a
    name declared in two places can be reported AMBIGUOUS instead of resolved by walk order.

    ⚠ Block comments are skipped. Without that, a Mathlib docstring line reading e.g.
    "… def the thing …" registers a declaration named `the`, and this pollutes the index with
    `the`, `a`, `of`, `this`, `that`, `it`, `and`, `we`. That is a fail-WRONG route, not a
    fail-open one, so the unresolved-witness guard structurally cannot see it."""
    index = {}
    for dp, _, files in os.walk(os.path.join(REPO_ROOT, "ZeroParadox")):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            full = os.path.join(dp, fn)
            rel = os.path.relpath(full, REPO_ROOT).replace(os.sep, "/")
            owner = None                      # the class/structure whose body we are inside
            depth = 0                         # block-comment nesting
            ns = []                           # enclosing namespace stack
            try:
                with open(full, encoding="utf-8") as f:
                    for line in f:
                        opens, closes = len(_COMMENT_OPEN.findall(line)), len(_COMMENT_CLOSE.findall(line))
                        was_in = depth > 0
                        depth = max(0, depth + opens - closes)
                        if was_in or opens:
                            continue          # any line inside or opening a block comment
                        _ns_track(line, ns)
                        m = _DECL.match(line)
                        if m:
                            fq = ".".join(ns + [m.group(2)])
                            index.setdefault(fq, []).append(
                                (rel, m.group(1), type_head(line[m.end():]), fq))
                            b = _BLOCK_OPEN.match(line)
                            owner = b.group(1) if (b and line.rstrip().endswith("where")) else None
                            continue
                        if owner:
                            if line.strip() and not line[:1].isspace():
                                owner = None          # dedent ends the body
                            else:
                                fm = _FIELD.match(line)
                                if fm:
                                    ffq = ".".join(ns + [fm.group(1)])
                                    index.setdefault(ffq, []).append(
                                        (rel, f"class field of {owner}",
                                         type_head(line[fm.end() - 1:]), ffq))
            except Exception:
                pass
    return index

INDEX = scan_declarations()
UNRESOLVED = []
_CITED = set()          # every witness name this build actually rendered

# Kinds that are ordinary proved results; anything else is called out on the page.
_PROVED = {"theorem", "lemma"}

_MATHLIB = os.path.join(REPO_ROOT, ".lake", "packages", "mathlib", "Mathlib")
_EXT_CACHE = None

def _scan_external(name):
    """Resolve a witness declared OUTSIDE ZeroParadox (i.e. in the pinned Mathlib).

    Needed because the kind claim must hold for EVERY cited witness. Without this an external
    name resolved to nothing and fell through to the strongest mark - a gate that fails OPEN,
    which is worse than no gate. Scanned lazily and cached: only names the local index missed."""
    # ⚠ Match the FULL name as written, never the tail after the last dot. Matching the tail
    # resolved `IsInitial.op` off `MulOpposite.op` in `Algebra/Opposites.lean` — 39 declarations
    # in the pin share the base name `op`, so the correct answer arrived by filesystem walk order
    # rather than by derivation, and `Nonsense.op` resolved to `def`. Requiring the full name
    # fails CLOSED on anything declared inside a `namespace` block instead of guessing.
    global _EXT_CACHE
    if _EXT_CACHE is None:                 # built once, lazily, on the first external lookup
        _EXT_CACHE = {}
        rx = re.compile(
            r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|local\s+)*"
            r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.M)
        for dp, _, files in os.walk(_MATHLIB):
            for fn in files:
                if not fn.endswith(".lean"):
                    continue
                try:
                    depth = 0; ns = []
                    with open(os.path.join(dp, fn), encoding="utf-8") as f:
                        for line in f:
                            opens = len(_COMMENT_OPEN.findall(line))
                            closes = len(_COMMENT_CLOSE.findall(line))
                            was_in = depth > 0
                            depth = max(0, depth + opens - closes)
                            if was_in or opens:
                                continue
                            _ns_track(line, ns)
                            m = rx.match(line)
                            if m:
                                efq = ".".join(ns + [m.group(2)])
                                _EXT_CACHE.setdefault(efq, []).append(
                                    ("Mathlib", m.group(1), type_head(line[m.end():]), efq))
                except Exception:
                    pass
    return _EXT_CACHE.get(name)

AMBIGUOUS = []

def _entry(name):
    """The unique declaration for `name`, or None when there is not exactly one.

    ⚠ FAIL CLOSED ON A MULTI-HIT. The witness-name half of this resolver was hardened after
    `IsInitial.op` matched `MulOpposite.op`, whose own comment records that the right answer had
    arrived "by filesystem walk order rather than by derivation" - and the same reasoning was not
    carried here. Measured: `IsInitial` has TWO declaration sites in the pin and the second
    (`SetTheory/Cardinal/Aleph.lean`) is `Prop`-valued, so a different walk order would have
    rendered a `≝` cell as `✓` with a provably false sentence beside it; and `IsZero` already
    resolved to a Lie-theory `def` rather than the category-theory `structure … : Prop`, harmless
    only because the witness citing it short-circuits first. **A wrong resolution is worse than no
    resolution**: unresolved refuses to write, wrong ships a confident false sentence."""
    hits = INDEX.get(name) or _scan_external(name)
    if not hits:
        # Cited names are written short (`fC_zero_isInitial`, `Limits.IsInitial`) while the index
        # is keyed fully-qualified. Accept a SUFFIX match only when exactly one declaration in
        # either tree ends that way; two candidates means the short name does not identify a
        # declaration, and guessing is what produced the `IsZero` mis-resolution.
        suf = "." + name
        cands = [(k, v) for k, v in INDEX.items() if k == name or k.endswith(suf)]
        if not cands:
            _scan_external(name)
            cands = [(k, v) for k, v in (_EXT_CACHE or {}).items()
                     if k == name or k.endswith(suf)]
        flat = [(k, e) for k, vs in cands for e in vs]
        if not flat:
            return None
        if len({k for k, _ in flat}) > 1:
            AMBIGUOUS.append((name, sorted({k for k, _ in flat})[:4]))
            return None
        hits = [e for _, e in flat]
    if len(hits) > 1:
        AMBIGUOUS.append((name, [h[0] for h in hits]))
        return None
    return hits[0]

UNRESOLVED_HEADS = []
HEAD_BY_SUFFIX = []

def _resolve_head(thead, ctx=None):
    """Resolve a TYPE HEAD, allowing a leading namespace to be stripped.

    ⚠ This is NOT the bare tail-match forbidden for witness names. There, `IsInitial.op` matching
    any declaration called `op` is wrong - 39 in the pin share that base. Here the dotted form is
    a namespace-qualified USE of a type (`Limits.IsInitial`) whose declaration site writes the
    short name, so stripping leading components is the correct lookup. Suffix resolutions are
    reported at build time so the weaker step is never silent."""
    # Resolve IN CONTEXT first: a type head is written relative to the enclosing namespace, so
    # `IsTerminal` inside `CategoryTheory.Limits` means `CategoryTheory.Limits.IsTerminal`, not the
    # unrelated `…Diagram.IsTerminal`. Without this the bare name is genuinely ambiguous and the
    # build correctly refuses - which is right, and unhelpful. This is what Lean itself does.
    if ctx:
        ns = ctx.split(".")[:-1]
        for i in range(len(ns), -1, -1):
            hits = INDEX.get(".".join(ns[:i] + [thead])) or (_EXT_CACHE or {}).get(".".join(ns[:i] + [thead]))
            if hits and len(hits) == 1:
                return hits[0]
    e = _entry(thead)
    if e:
        return e
    parts = thead.split(".")
    for i in range(1, len(parts)):
        e = _entry(".".join(parts[i:]))
        if e:
            HEAD_BY_SUFFIX.append((thead, ".".join(parts[i:])))
            return e
    return None

def witness_kind(name):
    e = _entry(name)
    return e[1] if e else None

def is_proof(name):
    """Did the KERNEL CHECK A PROOF OF A PROPOSITION for this witness?

    This is the semantic question the glyph is about, and the declaration keyword is only a proxy
    for it — a proxy that was wrong twice, in both directions, before this was measured:
      * `theorem`/`lemma` — always a proof; Lean enforces it.
      * `def`/`abbrev`/`instance` — a proof **iff its type is Prop-valued**. `hasZeroObject_op` is
        an `instance` of `class HasZeroObject : Prop`, so it IS a proof (verified: a `theorem`
        form of it elaborates). `fC_zero_isInitial` is a `def` of `IsInitial`, which unfolds to
        `IsColimit` — a structure whose first field is the mediating morphism `desc`, so it
        CARRIES the route and is data; Lean refuses `theorem` for it.
      * a class field — NOT a proof here whatever its type: the class ASSUMES it and each
        instance discharges it separately.
    Decided by one level of indirection: take the witness's type head, then ask whether THAT is
    itself declared `: Prop`."""
    e = _entry(name)
    if e is None:
        return False
    _, kind, thead = e[0], e[1], e[2]
    ctx = e[3] if len(e) > 3 else None
    if kind in _PROVED:
        return True
    if kind.startswith("class field") or kind in ("class", "structure"):
        return False
    if thead is None:
        return False
    # ⚠ INVERTED IN AN EARLIER ROUND. A witness whose own stated type IS `Prop` is a PREDICATE
    # DEFINITION (`def IsQuineAtom … : Prop := …`) - nothing was asserted, let alone proved. A
    # witness that ASSERTS something has type `P` where `P : Prop`, which is the indirection
    # below. Measured with this function: the old branch scored `IsQuineAtom`, `q2SelfMem`,
    # `selfMemDerived` and Mathlib's `Monotone` as assertions and would have given them the
    # strongest mark. Latent only because no live cell leads with a predicate definition.
    if thead == "Prop":
        return False
    t = _resolve_head(thead, ctx)
    if t is None:
        # Cannot determine what the type is, so cannot claim either mark. Recorded, and the build
        # refuses to write rather than defaulting - defaulting would silently mark an ASSERTED
        # result as constructed, which is the direction that misleads.
        UNRESOLVED_HEADS.append(thead)
        return False
    return t[2] == "Prop"

def link_witness(name):
    _CITED.add(name)
    # ⚠ Through `_entry`, never `INDEX.get(name)`. The index is keyed FULLY QUALIFIED, so a bare
    # cited name misses it entirely - which silently unlinked every local witness and dumped them
    # all into UNRESOLVED. `_entry` does the suffix resolution and the ambiguity check.
    e = _entry(name)
    if e and e[0].endswith(".lean"):
        return f"[`{name}`]({e[0]})"
    if e:
        return f"`{name}`"          # external (Mathlib): resolved for its KIND, but not linkable
    UNRESOLVED.append(name)
    return f"`{name}`"  # not a local declaration (e.g. Mathlib) - shown, not linked

def witness_note(name):
    """Rendered kind marker, DERIVED from the source. Empty for a plain theorem/lemma.

    ⚠⚠ THE NOTE STATES ONLY THE DECLARATION KEYWORD. It must NOT infer the type's universe.
    The keyword is a PROXY: `def` and `instance` inhabit `Prop` as freely as `Type`, so
    "constructed data / Lean does not admit `theorem` for it" is FALSE of them in general.
    Measured 2026-08-13: `class HasZeroObject : Prop` (Mathlib `ZeroObjects.lean:174`), so
    `hasZeroObject_op` is an `instance` that IS a proof of a proposition - and Mathlib declares
    `theorem hasZeroObject_unop` eight lines below it. The same over-generalization was killed one
    category narrower a round earlier, for class fields: `unique_fp` is `Prop`-valued and
    `q2_unique_fp` (`Computability/SelfApp.lean:143`) proves exactly it.
    **Both times the defect was inferring a semantic fact from a syntactic one.** Say what was
    read; let the legend give the usual reason, fenced as usual rather than universal.
    The class-field note is the one interpretive line kept, because it holds structurally whatever
    the universe: a field is a precondition, and the kernel checks each instance supplies it."""
    k = witness_kind(name)
    if k is None:
        return " *(kind not derived - see the build warning)*"
    # Each branch states the DERIVED FACT first and any reading second, so the sentence is about
    # THIS witness and asserts no rule over the others. Six gate rounds put every prose-layer
    # bedrock finding in a universal; a per-cell sentence has no universal to be wrong about.
    if k in _PROVED or is_proof(name):
        return "" if k in _PROVED else f" *(an `{k}`, and its type is a proposition - so a proof)*"
    if k.startswith("class field"):
        return f" *({k} - assumed by the class, discharged by each instance)*"
    if k in ("class", "structure"):
        return f" *(a `{k}` - the requirements bundle itself)*"
    # ⚠ NEVER "not a proof", and no reading appended either. "it hands over the object itself" was
    # false of `IsLimit`, whose value is `{ lift, fac := _proof_3, uniq := _proof_4 }` - it carries
    # proofs alongside the map. State the derived fact and stop.
    return f" *(a `{k}`, and its type is not a proposition)*"

def annotate_witness(txt):
    """Append the derived kind to a cell whose text OPENS with its witness name.

    Scoped deliberately: a name appearing mid-sentence is a mention, and a `∅` cell's text is a
    reason rather than a witness. Only the leading token of a claim-bearing cell is a citation."""
    m = re.match(r"([A-Za-z][A-Za-z0-9_.']*)", txt or "")
    if not m:
        return txt
    name = m.group(1)
    if witness_kind(name) is None:      # not `name in INDEX` - external witnesses resolve too
        return txt
    note = witness_note(name)
    return txt[:m.end()] + note + txt[m.end():] if note else txt

def render_witnesses(names):
    # A plain theorem/lemma renders bare; anything else is marked, and the mark is DERIVED.
    return ", ".join(link_witness(n) + witness_note(n) for n in names) if names else "*meta (no Lean witness)*"

# --- Reading key 1: slot codes ---
SLOT_GLOSS = {
    "CANT":  "**cannot-have** - what ⊥ provably is NOT (its exclusions)",
    "NARR":  "**narrow** - ⊥ is a single, unique point",
    "MEAS":  "**measure** - some quantity becomes infinite exactly at ⊥",
    "INV":   "**inversion** - the map z↦1/z swaps ⊥ (which is 0) with infinity (the two poles of a Riemann sphere)",
    "CONC":  "**concurrency** - applying ⊥'s own operation returns ⊥ unchanged (a fixed point: operation and result coincide)",
    "SELF":  "**self-reference** - ⊥ is defined by referring to itself (a self-reproducing / self-containing object)",
    "GEN":   "**generation** - ⊥ generates the structure built above it (for example, the ordinal ε₀ generated from 0)",
    "DYN":   "**dynamics** - how ⊥ is approached and departed, one directional axis with two sub-senses: **↓ inbound** (orbits converge *to* ⊥ - a sink) and **↑ outbound** (structure departs *from* ⊥ irreversibly - a source). ↕ = both, which happens only at a seam (μ=ν). Single-directional, set by whether ⊥ is a sink or a source",
}

# --- Reading key 2: constructions (map rows) ---
CONSTRUCTION_GLOSS = {
    "Lat ⊥ (ZPA/ZPE)": "the abstract order bottom: ⊥ as the least element of the framework's lattice",
    "p-adic (ℚ₂/ℤ₂)": "the number 0 in the 2-adic numbers (the floor of the 2-adic distance)",
    "Info (ZPC)": "the information-theoretic bottom, where surprisal / information grows without bound",
    "#4 Kleisli (Fin 0)": "the empty type, as the initial object of a probability (Kleisli) category",
    "#5 Hilbert (zero obj/seam)": "the zero vector space, as the zero object of a linear category (the 'seam')",
    "#3 TopCat ({0} limit)": "the one-point space {0}, obtained as a topological limit of shrinking balls",
    "#2 Markov (attractor)": "the stationary distribution a random walk settles into",
    "Kleene (quine, ZPK)": "the self-reproducing program (Kleene fixed point) of computability",
    "ε₀ (ordinal, ZPL/M)": "the ordinal ε₀, generated from 0 by iterating omega-to-the-power",
    "selfApp (abstract ⊥)": "the abstract self-application ⊥: the unique fixed point of a self-map",
}

# --- Reading key 3: recurring terms ---
TERMS = [
    ("apophatic", "characterizing something by what it is NOT (definition by exclusion)"),
    ("μ / ν", "least fixed point (μ, built up from the floor) vs greatest fixed point (ν, closed down)"),
    ("Quine atom / Kleene quine", "a self-containing set (x = {x}) / a program that prints itself"),
    ("the snap", "the framework's discrete jump off ⊥ into the first structured state"),
    ("ε₀", "the fixed point of omega-to-the-power reached from 0 - both min and max at once (epsilon0_min_eq_max): the least such fixed point (the minimum closure, a floor in the fixed-point order) and the supremum of the ascending tower (a ceiling) - never only a ceiling"),
    ("v₂ → ∞", "the 2-adic valuation going to infinity at 0 (0 is infinitely divisible by 2)"),
]

# --- Dictionary: negative entries.  (id, description, [witness theorem names]) ---
APOPHATIC = [
    ("A1", "a Lean term or otherwise finitely written down - this is the *apophatic* ⊥, the descriptionless limit-notion, distinct from the algebraic bottom element the Lean manipulates as a finite, decidable term. The two share the symbol ⊥, not an identity: any written form is a description, so it captures an interpretation of ⊥, never the descriptionless limit itself", []),
    ("A2", "anything that keeps time, space, description, measure or structure (that would be an *interpretation* of ⊥, not ⊥)", []),
    ("A3", "finite: ⊥ is by definition the point where every finite measure diverges to infinity", []),
    ("B1", "the same object as both the proof-theory floor and the attractor floor (one is well-founded, the other is not)",
     ["no_strictMono_real_to_ordinal", "simplex_antichain"]),
    ("B2", "the same object as a categorical initial bottom, if it is a topological limit bottom (their universal properties point opposite ways)",
     ["padic_bottom_not_initial", "split_kleisli_vs_hilbert"]),
    ("B4", "reached by a comparison that preserves the 'closed-down' (ν) structure - you can only get to ⊥ by forgetting that structure",
     ["faithful_iff_descending"]),
    ("B5", "unified with its self-referential face in a structure-preserving way - the two coincide only as a bare point",
     ["faces_iso_unique"]),
    ("C1", "forced to a single point as a Markov bottom (#2): a reducible chain settles into a whole family of distributions, not one",
     ["markov_node_no_universal_property"]),
    ("C3", "an *initial* object of the category of spaces (the p-adic floor behaves like a limit / terminal object, the opposite)",
     ["padic_bottom_not_initial"]),
    ("D1", "a *zero object* (both initial and terminal) of the Kleisli or p-adic categories",
     ["kleisli_bottom_not_zero", "padic_bottom_not_zero"]),
    ("D2", "a *greatest* element (it is the floor, not the top)", ["zpa_bot_not_greatest"]),
    ("D4", "an inhabited least-fixed-point for the identity functor: that least fixed point is provably empty",
     ["strict_fix_isEmpty", "fix_isEmpty_constructive"]),
    ("D5", "recovered by mapping the least fixed point onto the greatest: the comparison map is not onto",
     ["fixToCofix_not_surjective"]),
    ("D6", "reached by a non-contracting orbit: unit-norm and swap orbits provably do not converge to ⊥",
     ["unit_orbit_not_tendsto_zero", "swap_orbit_not_convergent"]),
]

# --- Dictionary: positive handles.  (slot, aspect, characterization, [witness names]) ---
POSITIVE = [
    ("narrow", "noun", "the single, unique pinned point", ["q2_unique_fp", "fB_bottom_is_limit"]),
    ("measure", "noun", "a quantity that becomes infinite exactly at ⊥", ["t2_diverges", "addVal_bot"]),
    ("inversion", "verb", "the 0 = ∞ pole: the map z↦1/z swaps 0 and infinity",
     ["rInv_swaps", "inversion_reverses_filtration"]),
    # `Statement:` COINCIDENCE - `selfApp_bot_is_both_extremal` proves ⊥ is simultaneously the
    # LEAST and the GREATEST fixed point of `selfApp`, i.e. both readings of one object at once
    # (the μ=ν seam). Tag emitted from here because the page is generated: hand-patching the
    # rendered line would be overwritten on the next build.
    ("concurrency", "hinge",
     "the fixed point where least and greatest coincide (operation = result) - `Statement:` COINCIDENCE",
     ["unique_fp", "selfApp_bot_is_both_extremal"]),
    ("self-reference", "hinge", "the self-reproducing / self-containing fixed point (Quine / Kleene)",
     ["kleene_quine_is_bot", "quine_period_is_goedel"]),
    ("generation", "verb", "the floor generates the ceiling (ε₀ = the closure of 0 under omega-to-the-power)",
     ["epsilonZero_eq_nfp"]),
    ("dynamics", "verb", "⊥'s one-way approach and departure - two sub-senses: **inbound** (↓, orbits converge *to* ⊥ - a sink) and **outbound** (↑, structure departs *from* ⊥ irreversibly - a source); ↕ = both, only at a seam (μ=ν)",
     ["contraction_orbit_tendsto_zero", "t_snap_derived", "c3_irreversible", "fC_no_return"]),
]

def leading_witness(txt):
    """The name a cell OPENS with, if its kind resolves - the cell's actual citation.

    ⚠ Gate on `witness_kind`, NOT on `name in INDEX`. Gating on the local index made every
    EXTERNAL (Mathlib) witness invisible here, so it fell through to the strongest mark: two live
    cells rendered `✓` while citing a Mathlib `def` and `instance`. Fail-open, found by the gates."""
    m = re.match(r"([A-Za-z][A-Za-z0-9_.']*)", txt or "")
    if not m:
        return None
    name = m.group(1)
    if witness_kind(name) is not None:
        return name
    # FAIL CLOSED on the MAP path too. This used to return None here and fall through to `✓` —
    # the strongest mark, on no evidence — without ever reaching UNRESOLVED.
    # ⚠ The `_decl_shaped` guard that used to sit here left the hole HALF open: it rejects
    # all-lowercase names, so `Bogus_zzz` was caught and plain `bogus` still rendered `✓`. A
    # claim-bearing cell's leading token IS its witness whatever it looks like, so register it
    # unconditionally. (`∅` cells never reach here - they carry a reason, not a witness.)
    UNRESOLVED.append(name)
    return None

def cell_mark(w, key=None):
    # DYN is the directional dynamics column: ↓ inbound · ↑ outbound · ↕ seam (both); trailing * = conditional/inherited.
    # Every other column: ✓ proved · ≝ definitional · ✗ refuted · ∅ n/a-structural · ? open; trailing * = conditional.
    #
    # ⭐ ✓ vs ≝ is DERIVED, never hand-set, and it is a distinction of ENCODING - NOT of status.
    # ⚠⚠ BOTH MARKS ARE ESTABLISHED RESULTS. `≝` must never be read, or worded, as "unproved" or
    # "not a proof". `IsInitial X` lives in `Type` because an initiality witness must physically
    # CARRY the mediating morphism, so `def` is FORCED BY THE SIGNATURE - it is not a gap. Restate
    # the same content so the type lands in `Prop` and `theorem` returns immediately; measured, it
    # elaborates: `theorem _ [HasInitial C] : Nonempty (IsInitial (⊥_ C)) := ⟨theInitial⟩`.
    # The honest distinction is Tim's: does the witness HAND YOU THE CONSTRUCTION, or ASSERT a
    # proposition? A `def` producing an `IsInitial` gives you the route itself; an `instance` of
    # `class HasZeroObject : Prop` asserts one exists.
    # ⚠ build_bottom_matrix.cell() does NOT make this split - it cannot, it never scans the Lean
    # source. Its printer is dev-side only; BOTTOMELEMENT.md is the rendered artifact.
    if key == "DYN":
        return dyn_glyph(w)
    st = classify(w)[0]
    if st in ("go", "cond"):
        txt = classify(w)[1]
        name = leading_witness(txt)
        if name is None and txt.strip():
            # ⚠ THE PROPERTY, not one route to it. `leading_witness` registers an unresolved NAME,
            # but a claim-bearing cell whose text does not begin with an identifier at all yielded
            # no name, so nothing was registered and `✓` — the strongest mark — was emitted with
            # nothing read. Third route to the same hole; the first two are recorded there.
            UNRESOLVED.append(f"<no leading identifier: {txt[:40]!r}>")
        if name and not is_proof(name):
            return "≝" + ("*" if st == "cond" else "")
    return GLYPH[st]

def render_table(rows, headers):
    out = ["| " + " | ".join(headers) + " |", "|" + "---|" * len(headers)]
    for r in rows:
        out.append("| " + " | ".join(r) + " |")
    return "\n".join(out)

def render_slot_gloss():
    return render_table([[k, SLOT_GLOSS[k]] for k, _ in SLOTS], ["code", "what it means"])

def render_construction_gloss():
    return render_table([[c, g] for c, g in CONSTRUCTION_GLOSS.items()], ["construction (map row)", "what it means"])

def render_terms():
    return render_table([[t, g] for t, g in TERMS], ["term", "plain meaning"])

def render_map():
    keys = [k for k, _ in SLOTS]
    rows = ["| construction | " + " | ".join(keys) + " |", "|---|" + ":--:|" * len(keys)]
    for c, d in CELLS.items():
        rows.append("| " + c + " | " + " | ".join(cell_mark(d.get(k), k) for k in keys) + " |")
    return "\n".join(rows)

_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
def _decl_shaped(name):
    # only auto-link tokens that LOOK like ZP witness names - snake_case or camelCase - so common
    # English words that happen to collide with a short decl (e.g. `is`) are never linked.
    return "_" in name or re.search(r"[A-Z]", name[1:]) is not None
def link_in_text(text):
    """Auto-link any decl-shaped token that resolves against the Lean source; leave prose untouched."""
    def repl(m):
        name = m.group(0)
        if _decl_shaped(name) and _entry(name) is not None:
            return link_witness(name)      # a MENTION in prose - no kind note; see annotate_witness
        return name
    return _TOKEN.sub(repl, text or "")

def render_cell_details():
    """Collapsible per-cell reasoning: glyph + the reason/witness behind every mark (witnesses auto-linked)."""
    out = ["<details>",
           "<summary><b>Why each cell</b> - the reason or witness behind every mark (click to expand)</summary>",
           ""]
    for c, d in CELLS.items():
        out.append(f"**{c}**")
        for k, _ in SLOTS:
            v = d.get(k)
            if k == "DYN":
                g = dyn_glyph(v)
                parts = str(v).strip().split(" ", 1) if v else []
                txt = parts[1] if len(parts) > 1 else ""
            else:
                st, txt = classify(v)
                # ONE source of truth for the glyph. This used to recompute `GLYPH[st]` here, so the
                # map said ≝ and this block said ✓ for the same cell - the page refuting itself on
                # every cell the kind-derivation touched. Both gates found it independently.
                g = cell_mark(v, k)
                # A `∅` cell carries a REASON, not a witness - never annotate a kind there.
                if st != "na":
                    txt = annotate_witness(txt)
            body = f" - {link_in_text(txt)}" if txt else ""
            out.append(f"- `{k}` {g}{body}")
        out.append("")
    out.append("</details>")
    return "\n".join(out)

# --- Front-door on-ramp: the same fixed point across disparate fields, tiered by confidence ---
# The witnesses named in the prose auto-link via link_in_text(); this list forces a fail-loud
# UNRESOLVED warning if any of them is renamed/moved (so the on-ramp cannot silently rot).
ROSETTA_WITNESSES = [
    "t_comp", "t_exec", "kleene_quine_is_bot", "addVal_bot", "t2_diverges",
    "mc1_correspondence", "completions_exhaustive", "real_not_equiv_padic",
    "fork_collapse_iff", "zpm_triangle",
]
def render_rosetta():
    for w in ROSETTA_WITNESSES:
        if witness_kind(w) is None:
            UNRESOLVED.append(w)
    body = """## The short version: concepts that should not coincide, but do

One self-referential structure - a thing that is its own fixed point - keeps turning up in fields that do not expect to meet. Here is each coincidence, ordered by how sure we are of it. Everything provable is checkable: clone the repo and run `#print axioms <name>`.

**Proved, with one commitment - the same element.** In any Kleene-structured ZP lattice, the *Quine atom* (a set that is its own only member, set theory / AFA), the *order-bottom* ⊥, and the *algebraic join-identity* are proved to be the **same element** - the three-name core, **axiom-free** (t_exec). The fourth name, the *Kleene fixed point* (a program that reproduces itself, computability), is *joined* to the other three by an explicit structural commitment: the KleeneStructure typeclass names the computational fixed point as the same role - the motivating commitment, not a derived theorem. So the set that is its own only member is identified with the program that prints itself by that commitment, not proved equal. The computational witness rests on Mathlib's recursion theorem, which carries `Classical.choice`; the three-name core needs none.

**Proved - each field's own floor.** 0 in the 2-adics, where v₂(0) = ∞ (addVal_bot); unbounded surprisal, the state with no finite description (t2_diverges); the categorical bottom of each real Mathlib category, an inverse limit or initial object (fD_zero_isInitial, fC_zero_isInitial and fB_bottom_is_limit, collected in mc1_correspondence); and the case where the coincidence *fails*, ℝ vs ℚ₂ by Ostrowski (completions_exhaustive, real_not_equiv_padic). They share a SHAPE (`Statement:` COINCIDENCE, per field's own witness above) - one object carrying both extremal characterisations at once - and a shared shape across distinct structures is a type boundary, never a common theorem. (The order-theoretic form of that shape is fork_collapse_iff, choice-free, but none of these satisfies its hypotheses of a complete lattice and a monotone map, so none is an instance of it.) ε₀ is co-witnessed with the 2-adic limit and the machine snap (zpm_triangle).

**Mostly proved - a narrow residue argued.** The framework's set-theoretic *commitment* is not *AFA specifically* but a fragment it assumes of its host theory: a unique Quine atom ⊥ = {⊥}. That fragment is a checkable object, the QuineHost typeclass. Foundation-freeness is *forced* by the Quine atom (quineHost_not_wellFounded, axiom-free - a self-loop cannot live in a well-founded world); ordinary set theory (Foundation) is excluded in-kernel about the real theory (zfSet_no_quine_bottom - no set is self-membered under Foundation); Boffa's axiom is set aside because it admits a proper class of Quine atoms rather than one (Boffa 1968), a gap a toy model makes concrete (boffa_fails_unique) rather than an in-kernel fact about Boffa's axiom; and AFA is exhibited as the example meeting all three (afaStructure_isQuineHost). What remains argued is only that a Quine atom and its uniqueness are the right two requirements - a Forced Metatheoretic Commitment with a named falsifier, stronger than a free choice and weaker than a theorem. The set-membership face ⊥ ∈ ⊥ stays metatheoretic; the structural fixed point is machine-checked and axiom-free (t_exec).

**The family - MC-1.** MC-1 names not one object but one **family**. Each of these floors is a member: it satisfies the shared criteria mapped in the slots below, with per-domain membership machine-verified where marked (the categorical criterion is the per-domain witnesses fD_zero_isInitial, fC_zero_isInitial and fB_bottom_is_limit, collected in mc1_correspondence). The *choice* of criteria is a design principle; that they characterize the family is an argument. The cross-category numerical identity - that the bottoms are *one and the same object* - is **retired** as ill-typed (`x = y` across distinct categories is not a well-formed proposition), and the members are provably **distinct** (the "walls" below). What survives is the proved leaves and the proved walls; the only oneness is the shared self-referential *shape* - the diagonal fixed point - which lives in the apophatic register, never as a formal identity. Within-frame identities stand (the three-name core above; 0 = ∞ under rInv in ℚ₂)."""
    return link_in_text(body)

# --- The diagonal family: the self-reference arguments as one fixed point (ZP-R) ---
# (face, side, what it says, witness-name, axiom footprint).  The witness column links via
# link_witness (fail-loud: an unresolved name lands in the UNRESOLVED warning, so a rename cannot
# silently rot). Axiom footprints are the #print axioms result of each witness, verified against source.
DIAGONAL_FAMILY = [
    ("Cantor",       "μ wall",  "no surjection onto its own power set - the reflexive object is refuted", "cantor_via_engine", "(none)"),
    ("Russell",      "μ wall",  "membership is not surjective - no set of all non-self-membered sets", "russell_via_engine", "(none)"),
    ("Turing",       "μ wall",  "no machine decides its own halting - no self-decider", "no_self_decider", "(none)"),
    ("Tarski",       "μ wall",  "no internal truth predicate - the liar sentence has no witness", "tarski_no_internal_truth", "(none)"),
    ("Curry",        "μ wall",  "no naming surjection - Curry's paradox forces any conclusion", "curry_no_bottom", "(none)"),
    ("the wall",     "μ",       "no well-founded relation admits a self-loop (the engine's floor)", "wf_no_selfloop", "(none)"),
    ("Gödel 1st",    "between", "the undecidable diagonal sentence, built by the shared engine", "lawvere_fixedpoint", "(none)"),
    ("Quine atom",   "ν floor", "the self-containing set ⊥ = {⊥} - executable self-reference, landing at ⊥", "t_exec", "(none)"),
    ("Löb",          "ν floor", "provability of (□A → A) yields A - the provability-logic fixed point", "loeb", "(none)"),
    ("Gödel 2nd",    "ν floor", "no consistent system proves its own consistency", "godel_two", "(none)"),
    ("Kleene quine", "ν floor", "a program that reproduces itself - the recursion theorem fires", "computability_face_fixedPoint", "`Classical.choice`"),
    ("Rice",         "ν floor", "the fixed point provably exists, yet its membership is undecidable", "rice_face_has_bottom", "`Classical.choice`"),
]

def render_diagonal_family():
    intro = """## The diagonal family - the self-reference arguments as one fixed point

The classical self-reference arguments are not separate theorems that happen to rhyme; they are one diagonal fixed point seen under different conditions (Lawvere 1969; Yanofsky 2003). The framework maps the full roster against ⊥, organized by the μ/ν fork and built off a single engine - negation_no_fixedpoint / lawvere_fixedpoint, both axiom-free. On the **wall** side (μ) self-reference cannot close: the argument runs as a proof that no reflexive object exists. On the **floor** side (ν) it does close - the fixed point is genuinely produced, and lands at ⊥. Cantor, Russell, Turing, Tarski, Curry, Löb, and Gödel's second incompleteness are all **axiom-free**; only the two computability floor faces (the Kleene quine and Rice's exists-but-undecidable) carry `Classical.choice`, inherited from Mathlib's recursion theory. This roster is ZP-R (the Cross-Category Fixed Point layer and its Diagonal Family Addendum) - a *placement* of ⊥ among recognized results, not a new theorem; the cross-face identity stays a type boundary, the same walls the map above records.

**See it:** the interactive [Diagonal Family](diagonal-family.html) map renders this roster as one engine forking into walls (μ) and floors (ν), each node linking its Lean witness and axiom footprint."""
    rows = [[face, side, gloss, link_witness(w), ax]
            for (face, side, gloss, w, ax) in DIAGONAL_FAMILY]
    table = render_table(rows, ["face", "side", "what it says", "witness", "axioms"])
    return link_in_text(intro) + "\n\n" + table

PAGE = """# The Bottom Element (⊥) - Dictionary and Map

*A dictionary and map of the framework's bottom element ⊥ - what it is, what it is not, and where each characterization is established, most with a machine-checked Lean witness linked to the source.*

[![Lean Action CI](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-ff69b4?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/timbrigham) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20060860.svg)](https://doi.org/10.5281/zenodo.20060860)

For the formal framework index and Lean verification, see [README](README.md). For plain-language introductions, companions, and reading paths, see [GUIDE](GUIDE.md). For the claim-by-claim status of every result, see the [Claims Ledger](CLAIMS.md).

---

## What this is

This is a **reference** for the framework's bottom element ⊥: a **dictionary** (what ⊥ is and is not) and a
**map** (where each characterization is established). It is a **beginning, not a resolution.** What is
*proved* is that each construction's bottom belongs to the family and that the slot structure recurs; the
reading that the various bottoms are *one object* is retired as ill-typed - they are provably distinct as
structures (the "walls"). It closes a standing gap: a framework built on ⊥ that had not yet characterized ⊥ itself.

---

{rosetta}

---

## Reading key (for a reader with no prior context)

**Slot codes** (the map columns, and the positive dictionary entries):

{slot_gloss}

**Constructions** (the map rows). A `#N` prefix (#2 Markov, #3 TopCat/p-adic limit, #4 Kleisli, #5 Hilbert
seam) cross-references the **bottom-diagram-tree nodes** used throughout the Lean source (`node #4`,
`seam node #5`, …). Only those four appear as numbered rows; the tree's order-floor node #1 is the abstract
`Lat ⊥` row (shown here without the number), and the other rows (Info, Kleene, ε₀, selfApp, the p-adic
valuation) come from other layers. The partial numbering is scoped, not missing data:

{construction_gloss}

**A few recurring terms:**

{terms}

---

## Dictionary

### ⊥ cannot be (characterization by exclusion)

{apophatic}

### ⊥ is (positive handles - the slots)

The handles sort by **aspect**: what ⊥ *is* (**noun**), what ⊥ *does* (**verb**), or **both at once**
(**hinge**). The hinge is ⊥'s signature: at the floor the two collapse - the fixed point that *is* a thing
and *acts on itself* in one step (operation = result). *This noun-and-verb reading, and the claim that they
collapse at ⊥, is the framework's interpretation; the slot witnesses below are proved, the lens over them is
not.*

{positive}

---

## Map - slot × construction

Where each characterization stands. Most columns are a **claim with a status**, not a checkbox: `✓` the witness states a proposition and the kernel checked it · `≝` **the cell's own sentence in *Why each cell* below says what the witness is** ·
`✗` refuted (a proved obstruction) · `∅` not-applicable by structure (a category
error - e.g. asking a ν-limit for a μ-generation property - not a gap). A trailing `*` (`✓*`, `≝*`, `↑*`, `↓*`) means conditional - established via a bridge or inherited from a sibling layer, a separate axis from `✓`/`≝`. The last column,
**dynamics**, is DIRECTIONAL instead: `↓` inbound (converges *to* ⊥ - a sink), `↑` outbound (departs *from* ⊥
irreversibly - a source), `↕` both (a seam). (The dictionary above links the witnesses it cites; each
map cell's own witness, or the reason it has none, is in *Why each cell* below.)

{map}

The informative content is in the non-`✓` cells, and splitting them is the point: a `∅`
is a settled structural fact (a category error, not a gap), a `✗` is news (a proved obstruction), a `✓*` holds only via a bridge, and a `≝` sends you to that cell's sentence. Two things worth reading off the table:
(1) **generation** (GEN) is the μ / build-up-from-the-floor side, so the ν-bottoms (p-adic, Markov, the TopCat
point-limit) read `∅` there - a ν-object has no μ-property - and the self-coincident fixed points (Kleene,
selfApp) carry SELF rather than GEN; GEN's one live cell is ε₀, where the floor generates a *distinct* ceiling.
(2) The **dynamics** column is single-directional - `↓` for a sink (ν), `↑` for a source (μ) - and `↕` (both)
appears *only* at a seam (μ=ν): the zero-object seam **#5 Hilbert**, and **ε₀**, whose row is itself the snap-arc
0→ε₀. So ⊥'s dynamics has one direction, fixed by whether ⊥ is a source or a sink.

**The structural reading is in the non-`✓` cells** - the proved obstructions (`✗`), the structural non-applicabilities (`∅`), and the `≝` cells, whose witness is named in its own sentence - not the
filled count. The full reasoning behind the `GEN` and `dynamics` columns is written up in
**[Structural Findings](BOTTOMELEMENT_findings.md)**; the reason or witness behind *every* mark is below.

{cell_details}

---

{diagonal_family}

---

*Generated from `bottom_cannot_be.md` and the matrix data by `build_dictionary_map.py`. Witness names are
resolved against the Lean source at generation time and link to the file that declares them; the `meta`
entries (marked as such) have no Lean witness. To update: edit a source and rerun. The links render
natively on GitHub.*
"""

def main():
    page = PAGE.format(
        rosetta=render_rosetta(),
        slot_gloss=render_slot_gloss(),
        construction_gloss=render_construction_gloss(),
        terms=render_terms(),
        apophatic=render_table([[c, render_witnesses(ws)] for (_i, c, ws) in APOPHATIC],
                               ["⊥ cannot be...", "witness (links to Lean source)"]),
        positive=render_table([[s, a, c, render_witnesses(ws)] for (s, a, c, ws) in POSITIVE],
                              ["slot", "aspect", "characterization of ⊥", "witness (links to Lean source)"]),
        map=render_map(),
        cell_details=render_cell_details(),
        diagonal_family=render_diagonal_family(),
    )
    # ⚠ CHECK BEFORE WRITING. The guard used to sit after `f.write(page)`, so a page whose marks
    # could not be justified was written to disk and only then did the process exit 1 — the exit
    # code failed closed while the artifact failed open, which is the worse half.
    if UNRESOLVED or UNRESOLVED_HEADS:
        if UNRESOLVED:
            print("UNRESOLVED witnesses - kind not derivable: " + ", ".join(sorted(set(UNRESOLVED))))
        if UNRESOLVED_HEADS:
            print("UNRESOLVED type heads - cannot tell asserted from constructed: "
                  + ", ".join(sorted(set(UNRESOLVED_HEADS))))
        print("REFUSING TO WRITE " + OUT)
        sys.exit(1)
    if AMBIGUOUS:
        print("AMBIGUOUS names refused (more than one declaration site, so not resolved): "
              + ", ".join(f"{n}" for n, _ in sorted(set((a, tuple(b)) for a, b in AMBIGUOUS))))
    if HEAD_BY_SUFFIX:
        print("type heads resolved by stripping a namespace (weaker step, reported not silent): "
              + ", ".join(f"{a}->{b}" for a, b in sorted(set(HEAD_BY_SUFFIX))))
    # newline="\n": Python's Windows default translates to CRLF, but `.gitattributes` declares
    # `* text=auto eol=lf`, so the committed and freshly-checked-out file is LF. The review-signal
    # scheme hashes the file ON DISK, so a CRLF working copy hashes differently from the same
    # content after a clean checkout and every signal would go stale. Measured: 291 CRLF / 0 LF
    # generated against 0 CRLF / 291 LF committed.
    with open(OUT, "w", encoding="utf-8", newline="\n") as f:
        f.write(page)
    print(f"wrote {OUT}")
    print(f"{sum(len(v) for v in INDEX.values())} declarations indexed · {len(APOPHATIC)} apophatic · {len(POSITIVE)} positive · "
          f"{len(CONSTRUCTION_GLOSS)} constructions · {len(CELLS)}x{len(SLOTS)} map")
    nonthm = sorted(n for n in _CITED if not is_proof(n))
    if nonthm:
        # ⚠ Do NOT claim these all render a kind note on the page. `link_in_text` deliberately
        # suppresses the note where a name is MENTIONED rather than cited as a witness, so most
        # of this list renders bare. Report what was found, not what the page does with it.
        print("Cited witnesses that are not theorems/lemmas: "
              + ", ".join(f"{n} [{witness_kind(n)}]" for n in nonthm))
    else:
        print("all cited witnesses are theorems/lemmas")
    # ⚠ Says only that every cited witness RESOLVED. It must not claim how each mark was reached:
    # the stated type is consulted for a minority of witnesses (a `theorem` short-circuits on the
    # keyword, a class field short-circuits before the type is read). Round 3 deleted that claim
    # from the page and it reappeared HERE, in the same commit - fix-the-site-not-the-class, and
    # this line ships in the public `scripts/` mirror.
    print("all cited witnesses resolved against the Lean source")

if __name__ == "__main__":
    main()
