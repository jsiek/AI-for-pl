"""Guardrail checks of plan section 7, as functions the harness calls.
Each returns a verdict dict {"ok": bool, ...details}; none modifies its
inputs.

  overlay(run, orig_c, edited_c)        7.1  annotation overlay
  spec_items(text) / frozen(base, ed)   7.2  hashes of the frozen spec
  lint_acsl(base, ed)                   7.3, 7.3a  agent-added axioms,
                                        admits and definitions
  lint_ghost(base, ed)                  7.3  ghost code: no loops, jumps,
                                        calls, writes of __heap
  lint_coq(path)                        7.3  Admitted, Axiom, admit, ...
                                        in a Coq proof script
  allow_list(axioms, wp_axioms)         7.4  coqchk / Print Assumptions
                                        against the allow-list
  accounting(goals, expected, ...)      7.5  every goal proved or out of
                                        scope

  directives(base, ed)                  7.1 (defence in depth): the
                                        preprocessor directives unchanged
  spec_checks(base, ed, cpp_args)       directives, then 7.2, 7.3 on the
                                        texts as Frama-C expands their
                                        annotations (frozen, lint_acsl,
                                        lint_ghost)

The ACSL parsing is textual (comments, strings and C braces are tracked;
annotations are `/*@ ... */` and `//@ ...`).  It is enough for the
benchmarks' style; the overlay check, which uses Frama-C's own parser,
does not depend on it.  The textual checks run on the source with the
macros inside its annotations expanded by Frama-C itself
(`acsl_expand.py`, plan Q11:
"the macros are expanded before the check"), so a spec written with the
templates of `bench/sglib_spec/` is hashed as the ACSL Frama-C reads.
"""
import hashlib
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ARIADNE, "prover"))
from reallms_coq import FORBIDDEN, split_goal  # noqa: E402
sys.path.insert(0, HERE)
from acsl_expand import acsl_code, annotations, expand  # noqa: E402,F401

RUN = os.path.join(ARIADNE, "env", "run.sh")

# ---- ACSL annotations ------------------------------------------------

DECL = ("predicate", "logic", "inductive", "axiomatic", "lemma", "axiom",
        "type")
# Definitions the agent may not add or change (plan 7.3a); lemmas it may
# add (they are proved), axioms never (lint_acsl).
DEFINITIONS = ("predicate", "logic", "inductive", "axiomatic", "type")


def _declarations(code):
    """Split a file-scope logic block into its declarations: each starts
    at a DECL keyword at brace depth 0, after the start, `;` or `}`."""
    starts, depth = [], 0
    for m in re.finditer(r"[{}]|\b(" + "|".join(DECL) + r")\b", code):
        tok = m.group(0)
        if tok in "{}":
            depth += 1 if tok == "{" else -1
            continue
        before = code[:m.start()].rstrip()
        if depth == 0 and (not before or before[-1] in ";}"):
            starts.append((m.start(), tok))
    out = []
    for k, (s, kind) in enumerate(starts):
        e = starts[k + 1][0] if k + 1 < len(starts) else len(code)
        decl = code[s:e].strip()
        head = re.split(r"[({=:;]", decl, maxsplit=1)[0]
        names = re.findall(r"[A-Za-z_]\w*", head)
        out.append((kind, names[-1] if len(names) > 1 else "?", decl))
    return out


def spec_items(text):
    """The specification items of a C file, as {key: code}: file-scope
    declarations (`predicate:live`, `lemma:mem_cons`, ...) and function
    contracts (`contract:sglib_dllist_add`: the file-scope annotation
    just before a function's declaration or definition).  Annotations
    inside function bodies (asserts, loop annotations, ghost code) are
    not spec items."""
    items = {}
    for depth, _, end, body in annotations(text):
        if depth:
            continue
        code = acsl_code(body)
        if not code:
            continue
        if re.match(r"(" + "|".join(DECL) + r")\b", code):
            for kind, name, decl in _declarations(code):
                key = f"{kind}:{name}"
                while key in items:  # overloading, or a repeated name
                    key += "'"
                items[key] = decl
        else:
            m = re.search(r"([A-Za-z_]\w*)\s*\(", text[end:])
            key = f"contract:{m.group(1) if m else '?'}"
            items[key] = (items[key] + " " + code) if key in items else code
    return items


def digest(code):
    return hashlib.sha256(code.encode()).hexdigest()[:16]


def frozen(base_text, edited_text):
    """Plan 7.2 (and 7.3a): the function contracts and the logic
    definitions of the edited file must be those of the frozen
    baseline, item for item (hash of the comment-free, whitespace-
    normalised text).  Lemmas are not frozen: the agent may add them,
    and each one is proved."""
    def frozen_items(text):
        return {k: digest(v) for k, v in spec_items(text).items()
                if k.split(":")[0] in DEFINITIONS + ("contract",)}
    base, ed = frozen_items(base_text), frozen_items(edited_text)
    changed = sorted(k for k in base if k in ed and base[k] != ed[k])
    removed = sorted(k for k in base if k not in ed)
    added = sorted(k for k in ed if k not in base)
    return {"ok": not (changed or removed or added),
            "items": len(base),
            "digest": digest(" ".join(f"{k}={v}"
                                      for k, v in sorted(base.items()))),
            "changed": changed, "removed": removed, "added": added}


ACSL_FORBIDDEN = ("axiom", "axiomatic", "admit") + DEFINITIONS


def lint_acsl(base_text, edited_text):
    """Plan 7.3 / 7.3a: the edited file may not have more `axiom`,
    `axiomatic`, `admit`, `logic`, `predicate`, `inductive` or `type`
    keywords in its annotations than the baseline."""
    def counts(text):
        code = " ".join(acsl_code(b) for _, _, _, b in annotations(text))
        return {k: len(re.findall(rf"\b{k}\b", code))
                for k in ACSL_FORBIDDEN}
    base, ed = counts(base_text), counts(edited_text)
    added = {k: ed[k] - base[k] for k in ACSL_FORBIDDEN if ed[k] > base[k]}
    return {"ok": not added, "added": added}


GHOST_FORBIDDEN = ("while", "for", "do", "goto", "break", "continue",
                   "return", "__heap", "ariadne_alloc", "ariadne_free",
                   "assigns")


def lint_ghost(base_text, edited_text):
    """Ghost code the agent adds may only declare and assign ghost
    variables.  WP does not prove termination here (terminates:skip), so
    a ghost loop such as `while (1);` would make every later goal
    vacuous; ghost jumps and returns could change the control flow; and
    writing `__heap` (or calling the allocators) would edit the frozen
    liveness model.  So, in ghost annotations, no more loops, jumps,
    returns, `__heap`, allocator calls, or ghost function contracts than
    the baseline has, and no ghost function calls at all beyond it."""
    def counts(text):
        code = " ".join(acsl_code(b) for _, _, _, b in annotations(text)
                        if re.match(r"\s*ghost\b", b))
        c = {k: len(re.findall(rf"\b{k}\b", code)) for k in GHOST_FORBIDDEN}
        # a call: an identifier followed by `(` that is not a cast or a
        # keyword (sizeof and the ACSL built-ins start with `\`), or any
        # `(` right after `)`, which also covers `(f)(x)` and `(*fp)(x)`
        # (and so refuses a cast of a parenthesised operand, `(int)(x)`)
        c["call"] = len([m for m in re.finditer(r"\b([A-Za-z_]\w*)\s*\(",
                                                code)
                         if m.group(1) not in ("sizeof", "if", "switch")
                         + GHOST_FORBIDDEN]) \
            + len(re.findall(r"\)\s*\(", code))
        return c
    base, ed = counts(base_text), counts(edited_text)
    added = {k: ed[k] - base[k] for k in ed if ed[k] > base[k]}
    return {"ok": not added, "added": added}


def preprocessor_lines(text):
    """The preprocessor directives of C text, in order: every line whose
    first character outside comments (ACSL annotations included) is `#`,
    with its backslash continuations joined and whitespace collapsed."""
    out, i, n = [], 0, len(text)
    buf = []
    while i < n:      # comments -> spaces (newlines kept); strings kept
        if text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            buf.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
        elif text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            buf.append(" " * (j - i))
            i = j
        elif text[i] in "\"'":
            q, j = text[i], i + 1
            while j < n and text[j] != q and text[j] != "\n":
                j += 2 if text[j] == "\\" else 1
            buf.append(text[i:j + 1])
            i = j + 1
        else:
            buf.append(text[i])
            i += 1
    code = "".join(buf).replace("\\\n", " ")
    for line in code.split("\n"):
        if line.lstrip().startswith("#"):
            out.append(" ".join(line.split()))
    return out


def directives(base_text, edited_text):
    """Defence in depth for the overlay rule (7.1): the edited source has
    exactly the baseline's preprocessor directives, in order.  The
    overlay check compares code after preprocessing, so an added
    `#define` or `#if` (which can change what Frama-C reads inside
    annotations) would pass it.  No pipeline step adds directives: the
    annotator writes annotations only.  The baseline is the benchmark's
    source as committed, so it already carries the logged changes (plan
    Q11's bug fixes and verification refactors, each in the benchmark's
    CHANGES.md): a fix found in a run enters the baseline by being
    applied to the benchmark with its log entry, and only then.  So a
    directive changed in a run, logged or not, fails here; that the
    benchmark's own changes are exactly the logged ones is the
    certification diff's check (Q11, final product 4)."""
    a, b = preprocessor_lines(base_text), preprocessor_lines(edited_text)
    if a == b:
        return {"ok": True, "directives": len(a)}
    k = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y),
             min(len(a), len(b)))
    return {"ok": False, "first_difference": k,
            "original": a[k] if k < len(a) else "(none)",
            "edited": b[k] if k < len(b) else "(none)"}


def spec_checks(base_text, edited_text, cpp_args, work=None):
    """directives, then frozen, lint_acsl and lint_ghost of the edited
    source against the baseline, both with the macros inside their
    annotations expanded as Frama-C expands them (acsl_expand.py):
    {check: verdict}.  A source Frama-C cannot preprocess fails the
    three expanded checks."""
    v = {"directives": directives(base_text, edited_text)}
    try:
        base = expand(base_text, cpp_args, work)
        ed = expand(edited_text, cpp_args, work)
    except RuntimeError as e:
        bad = {"ok": False, "error": str(e)[:2000]}
        v.update({"frozen_spec": bad, "lint_acsl": bad, "lint_ghost": bad})
        return v
    v.update({"frozen_spec": frozen(base, ed),
              "lint_acsl": lint_acsl(base, ed),
              "lint_ghost": lint_ghost(base, ed)})
    return v


def strip_annotations(text):
    """The C text with every ACSL annotation (and so all ghost code)
    replaced by a space."""
    out, last = [], 0
    for _, s, e, _ in annotations(text):
        out.append(text[last:s])
        out.append(" ")
        last = e
    out.append(text[last:])
    return "".join(out)


def frama_print(run_dir, text, cpp_args, log):
    """`frama-c -no-annot -print` of C text (written to a temporary
    file, always under the same name so the output cannot differ by
    file name); None if Frama-C fails."""
    d = tempfile.mkdtemp(dir=run_dir, prefix="overlay_")
    try:
        with open(os.path.join(d, "src.c"), "w") as f:
            f.write(text)
        r = subprocess.run([RUN, "frama-c", f"-cpp-extra-args={cpp_args}",
                            "-no-annot", "src.c", "-print", "-ocode",
                            "out.c"], cwd=d, capture_output=True,
                           text=True)
        with open(log, "a") as f:
            f.write(r.stdout + r.stderr)
        if r.returncode:
            return None
        return open(os.path.join(d, "out.c")).read()
    finally:
        subprocess.run(["rm", "-rf", d])


def overlay(run_dir, orig_text, edited_text, cpp_args, log):
    """Plan 7.1: with annotations and ghost code stripped, the edited C
    must normalise (`frama-c -no-annot -print`) to exactly the
    original's.  Stripping is done twice: textually here, and by
    Frama-C's `-no-annot`."""
    a = frama_print(run_dir, strip_annotations(orig_text), cpp_args, log)
    b = frama_print(run_dir, strip_annotations(edited_text), cpp_args, log)
    if a is None or b is None:
        return {"ok": False, "error": "frama-c -print failed"}
    if a == b:
        return {"ok": True, "normalised_lines": a.count("\n")}
    al, bl = a.splitlines(), b.splitlines()
    k = next((i for i, (x, y) in enumerate(zip(al, bl)) if x != y),
             min(len(al), len(bl)))
    return {"ok": False, "first_difference_line": k + 1,
            "original": al[k] if k < len(al) else "(end)",
            "edited": bl[k] if k < len(bl) else "(end)"}


# ---- Coq -------------------------------------------------------------

def lint_coq(path, wp_prefix=None):
    """Plan 7.3: the proof script of a WP goal file (between the goal's
    `Proof.` and `Qed.`) uses no Admitted, Axiom, admit, Parameter, ...
    (reallms_coq.FORBIDDEN, the prover's own rule), and, when WP's own
    version of the file is given, the text outside the script is WP's."""
    text = open(path).read()
    try:
        prefix, script, suffix = split_goal(text)
    except SystemExit:
        return {"ok": False, "error": "no `Theorem wp_goal ... Qed.`"}
    bad = sorted(set(m.group(1) for m in FORBIDDEN.finditer(script)))
    v = {"ok": not bad, "forbidden": bad}
    if suffix.strip() != "Qed.":
        v.update(ok=False, error="text after the proof's Qed.")
    if wp_prefix is not None and prefix != wp_prefix:
        v.update(ok=False, error="context differs from WP's")
    return v


ALLOWED_STDLIB = {
    # Rocq's classical axioms, used by Why3's Coq realisations.
    "Stdlib.Logic.Classical_Prop.classic",
    "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep",
    "Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq",
    "Stdlib.Logic.ClassicalEpsilon.constructive_indefinite_description",
    "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec",
    "Stdlib.Reals.ClassicalDedekindReals.sig_not_dec",
}


def wp_axioms(prefix):
    """Names a WP goal file's context declares as Axiom or Parameter:
    Why3's theories and the frozen ACSL spec, as WP exports them (plan
    7.3a; earlier lemmas appear as axioms too, each proved as its own
    goal)."""
    return set(re.findall(r"^(?:Axiom|Parameter)\s+([A-Za-z_][\w']*)",
                          prefix, re.M))


def coqchk_axioms(output):
    """The axiom names `coqchk -o` lists (section "Axioms:")."""
    m = re.search(r"\* Axioms:\s*\n(.*?)\n\s*\n?\s*\*", output, re.S)
    if not m:
        return None
    return [x.strip() for x in m.group(1).splitlines() if x.strip()]


def allow_list(axioms, module_axioms):
    """Plan 7.4: every axiom must be a Rocq classical axiom of the fixed
    list, a Why3 library axiom, or `<Module>.<name>` where <name> is
    declared in the WP-generated context of that module's goal file
    (`module_axioms`: module -> names).  Anything else fails."""
    bad = []
    for a in axioms:
        if a in ALLOWED_STDLIB or a.startswith("Why3."):
            continue
        mod, _, name = a.rpartition(".")
        if name in module_axioms.get(mod, ()):
            continue
        bad.append(a)
    return {"ok": not bad, "axioms": len(axioms), "not_allowed": bad}


# ---- goal accounting -------------------------------------------------

def accounting(goals, expected, out_of_scope=(), coq_certified=None):
    """Plan 7.5: every goal has a discharger (Qed, an SMT prover, Coq)
    or is explicitly out of scope; each pass has its expected number of
    goals (a selection that silently shrinks fails), or at least
    `{"min": n}` of them when the annotator adds annotations; and a goal claimed
    by Coq is one whose script step 6 certified (`coq_certified`, a set
    of goal names, when given)."""
    by_pass = {}
    for g in goals:
        by_pass[g["pass"]] = by_pass.get(g["pass"], 0) + 1
    counts = {p: {"goals": by_pass.get(p, 0), "expected": n}
              for p, n in expected.items()}

    def wrong(c):  # an exact count, or {"min": n} once annotations vary
        e = c["expected"]
        return c["goals"] < e["min"] if isinstance(e, dict) \
            else c["goals"] != e
    wrong_counts = sorted(p for p, c in counts.items() if wrong(c))
    oos = set(out_of_scope)
    unproved = [g["goal"] for g in goals
                if g["discharger"] == "open" and g["goal"] not in oos]
    uncertified = []
    if coq_certified is not None:
        uncertified = [g["goal"] for g in goals if g["discharger"] == "coq"
                       and g["goal"] not in coq_certified]
    return {"ok": not (wrong_counts or unproved or uncertified),
            "counts": counts, "wrong_counts": wrong_counts,
            "unproved": unproved, "out_of_scope": sorted(oos),
            "coq_uncertified": uncertified}
