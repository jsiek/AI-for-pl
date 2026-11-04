"""Generate the E-ACSL build input b1_rac.c from b1.c (or a mutant of it).

   usage: python3 -I gen_rac.py <b1.c> <outdir>

Writes <outdir>/b1_rac.c, <outdir>/b1_types.h (b1.c's generated part 1,
for the twins and the allocator), and <outdir>/annotations.txt (what
happened to every annotation).  The rules are in README.md ("Translation
rules"); in short:

  * the spec block is replaced by rac_spec.h (hand-written executable
    version, guarded by a hash of the block), ariadne_alloc.h by rac.h;
  * every annotation is split into clauses, and an assert / requires /
    ensures / invariant whose predicate is a conjunction into conjuncts;
  * a binder over a list or pointer variable is eliminated by a witness
    taken from a dll / live_dll conjunct that determines the variable
    (W1-W4 in the README); integer binders stay; a clause or conjunct
    with a binder that has no witness is dropped, with the reason;
  * \\nth, \\length, \\Cons, \\Nil become the twins rac_nth, rac_length,
    rac_cons, and the NULL handle;
  * assigns clauses are dropped (E-ACSL does not check them).

Nothing is translated by hand per annotation: a new annotation in b1.c
goes through the same rules, and one they cannot handle is reported as
dropped (never silently kept in a non-executable form)."""
import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
src_path, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
src = open(src_path).read()
report = []

# ---------------------------------------------------------------- blocks

P1_BEGIN = "/* BEGIN GENERATED (b1_gen.c), part 1: types */\n"
P1_END = "/* END GENERATED, part 1 */\n"
a = src.index(P1_BEGIN) + len(P1_BEGIN)
b = src.index(P1_END)
open(os.path.join(out, "b1_types.h"), "w").write(
    "/* b1.c's generated part 1, written by gen_rac.py */\n"
    "#ifndef B1_TYPES_H\n#define B1_TYPES_H\n#include <stddef.h>\n"
    + src[a:b] + "#endif\n")

SPEC_BEGIN = "/*@ // p is a usable list node"
s0 = src.index(SPEC_BEGIN)
s1 = src.index("*/", s0) + 2
spec = src[s0:s1]
digest = hashlib.sha256(spec.encode()).hexdigest()
rac_spec = open(os.path.join(HERE, "rac_spec.h")).read()
m = re.search(r"spec-sha256: (\w+)", rac_spec)
if not m or m.group(1) != digest:
    sys.exit(f"gen_rac.py: b1.c's spec block changed (sha256 {digest});\n"
             "review rac_spec.h against it, then update its spec-sha256 line")
assert src.count('#include "ariadne_alloc.h"') == 1
head = src[:s0].replace('#include "ariadne_alloc.h"', '#include "rac.h"')
body = src[s1:]
line_base = src[:s1].count("\n")

# ---------------------------------------------------------------- parsing


def match_paren(t, i):
    """t[i] is '(' (or '{'); index just after its partner."""
    depth = 0
    for j in range(i, len(t)):
        if t[j] in "({":
            depth += 1
        elif t[j] in ")}":
            depth -= 1
            if depth == 0:
                return j + 1
    raise ValueError("unbalanced: " + t[i:])


def split_top(t, sep):
    """Split t at top-level occurrences of sep (not inside parens, and not
    inside the body of a binder, which extends to the end)."""
    parts, depth, last, i = [], 0, 0, 0
    while i < len(t):
        c = t[i]
        if c in "({":
            depth += 1
        elif c in ")}":
            depth -= 1
        elif depth == 0 and re.match(r"\\(forall|exists|let)\b", t[i:]):
            break  # a binder's body runs to the end of t
        elif depth == 0 and t.startswith(sep, i):
            parts.append(t[last:i])
            last = i + len(sep)
            i += len(sep)
            continue
        i += 1
    parts.append(t[last:])
    return [p.strip() for p in parts]


def body_end(t, i):
    """End of a binder body starting at t[i]: the first unmatched ')'."""
    depth = 0
    for j in range(i, len(t)):
        if t[j] in "({":
            depth += 1
        elif t[j] in ")}":
            if depth == 0:
                return j
            depth -= 1
    return len(t)


def parse_binders(text):
    """'dllist *p, *h, \\list<dllist *> s, integer k' -> [(type, name)]."""
    out, ty = [], None
    for item in [x.strip() for x in text.split(",")]:
        m = re.match(r"(\\list<dllist \*>|dllist|integer|char)\s*(.*)", item)
        if m:
            ty, item = m.group(1), m.group(2)
        star = item.startswith("*")
        name = item.lstrip("*").strip()
        kind = ("list" if ty.startswith("\\list") else
                "int" if ty == "integer" else "ptr")
        out.append((kind, name, ty + (" *" if star else "")))
    return out


DLL = re.compile(r"(live_dll|dll)(\{(\w+)\})?\(")


def dll_args(conj):
    """If conj is (live_)dll{L}(P, H, S) exactly: (label, P, H, S)."""
    m = DLL.match(conj)
    if not m:
        return None
    i = m.end() - 1
    j = match_paren(conj, i)
    if j != len(conj):
        return None
    args = split_top(conj[i + 1:j - 1], ",")
    if len(args) != 3:
        return None
    return m.group(3), args[0], args[1], args[2]


def stable(h, label):
    """h evaluates to the same value at label as here: a constant, or an
    \\at(..., label) term (so the witness can be computed at label)."""
    if h in ("\\null",):
        return True
    m = re.match(r"\\at\((.*), (\w+)\)$", h)
    return bool(m) and m.group(2) == label and match_paren(h, 3) == len(h)


def at(term, label):
    return term if label in (None, "Here") else f"\\at({term}, {label})"


def witnesses(kind, binders, conjs):
    """Witness definitions [(name, term, rule)] for the list/pointer
    binders, from the determining dll conjuncts; None if some binder has
    none.  The binders' scope is conjs (a conjunction)."""
    names = {n for _, n, _ in binders}
    lets, todo = {}, [b for b in binders if b[0] != "int"]
    for conj in conjs:
        d = dll_args(conj)
        if not d:
            continue
        label, p, h, s = d
        if not (label is None or stable(h, label)) and \
           any(n in (p, h, s) or re.search(rf"\b{n}\b", s) for n in names):
            return None, f"witness would be computed at {label} from a " \
                         "value read here"
        for k, n, _ in todo:
            if n in lets:
                continue
            if k == "list" and s == n and h not in names:
                lets[n] = (at(f"rac_reach({h})", label), "W1 reach")
            elif k == "list" and re.fullmatch(rf"\\Cons\((.+), {n}\)", s) \
                    and h not in names:
                lets[n] = (at(f"rac_tail(rac_reach({h}))", label),
                           "W2 tail of reach")
            elif k == "ptr" and p == n and h not in names:
                lets[n] = (at(f"rac_prev({h})", label), "W3 prev")
            elif k == "ptr" and h == n and p == "\\null" and kind == "exists":
                # W4: the head of the list that contains some named node x
                for c in conjs:
                    mm = re.fullmatch(
                        rf"(?:(.+) == \\nth\({s}, .+\)|\\nth\({s}, .+\) == (.+))",
                        c)
                    x = mm and (mm.group(1) or mm.group(2))
                    if x and not any(re.search(rf"\b{v}\b", x) for v in names):
                        lets[n] = (at(f"rac_head({x})", label), "W4 head")
                        break
                if n in lets and s in names and s not in lets:
                    lets[s] = (at(f"rac_reach({n})", label), "W1 reach")
    missing = [n for k, n, _ in todo if n not in lets]
    if missing:
        return None, "no witness for " + ", ".join(missing)
    # order: heads, then the rest (a list may be reached from a head)
    order = sorted(lets, key=lambda n: 0 if lets[n][1] == "W4 head" else 1)
    return [(n,) + lets[n] for n in order], None


def elim_binders(t, notes):
    """Rewrite every \\forall / \\exists over lists or pointers in t; raise
    Drop if one cannot be eliminated."""
    m = re.search(r"\\(forall|exists) ", t)
    if not m:
        return t
    kind = m.group(1)
    semi = t.index(";", m.end())
    binders = parse_binders(t[m.end():semi])
    start = semi + 1
    end = body_end(t, start)
    bod = elim_binders(t[start:end].strip(), notes)
    tail = elim_binders(t[end:], notes)
    if all(k == "int" for k, _, _ in binders):
        return t[:start] + " " + bod + tail
    if kind == "forall":
        if any(k == "ptr" for k, _, _ in binders):
            raise Drop("\\forall over pointers (no finite range)")
        prem = split_top(bod, "==>")
        if len(prem) < 2:
            raise Drop("\\forall over all lists")
        lets, why = witnesses(kind, binders, split_top(prem[0], "&&"))
        if lets is None:
            raise Drop("\\forall over lists: " + why)
        new = bod
    else:
        conjs = split_top(bod, "&&")
        lets, why = witnesses(kind, binders, conjs)
        if lets is None:
            raise Drop("\\exists: " + why)
        ints = [(n, ty) for k, n, ty in binders if k == "int"]
        if ints:
            # conjuncts that mention no integer binder come first
            def uses(c):
                return any(re.search(rf"\b{n}\b", c) for n, _ in ints)
            first = [c for c in conjs if not uses(c)]
            rest = [c for c in conjs if uses(c)]
            ex = "\\exists integer " + ", ".join(n for n, _ in ints) + "; " \
                + " && ".join(rest)
            new = " && ".join(first + [f"({ex})"])
        else:
            new = bod
    # E-ACSL 33 has no \\let on pointers: substitute each witness for its
    # variable (heads first, so a list reached from a head gets it too).
    terms = [term for _, term, _ in lets]
    for i, (n, term, rule) in enumerate(lets):
        notes.append(f"{n} := {term} [{rule}]")

        def sub(x, n=n, term=terms[i]):
            return re.sub(rf"(?<![\\\w>.]){n}\b", lambda _: term, x)
        new = sub(new)
        terms = terms[:i + 1] + [sub(x) for x in terms[i + 1:]]
    return t[:m.start()] + "(" + new + ")" + tail


class Drop(Exception):
    pass


def subst_lists(t):
    out, i = "", 0
    while i < len(t):
        if t.startswith("\\nth(", i):
            j = match_paren(t, i + 4)
            args = split_top(t[i + 5:j - 1], ",")
            out += f"rac_nth({subst_lists(args[0])}, " \
                   f"(long)({subst_lists(args[1])}))"
            i = j
            continue
        out += t[i]
        i += 1
    out = out.replace("\\length(", "rac_length(").replace("\\Cons(", "rac_cons(")
    return out.replace("\\Nil", "(rac_list)0")


def base_addr(p):
    """heap(\\base_addr(X)) -> heap_of((void *)(X)), and dead(v,
    \\base_addr(X)) -> dead_of((void *)(X)): E-ACSL 33 has no \\base_addr."""
    for pat, name in ((r"heap\(\\base_addr\(", "heap_of"),
                      (r"dead\(__heap, \\base_addr\(", "dead_of")):
        while True:
            m = re.search(pat, p)
            if not m:
                break
            j = match_paren(p, m.end() - 1)   # end of \\base_addr(...)
            x = p[m.end():j - 1]
            assert p[j] == ")", p
            p = p[:m.start()] + f"{name}((void *)({x}))" + p[j + 1:]
    if "\\base_addr" in p:
        raise Drop("\\base_addr outside heap/dead (E-ACSL: not supported)")
    return p


def labels(p):
    """P{L}(args) -> \\at(P(args), L) when every argument has the same
    value at L as here (E-ACSL 33 has no predicates with labels)."""
    out, i = "", 0
    for m in re.finditer(r"\b(\w+)\{(\w+)\}\(", p):
        if m.start() < i:
            continue
        j = match_paren(p, m.end() - 1)
        args = split_top(p[m.end():j - 1], ",")
        if not all(stable(a, m.group(2)) for a in args):
            raise Drop(f"{m.group(1)}{{{m.group(2)}}} with an argument read "
                       "here (E-ACSL: no predicates with labels)")
        out += p[i:m.start()] + \
            f"\\at({m.group(1)}({p[m.end():j - 1]}), {m.group(2)})"
        i = j
    return out + p[i:]


# Each twin: result type for the wrapper (None: an int used as such) and
# its parameter kinds (node: a pointer, passed as is; else cast to long).
TWIN_SIG = {"length": (None, "l"), "dll": (None, "nnl"),
            "nth": ("dllist *", "ll"), "head": ("dllist *", "n"),
            "prev": ("dllist *", "n"), "reach": ("rac_list", "n"),
            "tail": ("rac_list", "l"), "cons": ("rac_list", "nl")}


PREDS = ("live_dll", "dll", "mem", "all_live", "all_init", "live",
         "in_live_list", "iter_ok")


def null_args(t):
    """\\null as an argument of a spec predicate -> rac_null (a C global
    dllist * equal to NULL): E-ACSL 33 specialises a predicate by the
    integer range of its arguments and typed a node parameter called with
    \\null as int, which then truncated the real nodes passed to it."""
    out, i = "", 0
    pat = re.compile(r"\b(" + "|".join(PREDS) + r")(\{\w+\})?\(")
    while True:
        m = pat.search(t, i)
        if not m:
            return out + t[i:]
        j = match_paren(t, m.end() - 1)
        args = [null_args(a) for a in split_top(t[m.end():j - 1], ",")]
        args = ["rac_null" if a == "\\null" else a for a in args]
        out += t[i:m.end()] + ", ".join(args) + ")"
        i = j


def wrap(t):
    """Write each twin call rac_f(a, ...) as E-ACSL 33 accepts it: a call
    whose value is a node or a list is hidden behind integer arithmetic
    and a cast, (T)(0 + rac_f(...)), because E-ACSL rejects a function
    application as an argument of a predicate or of \\valid; list and
    index arguments are cast to long (the builtins' C type)."""
    t = null_args(t)
    out, i = "", 0
    pat = re.compile(r"\brac_(" + "|".join(TWIN_SIG) + r")\(")
    while True:
        m = pat.search(t, i)
        if not m:
            return out + t[i:]
        j = match_paren(t, m.end() - 1)
        ty, kinds = TWIN_SIG[m.group(1)]
        args = [wrap(a) for a in split_top(t[m.end():j - 1], ",")]
        assert len(args) == len(kinds), (m.group(0), args)
        call = f"rac_{m.group(1)}(" + ", ".join(
            a if k == "n" or a.startswith("(long)") else f"(long)({a})"
            for a, k in zip(args, kinds)) + ")"
        out += t[i:m.start()] + (f"({ty})(0 + {call})" if ty else call)
        i = j


def tr_pred(p, notes):
    """Translate one predicate; raise Drop."""
    p = elim_binders(p, notes)
    if "\\list" in p:
        raise Drop("list type left after binder elimination")
    return wrap(labels(base_addr(subst_lists(p))))


KEYWORDS = r"(requires|ensures|assigns|assert|check|loop invariant|" \
           r"loop assigns|loop variant)\b"


def clauses(text):
    """Split an annotation into clauses, each starting with a keyword at
    paren depth 0 at the start or after ';'."""
    pos, depth, i, prev_semi = [], 0, 0, True
    while i < len(text):
        c = text[i]
        if c in "({":
            depth += 1
        elif c in ")}":
            depth -= 1
        elif c == ";" and depth == 0:
            prev_semi = True
        elif not c.isspace():
            if depth == 0 and prev_semi and re.match(KEYWORDS, text[i:]):
                pos.append(i)
            prev_semi = False
        i += 1
    return [text[a:b].strip() for a, b in zip(pos, pos[1:] + [len(text)])]


def tr_clause(c, where):
    m = re.match(KEYWORDS, c)
    kw = m.group(1)
    rest = c[m.end():].strip()
    if rest.endswith(";"):
        rest = rest[:-1].rstrip()
    if kw in ("assigns", "loop assigns"):
        report.append(f"{where}: {kw}: dropped (E-ACSL does not check "
                      "assigns)")
        return None
    names = ""
    while True:
        mm = re.match(r"(\w+)\s*:(?!:)\s*", rest)
        if not mm or mm.group(1) in ("rte",):
            break
        names += mm.group(1) + ": "
        rest = rest[mm.end():]
    label = f"{kw} {names}".strip().rstrip(":")
    conjs = split_top(rest, "&&") if kw != "loop variant" else [rest]
    kept, dropped, notes = [], [], []
    for cj in conjs:
        try:
            kept.append(tr_pred(cj, notes))
        except Drop as e:
            dropped.append(str(e))
    if not kept:
        report.append(f"{where}: {label}: dropped ({'; '.join(dropped)})")
        return None
    same = not dropped and kept == conjs
    status = "kept" if same else "partly-kept" if dropped else "rewritten"
    detail = []
    if notes:
        detail.append("witnesses " + ", ".join(notes))
    if dropped:
        detail.append(f"{len(dropped)} of {len(conjs)} conjuncts dropped: "
                      + "; ".join(dropped))
    report.append(f"{where}: {label}: {status}"
                  + (f" ({'; '.join(detail)})" if detail else ""))
    return f"{kw} {names}" + " && ".join(kept) + ";"


ANNOT = re.compile(r"/\*@(.*?)\*/|//@([^\n]*)", re.S)


def tr_annot(m):
    lineno = line_base + body[:m.start()].count("\n") + 1
    text = m.group(1) if m.group(1) is not None else m.group(2)
    if text.strip() in ("ARIADNE_ALLOC", "ARIADNE_FREE"):
        return m.group(0)
    text = re.sub(r"//[^\n]*", "", text)  # comments inside annotations
    out = [x for x in (tr_clause(c, f"b1.c:{lineno}") for c in clauses(text))
           if x]
    if not out:
        return f"/* (annotation at b1.c:{lineno} dropped, see annotations.txt) */"
    return "/*@ " + "\n    ".join(out) + " */"


body = ANNOT.sub(tr_annot, body)
open(os.path.join(out, "b1_rac.c"), "w").write(
    "/* Generated by gen_rac.py from " + os.path.basename(src_path)
    + "; do not edit. */\n" + head
    + "/* rac_spec.h, twin calls written for E-ACSL (gen_rac.py, wrap) */\n"
    + re.sub(r"/\*@.*?\*/", lambda m: wrap(m.group(0)), rac_spec, flags=re.S)
    + body
    + "\n/* RAC harness (E-ACSL build): allocators and driver. */\n"
      "#define RAC_IN_B1\n#include \"rac_alloc.c\"\n#include \"rac_main.c\"\n")
open(os.path.join(out, "annotations.txt"), "w").write("\n".join(report) + "\n")
counts = {}
for r in report:
    k = re.search(r": (kept|partly-kept|rewritten|dropped)\b", r).group(1)
    counts[k] = counts.get(k, 0) + 1
print("gen_rac: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items()))
      + " clauses")
