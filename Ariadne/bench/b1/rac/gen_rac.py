"""Generate the E-ACSL build input b1_rac.c from b1.c (or a mutant of it).

   usage: python3 -I gen_rac.py <b1.c> <outdir> <twins dir>
                                [--name NAME] [--no-harness]

Writes <outdir>/b1_rac.c, <outdir>/b1_types.h (b1.c's generated part 1,
for the twins and the allocator), and <outdir>/annotations.txt (what
happened to every annotation).  With --name NAME (another client of the
same spec, e.g. sglib's self-test), the output is NAME_rac.c and
annotations are reported as NAME.c:LINE; a source without the part-1
markers gets no types header; --no-harness leaves out B1's allocators
and driver (rac_alloc.c, rac_main.c), for a source with its own.  The rules are in README.md ("Translation
rules"); in short:

  * the spec block is replaced by rac_spec.h, generated from it by
    ../../../rac/gen_twins.py into <twins dir> (with rac_twins.json, the
    manifest read here), and found by its hash; ariadne_alloc.h by rac.h;
  * every annotation is split into clauses, and an assert / requires /
    ensures / invariant whose predicate is a conjunction into conjuncts;
  * a binder over a list or pointer variable is eliminated by a witness
    taken from a conjunct that determines the variable: an application of
    a predicate with witness functions in the manifest (gen_twins.py
    derives them from each inductive's cases); integer binders stay; a
    clause or conjunct with a binder that has no witness is dropped, with
    the reason;
  * \\nth, \\length, \\Cons, \\Nil become the twins rac_nth, rac_length,
    rac_cons, and the NULL handle;
  * a conjunct that uses a spec definition gen_twins.py could not
    translate (the manifest's "dropped") is dropped;
  * assigns clauses are dropped (E-ACSL does not check them).

Nothing is translated by hand per annotation: a new annotation in b1.c
goes through the same rules, and one they cannot handle is reported as
dropped (never silently kept in a non-executable form)."""
import hashlib
import json
import os
import re
import sys

src_path, out, twins = sys.argv[1], sys.argv[2], sys.argv[3]
NAME = sys.argv[sys.argv.index("--name") + 1] if "--name" in sys.argv \
    else "b1"
# --cov (coverage build, plan Q11 step 0): every kept clause gets the name
# rac_cov_<n>, and each side of a top-level implication or disjunction a
# probe clause rac_side_<n>_<j> (counted by ../../../rac/rac_collect.c,
# never failing); coverage_map.json says which is which.
COV = "--cov" in sys.argv
cov_map = []
HARNESS = "--no-harness" not in sys.argv
manifest = json.load(open(os.path.join(twins, "rac_twins.json")))
os.makedirs(out, exist_ok=True)
src = open(src_path).read()
report = []

# ---------------------------------------------------------------- blocks

P1_BEGIN = "/* BEGIN GENERATED (b1_gen.c), part 1: types */\n"
P1_END = "/* END GENERATED, part 1 */\n"
if P1_BEGIN in src:
    a = src.index(P1_BEGIN) + len(P1_BEGIN)
    b = src.index(P1_END)
    open(os.path.join(out, "b1_types.h"), "w").write(
        "/* b1.c's generated part 1, written by gen_rac.py */\n"
        "#ifndef B1_TYPES_H\n#define B1_TYPES_H\n#include <stddef.h>\n"
        + src[a:b] + "#endif\n")

# The spec block: the /*@ ... */ comment gen_twins.py generated
# rac_spec.h from (same SHA-256), so a changed spec needs regenerating.
for m in re.finditer(r"/\*@.*?\*/", src, re.S):
    if hashlib.sha256(m.group(0).encode()).hexdigest() == \
            manifest["spec_sha256"]:
        s0, s1 = m.start(), m.end()
        break
else:
    sys.exit(f"gen_rac.py: no annotation of {src_path} has the spec block's "
             f"sha256 {manifest['spec_sha256']}; rerun gen_twins.py on it")
spec = src[s0:s1]
rac_spec = open(os.path.join(twins, manifest["spec_header"])).read()
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
        elif depth == 0 and t.startswith(sep, i) \
                and not (sep == "==>" and t[i - 1:i] == "<"):  # not <==>
            parts.append(t[last:i])
            last = i + len(sep)
            i += len(sep)
            continue
        i += 1
    parts.append(t[last:])
    return [p.strip() for p in parts]


LOOSER = ("==>", "<==>", "||", "^^", "?")  # bind looser than && in ACSL


def conjuncts(t):
    """The conjuncts of t: split at top-level && only if no operator that
    binds looser than && occurs at top level; otherwise t is one conjunct
    (`a ==> b && c` is `a ==> (b && c)`, so dropping b must not leave c)."""
    depth, i = 0, 0
    while i < len(t):
        c = t[i]
        if c in "({":
            depth += 1
        elif c in ")}":
            depth -= 1
        elif depth == 0 and re.match(r"\\(forall|exists|let)\b", t[i:]):
            break  # a binder's body runs to the end of t
        elif depth == 0 and t.startswith(LOOSER, i):
            return [t.strip()]
        i += 1
    return split_top(t, "&&")


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


INT_TYPES = ("integer", "int", "long", "unsigned", "short", "char",
             "size_t")


def parse_binders(text):
    """'dllist *p, *h, \\list<dllist *> s, integer k' -> [(kind, name,
    type)], kind one of list, ptr, int."""
    out, ty = [], None
    for item in split_top(text, ","):
        m = re.match(r"(\\list<[^>]*>|(?:struct\s+)?\w+)\s+(?=[*\w])", item)
        if m and not re.fullmatch(r"\**\s*\w+", item):
            ty, item = m.group(1), item[m.end():]
        star = item.startswith("*")
        name = item.lstrip("*").strip()
        kind = ("list" if ty.startswith("\\list") else "ptr" if star else
                "int" if ty in INT_TYPES else "other")
        out.append((kind, name, ty + (" *" if star else "")))
    return out


PRED_APP = re.compile(r"(\w+)(\{(\w+)\})?\(")


def pred_args(conj):
    """If conj is P{L}(args) exactly, for a P with witness functions:
    (P, label, [args])."""
    m = PRED_APP.match(conj)
    if not m or m.group(1) not in manifest["preds"]:
        return None
    i = m.end() - 1
    if match_paren(conj, i) != len(conj):
        return None
    return m.group(1), m.group(3), split_top(conj[i + 1:-1], ",")


def stable(h, label):
    """h evaluates to the same value at label as here: a constant, or an
    \\at(..., label) term (so the witness can be computed at label)."""
    if h in ("\\null",):
        return True
    m = re.match(r"\\at\((.*), (\w+)\)$", h)
    return bool(m) and m.group(2) == label and match_paren(h, 3) == len(h)


def at(term, label):
    return term if label in (None, "Here") else f"\\at({term}, {label})"


def mentions(x, names):
    return any(re.search(rf"(?<![\\\w>.]){n}\b", x) for n in names)


def rule(P, e):
    """How a witness was found, for annotations.txt."""
    ps = manifest["preds"][P]["params"]
    if e["kind"] == "fwd":
        return f"{P}: {ps[e['out']]} from " + ", ".join(ps[i] for i in e["in"])
    return f"{P}: {ps[e['node']]} from a member of {ps[e['list']]}"


def witnesses(kind, binders, conjs):
    """Witness definitions [(name, term, rule)] for the list/pointer
    binders, from the conjuncts that determine them; None if some binder
    has none.  The binders' scope is conjs (a conjunction).  A witness
    is an application of a witness function of the manifest (README of
    ../../../rac, "Witnesses"):
      fwd     argument `out` of P from the arguments `in` (also gives t
              when that argument is \\Cons(e, t): rac_tail of it);
      member  the node argument of P(\\null, node, s), from a known x
              with x == \\nth(s, k) among the conjuncts.
    Under \\forall only exact witnesses are used (the cases are exclusive,
    no "any value"); under \\exists an "any value" witness only when the
    variable occurs in no other conjunct."""
    names = {n for _, n, _ in binders}
    kinds = {n: k for k, n, _ in binders}
    lets, why = {}, None
    progress = True
    while progress:
        progress = False
        unb = names - set(lets)
        for ci, conj in enumerate(conjs):
            d = pred_args(conj)
            if not d:
                continue
            P, label, args = d
            for e in manifest["preds"][P]["witnesses"]:
                if e["kind"] == "fwd":
                    ins = [args[i] for i in e["in"]]
                    out_a = args[e["out"]]
                    if any(mentions(x, unb) for x in ins):
                        continue
                    if label is not None and \
                            not all(stable(x, label) for x in ins):
                        why = (f"witness would be computed at {label} from "
                               "a value read here")
                        continue
                    if kind == "forall" and (e["free"] or not e["exclusive"]):
                        continue
                    term = at(f"{e['fn']}({', '.join(ins)})", label)
                    mm = re.fullmatch(r"\\Cons\((.+), (\w+)\)", out_a)
                    if out_a in unb and kinds[out_a] == e["out_kind"]:
                        if e["free"] and any(mentions(c, {out_a})
                                             for j, c in enumerate(conjs)
                                             if j != ci):
                            continue
                        lets[out_a] = (term, rule(P, e))
                    elif mm and mm.group(2) in unb and \
                            kinds[mm.group(2)] == "list" and \
                            e["out_kind"] == "list" and \
                            not mentions(mm.group(1), unb):
                        lets[mm.group(2)] = (at(f"rac_tail({e['fn']}("
                                                f"{', '.join(ins)}))", label),
                                             "tail of " + rule(P, e))
                    else:
                        continue
                elif kind == "exists":
                    n, s = args[e["node"]], args[e["list"]]
                    if args[e["root"]] != "\\null" or n not in unb:
                        continue
                    x = None
                    for c in conjs:
                        mm = re.fullmatch(
                            rf"(?:(.+) == \\nth\({re.escape(s)}, .+\)|"
                            rf"\\nth\({re.escape(s)}, .+\) == (.+))", c)
                        x = mm and (mm.group(1) or mm.group(2))
                        if x and not mentions(x, unb):
                            break
                        x = None
                    if not x:
                        continue
                    lets[n] = (at(f"{e['fn']}({x})", label), rule(P, e))
                else:
                    continue
                progress = True
                break
            if progress:
                break
    missing = [n for k, n, _ in binders if k != "int" and n not in lets]
    if missing:
        return None, why or "no witness for " + ", ".join(missing)
    # in the order found: a witness may use an earlier one
    return [(n,) + lets[n] for n in lets], None


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
    if kind == "forall" and len(binders) == 1 and binders[0][0] == "ptr":
        # \forall T *q; live(q) ==> P(q) (or heap(\base_addr(q)) &&
        # \offset(q) == 0 ==> ...): q is a heap block's base, so q ranges
        # over the allocation registry's slots (rac_reg_nth)
        _, q, ty = binders[0]
        prem = split_top(bod, "==>")
        cs = conjuncts(prem[0]) if len(prem) > 1 else []
        live_g = any(re.fullmatch(rf"live\({q}\)", c) for c in cs)
        heap_g = any(re.fullmatch(rf"heap\(\\base_addr\({q}\)\)", c)
                     for c in cs) and any(
            re.fullmatch(rf"\\offset\({q}\) == 0", c) for c in cs)
        if not (live_g or heap_g):
            raise Drop("\\forall over pointers (no finite range)")
        notes.append(f"{q} ranges over the allocation registry")
        node = f"(({ty})(0 + rac_reg_nth((long)(rac_i))))"
        new = re.sub(rf"(?<![\w>.]){q}\b", node, bod)
        return (t[:m.start()] + "\\forall integer rac_i; 0 <= rac_i < "
                f"rac_reg_count(0) ==> ({new})" + tail)
    if kind == "forall":
        if any(k == "ptr" for k, _, _ in binders):
            raise Drop("\\forall over pointers (no finite range)")
        prem = split_top(bod, "==>")
        if len(prem) < 2:
            raise Drop("\\forall over all lists")
        lets, why = witnesses(kind, binders, conjuncts(prem[0]))
        if lets is None:
            raise Drop("\\forall over lists: " + why)
        new = bod
    else:
        conjs = conjuncts(bod)
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
    # variable (in the order found, so a witness that uses an earlier one
    # gets it too).
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
    """A spec predicate applied at another label, P{L}(args), cannot be
    executed by E-ACSL 33: neither P{L}(...) nor \\at(P(...), L) is
    translated ("predicate(s) with labels", annotation ignored).  The
    conjunct is dropped with that reason.  (Its list witness is computed
    at L correctly, \\at(rac_dll_s_of_h(h), L), when h is label-stable; a
    future E-ACSL could take \\at(P(args), L).)"""
    m = re.search(r"\b(" + "|".join(PREDS) + r")\{(\w+)\}\(", p)
    if m and m.group(2) != "Here":
        raise Drop(f"{m.group(1)}{{{m.group(2)}}}: E-ACSL 33 does not "
                   "translate predicates under a label")
    return p


# Each builtin: result type for the wrapper (None: an int used as such)
# and its parameter kinds (n: a pointer, passed as is; l: cast to long),
# from the manifest.
TWIN_SIG = {}
for _name, _s in manifest["builtins"].items():
    TWIN_SIG[_name[len("rac_"):]] = (
        {"int": None, "list": "rac_list"}.get(_s["ret"], _s.get("ret_c")),
        "".join(_s["params"]))


PREDS = tuple(sorted(manifest["preds"], key=len, reverse=True))


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
        inner = t[m.end():j - 1]
        args = [wrap(a) for a in split_top(inner, ",")] if inner.strip() \
            else []
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
    for name, why in manifest["dropped"].items():
        if re.search(rf"\b{name}\b", p):
            raise Drop(f"uses {name}, not executable ({why})")
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
    conjs = conjuncts(rest) if kw != "loop variant" else [rest]
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
    probes = []
    if COV and kw != "loop variant":
        n = len(cov_map)
        sides = []
        for cj in kept:
            imp = split_top(cj, "==>")
            if len(imp) > 1:
                sides.append(("antecedent", imp[0]))
                continue
            dis = split_top(cj, "||")
            if len(dis) > 1:
                for k, d in enumerate(dis):
                    # the first disjunct that holds (the clause evaluates
                    # the later ones only when the earlier ones fail)
                    pre = " && ".join(f"!({x})" for x in dis[:k])
                    sides.append(("disjunct " + str(k + 1),
                                  f"{pre} && ({d})" if pre else d))
        cov_map.append({"n": n, "where": where, "label": label, "kind": kw,
                        "status": status, "sides": [
                            {"j": j, "role": r, "pred": x}
                            for j, (r, x) in enumerate(sides)]})
        names = f"rac_cov_{n}: " + names
        probes = [f"{kw} rac_side_{n}_{j}: {x};"
                  for j, (_, x) in enumerate(sides)]
    detail = []
    if notes:
        detail.append("witnesses " + ", ".join(notes))
    if dropped:
        detail.append(f"{len(dropped)} of {len(conjs)} conjuncts dropped: "
                      + "; ".join(dropped))
    report.append(f"{where}: {label}: {status}"
                  + (f" ({'; '.join(detail)})" if detail else ""))
    return [f"{kw} {names}" + " && ".join(kept) + ";"] + probes


ANNOT = re.compile(r"/\*@(.*?)\*/|//@([^\n]*)", re.S)


def tr_annot(m):
    lineno = line_base + body[:m.start()].count("\n") + 1
    text = m.group(1) if m.group(1) is not None else m.group(2)
    if text.strip() in ("ARIADNE_ALLOC", "ARIADNE_FREE"):
        return m.group(0)
    text = re.sub(r"//[^\n]*", "", text)  # comments inside annotations
    out = [y for x in (tr_clause(c, f"{NAME}.c:{lineno}")
                       for c in clauses(text)) if x for y in x]
    if not out:
        return (f"/* (annotation at {NAME}.c:{lineno} dropped, see "
                "annotations.txt) */")
    if re.match(r"(assert|check)\b", out[0]):   # one per comment
        return " ".join("/*@ " + x + " */" for x in out)
    return "/*@ " + "\n    ".join(out) + " */"


body = ANNOT.sub(tr_annot, body)
open(os.path.join(out, f"{NAME}_rac.c"), "w").write(
    "/* Generated by gen_rac.py from " + os.path.basename(src_path)
    + "; do not edit. */\n" + head
    + "/* rac_spec.h, twin calls written for E-ACSL (gen_rac.py, wrap) */\n"
    + re.sub(r"/\*@.*?\*/", lambda m: wrap(m.group(0)), rac_spec, flags=re.S)
    + body
    + ("\n/* RAC harness (E-ACSL build): allocators and driver. */\n"
       "#define RAC_IN_B1\n#include \"rac_alloc.c\"\n#include \"rac_main.c\"\n"
       if HARNESS else ""))
open(os.path.join(out, "annotations.txt"), "w").write("\n".join(report) + "\n")
if COV:
    json.dump(cov_map, open(os.path.join(out, "coverage_map.json"), "w"),
              indent=1)
counts = {}
for r in report:
    k = re.search(r": (kept|partly-kept|rewritten|dropped)\b", r).group(1)
    counts[k] = counts.get(k, 0) + 1
print("gen_rac: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items()))
      + " clauses")
