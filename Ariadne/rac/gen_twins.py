"""Generate executable twins of ACSL logic definitions (plan section 4
item 5) for runtime checking with E-ACSL (plan section 5 step 0).

   usage: python3 -I gen_twins.py SRC.c OUTDIR [--prefix rac]
              [--include HDR]... [--cpp-args ARGS] [--json DUMP.json]

SRC.c is an annotated C file; its ACSL logic definitions are read through
Frama-C (the logic_dump plugin in dump/, which writes Frama-C's typed AST
as JSON), so no ACSL text is parsed here.  Writes, in OUTDIR:

  <prefix>_twins.h    prototypes of the builtins (force-includable)
  <prefix>_twins.c    the twins: one C function per inductive predicate
                      and mode, list builtins, witness functions
  <prefix>_spec.h     the executable spec block: every definition E-ACSL
                      can run, in ACSL, with the twins in place of what it
                      cannot (inductives, binders over lists / pointers)
  <prefix>_twins.json manifest for gen_rac.py / check.sh: builtins and
                      their C signatures, witness modes, dropped names
  <prefix>_twins.txt  diagnostics: what was generated, kept, dropped, why

Translation rules and limits: README.md.  Every definition is either
translated by a rule or reported (by name, with the reason) as not
translated; nothing is guessed.  Exit status 1 if an inductive predicate
cannot be translated (the twins would be incomplete), else 0."""
import argparse
import copy
import hashlib
import itertools
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


class Untranslatable(Exception):
    pass


# ======================================================================
# Reading the spec (Frama-C's AST)
# ======================================================================

def run_dump(src, cpp_args, json_out):
    cmxs = os.path.join(HERE, "dump", "_build", "default", "logic_dump.cmxs")
    if not os.path.exists(cmxs):
        subprocess.run(["dune", "build"], cwd=os.path.join(HERE, "dump"),
                       check=True, env=dict(os.environ, DUNE_CACHE="disabled"))
    cmd = ["frama-c", "-no-unicode", "-load-module", cmxs]
    if cpp_args:
        cmd.append("-cpp-extra-args=" + cpp_args)
    cmd += [src, "-logic-dump", json_out]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("gen_twins.py: frama-c failed:\n" + r.stdout + r.stderr)


def strip(t):
    """Drop implicit casts (integer promotions, coercions to integer)."""
    while t.get("n") == "cast" and t.get("implicit"):
        t = t["a"]
    return t


def is_var(t, names=None):
    t = strip(t)
    ok = (t.get("n") == "lval" and t["host"]["h"] == "var" and not t["off"]
          and not t["host"]["c"])
    return ok and (names is None or t["host"]["name"] in names)


def var_name(t):
    return strip(t)["host"]["name"]


def children(x):
    for k, v in x.items():
        if k in ("ty", "type", "vars", "to", "entry"):
            continue
        if isinstance(v, dict):
            yield v
        elif isinstance(v, list):
            for e in v:
                if isinstance(e, dict):
                    yield e


def fv(x, bound=frozenset()):
    """Free logic variables of a term / predicate."""
    out = set()
    if x.get("n") == "lval" or x.get("n") in ("addrof", "startof"):
        h = x["host"]
        if h["h"] == "var" and not h["c"] and h["name"] not in bound:
            out.add(h["name"])
    if x.get("p") in ("forall", "exists"):
        bound = bound | {v["name"] for v in x["vars"]}
    for c in children(x):
        out |= fv(c, bound)
    return out


def subst(x, m):
    """Substitute terms for variables (no capture: binders shadow)."""
    if not m:
        return x
    if x.get("n") == "lval" and x["host"]["h"] == "var" and \
            x["host"]["name"] in m and not x["host"]["c"]:
        if x["off"]:
            raise Untranslatable("substitution into " + x["pp"])
        return m[x["host"]["name"]]
    if x.get("p") in ("forall", "exists"):
        m = {k: v for k, v in m.items()
             if k not in {v_["name"] for v_ in x["vars"]}}
    y = {}
    for k, v in x.items():
        if k in ("ty", "type", "vars", "to", "entry"):
            y[k] = v
        elif isinstance(v, dict):
            y[k] = subst(v, m)
        elif isinstance(v, list):
            y[k] = [subst(e, m) if isinstance(e, dict) else e for e in v]
        else:
            y[k] = v
    return y


def conjs(p):
    if p.get("p") == "and":
        return conjs(p["a"]) + conjs(p["b"])
    return [p]


def mk_and(ps):
    if not ps:
        return {"p": "true", "pp": "\\true"}
    r = ps[0]
    for q in ps[1:]:
        r = {"p": "and", "a": r, "b": q, "pp": r["pp"] + " && " + q["pp"]}
    return r


def implications(p):
    """p1 ==> p2 ==> ... ==> c  as  ([conjuncts of p1, p2, ...], c)."""
    prems = []
    while p.get("p") == "implies":
        prems += conjs(p["a"])
        p = p["b"]
    return prems, p


def mk_implies(prems, c):
    for q in reversed(prems):
        c = {"p": "implies", "a": q, "b": c, "pp": q["pp"] + " ==> " + c["pp"]}
    return c


def tkind(ty):
    return ty["k"]


def is_nullt(t):
    t = strip(t)
    return t.get("n") == "null" or (
        t.get("n") == "cast" and strip(t["a"]).get("n") == "null")


# ======================================================================
# C types
# ======================================================================

def ctype(ty):
    """C type of a logic value inside the twins."""
    k = ty["k"]
    if k == "ptr":
        return ty["c"]
    if k == "list":
        return "struct rac_seq *"
    if k == "integer":
        return "long"
    if k == "boolean":
        return "int"
    if k == "cint":
        return ty["c"]
    raise Untranslatable("type " + ty.get("pp", ty.get("c", k)))


def cdecl(ty_c, name):
    """A C declaration: `T *x`, not `T * x`."""
    ty_c = re.sub(r"\s*\*", " *", ty_c).replace("* *", "**")
    return ty_c + name if ty_c.endswith("*") else f"{ty_c} {name}"


def valid(p):
    """The twins' \\valid(p) for a read of *p: the registry."""
    return f"rac_valid({p}, sizeof *({p}))"


def ptype(ty):
    """C type at the builtin interface (no typedef names: force-included)."""
    k = ty["k"]
    if k == "ptr":
        return f"struct {ty['comp']} *" if ty.get("comp") else ty["c"]
    if k == "list":
        return "long"
    if k == "integer":
        return "long"
    return ctype(ty)


def sig_kind(ty):
    """Parameter kind for gen_rac.py's wrap: n (pointer, passed as is) or
    l (cast to long)."""
    return "n" if ty["k"] == "ptr" else "l"


def default(ty):
    return {"list": "((struct rac_seq *)0)", "ptr": "NULL"}.get(ty["k"], "0")


def bad(ty):
    return {"list": "RAC_BAD", "ptr": "NULL"}.get(ty["k"], "0")


def to_long(ty, e):
    return f"(long)(size_t)({e})" if ty["k"] in ("ptr", "list") else \
        f"(long)({e})"


def from_long(ty, e):
    if ty["k"] in ("ptr", "list"):
        return f"({ctype(ty)})(size_t)({e})"
    return f"({ctype(ty)})({e})"


C_REL = {"==": "==", "!=": "!=", "<": "<", "<=": "<=", ">": ">", ">=": ">="}
C_BIN = {"+", "-", "*", "/", "%", "<<", ">>", "&", "|", "^"}

# The ghost liveness model of ariadne_alloc.h: abstract in ACSL, the
# allocation registry here.  (name, arity) -> registry function.
PRIMITIVES = {("heap", 1): "rac_heap", ("dead", 2): "rac_dead"}


# ======================================================================
# The generator
# ======================================================================

class Gen:
    def __init__(self, decls, src_file, prefix):
        self.prefix = prefix
        self.src_file = src_file
        self.all = decls
        self.defs = {}           # name -> decl, definitions of the spec
        self.order = []
        def own(d):
            return os.path.basename(d.get("file", "")) == \
                os.path.basename(src_file)
        for d in decls:
            if d["kind"] in ("pred", "func", "inductive", "decl"):
                # an overload among the libc's own logic (strlen etc.,
                # when the source includes <string.h>) is not ours to
                # translate: the first is kept, the spec cannot use it
                if d["name"] in self.defs and not own(d) \
                        and not own(self.defs[d["name"]]):
                    continue
                if d["name"] in self.defs:
                    raise SystemExit(f"gen_twins.py: overloaded {d['name']}"
                                     " is not supported")
                self.defs[d["name"]] = d
            if os.path.basename(d.get("file", "")) == os.path.basename(src_file):
                self.order.append(d)
        self.diag = []           # (name, status, detail)
        self.funcs = {}          # C function name -> text (ordered)
        self.protos = {}         # C function name -> prototype
        self.modes = {}          # (P, I, o) -> info
        self.ctwins = {}         # pred / func name -> C name (or None)
        self.nq = 0
        self.elem_types = {}     # comp -> list element C type
        self.builtins = {}       # name -> signature (manifest)
        self.witness = {}        # pred -> [entries]
        self.dropped = {}        # name -> reason
        self.member_fns = {}

    # ---------------------------------------------------------- helpers
    def add_func(self, name, proto, body):
        self.protos[name] = proto + ";"
        self.funcs[name] = proto + " {\n" + body + "}\n"

    def snapshot(self):
        return (dict(self.funcs), dict(self.protos), dict(self.modes),
                dict(self.ctwins), self.nq)

    def restore(self, s):
        self.funcs, self.protos, self.modes, self.ctwins, self.nq = \
            (dict(s[0]), dict(s[1]), dict(s[2]), dict(s[3]), s[4])

    def note_elem(self, ty):
        if ty["k"] == "list" and ty["elem"]["k"] == "ptr":
            e = ty["elem"]
            self.elem_types[e.get("comp") or e["c"]] = e

    def inductive(self, name):
        d = self.defs.get(name)
        return d if d and d["kind"] == "inductive" else None

    # ============================================================ C terms
    def cterm(self, t, env, own):
        """C expression of term t, and the conditions under which its
        memory reads are allowed (rac_valid of each object read, in
        evaluation order; see guard()).  A condition for a read under
        one arm of ?: is that arm's only."""
        n = t.get("n")
        if n == "int":
            return t["v"] + ("L" if abs(int(t["v"])) > 2**31 else ""), []
        if n == "null":
            return "NULL", []
        if n == "lval" or n == "addrof":
            h = t["host"]
            derefs = []
            if h["h"] == "var":
                if h["c"]:
                    raise Untranslatable(f"C variable {h['name']} in a twin")
                if h["name"] not in env:
                    raise Untranslatable(f"unbound {h['name']}")
                e = env[h["name"]][0]
            elif h["h"] == "mem":
                e, derefs = self.cterm(h["t"], env, own)
                if not t["off"]:
                    derefs = derefs + [valid(e)]
                    e = f"(*{e})"
            else:
                raise Untranslatable("\\result in a twin")
            first = h["h"] == "mem"
            for o in t["off"]:
                if o["o"] == "field":
                    if first:
                        derefs = derefs + [valid(e)]
                        e = f"({e})->{o['f']}"
                    else:
                        e = f"({e}).{o['f']}"
                elif o["o"] == "index":
                    # whatever the host (a pointer, an array field of a
                    # valid object): the index may leave the object
                    i, di = self.cterm(o["t"], env, own)
                    if first:
                        derefs = derefs + [valid(e)]
                    e = f"({e})[{i}]"
                    derefs = derefs + di + [valid(f"&{e}")]
                else:
                    raise Untranslatable("model field " + o["f"])
                first = False
            if n == "addrof":
                # &p->f reads nothing
                return f"(&{e})", derefs[:-1]
            return e, derefs
        if n == "unop":
            a, d = self.cterm(t["a"], env, own)
            return f"({t['op']}{a})", d
        if n == "binop":
            if t["op"] not in C_BIN:
                raise Untranslatable("operator " + t["op"])
            a, da = self.cterm(t["a"], env, own)
            b, db = self.cterm(t["b"], env, own)
            if t["ty"]["k"] == "integer":  # mathematical: compute in long
                a, b = f"(long)({a})", f"(long)({b})"
            return f"({a} {t['op']} {b})", da + db
        if n == "cast":
            a, d = self.cterm(t["a"], env, own)
            if t.get("implicit"):
                return a, d
            return f"(({ctype(t['to'])})({a}))", d
        if n == "app":
            self.check_labels(t, own)
            f, args = t["f"], t["args"]
            cs = [self.cterm(a, env, own) for a in args]
            ds = [x for _, d in cs for x in d]
            es = [e for e, _ in cs]
            if f == "\\length":
                return f"rac_seq_len({es[0]})", ds
            if f == "\\nth":
                return f"(({ctype(t['ty'])})rac_seq_nth({es[0]}, {es[1]}))", ds
            if f == "\\concat":
                return f"rac_seq_concat({es[0]}, {es[1]})", ds
            c = self.need_twin(f)
            return f"{c}({', '.join(es + ['d + 1'])})", ds
        if n == "ctor":
            if t["c"] == "\\Nil":
                return "((struct rac_seq *)0)", []
            if t["c"] == "\\Cons":
                (h, dh), (tl, dt) = [self.cterm(a, env, own) for a in t["args"]]
                return f"rac_seq_cons((void *)({h}), {tl})", dh + dt
            raise Untranslatable("constructor " + t["c"])
        if n == "if":
            c = self.cpred(t["c"], env, own)
            a, da = self.cterm(t["a"], env, own)
            b, db = self.cterm(t["b"], env, own)
            if not da and not db:
                return f"({c} ? {a} : {b})", []
            # each arm's reads guarded in that arm only
            ga, gb = self.guard(da, None), self.guard(db, None)
            return f"({c} ? {a} : {b})", [f"({c} ? ({ga}) : ({gb}))"]
        if n == "witness":
            e = t["entry"]
            cs = [self.cterm(a, env, own) for a in t["args"]]
            return (f"{e['cval']}({', '.join([x for x, _ in cs] + ['d + 1'])})",
                    [x for _, d in cs for x in d])
        if n == "tail":
            a, d = self.cterm(t["a"], env, own)
            return f"rac_seq_tail({a})", d
        if n == "at" and t["label"] in own + ["Here"]:
            return self.cterm(t["a"], env, own)
        raise Untranslatable(f"term {t['pp']} ({n})")

    def check_labels(self, x, own):
        for lab in x.get("labels", []):
            if lab not in own + ["Here"]:
                raise Untranslatable(f"{x.get('pp')}: label {lab} (a twin "
                                     "reads the current state only)")

    def guard(self, derefs, e):
        seen = []
        for d in derefs:
            if d not in seen:
                seen.append(d)
        vs = seen
        if e is None:
            return " && ".join(vs) or "1"
        if not seen:
            return e
        return "(" + " && ".join(vs) + f" && {e})"

    # ============================================================ C preds
    def cpred(self, p, env, own):
        k = p["p"]
        if k == "true":
            return "1"
        if k == "false":
            return "0"
        if k == "rel":
            a, da = self.cterm(p["a"], env, own)
            b, db = self.cterm(p["b"], env, own)
            if strip(p["a"])["ty"]["k"] == "list":
                if p["op"] not in ("==", "!="):
                    raise Untranslatable("list relation " + p["op"])
                e = ("" if p["op"] == "==" else "!") + f"rac_seq_eq({a}, {b})"
            else:
                e = f"({a} {C_REL[p['op']]} {b})"
            return self.guard(da + db, e)
        if k in ("and", "or", "implies", "iff", "xor"):
            a = self.cpred(p["a"], env, own)
            b = self.cpred(p["b"], env, own)
            return {"and": f"({a} && {b})", "or": f"({a} || {b})",
                    "implies": f"(!{a} || {b})", "iff": f"(!{a} == !{b})",
                    "xor": f"(!{a} != !{b})"}[k]
        if k == "not":
            return f"(!{self.cpred(p['a'], env, own)})"
        if k == "app":
            self.check_labels(p, own)
            f, args = p["f"], p["args"]
            prim = PRIMITIVES.get((f, len(args)))
            if prim:
                last = strip(args[-1])
                if last.get("n") == "base_addr":
                    x, d = self.cterm(last["a"], env, own)
                    return self.guard(d, f"{prim}_of((void *)({x}))")
                x, d = self.cterm(last, env, own)
                return self.guard(d, f"{prim}((char *)({x}))")
            cs = [self.cterm(a, env, own) for a in args]
            ds = [x for _, d in cs for x in d]
            c = self.need_twin(f)
            return self.guard(ds, f"{c}({', '.join([e for e, _ in cs] + ['d + 1'])})")
        if k in ("valid", "valid_read"):
            if p["label"] not in own + ["Here"]:
                raise Untranslatable(f"{p['pp']}: label {p['label']}")
            x, d = self.cterm(p["t"], env, own)
            return self.guard(d, f"rac_valid({x}, sizeof *({x}))")
        if k in ("forall", "exists"):
            if any(v["type"]["k"] != "integer" and v["type"]["k"] != "cint"
                   for v in p["vars"]):
                return self.cpred(self.elim(p, own), env, own)
            return self.cquant(p, env, own)
        if k == "at" and p["label"] in own + ["Here"]:
            return self.cpred(p["a"], env, own)
        if k == "initialized":
            raise Untranslatable(f"{p['pp']}: \\initialized needs E-ACSL's "
                                 "shadow memory, which plain C cannot query")
        raise Untranslatable(f"{p['pp']} ({k})")

    def cquant(self, p, env, own):
        """A bounded integer quantifier: a loop in a helper function whose
        parameters are the free variables."""
        v, rest = p["vars"][0], p["vars"][1:]
        kind = p["p"]
        name = v["name"]
        others = {w["name"] for w in rest}
        if kind == "exists":
            cs = conjs(p["body"])
        else:
            cs, concl = implications(p["body"])
        lo = hi = None
        body = []
        for c in cs:
            cc = c
            if lo is None and cc["p"] == "rel" and cc["op"] in ("<=", "<") \
                    and is_var(cc["b"], {name}) \
                    and not fv(cc["a"]) & (others | {name}):
                lo = (cc["a"], cc["op"] == "<")
            elif hi is None and cc["p"] == "rel" and cc["op"] in ("<", "<=") \
                    and is_var(cc["a"], {name}) \
                    and not fv(cc["b"]) & (others | {name}):
                hi = (cc["b"], cc["op"] == "<=")
            else:
                body.append(c)
        if lo is None or hi is None:
            raise Untranslatable(f"{p['pp']}: unbounded integer quantifier")
        inner = mk_and(body) if kind == "exists" else mk_implies(body, concl)
        if rest:
            inner = {"p": kind, "vars": rest, "body": inner, "pp": inner["pp"]}
        free = sorted(fv(p) & set(env))
        self.nq += 1
        q = f"q{self.nq}_{name}"
        params = [(f"x_{x}", env[x][1]) for x in free]
        benv = {x: (f"x_{x}", env[x][1]) for x in free}
        lo_e, dlo = self.cterm(lo[0], benv, own)
        hi_e, dhi = self.cterm(hi[0], benv, own)
        benv[name] = (f"k_{name}", v["type"])
        b = self.cpred(inner, benv, own)
        bounds = self.guard(dlo + dhi, None)
        first = f"({lo_e}) + 1" if lo[1] else lo_e
        cmp = "<=" if hi[1] else "<"
        loop = (f"  for (long k_{name} = {first}; k_{name} {cmp} {hi_e}; "
                f"k_{name}++)\n")
        pre = "" if bounds == "1" else f"  if (!({bounds})) return 0;\n"
        if kind == "exists":
            body_c = f"{pre}{loop}    if ({b}) return 1;\n  return 0;\n"
        else:
            body_c = f"{pre}{loop}    if (!{b}) return 0;\n  return 1;\n"
        proto = (f"static int {q}(" + ", ".join(
            [cdecl(ctype(t), x) for x, t in params] + ["int d"]) + ")")
        self.add_func(q, proto, f"  /* {p['pp']} */\n  (void)d;\n" + body_c)
        return f"{q}({', '.join([env[x][0] for x in free] + ['d'])})"

    # ======================================================= twins of defs
    def need_twin(self, f):
        """C twin of a predicate or logic function f (generated once)."""
        if f in self.ctwins:
            if self.ctwins[f] is None:
                raise Untranslatable(f"{f} has no twin")
            return self.ctwins[f]
        d = self.defs.get(f)
        if d is None:
            raise Untranslatable(f"logic function {f}")
        if d["kind"] == "inductive":
            self.gen_mode(f, tuple(range(len(d["params"]))), None)
            return self.modes[(f, tuple(range(len(d["params"]))), None)]["name"]
        if d["kind"] not in ("pred", "func"):
            raise Untranslatable(f"{f} is declared without a definition")
        if len(d["labels"]) > 1:
            raise Untranslatable(f"{f} has {len(d['labels'])} labels")
        name = f"tw_{f}"
        self.ctwins[f] = name
        env = {v["name"]: (f"a_{v['name']}", v["type"]) for v in d["params"]}
        for v in d["params"]:
            self.note_elem(v["type"])
        ret = "int" if d["kind"] == "pred" else ctype(d["ret"])
        proto = (f"static {cdecl(ret, name)}(" + ", ".join(
            [cdecl(ctype(v["type"]), "a_" + v["name"]) for v in d["params"]]
            + ["int d"]) + ")")
        self.protos[name] = proto + ";"
        try:
            if d["kind"] == "pred":
                e = self.cpred(d["body"], env, d["labels"])
            else:
                e, ds = self.cterm(d["body"], env, d["labels"])
                if ds:
                    raise Untranslatable("a logic function that reads memory")
        except Untranslatable:
            self.ctwins[f] = None
            raise
        self.add_func(name, proto,
                      f"  if (!rac_tick(d)) return 0;\n  return {e};\n")
        return name

    # ====================================================== inductive modes
    def split_case(self, P, case):
        p = case["pred"]
        vs = []
        while p["p"] == "forall":
            vs += p["vars"]
            p = p["body"]
        prems, concl = implications(p)
        if concl["p"] != "app" or concl["f"] != P:
            raise Untranslatable(f"case {case['name']}: conclusion is not "
                                 f"{P}(...)")
        return vs, prems, [strip(a) for a in concl["args"]]

    def mode_name(self, P, I, o):
        ps = [v["name"] for v in self.defs[P]["params"]]
        if o is None:
            return f"m_{P}"
        return f"m_{P}_{ps[o]}_of_" + ("_".join(ps[i] for i in I) or "none")

    def gen_mode(self, P, I, o):
        """C function deciding P (o None: every argument given) or
        computing argument o of P from the arguments at positions I
        (a witness).  Raises Untranslatable if a case cannot be run in
        this mode."""
        key = (P, I, o)
        if key in self.modes:
            return self.modes[key]
        d = self.defs[P]
        params = d["params"]
        for v in params:
            self.note_elem(v["type"])
        info = {"name": self.mode_name(P, I, o), "free": False,
                "exclusive": True, "guards": [], "deps": set(), "key": key}
        self.modes[key] = info
        own = d["labels"]
        args = [cdecl(ctype(params[i]["type"]), f"a{i}") for i in I]
        if o is not None:
            args.append(cdecl(ctype(params[o]["type"]) + " *", "out"))
        proto = f"static int {info['name']}(" + ", ".join(args + ["int d"]) + ")"
        self.protos[info["name"]] = proto + ";"
        what = (f"decides {P}" if o is None else
                f"computes {params[o]['name']} with {P}(...) from "
                + (", ".join(params[i]["name"] for i in I) or "nothing"))
        body = f"  /* {what} */\n  if (!rac_tick(d)) return 0;\n"
        for ci, case in enumerate(d["cases"]):
            body += self.gen_case(P, I, o, case, ci, own, info)
        body += "  return 0;  /* no case applies */\n"
        self.add_func(info["name"], proto, body)
        if o is not None:
            g = info["guards"]
            for a, b in itertools.combinations(range(len(g)), 2):
                if g[a] is not None and g[b] is not None and \
                        not exclusive(g[a], g[b]):
                    info["exclusive"] = False
        return info

    def gen_case(self, P, I, o, case, ci, own, info):
        params = self.defs[P]["params"]
        vs, prems, cargs = self.split_case(P, case)
        vtypes = {v["name"]: v["type"] for v in vs}
        cname = case["name"]
        nxt = f"next{ci}"
        lines = []
        env = {}         # case variable -> (C expr, type)
        path = {}        # case variable -> input path (for guards)
        from_in = set()  # variables determined by the inputs alone
        guards = []

        def check(e):
            lines.append(f"    if (!({e})) goto {nxt};")

        def bind(v, e, src_inputs):
            env[v] = (f"v_{v}", vtypes[v])
            lines.append(f"    v_{v} = {e};")
            if src_inputs:
                from_in.add(v)

        def match(pat, e, ty, pth):
            pat = strip(pat)
            if is_var(pat) and var_name(pat) in vtypes:
                v = var_name(pat)
                if v not in env:
                    bind(v, e, True)
                    path[v] = pth
                else:
                    if ty["k"] == "list":
                        check(f"rac_seq_eq({env[v][0]}, {e})")
                    else:
                        check(f"{env[v][0]} == {e}")
                    guards.append(("eq",) + tuple(sorted((path.get(v, env[v][0]), pth))))
                return True
            if is_nullt(pat):
                check(f"{e} == NULL")
                guards.append(("null", pth))
                return True
            if pat.get("n") == "int":
                check(f"{e} == {pat['v']}")
                guards.append(("const", pth, pat["v"]))
                return True
            if pat.get("n") == "ctor" and pat["c"] == "\\Nil":
                check(f"rac_seq_is_nil({e})")
                guards.append(("nil", pth))
                return True
            if pat.get("n") == "ctor" and pat["c"] == "\\Cons":
                check(f"rac_seq_is_cons({e})")
                guards.append(("cons", pth))
                el = ty["elem"]
                match(pat["args"][0], f"(({ctype(el)})rac_seq_hd({e}))", el,
                      f"hd({pth})")
                match(pat["args"][1], f"rac_seq_tl({e})", ty, f"tl({pth})")
                return True
            # not a pattern: compared once its variables are known
            v = f"g{len(later)}"
            lines.append(f"    {cdecl(ctype(ty), v)} = {e};")
            later.append((pat, v, ty))
            return True

        def compare(pat, e, ty):
            x, ds = self.cterm(pat, env, own)
            check(self.guard(ds, f"rac_seq_eq({x}, {e})" if ty["k"] == "list"
                             else f"({x}) == {e}"))

        # 1. the given arguments against the conclusion's patterns
        later = []       # (term, C value, type): compared when known
        for i in I:
            match(cargs[i], f"a{i}", params[i]["type"], f"a{i}")
        for x in list(later):
            if not fv(x[0]) - set(env):
                compare(*x)
                from_in |= fv(x[0])
                later.remove(x)

        # 2. the premises, in order, as soon as their variables are known
        pending = list(prems)

        def simple(q):
            """A premise whose variables are known (a check, or left to
            the final check), or an equation v == t that determines v."""
            unb = fv(q) - set(env)
            if not unb:
                ind = q["p"] == "app" and self.inductive(q["f"])
                if o is not None and (ind or not fv(q) <= from_in):
                    return True  # left to the final check (not discriminating)
                try:
                    check(self.cpred(q, env, own))
                except Untranslatable:
                    if o is None:
                        raise
                    return True
                if o is not None:
                    g = guard_of(q, env, path)
                    if g:
                        guards.append(g)
                return True
            if q["p"] == "rel" and q["op"] == "==":
                for x, y in ((q["a"], q["b"]), (q["b"], q["a"])):
                    if is_var(x) and var_name(x) in unb and \
                            not fv(y) - set(env):
                        e, ds = self.cterm(y, env, own)
                        if ds:
                            check(self.guard(ds, None))
                        bind(var_name(x), e, fv(y) <= from_in)
                        return True
            return False

        def producer(q):
            """An inductive premise Q(...) whose unknown arguments are
            variables: a witness for each, from the known arguments (run
            only while the result still needs a variable)."""
            unb = fv(q) - set(env)
            if not (q["p"] == "app" and self.inductive(q["f"])):
                return False
            qa = [strip(a) for a in q["args"]]
            outs = [j for j, a in enumerate(qa) if fv(a) & unb]
            if not (all(is_var(qa[j]) for j in outs) and
                    len({var_name(qa[j]) for j in outs}) == len(outs)):
                return False
            if o is not None and not fv(cargs[o]) - set(env):
                return True  # the result is known: left to the final check
            self.check_labels(q, own)
            K = tuple(j for j in range(len(qa)) if j not in outs)
            cs = [self.cterm(qa[j], env, own) for j in K]
            ds = [x for _, dd in cs for x in dd]
            if ds:
                check(self.guard(ds, None))
            for j in outs:
                try:
                    m = self.gen_mode(q["f"], K, j)
                except Untranslatable as e:
                    qp = self.defs[q["f"]]["params"]
                    raise Untranslatable(
                        f"case {cname}: premise {q['pp']} needs "
                        f"{var_name(qa[j])}, and {q['f']} has no mode "
                        f"computing {qp[j]['name']} from "
                        + (", ".join(qp[i]["name"] for i in K) or "nothing")
                        + f" ({e})")
                info["deps"].add(m["key"])
                v = var_name(qa[j])
                env[v] = (f"v_{v}", vtypes[v])
                check(f"{m['name']}(" + ", ".join(
                    [e for e, _ in cs] + [f"&v_{v}", "d + 1"]) + ")")
            if o is None:
                check(self.cpred(q, env, own))
            return True

        while pending:
            q = next((q for q in pending if simple(q)), None) or \
                next((q for q in pending if producer(q)), None)
            if q is None:
                break
            pending.remove(q)
        for x in later:
            if fv(x[0]) - set(env):
                raise Untranslatable(
                    f"case {cname}: conclusion argument {x[0]['pp']} has "
                    "variables no premise determines")
            compare(*x)
        if pending and o is None:
            q = pending[0]
            raise Untranslatable(
                f"case {cname}: premise {q['pp']} has variables "
                f"{', '.join(sorted(fv(q) - set(env)))} that neither the "
                "conclusion nor an earlier premise determines")

        # 3. the result
        if o is None:
            lines.append("    return 1;")
        else:
            t = cargs[o]
            if not fv(t) - set(env):
                e, ds = self.cterm(t, env, own)
                if ds:
                    check(self.guard(ds, None))
                lines.append(f"    *out = {e};")
            elif is_var(t) and all(var_name(t) not in fv(q) for q in prems) \
                    and all(var_name(t) not in fv(cargs[i])
                            for i in range(len(cargs)) if i != o):
                lines.append(f"    *out = {default(params[o]['type'])};"
                             "  /* any value works */")
                info["free"] = True
            else:
                raise Untranslatable(
                    f"case {cname} does not determine {params[o]['name']} "
                    "from " + (", ".join(params[i]["name"] for i in I)
                               or "nothing"))
            lines.append("    return 1;")
            info["guards"].append(guards)
        decls = "".join(f"    {cdecl(ctype(t), 'v_' + v)};\n" for v, t in vtypes.items())
        unused = "".join(f"    (void)v_{v};\n" for v in vtypes)
        label = f"  {nxt}:;\n" if any(f"goto {nxt};" in x for x in lines) \
            else ""
        return (f"  {{ /* case {cname} */\n{decls}{unused}"
                + "\n".join(lines) + f"\n  }}\n{label}")

    def exact(self, key):
        """The mode computes the only possible value: its cases are
        exclusive, and every witness it uses is exact and not "any
        value" (a free output is exact only where it is returned)."""
        if not self.modes[key]["exclusive"]:
            return False
        seen, todo = set(), list(self.modes[key]["deps"])
        while todo:
            k = todo.pop()
            if k in seen:
                continue
            seen.add(k)
            m = self.modes[k]
            if not m["exclusive"] or m["free"]:
                return False
            todo += list(m["deps"])
        return True

    def try_mode(self, P, I, o):
        s = self.snapshot()
        try:
            return self.gen_mode(P, I, o)
        except Untranslatable:
            self.restore(s)
            return None

    # ------------------------------------------------- the member witness
    def gen_member(self, P):
        """For P(root, node, list) shaped like dll: the node h with
        P(\\null, h, s) for a known member x of s, by walking from x back
        along the field F that links each node to its parent (the premise
        node->F == parent of the case that recurses on the tail).  None
        if P has no such shape."""
        d = self.defs[P]
        params = d["params"]
        for ci, case in enumerate(d["cases"]):
            try:
                vs, prems, cargs = self.split_case(P, case)
            except Untranslatable:
                return None
            for S, a in enumerate(cargs):
                if not (a.get("n") == "ctor" and a["c"] == "\\Cons"):
                    continue
                hv, tv = [strip(x) for x in a["args"]]
                if not (is_var(hv) and is_var(tv)):
                    continue
                hn, tn = var_name(hv), var_name(tv)
                H = [i for i, c in enumerate(cargs) if is_var(c) and
                     var_name(c) == hn]
                if len(H) != 1:
                    continue
                H = H[0]
                nonnull = any(q["p"] == "rel" and q["op"] == "!=" and
                              {var_name(x) for x in (q["a"], q["b"])
                               if is_var(x)} == {hn} and
                              any(is_nullt(x) for x in (q["a"], q["b"]))
                              for q in prems)
                for q in prems:
                    if not (q["p"] == "app" and q["f"] == P):
                        continue
                    ra = [strip(x) for x in q["args"]]
                    if not (is_var(ra[S]) and var_name(ra[S]) == tn):
                        continue
                    for R, r in enumerate(ra):
                        if R in (S, H) or not is_var(r) or var_name(r) != hn \
                                or not is_var(cargs[R]):
                            continue
                        pv = var_name(cargs[R])
                        for e in prems:
                            fld = link_field(e, hn, pv)
                            if fld and nonnull and \
                                    self.nil_case(P, S, H, R):
                                return self.emit_member(P, R, H, S, fld)
        return None

    def nil_case(self, P, S, H, R):
        """Every other case concludes with \\Nil at S and \\null at H."""
        ok = False
        for case in self.defs[P]["cases"]:
            vs, prems, cargs = self.split_case(P, case)
            if cargs[S].get("n") == "ctor" and cargs[S]["c"] == "\\Nil":
                ok = True
                if not is_nullt(cargs[H]):
                    return False
        return ok

    def emit_member(self, P, R, H, S, fld):
        params = self.defs[P]["params"]
        ty = params[H]["type"]
        name = f"rac_{P}_{params[H]['name']}_of_member"
        proto = f"long {name}({cdecl(ptype(ty), 'x')})"
        body = (f"  /* the {params[H]['name']} with {P}(\\null, "
                f"{params[H]['name']}, {params[S]['name']}) and x in "
                f"{params[S]['name']}: walk from x along ->{fld} to the node "
                f"whose {fld} is \\null */\n"
                "  long n = 0;\n"
                f"  for ({cdecl(ctype(ty), 'c')} = x; rac_valid(c, sizeof *c); "
                f"c = c->{fld}) {{\n"
                f"    if (c->{fld} == NULL)\n      return (long)(size_t)c;\n"
                "    if (++n > RAC_FUEL_MEMBER)\n      break;\n  }\n"
                "  return 0;\n")
        self.add_func(name, proto, body)
        self.builtins[name] = {"ret": "ptr", "ret_c": ty["c"],
                               "params": [sig_kind(ty)]}
        return {"kind": "member", "root": R, "node": H, "list": S,
                "fn": name, "cval": f"tw_{name}", "out_ty": ty, "field": fld}

    # =============================================== binders over lists
    def entries(self, f):
        """Witness entries of predicate f: its own if inductive, else
        those of an inductive conjunct of its body applied to f's own
        parameters (as live_dll = dll(...) && ...)."""
        if f in self.witness:
            return self.witness[f]
        d = self.defs.get(f)
        res = []
        if d and d["kind"] == "pred" and len(d["labels"]) <= 1:
            names = [v["name"] for v in d["params"]]
            for c in conjs(d["body"]):
                if c["p"] == "app" and self.inductive(c["f"]) and \
                        all(is_var(a, set(names)) for a in c["args"]):
                    pos = [names.index(var_name(a)) for a in c["args"]]
                    if len(set(pos)) != len(pos):
                        continue
                    for e in self.entries(c["f"]):
                        e2 = dict(e)
                        if e["kind"] == "fwd":
                            e2["in"] = [pos[i] for i in e["in"]]
                            e2["out"] = pos[e["out"]]
                        else:
                            for k in ("root", "node", "list"):
                                e2[k] = pos[e[k]]
                        e2["via"] = c["f"]
                        res.append(e2)
                    break
        self.witness[f] = res
        return res

    def elim(self, p, own):
        """Replace the list / pointer binders of a \\forall or \\exists by
        witnesses (README, "Witnesses"); integer binders stay."""
        kind = p["p"]
        bs = {v["name"]: v["type"] for v in p["vars"]
              if v["type"]["k"] not in ("integer", "cint")}
        ints = [v for v in p["vars"] if v["name"] not in bs]
        if kind == "forall":
            if any(t["k"] == "ptr" for t in bs.values()):
                raise Untranslatable(f"{p['pp']}: \\forall over pointers "
                                     "(no finite range)")
            cs, concl = implications(p["body"])
            if not cs:
                raise Untranslatable(f"{p['pp']}: \\forall over all lists")
        else:
            cs = conjs(p["body"])
        lets = {}
        progress = True
        while progress and set(bs) - set(lets):
            progress = False
            unb = set(bs) - set(lets)
            cur = [subst(c, lets) for c in cs]
            for ci, c in enumerate(cur):
                if c["p"] != "app" or not self.entries(c["f"]):
                    continue
                if any(lab not in own + ["Here"] for lab in c["labels"]):
                    continue
                a = [strip(x) for x in c["args"]]
                for e in self.entries(c["f"]):
                    if e["kind"] == "fwd":
                        if any(fv(a[i]) & unb for i in e["in"]):
                            continue
                        out = a[e["out"]]
                        if kind == "forall" and (e["free"] or not e["exclusive"]):
                            continue
                        w = {"n": "witness", "entry": e,
                             "args": [a[i] for i in e["in"]],
                             "ty": e["out_ty"],
                             "pp": e["fn"] + "(" + ", ".join(
                                 a[i]["pp"] for i in e["in"]) + ")"}
                        if is_var(out, unb):
                            v = var_name(out)
                            if e["free"] and any(
                                    v in fv(x) for j, x in enumerate(cs)
                                    if j != ci):
                                continue
                            lets[v] = w
                        elif out.get("n") == "ctor" and out["c"] == "\\Cons" \
                                and is_var(out["args"][1], unb) \
                                and not fv(out["args"][0]) & unb:
                            v = var_name(out["args"][1])
                            lets[v] = {"n": "tail", "a": w, "ty": bs[v],
                                       "pp": f"rac_tail({w['pp']})"}
                        else:
                            continue
                        progress = True
                        break
                    elif kind == "exists":
                        if not (is_nullt(a[e["root"]]) and
                                is_var(a[e["node"]], unb)):
                            continue
                        x = self.member_of(cur, a[e["list"]], unb)
                        if x is None:
                            continue
                        lets[var_name(a[e["node"]])] = {
                            "n": "witness", "entry": e, "args": [x],
                            "ty": e["out_ty"],
                            "pp": f"{e['fn']}({x['pp']})"}
                        progress = True
                        break
                if progress:
                    break
        miss = set(bs) - set(lets)
        if miss:
            raise Untranslatable(f"{p['pp']}: no witness for "
                                 + ", ".join(sorted(miss)))
        # resolve lets that mention other binders
        for _ in range(len(lets)):
            lets = {k: subst(v, lets) for k, v in lets.items()}
        body = subst(p["body"], lets)
        if not ints:
            return body
        if kind == "exists":
            names = {v["name"] for v in ints}
            bc = conjs(body)
            first = [c for c in bc if not fv(c) & names]
            rest = [c for c in bc if fv(c) & names]
            q = {"p": "exists", "vars": ints, "body": mk_and(rest),
                 "pp": "\\exists ...; " + mk_and(rest)["pp"]}
            return mk_and(first + [q])
        return {"p": "forall", "vars": ints, "body": body, "pp": body["pp"]}

    def member_of(self, cs, s, unb):
        """x with a conjunct x == \\nth(s, k) (or \\nth(s, k) == x)."""
        for c in cs:
            if c["p"] != "rel" or c["op"] != "==":
                continue
            for x, y in ((c["a"], c["b"]), (c["b"], c["a"])):
                y = strip(y)
                if y.get("n") == "app" and y["f"] == "\\nth" and \
                        strip(y["args"][0]) == s and not fv(x) & unb:
                    return strip(x)
        return None

    # ============================================================ ACSL
    def aterm(self, t, own):
        n = t.get("n")
        if n == "int":
            return t["v"]
        if n == "null":
            return "\\null"
        if n in ("lval", "addrof"):
            h = t["host"]
            if h["h"] == "var":
                e = h["name"]
            elif h["h"] == "mem":
                e = self.aterm(h["t"], own)
                if not t["off"]:
                    e = f"*{paren(e)}"
            else:
                e = "\\result"
            first = h["h"] == "mem"
            for o in t["off"]:
                if o["o"] == "field":
                    e = f"{paren(e)}->{o['f']}" if first else f"{e}.{o['f']}"
                elif o["o"] == "index":
                    e = f"{e}[{self.aterm(o['t'], own)}]"
                else:
                    raise Untranslatable("model field")
                first = False
            return "&" + e if n == "addrof" else e
        if n == "unop":
            return f"{t['op']}{paren(self.aterm(t['a'], own))}"
        if n == "binop":
            return (f"{paren(self.aterm(t['a'], own))} {t['op']} "
                    f"{paren(self.aterm(t['b'], own))}")
        if n == "cast":
            a = self.aterm(t["a"], own)
            if t.get("implicit"):
                return a
            return f"({self.atype(t['to'])}){paren(a)}"
        if n == "app":
            f, args = t["f"], [self.aterm(a, own) for a in t["args"]]
            if f == "\\length":
                return f"rac_length({args[0]})"
            if f == "\\nth":
                return f"rac_nth({args[0]}, {args[1]})"
            if f == "\\concat":
                self.builtins["rac_concat"] = {"ret": "list",
                                               "params": ["l", "l"]}
                return f"rac_concat({args[0]}, {args[1]})"
            if f in self.dropped:
                raise Untranslatable(f"uses {f}")
            return f + self.alabels(t, own) + f"({', '.join(args)})"
        if n == "ctor":
            if t["c"] == "\\Nil":
                return "(rac_list)0"
            if t["c"] == "\\Cons":
                self.note_elem(t["ty"])
                a = [self.aterm(x, own) for x in t["args"]]
                return f"{self.cons_name(t['ty'])}({a[0]}, {a[1]})"
            raise Untranslatable("constructor " + t["c"])
        if n == "if":
            return (f"({self.apred(t['c'], own)} ? {self.aterm(t['a'], own)}"
                    f" : {self.aterm(t['b'], own)})")
        if n == "at":
            return f"\\at({self.aterm(t['a'], own)}, {t['label']})"
        if n == "offset":
            return f"\\offset({self.aterm(t['a'], own)})"
        if n == "witness":
            return t["entry"]["fn"] + "(" + ", ".join(
                self.aterm(a, own) for a in t["args"]) + ")"
        if n == "tail":
            return f"rac_tail({self.aterm(t['a'], own)})"
        if n == "base_addr":
            raise Untranslatable("\\base_addr outside heap / dead (E-ACSL 33 "
                                 "does not execute it)")
        raise Untranslatable(f"term {t['pp']}")

    def alabels(self, x, own):
        labs = x.get("labels", [])
        if not labs or labs == own or labs == ["Here"]:
            return ""
        return "{" + ", ".join(labs) + "}"

    def atype(self, ty):
        k = ty["k"]
        if k == "list":
            self.note_elem(ty)
            return "rac_list"
        if k in ("ptr", "cint", "c", "comp"):
            return ty["c"]
        if k in ("integer", "boolean", "real"):
            return k
        raise Untranslatable("type " + ty.get("pp", k))

    def apred(self, p, own):
        k = p["p"]
        if k == "true":
            return "\\true"
        if k == "false":
            return "\\false"
        if k == "rel":
            return (f"{self.aterm(p['a'], own)} {p['op']} "
                    f"{self.aterm(p['b'], own)}")
        if k in ("and", "or", "implies", "iff", "xor"):
            op = {"and": "&&", "or": "||", "implies": "==>", "iff": "<==>",
                  "xor": "^^"}[k]
            a, b = self.apred(p["a"], own), self.apred(p["b"], own)
            ca = "" if p["a"]["p"] in ("rel", "app", "and") and k == "and" \
                else "x"
            cb = "" if p["b"]["p"] in ("rel", "app", "and") and k == "and" \
                else "x"
            return (f"{a if not ca else pparen(a, p['a'])} {op} "
                    f"{b if not cb else pparen(b, p['b'])}")
        if k == "not":
            return "!" + pparen(self.apred(p["a"], own), p["a"])
        if k == "app":
            f, args = p["f"], p["args"]
            prim = PRIMITIVES.get((f, len(args)))
            if prim:
                last = strip(args[-1])
                if last.get("n") == "base_addr":
                    return f"{f}_of((void *){paren(self.aterm(last['a'], own))})"
                return f"{f}({', '.join(self.aterm(a, own) for a in args)})"
            if f in self.dropped:
                raise Untranslatable(f"uses {f} ({self.dropped[f]})")
            return f + self.alabels(p, own) + "(" + ", ".join(
                self.aterm(a, own) for a in args) + ")"
        if k in ("valid", "valid_read", "initialized", "freeable",
                 "dangling", "allocable", "object_pointer"):
            lab = "" if p["label"] in own + ["Here"] else "{" + p["label"] + "}"
            return f"\\{k}{lab}({self.aterm(p['t'], own)})"
        if k == "separated":
            return "\\separated(" + ", ".join(
                self.aterm(t, own) for t in p["ts"]) + ")"
        if k in ("forall", "exists"):
            if any(v["type"]["k"] not in ("integer", "cint") for v in p["vars"]):
                return pparen(self.apred(self.elim(p, own), own), {"p": "and"})
            vs = ", ".join(cdecl(self.atype(v["type"]), v["name"])
                           for v in p["vars"])
            return f"\\{k} {vs}; {self.apred(p['body'], own)}"
        if k == "at":
            return f"\\at({self.apred(p['a'], own)}, {p['label']})"
        raise Untranslatable(f"{p['pp']}")

    def cons_name(self, ty):
        e = ty["elem"]
        key = e.get("comp") or e["c"]
        return "rac_cons" if len(self.elem_types) <= 1 else f"rac_cons_{key}"

    # ============================================================ driver
    def run(self):
        ok = True
        # every list element type first: the name of the cons builtin
        # (rac_cons, or rac_cons_<T> for several) depends on all of them
        def types(x):
            if isinstance(x, dict):
                if x.get("k") == "list":
                    self.note_elem(x)
                for v in x.values():
                    types(v)
            elif isinstance(x, list):
                for v in x:
                    types(v)
        types(self.order)
        # 1. inductives: the decision twin, witness modes, member walk
        for d in self.order:
            if d["kind"] != "inductive":
                continue
            P = d["name"]
            params = d["params"]
            try:
                if len(d["labels"]) > 1:
                    raise Untranslatable(f"{len(d['labels'])} labels")
                info = self.gen_mode(P, tuple(range(len(params))), None)
            except Untranslatable as e:
                self.diag.append((P, "NOT TRANSLATED", str(e)))
                self.dropped[P] = str(e)
                ok = False
                continue
            name = f"rac_{P}"
            proto = f"int {name}(" + ", ".join(
                cdecl(ptype(v["type"]), v["name"]) for v in params) + ")"
            call = ", ".join(from_long(v["type"], v["name"])
                             if v["type"]["k"] == "list" else v["name"]
                             for v in params)
            self.add_func(name, proto, f"  rac_steps = 0;\n"
                          f"  return {info['name']}({call}, 0);\n")
            self.builtins[name] = {"ret": "int",
                                   "params": [sig_kind(v["type"])
                                              for v in params]}
            ents, inexact = [], []
            n = len(params)
            for o in range(n):
                found = []
                others = [i for i in range(n) if i != o]
                for size in range(0, n):
                    for I in itertools.combinations(others, size):
                        if any(set(f) <= set(I) for f in found):
                            continue
                        m = self.try_mode(P, I, o)
                        if not m:
                            continue
                        if not self.exact(m["key"]):
                            inexact.append(describe(P, params, {
                                "kind": "fwd", "in": I, "out": o,
                                "fn": "", "free": False, "exclusive": True}
                            ).split(":")[0])
                            continue
                        found.append(I)
                        ents.append(self.export_mode(P, I, o, m))
            self.witness[P] = ents
            mem = self.gen_member(P)
            if mem:
                ents.append(mem)
                self.add_value_fn_member(mem)
            self.diag.append((P, "twin", f"{info['name']} (decides {P}), "
                              f"builtin {name}; witnesses: "
                              + ("; ".join(describe(P, params, e) for e in ents)
                                 or "none")))
            if inexact:
                self.diag.append((P, "note", "not exported (not a function "
                                  "of the inputs: cases not provably "
                                  "exclusive, or a free value used): "
                                  + "; ".join(inexact)))
        # 2. every definition of the spec block, in order
        acsl = []
        for d in self.order:
            name, kind = d["name"], d["kind"]
            own = d["labels"]
            if kind in ("lemma", "axiom"):
                self.diag.append((name, "left out", f"{kind}: a proof fact"))
                continue
            if kind == "type":
                self.diag.append((name, "left out", "logic type"))
                continue
            if kind == "decl":
                self.dropped[name] = "declared without a definition"
                self.diag.append((name, "NOT TRANSLATED",
                                  "declared without a definition"))
                continue
            head = self.ahead(d)
            if kind == "inductive":
                if name in self.dropped:
                    continue
                acsl.append(f"// inductive {name}: its twin rac_{name}\n"
                            f"{head} =\n  rac_{name}("
                            + ", ".join(v["name"] for v in d["params"])
                            + ") != 0;")
                continue
            if len(own) > 1:
                why = (f"{len(own)} labels: E-ACSL 33 does not execute "
                       "predicates under labels")
                self.dropped[name] = why
                self.diag.append((name, "NOT TRANSLATED", why))
                continue
            try:
                body = (self.apred(d["body"], own) if kind == "pred"
                        else self.aterm(d["body"], own))
            except Untranslatable as e:
                self.dropped[name] = str(e)
                self.diag.append((name, "NOT TRANSLATED", str(e)))
                continue
            elim = "witness" in json.dumps(self.elimed(d), default=str)
            acsl.append((f"// {name}: binders over lists / pointers replaced"
                         " by witnesses\n" if elim else "") +
                        f"{head} =\n  {body};")
            self.diag.append((name, "ACSL", "kept, binders replaced by "
                              "witnesses" if elim else "kept"))
            if self.entries(name):
                self.diag.append((name, "witnesses", "via " + self.entries(
                    name)[0]["via"] + ": " + "; ".join(
                    describe(name, d["params"], e) for e in self.entries(name))))
        for name, c in self.ctwins.items():
            if c:
                self.diag.append((name, "C twin", f"{c} (called by twins)"))
        return ok, acsl

    def elimed(self, d):
        try:
            return self.elim_all(d["body"], d["labels"])
        except Untranslatable:
            return {}

    def elim_all(self, x, own):
        if isinstance(x, dict):
            if x.get("p") in ("forall", "exists") and any(
                    v["type"]["k"] not in ("integer", "cint") for v in x["vars"]):
                return self.elim(x, own)
            return {k: self.elim_all(v, own) for k, v in x.items()}
        if isinstance(x, list):
            return [self.elim_all(v, own) for v in x]
        return x

    def ahead(self, d):
        labs = "{" + ", ".join(d["labels"]) + "}" if d["labels"] else ""
        ps = ", ".join(cdecl(self.atype(v["type"]), v["name"])
                       for v in d["params"])
        if d["kind"] in ("pred", "inductive"):
            return f"predicate {d['name']}{labs}({ps})"
        return f"logic {self.atype(d['ret'])} {d['name']}{labs}({ps})"

    def export_mode(self, P, I, o, m):
        params = self.defs[P]["params"]
        out_ty = params[o]["type"]
        name = f"rac_{P}_{params[o]['name']}_of_" + \
            ("_".join(params[i]["name"] for i in I) or "none")
        cval = "wv" + m["name"][1:]
        vproto = (f"static {cdecl(ctype(out_ty), cval)}(" + ", ".join(
            [cdecl(ctype(params[i]["type"]), f"a{i}") for i in I] + ["int d"]) + ")")
        self.add_func(cval, vproto,
                      f"  {cdecl(ctype(out_ty), 'r')};\n  return {m['name']}(" + ", ".join(
                          [f"a{i}" for i in I] + ["&r", "d"]) +
                      f") ? r : {bad(out_ty)};\n")
        proto = f"long {name}(" + (", ".join(
            cdecl(ptype(params[i]["type"]), params[i]["name"]) for i in I)
            or "void") + ")"
        call = ", ".join([from_long(params[i]["type"], params[i]["name"])
                          if params[i]["type"]["k"] == "list"
                          else params[i]["name"] for i in I] + ["0"])
        self.add_func(name, proto, f"  rac_steps = 0;\n  return "
                      f"{to_long(out_ty, f'{cval}({call})')};\n")
        self.builtins[name] = {
            "ret": out_ty["k"] if out_ty["k"] in ("ptr", "list") else "int",
            "ret_c": out_ty.get("c"),
            "params": [sig_kind(params[i]["type"]) for i in I]}
        return {"kind": "fwd", "in": list(I), "out": o, "fn": name,
                "cval": cval, "out_ty": out_ty, "free": m["free"],
                "exclusive": m["exclusive"]}

    def add_value_fn_member(self, e):
        ty = e["out_ty"]
        self.add_func(e["cval"], f"static {cdecl(ctype(ty), e['cval'])}"
                      f"({cdecl(ctype(ty), 'x')}, int d)",
                      f"  (void)d;\n  return ({ctype(ty)})(size_t)"
                      f"{e['fn']}(x);\n")


def describe(P, params, e):
    ps = [v["name"] for v in params]
    if e["kind"] == "fwd":
        flags = [x for x, on in (("any value when free", e["free"]),
                                 ("cases not provably exclusive",
                                  not e["exclusive"])) if on]
        return (f"{ps[e['out']]} from "
                f"{', '.join(ps[i] for i in e['in']) or 'nothing'}: "
                f"{e['fn']}" + (f" [{', '.join(flags)}]" if flags else ""))
    return (f"{ps[e['node']]} from a member of {ps[e['list']]} when "
            f"{ps[e['root']]} == \\null: {e['fn']} (walk ->{e['field']})")


def link_field(q, hn, pv):
    """Field F if q is hn->F == pv (or pv == hn->F)."""
    if q["p"] != "rel" or q["op"] != "==":
        return None
    for x, y in ((q["a"], q["b"]), (q["b"], q["a"])):
        x = strip(x)
        if is_var(y) and var_name(y) == pv and x.get("n") == "lval" and \
                x["host"]["h"] == "mem" and is_var(x["host"]["t"]) and \
                var_name(x["host"]["t"]) == hn and len(x["off"]) == 1 and \
                x["off"][0]["o"] == "field":
            return x["off"][0]["f"]
    return None


def guard_of(q, env, path):
    """Symbolic form of a discriminating premise, for exclusive()."""
    if q["p"] != "rel" or q["op"] not in ("==", "!="):
        return None
    a, b = strip(q["a"]), strip(q["b"])

    def pth(x):
        if is_var(x) and var_name(x) in path:
            return path[var_name(x)]
        return None
    if is_nullt(b):
        a, b = b, a
    if is_nullt(a) and pth(b):
        return ("null" if q["op"] == "==" else "nonnull", pth(b))
    if pth(a) and pth(b):
        return ("eq" if q["op"] == "==" else "ne",) + tuple(sorted((pth(a), pth(b))))
    return None


def exclusive(g1, g2):
    """Two cases' input guards cannot both hold."""
    opp = {"null": "nonnull", "nonnull": "null", "nil": "cons",
           "cons": "nil", "eq": "ne", "ne": "eq"}
    for x in g1:
        for y in g2:
            if y[0] == opp.get(x[0]) and x[1:] == y[1:]:
                return True
            if x[0] == y[0] == "const" and x[1] == y[1] and x[2] != y[2]:
                return True
            # \null at a position vs a \Cons / nonnull etc. are covered;
            # a repeated variable (eq) vs != premise likewise
    return False


def paren(e):
    return e if re.fullmatch(r"[\w\\>.\-]*(\(.*\))?", e) and \
        not re.search(r"\s", e) else f"({e})"


def pparen(s, p):
    return s if p.get("p") in ("rel", "app", "true", "false", "valid",
                               "initialized", "valid_read") else f"({s})"


# ======================================================================
# Output
# ======================================================================

def spec_block(src_text, line):
    """The /*@ ... */ comment that contains `line` (1-based): its text."""
    lines = src_text.split("\n")
    off = sum(len(x) + 1 for x in lines[:line - 1])
    s0 = src_text.rfind("/*@", 0, off + len(lines[line - 1]))
    s1 = src_text.index("*/", s0) + 2
    if s1 < off:
        sys.exit("gen_twins.py: cannot locate the spec block")
    return src_text[s0:s1]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("src")
    ap.add_argument("out")
    ap.add_argument("--prefix", default="rac")
    ap.add_argument("--include", action="append", default=[],
                    help="header with the C types (for the twins)")
    ap.add_argument("--cpp-args", default="")
    ap.add_argument("--json", help="use this dump instead of running frama-c")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    pre = a.prefix
    dump = a.json or os.path.join(a.out, f"{pre}_logic.json")
    if not a.json:
        run_dump(a.src, a.cpp_args, dump)
    decls = json.load(open(dump))["decls"]
    g = Gen(decls, a.src, pre)
    ok, acsl = g.run()
    src_text = open(a.src).read()
    first = [d for d in g.order if "line" in d]
    block = spec_block(src_text, first[0]["line"]) if first else ""
    digest = hashlib.sha256(block.encode()).hexdigest()
    base = os.path.basename(a.src)
    if len(g.elem_types) > 1:
        g.diag.append(("(lists)", "note", "several element types: rac_cons_<T>"
                       " per type; rac_null is the first"))
    elems = list(g.elem_types.values())
    # ---- C
    cons = []
    for e in elems:
        cn = "rac_cons" if len(elems) <= 1 else f"rac_cons_{e.get('comp') or e['c']}"
        pt = f"struct {e['comp']} *" if e.get("comp") else e["c"]
        cons.append((cn, f"long {cn}({cdecl(pt, 'h')}, long t)",
                     "  return (long)(size_t)rac_seq_cons((void *)h, "
                     "(struct rac_seq *)(size_t)t);\n"))
        g.builtins[cn] = {"ret": "list", "params": ["n", "l"]}
    for n in ("rac_length", "rac_tail"):
        g.builtins[n] = {"ret": "int" if n == "rac_length" else "list",
                         "params": ["l"]}
    g.builtins["rac_nth"] = {"ret": "ptr", "ret_c": elems[0]["c"] if elems
                             else "void *", "params": ["l", "l"]}
    for n in ("rac_heap", "rac_dead", "rac_heap_of", "rac_dead_of"):
        g.builtins[n] = {"ret": "int", "params": ["n"]}
    publics = [n for n in g.funcs if n.startswith("rac_")]
    # only what the builtins use (modes tried but not exported are left out)
    live, todo = set(), list(publics)
    while todo:
        n = todo.pop()
        if n in live:
            continue
        live.add(n)
        todo += [m for m in re.findall(r"\b\w+\b", g.funcs[n])
                 if m in g.funcs and m not in live]
    g.funcs = {n: f for n, f in g.funcs.items() if n in live}
    g.protos = {n: f for n, f in g.protos.items() if n in live}
    h = [f"/* Generated by gen_twins.py from {base}; do not edit.",
         "   Prototypes of the executable twins (E-ACSL builtins); no typedefs,",
         "   so the header can be force-included (gcc -include). */",
         f"#ifndef {pre.upper()}_TWINS_H", f"#define {pre.upper()}_TWINS_H",
         '#include "rac_rt.h"', ""]
    h += [f"struct {e['comp']};" for e in elems if e.get("comp")]
    for _, p, _ in cons:
        h.append(p + ";")
    for n in publics:
        h.append(g.protos[n])
    h += ["", "#endif", ""]
    open(os.path.join(a.out, f"{pre}_twins.h"), "w").write("\n".join(h))
    c = [f"/* Generated by gen_twins.py from {base}; do not edit.",
         "   Executable twins of its ACSL logic definitions (README.md of",
         "   Ariadne/rac); diagnostics in " + f"{pre}_twins.txt. */",
         "#include <stddef.h>"]
    c += [f'#include "{x}"' for x in a.include]
    c += ["#define RAC_TWIN_IMPL", '#include "rac_rt.h"',
          f'#include "{pre}_twins.h"', "",
          "#ifndef RAC_FUEL_MEMBER", "#define RAC_FUEL_MEMBER 1000000L",
          "#endif", ""]
    c += [p for n, p in g.protos.items() if n.startswith(("m_", "tw_", "q",
                                                           "wv_"))]
    c.append("")
    for cn, p, b in cons:
        c.append(f"{p} {{\n{b}}}\n")
    c += list(g.funcs.values())
    open(os.path.join(a.out, f"{pre}_twins.c"), "w").write("\n".join(c))
    # ---- ACSL
    null_ty = elems[0]["c"] if elems else "void *"
    s = [f"/* Generated by gen_twins.py from {base}; do not edit.",
         "   The executable version of its spec block, for E-ACSL: each",
         "   definition E-ACSL can run is kept (\\list values as rac_list",
         "   handles, \\length / \\nth / \\Cons / \\Nil as builtins); each",
         "   inductive is its twin; binders over lists and pointers are",
         "   replaced by witnesses.  Diagnostics: " + f"{pre}_twins.txt.",
         "", f"   spec-sha256: {digest} */", "",
         "typedef long rac_list;", "",
         "/* NULL as a node, for \\null arguments of spec predicates",
         "   (gen_rac.py, null_args); not const: E-ACSL 33 aborts marking",
         "   it read-only. */",
         cdecl(null_ty, "rac_null") + " = 0;", "",
         "/*@ // The ghost liveness model as the allocation registry.",
         "    predicate heap(char *b) = rac_heap(b) != 0;",
         "    predicate dead(integer v, char *b) = rac_dead(b) != 0;",
         "    // heap(\\base_addr(p)), dead(v, \\base_addr(p)): E-ACSL 33 does",
         "    // not execute \\base_addr, the registry finds p's block.",
         "    predicate heap_of(void *p) = rac_heap_of(p) != 0;",
         "    predicate dead_of(void *p) = rac_dead_of(p) != 0;", ""]
    for x in acsl:
        s += ["    " + ln for ln in x.split("\n")] + [""]
    s += ["*/", ""]
    open(os.path.join(a.out, f"{pre}_spec.h"), "w").write("\n".join(s))
    # ---- manifest, diagnostics
    preds = {}
    for name in [d["name"] for d in g.order]:
        if name in g.dropped or g.defs.get(name, {}).get("kind") not in \
                ("pred", "inductive", "func"):
            continue
        ents = [{k: v for k, v in e.items() if k not in ("cval", "out_ty")}
                | {"out_kind": e["out_ty"]["k"]} for e in g.entries(name)]
        preds[name] = {"params": [v["name"] for v in g.defs[name]["params"]],
                       "witnesses": ents}
    man = {"source": base, "spec_sha256": digest, "spec_header": f"{pre}_spec.h",
           "builtins": g.builtins, "preds": preds, "dropped": g.dropped}
    json.dump(man, open(os.path.join(a.out, f"{pre}_twins.json"), "w"),
              indent=1)
    rep = [f"gen_twins.py {base}: spec-sha256 {digest}"]
    for name, st, det in g.diag:
        rep.append(f"{name}: {st}: {det}")
    open(os.path.join(a.out, f"{pre}_twins.txt"), "w").write("\n".join(rep) + "\n")
    nt = sum(1 for _, st, _ in g.diag if st == "NOT TRANSLATED")
    print(f"gen_twins: {sum(1 for d in g.order if d['kind'] == 'inductive')} "
          f"inductive(s), {len(publics)} builtins, {len(acsl)} ACSL "
          f"definitions, {nt} not translated (see {pre}_twins.txt)")
    for name, st, det in g.diag:
        if st == "NOT TRANSLATED":
            print(f"  {name}: {det}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
