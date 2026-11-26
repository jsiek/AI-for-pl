"""VST readiness: what in a C program VST cannot verify as it stands,
found from clightgen's output before any paid run (EVALUATION.md §5).

Each finding names the function it is in:
  goto            a `goto` (VST's `semax_goto` has precondition FF, so
                  a reachable one has no proof);
  switch          a `switch` without `default` (no case matches: VST's
                  switch rule gives that exit FF);
  variadic call   a call to a variadic function (no VST rule; replace
                  with fixed-argument functions);
  variadic def    a variadic function defined by the program;
  struct value    a struct passed or returned by value;
  extern global   a global with no definition in the unit (VST gives no
                  permission on it; define it, as picol_vst.c does);
  setjmp          setjmp/longjmp;
  address taken   a function whose address is taken (a callback: needs
                  a funspec for the pointer, `func_ptr'`);
  clightgen       clightgen rejected the file (its message).

    python3 vst_ready.py FILE.c [-- CLIGHTGEN_ARGS...]   # report as JSON

The C file is copied to a scratch directory and run through
`clightgen -normalize` in the VST image (vst/run.sh).
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ARIADNE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RUN = os.path.join(ARIADNE, "vst", "run.sh")
VARARG = "cc_vararg:=(Some"
# a call's result: None, or the temporary it is stored in
CALLED = r"(?:None|\(Some _[\w']+\))\s+"


def span(text, i):
    """End of the parenthesised term opening at text[i] == '('."""
    depth = 0
    for j in range(i, len(text)):
        if text[j] == "(":
            depth += 1
        elif text[j] == ")":
            depth -= 1
            if depth == 0:
                return j + 1
    return len(text)


def functions(ast):
    """{name: body text} for each internal function of the Clight file."""
    out = {}
    for m in re.finditer(r"^Definition f_(\w+) := \{\|(.*?)^\|\}\.", ast,
                         re.M | re.S):
        out[m.group(1)] = m.group(2)
    return out


def switches_without_default(body):
    n = 0
    for m in re.finditer(r"\(Sswitch ", body):
        term = body[m.start():span(body, m.start())]
        # drop nested switches, which are counted on their own
        inner = [k.start() for k in re.finditer(r"\(Sswitch ", term)][1:]
        for k in reversed(inner):
            term = term[:k] + term[span(term, k):]
        if "(LScons None" not in term:
            n += 1
    return n


def analyse(ast):
    """Findings in a Clight file: a list of {kind, function, detail}."""
    found = []
    fns = functions(ast)
    for f, body in fns.items():
        for _ in re.findall(r"\(Sgoto ", body):
            found.append({"kind": "goto", "function": f})
        for _ in range(switches_without_default(body)):
            found.append({"kind": "switch", "function": f,
                          "detail": "no default"})
        for m in re.finditer(r"\(Scall " + CALLED + r"\(Evar _(\w+)\s+(\(Tfunction)",
                             body):
            if VARARG in body[m.start(2):span(body, m.start(2))]:
                found.append({"kind": "variadic call", "function": f,
                              "detail": m.group(1)})
        if re.search(r"fn_callconv := \{\|" + re.escape(VARARG), body):
            found.append({"kind": "variadic def", "function": f})
        sig = body.split("fn_vars")[0]
        if re.search(r"(?<!tptr )\(Tstruct ", sig):
            found.append({"kind": "struct value", "function": f,
                          "detail": "parameter or return"})
        for callee in re.findall(r"\(Scall " + CALLED + r"\(Evar _(\w+)", body):
            if callee in ("setjmp", "_setjmp", "longjmp", "_longjmp"):
                found.append({"kind": "setjmp", "function": f})
        called = len(re.findall(r"\(Scall " + CALLED + r"\(Evar _\w+\s+\(Tfunction", body))
        refs = re.findall(r"\(Evar _(\w+)\s+\(Tfunction", body)
        if len(refs) > called:
            callees = re.findall(r"\(Scall " + CALLED + r"\(Evar _(\w+)\s+\(Tfunction",
                                 body)
            taken = list(refs)
            for c in callees:
                taken.remove(c)
            for g in sorted(set(taken)):
                found.append({"kind": "address taken", "function": f,
                              "detail": g})
    for sym in re.findall(r"^Definition v_(\w+) := \{\|\s*gvar_info := "
                          r"[^;]*;\s*gvar_init := nil;", ast, re.M):
        found.append({"kind": "extern global", "function": None,
                      "detail": sym})
    return found


def external_functions(ast):
    """Library functions the program calls (not builtins)."""
    return sorted(set(re.findall(r"Gfun\(External \(EF_external \"(\w+)\"",
                                 ast)))


def clight(c_file, args=()):
    """(Clight text or None, clightgen's message) for a C file."""
    d = tempfile.mkdtemp(prefix="vst_ready_", dir=os.path.join(
        ARIADNE, "runs"))
    try:
        name = os.path.basename(c_file)
        shutil.copy(c_file, d)
        r = subprocess.run([RUN, "clightgen", "-normalize", *args, name],
                           cwd=d, capture_output=True, text=True)
        v = os.path.join(d, name[:-2] + ".v")
        ast = open(v).read() if r.returncode == 0 and os.path.exists(v) \
            else None
        return ast, (r.stdout + r.stderr).strip()
    finally:
        shutil.rmtree(d, ignore_errors=True)


def report(c_file, args=()):
    ast, msg = clight(c_file, args)
    if ast is None:
        return {"file": c_file, "clightgen": msg,
                "findings": [{"kind": "clightgen", "function": None,
                              "detail": msg[-1500:]}]}
    return {"file": c_file, "clightgen": msg, "findings": analyse(ast),
            "externals": external_functions(ast)}


if __name__ == "__main__":
    argv = sys.argv[1:]
    extra = argv[argv.index("--") + 1:] if "--" in argv else []
    print(json.dumps(report(os.path.abspath(argv[0]), extra), indent=1))
