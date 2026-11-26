"""vst_ready.py on upstream picol (bench/picol/upstream/picol.c, with
musl's headers) must report what the four picol runs and the owner's
fixes 3-5 and 7 dealt with: the 7 `goto`s (4 in picolEval, 3 in
picolCommandCallProc), the 2 `switch`es without `default`
(picolParseString, picolExpr), the variadic snprintf/printf/fprintf
calls, the extern stdin/stdout/stderr, and the command functions whose
addresses picolRegisterCoreCommands takes; and on the fixed picol_vst.c
none of the first three.

    python3 test_vst_ready.py
"""
import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import targets  # noqa: E402
import vst_ready  # noqa: E402

fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + " " + name)
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:1500])


def findings(source):
    inc = targets.load("picol")["files"]["picol_full.c"]["includes"]
    text = targets.preprocess([source], ".", inc, "")
    path = os.path.join(targets.ARIADNE, "runs", "test_vst_ready.c")
    open(path, "w").write(text)
    try:
        return vst_ready.report(path)["findings"]
    finally:
        os.remove(path)


up = findings("bench/picol/upstream/picol.c")
by = collections.Counter((f["kind"], f["function"]) for f in up)
expect("upstream: 4 gotos in picolEval, 3 in picolCommandCallProc",
       by[("goto", "picolEval")] == 4
       and by[("goto", "picolCommandCallProc")] == 3, by)
sw = sorted(f["function"] for f in up if f["kind"] == "switch")
expect("upstream: switch without default in picolParseString, picolExpr",
       sw == ["picolExpr", "picolParseString"], sw)
va = collections.Counter(f["detail"] for f in up
                         if f["kind"] == "variadic call")
expect("upstream: variadic calls to snprintf, printf, fprintf",
       va["snprintf"] >= 6 and va["printf"] >= 4 and va["fprintf"] >= 1, va)
ext = {f["detail"] for f in up if f["kind"] == "extern global"}
expect("upstream: extern stdin, stdout, stderr",
       {"stdin", "stdout", "stderr"} <= ext, ext)
taken = {f["detail"] for f in up if f["kind"] == "address taken"}
expect("upstream: command functions' addresses taken",
       {"picolCommandSet", "picolCommandPuts", "picolCommandProc"} <= taken,
       taken)
fixed = findings("bench/picol/picol_vst.c")
kinds = collections.Counter(f["kind"] for f in fixed)
expect("fixed picol_vst.c: no goto, switch without default, or variadic "
       "call", not (kinds["goto"] or kinds["switch"]
                    or kinds["variadic call"]), kinds)
print("%s: %d failed" % ("FAIL" if fails else "PASS", len(fails)))
sys.exit(1 if fails else 0)
