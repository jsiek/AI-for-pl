"""Summarise a run log in one line (used by check.sh).

   classify.py san <log>       ASan/UBSan run: the error kind, `oracle`, or `-`
   classify.py eacsl <log>     E-ACSL run: `<Kind> <name> in <function>` of
                               the first failed check, `oracle`, or `-`
   classify.py warnings <log>  E-ACSL build: one line per annotation it
                               could not translate"""
import re
import sys

mode, path = sys.argv[1], sys.argv[2]
log = open(path, errors="replace").read()

if mode == "san":
    m = re.search(r"ERROR: AddressSanitizer: ([\w-]+)", log)
    if m:
        print(m.group(1))
    elif re.search(r"runtime error:", log):
        print("ubsan: " + re.search(r"runtime error: ([^\n]*)", log).group(1))
    elif "ORACLE FAIL" in log:
        print("oracle")
    elif re.search(r"^ok:", log, re.M):
        print("-")
    else:
        print("crash")
elif mode == "eacsl":
    m = re.search(r"In function '(\w+)'\n[^\n]*: Error: (\w+) failed:\n"
                  r"\s*The failing predicate is:\n\s*([^\n]*)", log)
    if m:
        fct, kind, first = m.groups()
        name = first[:-1] if first.endswith(":") else ""
        print(f"{kind} {name + ' ' if name else ''}in {fct}")
    elif "ORACLE FAIL" in log:
        print("oracle")
    elif re.search(r"^ok:", log, re.M):
        print("-")
    else:
        print("crash: " + (log.strip().splitlines() or ["no output"])[-1])
elif mode == "warnings":
    seen = []
    for m in re.finditer(r"\[e-acsl\] ([^\n]*?): Warning: *\n((?:  [^\n]*\n)+)",
                         log):
        msg = " ".join(x.strip() for x in m.group(2).splitlines())
        line = f"{m.group(1)}: {msg}"
        if line not in seen:
            seen.append(line)
    print("\n".join(seen))
