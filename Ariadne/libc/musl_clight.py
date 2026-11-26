"""Which musl C files does a set of libc functions pull in, and does
clightgen accept each one?

usage: python3 -I musl_clight.py strlen strcmp ...   (after fetch_musl.py)

1. Generates musl's headers (as its Makefile does) and a shim
   features.h: CompCert has no `__typeof`, so musl's `weak_alias` is
   defined as nothing.
2. Indexes the defined and undefined symbols of every generic C file
   (src/*/*.c; the arch-specific asm versions are not used) with host
   gcc and CompCert's preprocessor defines (-U__GNUC__
   -U__SIZEOF_INT128__, from compcert.ini), which also turns off musl's
   word-at-a-time string loops.
3. Computes the closure of the given functions, stopping at the
   allocator, threads, signals and syscalls (reported as the boundary).
4. Runs clightgen -normalize on each file in the VST image and prints
   OK, or FAIL with the first line of the error.
"""
import glob, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
M = os.path.join(HERE, "musl-1.2.6")
RUN = os.path.join(HERE, "..", "vst", "run.sh")
BOUNDARY_DIRS = ("src/malloc/", "src/thread/", "src/signal/", "src/unistd/",
                 "src/process/", "src/exit/", "src/env/", "src/ldso/")
INC = ["-I" + p for p in ("arch/x86_64", "arch/generic", "obj/src/internal",
                          "src/include", "src/internal", "obj/include", "include")]
FLAGS = ["-std=c99", "-ffreestanding", "-nostdinc", "-D_XOPEN_SOURCE=700",
         "-U__GNUC__", "-U__SIZEOF_INT128__"] + INC


def headers():
    for d in ("obj/include/bits", "obj/src/internal", "obj/shim", "obj/log"):
        os.makedirs(os.path.join(M, d), exist_ok=True)
    with open(M + "/obj/include/bits/alltypes.h", "w") as f:
        subprocess.run(["sed", "-f", "tools/mkalltypes.sed",
                        "arch/x86_64/bits/alltypes.h.in",
                        "include/alltypes.h.in"], cwd=M, stdout=f, check=True)
    src = open(M + "/arch/x86_64/bits/syscall.h.in").read()
    open(M + "/obj/include/bits/syscall.h", "w").write(
        src + "".join(l.replace("__NR_", "SYS_") + "\n"
                      for l in src.splitlines() if "__NR_" in l))
    open(M + "/obj/src/internal/version.h", "w").write(
        '#define VERSION "1.2.6"\n')
    open(M + "/obj/shim/features.h", "w").write(
        '#ifndef FEATURES_H\n#define FEATURES_H\n'
        '#include "../../include/features.h"\n'
        '#define weak\n#define hidden\n#define weak_alias(old, new)\n#endif\n')


def index():
    path = M + "/obj/index.json"
    if os.path.exists(path):
        return json.load(open(path))
    idx = {}
    for c in sorted(glob.glob(M + "/src/*/*.c")):
        rel = os.path.relpath(c, M)
        o = M + "/obj/idx.o"
        r = subprocess.run(["gcc", "-c", "-O0", "-w"] + FLAGS + ["-o", o, rel],
                           cwd=M, capture_output=True, text=True)
        if r.returncode:
            idx[rel] = {"error": r.stderr[-300:]}
            continue
        d, u = [], []
        for l in subprocess.run(["nm", o], capture_output=True,
                                text=True).stdout.splitlines():
            p = l.split()
            if len(p) == 3 and (p[1] in "TDBRCWV"):
                d.append(p[2])
            elif len(p) == 2 and p[0] == "U":
                u.append(p[1])
        idx[rel] = {"def": d, "undef": u}
    json.dump(idx, open(path, "w"))
    return idx


def closure(idx, roots):
    where = {}
    for rel, e in idx.items():
        for s in e.get("def", []):
            where.setdefault(s, []).append(rel)
    files, boundary, missing, seen, todo = [], {}, [], set(), list(roots)
    while todo:
        s = todo.pop()
        if s in seen:
            continue
        seen.add(s)
        if s not in where:
            missing.append(s)
            continue
        f = sorted(where[s], key=len)[0]
        if f.startswith(BOUNDARY_DIRS) or "syscall" in f:
            boundary.setdefault(f, []).append(s)
        elif f not in files:
            files.append(f)
            todo.extend(idx[f]["undef"])
    return sorted(files), boundary, sorted(missing)


def clight(files):
    cf = " ".join(["-Wp,-nostdinc", "-D_XOPEN_SOURCE=700", "-Iobj/shim"] + INC)
    lines = ["cd /work"] + [
        'if clightgen -normalize %s %s > obj/log/%s.log 2>&1; then echo "OK %s";'
        ' else echo "FAIL %s"; fi' % (cf, f, f.replace("/", "_"), f, f)
        for f in files]
    open(M + "/obj/clight.sh", "w").write("\n".join(lines) + "\n")
    out = subprocess.run([RUN, "bash", "obj/clight.sh"], cwd=M,
                         capture_output=True, text=True).stdout
    for l in out.splitlines():
        st, f = l.split()
        if st == "OK":
            print("OK  ", f)
        else:
            log = open(M + "/obj/log/" + f.replace("/", "_") + ".log").read()
            err = [x for x in log.splitlines()
                   if "error" in x or "syntax error" in x] or log.splitlines()
            print("FAIL", f, "|", err[0][:200])


headers()
files, boundary, missing = closure(index(), sys.argv[1:])
print("%d files; boundary %s; not found %s" % (len(files), boundary, missing))
clight(files)
