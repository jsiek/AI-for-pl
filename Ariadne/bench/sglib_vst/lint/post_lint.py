"""Leak-freedom lint for VST funspec files (owner, R10, 2026-11-17).

VST 2.17 lets a proof drop owned memory only through an absorbing
predicate in a postcondition (`affine_probe/`).  So this lint forbids,
in every postcondition of the given files:

* `TT`, and
* an existential over `mpred` (`EX R: mpred, ..`, `exp (fun R: mpred => ..)`),

including inside the predicates the postcondition uses: every name the
postcondition mentions that is defined in the same files (`Definition`,
`Fixpoint`) is unfolded, recursively.  A name whose body is itself a
funspec (it has a `POST [`) is not unfolded: its own postcondition is
checked in its own right.  Section variables (`Context (Rc: ..)`) are
checked where a client instantiates them, by running this lint on the
client's file.

`main` (a `DECLARE _main` funspec) must also mention the allocator's
state, `mem_mgr`, in its postcondition: main ends owning the allocator
state plus its globals, and no other heap memory.

A private helper whose postcondition contains TT cannot hide a leak:
its caller would then hold TT, and TT entails no TT-free assertion
(`TT |-- emp` is false in VST), so the caller could not end in a
TT-free public postcondition.  The lint therefore checks only the
postconditions it is given.

    python3 -I post_lint.py FILE.v [FILE.v ...]

Prints one line per violation and exits 1 if there is any.
"""
import re
import sys

FORBIDDEN = [
    (re.compile(r"\bTT\b"), "TT"),
    (re.compile(r"\bEX\s+[\w' ]+:\s*[^,]*\bmpred\b"),
     "existential over mpred"),
    (re.compile(r"\bexp\s*\(\s*fun\s+[\w' ]+:\s*[^=]*\bmpred\b"),
     "existential over mpred"),
]
IDENT = re.compile(r"[A-Za-z_][\w']*")
DEF = re.compile(r"^\s*(?:#\[[^\]]*\]\s*)?(?:Program\s+)?"
                 r"(Definition|Fixpoint)\s+([A-Za-z_][\w']*)")


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


def sentences(text):
    """Coq sentences: split at a period followed by whitespace or the
    end (so `Val.eq` and `1.5` do not split)."""
    return [s for s in re.split(r"\.(?=\s|$)", text) if s.strip()]


def definitions(texts):
    defs = {}
    for text in texts:
        for s in sentences(strip_comments(text)):
            m = DEF.match(s)
            if m:
                defs[m.group(2)] = s
    return defs


def post_of(body):
    i = body.find("POST [")
    return None if i < 0 else body[i:]


def violations_in(text, defs, path, seen):
    found = []
    for rx, what in FORBIDDEN:
        if rx.search(text):
            found.append((path, what))
    for name in sorted(set(IDENT.findall(text))):
        if name in defs and name not in seen and post_of(defs[name]) is None:
            seen.add(name)
            found += violations_in(defs[name], defs, path + [name], seen)
    return found


def lint(texts):
    defs = definitions(texts)
    report = []
    for name, body in sorted(defs.items()):
        post = post_of(body)
        if post is None:
            continue
        for path, what in violations_in(post, defs, [name], {name}):
            report.append("%s: %s in the postcondition (via %s)"
                          % (name, what, " -> ".join(path)))
        if re.search(r"DECLARE\s+_main\b", body) and "mem_mgr" not in post:
            report.append("%s: main's postcondition does not hold the "
                          "allocator state (mem_mgr)" % name)
    return report


def main(argv):
    texts = [open(p).read() for p in argv[1:]]
    report = lint(texts)
    for line in report:
        print("FAIL:", line)
    if not report:
        print("OK: no TT and no existential over mpred in %d file(s)'s "
              "postconditions" % len(texts))
    return 1 if report else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
