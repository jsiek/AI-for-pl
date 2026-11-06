"""Expand the C macros used inside ACSL annotations (plan Q11, Q12).

   usage: python3 -I acsl_expand.py SRC.c OUT.c [--cpp-args ARGS]
                                     [--keep NAME,...]

Frama-C preprocesses annotations (`-pp-annot`, the default with gcc's
cpp): a macro used inside `/*@ ... */` is expanded before the ACSL is
parsed.  The spec templates (`bench/sglib_spec/`) rely on this: B1's
predicates and contracts are written as macros, and b1.c holds only
their invocations, such as `/*@ SGLIB_DL_LIST_SPEC(dllist, ...) */`.
The textual tools (the guardrails' spec hashes and lints, the RAC
pipeline's clause rewriting) must see the ACSL that Frama-C sees, so
they work on the expanded text this module produces.

How: one cpp run (`cpp -P -std=c11`, the language mode of Frama-C's own
annotation preprocessing) over the source's `#include "..."`, `#define`
and `#undef` lines and the annotation bodies, in source order, each body
between two marker lines.  An annotation whose expansion differs from
its own text (comments dropped, whitespace collapsed) is replaced by
the expansion, on one line followed by as many newlines as the original
body had, so every later line keeps its number; any other annotation,
and all C code, is left byte for byte.  System headers (`#include <...>`)
and conditionals (`#if...`) are not read, so a macro from a system
header is not expanded inside annotations (none of the benchmarks uses
one there).  `keep` names annotations left as they are when their whole
text is one of the names (the RAC pipeline keeps `ARIADNE_ALLOC` and
`ARIADNE_FREE`, which its rac.h redefines for runtime checking).

cpp is the image's (gcc 12): this module calls it directly inside the
M0 image and through ../env/run.sh outside it, so the expansion, and the
hashes over it, do not depend on the host."""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
RUN = os.path.join(ARIADNE, "env", "run.sh")
IN_IMAGE = os.path.isdir("/ariadne") and shutil.which("frama-c") is not None


def annotations(text):
    """[(depth, start, end, body)] of the ACSL annotations of C text:
    `depth` is the C brace depth where the annotation starts (0 = file
    scope), `body` the text between `/*@` and `*/` (or after `//@`)."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/*@", i):
            j = text.find("*/", i + 3)
            j = n if j < 0 else j
            out.append((depth, i, j + 2, text[i + 3:j]))
            i = j + 2
        elif text.startswith("//@", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append((depth, i, j, text[i + 3:j]))
            i = j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            i = n if j < 0 else j + 2
        elif text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text[i] in "\"'":
            q, i = text[i], i + 1
            while i < n and text[i] != q:
                i += 2 if text[i] == "\\" else 1
            i += 1
        else:
            depth += (text[i] == "{") - (text[i] == "}")
            i += 1
    return out


def acsl_code(body):
    """An annotation's text without its ACSL `//` comments, whitespace
    collapsed: what hashing and linting look at."""
    return " ".join(re.sub(r"//[^\n]*", "", body).split())


DIRECTIVE = re.compile(r'^[ \t]*#[ \t]*(?:define|undef|include[ \t]*")'
                       r'(?:[^\n]*\\\n)*[^\n]*', re.M)
BEGIN, END = "__ariadne_expand_begin_{}__", "__ariadne_expand_end_{}__"


def cpp_input(text, anns):
    """The cpp input: directives and marked annotation bodies, in order."""
    parts, last = [], 0
    for k, (_, s, e, body) in enumerate(anns):
        parts += [m.group(0) for m in DIRECTIVE.finditer(text, last, s)]
        parts += [BEGIN.format(k), body, END.format(k)]
        last = e
    parts += [m.group(0) for m in DIRECTIVE.finditer(text, last)]
    return "\n".join(parts) + "\n"


def run_cpp(src_text, cpp_args, work=None):
    """`cpp -P cpp_args` of src_text in the image: (returncode, stdout,
    stderr)."""
    if work is None and not IN_IMAGE:
        work = os.path.join(ARIADNE, "runs")  # mounted by env/run.sh
    d = tempfile.mkdtemp(dir=work, prefix="expand_")
    try:
        with open(os.path.join(d, "in.c"), "w") as f:
            f.write(src_text)
        cmd = (["cpp"] if IN_IMAGE else [RUN, "cpp"]) \
            + ["-P", "-std=c11"] + cpp_args.split() + ["in.c"]
        r = subprocess.run(cmd, cwd=d, capture_output=True, text=True)
        return r.returncode, r.stdout, r.stderr
    finally:
        shutil.rmtree(d, ignore_errors=True)


def expand(text, cpp_args, work=None, keep=()):
    """The text with the macros inside its annotations expanded (see the
    module comment); raises RuntimeError if cpp fails."""
    anns = annotations(text)
    if not anns:
        return text
    rc, out, err = run_cpp(cpp_input(text, anns), cpp_args, work)
    if rc:
        raise RuntimeError("acsl_expand: cpp failed:\n" + err[-2000:])
    found = {int(m.group(1)): " ".join(m.group(2).split())
             for m in re.finditer(r"__ariadne_expand_begin_(\d+)__(.*?)"
                                  r"__ariadne_expand_end_\1__", out, re.S)}
    if len(found) != len(anns):
        raise RuntimeError("acsl_expand: lost annotation markers")
    pieces, last = [], 0
    for k, (_, s, e, body) in enumerate(anns):
        if found[k] == acsl_code(body) or acsl_code(body) in keep:
            continue
        head = text[s:s + 3]
        tail = "" if head == "//@" else "*/"
        pieces += [text[last:s], head, " ", found[k], " ",
                   "\n" * body.count("\n"), tail]
        last = e
    pieces.append(text[last:])
    return "".join(pieces)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("src")
    ap.add_argument("out")
    ap.add_argument("--cpp-args", default="")
    ap.add_argument("--keep", default="")
    a = ap.parse_args()
    try:
        text = expand(open(a.src).read(), a.cpp_args,
                      keep=[k for k in a.keep.split(",") if k])
    except RuntimeError as e:
        sys.exit(str(e))
    with open(a.out, "w") as f:
        f.write(text)


if __name__ == "__main__":
    main()
