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

How: Frama-C's own expansion, not an imitation.  Frama-C 33 runs, on
the whole source, its C preprocessing (`gcc -E -C -dD` with its libc,
its machdep headers, `-imacros __fc_builtin_macros.h`, `-std=c11`, and
`-cpp-extra-args`), then its logic preprocessing: every *active*
annotation, with the `#define` / `#undef` lines active before it, goes
through `gcc -E -C -std=c11`, and the result (`cppannot*.c`) holds each
annotation's expansion after a `# LINE "FILE"` marker.  This module runs
`frama-c -keep-temp-files` on the source with the benchmark's
`cpp_args`, reads that file, and takes the blocks of the source file
itself.  So `#if` / `#ifdef` / `#else`, system headers, includes and
pragmas mean exactly what they mean to Frama-C.

The result: each annotation of the source is matched with its block by
start line (and order within a line).  One whose expansion differs from
its own text (comments dropped, whitespace collapsed) is replaced by the
expansion, on one line followed by as many newlines as the original
body had, so every later line keeps its number; other annotations and
all C code are left byte for byte.  An annotation with no block sits in
an inactive branch (`#if 0`, `#else` of a true `#if`): Frama-C never
reads it, so it is **removed** (blanked, line count kept).  A block with
no annotation of the source is an error.  `keep` names annotations left
as they are when their whole text is one of the names (the RAC pipeline
keeps `ARIADNE_ALLOC` and `ARIADNE_FREE`, which its rac.h redefines for
runtime checking).

Frama-C is the image's: this module calls it directly inside the M0
image and through ../env/run.sh outside it, so the expansion, and the
hashes over it, do not depend on the host."""
import argparse
import glob
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
RUN = os.path.join(ARIADNE, "env", "run.sh")
IN_IMAGE = os.path.isdir("/ariadne") and shutil.which("frama-c") is not None
SRC = "ariadne_src.c"


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


BLOCK = re.compile(r"/+__ANNOT_BEG__\n#\s*(\d+)\s+\"([^\"]*)\"[^\n]*\n"
                   r"(.*?)/+__ANNOT_END(?:_NL)?__", re.S)


def _decode(s):
    """Undo Frama-C's encoding of annotations for cpp (backslashes and
    non-ASCII bytes)."""
    s = s.replace("__ANNOT_BACKSLASH__", "\\")
    return re.sub(r"(?:__FC_UTF8_\d+)+",
                  lambda m: bytes(int(x) for x in re.findall(
                      r"__FC_UTF8_(\d+)", m.group(0))).decode(
                          "utf-8", "replace"), s)


def frama_c_blocks(text, cpp_args, work):
    """Frama-C's own expansion of the active annotations of text:
    {line: [expansion, ...]} for the annotations of the source file."""
    open(os.path.join(work, SRC), "w").write(text)
    os.makedirs(os.path.join(work, "tmp"))
    script = (f"TMPDIR=\"$PWD/tmp\" frama-c "
              f"-cpp-extra-args={shlex.quote(cpp_args)} {SRC} "
              "-keep-temp-files")
    cmd = ["sh", "-c", script] if IN_IMAGE else [RUN, "sh", "-c", script]
    r = subprocess.run(cmd, cwd=work, capture_output=True, text=True)
    files = glob.glob(os.path.join(work, "tmp", "cppannot*.c"))
    if len(files) != 1:
        raise RuntimeError("acsl_expand: Frama-C's annotation preprocessing "
                           "did not run:\n" + (r.stdout + r.stderr)[-2000:])
    blocks = {}
    for m in BLOCK.finditer(open(files[0]).read()):
        if os.path.basename(m.group(2)) == SRC:
            # comments dropped, then one line (as acsl_code does)
            blocks.setdefault(int(m.group(1)), []).append(
                acsl_code(_decode(m.group(3))))
    return blocks


def expand(text, cpp_args, work=None, keep=()):
    """The text with the macros inside its annotations expanded and its
    inactive annotations removed (see the module comment); raises
    RuntimeError if Frama-C's preprocessing does not run or does not
    match the source's annotations."""
    src_anns = annotations(text)
    if not src_anns:
        return text
    if work is None and not IN_IMAGE:
        work = os.path.join(ARIADNE, "runs")  # mounted by env/run.sh
    d = tempfile.mkdtemp(dir=work, prefix="expand_")
    try:
        blocks = frama_c_blocks(text, cpp_args, d)
    finally:
        shutil.rmtree(d, ignore_errors=True)
    pieces, last = [], 0
    for _, s, e, body in src_anns:
        line = text.count("\n", 0, s) + 1
        here = blocks.get(line)
        if not here:   # inactive branch: Frama-C does not read it
            pieces += [text[last:s], " ", "\n" * body.count("\n")]
            last = e
            continue
        exp = here.pop(0)
        if exp == acsl_code(body) or acsl_code(body) in keep:
            continue
        head = text[s:s + 3]
        tail = "" if head == "//@" else "*/"
        pieces += [text[last:s], head, " ", exp, " ",
                   "\n" * body.count("\n"), tail]
        last = e
    if any(blocks.values()):
        raise RuntimeError("acsl_expand: Frama-C read an annotation that is "
                           "not in the source: " + repr(
                               [k for k, v in blocks.items() if v]))
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
