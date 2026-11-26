"""Targets: what a run proves and what the check requires, one TOML
table per target.

A `targets.toml` file (Ariadne/*/, Ariadne/bench/*/ or one level
below) holds a
`[defaults]` table and one `[[target]]` table per target; each target is
the defaults updated with its own keys, and every string in it has
`{key}` replaced by the target's own string fields (so one file can
describe the 13 sglib clients).  Keys:

  name        the target's name (unique across all files)
  lib         the Coq logical name of the run directory (-Q . LIB)
  c           the C file that is verified (clightgen -normalize)
  compile     pristine .v files, compiled in order after the C file's AST
  proof       the proof file every run must produce (its module holds
              the goals); more files may precede it in proof_files.txt
  goals       {lemma: statement}: each lemma of `proof`'s module, checked
              against its statement (`{M}` is that module)
  extra       Coq lines the check file must accept (e.g. Gprog entries)
  preamble    Coq lines before the goals (e.g. the Espec instance)
  lint        pristine modules (short names) the leak lint also reads
  lint_allow_none   pass --allow-none to the leak lint
  cap_usd     the default budget of a run
  task        the task template (path; placeholders below)
  [files.NAME]      the run directory's frozen files:
      copy = PATH                        a file of the repository, or
      text = TEXT                        this text, or
      preprocess = [PATH, ...]           C sources (relative to root)
          root = DIR, includes = [...]   preprocessed into one file in the
                                         VST image (CompCert's defines,
                                         musl's headers)
      prefix = TEXT                      put before the text
      replace = [[OLD, NEW], ...]        each OLD occurs exactly once
      libc = true                        expand `(* @libc f g ... *)`
                                         lines with libc/specs/f.v, ...
      check = false                      only for reading: not compiled
  [dirs] NAME = [PATTERN, ...]   files copied into the directory NAME/ of
              the run (example/ is always VST's smoke proof)

Paths are relative to Ariadne/.
"""
import glob
import os
import re
import subprocess
import sys
import threading
import tomllib

ARIADNE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RUN = os.path.join(ARIADNE, "vst", "run.sh")
LIBC_SPECS = os.path.join(ARIADNE, "libc", "specs")


def _fill(x, env):
    if isinstance(x, str):
        for k, v in env.items():
            x = x.replace("{%s}" % k, v)
        return x
    if isinstance(x, list):
        return [_fill(y, env) for y in x]
    if isinstance(x, dict):
        return {_fill(k, env): _fill(v, env) for k, v in x.items()}
    return x


def _merge(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = _merge(out[k], v) if isinstance(v, dict) and isinstance(
            out.get(k), dict) else v
    return out


def all_targets():
    """{name: target dict} from every targets.toml."""
    out = {}
    files = sorted(glob.glob(os.path.join(ARIADNE, "*", "targets.toml"))
                   + glob.glob(os.path.join(ARIADNE, "bench", "*",
                                            "targets.toml"))
                   + glob.glob(os.path.join(ARIADNE, "bench", "*", "*",
                                            "targets.toml")))
    for path in files:
        d = tomllib.load(open(path, "rb"))
        for t in d.get("target", []):
            env = {k: v for k, v in t.items() if isinstance(v, str)}
            m = _fill(_merge(_fill(d.get("defaults", {}), env), t), env)
            m["toml"] = os.path.relpath(path, ARIADNE)
            assert m["name"] not in out, m["name"]
            out[m["name"]] = m
    return out


def load(name):
    ts = all_targets()
    if name not in ts:
        sys.exit("unknown target %s (known: %s)" % (name, " ".join(sorted(ts))))
    return ts[name]


def preprocess(sources, root, includes, header):
    """C sources preprocessed into one file as clightgen does (the
    caller's root is mounted in the VST image)."""
    root = os.path.join(ARIADNE, root)
    if len(sources) == 1:
        rel, wrapper = sources[0], None
    else:
        rel = ".ariadne_unit_%d_%d.c" % (os.getpid(), threading.get_ident())
        wrapper = os.path.join(root, rel)
        open(wrapper, "w").write("".join('#include "%s"\n' % s
                                         for s in sources))
    try:
        r = subprocess.run([RUN, "clightgen", "-E", "-Wp,-nostdinc,-P",
                            "-D_XOPEN_SOURCE=700"]
                           + ["-I" + i for i in includes] + [rel],
                           cwd=root, capture_output=True, text=True)
    finally:
        if wrapper:
            os.remove(wrapper)
    if r.returncode:
        sys.exit("preprocessing failed: " + r.stderr[-800:])
    body = "\n".join(l for l in r.stdout.splitlines() if l.strip())
    return header + body + "\n"


def expand_libc(text):
    """Replace each `(* @libc f g *)` line with libc/specs/f.v, g.v."""
    def one(m):
        return "\n".join(open(os.path.join(LIBC_SPECS, f + ".v")).read()
                         .rstrip("\n") for f in m.group(1).split())
    return re.sub(r"^\(\* @libc ([\w ]+) \*\)$", one, text, flags=re.M)


def file_text(spec):
    if "text" in spec:
        text = spec["text"]
    elif "copy" in spec:
        text = open(os.path.join(ARIADNE, spec["copy"])).read()
    else:
        text = preprocess(spec["preprocess"], spec.get("root", "."),
                          spec.get("includes", []),
                          "/* %s, preprocessed by ariadne/targets.py with "
                          "CompCert's defines.  Do not edit. */\n"
                          % ", ".join(spec["preprocess"]))
    for old, new in spec.get("replace", []):
        assert text.count(old) == 1, (old, spec)
        text = text.replace(old, new)
    if spec.get("libc"):
        text = expand_libc(text)
    return spec.get("prefix", "") + text


def frozen_files(t):
    """{name: text} of the target's frozen files."""
    return {name: file_text(spec) for name, spec in t.get("files", {}).items()}


def checked_files(t):
    return [n for n, s in t.get("files", {}).items() if s.get("check", True)]


def modules(t, files):
    return ["%s.%s" % (t["lib"], f[:-2]) for f in files]
