"""Plan M6: the run_vst.py / check_vst.py port to the frozen stage-1
spec of sglib's DL list (bench/sglib_vst/, digest ee6043a2f971a9f6).

Benchmarks:
  dllist      the six library functions: prove the given funspecs
              (`semax_body` for add, get_first, get_last,
              it_init_on_equal, it_init, it_next) in verif_dllist.v,
              which Requires the frozen spec and never edits it;
  client1-9   the 9 stage-1 survey clients (bench/sglib_vst/clients/):
              write the client's funspecs (leak-free: no TT, `main`
              ends with mem_mgr), prove every function of clientN.c and
              `semax_prog`, against the frozen funspecs restated for the
              client's program (spec_clientN.v: the frozen file with its
              one `Require Import SglibVST.dllist.` line pointing at the
              client's program instead; nothing else changes).

The harness writes the run directory; the frozen files in it are
write-denied (fence) and compared with the pristine ones after the run;
check() recompiles with pristine copies only and checks the result.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
SGV = os.path.join(ARIADNE, "bench", "sglib_vst")
RUN = os.path.join(ARIADNE, "vst", "run.sh")
EXPECTED = os.path.join(ARIADNE, "vst", "smoke", "expected_assumptions.txt")
LIB = "SglibVST"
DIGEST = "ee6043a2f971a9f6"
SPEC_REQUIRE = "Require Import SglibVST.dllist."

# name, funspec, takes Rc
FUNCS = [("add", "add_spec", False),
         ("get_first", "get_first_spec", False),
         ("get_last", "get_last_spec", False),
         ("it_init_on_equal", "it_init_on_equal_spec", True),
         ("it_init", "it_init_spec", False),
         ("it_next", "it_next_spec", True)]

# per-benchmark budget caps (USD), used when --usd is not given
CAPS = {"b1a": 15.0, "b1c": 15.0, "dllist": 25.0}
CLIENT_IDS = [str(i) for i in range(1, 10)] + ["b1", "b1a", "b1c", "st"]
CAPS.update({"client" + i: 10.0 for i in CLIENT_IDS})
BENCHES = sorted(CAPS)
# the covered clients ported to the frozen spec (survey, "Covered
# clients ported")
PORTS = {"b1": "B1 (b1/b1.c:b1)", "b1a": "B1a (b1a/b1a_ref.c:b1)",
         "b1c": "B1c (b1c/b1c_ref.c:b1)",
         "st": "the self-test driver st_iter_equal (selftest/wp/driver.c)"}
FORBIDDEN = r"\b(admit|Axiom|Parameter|Conjecture)\b"


def is_m6(bench):
    return bench == "dllist" or bench.startswith("client")


def statement(f, spec, rc, qualified=True):
    """The frozen statement of f's semax_body lemma (fully qualified for
    the check, so that nothing the proof file defines can shadow it)."""
    s, d = (("SglibVST.spec_dllist.", "SglibVST.dllist.") if qualified
            else ("", ""))
    sp = "(%s%s Rc)" % (s, spec) if rc else s + spec
    return ("forall Rc : globals -> val -> mpred, semax_body %sVprog "
            "(%sGprog Rc) %sf_sglib_dllist_%s %s" % (s, s, d, f, sp))


def client_spec(n):
    """spec_clientN.v: the frozen spec over client N's program."""
    t = open(os.path.join(SGV, "spec_dllist.v")).read()
    assert t.count(SPEC_REQUIRE) == 1
    return t.replace(SPEC_REQUIRE, "Require Import SglibVST.client%s." % n)


LIB_REQUIRE = "Require Import SglibVST.dllist SglibVST.spec_dllist."


def client_lib(n):
    """lib_clientN.v: the checked library proof (verif_dllist.v, pilot 2)
    over client N's program; it re-checks with only its Require changed."""
    t = open(os.path.join(SGV, "verif_dllist.v")).read()
    assert t.count(LIB_REQUIRE) == 1
    return t.replace(LIB_REQUIRE, "Require Import SglibVST.client%s "
                     "SglibVST.spec_client%s." % (n, n))


def frozen_files(bench):
    """{name in the run directory: pristine text}."""
    files = {"spec_dllist.v": open(os.path.join(SGV, "spec_dllist.v")).read(),
             "SPEC.md": open(os.path.join(SGV, "SPEC.md")).read(),
             "dllist.c": open(os.path.join(SGV, "dllist.c")).read()}
    if bench.startswith("client"):
        n = bench[len("client"):]
        files["client%s.c" % n] = open(os.path.join(
            SGV, "clients", "client%s.c" % n)).read()
        files["spec_client%s.v" % n] = client_spec(n)
        files["lib_client%s.v" % n] = client_lib(n)
        files["CLIENT_SURVEY.md"] = open(os.path.join(
            ARIADNE, "bench", "sglib_spec", "CLIENT_SURVEY.md")).read()
    return files


def proof_file(bench):
    return "verif_%s.v" % bench


TASK_DLLIST = """\
# Task: VST proofs of the frozen stage-1 spec of sglib's DL list

You are verifying C code with VST (Verifiable C 2.17, CompCert 3.18
clightgen, Rocq 9.0.1).  Files in this directory:

* `dllist.c`: the C code (sglib's doubly linked list: six functions).
  Do not change it.
* `spec_dllist.v`: the **frozen** public spec: representation
  predicates and the VST funspecs of the six functions, approved by the
  owner (digest {digest}).  Do not change it: it is write-protected and
  checked after the run.  It ends with six `Admitted` lemmas that only
  type-check the statements; your job is to prove them elsewhere.
* `SPEC.md`: the same spec in English, with the reason for each clause.
* `example/`: a small complete VST proof that is not this benchmark
  (`good.c`, `verif_good.v`), as a reference for the setup and style.

## What to produce

One file, `verif_dllist.v`, that starts with

    Require Import VST.floyd.proofauto.
    Require Import VST.floyd.library.
    Require Import SglibVST.dllist SglibVST.spec_dllist.

and proves, each ending in `Qed.`, these six lemmas with exactly these
names and statements (a `Section` with `Variable Rc : globals -> val ->
mpred.` gives the `forall Rc` form):

{lemmas}

No `Axiom`, `Parameter`, `admit` or `Conjecture`, and no change to the
funspecs.  Helper lemmas are fine (in `verif_dllist.v`).  If you cannot
finish a proof, end it with `Admitted.` so that the file still
compiles, and say which ones are open in your last answer.

Tip: a function whose funspec has no `GLOBALS (gv)` may still call one
that has, by first adding `gvars gv` to its LOCAL clause: `apply
semax_pre with (EX gv: globals, PROP () LOCAL (gvars gv; ...) SEP
(...))` and, in the side goal after `go_lowerx`, `apply exp_right with
(globals_of_env rho)` (`gvars_denote gv rho` is `gv = globals_of_env
rho`).

"""

# shared by both tasks: {compile} is the list of compile commands
TOOLS = """\
## How to run the tools

Your only command is `{tool}`: it runs one command inside the VST image,
with this directory mounted at `/work` (the current directory there).
For example:

{compile}

The example compiles the same way from `example/` with `-Q . Smoke`.
`-native-compiler no` is required.  Each call starts a container (a few
seconds); `coqc` on a large VST file can take minutes, so give the Bash
call a long timeout.  `coqtop` works the same way (pipe a script into it
to see a goal).  The VST and Rocq sources are in the image under
`/home/rocq/.opam/4.14.2/lib/coq/`; you may read them with the tool.

## Rules

* Do not read or search anything outside this directory except the VST
  and Rocq installation inside the image (through the tool).  In
  particular do not look for existing proofs of this code.
* Run one command per Bash call (no `&&`, `;`, pipes or newlines outside
  the tool's own argument), and write files with Write or Edit.  Any
  other command is denied; a denial does not end the task.
* You have a budget of about ${usd} for this task.  Work toward a
  complete `{verif}`; when you are done (or out of budget),
  answer with one line per function: its name and PROVED or OPEN.
"""

TASK_CLIENT = """\
# Task: VST proof of stage-1 client {n} of sglib's DL list

You are verifying C code with VST (Verifiable C 2.17, CompCert 3.18
clightgen, Rocq 9.0.1).  Files in this directory:

* `client{n}.c`: the client program: sglib's six DL-list functions
  (verbatim), the client's driver and `main`.  Do not change it.
* `spec_client{n}.v`: the **frozen** public spec of the six library
  functions (digest {digest}), restated over this program (only its
  `Require Import` line differs from `spec_dllist.v`).  Do not change it.
* `SPEC.md`, `CLIENT_SURVEY.md`: the spec in English and the client
  survey ({where}).
* `lib_client{n}.v`: the **finished** proofs of the six library
  functions over this program: `body_add`, `body_get_first`,
  `body_get_last`, `body_it_init_on_equal`, `body_it_init`,
  `body_it_next`, each `forall Rc, semax_body Vprog (Gprog Rc) f spec`
  with `Vprog`, `Gprog` and the specs from `spec_client{n}.v`.  Use
  them; do not prove the library functions again.  Do not change it.
* `example/`: a small complete VST proof that is not this benchmark.

## What to produce

One file, `verif_client{n}.v`, that starts with

    Require Import VST.floyd.proofauto.
    Require Import VST.floyd.library.
    Require Import SglibVST.client{n} SglibVST.spec_client{n}.
    Require SglibVST.lib_client{n}.

and that

* defines `Rc_client : globals -> val -> mpred` (the comparator
  resource this program uses; any value if it uses no comparator);
* defines its own `Gprog`, in which each of the six library functions
  has exactly its frozen funspec instantiated at `Rc_client`.  The
  check proves, by `reflexivity`, `find_id i Gprog = find_id i
  (SglibVST.spec_client{n}.Gprog Rc_client)` for each library function
  `i`;
* declares `#[export] Existing Instance NullExtension.Espec.` (the
  check states `semax_prog` with it);
* writes funspecs for the client's own functions and `main`;
* proves `semax_body` for each of the client's own functions and
  `main`, and `prog_correct : semax_prog prog tt Vprog Gprog`, each
  ending in `Qed.`.  For a library function, derive its `semax_body`
  under your `Gprog` from the `lib_client{n}` lemma (e.g. with
  `semax_body_subsumption`).

Leak freedom (owner, 2026-11-17): no postcondition may contain `TT` or
an existential over `mpred` (also inside the predicates it uses), and
`main`'s postcondition is `mem_mgr gv` plus the program's globals (and
`has_ext tt`, which `main_pre` provides: VST's external-state token,
not memory).

No `Axiom`, `Parameter`, `admit` or `Conjecture`.  If you cannot finish
a proof, end it with `Admitted.` so that the file still compiles, and
say which ones are open in your last answer.

"""


def task(bench, tool, usd):
    if bench == "dllist":
        lemmas = "\n".join("    Lemma body_%s :\n      %s."
                           % (f, statement(f, s, r, False))
                           for f, s, r in FUNCS)
        text = TASK_DLLIST.replace("{lemmas}", lemmas)
        files = ["dllist.c", "dllist.v", "spec_dllist.v", "verif_dllist.v"]
    else:
        n = bench[len("client"):]
        where = ('this client is "client %s" under "New clients"' % n
                 if n.isdigit() else
                 'this client is %s, ported under "Covered clients '
                 'ported"' % PORTS[n])
        text = TASK_CLIENT.replace("{where}", where).replace("{n}", n)
        files = ["client%s.%s" % (n, e) for e in ("c", "v")] + [
            f % n for f in ("spec_client%s.v", "lib_client%s.v",
                            "verif_client%s.v")]
    compile = "\n".join(
        "    {tool} " + ("clightgen -normalize " if f.endswith(".c") else
                         "coqc -native-compiler no -Q . SglibVST ") + f
        for f in files)
    return ((text + TOOLS).replace("{compile}", compile)
            .replace("{verif}", proof_file(bench))
            .replace("{digest}", DIGEST).replace("{tool}", tool)
            .replace("{usd}", str(usd)))


def setup(run, bench):
    os.makedirs(os.path.join(run, "example"))
    for name, text in frozen_files(bench).items():
        open(os.path.join(run, name), "w").write(text)
    smoke = os.path.join(ARIADNE, "vst", "smoke")
    for f in ("good.c", "verif_good.v", "_CoqProject"):
        shutil.copy(os.path.join(smoke, f), os.path.join(run, "example"))


def deny_rules(run, bench, roots):
    """Fence additions: no writes to `bench`'s frozen files; no reads of
    earlier runs' proofs, of the existing VST proofs, or of the check
    fixtures (which hold a hand proof)."""
    rules = []
    for name in frozen_files(bench):
        rules += ["%s(/%s/%s)" % (t, run, name) for t in ("Edit", "Write")]
    for r in sorted(roots):
        # (other runs under runs/m6 are denied by run_vst.py's sibling
        # rule; the run directory itself is under runs/m6)
        for d in ("Ariadne/runs/q10", "Ariadne/vst/b1",
                  "Ariadne/q10/m6_fixtures", "Ariadne/bench"):
            rules += ["%s(/%s/%s/**)" % (t, r, d)
                      for t in ("Read", "Edit", "Write")]
    return rules


def frozen_unchanged(run, bench):
    """{file: True if the run directory's copy equals the pristine one}."""
    out = {}
    for name, text in frozen_files(bench).items():
        p = os.path.join(run, name)
        out[name] = os.path.exists(p) and hashlib.sha256(
            open(p, "rb").read()).hexdigest() == hashlib.sha256(
            text.encode()).hexdigest()
    return out


# ---------------------------------------------------------------- check

def sh(work, cmd, log):
    with open(os.path.join(work, log), "w") as f:
        return subprocess.run([RUN] + cmd, cwd=work, stdout=f,
                              stderr=subprocess.STDOUT).returncode


def coqc(work, path, log):
    return sh(work, ["coqc", "-native-compiler", "no", "-Q", ".", LIB,
                     path], log)


def allowed_axioms():
    names = set()
    for l in open(EXPECTED):
        m = re.match(r"([A-Za-z_][\w.']*) :", l)
        if m:
            names.add(m.group(1).split(".")[-1])
    return names


def assumptions(text):
    """Axiom names in Print Assumptions output (None: closed)."""
    if "Closed under the global context" in text:
        return []
    if "Axioms:" not in text:
        return None
    names = []
    for l in text[text.index("Axioms:") + len("Axioms:"):].split("\n"):
        m = re.match(r"([A-Za-z_][\w.']*) :", l)
        if m:
            names.append(m.group(1).split(".")[-1])
    return names


DECL = (r"\b(?:Lemma|Theorem|Corollary|Fact|Remark|Proposition|Example|"
        r"Definition|Fixpoint|Instance|Hypothesis|Hypotheses|Variable|"
        r"Variables|Context)\s+([A-Za-z_][\w']*)")


def declared(text):
    """Names the proof file declares (short names, as assumptions())."""
    return set(re.findall(DECL, text))


def lint_text(text):
    out = []
    for i, l in enumerate(text.split("\n"), 1):
        code = re.sub(r"\(\*.*?\*\)", "", l)
        if re.search(FORBIDDEN, code):
            out.append("%d: %s" % (i, l.strip()))
    return out


def check(run, bench, out_dir=None):
    """Recompile with pristine files and check the run's proof file.
    Returns (and writes to <run>/m6-check/summary.json) the summary."""
    run = os.path.abspath(run)
    out = out_dir or os.path.join(run, "m6-check")
    work = os.path.join(out, "control")
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(work)
    verif_name = proof_file(bench)
    verif = os.path.join(run, verif_name)
    s = {"bench": bench, "digest": DIGEST,
         "frozen_unchanged": frozen_unchanged(run, bench),
         "violations": []}
    # a changed .c/.v file is a violation; a changed document (SPEC.md,
    # CLIENT_SURVEY.md) is only recorded: the check compiles pristine
    # copies, and the documents may be updated after a run (e.g. the
    # survey's Callbacks section, 2026-11-20)
    changed = sorted(k for k, v in s["frozen_unchanged"].items() if not v)
    if any(k.endswith((".c", ".v")) for k in changed):
        s["violations"].append("a frozen file in the run directory was "
                               "changed: %s" % changed)
    if not os.path.exists(verif):
        s["violations"].append("%s missing" % verif_name)
        return finish(out, s)
    text = open(verif).read()
    s["forbidden"] = lint_text(text)
    if s["forbidden"]:
        s["violations"].append("forbidden keywords: %s" % s["forbidden"])
    s["admitted_count"] = len(re.findall(r"\bAdmitted\.", text))
    for name, t in frozen_files(bench).items():
        if name.endswith((".c", ".v")):
            open(os.path.join(work, name), "w").write(t)
    shutil.copy(verif, work)
    os.makedirs(os.path.join(work, "lint"))
    shutil.copy(os.path.join(SGV, "lint", "PostLint.v"),
                os.path.join(work, "lint"))
    prog = "dllist" if bench == "dllist" else bench
    c = {"clightgen": sh(work, ["clightgen", "-normalize", prog + ".c"],
                         "clightgen.log")}
    c["ast"] = coqc(work, prog + ".v", "ast.log")
    spec = "spec_dllist.v" if bench == "dllist" else "spec_%s.v" % bench
    c["spec"] = coqc(work, spec, "spec.log")
    if bench != "dllist":
        c["lib"] = coqc(work, "lib_%s.v" % bench, "lib.log")
    c["verif"] = coqc(work, verif_name, "verif.log")
    s["compile"] = c
    if any(c.values()):
        s["violations"].append("does not compile: %s" % c)
        s["verif_error"] = open(os.path.join(work, "verif.log")).read()[-1500:]
        return finish(out, s)
    allowed = allowed_axioms()
    mod = "SglibVST." + verif_name[:-2]
    goals = ([("body_" + f, statement(f, sp, r)) for f, sp, r in FUNCS]
             if bench == "dllist" else
             [("prog_correct", None)])
    s["lemmas"] = {}
    for name, stmt in goals:
        chk = "check_%s.v" % name
        lines = ["Require %s." % mod,
                 "Require Import VST.floyd.proofauto.",
                 "Require Import VST.floyd.library."]
        if bench == "dllist":
            lines += ["Require Import SglibVST.dllist SglibVST.spec_dllist.",
                      "Check (%s.%s : %s)." % (mod, name, stmt)]
        else:
            lines += ["Require Import %s.%s %s.spec_%s." % (LIB, bench, LIB,
                                                           bench),
                      "#[local] Existing Instance NullExtension.Espec.",
                      "Check (%s.%s : semax_prog %s.%s.prog tt "
                      "%s.spec_%s.Vprog %s.Gprog)."
                      % (mod, name, LIB, bench, LIB, bench, mod)]
            # the six library entries of the client's Gprog are the
            # frozen funspecs at the client's Rc
            fid = "VST.veric.initial_world.find_id %s.%s._sglib_dllist_" % (
                LIB, bench)
            lines += ["Goal %s%s %s.Gprog = %s%s (%s.spec_%s.Gprog "
                      "%s.Rc_client). Proof. reflexivity. Qed."
                      % (fid, f, mod, fid, f, LIB, bench, mod)
                      for f, _, _ in FUNCS]
        lines += ["Print Assumptions %s.%s." % (mod, name)]
        open(os.path.join(work, chk), "w").write("\n".join(lines) + "\n")
        rc = coqc(work, chk, chk + ".log")
        log = open(os.path.join(work, chk + ".log")).read()
        if rc:
            s["lemmas"][name] = "MISSING OR WRONG STATEMENT"
            s["violations"].append(
                "%s: missing or not the frozen statement%s" % (name, (
                    "" if bench == "dllist" else
                    ", or Gprog's library entries are not the frozen "
                    "funspecs at Rc_client")))
            continue
        # The lint forbids Axiom/Parameter in the proof file, and only the
        # proof file and pristine files are compiled here, so an
        # assumption outside the allow-list is an Admitted lemma: open.
        # So is one named in the proof file, even with an allowed name
        # (`Module Evil. Lemma mem_mgr : False. Admitted. End Evil.`).
        ax = assumptions(log)
        extra = (sorted((set(ax) - allowed) | (set(ax) & declared(text)))
                 if ax is not None else ["?"])
        s["lemmas"][name] = ("PROVED" if not extra else
                             "OPEN (assumes %s)" % ", ".join(extra))
    # with the frozen spec module, so that a funspec the proof builds from
    # the spec's definitions (e.g. `cmp_spec Rc f` for a comparator) is
    # unfolded and checked rather than failing closed
    pl = subprocess.run(["python3", "-I", os.path.join(SGV, "lint",
                                                       "post_lint.py"),
                         "--root", work, "--allow-none",
                         "%s.%s" % (LIB, spec[:-2]), mod],
                        capture_output=True, text=True)
    s["post_lint"] = {"rc": pl.returncode, "out": pl.stdout[-2000:]}
    if pl.returncode:
        s["violations"].append("post_lint failed (leak freedom)")
    return finish(out, s)


def finish(out, s):
    lem = s.get("lemmas", {})
    s["proved"] = sorted(k for k, v in lem.items() if v == "PROVED")
    s["open"] = sorted(k for k, v in lem.items() if v != "PROVED")
    s["accepted"] = (not s["violations"] and bool(lem)
                     and not s["open"])
    os.makedirs(out, exist_ok=True)
    json.dump(s, open(os.path.join(out, "summary.json"), "w"), indent=1)
    return s
