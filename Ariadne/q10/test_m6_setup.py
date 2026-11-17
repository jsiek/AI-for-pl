"""Offline tests of run_vst.py's M6 setup (dry runs; no model, no
image): the run directory holds the pristine frozen files and nothing
else of the repository; the fence write-protects the frozen files,
denies earlier runs, existing proofs and the check fixtures, and does
not deny the run directory itself; the per-benchmark cap is used when
--usd is not given; a client run gets the spec restated over its
program and nothing else changed.

    python3 test_m6_setup.py
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import m6  # noqa: E402

fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800])


def dry(bench, run):
    p = subprocess.run([sys.executable, os.path.join(HERE, "run_vst.py"),
                        "--bench", bench, "--dry-run", "--run-dir", run],
                       capture_output=True, text=True)
    assert p.returncode == 0, p.stderr
    return json.loads(p.stdout)


tmp = tempfile.mkdtemp(prefix="test_m6_setup_")
try:
    run = os.path.join(tmp, "dllist-x")
    f = dry("dllist", run)
    cmd = f["command"]
    denied = cmd[cmd.index("--disallowedTools") + 1:
                 cmd.index("--permission-mode")]
    expect("dllist: the run directory holds the frozen files, TASK.md and "
           "the example only",
           sorted(f["files"]) == ["SPEC.md", "TASK.md", "dllist.c",
                                  "example/_CoqProject", "example/good.c",
                                  "example/verif_good.v", "spec_dllist.v"],
           f["files"])
    expect("dllist: the frozen files are byte-identical to the pristine ones",
           all(m6.frozen_unchanged(run, "dllist").values()))
    expect("dllist: cap is the benchmark's ($25)",
           cmd[cmd.index("--max-budget-usd") + 1] == "25.0", cmd)
    for name in ("spec_dllist.v", "SPEC.md", "dllist.c"):
        expect("dllist: writes to %s denied" % name,
               all("%s(/%s/%s)" % (t, run, name) in denied
                   for t in ("Edit", "Write")), denied)
    expect("dllist: runs/q10, vst/b1, the fixtures and bench/ unreadable",
           all(any(x.startswith("Read(") and x.endswith(d + "/**)")
                   for x in denied)
               for d in ("Ariadne/runs/q10", "Ariadne/vst/b1",
                         "Ariadne/q10/m6_fixtures", "Ariadne/bench")),
           denied)
    expect("dllist: the run directory itself is not denied",
           not any(x.endswith("(/%s/**)" % run) for x in denied), denied)
    task = open(os.path.join(run, "TASK.md")).read()
    expect("dllist: the task gives the six frozen statements and the digest",
           all("Lemma body_%s" % fn in task for fn, _, _ in m6.FUNCS)
           and m6.DIGEST in task, task[:300])
    run = os.path.join(tmp, "client3-x")
    f = dry("client3", run)
    spec = open(os.path.join(run, "spec_client3.v")).read()
    orig = open(os.path.join(m6.SGV, "spec_dllist.v")).read()
    expect("client3: spec_client3.v is the frozen spec with only its "
           "Require line changed",
           spec.replace("Require Import SglibVST.client3.",
                        m6.SPEC_REQUIRE) == orig and spec != orig)
    cmd = f["command"]
    expect("client3: cap is the benchmark's ($10)",
           cmd[cmd.index("--max-budget-usd") + 1] == "10.0", cmd)
finally:
    shutil.rmtree(tmp)
print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
