"""End-to-end tests of harness.py on bad annotation overlays of B1: each
must be rejected by the named guardrail before any tool runs on it, with
no certificate.  Each run takes about a second (Frama-C's `-print` only).

    python3 test_harness.py
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
B1 = os.path.join(ARIADNE, "bench", "b1")
fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800].replace("\n", "\n    "))


src = open(os.path.join(B1, "b1.c")).read()
BAD = {
    "overlay": ("    l->i = input[k];", "    l->i = input[k] + 1;"),
    "frozen_spec": ("    requires live(elem);", "    requires \\false;"),
    "lint_acsl": ("  //@ assert live_dll(\\null, the_list, \\Nil);",
                  "  //@ admit live_dll(\\null, the_list, \\Nil);"),
}
tmp = tempfile.mkdtemp(dir=os.path.join(ARIADNE, "runs"), prefix="test_")
try:
    for guard, (old, new) in BAD.items():
        assert src.count(old) == 1, old
        edited = os.path.join(tmp, f"{guard}.c")
        open(edited, "w").write(src.replace(old, new))
        run = os.path.join(tmp, f"run_{guard}")
        p = subprocess.run([sys.executable, os.path.join(HERE, "harness.py"),
                            B1, "--overlay", edited, "--run-dir", run],
                           capture_output=True, text=True)
        r = json.load(open(os.path.join(run, "report.json")))
        failed = r.get("failure", {}).get("guardrails_failed", [])
        expect(f"{guard}: bad overlay rejected before step 0",
               p.returncode == 1 and r["verdict"] == "failed"
               and guard in failed and "0_rac" not in r["steps"]
               and not os.path.exists(os.path.join(run, "cert")),
               {"failed": failed, "steps": list(r["steps"])})
finally:
    shutil.rmtree(tmp)
print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
