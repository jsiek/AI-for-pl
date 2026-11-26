"""Plan M6: run the stage-1 survey clients one at a time (run_vst.py,
each at its benchmark cap), re-check each with check_vst.py, and stop at
the first run whose ledger refuses it.  Prints one JSON line per client.

    python3 run_clients.py 2 3 4 5 6 7 8 9
"""
import glob
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = os.path.join(os.path.dirname(HERE), "runs", "m6")

for n in sys.argv[1:]:
    bench = "client" + n
    before = set(glob.glob(os.path.join(RUNS, bench + "-*[0-9]")))
    r = subprocess.run([sys.executable, os.path.join(HERE, "run_vst.py"),
                        "--bench", bench], capture_output=True, text=True)
    new = sorted(set(glob.glob(os.path.join(RUNS, bench + "-*[0-9]")))
                 - before)
    line = {"bench": bench, "rc": r.returncode, "run": new[-1] if new else None}
    try:
        s = json.loads(r.stdout[r.stdout.index("{"):])
        line.update(end=s.get("end"), usd=s.get("usd"),
                    seconds=s.get("seconds"), turns=s.get("num_turns"))
    except ValueError:
        line["stdout"] = r.stdout[-500:] + r.stderr[-500:]
    # run_vst.py creates the run directory before the ledger is asked, so
    # a refusal leaves a new directory with a refused budget_gate.json
    gate = os.path.join(new[-1], "budget_gate.json") if new else None
    if gate and os.path.exists(gate) and not json.load(open(gate))["ok"]:
        line["refused"] = True
        print(json.dumps(line), flush=True)
        break
    if new:
        c = subprocess.run([sys.executable, os.path.join(HERE, "check_vst.py"),
                            "--bench", bench, new[-1]],
                           capture_output=True, text=True)
        try:
            k = json.loads(c.stdout)
            line.update(accepted=k.get("accepted"),
                        violations=k.get("violations"))
        except ValueError:
            line["check"] = c.stdout[-500:] + c.stderr[-500:]
    print(json.dumps(line), flush=True)
    if r.returncode and not new:
        break
