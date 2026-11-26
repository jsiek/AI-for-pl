#!/usr/bin/env python3
"""Ariadne's one command: prover runs, the check, and the VST-readiness
pre-pass, for every target (`targets.toml` files; `list` shows them).

    python3 Ariadne/ariadne/cli.py list
    python3 Ariadne/ariadne/cli.py ready C_FILE [-- CLIGHTGEN_ARGS]
    python3 Ariadne/ariadne/cli.py ready --target NAME
    python3 Ariadne/ariadne/cli.py check NAME PROOF_DIR [--no-coqchk]
    python3 Ariadne/ariadne/cli.py run NAME [--usd N] [--from RUN_DIR]
                                       [--note FILE] [--dry-run]

`check` writes PROOF_DIR/check_NAME.json and manifest_NAME.json; `run`
creates runs/NAME/run-<time>/ (paid: owner-approved budgets only).
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check  # noqa: E402
import session  # noqa: E402
import targets  # noqa: E402
import vst_ready  # noqa: E402


def main(argv):
    extra = argv[argv.index("--") + 1:] if "--" in argv else []
    argv = argv[:argv.index("--")] if "--" in argv else argv
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("list")
    r = sub.add_parser("ready")
    r.add_argument("c_file", nargs="?")
    r.add_argument("--target")
    c = sub.add_parser("check")
    c.add_argument("name")
    c.add_argument("proof_dir")
    c.add_argument("--no-coqchk", action="store_true")
    p = sub.add_parser("run")
    p.add_argument("name")
    p.add_argument("--usd", type=float)
    p.add_argument("--from", dest="previous", metavar="RUN_DIR")
    p.add_argument("--note", help="a file appended to the task")
    p.add_argument("--turns", type=int, default=2000)
    p.add_argument("--seconds", type=int, default=10 * 3600)
    p.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    if a.cmd == "list":
        for n, t in sorted(targets.all_targets().items()):
            print("%-14s %s" % (n, t["toml"]))
    elif a.cmd == "ready":
        if a.target:
            t = targets.load(a.target)
            src = os.path.join(targets.ARIADNE, "runs", "ready_%s.c" % a.target)
            open(src, "w").write(targets.frozen_files(t)[t["c"]])
            try:
                out = vst_ready.report(src, extra)
            finally:
                os.remove(src)
        else:
            out = vst_ready.report(os.path.abspath(a.c_file), extra)
        print(json.dumps(out, indent=1))
    elif a.cmd == "check":
        s = check.check(a.name, a.proof_dir, coqchk=not a.no_coqchk)
        print(json.dumps({k: v for k, v in s.items() if k != "post_lint"},
                         indent=1))
        print("verdict:", s["verdict"], s["violations"])
        return 0 if s["verdict"] == "PROVED" else 1
    else:
        note = a.note and open(a.note).read()
        s = session.run(a.name, a.usd, a.previous, note, a.turns, a.seconds,
                        dry_run=a.dry_run)
        print(json.dumps({k: v for k, v in s.items() if k != "check"},
                         indent=1))
        if "check" in s:
            print("verdict:", s["check"]["verdict"], s["check"]["violations"])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
