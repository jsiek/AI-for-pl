#!/usr/bin/env python3
"""Re-check every kept proof with the merged checker (no model calls):
the libc units (libc/proofs/), sglib's library and 13 clients
(bench/sglib_vst/, bench/sglib_vst/clients/) and picol
(bench/picol/proofs/), four at a time.  Prints one line per target and
exits 1 unless all are PROVED.

    python3 Ariadne/ariadne/check_all.py [NAME ...]
"""
import os
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check  # noqa: E402
import targets  # noqa: E402

KEPT = {"picol": "bench/picol/proofs", "dllist": "bench/sglib_vst"}


def proof_dir(name):
    if name in KEPT:
        return KEPT[name]
    if name.startswith("libc-"):
        return "libc/proofs"
    return "bench/sglib_vst/clients"


def one(name):
    try:
        s = check.check(name, os.path.join(targets.ARIADNE, proof_dir(name)))
        return name, s["verdict"], s["violations"]
    except Exception as e:  # report and go on with the others
        return name, "ERROR", [repr(e)]


def main(names):
    names = names or sorted(targets.all_targets())
    bad = 0
    with ThreadPoolExecutor(4) as pool:
        for name, verdict, why in pool.map(one, names):
            print("%-14s %s %s" % (name, verdict, why if why else ""),
                  flush=True)
            bad += verdict != "PROVED"
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
