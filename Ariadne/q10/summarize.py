#!/usr/bin/env python3
"""Plan Q10: one table row per run, from the run directories.

    python3 summarize.py ../runs/q10/wp-run2 ... ../runs/q10/vst-run1

Frama-C runs (harness.py): wall time and verdict from report.json; tokens,
USD and turns summed over every `claude -p` result.json under
annotator/ and tier2/ (`modelUsage`); goals from the census; step 0's
last result from logs/step0_rac.log (PASS/FAIL, mutants caught, the
coverage line); mutants from q10-mutants/summary.json (check_wp.py).
VST runs (run_vst.py): summary.json and q10-check/summary.json.
"""
import glob
import json
import os
import re
import sys

KEYS = ("inputTokens", "outputTokens", "cacheCreationInputTokens",
        "cacheReadInputTokens")


def tokens(results):
    t = dict.fromkeys(KEYS, 0)
    usd = turns = 0
    for d in results:
        for u in d.get("modelUsage", {}).values():
            for k in KEYS:
                t[k] += u.get(k, 0)
        usd += d.get("total_cost_usd") or 0
        turns += d.get("num_turns") or 0
    return t, usd, turns


def fmt(t):
    return (" / ".join(f"{t[k]:,}" for k in KEYS)
            + f" ({sum(t.values()) / 1e6:.2f} M)")


def wp(run):
    r = json.load(open(os.path.join(run, "report.json")))
    ann = [json.load(open(p)) for p in
           sorted(glob.glob(os.path.join(run, "annotator", "*",
                                         "result.json")))]
    prv = [json.load(open(p)) for p in
           sorted(glob.glob(os.path.join(run, "tier2", "*", "result.json")))]
    t, usd, turns = tokens(ann + prv)
    c = r["census"]
    opened = [g for g in r["goals"] if g["discharger"] == "open"]
    fo = sum(g["pass"] == "functions" for g in opened) \
        if opened and "pass" in opened[0] else None
    row = {"run": os.path.basename(run), "seconds": r["seconds"],
           "tokens": fmt(t), "usd": round(usd, 2),
           "calls": f"{len(ann) + len(prv)} ({len(ann)} annotator, "
                    f"{len(prv)} prover), {turns} turns",
           "proved": f"{c['proved']} / {c['goals']} "
                     f"(Qed {c['qed']}, SMT {c['smt']}, Coq {c['coq']})",
           "open": c["open"], "verdict": r["verdict"],
           "cap_hit": r.get("cap_hit")}
    if fo is not None:
        row["open_functions"] = fo
    log = os.path.join(run, "logs", "step0_rac.log")
    if os.path.exists(log):
        text = open(log).read().rsplit("\n$ ", 1)[-1]
        cov = re.findall(r"^coverage: (.*)", text, re.M)
        caught = len(re.findall(r"\[ok\]\s*$", text, re.M))
        total = len(re.findall(r"\[(ok|MISSED)\]\s*$", text, re.M))
        res = ("PASS" if re.search(r"^PASS: runtime checking", text, re.M)
               else "FAIL")
        row["step0"] = (f"{res}; mutants caught {caught}/{total}; "
                        + (cov[-1] if cov else "no coverage line"))
        row["step0_runs"] = len(re.findall(
            r"^PASS: runtime checking|^FAIL: runtime checking",
            open(log).read(), re.M))
    m = os.path.join(run, "q10-mutants", "summary.json")
    if os.path.exists(m):
        s = json.load(open(m))
        names = [k for k in s if k != "control"]
        row["mutants"] = (f"{sum(s[k]['verdict'] == 'rejected' for k in names)}"
                          f" / {len(names)}")
    return row


def vst(run):
    s = json.load(open(os.path.join(run, "summary.json")))
    t = {"inputTokens": s["usage"]["claude-opus-5-5"]["input_tokens"],
         "outputTokens": s["usage"]["claude-opus-5-5"]["output_tokens"],
         "cacheCreationInputTokens":
             s["usage"]["claude-opus-5-5"]["cache_creation_input_tokens"],
         "cacheReadInputTokens":
             s["usage"]["claude-opus-5-5"]["cache_read_input_tokens"]}
    row = {"run": os.path.basename(run), "seconds": s["seconds"],
           "tokens": fmt(t), "usd": round(s["total_cost_usd"], 2),
           "calls": f"1, {s['num_turns']} turns"}
    c = os.path.join(run, "q10-check", "summary.json")
    if os.path.exists(c):
        d = json.load(open(c))
        row["proved"] = ", ".join(f"{k} {v}" for k, v in d["lemmas"].items())
        row["mutants"] = (f"{sum(v['verdict'] == 'rejected' for v in d['mutants'].values())}"
                          f" / {len(d['mutants'])} C-level")
    return row


for run in sys.argv[1:]:
    run = os.path.abspath(run)
    row = wp(run) if os.path.exists(os.path.join(run, "report.json")) \
        else vst(run)
    print(json.dumps(row, indent=1))
