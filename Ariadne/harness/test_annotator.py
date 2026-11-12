"""Offline tests of step 5 (annotator.py, harness.py --annotator): no
model calls.

  1. the Opus command line is fenced like tier 2's, and Opus.run with a
     fake `claude` reserves and charges the ledger's annotator role and
     returns the SOURCE.c it left (also: a budget refusal);
  2. end to end on B1's frozen-only variant, get_first only, with a fake
     annotator (fake_patches.py):
     a. a good patch (the human's get_first annotations and lemmas) is
        accepted, step 3 runs again on it, and only the five lemmas
        M1 proved in Coq stay open (no Coq tier offline);
     b. a patch that weakens a frozen contract, one that adds a
        predicate, one with a ghost loop, and one with a false loop
        invariant are each rejected (the first three by the guardrails,
        before Frama-C; the last by step 0's runtime checks), each
        rejection goes back to the annotator with its reason, and WP
        runs only once;
     d. a call the fence stopped with no patch is retried once, with the
        refused command named in TASK.md, and not twice;
     c. an annotator that keeps adding useless asserts runs into
        --max-iterations.

    python3 test_annotator.py [--quick]     (--quick: only 1, no image)
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import annotator  # noqa: E402
import budget  # noqa: E402
import fake_patches  # noqa: E402

B1 = os.path.join(ARIADNE, "bench", "b1")
fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:1200].replace("\n", "\n    "))


def unit(tmp):
    import harness
    expect("rac_outcome: a fired check is `false`, an E-ACSL build "
           "failure alone `inconclusive`",
           harness.rac_outcome({"ok": False, "fail_lines": [
               "FAIL: E-ACSL run of b1.c:"]}) == "false"
           and harness.rac_outcome({"ok": False, "fail_lines": [
               "FAIL: E-ACSL build of b1.c:"]}) == "inconclusive"
           and harness.rac_outcome({"ok": False, "fail_lines": [
               "FAIL: E-ACSL build of b1.c:",
               "FAIL: ASan+UBSan build of b1.c:"]}) == "false"
           and harness.rac_outcome({"ok": True}) == "pass")
    cmd = annotator.opus_command("/w", calls=12)
    flags = " ".join(cmd[2:])
    expect("opus command: Opus 5.5, JSON, restricted tools, no git",
           cmd[:2] == ["claude", "-p"] and "--model claude-opus-5-5" in
           flags and "--output-format json" in flags
           and "--tools Bash,Read,Write,Edit" in flags
           and "--permission-mode dontAsk" in flags
           and "--restricted" in flags and "--safe-mode" in flags
           and "Bash(git *)" in cmd and "--max-budget-usd" in cmd, flags)
    allowed = cmd[cmd.index("--allowedTools") + 1:
                  cmd.index("--disallowedTools")]
    expect("opus command: Bash only annotator_cli on SOURCE.c, files only "
           "in the work dir",
           all(x.startswith((f"Bash(python3 {annotator.CLI} ",
                             "Read(//w/", "Write(//w/", "Edit(//w/"))
               for x in allowed) and len(allowed) == 5
           and all(" SOURCE.c" in x for x in allowed if x.startswith("Bash")),
           allowed)
    bindir = os.path.join(tmp, "bin")
    os.makedirs(bindir)
    fake = os.path.join(bindir, "claude")
    with open(fake, "w") as f:
        f.write(f"""#!{sys.executable}
import json, sys
json.dump(sys.argv, open("argv.json", "w"))
src = open("SOURCE.c").read()
open("SOURCE.c", "w").write(src + "/* patched */\\n")
print(json.dumps({{"subtype": "success", "num_turns": 3, "result": "DONE",
  "total_cost_usd": 0.5, "modelUsage": {{"claude-opus-5-5": {{
  "inputTokens": 10, "outputTokens": 20, "cacheCreationInputTokens": 0,
  "cacheReadInputTokens": 100, "costUSD": 0.5}}}}}}))
""")
    os.chmod(fake, 0o755)
    old = os.environ["PATH"]
    os.environ["PATH"] = bindir + os.pathsep + old
    try:
        led = budget.Ledger(os.path.join(tmp, "ledger.json"))
        o = annotator.Opus(os.path.join(tmp, "ann"), led, "cfg.json",
                           "base.c", usd=5.0)
        r = o.run("int x;\n", "# task\n")
        s = led.summary()
        expect("Opus.run: answered, SOURCE.c returned, $0.50 charged to "
               "the annotator role",
               r["status"] == "answered"
               and r["source"] == "int x;\n/* patched */\n"
               and r["usd"] == 0.5 and s["usd_by_role"]["annotator"] == 0.5
               and s["usd_by_role"]["prover"] == 0
               and open(os.path.join(tmp, "ann", "call1", "TASK.md")).read()
               == "# task\n", (r, s))
        # Under a run cap with $0.80 left, the $5 call runs capped at $0.80.
        rc = budget.RunCap(led, 1.3)
        rc.spent = 0.5
        o = annotator.Opus(os.path.join(tmp, "ann3"), rc, "cfg.json",
                           "base.c", usd=5.0)
        r = o.run("int x;\n", "# task\n")
        argv = json.load(open(os.path.join(tmp, "ann3", "call1",
                                           "argv.json")))
        cap = argv[argv.index("--max-budget-usd") + 1]
        expect("Opus.run under --max-usd: the call's cap is what the run "
               "has left ($0.80), not refused",
               r["status"] == "answered" and cap == "0.8"
               and r["budget"]["usd"] == 0.8, (cap, r.get("budget")))
        # Fake gets the config as Opus does: the spec header it names
        # (a regression test: Fake had no cfg_path, PR #235 review)
        cfg = os.path.join(tmp, "b1a_cfg.json")
        json.dump({"spec_header": "bench/b1a/spec/sglib_dl_list_spec.h"},
                  open(cfg, "w"))
        fk = annotator.Fake(os.path.join(tmp, "fake"), [None], cfg)
        r = fk.run("int x;\n", "# task\n")
        hdr = open(os.path.join(tmp, "fake", "call1",
                                "sglib_dl_list_spec.h")).read()
        expect("Fake.run: answered, with the config's spec header",
               r["status"] == "answered" and hdr == open(os.path.join(
                   annotator.ARIADNE, "bench", "b1a", "spec",
                   "sglib_dl_list_spec.h")).read(), r)
        fk = annotator.Fake(os.path.join(tmp, "fake2"), [None])
        r = fk.run("int x;\n", "# task\n")
        expect("Fake.run without a config: the whole template",
               open(os.path.join(tmp, "fake2", "call1",
                                 "sglib_dl_list_spec.h")).read()
               == open(annotator.SPEC_H).read(), r)
        o = annotator.Opus(os.path.join(tmp, "ann2"), led, "cfg.json",
                           "base.c", usd=1e6)
        r = o.run("int x;\n", "# task\n")
        expect("Opus.run: refused when the call's cap would pass the "
               "weekly cap, nothing run",
               r["status"] == "refused" and r["source"] is None
               and not os.path.exists(os.path.join(tmp, "ann2")), r)
    finally:
        os.environ["PATH"] = old


def harness(tmp, name, patches, *extra):
    lst = fake_patches.write(os.path.join(tmp, name + "_patches"), patches)
    run = os.path.join(ARIADNE, "runs", f"test-annotator-{name}-"
                       f"{os.getpid()}")
    cmd = [sys.executable, os.path.join(HERE, "harness.py"), B1,
           "--config", os.path.join(HERE, "b1_frozen.json"),
           "--functions", "sglib_dllist_get_first", "--tiers", "",
           "--annotator", "fake:" + lst, "--run-dir", run,
           "--ledger", os.path.join(tmp, "ledger.json")] + list(extra)
    p = subprocess.run(cmd, capture_output=True, text=True)
    open(os.path.join(tmp, name + ".out"), "w").write(p.stdout + p.stderr)
    rep = json.load(open(os.path.join(run, "report.json")))
    return run, rep


def e2e(tmp):
    keep = []
    # a. a good patch
    # (the first call is stopped by the fence: one fence retry)
    run, r = harness(tmp, "good", ["FENCED", "good_full"],
                     "--annotator-retries", "0")
    keep.append(run)
    ref = r.get("refinement", [{}])
    calls = ref[0].get("calls", [])
    open_goals = sorted(g["goal"] for g in r["goals"]
                        if g["discharger"] == "open")
    coq5 = sorted(f"typed_lemma_{n}" for n in fake_patches.SMT_LEMMAS_DROP)
    expect("good patch: accepted, WP reran, get_first's goals all proved, "
           "only the Coq lemmas open",
           len(calls) == 2 and calls[1].get("verdict") == "accepted"
           and r["steps"]["3_wp"].get("runs") == 2
           and open_goals == coq5
           and r["guardrails"]["frozen_spec"]["ok"]
           and r["guardrails"]["lint_ghost"]["ok"],
           (calls, open_goals, r["steps"]["3_wp"]))
    expect("good patch: patch saved in the run directory",
           os.path.exists(os.path.join(run, "patch1.c")))
    t2 = open(os.path.join(run, "annotator", "call2", "TASK.md")).read()
    expect("fence retry: a call stopped by the fence is retried once "
           "(beyond --annotator-retries), the refused command named",
           calls[0].get("verdict") == "no change after a refused command"
           and "stopped by the fence" in t2 and "sed -i x SOURCE.c" in t2,
           (calls, t2[:1500]))
    run, r = harness(tmp, "fenced", ["FENCED", "FENCED", "good_full"],
                     "--annotator-retries", "0", "--no-rac")
    keep.append(run)
    calls = r.get("refinement", [{}])[0].get("calls", [])
    expect("fence retry: only once; then the stall ends refinement",
           len(calls) == 2 and r["steps"]["3_wp"].get("runs", 1) == 1
           and r["verdict"] == "failed", calls)
    # b. four bad patches, each rejected and sent back with the reason
    run, r = harness(tmp, "bad", ["frozen_edit", "new_logic", "ghost_loop",
                                  "false_inv"], "--annotator-retries", "3")
    keep.append(run)
    calls = r.get("refinement", [{}])[0].get("calls", [])
    v = [(c.get("verdict"), {k for k, ok in c.get("guardrails", {}).items()
                             if not ok}) for c in calls]
    expect("bad patches: frozen contract edit, new predicate, ghost loop "
           "rejected by the guardrails; false invariant by step 0",
           len(v) == 4
           and v[0] == ("rejected by the guardrails",
                        {"frozen_spec", "overlay"})
           and v[1][0] == "rejected by the guardrails"
           and {"lint_acsl", "frozen_spec"} <= v[1][1]
           and v[2] == ("rejected by the guardrails",
                        {"lint_ghost", "overlay"})
           and v[3][0] == "rejected by the runtime checks", v)
    tasks = sorted(os.listdir(os.path.join(run, "annotator")))
    t2 = open(os.path.join(run, "annotator", "call2", "TASK.md")).read()
    t4 = open(os.path.join(run, "annotator", "call4", "TASK.md")).read()
    expect("bad patches: each rejection reaches the next call",
           len(tasks) == 4 and "frozen_spec: REJECTED" in t2
           and "runtime checking" not in t2 and "Frama-C did not run" in t2
           and "lint_ghost: REJECTED" in t4, (tasks, t2[-800:]))
    wp_runs = r["steps"]["3_wp"].get("runs", 1)
    src = open(os.path.join(run, "bench", "b1_frozen.c")).read()
    expect("bad patches: WP ran once; the copy is the frozen-only source; "
           "step 0 still passes; verdict failed",
           wp_runs == 1 and src == open(os.path.join(B1, "b1_frozen.c"))
           .read() and r["steps"]["0_rac"]["ok"] is True
           and r["verdict"] == "failed"
           and r["refinement_iterations"] == 1, (wp_runs, r["steps"]))
    # c. a stall loop
    run, r = harness(tmp, "stall", ["weak1", "weak2", "weak3", "weak4"],
                     "--max-iterations", "3", "--no-rac")
    keep.append(run)
    expect("stall loop: three patches accepted, then the iteration cap",
           r.get("cap_hit") == "max_iterations"
           and r["refinement_iterations"] == 3
           and r["steps"]["3_wp"].get("runs") == 4
           and r["verdict"] == "failed", (r.get("cap_hit"),
                                          r.get("refinement_iterations")))
    hist = open(os.path.join(run, "annotator", "call3", "TASK.md")).read()
    expect("stall loop: the history of earlier iterations reaches the "
           "annotator", "iteration 2: your patch was accepted" in hist,
           hist[-600:])
    if not fails:
        for d in keep:
            shutil.rmtree(d, ignore_errors=True)


def main():
    tmp = tempfile.mkdtemp(prefix="test_annotator_")
    try:
        unit(tmp)
        if "--quick" not in sys.argv:
            e2e(tmp)
    finally:
        if fails:
            print(f"(outputs kept in {tmp})")
        else:
            shutil.rmtree(tmp)
    print(f"{'PASS' if not fails else 'FAIL'}: {len(fails)} failed")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
