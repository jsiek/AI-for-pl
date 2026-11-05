"""Offline tests of the tier chain (tiers.py), with fake tiers, a fake
coqc and a fake `claude` executable: no model calls, no image.

  chain: tier 1 proves -> tier 2 never runs; tier 1 fails -> tier 2;
  a proof coqc rejects, or one with a forbidden command, does not count
  and the next tier runs; a budget refusal ends the chain; the time cap
  stops it.
  Tier2: the claude command's restrictions; a run of the fake claude is
  charged its reported cost, its proof found through the call log; a
  timed-out run is charged its cap; the ledger refuses past the cap.

    python3 test_tiers.py
"""
import json
import os
import shutil
import stat
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import budget  # noqa: E402
import tiers  # noqa: E402

ARIADNE = tiers.ARIADNE
GOAL = os.path.join(ARIADNE, "bench", "b1", "session", "interactive",
                    "lemma_mem_cons.v")
fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800].replace("\n", "\n    "))


class Fake:
    def __init__(self, tier, status, script=None, tokens=0, usd=0.0):
        self.tier, self.ran = tier, 0
        self.r = {"tier": tier, "model": f"fake{tier}", "status": status,
                  "script": script, "seconds": 1.0, "tokens": tokens,
                  "usd": usd, "charged": tier >= 2}

    def run(self, path, goal):
        self.ran += 1
        return dict(self.r)


def coqc(prefix, script, suffix, timeout):
    """Accepts exactly the script `good.`"""
    return script.strip() == "good.", "fake coqc"


tmp = tempfile.mkdtemp(dir=os.path.join(ARIADNE, "runs"), prefix="test_")
try:
    path = os.path.join(tmp, "lemma_mem_cons.v")
    shutil.copy(GOAL, path)
    original = open(path).read()

    def fresh():
        open(path, "w").write(original)

    a, b = Fake(1, "proved", "good.", 900), Fake(2, "proved", "good.")
    r = tiers.chain(path, "g", [a, b], coqc)
    expect("tier 1 proves: tier 2 never runs",
           r["status"] == "proved" and r["tier"] == 1 and b.ran == 0
           and "\ngood.\nQed." in open(path).read(), r)
    expect("tier 1 tokens reported, not charged",
           r["tokens"] == 900 and r["charged_tokens"] == 0 and r["usd"] == 0,
           r)
    fresh()
    a, b = Fake(1, "open"), Fake(2, "proved", "good.", 40000, 0.2)
    r = tiers.chain(path, "g", [a, b], coqc)
    expect("tier 1 fails: tier 2 proves",
           r["status"] == "proved" and r["tier"] == 2 and a.ran == b.ran == 1
           and r["usd"] == 0.2 and r["charged_tokens"] == 40000, r)
    fresh()
    a, b = Fake(1, "proved", "bad."), Fake(2, "proved", "good.")
    r = tiers.chain(path, "g", [a, b], coqc)
    expect("a proof coqc rejects does not count",
           r["tier"] == 2 and r["attempts"][0]["status"] == "rejected"
           and r["attempts"][0]["coqc_confirmed"] is False, r)
    fresh()
    a = Fake(1, "proved", "intros. admit.")
    r = tiers.chain(path, "g", [a], lambda *x: (True, ""))
    expect("a forbidden command is rejected even if coqc accepts",
           r["status"] == "open" and "forbidden" in
           r["attempts"][0]["confirm_error"]
           and open(path).read() == original, r)
    a, b = Fake(1, "open"), Fake(2, "refused")
    r = tiers.chain(path, "g", [a, b, Fake(3, "proved", "good.")], coqc)
    expect("a budget refusal ends the chain",
           r["status"] == "refused" and len(r["attempts"]) == 2, r)
    a = Fake(1, "proved", "good.")
    r = tiers.chain(path, "g", [a], coqc, stop=lambda: True)
    expect("the time cap stops the chain",
           a.ran == 0 and r.get("stopped") == "total time cap", r)

    # ---- Tier2 with a fake claude --------------------------------------
    cmd = tiers.sonnet_command("/w", calls=30)
    flags = " ".join(cmd[2:])
    expect("claude command: subscription model, JSON, restricted tools",
           cmd[:2] == ["claude", "-p"] and "--model claude-sonnet-5-5" in
           flags and "--output-format json" in flags
           and "--tools Bash,Read,Write,Edit" in flags
           and "--permission-mode dontAsk" in flags
           and "--restricted" in flags and "--safe-mode" in flags
           and "Bash(git *)" in cmd and "--max-budget-usd" in cmd, flags)
    allowed = cmd[cmd.index("--allowedTools") + 1:
                  cmd.index("--disallowedTools")]
    expect("claude command: Bash only prover_cli on GOAL.v/SCRIPT.v, "
           "files only in the work dir",
           all(x.startswith((f"Bash(python3 {tiers.CLI} ",
                             "Read(//w/", "Write(//w/", "Edit(//w/"))
               for x in allowed) and len(allowed) == 7, allowed)
    bindir = os.path.join(tmp, "bin")
    os.makedirs(bindir)
    fake = os.path.join(bindir, "claude")
    with open(fake, "w") as f:
        f.write(f"""#!{sys.executable}
import json, os, sys, time
if os.environ.get("FAKE_CLAUDE") == "slow":
    time.sleep(30)
open("SCRIPT.v", "w").write("good.")
with open(os.environ["PROVER_CLI_LOG"], "a") as f:
    f.write(json.dumps({{"cmd": "check", "ok": True}}) + "\\n")
print(json.dumps({{"subtype": "success", "num_turns": 4,
    "total_cost_usd": 0.25, "result": "SOLVED",
    "permission_denials": [],
    "modelUsage": {{"claude-sonnet-5-5": {{"inputTokens": 5,
        "outputTokens": 1000, "cacheReadInputTokens": 30000,
        "cacheCreationInputTokens": 6000, "costUSD": 0.25}}}}}}))
""")
    os.chmod(fake, os.stat(fake).st_mode | stat.S_IEXEC)
    os.environ["PATH"] = bindir + os.pathsep + os.environ["PATH"]
    L = budget.Ledger(os.path.join(tmp, "budget.json"))
    t2 = tiers.Tier2(os.path.join(tmp, "tier2"), L, usd=1.0)
    fresh()
    r = tiers.chain(path, "mem_cons", [Fake(1, "open"), t2], coqc)
    a = r["attempts"][-1]
    expect("Tier2 (fake claude): proved, confirmed, charged its cost",
           r["status"] == "proved" and r["tier"] == 2
           and a["coqc_confirmed"] and a["usd"] == 0.25
           and a["tokens"] == 37005 and L.summary()["usd"] == 0.25
           and a["cli_calls"]["counts"] == {"check": 1}, a)
    work = os.path.join(tmp, "tier2", "mem_cons")
    g = open(os.path.join(work, "GOAL.v")).read()
    expect("Tier2's goal copy has the statement and no proof",
           "Theorem wp_goal" in g
           and not tiers.split_goal(g)[1].strip(), g[-200:])
    os.environ["FAKE_CLAUDE"] = "slow"
    t2 = tiers.Tier2(os.path.join(tmp, "tier2b"), L, usd=1.0, seconds=2)
    r = t2.run(path, "mem_cons")
    expect("a timed-out claude run is charged its cap",
           r["estimated"] and r["usd"] == 1.0 and r.get("end") == "timeout"
           and L.summary()["usd"] == 1.25, r)
    del os.environ["FAKE_CLAUDE"]
    # Placeholder 2%/USD: $1.25 = 2.5%; a $9 cap would make 20.5%.
    t2 = tiers.Tier2(os.path.join(tmp, "tier2c"), L, usd=9.0)
    r = t2.run(path, "mem_cons")
    expect("the ledger refuses a call past the cap, claude never runs",
           r["status"] == "refused" and not os.path.exists(
               os.path.join(tmp, "tier2c")) and L.summary()["usd"] == 1.25,
           r)
    expect("hidden paths cover other runs, results and benchmark sessions",
           os.path.join(ARIADNE, "runs") in tiers.hidden_paths()
           and os.path.join(ARIADNE, "bench", "b1", "session")
           in tiers.hidden_paths(), tiers.hidden_paths())
finally:
    shutil.rmtree(tmp)
print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
