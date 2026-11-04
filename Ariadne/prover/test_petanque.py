"""Offline test of the Pétanque backend of reallms_coq.py (no model
calls) on a WP goal file whose proof is known.
Usage: python3 test_petanque.py <goal.v>"""
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from reallms_coq import Worker, sentences  # noqa: E402

fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800].replace("\n", "\n    "))


expect("sentences", sentences(
    "intros a l. (* c. d *) - split. { lia. }\n  + exact \"x. y\". apply f.g.")
    == ["intros a l.", "(* c. d *) - split.", "{ lia.",
        "}\n  + exact \"x. y\".", "apply f.g."],
    sentences("intros a l. (* c. d *) - split. { lia. }\n  + exact \"x. y\". apply f.g."))

w = Worker(sys.argv[1], timeout=60, fh=None, backend="petanque")
try:
    t = time.time()
    r = w.run_tactics("intros a l a1.")
    expect("first step", r["ok"] and r["state"] == 1 and "a1 : addr" in
           r["goals"], r)
    print(f"     (session start + first step: {time.time() - t:.1f} s)")
    r = w.run_tactics("split. - intros H. rewrite nth_cons.")
    expect("failing sentence reported",
           not r["ok"] and r["failed_sentence"] == "rewrite nth_cons."
           and "H : a1 = a" in r["goals_before_failing_sentence"], r)
    expect("failure leaves no new state", len(w.states) == 2, w.states)
    r = w.run_tactics("revert a1.", state=0)
    expect("state 0 has no a1 yet", not r["ok"], r)
    r = w.run_tactics("revert a1.", state=1)
    expect("state 1 has a1", r["ok"] and "\n  a1 : addr" not in r["goals"], r)
    # after a bullet's branch, the unfocused goal is shown in full
    r = w.run_tactics("split; intro H. - exfalso. admit_me.", state=1)
    r = w.run_tactics("split; intro H. - left; reflexivity.", state=1)
    expect("finished-branch run: wrong tactic fails", not r["ok"], r)
    r = w.run_tactics("split; intro H. - assert (Z : True) by trivial. "
                      "clear Z. destruct H as [E | M]. + exists 0%Z. "
                      "rewrite E. split; [split; [apply nth_zero | lia] |]. "
                      "rewrite length_cons. pose proof (length_pos l). lia. "
                      "+ destruct M as (i & (Hn & Hi) & Hl). "
                      "exists (i + 1)%Z. "
                      "destruct (nth_cons (i + 1)%Z a l) as [_ Hc]; [lia |]. "
                      "rewrite Hc by lia. "
                      "replace (i + 1 - 1)%Z with i by lia. "
                      "rewrite length_cons. split; [split |]; "
                      "[exact Hn | lia | lia].", state=1)
    expect("unfocused goal shown with its hypotheses",
           r["ok"] and "next bullet" in r["goals"]
           and "H : P_mem a1 (a :: l)" in r["goals"], r)
    out = w.coq_query("Check nth_cons.")
    expect("coq_query via Pétanque", "nth_cons" in out and "forall" in out,
           out)
    # the known proof, from state 1, sentence by sentence
    known = w.script.split("intros a l a1.", 1)[1]
    t = time.time()
    r = w.run_tactics(known, state=1)
    expect("known proof finishes and coqc accepts it",
           r["ok"] and r.get("proof_finished")
           and r["coqc"].startswith("accepted") and w.last_ok, r)
    print(f"     ({len(sentences(known))} sentences + coqc: "
          f"{time.time() - t:.1f} s)")
    # a timeout restarts the session; old states are replayed
    w.timeout = 3
    r = w.run_tactics("do 2000000000 idtac.", state=1)
    expect("timeout reported", not r["ok"] and "timed out" in r["error"], r)
    w.timeout = 60
    r = w.run_tactics("split.", state=1)
    expect("state 1 replayed after restart", r["ok"] and
           w.pet_restarts == 1, r)
finally:
    w._pet_close()
left = subprocess.run(["docker", "ps", "-q", "--filter",
                       f"name=ariadne-pet-{os.getpid()}-"],
                      capture_output=True, text=True).stdout.strip()
expect("no container left", not left, left)
sys.exit(1 if fails else 0)
