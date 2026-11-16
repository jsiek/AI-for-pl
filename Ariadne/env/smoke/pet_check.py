"""M0 smoke test: drive a WP-generated Coq goal through Petanque (pet).

Runs from Ariadne/env/smoke (mounted at /work in the container):

    python3 pet_check.py

Starts `pet` in the toolchain image, opens the goal `wp_goal` of
pet/lemma_sum_nonneg.v, runs the proof tactic by tactic, and prints the
number of open goals after each step.
"""

import json
import subprocess
import sys

TACTICS = [
    "intros i.",
    "assert (Hpos : forall n, (0 <= n)%Z -> (0 <= L_sum n)%Z).",
    "{ apply natlike_ind.",
    "- destruct (L_sum_def 0%Z) as [H0 _]. rewrite (H0 (Z.le_refl 0%Z)). lia.",
    "- intros x Hx IH. destruct (L_sum_def (Z.succ x)) as [_ H1]."
    " rewrite H1 by lia. replace ((-1%Z)%Z + Z.succ x)%Z with x by lia. lia. }",
    "destruct (Z_le_gt_dec i 0%Z) as [H|H].",
    "- destruct (L_sum_def i) as [H0 _]. rewrite (H0 H). lia.",
    "- apply Hpos. lia.",
]


class Pet:
    def __init__(self):
        self.proc = subprocess.Popen(
            ["../run.sh", "pet"], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE)
        self.next_id = 0

    def send(self, msg):
        body = json.dumps(msg).encode()
        self.proc.stdin.write(
            b"Content-Length: %d\r\n\r\n" % len(body) + body)
        self.proc.stdin.flush()

    def recv(self):
        length = None
        while True:
            line = self.proc.stdout.readline()
            if not line:
                raise EOFError("pet exited")
            line = line.strip()
            if not line:
                break
            name, _, value = line.partition(b":")
            if name.lower() == b"content-length":
                length = int(value)
        return json.loads(self.proc.stdout.read(length))

    def call(self, method, params):
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": self.next_id,
                   "method": method, "params": params})
        while True:
            msg = self.recv()
            if msg.get("id") == self.next_id:
                if "error" in msg:
                    raise RuntimeError(msg["error"])
                return msg["result"]


def main():
    pet = Pet()
    pet.call("petanque/setWorkspace",
             {"debug": False, "root": "file:///work/pet"})
    start = pet.call("petanque/start",
                     {"uri": "file:///work/pet/lemma_sum_nonneg.v",
                      "thm": "wp_goal"})
    st = start["st"]
    for tac in TACTICS:
        res = pet.call("petanque/run", {"st": st, "tac": tac})
        st = res["st"]
        goals = pet.call("petanque/goals", {"st": st})
        print(f"{len(goals['goals']):2d} goal(s) after: {tac[:60]}")
    done = pet.call("petanque/run", {"st": st, "tac": "Qed."})
    print("proof finished:", done.get("proof_finished"))
    pet.proc.stdin.close()
    pet.proc.wait()
    return 0 if done.get("proof_finished") else 1


if __name__ == "__main__":
    sys.exit(main())
