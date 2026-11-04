"""VST smoke test: drive a VST proof through Petanque (pet).

Runs from Ariadne/vst/smoke (mounted at /work in the container), after
check.sh step 1 has compiled good.v and bad.v:

    python3 -I pet_check.py

1. Opens `body_use_cell` of verif_good.v and runs its proof sentence by
   sentence, printing the number of goals after each step; `Qed` must
   finish the proof.
2. Opens `body_use_after_free` of verif_bad.v, replays the steps up to
   the line marked BAD, and checks that `forward` there is rejected
   with VST's "not obvious how to move forward" error.  This is what a
   prover agent would see.
"""

import json
import subprocess
import sys

GOOD = [
    "start_function.",
    "forward_call (t_cell, gv).",
    "Intros p.",
    "forward_if (PROP () LOCAL (temp _p p; gvars gv) SEP (mem_mgr gv;"
    " malloc_token Ews t_cell p; data_at_ Ews t_cell p)).",
    "-", "if_tac; entailer!.",
    "-", "forward.", "Exists 0.", "entailer!.",
    "-", "if_tac.",
    "+", "subst p.", "contradiction.",
    "+", "forward.", "entailer!.",
    "-", "forward.", "forward.", "forward.",
    "forward_call (t_cell, p, gv).",
    "{", "assert_PROP (isptr p) by entailer!.",
    "rewrite if_false by (intro; subst; contradiction).", "cancel.", "}",
    "forward.", "Exists 1.", "entailer!.",
]

BAD_PREFIX = [
    "start_function.",
    "malloc_nonnull gv.",
    "forward.", "forward.",
    "forward_call (t_cell, p, gv).",
    "{", "assert_PROP (isptr p) by entailer!.",
    "rewrite if_false by (intro; subst; contradiction).", "cancel.", "}",
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


def run_all(pet, uri, thm, tactics, show):
    st = pet.call("petanque/start", {"uri": uri, "thm": thm})["st"]
    for tac in tactics:
        st = pet.call("petanque/run", {"st": st, "tac": tac})["st"]
        if show:
            goals = pet.call("petanque/goals", {"st": st})
            print(f"{len(goals['goals']):2d} goal(s) after: {tac[:60]}")
    return st


def main():
    pet = Pet()
    pet.call("petanque/setWorkspace",
             {"debug": False, "root": "file:///work"})
    st = run_all(pet, "file:///work/verif_good.v", "body_use_cell",
                 GOOD, show=True)
    done = pet.call("petanque/run", {"st": st, "tac": "Qed."})
    finished = bool(done.get("proof_finished"))
    print("body_use_cell proof finished:", finished)

    st = run_all(pet, "file:///work/verif_bad.v", "body_use_after_free",
                 BAD_PREFIX, show=False)
    try:
        pet.call("petanque/run", {"st": st, "tac": "forward."})
        refused = False
        print("BAD: forward after free was accepted")
    except RuntimeError as err:
        msg = json.dumps(err.args[0])
        refused = "not obvious how to move forward" in msg
        print("forward after free refused:", refused)
    pet.proc.stdin.close()
    pet.proc.wait()
    return 0 if finished and refused else 1


if __name__ == "__main__":
    sys.exit(main())
