"""Minimal client for Pétanque (coq-lsp's `pet`, JSON-RPC over stdio),
run in the M0 image.

    with Petanque(workdir) as pet:
        st = pet.start("goal.v", "wp_goal")      # state after the statement
        r = pet.run(st["st"], "intros a l a1.")  # new state, or PetanqueError
        pet.goals(r["st"])

`workdir` must be under Ariadne/ (mounted at /ariadne in the image); a
_CoqProject there gives coq-lsp the Why3 load path.  Messages use LSP
framing (Content-Length): with `--http_headers=no` pet answers only at
end of input.
"""
import json
import os
import select
import subprocess
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
COQPROJECT = "-R /home/rocq/.opam/4.14.2/lib/why3/coq Why3\n"


class PetanqueTimeout(Exception):
    """No answer in time; the process is then unusable (close it)."""


class PetanqueError(Exception):
    def __init__(self, error):
        self.error = error
        super().__init__(error.get("message", str(error)))


class Petanque:
    count = 0

    def __init__(self, workdir):
        self.workdir = os.path.abspath(workdir)
        self.inner = "/ariadne/" + os.path.relpath(self.workdir, ARIADNE)
        with open(os.path.join(self.workdir, "_CoqProject"), "w") as f:
            f.write(COQPROJECT)
        # As ../env/run.sh, plus --init (pet as PID 1 would ignore
        # SIGTERM) and a name, so close() can always stop the container.
        Petanque.count += 1
        self.name = f"ariadne-pet-{os.getpid()}-{Petanque.count}"
        image = os.environ.get("ARIADNE_IMAGE", "ariadne-m0:dev")
        self.proc = subprocess.Popen(
            ["docker", "run", "--rm", "-i", "--init", "--name", self.name,
             "--user", f"{os.getuid()}:{os.getgid()}",
             "-e", "HOME=/home/rocq", "-v", f"{ARIADNE}:/ariadne",
             "-w", self.inner, image, "pet", f"--root={self.inner}"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, bufsize=0)
        self.fd = self.proc.stdout.fileno()
        self.buf = b""
        self.next_id = 0

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()

    def close(self):
        # pet does not exit at end of input (it loops on "Blank input
        # data"), so stop its container by name.
        subprocess.run(["docker", "stop", "-t", "2", self.name],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            self.proc.wait(timeout=20)
        except subprocess.TimeoutExpired:
            self.proc.kill()

    def _fill(self, deadline):
        left = deadline - time.time()
        if left <= 0 or not select.select([self.fd], [], [], left)[0]:
            raise PetanqueTimeout()
        chunk = os.read(self.fd, 65536)
        if not chunk:
            raise PetanqueError({"message": "pet exited"})
        self.buf += chunk

    def _recv(self, deadline):
        # Tactics that run shell commands write to pet's stdout too:
        # `hammer` looks for its ATPs with `sh`, which prints "sh: 1:
        # z3_tptp: not found" before the next message.  Skip any such
        # text before a header.
        while True:
            k = self.buf.find(b"Content-Length:")
            if k >= 0 and b"\r\n\r\n" in self.buf[k:]:
                self.buf = self.buf[k:]
                break
            self._fill(deadline)
        head, _, _ = self.buf.partition(b"\r\n\r\n")
        length = None
        for line in head.split(b"\r\n"):
            k, _, v = line.decode().partition(":")
            if k.strip().lower() == "content-length":
                length = int(v)
        start = len(head) + 4
        while len(self.buf) < start + length:
            self._fill(deadline)
        body = self.buf[start:start + length]
        self.buf = self.buf[start + length:]
        return json.loads(body)

    def call(self, method, params, timeout=60):
        deadline = time.time() + timeout
        self.next_id += 1
        rid = self.next_id
        body = json.dumps({"jsonrpc": "2.0", "id": rid, "method": method,
                           "params": params}).encode()
        self.proc.stdin.write(b"Content-Length: %d\r\n\r\n" % len(body)
                              + body)
        self.proc.stdin.flush()
        while True:
            msg = self._recv(deadline)
            if msg.get("id") != rid:
                continue  # notifications (progress, logs)
            if "error" in msg:
                raise PetanqueError(msg["error"])
            return msg["result"]

    def start(self, name, thm, timeout=300):
        uri = f"file://{self.inner}/{name}"
        return self.call("petanque/start", {"uri": uri, "thm": thm},
                         timeout)

    def run(self, st, tac, timeout=60):
        return self.call("petanque/run", {"st": st, "tac": tac}, timeout)

    def goals(self, st, timeout=60):
        return self.call("petanque/goals", {"st": st}, timeout)
