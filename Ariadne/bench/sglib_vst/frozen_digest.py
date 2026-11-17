"""The frozen digest of the stage-1 public spec (owner's approval,
2026-11-17): the first 16 hex digits of SHA-256 over SPEC.md (without
its "Frozen digest:" line, which states the digest) and spec_dllist.v,
each preceded by its name, as B1's frozen digest
(../../harness/guardrails.py) is a 16-digit SHA-256 prefix.

    python3 -I frozen_digest.py          (from this directory)

prints the digest.  `check.sh` compares it with the recorded value and
with the one SPEC.md states; a change to either file changes it.
"""
import hashlib
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
FILES = ["SPEC.md", "spec_dllist.v"]
MARK = "Frozen digest: `"


def text(name):
    t = open(os.path.join(HERE, name), encoding="utf-8").read()
    if name == "SPEC.md":
        t = "\n".join(l for l in t.split("\n") if not l.startswith(MARK))
    return t


def digest():
    h = hashlib.sha256()
    for name in FILES:
        h.update(name.encode() + b"\0" + text(name).encode() + b"\0")
    return h.hexdigest()[:16]


def stated():
    """The digest SPEC.md states on its "Frozen digest:" line."""
    for l in open(os.path.join(HERE, "SPEC.md"), encoding="utf-8"):
        if l.startswith(MARK):
            return l[len(MARK):].split("`")[0]
    return None


if __name__ == "__main__":
    if sys.argv[1:] == ["--stated"]:
        print(stated())
    else:
        print(digest())
