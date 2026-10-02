#!/usr/bin/env python3
"""Hygiene check over exactly the modules All.agda imports.

Run from GTNF/agda after `agda --dependency-graph=_build/deps.dot All.agda`.
Fails if any reachable local module contains a postulate, a hole or an
unsafe pragma.  Skeleton proofs with holes may exist in the tree as long
as All.agda does not import them (they are checked by `make wip`).
"""
import os
import re
import sys

BAD = re.compile(r"postulate|\{!|TERMINATING|NON_TERMINATING|"
                 r"NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK")
dot = open("_build/deps.dot", encoding="utf-8").read()
mods = set(re.findall(r'label="([^"]+)"', dot))
failed = False
checked = 0
for m in sorted(mods):
    f = m.replace(".", "/") + ".agda"
    if not os.path.exists(f):
        continue                      # a library module
    checked += 1
    for i, line in enumerate(open(f, encoding="utf-8"), 1):
        code = line.split("--")[0]
        if BAD.search(code):
            print(f"{f}:{i}: {line.rstrip()}")
            failed = True
if failed:
    print("postulate-check: FAILED (see matches above)")
    sys.exit(1)
print(f"postulate-check: OK ({checked} modules reachable from All.agda; "
      "no postulates or holes)")
