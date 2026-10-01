#!/usr/bin/env python3
"""Can a compiled program produce a LEFT-ONLY unbind of a shared name?
(GTNF/design.md §12.5, question 3.)

GTNF's `inst_X` puts `[−X^α]` around a value cast by `gen X. p`.  The
unbind is left-only exactly when, at a name X that both sides bind
(`∀X.B ⊑ ∀X.B′` by `∀⊑∀`), the more precise evidence handles the
target's binder X by `gen` and the less precise evidence does not.

For evidence `c : A ∼ ∀X.B`, the node that HANDLES the target binder is
found by descending through `check` (`？_`, whose child keeps the
target) and `inst` (whose child's target is the shifted `∀X.B`, still
with X on top).  It is `gen`, `all` (∀ᶜ), or a bottom rule.

The search ranges over ALL declarative evidence on both sides (source
typing accepts any derivation), not only the canonical one.

    python3 left_only_unbind.py --max-size 6 --depths 0 1
"""

from __future__ import annotations

import argparse
import time
from functools import cache

from model import (
    All, Star, enumerate_evidence, identity_consistency_env,
    identity_imp_env, imprecision_evidence, pretty_type, types_upto,
)


def handler(evidence) -> str:
    node = evidence
    while node.ctor in ("check", "inst"):
        node = node.children[0]
    return node.ctor


def search(depth: int, bound: int) -> dict:
    env = identity_consistency_env(depth)
    imp = identity_imp_env(depth)
    types = types_upto(depth, bound)
    alls = [t for t in types if isinstance(t, All)]

    @cache
    def handlers(left, right) -> frozenset:
        return frozenset(handler(e) for e in
                         enumerate_evidence(env, left, right))

    # imprecision pairs among sources, and ∀⊑∀ pairs among targets
    src_pairs = [(a, a2) for a in types for a2 in types
                 if imprecision_evidence(imp, a, a2) is not None]
    tgt_pairs = []
    for b in alls:
        for b2 in alls:
            ev = imprecision_evidence(imp, b, b2)
            if ev is not None and ev.ctor == "all":
                tgt_pairs.append((b, b2))

    checked = 0
    left_gen = 0
    hits = []
    for (b, b2) in tgt_pairs:
        for (a, a2) in src_pairs:
            hl = handlers(a, b)
            if "gen" not in hl:
                continue
            hr = handlers(a2, b2)
            if not hr:
                continue          # less precise side not consistent
            checked += 1
            left_gen += 1
            bad = hr - {"gen"}
            if bad:
                hits.append((a, b, a2, b2, sorted(hl), sorted(hr)))
    return dict(depth=depth, types=len(types), src_pairs=len(src_pairs),
                tgt_pairs=len(tgt_pairs), squares_with_left_gen=left_gen,
                hits=hits)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-size", type=int, default=5)
    parser.add_argument("--depths", type=int, nargs="*", default=[0, 1])
    parser.add_argument("--show", type=int, default=10)
    args = parser.parse_args()
    for depth in args.depths:
        start = time.time()
        r = search(depth, args.max_size)
        print(f"depth={depth} size≤{args.max_size}: types={r['types']} "
              f"source ⊑-pairs={r['src_pairs']} target ∀⊑∀-pairs="
              f"{r['tgt_pairs']} squares with a left gen="
              f"{r['squares_with_left_gen']} hits={len(r['hits'])} "
              f"({time.time() - start:.1f}s)")
        for (a, b, a2, b2, hl, hr) in r["hits"][:args.show]:
            print(f"  L {pretty_type(a, depth)} ∼ {pretty_type(b, depth)}"
                  f" {hl}   R {pretty_type(a2, depth)} ∼ "
                  f"{pretty_type(b2, depth)} {hr}")


if __name__ == "__main__":
    main()
