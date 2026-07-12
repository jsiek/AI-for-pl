#!/usr/bin/env python3
"""Regression and bounded property tests for the simple endpoint MLB."""

from __future__ import annotations

import argparse
import random
import sys
import unittest
from functools import lru_cache
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from endpoint_canonical_mlb_simple import (
    all_endpoint_mlbs,
    endpoint_ctx,
    raw_endpoint_mlbs,
    simple_endpoint_mlb,
    type_ctx_bound,
)
from mlb_counterexample_search import (
    BOOL,
    NAT,
    STAR,
    Ty,
    derivs,
    find_related_pair,
    id_ctx,
    make_pool,
    occurs,
    pp_ty,
    random_ctx,
    rename,
    seeded_types,
    well_formed,
)


DERIV_CAP = 80
PROPERTY_SEED = 20260710
PROPERTY_DEPTHS = 4
PROPERTY_POOL_CAP = 110
PROPERTY_POOL_DRAWS = 6000


def arr(left: Ty, right: Ty) -> Ty:
    return Ty.arr(left, right)


def all_(body: Ty) -> Ty:
    return Ty.all(body)


def var(index: int) -> Ty:
    return Ty.var(index)


def is_lower(lower: Ty, left: Ty, right: Ty, depth: int = 0) -> bool:
    ctx = id_ctx(depth)
    return bool(derivs(ctx, depth, depth, lower, left, DERIV_CAP)) and bool(
        derivs(ctx, depth, depth, lower, right, DERIV_CAP)
    )


def swap01(index: int) -> int:
    if index == 0:
        return 1
    if index == 1:
        return 0
    return index


def forall_permutation_steps(ty: Ty) -> set[Ty]:
    steps: set[Ty] = set()
    if ty.tag == "all":
        body = ty.args[0]
        if body.tag == "all":
            steps.add(all_(all_(rename(body.args[0], swap01))))
        steps.update(all_(step) for step in forall_permutation_steps(body))
    elif ty.tag == "arr":
        domain, codomain = ty.args
        steps.update(
            arr(step, codomain) for step in forall_permutation_steps(domain)
        )
        steps.update(
            arr(domain, step) for step in forall_permutation_steps(codomain)
        )
    return steps


@lru_cache(maxsize=None)
def forall_permutations(ty: Ty) -> frozenset[Ty]:
    seen = {ty}
    pending = [ty]
    while pending:
        current = pending.pop()
        for step in forall_permutation_steps(current):
            if step not in seen:
                seen.add(step)
                pending.append(step)
    return frozenset(seen)


def quotient_below(
    ctx: tuple,
    left_depth: int,
    right_depth: int,
    src: Ty,
    tgt: Ty,
) -> bool:
    return any(
        derivs(ctx, left_depth, right_depth, src_prime, tgt_prime, DERIV_CAP)
        for src_prime in forall_permutations(src)
        for tgt_prime in forall_permutations(tgt)
    )


def binder_free(ty: Ty) -> bool:
    if ty.tag == "all":
        return False
    if ty.tag == "arr":
        return binder_free(ty.args[0]) and binder_free(ty.args[1])
    return True


def recursive_structure_success(src: Ty, tgt: Ty) -> bool:
    """Mirror `recursive-structure?` from the Agda factor proof."""

    if binder_free(src) and tgt.tag != "all":
        return True
    if src.tag == "arr" and tgt.tag == "star":
        return recursive_structure_success(
            src.args[0], STAR
        ) and recursive_structure_success(src.args[1], STAR)
    if src.tag == "arr" and tgt.tag == "arr":
        return recursive_structure_success(
            src.args[0], tgt.args[0]
        ) and recursive_structure_success(src.args[1], tgt.args[1])
    if (
        src.tag == "all"
        and tgt.tag == "all"
        and recursive_structure_success(src.args[0], tgt.args[0])
    ):
        return True
    if src.tag == "all":
        return occurs(0, src.args[0]) and recursive_structure_success(
            src.args[0], tgt
        )
    return False


def all_well_formed_contexts(left_depth: int, right_depth: int) -> list[tuple]:
    assumptions = [
        ("star", left, None)
        for left in range(left_depth)
    ] + [
        ("var", left, right)
        for left in range(left_depth)
        for right in range(right_depth)
    ]
    return [
        tuple(subset)
        for size in range(len(assumptions) + 1)
        for subset in combinations(assumptions, size)
    ]


@lru_cache(maxsize=1)
def property_pools() -> tuple[tuple[Ty, ...], ...]:
    rng = random.Random(PROPERTY_SEED)
    args = argparse.Namespace(
        max_arrow=5,
        max_forall=5,
        max_size=14,
        pool_cap=PROPERTY_POOL_CAP,
        pool_draws=PROPERTY_POOL_DRAWS,
    )
    return tuple(
        tuple(make_pool(args, rng, depth))
        for depth in range(PROPERTY_DEPTHS)
    )


class SimpleEndpointMlbTests(unittest.TestCase):
    def assert_mlb(self, left: Ty, right: Ty, expected: Ty) -> None:
        actual = simple_endpoint_mlb(left, right)
        self.assertEqual(
            actual,
            expected,
            f"\nleft     = {pp_ty(left)}"
            f"\nright    = {pp_ty(right)}"
            f"\nexpected = {pp_ty(expected)}"
            f"\nactual   = {pp_ty(actual) if actual else 'nothing'}",
        )
        self.assertTrue(
            is_lower(expected, left, right),
            f"expected result is not a lower bound: {pp_ty(expected)}",
        )

    def assert_no_mlb(self, left: Ty, right: Ty) -> None:
        actual = simple_endpoint_mlb(left, right)
        self.assertIsNone(
            actual,
            f"\nleft   = {pp_ty(left)}"
            f"\nright  = {pp_ty(right)}"
            f"\nactual = {pp_ty(actual) if actual else 'nothing'}",
        )

    def test_type_context_bound(self) -> None:
        self.assertEqual(type_ctx_bound(STAR), 0)
        self.assertEqual(type_ctx_bound(var(0)), 1)
        self.assertEqual(type_ctx_bound(var(2)), 3)
        self.assertEqual(type_ctx_bound(all_(var(0))), 0)
        self.assertEqual(type_ctx_bound(all_(var(1))), 1)
        self.assertEqual(endpoint_ctx(all_(var(1)), var(2)), 3)

    def test_bad_glb_pair_enumerates_both_maximal_routes(self) -> None:
        left = all_(arr(var(0), STAR))
        right = all_(arr(STAR, var(0)))
        expected = [
            all_(all_(arr(var(1), var(0)))),
            all_(all_(arr(var(0), var(1)))),
        ]
        self.assertEqual(all_endpoint_mlbs(left, right), expected)
        self.assert_mlb(left, right, expected[0])

    def test_bad_glb_pair_reversed_first_route(self) -> None:
        left = all_(arr(STAR, var(0)))
        right = all_(arr(var(0), STAR))
        expected = [
            all_(all_(arr(var(0), var(1)))),
            all_(all_(arr(var(1), var(0)))),
        ]
        self.assertEqual(all_endpoint_mlbs(left, right), expected)
        self.assert_mlb(left, right, expected[0])

    def test_bad_glb_routes_are_quotient_related(self) -> None:
        xy = all_(all_(arr(var(1), var(0))))
        yx = all_(all_(arr(var(0), var(1))))
        self.assertTrue(quotient_below(id_ctx(0), 0, 0, xy, yx))
        self.assertTrue(quotient_below(id_ctx(0), 0, 0, yx, xy))

    def test_recursive_structure_uses_source_forall_fallback(self) -> None:
        source = all_(all_(var(1)))
        target = all_(STAR)
        self.assertTrue(recursive_structure_success(source, target))
        self.assertTrue(derivs(id_ctx(0), 0, 0, source, target, DERIV_CAP))

    def test_repeated_one_sided_use_against_star_reuses_binder(self) -> None:
        left = all_(arr(var(0), var(0)))
        self.assert_mlb(left, STAR, left)
        self.assert_mlb(STAR, left, left)
        self.assert_mlb(all_(var(0)), STAR, all_(var(0)))
        self.assert_mlb(STAR, all_(var(0)), all_(var(0)))

    def test_unused_one_sided_binder_fails(self) -> None:
        self.assert_no_mlb(all_(STAR), STAR)
        self.assert_no_mlb(STAR, all_(STAR))
        self.assert_no_mlb(all_(NAT), STAR)
        self.assert_no_mlb(STAR, all_(NAT))
        self.assert_no_mlb(all_(arr(NAT, BOOL)), STAR)
        self.assert_no_mlb(STAR, all_(arr(NAT, BOOL)))

    def test_unused_binders_pair_across_sides(self) -> None:
        self.assert_mlb(all_(STAR), all_(STAR), all_(STAR))
        self.assert_mlb(all_(all_(STAR)), all_(all_(STAR)), all_(all_(STAR)))

    def test_incompatible_and_crossing_cases_fail(self) -> None:
        self.assert_no_mlb(
            all_(arr(var(0), var(0))),
            all_(arr(var(0), STAR)),
        )
        self.assert_no_mlb(
            all_(all_(arr(var(1), var(0)))),
            all_(arr(var(0), var(0))),
        )
        self.assert_no_mlb(all_(all_(var(1))), all_(all_(var(0))))

    def test_base_arrow_and_nested_examples(self) -> None:
        self.assert_mlb(NAT, STAR, NAT)
        self.assert_mlb(STAR, BOOL, BOOL)
        self.assert_no_mlb(NAT, BOOL)
        self.assert_mlb(arr(NAT, BOOL), STAR, arr(NAT, BOOL))
        self.assert_mlb(STAR, arr(NAT, BOOL), arr(NAT, BOOL))
        nested = arr(all_(var(0)), all_(STAR))
        self.assert_mlb(nested, nested, nested)

    def test_first_route_respects_endpoint_exposure(self) -> None:
        right = all_(all_(arr(var(0), var(1))))
        self.assert_mlb(STAR, right, right)
        self.assert_mlb(right, STAR, right)

    def test_positive_results_are_common_lowers_on_seeded_pool(self) -> None:
        pool = sorted(seeded_types(0), key=pp_ty)
        checked = 0
        for left in pool:
            for right in pool:
                result = simple_endpoint_mlb(left, right)
                if result is None:
                    continue
                checked += 1
                self.assertTrue(well_formed(0, result), pp_ty(result))
                self.assertTrue(
                    is_lower(result, left, right),
                    f"\nleft   = {pp_ty(left)}"
                    f"\nright  = {pp_ty(right)}"
                    f"\nresult = {pp_ty(result)}",
                )
        self.assertGreater(checked, 20)

    def test_bounded_maximality_on_seeded_pool(self) -> None:
        pool = sorted(seeded_types(0), key=pp_ty)
        checked = 0
        for left in pool:
            for right in pool:
                result = simple_endpoint_mlb(left, right)
                if result is None:
                    continue
                checked += 1
                for witness in pool + [result]:
                    if not is_lower(witness, left, right):
                        continue
                    if not derivs(id_ctx(0), 0, 0, result, witness, DERIV_CAP):
                        continue
                    self.assertTrue(
                        derivs(id_ctx(0), 0, 0, witness, result, DERIV_CAP),
                        f"\nleft    = {pp_ty(left)}"
                        f"\nright   = {pp_ty(right)}"
                        f"\nresult  = {pp_ty(result)}"
                        f"\nwitness = {pp_ty(witness)}",
                    )
        self.assertGreater(checked, 20)

    def test_seeded_nothing_results_have_no_seeded_lower(self) -> None:
        pool = sorted(seeded_types(0), key=pp_ty)
        checked = 0
        for left in pool:
            for right in pool:
                if simple_endpoint_mlb(left, right) is not None:
                    continue
                for witness in pool:
                    checked += 1
                    self.assertFalse(
                        is_lower(witness, left, right),
                        f"\nleft    = {pp_ty(left)}"
                        f"\nright   = {pp_ty(right)}"
                        f"\nwitness = {pp_ty(witness)}",
                    )
        self.assertGreater(checked, 100)

    def test_property_common_lower_soundness_on_small_pools(self) -> None:
        checked = 0
        for depth, pool in enumerate(property_pools()):
            ctx = id_ctx(depth)
            for left in pool:
                for right in pool:
                    result = simple_endpoint_mlb(left, right, depth)
                    if result is None:
                        continue
                    checked += 1
                    self.assertTrue(well_formed(depth, result), pp_ty(result))
                    self.assertTrue(
                        derivs(ctx, depth, depth, result, left, DERIV_CAP),
                        f"\ndepth  = {depth}"
                        f"\nleft   = {pp_ty(left)}"
                        f"\nright  = {pp_ty(right)}"
                        f"\nresult = {pp_ty(result)}",
                    )
                    self.assertTrue(
                        derivs(ctx, depth, depth, result, right, DERIV_CAP),
                        f"\ndepth  = {depth}"
                        f"\nleft   = {pp_ty(left)}"
                        f"\nright  = {pp_ty(right)}"
                        f"\nresult = {pp_ty(result)}",
                    )
        self.assertGreater(checked, 100)

    def test_property_bounded_maximality_on_small_pools(self) -> None:
        comparisons = 0
        for depth, pool_tuple in enumerate(property_pools()):
            pool = list(pool_tuple)
            ctx = id_ctx(depth)
            for left in pool:
                for right in pool:
                    result = simple_endpoint_mlb(left, right, depth)
                    if result is None:
                        continue
                    for witness in pool + [result]:
                        if not derivs(ctx, depth, depth, witness, left,
                                      DERIV_CAP):
                            continue
                        if not derivs(ctx, depth, depth, witness, right,
                                      DERIV_CAP):
                            continue
                        if not derivs(ctx, depth, depth, result, witness,
                                      DERIV_CAP):
                            continue
                        comparisons += 1
                        self.assertTrue(
                            derivs(ctx, depth, depth, witness, result,
                                   DERIV_CAP),
                            f"\ndepth   = {depth}"
                            f"\nleft    = {pp_ty(left)}"
                            f"\nright   = {pp_ty(right)}"
                            f"\nresult  = {pp_ty(result)}"
                            f"\nwitness = {pp_ty(witness)}",
                        )
        self.assertGreater(comparisons, 150)

    def test_property_maxima_differ_only_by_forall_permutation(self) -> None:
        compared = 0
        for depth, pool in enumerate(property_pools()):
            for left in pool:
                for right in pool:
                    maxima = all_endpoint_mlbs(left, right, depth)
                    for first in maxima:
                        for second in maxima:
                            compared += 1
                            self.assertIn(
                                second,
                                forall_permutations(first),
                                f"\ndepth  = {depth}"
                                f"\nleft   = {pp_ty(left)}"
                                f"\nright  = {pp_ty(right)}"
                                f"\nfirst  = {pp_ty(first)}"
                                f"\nsecond = {pp_ty(second)}",
                            )
        self.assertGreater(compared, 100)

    def test_raw_polymorphic_routes_differ_only_by_permutation(self) -> None:
        atoms = [STAR, NAT, BOOL, var(0)]
        bodies = atoms + [arr(left, right)
                          for left in atoms for right in atoms]
        endpoints = [all_(body) for body in bodies]
        compared = 0
        multi_route_pairs = 0
        for left in endpoints:
            for right in endpoints:
                routes = raw_endpoint_mlbs(left, right)
                if len(routes) > 1:
                    multi_route_pairs += 1
                for first in routes:
                    for second in routes:
                        compared += 1
                        self.assertIn(
                            second,
                            forall_permutations(first),
                            f"\nleft   = {pp_ty(left)}"
                            f"\nright  = {pp_ty(right)}"
                            f"\nfirst  = {pp_ty(first)}"
                            f"\nsecond = {pp_ty(second)}",
                        )
        self.assertGreater(multi_route_pairs, 1)
        self.assertGreater(compared, 80)

    def test_property_failure_completeness_on_small_pools(self) -> None:
        checked = 0
        for depth, pool in enumerate(property_pools()):
            ctx = id_ctx(depth)
            for left in pool:
                for right in pool:
                    if simple_endpoint_mlb(left, right, depth) is not None:
                        continue
                    for witness in pool:
                        checked += 1
                        self.assertFalse(
                            derivs(ctx, depth, depth, witness, left,
                                   DERIV_CAP)
                            and derivs(ctx, depth, depth, witness, right,
                                      DERIV_CAP),
                            f"\ndepth   = {depth}"
                            f"\nleft    = {pp_ty(left)}"
                            f"\nright   = {pp_ty(right)}"
                            f"\nwitness = {pp_ty(witness)}",
                        )
        self.assertGreater(checked, 10_000)

    def test_property_quotient_coherence_on_small_samples(self) -> None:
        rng = random.Random(PROPERTY_SEED + 1)
        pools = property_pools()
        checked = 0
        for _ in range(60_000):
            left_depth = rng.randrange(PROPERTY_DEPTHS)
            right_depth = rng.randrange(PROPERTY_DEPTHS)
            ctx = random_ctx(rng, left_depth, right_depth)
            left_pool = pools[left_depth]
            right_pool = pools[right_depth]

            left_pair = find_related_pair(
                rng, ctx, left_depth, right_depth, left_pool, right_pool,
                70, DERIV_CAP,
            )
            right_pair = find_related_pair(
                rng, ctx, left_depth, right_depth, left_pool, right_pool,
                70, DERIV_CAP,
            )
            if left_pair is None or right_pair is None:
                continue

            left, left_prime = left_pair
            right, right_prime = right_pair
            result = simple_endpoint_mlb(left, right, left_depth)
            result_prime = simple_endpoint_mlb(
                left_prime, right_prime, right_depth
            )
            if result is None or result_prime is None:
                continue

            checked += 1
            self.assertTrue(
                quotient_below(
                    ctx, left_depth, right_depth, result, result_prime
                ),
                f"\nleft depth  = {left_depth}"
                f"\nright depth = {right_depth}"
                f"\ncontext     = {ctx}"
                f"\nA           = {pp_ty(left)}"
                f"\nA'          = {pp_ty(left_prime)}"
                f"\nB           = {pp_ty(right)}"
                f"\nB'          = {pp_ty(right_prime)}"
                f"\nC           = {pp_ty(result)}"
                f"\nC'          = {pp_ty(result_prime)}",
            )
        self.assertGreater(checked, 30)

    def test_exhaustive_contextual_quotient_coherence_depth_two(self) -> None:
        checked = 0
        factored = 0
        for left_depth in range(3):
            left_pool = tuple(seeded_types(left_depth))
            for right_depth in range(3):
                right_pool = tuple(seeded_types(right_depth))
                for ctx in all_well_formed_contexts(
                    left_depth, right_depth
                ):
                    related = [
                        (left, right)
                        for left in left_pool
                        for right in right_pool
                        if derivs(
                            ctx, left_depth, right_depth,
                            left, right, DERIV_CAP
                        )
                    ]
                    for left, left_prime in related:
                        for right, right_prime in related:
                            result = simple_endpoint_mlb(
                                left, right, left_depth
                            )
                            result_prime = simple_endpoint_mlb(
                                left_prime, right_prime, right_depth
                            )
                            if result is None or result_prime is None:
                                continue
                            checked += 1
                            message = (
                                f"\nleft depth  = {left_depth}"
                                f"\nright depth = {right_depth}"
                                f"\ncontext     = {ctx}"
                                f"\nA           = {pp_ty(left)}"
                                f"\nA'          = {pp_ty(left_prime)}"
                                f"\nB           = {pp_ty(right)}"
                                f"\nB'          = {pp_ty(right_prime)}"
                                f"\nC           = {pp_ty(result)}"
                                f"\nC'          = {pp_ty(result_prime)}"
                            )
                            self.assertTrue(
                                quotient_below(
                                    ctx, left_depth, right_depth,
                                    result, result_prime
                                ),
                                message,
                            )
                            target_raw = raw_endpoint_mlbs(
                                left_prime, right_prime, right_depth
                            )
                            self.assertTrue(
                                recursive_structure_success(
                                    result, result_prime
                                ),
                                "recursive factor structure failed" + message,
                            )
                            self.assertTrue(
                                any(
                                    derivs(
                                        ctx, left_depth, right_depth,
                                        result, candidate, DERIV_CAP
                                    )
                                    for candidate in target_raw
                                ),
                                "raw factorization failed" + message,
                            )
                            factored += 1
        self.assertGreater(checked, 100)
        self.assertEqual(factored, checked)

    def test_paired_source_forall_implies_paired_target_route(self) -> None:
        checked = 0
        for left_depth in range(3):
            left_pool = tuple(seeded_types(left_depth))
            for right_depth in range(3):
                right_pool = tuple(seeded_types(right_depth))
                for ctx in all_well_formed_contexts(
                    left_depth, right_depth
                ):
                    for source in left_pool:
                        if source.tag != "all":
                            continue
                        for left in right_pool:
                            if left.tag != "all":
                                continue
                            left_derivs = derivs(
                                ctx, left_depth, right_depth,
                                source, left, DERIV_CAP
                            )
                            if not any(
                                proof.tag == "forall"
                                for proof in left_derivs
                            ):
                                continue
                            for right in right_pool:
                                if right.tag != "all":
                                    continue
                                right_derivs = derivs(
                                    ctx, left_depth, right_depth,
                                    source, right, DERIV_CAP
                                )
                                if not any(
                                    proof.tag == "forall"
                                    for proof in right_derivs
                                ):
                                    continue
                                outer_routes = raw_endpoint_mlbs(
                                    left, right, right_depth
                                )
                                if not outer_routes:
                                    continue
                                checked += 1
                                self.assertTrue(
                                    raw_endpoint_mlbs(
                                        left.args[0], right.args[0],
                                        right_depth + 1
                                    ),
                                    "paired source exposure had no paired "
                                    "target route"
                                    f"\nleft depth  = {left_depth}"
                                    f"\nright depth = {right_depth}"
                                    f"\ncontext     = {ctx}"
                                    f"\nsource      = {pp_ty(source)}"
                                    f"\nleft        = {pp_ty(left)}"
                                    f"\nright       = {pp_ty(right)}"
                                    f"\nouter routes = "
                                    f"{[pp_ty(ty) for ty in outer_routes]}",
                                )
        self.assertGreater(checked, 10)


if __name__ == "__main__":
    unittest.main()
