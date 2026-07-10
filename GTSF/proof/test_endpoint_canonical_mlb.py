#!/usr/bin/env python3
"""Regression tests for `endpoint_canonical_mlb.py`."""

from __future__ import annotations

import argparse
import random
import sys
import unittest
from functools import lru_cache
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from endpoint_canonical_mlb import endpoint_mlb
from mlb_counterexample_search import (
    BOOL,
    NAT,
    STAR,
    Ty,
    derivs,
    find_related_pair,
    id_ctx,
    make_pool,
    pp_ty,
    random_ctx,
    seeded_types,
    well_formed,
)


DERIV_CAP = 80
PROPERTY_SEED = 20260710
PROPERTY_DEPTHS = 3
PROPERTY_POOL_CAP = 80
PROPERTY_POOL_DRAWS = 1500


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


@lru_cache(maxsize=1)
def property_pools() -> tuple[tuple[Ty, ...], ...]:
    rng = random.Random(PROPERTY_SEED)
    args = argparse.Namespace(
        max_arrow=2,
        max_forall=3,
        max_size=8,
        pool_cap=PROPERTY_POOL_CAP,
        pool_draws=PROPERTY_POOL_DRAWS,
    )
    return tuple(
        tuple(make_pool(args, rng, depth))
        for depth in range(PROPERTY_DEPTHS)
    )


class EndpointCanonicalMlbTests(unittest.TestCase):
    def assert_mlb(self, left: Ty, right: Ty, expected: Ty) -> None:
        actual = endpoint_mlb(left, right)
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
        actual = endpoint_mlb(left, right)
        self.assertIsNone(
            actual,
            f"\nleft   = {pp_ty(left)}"
            f"\nright  = {pp_ty(right)}"
            f"\nactual = {pp_ty(actual) if actual else 'nothing'}",
        )

    def test_bad_glb_pair_uses_body_occurrence_order(self) -> None:
        left = all_(arr(var(0), STAR))
        right = all_(arr(STAR, var(0)))
        expected = all_(all_(arr(var(1), var(0))))
        self.assert_mlb(left, right, expected)

    def test_bad_glb_pair_reversed_occurrence_order(self) -> None:
        left = all_(arr(STAR, var(0)))
        right = all_(arr(var(0), STAR))
        expected = all_(all_(arr(var(1), var(0))))
        self.assert_mlb(left, right, expected)

    def test_repeated_one_sided_use_against_star_reuses_binder(self) -> None:
        left = all_(arr(var(0), var(0)))
        right = STAR
        expected = all_(arr(var(0), var(0)))
        self.assert_mlb(left, right, expected)
        self.assert_mlb(right, left, expected)
        self.assert_mlb(all_(var(0)), STAR, all_(var(0)))
        self.assert_mlb(STAR, all_(var(0)), all_(var(0)))
        used_var_base = all_(arr(var(0), NAT))
        self.assert_mlb(used_var_base, STAR, used_var_base)
        self.assert_mlb(STAR, used_var_base, used_var_base)
        used_var_star = all_(arr(var(0), STAR))
        self.assert_mlb(used_var_star, STAR, used_var_star)
        self.assert_mlb(STAR, used_var_star, used_var_star)

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

    def test_repeated_one_sided_use_does_not_cross_unused_target(self) -> None:
        left = all_(arr(var(0), var(0)))
        right = all_(arr(STAR, STAR))
        self.assert_no_mlb(left, right)
        self.assert_no_mlb(right, left)

    def test_incompatible_shared_and_one_sided_use_fails(self) -> None:
        left = all_(arr(var(0), var(0)))
        right = all_(arr(var(0), STAR))
        self.assert_no_mlb(left, right)
        self.assert_no_mlb(right, left)

    def test_one_endpoint_binder_cannot_pair_with_two_binders(self) -> None:
        left = all_(all_(arr(var(1), var(0))))
        right = all_(arr(var(0), var(0)))
        self.assert_no_mlb(left, right)

    def test_crossing_exposure_order_fails(self) -> None:
        left = all_(all_(var(1)))
        right = all_(all_(var(0)))
        self.assert_no_mlb(left, right)

    def test_matching_two_binder_order_succeeds(self) -> None:
        left = all_(all_(arr(var(1), var(0))))
        right = all_(all_(arr(var(1), var(0))))
        expected = all_(all_(arr(var(1), var(0))))
        self.assert_mlb(left, right, expected)

    def test_base_and_star_cases(self) -> None:
        self.assert_mlb(NAT, STAR, NAT)
        self.assert_mlb(STAR, BOOL, BOOL)
        self.assert_no_mlb(NAT, BOOL)

    def test_arrow_star_cases(self) -> None:
        left = arr(NAT, BOOL)
        self.assert_mlb(left, STAR, left)
        self.assert_mlb(STAR, left, left)

    def test_nested_forall_blocks(self) -> None:
        left = arr(all_(var(0)), all_(STAR))
        right = arr(all_(var(0)), all_(STAR))
        expected = arr(all_(var(0)), all_(STAR))
        self.assert_mlb(left, right, expected)

    def test_nested_forall_can_capture_outer_profiles(self) -> None:
        left = all_(arr(all_(arr(var(1), var(0))), var(0)))
        right = all_(arr(all_(arr(var(1), var(0))), var(0)))
        expected = all_(arr(all_(arr(var(1), var(0))), var(0)))
        self.assert_mlb(left, right, expected)

    def test_first_use_does_not_override_endpoint_exposure(self) -> None:
        right = all_(all_(arr(var(0), var(1))))
        self.assert_mlb(STAR, right, right)
        self.assert_mlb(right, STAR, right)

    def test_positive_results_are_common_lowers_on_seeded_pool(self) -> None:
        pool = sorted(seeded_types(0), key=pp_ty)
        checked = 0
        for left in pool:
            for right in pool:
                result = endpoint_mlb(left, right)
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
                result = endpoint_mlb(left, right)
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
                if endpoint_mlb(left, right) is not None:
                    continue
                checked += 1
                for witness in pool:
                    self.assertFalse(
                        is_lower(witness, left, right),
                        f"\nleft    = {pp_ty(left)}"
                        f"\nright   = {pp_ty(right)}"
                        f"\nwitness = {pp_ty(witness)}",
                    )
        self.assertGreater(checked, 100)

    def test_generated_pool_positive_results_are_common_lowers(self) -> None:
        rng = random.Random(1729)
        args = argparse.Namespace(
            max_arrow=2,
            max_forall=3,
            max_size=8,
            pool_cap=120,
            pool_draws=2500,
        )
        pool = make_pool(args, rng, 0)
        checked = 0
        for left in pool:
            for right in pool:
                result = endpoint_mlb(left, right)
                if result is None:
                    continue
                checked += 1
                self.assertTrue(
                    is_lower(result, left, right),
                    f"\nleft   = {pp_ty(left)}"
                    f"\nright  = {pp_ty(right)}"
                    f"\nresult = {pp_ty(result)}",
                )
        self.assertGreater(checked, 300)

    def test_property_common_lower_soundness_on_generated_pools(self) -> None:
        checked = 0
        for depth, pool in enumerate(property_pools()):
            ctx = id_ctx(depth)
            for left in pool:
                for right in pool:
                    result = endpoint_mlb(left, right)
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
        self.assertGreater(checked, 400)

    def test_property_bounded_maximality_on_generated_pools(self) -> None:
        comparisons = 0
        for depth, pool_tuple in enumerate(property_pools()):
            pool = list(pool_tuple)
            ctx = id_ctx(depth)
            for left in pool:
                for right in pool:
                    result = endpoint_mlb(left, right)
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
        self.assertGreater(comparisons, 900)

    def test_property_failure_completeness_on_generated_pools(self) -> None:
        checked = 0
        for depth, pool in enumerate(property_pools()):
            ctx = id_ctx(depth)
            for left in pool:
                for right in pool:
                    if endpoint_mlb(left, right) is not None:
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
        self.assertGreater(checked, 1_000_000)

    def test_property_contextual_coherence_on_generated_samples(self) -> None:
        rng = random.Random(PROPERTY_SEED + 1)
        pools = property_pools()
        checked = 0
        for _ in range(20_000):
            left_depth = rng.randrange(PROPERTY_DEPTHS)
            right_depth = rng.randrange(PROPERTY_DEPTHS)
            ctx = random_ctx(rng, left_depth, right_depth)
            left_pool = pools[left_depth]
            right_pool = pools[right_depth]

            left_pair = find_related_pair(
                rng, ctx, left_depth, right_depth, left_pool, right_pool,
                50, DERIV_CAP,
            )
            right_pair = find_related_pair(
                rng, ctx, left_depth, right_depth, left_pool, right_pool,
                50, DERIV_CAP,
            )
            if left_pair is None or right_pair is None:
                continue

            left, left_prime = left_pair
            right, right_prime = right_pair
            result = endpoint_mlb(left, right)
            result_prime = endpoint_mlb(left_prime, right_prime)
            if result is None or result_prime is None:
                continue

            checked += 1
            self.assertTrue(well_formed(left_depth, result), pp_ty(result))
            self.assertTrue(
                well_formed(right_depth, result_prime),
                pp_ty(result_prime),
            )
            self.assertTrue(
                derivs(ctx, left_depth, right_depth, result, result_prime,
                       DERIV_CAP),
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
        self.assertGreater(checked, 200)


if __name__ == "__main__":
    unittest.main()
