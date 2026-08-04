#!/usr/bin/env python3
"""Simple exhaustive endpoint-canonical MLB for small GTSF type models.

This is the slow reference algorithm from
`EndpointCanonicalMLBSimpleDesign.md`.  It enumerates supported `forall`
matching routes directly instead of solving support profiles.
"""

from __future__ import annotations

from functools import lru_cache
from itertools import product

from mlb_counterexample_search import (
    Ctx,
    STAR,
    Ty,
    derivs,
    forall_ctx,
    id_ctx,
    nu_ctx,
    occurs,
    pp_ty,
)


DERIV_CAP = 80


def pred(n: int) -> int:
    return 0 if n == 0 else n - 1


def type_ctx_bound(ty: Ty) -> int:
    """Return the least type-context size that makes `ty` well formed."""

    if ty.tag == "var":
        return ty.args[0] + 1
    if ty.tag in ("base", "star"):
        return 0
    if ty.tag == "arr":
        return max(type_ctx_bound(ty.args[0]), type_ctx_bound(ty.args[1]))
    if ty.tag == "all":
        return pred(type_ctx_bound(ty.args[0]))
    raise ValueError(ty)


def endpoint_ctx(left: Ty, right: Ty) -> int:
    return max(type_ctx_bound(left), type_ctx_bound(right))


def dedupe(types: list[Ty]) -> list[Ty]:
    seen: set[Ty] = set()
    out: list[Ty] = []
    for ty in types:
        if ty not in seen:
            seen.add(ty)
            out.append(ty)
    return out


def below(ctx: Ctx, dl: int, dr: int, src: Ty, tgt: Ty) -> bool:
    return bool(derivs(ctx, dl, dr, src, tgt, DERIV_CAP))


def strictly_below(depth: int, src: Ty, tgt: Ty) -> bool:
    ctx = id_ctx(depth)
    return below(ctx, depth, depth, src, tgt) and not below(
        ctx, depth, depth, tgt, src
    )


def prune_strictly_below(depth: int, candidates: list[Ty]) -> list[Ty]:
    out: list[Ty] = []
    for candidate in candidates:
        if any(
            candidate != other and strictly_below(depth, candidate, other)
            for other in candidates
        ):
            continue
        out.append(candidate)
    return out


def variable_candidates(
    ctx_l: Ctx,
    ctx_r: Ctx,
    dc: int,
    dl: int,
    dr: int,
    left: Ty,
    right: Ty,
) -> list[Ty]:
    out: list[Ty] = []
    for index in range(dc):
        candidate = Ty.var(index)
        if below(ctx_l, dc, dl, candidate, left) and below(
            ctx_r, dc, dr, candidate, right
        ):
            out.append(candidate)
    return out


@lru_cache(maxsize=None)
def enum_candidates(
    ctx_l: Ctx,
    ctx_r: Ctx,
    dc: int,
    dl: int,
    dr: int,
    left: Ty,
    right: Ty,
) -> tuple[Ty, ...]:
    """Enumerate supported lower-bound candidates in route order."""

    out: list[Ty] = []

    if left.tag == "all" and right.tag == "all":
        for body in enum_candidates(
            forall_ctx(ctx_l),
            forall_ctx(ctx_r),
            dc + 1,
            dl + 1,
            dr + 1,
            left.args[0],
            right.args[0],
        ):
            out.append(Ty.all(body))

    if left.tag == "all":
        for body in enum_candidates(
            forall_ctx(ctx_l),
            nu_ctx(ctx_r),
            dc + 1,
            dl + 1,
            dr,
            left.args[0],
            right,
        ):
            if occurs(0, body):
                out.append(Ty.all(body))

    if right.tag == "all":
        for body in enum_candidates(
            nu_ctx(ctx_l),
            forall_ctx(ctx_r),
            dc + 1,
            dl,
            dr + 1,
            left,
            right.args[0],
        ):
            if occurs(0, body):
                out.append(Ty.all(body))

    if left.tag == "all" or right.tag == "all":
        return tuple(dedupe(out))

    if left.tag == "star" and right.tag == "star":
        out.append(STAR)

    elif left.tag == "base" and right.tag == "base":
        if left.args[0] == right.args[0]:
            out.append(left)

    elif left.tag == "base" and right.tag == "star":
        out.append(left)

    elif left.tag == "star" and right.tag == "base":
        out.append(right)

    elif left.tag == "arr" and right.tag == "arr":
        lefts = enum_candidates(ctx_l, ctx_r, dc, dl, dr,
                                left.args[0], right.args[0])
        rights = enum_candidates(ctx_l, ctx_r, dc, dl, dr,
                                 left.args[1], right.args[1])
        out.extend(Ty.arr(domain, codomain)
                   for domain, codomain in product(lefts, rights))

    elif left.tag == "arr" and right.tag == "star":
        lefts = enum_candidates(ctx_l, ctx_r, dc, dl, dr,
                                left.args[0], STAR)
        rights = enum_candidates(ctx_l, ctx_r, dc, dl, dr,
                                 left.args[1], STAR)
        out.extend(Ty.arr(domain, codomain)
                   for domain, codomain in product(lefts, rights))

    elif left.tag == "star" and right.tag == "arr":
        lefts = enum_candidates(ctx_l, ctx_r, dc, dl, dr,
                                STAR, right.args[0])
        rights = enum_candidates(ctx_l, ctx_r, dc, dl, dr,
                                 STAR, right.args[1])
        out.extend(Ty.arr(domain, codomain)
                   for domain, codomain in product(lefts, rights))

    elif (
        (left.tag == "var" and right.tag == "var")
        or (left.tag == "var" and right.tag == "star")
        or (left.tag == "star" and right.tag == "var")
    ):
        out.extend(variable_candidates(ctx_l, ctx_r, dc, dl, dr, left, right))

    return tuple(dedupe(out))


def raw_endpoint_mlbs(left: Ty, right: Ty, depth: int | None = None) -> list[Ty]:
    """Return all supported candidates before maximal pruning."""

    if depth is None:
        depth = endpoint_ctx(left, right)
    ctx = id_ctx(depth)
    return list(enum_candidates(ctx, ctx, depth, depth, depth, left, right))


def all_endpoint_mlbs(left: Ty, right: Ty, depth: int | None = None) -> list[Ty]:
    """Return all maximal supported candidates in first-route order."""

    if depth is None:
        depth = endpoint_ctx(left, right)
    candidates = raw_endpoint_mlbs(left, right, depth)
    return prune_strictly_below(depth, candidates)


def simple_endpoint_mlb(left: Ty, right: Ty, depth: int | None = None) -> Ty | None:
    """Return the first maximal supported endpoint MLB candidate, if any."""

    candidates = all_endpoint_mlbs(left, right, depth)
    if not candidates:
        return None
    return candidates[0]


def endpoint_mlb(left: Ty, right: Ty) -> Ty | None:
    """Compatibility alias for tests that expect an endpoint MLB function."""

    return simple_endpoint_mlb(left, right)


def main() -> int:
    examples = [
        (Ty.all(Ty.arr(Ty.var(0), STAR)), Ty.all(Ty.arr(STAR, Ty.var(0)))),
        (Ty.all(Ty.arr(STAR, Ty.var(0))), Ty.all(Ty.arr(Ty.var(0), STAR))),
        (Ty.all(STAR), Ty.all(STAR)),
        (Ty.all(Ty.arr(Ty.var(0), Ty.var(0))), STAR),
    ]
    for left, right in examples:
        result = simple_endpoint_mlb(left, right)
        result_text = pp_ty(result) if result else "nothing"
        all_results = ", ".join(pp_ty(ty) for ty in all_endpoint_mlbs(left, right))
        print(f"{pp_ty(left)} /\\ {pp_ty(right)} = {result_text}")
        print(f"  maximal candidates: {all_results or 'none'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
