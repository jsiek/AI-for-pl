#!/usr/bin/env python3
"""Finite random search for small MLB coherence counterexamples.

This script models the GTSF `ImprecisionWf` clauses and the `mlb-type` type
constructor closely enough to search small closed types.  It is a bounded
counterexample finder, not part of the trusted Agda development.
"""

from __future__ import annotations

import argparse
import random
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from typing import Callable, Sequence


@dataclass(frozen=True, order=True)
class Ty:
    tag: str
    args: tuple

    @staticmethod
    def var(index: int) -> "Ty":
        return Ty("var", (index,))

    @staticmethod
    def base(name: str) -> "Ty":
        return Ty("base", (name,))

    @staticmethod
    def star() -> "Ty":
        return Ty("star", ())

    @staticmethod
    def arr(left: "Ty", right: "Ty") -> "Ty":
        return Ty("arr", (left, right))

    @staticmethod
    def all(body: "Ty") -> "Ty":
        return Ty("all", (body,))


STAR = Ty.star()
NAT = Ty.base("N")
BOOL = Ty.base("B")


def pp_ty(ty: Ty) -> str:
    if ty.tag == "var":
        return f"X{ty.args[0]}"
    if ty.tag == "base":
        return ty.args[0]
    if ty.tag == "star":
        return "*"
    if ty.tag == "arr":
        left, right = ty.args
        left_s = pp_ty(left)
        if left.tag == "arr":
            left_s = f"({left_s})"
        return f"{left_s} -> {pp_ty(right)}"
    if ty.tag == "all":
        return f"forall {pp_ty(ty.args[0])}"
    raise ValueError(ty)


def occurs(index: int, ty: Ty) -> bool:
    if ty.tag == "var":
        return index == ty.args[0]
    if ty.tag in ("base", "star"):
        return False
    if ty.tag == "arr":
        return occurs(index, ty.args[0]) or occurs(index, ty.args[1])
    if ty.tag == "all":
        return occurs(index + 1, ty.args[0])
    raise ValueError(ty)


def rename(ty: Ty, rho: Callable[[int], int]) -> Ty:
    if ty.tag == "var":
        return Ty.var(rho(ty.args[0]))
    if ty.tag in ("base", "star"):
        return ty
    if ty.tag == "arr":
        return Ty.arr(rename(ty.args[0], rho), rename(ty.args[1], rho))
    if ty.tag == "all":
        def ext(index: int) -> int:
            if index == 0:
                return 0
            return rho(index - 1) + 1

        return Ty.all(rename(ty.args[0], ext))
    raise ValueError(ty)


def open0(ty: Ty) -> Ty:
    def single_rename(index: int) -> int:
        if index == 0:
            return 0
        return index - 1

    return rename(ty, single_rename)


def close_neither(ty: Ty) -> Ty:
    if occurs(0, ty):
        return Ty.all(ty)
    return open0(ty)


def well_formed(depth: int, ty: Ty) -> bool:
    if ty.tag == "var":
        return ty.args[0] < depth
    if ty.tag in ("base", "star"):
        return True
    if ty.tag == "arr":
        return well_formed(depth, ty.args[0]) and well_formed(depth, ty.args[1])
    if ty.tag == "all":
        return well_formed(depth + 1, ty.args[0])
    raise ValueError(ty)


Assm = tuple[str, int, int | None]
Ctx = tuple[Assm, ...]


def id_ctx(depth: int) -> Ctx:
    return tuple(("var", index, index) for index in range(depth))


def lift_both(ctx: Ctx) -> Ctx:
    lifted: list[Assm] = []
    for tag, left, right in ctx:
        if tag == "star":
            lifted.append(("star", left + 1, None))
        else:
            assert right is not None
            lifted.append(("var", left + 1, right + 1))
    return tuple(lifted)


def lift_left(ctx: Ctx) -> Ctx:
    lifted: list[Assm] = []
    for tag, left, right in ctx:
        if tag == "star":
            lifted.append(("star", left + 1, None))
        else:
            lifted.append(("var", left + 1, right))
    return tuple(lifted)


def forall_ctx(ctx: Ctx) -> Ctx:
    return (("var", 0, 0),) + lift_both(ctx)


def nu_ctx(ctx: Ctx) -> Ctx:
    return (("star", 0, None),) + lift_left(ctx)


def has_var(ctx: Ctx, left: int, right: int) -> bool:
    return ("var", left, right) in ctx


def has_star(ctx: Ctx, left: int) -> bool:
    return ("star", left, None) in ctx


@dataclass(frozen=True)
class Deriv:
    tag: str
    src: Ty
    tgt: Ty
    subs: tuple["Deriv", ...] = ()


def combine(
    tag: str,
    src: Ty,
    tgt: Ty,
    lefts: Sequence[Deriv],
    rights: Sequence[Deriv],
    cap: int,
) -> list[Deriv]:
    out: list[Deriv] = []
    for left, right in product(lefts, rights):
        out.append(Deriv(tag, src, tgt, (left, right)))
        if len(out) >= cap:
            break
    return out


@lru_cache(maxsize=None)
def derivs(ctx: Ctx, dl: int, dr: int, src: Ty, tgt: Ty, cap: int) -> tuple[Deriv, ...]:
    out: list[Deriv] = []

    def add(deriv: Deriv) -> None:
        if len(out) < cap:
            out.append(deriv)

    if src.tag == "star" and tgt.tag == "star":
        add(Deriv("id_star", src, tgt))

    if src.tag == "var" and tgt.tag == "var":
        x = src.args[0]
        y = tgt.args[0]
        if x < dl and y < dr and has_var(ctx, x, y):
            add(Deriv("id_var", src, tgt))

    if src.tag == "base" and tgt.tag == "base" and src.args[0] == tgt.args[0]:
        add(Deriv("id_base", src, tgt))

    if src.tag == "arr" and tgt.tag == "arr":
        lefts = derivs(ctx, dl, dr, src.args[0], tgt.args[0], cap)
        rights = derivs(ctx, dl, dr, src.args[1], tgt.args[1], cap)
        for deriv in combine("arr", src, tgt, lefts, rights, cap - len(out)):
            add(deriv)

    if src.tag == "all" and tgt.tag == "all":
        for sub in derivs(forall_ctx(ctx), dl + 1, dr + 1,
                         src.args[0], tgt.args[0], cap - len(out)):
            add(Deriv("forall", src, tgt, (sub,)))

    if src.tag == "base" and tgt.tag == "star":
        add(Deriv("tag_base", src, tgt))

    if src.tag == "arr" and tgt.tag == "star":
        lefts = derivs(ctx, dl, dr, src.args[0], STAR, cap)
        rights = derivs(ctx, dl, dr, src.args[1], STAR, cap)
        for deriv in combine("tag_arr", src, tgt, lefts, rights,
                             cap - len(out)):
            add(deriv)

    if src.tag == "var" and tgt.tag == "star":
        x = src.args[0]
        if x < dl and has_star(ctx, x):
            add(Deriv("tag_var", src, tgt))

    if src.tag == "all" and occurs(0, src.args[0]):
        for sub in derivs(nu_ctx(ctx), dl + 1, dr, src.args[0], tgt,
                         cap - len(out)):
            add(Deriv("nu", src, tgt, (sub,)))

    return tuple(out[:cap])


def mlb_type(left: Deriv, right: Deriv) -> Ty:
    if left.tag == "id_star" and right.tag == "id_star":
        return STAR
    if left.tag == "id_var" and right.tag == "id_var":
        return left.src
    if left.tag == "id_base" and right.tag == "id_base":
        return left.src
    if left.tag == "id_base" and right.tag == "tag_base":
        return left.src
    if left.tag == "arr" and right.tag == "arr":
        return Ty.arr(mlb_type(left.subs[0], right.subs[0]),
                      mlb_type(left.subs[1], right.subs[1]))
    if left.tag == "arr" and right.tag == "tag_arr":
        return Ty.arr(mlb_type(left.subs[0], right.subs[0]),
                      mlb_type(left.subs[1], right.subs[1]))
    if left.tag == "forall" and right.tag == "forall":
        return Ty.all(mlb_type(left.subs[0], right.subs[0]))
    if left.tag == "forall" and right.tag == "nu":
        return Ty.all(mlb_type(left.subs[0], right.subs[0]))
    if left.tag == "tag_base" and right.tag == "id_base":
        return right.src
    if left.tag == "tag_base" and right.tag == "tag_base":
        return STAR
    if left.tag == "tag_arr" and right.tag == "arr":
        return Ty.arr(mlb_type(left.subs[0], right.subs[0]),
                      mlb_type(left.subs[1], right.subs[1]))
    if left.tag == "tag_arr" and right.tag == "tag_arr":
        return STAR
    if left.tag == "tag_var" and right.tag == "id_var":
        return left.src
    if left.tag == "tag_var" and right.tag == "tag_var":
        return STAR
    if left.tag == "nu" and right.tag == "forall":
        return Ty.all(mlb_type(left.subs[0], right.subs[0]))
    if left.tag == "nu" and right.tag == "nu":
        return close_neither(mlb_type(left.subs[0], right.subs[0]))
    if left.tag == "id_var" and right.tag == "tag_var":
        return left.src
    raise ValueError(
        f"unmodeled mlb clause: {left.tag} : {pp_ty(left.src)} <= "
        f"{pp_ty(left.tgt)}, {right.tag} : {pp_ty(right.src)} <= "
        f"{pp_ty(right.tgt)}"
    )


def random_type(rng: random.Random, depth: int, size: int,
                forall_left: int, arrow_left: int) -> Ty:
    atom_choices = [STAR, NAT, BOOL]
    if depth > 0:
        atom_choices.extend(Ty.var(index) for index in range(depth))

    constructors = ["atom"]
    if size > 1 and forall_left > 0:
        constructors.extend(["forall", "forall"])
    if size > 2 and arrow_left > 0:
        constructors.extend(["arr", "arr"])

    choice = rng.choice(constructors)
    if choice == "atom":
        return rng.choice(atom_choices)
    if choice == "forall":
        return Ty.all(random_type(rng, depth + 1, size - 1,
                                  forall_left - 1, arrow_left))

    left_size = rng.randint(1, size - 2)
    right_size = size - 1 - left_size
    return Ty.arr(random_type(rng, depth, left_size, forall_left,
                              arrow_left - 1),
                  random_type(rng, depth, right_size, forall_left,
                              arrow_left - 1))


def seeded_types(depth: int = 0) -> set[Ty]:
    x0 = Ty.var(0)
    x1 = Ty.var(1)
    x2 = Ty.var(2)
    types = {
        STAR,
        NAT,
        BOOL,
        Ty.all(x0),
        Ty.all(STAR),
        Ty.all(NAT),
        Ty.all(BOOL),
        Ty.all(Ty.arr(x0, STAR)),
        Ty.all(Ty.arr(x0, x0)),
        Ty.all(Ty.all(x1)),
        Ty.all(Ty.all(Ty.all(x2))),
        Ty.arr(NAT, BOOL),
        Ty.arr(NAT, Ty.arr(BOOL, STAR)),
        Ty.arr(Ty.all(x0), STAR),
        Ty.all(Ty.arr(x0, Ty.arr(NAT, x0))),
        Ty.all(Ty.all(Ty.arr(x1, Ty.arr(x0, x1)))),
        Ty.all(Ty.all(Ty.all(Ty.arr(x2, Ty.arr(x1, x0))))),
    }
    for index in range(depth):
        var = Ty.var(index)
        types.add(var)
        types.add(Ty.arr(var, STAR))
        types.add(Ty.arr(var, var))
        types.add(Ty.all(var))
    return {ty for ty in types if well_formed(depth, ty)}


def make_pool(args: argparse.Namespace, rng: random.Random,
              depth: int = 0) -> list[Ty]:
    types = seeded_types(depth)
    for _ in range(args.pool_draws):
        size = rng.randint(1, args.max_size)
        ty = random_type(rng, depth, size, args.max_forall, args.max_arrow)
        if well_formed(depth, ty):
            types.add(ty)
    seeded = seeded_types(depth)
    if args.pool_cap and len(types) > args.pool_cap:
        extras = sorted(types - seeded, key=lambda ty: (size_of(ty), pp_ty(ty)))
        keep = max(0, args.pool_cap - len(seeded))
        if len(extras) > keep:
            extras = rng.sample(extras, keep)
        types = seeded | set(extras)
    return sorted(types, key=lambda ty: (size_of(ty), pp_ty(ty)))


def size_of(ty: Ty) -> int:
    if ty.tag in ("var", "base", "star"):
        return 1
    if ty.tag == "arr":
        return 1 + size_of(ty.args[0]) + size_of(ty.args[1])
    if ty.tag == "all":
        return 1 + size_of(ty.args[0])
    raise ValueError(ty)


def forall_depth(ty: Ty) -> int:
    if ty.tag == "all":
        return 1 + forall_depth(ty.args[0])
    if ty.tag == "arr":
        return max(forall_depth(ty.args[0]), forall_depth(ty.args[1]))
    return 0


def arrow_depth(ty: Ty) -> int:
    if ty.tag == "arr":
        return 1 + max(arrow_depth(ty.args[0]), arrow_depth(ty.args[1]))
    if ty.tag == "all":
        return arrow_depth(ty.args[0])
    return 0


def related_pairs_for(
    ctx: Ctx,
    dl: int,
    dr: int,
    left_pool: Sequence[Ty],
    right_pool: Sequence[Ty],
    cap: int,
) -> list[tuple[Ty, Ty]]:
    pairs: list[tuple[Ty, Ty]] = []
    for src in left_pool:
        for tgt in right_pool:
            if derivs(ctx, dl, dr, src, tgt, cap):
                pairs.append((src, tgt))
    return pairs


def related_pairs(pool: Sequence[Ty], cap: int) -> list[tuple[Ty, Ty]]:
    return related_pairs_for((), 0, 0, pool, pool, cap)


@lru_cache(maxsize=None)
def lower_witnesses_at(
    depth: int,
    a: Ty,
    b: Ty,
    pool_key: tuple[Ty, ...],
    cap: int,
    per_pair: int,
) -> tuple[tuple[Ty, Deriv, Deriv], ...]:
    out: list[tuple[Ty, Deriv, Deriv]] = []
    ctx = id_ctx(depth)
    for c in pool_key:
        ps = derivs(ctx, depth, depth, c, a, cap)
        if not ps:
            continue
        qs = derivs(ctx, depth, depth, c, b, cap)
        if not qs:
            continue
        for p in ps:
            for q in qs:
                out.append((c, p, q))
                if len(out) >= per_pair:
                    return tuple(out)
    return tuple(out)


def lower_witnesses(a: Ty, b: Ty, pool_key: tuple[Ty, ...],
                    cap: int, per_pair: int) -> tuple[tuple[Ty, Deriv, Deriv], ...]:
    return lower_witnesses_at(0, a, b, pool_key, cap, per_pair)


def sample_one(seq: Sequence, rng: random.Random):
    return seq[rng.randrange(len(seq))]


def random_ctx(rng: random.Random, dl: int, dr: int) -> Ctx:
    assms: set[Assm] = set()
    if rng.random() < 0.35:
        for left in range(dl):
            assms.add(("star", left, None))
            for right in range(dr):
                assms.add(("var", left, right))
    else:
        for index in range(min(dl, dr)):
            if rng.random() < 0.65:
                assms.add(("var", index, index))
        for left in range(dl):
            if rng.random() < 0.40:
                assms.add(("star", left, None))
            for right in range(dr):
                if rng.random() < 0.18:
                    assms.add(("var", left, right))
    return tuple(sorted(assms))


def find_related_pair(
    rng: random.Random,
    ctx: Ctx,
    dl: int,
    dr: int,
    left_pool: Sequence[Ty],
    right_pool: Sequence[Ty],
    attempts: int,
    cap: int,
) -> tuple[Ty, Ty] | None:
    for _ in range(attempts):
        left = sample_one(left_pool, rng)
        right = sample_one(right_pool, rng)
        if derivs(ctx, dl, dr, left, right, cap):
            return left, right
    return None


def report_route_counterexample(
    depth: int,
    a: Ty,
    b: Ty,
    c: Ty,
    p: Deriv,
    q: Deriv,
    lower: Ty,
    reason: str,
    witness: Ty | None = None,
) -> None:
    print("route-postulate counterexample found")
    print(f"reason = {reason}")
    print(f"depth  = {depth}")
    print(f"A      = {pp_ty(a)}")
    print(f"B      = {pp_ty(b)}")
    print(f"C      = {pp_ty(c)}")
    print(f"mlb    = {pp_ty(lower)}")
    print(f"p tag  = {p.tag}, q tag = {q.tag}")
    if witness is not None:
        print(f"E      = {pp_ty(witness)}")


def route_observation_failure(
    depth: int,
    a: Ty,
    b: Ty,
    lower: Ty,
    pool: Sequence[Ty],
    cap: int,
) -> tuple[str, Ty | None] | None:
    ctx = id_ctx(depth)
    if not derivs(ctx, depth, depth, lower, a, cap):
        return "selected lower is not below A", None
    if not derivs(ctx, depth, depth, lower, b, cap):
        return "selected lower is not below B", None

    for witness in pool:
        if not derivs(ctx, depth, depth, witness, a, cap):
            continue
        if not derivs(ctx, depth, depth, witness, b, cap):
            continue
        if not derivs(ctx, depth, depth, lower, witness, cap):
            continue
        if not derivs(ctx, depth, depth, witness, lower, cap):
            return (
                "bounded common lower is strictly above selected lower",
                witness,
            )
    return None


def check_route_postulate(
    args: argparse.Namespace,
    rng: random.Random,
    pools: dict[int, list[Ty]],
) -> int:
    checked = 0
    valid_pairs = 0
    maximal_comparisons = 0
    for _ in range(args.trials):
        depth = rng.randrange(args.context_depth + 1)
        pool = pools[depth]
        pool_key = tuple(pool)
        a = sample_one(pool, rng)
        b = sample_one(pool, rng)
        lowers = lower_witnesses_at(depth, a, b, pool_key, args.deriv_cap,
                                    args.lower_cap)
        if not lowers:
            continue

        valid_pairs += 1
        for _route in range(min(args.routes_per_instance, len(lowers))):
            c, p, q = sample_one(lowers, rng)
            lower = mlb_type(p, q)
            ctx = id_ctx(depth)
            failure = route_observation_failure(
                depth, a, b, lower, pool, args.deriv_cap)
            checked += 1
            if failure is not None:
                reason, witness = failure
                report_route_counterexample(depth, a, b, c, p, q, lower,
                                            reason, witness)
                return 1
            for witness in pool:
                if derivs(ctx, depth, depth, witness, a, args.deriv_cap) and \
                   derivs(ctx, depth, depth, witness, b, args.deriv_cap) and \
                   derivs(ctx, depth, depth, lower, witness, args.deriv_cap):
                    maximal_comparisons += 1

    print(f"route_valid_endpoint_pairs={valid_pairs}")
    print(f"route_witnesses_checked={checked}")
    print(f"route_maximality_comparisons={maximal_comparisons}")
    print("route-postulate bounded check: no counterexample found")
    return 0


def report_coherence_counterexample(
    dl: int,
    dr: int,
    ctx: Ctx,
    a: Ty,
    ap: Ty,
    b: Ty,
    bp: Ty,
    c: Ty,
    cp: Ty,
    p: Deriv,
    q: Deriv,
    pp: Deriv,
    qq: Deriv,
    lower: Ty,
    lowerp: Ty,
) -> None:
    print("coherence-postulate counterexample found")
    print(f"left_depth  = {dl}")
    print(f"right_depth = {dr}")
    print(f"context     = {ctx}")
    print(f"A           = {pp_ty(a)}")
    print(f"A'          = {pp_ty(ap)}")
    print(f"B           = {pp_ty(b)}")
    print(f"B'          = {pp_ty(bp)}")
    print(f"C           = {pp_ty(c)}")
    print(f"C'          = {pp_ty(cp)}")
    print(f"mlb         = {pp_ty(lower)}")
    print(f"mlb'        = {pp_ty(lowerp)}")
    print(f"p tag       = {p.tag}, q tag = {q.tag}")
    print(f"p' tag      = {pp.tag}, q' tag = {qq.tag}")


def check_coherence_postulate(
    args: argparse.Namespace,
    rng: random.Random,
    pools: dict[int, list[Ty]],
) -> int:
    valid_endpoint_instances = 0
    route_pairs_checked = 0
    for _ in range(args.trials):
        dl = rng.randrange(args.context_depth + 1)
        dr = rng.randrange(args.context_depth + 1)
        ctx = random_ctx(rng, dl, dr)
        left_pool = pools[dl]
        right_pool = pools[dr]

        endpoint_a = find_related_pair(
            rng, ctx, dl, dr, left_pool, right_pool,
            args.relation_attempts, args.deriv_cap)
        endpoint_b = find_related_pair(
            rng, ctx, dl, dr, left_pool, right_pool,
            args.relation_attempts, args.deriv_cap)
        if endpoint_a is None or endpoint_b is None:
            continue
        a, ap = endpoint_a
        b, bp = endpoint_b

        left_lowers = lower_witnesses_at(dl, a, b, tuple(left_pool),
                                         args.deriv_cap, args.lower_cap)
        if not left_lowers:
            continue
        right_lowers = lower_witnesses_at(dr, ap, bp, tuple(right_pool),
                                          args.deriv_cap, args.lower_cap)
        if not right_lowers:
            continue

        valid_endpoint_instances += 1
        sample_count = min(args.routes_per_instance,
                           len(left_lowers) * len(right_lowers))
        for _route in range(sample_count):
            c, p, q = sample_one(left_lowers, rng)
            cp, pp, qq = sample_one(right_lowers, rng)
            lower = mlb_type(p, q)
            lowerp = mlb_type(pp, qq)
            left_failure = route_observation_failure(
                dl, a, b, lower, left_pool, args.deriv_cap)
            if left_failure is not None:
                reason, witness = left_failure
                report_route_counterexample(
                    dl, a, b, c, p, q, lower, reason, witness)
                return 1
            right_failure = route_observation_failure(
                dr, ap, bp, lowerp, right_pool, args.deriv_cap)
            if right_failure is not None:
                reason, witness = right_failure
                report_route_counterexample(
                    dr, ap, bp, cp, pp, qq, lowerp, reason, witness)
                return 1
            route_pairs_checked += 1
            if not derivs(ctx, dl, dr, lower, lowerp, args.deriv_cap):
                report_coherence_counterexample(
                    dl, dr, ctx, a, ap, b, bp, c, cp, p, q, pp, qq,
                    lower, lowerp)
                return 1

    print(f"coherence_valid_endpoint_instances={valid_endpoint_instances}")
    print(f"coherence_route_pairs_checked={route_pairs_checked}")
    print("coherence-postulate bounded check: no counterexample found")
    return 0


def check_postulates(args: argparse.Namespace) -> int:
    rng = random.Random(args.seed)
    pools = {depth: make_pool(args, rng, depth)
             for depth in range(args.context_depth + 1)}
    print(f"seed={args.seed}")
    for depth, pool in pools.items():
        max_forall_seen = max(forall_depth(ty) for ty in pool)
        max_arrow_seen = max(arrow_depth(ty) for ty in pool)
        print(
            f"depth={depth} type_pool={len(pool)} "
            f"max_forall_depth_seen={max_forall_seen} "
            f"max_arrow_depth_seen={max_arrow_seen}"
        )
    print(f"trials={args.trials} deriv_cap={args.deriv_cap} "
          f"lower_cap={args.lower_cap} context_depth={args.context_depth}")

    route_result = check_route_postulate(args, rng, pools)
    if route_result:
        return route_result
    coherence_result = check_coherence_postulate(args, rng, pools)
    if coherence_result:
        return coherence_result
    print("postulate bounded checks: no counterexample found")
    return 0


def check(args: argparse.Namespace) -> int:
    rng = random.Random(args.seed)
    pool = make_pool(args, rng)
    pool_key = tuple(pool)
    print(f"seed={args.seed}", flush=True)
    print(f"type_pool={len(pool)}", flush=True)
    pairs = related_pairs(pool, args.deriv_cap)

    max_forall_seen = max(forall_depth(ty) for ty in pool)
    max_arrow_seen = max(arrow_depth(ty) for ty in pool)
    print(f"related_pairs={len(pairs)}")
    print(f"max_forall_depth_seen={max_forall_seen} "
          f"max_arrow_depth_seen={max_arrow_seen}")
    print(f"trials={args.trials} deriv_cap={args.deriv_cap} "
          f"lower_cap={args.lower_cap}")

    if max_forall_seen < args.max_forall or max_arrow_seen < args.max_arrow:
        print("warning: generated pool did not reach requested nesting")

    checked = 0
    valid_instances = 0
    for _ in range(args.trials):
        a, ap = sample_one(pairs, rng)
        b, bp = sample_one(pairs, rng)
        left_lowers = lower_witnesses(a, b, pool_key, args.deriv_cap,
                                      args.lower_cap)
        if not left_lowers:
            continue
        right_lowers = lower_witnesses(ap, bp, pool_key, args.deriv_cap,
                                       args.lower_cap)
        if not right_lowers:
            continue

        valid_instances += 1
        sample_count = min(args.routes_per_instance,
                           len(left_lowers) * len(right_lowers))
        for _route in range(sample_count):
            c, p, q = sample_one(left_lowers, rng)
            cp, pp, qq = sample_one(right_lowers, rng)
            lower = mlb_type(p, q)
            lowerp = mlb_type(pp, qq)
            checked += 1
            if not derivs((), 0, 0, lower, lowerp, args.deriv_cap):
                print("counterexample found")
                print(f"A      = {pp_ty(a)}")
                print(f"A'     = {pp_ty(ap)}")
                print(f"B      = {pp_ty(b)}")
                print(f"B'     = {pp_ty(bp)}")
                print(f"C      = {pp_ty(c)}")
                print(f"C'     = {pp_ty(cp)}")
                print(f"mlb    = {pp_ty(lower)}")
                print(f"mlb'   = {pp_ty(lowerp)}")
                print(f"p tag  = {p.tag}, q tag = {q.tag}")
                print(f"p' tag = {pp.tag}, q' tag = {qq.tag}")
                return 1

    print(f"valid_endpoint_instances={valid_instances}")
    print(f"route_pairs_checked={checked}")
    print("no counterexample found")
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("coherence", "postulates"),
                        default="coherence")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--trials", type=int, default=20000)
    parser.add_argument("--pool-draws", type=int, default=20000)
    parser.add_argument("--pool-cap", type=int, default=350)
    parser.add_argument("--max-size", type=int, default=11)
    parser.add_argument("--max-forall", type=int, default=3)
    parser.add_argument("--max-arrow", type=int, default=2)
    parser.add_argument("--deriv-cap", type=int, default=128)
    parser.add_argument("--lower-cap", type=int, default=96)
    parser.add_argument("--routes-per-instance", type=int, default=4)
    parser.add_argument("--context-depth", type=int, default=3)
    parser.add_argument("--relation-attempts", type=int, default=200)
    return parser.parse_args()


if __name__ == "__main__":
    options = parse_args()
    if options.mode == "postulates":
        raise SystemExit(check_postulates(options))
    raise SystemExit(check(options))
