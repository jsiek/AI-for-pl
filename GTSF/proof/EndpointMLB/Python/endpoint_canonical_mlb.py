#!/usr/bin/env python3
"""Endpoint-canonical maximal lower bound for small GTSF type models.

This is an executable reference implementation of the design in
`EndpointCanonicalMLBDesign.md`.  It computes from endpoint types only; it does
not inspect lower-bound evidence or selector routes.

The implementation intentionally tracks endpoint binders by explicit IDs and
records which local `forall` block owns each generated support profile.  That
keeps nested `forall` blocks that mention outer binders from being confused with
ordinary free variables.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from mlb_counterexample_search import BOOL, NAT, STAR, Ty, pp_ty


Side = Literal["left", "right"]


class NoMlb(Exception):
    """Internal non-local return for unsatisfiable MLB constraints."""


@dataclass(frozen=True)
class Binder:
    id: int
    side: Side
    block: int
    exposure: int


@dataclass
class Profile:
    id: int
    block: int
    left: Binder | None
    right: Binder | None
    creation: int
    first_use: int | None


@dataclass
class Block:
    id: int
    left_binders: list[Binder]
    right_binders: list[Binder]
    profiles: list[Profile]
    next_use: int = 0


@dataclass(frozen=True)
class RawVar:
    tag: Literal["bound", "profile", "free"]
    index: int


@dataclass(frozen=True)
class RawTy:
    tag: str
    args: tuple

    @staticmethod
    def var(ref: RawVar) -> "RawTy":
        return RawTy("var", (ref,))

    @staticmethod
    def base(name: str) -> "RawTy":
        return RawTy("base", (name,))

    @staticmethod
    def star() -> "RawTy":
        return RawTy("star", ())

    @staticmethod
    def arr(left: "RawTy", right: "RawTy") -> "RawTy":
        return RawTy("arr", (left, right))

    @staticmethod
    def all(body: "RawTy") -> "RawTy":
        return RawTy("all", (body,))


RAW_STAR = RawTy.star()


class EndpointMlbSolver:
    def __init__(self) -> None:
        self.next_block = 0
        self.next_binder = 0
        self.next_profile = 0
        self.next_creation = 0
        self.blocks: dict[int, Block] = {}

    def fresh_block(self) -> Block:
        block = Block(self.next_block, [], [], [])
        self.blocks[block.id] = block
        self.next_block += 1
        return block

    def fresh_binder(self, side: Side, block: Block) -> Binder:
        exposure = (
            len(block.left_binders)
            if side == "left"
            else len(block.right_binders)
        )
        binder = Binder(self.next_binder, side, block.id, exposure)
        self.next_binder += 1
        if side == "left":
            block.left_binders.append(binder)
        else:
            block.right_binders.append(binder)
        return binder

    def mlb(self, left: Ty, right: Ty) -> Ty | None:
        try:
            raw = self.mlb_block(left, right, [], [])
            return self.raw_to_ty(raw)
        except NoMlb:
            return None

    def mlb_block(
        self,
        left: Ty,
        right: Ty,
        left_env: list[Binder],
        right_env: list[Binder],
    ) -> RawTy:
        block = self.fresh_block()
        left_body = left
        right_body = right
        left_env = list(left_env)
        right_env = list(right_env)

        while left_body.tag == "all":
            left_env.insert(0, self.fresh_binder("left", block))
            left_body = left_body.args[0]

        while right_body.tag == "all":
            right_env.insert(0, self.fresh_binder("right", block))
            right_body = right_body.args[0]

        body = self.mlb_body(left_body, right_body, left_env, right_env)
        return self.close_block(block, body)

    def mlb_body(
        self,
        left: Ty,
        right: Ty,
        left_env: list[Binder],
        right_env: list[Binder],
    ) -> RawTy:
        if left.tag == "all" or right.tag == "all":
            return self.mlb_block(left, right, left_env, right_env)

        if left.tag == "star" and right.tag == "star":
            return RAW_STAR

        if left.tag == "base" and right.tag == "base":
            if left.args[0] != right.args[0]:
                raise NoMlb()
            return RawTy.base(left.args[0])

        if left.tag == "base" and right.tag == "star":
            return RawTy.base(left.args[0])

        if left.tag == "star" and right.tag == "base":
            return RawTy.base(right.args[0])

        if left.tag == "arr" and right.tag == "arr":
            return RawTy.arr(
                self.mlb_body(left.args[0], right.args[0], left_env, right_env),
                self.mlb_body(left.args[1], right.args[1], left_env, right_env),
            )

        if left.tag == "arr" and right.tag == "star":
            return RawTy.arr(
                self.mlb_body(left.args[0], STAR, left_env, right_env),
                self.mlb_body(left.args[1], STAR, left_env, right_env),
            )

        if left.tag == "star" and right.tag == "arr":
            return RawTy.arr(
                self.mlb_body(STAR, right.args[0], left_env, right_env),
                self.mlb_body(STAR, right.args[1], left_env, right_env),
            )

        if left.tag == "var" and right.tag == "var":
            left_ref = self.lookup(left_env, left.args[0])
            right_ref = self.lookup(right_env, right.args[0])
            if isinstance(left_ref, Binder) or isinstance(right_ref, Binder):
                if not isinstance(left_ref, Binder) or not isinstance(
                    right_ref, Binder
                ):
                    raise NoMlb()
                return RawTy.var(
                    RawVar(
                        "profile",
                        self.request_profile(left_ref, right_ref).id,
                    )
                )
            if left_ref == right_ref:
                return RawTy.var(RawVar("free", left_ref))
            raise NoMlb()

        if left.tag == "var" and right.tag == "star":
            left_ref = self.lookup(left_env, left.args[0])
            if not isinstance(left_ref, Binder):
                raise NoMlb()
            return RawTy.var(
                RawVar("profile", self.request_profile(left_ref, None).id)
            )

        if left.tag == "star" and right.tag == "var":
            right_ref = self.lookup(right_env, right.args[0])
            if not isinstance(right_ref, Binder):
                raise NoMlb()
            return RawTy.var(
                RawVar("profile", self.request_profile(None, right_ref).id)
            )

        raise NoMlb()

    @staticmethod
    def lookup(env: list[Binder], index: int) -> Binder | int:
        if index < len(env):
            return env[index]
        return index - len(env)

    def request_profile(
        self,
        left: Binder | None,
        right: Binder | None,
    ) -> Profile:
        block_id = self.profile_block(left, right)
        block = self.blocks[block_id]

        for profile in block.profiles:
            if profile.left == left and profile.right == right:
                return profile
            if left is not None and profile.left == left:
                raise NoMlb()
            if right is not None and profile.right == right:
                raise NoMlb()

        profile = Profile(
            self.next_profile,
            block_id,
            left,
            right,
            self.next_creation,
            block.next_use,
        )
        self.next_profile += 1
        self.next_creation += 1
        block.next_use += 1
        block.profiles.append(profile)
        return profile

    @staticmethod
    def profile_block(left: Binder | None, right: Binder | None) -> int:
        if left is not None and right is not None:
            if left.block != right.block:
                raise NoMlb()
            return left.block
        if left is not None:
            return left.block
        if right is not None:
            return right.block
        raise NoMlb()

    def close_block(self, block: Block, body: RawTy) -> RawTy:
        self.pair_unused_binders(block)
        ordered = self.order_profiles(block)
        position = {profile.id: index for index, profile in enumerate(ordered)}
        body = self.resolve_block_refs(block.id, position, len(ordered), body)
        for _profile in reversed(ordered):
            body = RawTy.all(body)
        return body

    def pair_unused_binders(self, block: Block) -> None:
        used_left = {profile.left for profile in block.profiles}
        used_right = {profile.right for profile in block.profiles}
        left_unused = [
            binder for binder in block.left_binders if binder not in used_left
        ]
        right_unused = [
            binder for binder in block.right_binders if binder not in used_right
        ]

        if len(left_unused) != len(right_unused):
            raise NoMlb()

        for left, right in zip(left_unused, right_unused):
            profile = Profile(
                self.next_profile,
                block.id,
                left,
                right,
                self.next_creation,
                None,
            )
            self.next_profile += 1
            self.next_creation += 1
            block.profiles.append(profile)

    def order_profiles(self, block: Block) -> list[Profile]:
        profiles = block.profiles
        by_id = {profile.id: profile for profile in profiles}
        edges: set[tuple[int, int]] = set()

        left_order = sorted(
            (profile for profile in profiles if profile.left is not None),
            key=lambda profile: profile.left.exposure,
        )
        self.add_chain_edges(edges, left_order)

        right_order = sorted(
            (profile for profile in profiles if profile.right is not None),
            key=lambda profile: profile.right.exposure,
        )
        self.add_chain_edges(edges, right_order)

        remaining = set(by_id)
        ordered: list[Profile] = []
        while remaining:
            sources = [
                profile_id
                for profile_id in remaining
                if not any(
                    dst == profile_id and src in remaining
                    for src, dst in edges
                )
            ]
            if not sources:
                raise NoMlb()
            chosen = min(
                sources,
                key=lambda profile_id: self.tie_key(by_id[profile_id]),
            )
            remaining.remove(chosen)
            ordered.append(by_id[chosen])
        return ordered

    @staticmethod
    def add_chain_edges(
        edges: set[tuple[int, int]],
        profiles: list[Profile],
    ) -> None:
        for left, right in zip(profiles, profiles[1:]):
            if left.id != right.id:
                edges.add((left.id, right.id))

    @staticmethod
    def tie_key(profile: Profile) -> tuple[int, int, int, int, int, int, int]:
        first_use = 10**9 if profile.first_use is None else profile.first_use
        no_left = 1 if profile.left is None else 0
        left_exp = 10**9 if profile.left is None else profile.left.exposure
        no_right = 1 if profile.right is None else 0
        right_exp = 10**9 if profile.right is None else profile.right.exposure
        side_class = 0 if profile.left is not None else 1
        return (
            first_use,
            no_left,
            left_exp,
            no_right,
            right_exp,
            side_class,
            profile.creation,
        )

    def resolve_block_refs(
        self,
        block_id: int,
        position: dict[int, int],
        profile_count: int,
        raw: RawTy,
        depth: int = 0,
    ) -> RawTy:
        if raw.tag == "var":
            ref = raw.args[0]
            if ref.tag == "profile":
                profile = self.profile_by_id(ref.index)
                if profile.block == block_id:
                    index = depth + profile_count - 1 - position[profile.id]
                    return RawTy.var(RawVar("bound", index))
            return raw
        if raw.tag in ("base", "star"):
            return raw
        if raw.tag == "arr":
            return RawTy.arr(
                self.resolve_block_refs(
                    block_id, position, profile_count, raw.args[0], depth
                ),
                self.resolve_block_refs(
                    block_id, position, profile_count, raw.args[1], depth
                ),
            )
        if raw.tag == "all":
            return RawTy.all(
                self.resolve_block_refs(
                    block_id, position, profile_count, raw.args[0], depth + 1
                )
            )
        raise ValueError(raw)

    def profile_by_id(self, profile_id: int) -> Profile:
        for block in self.blocks.values():
            for profile in block.profiles:
                if profile.id == profile_id:
                    return profile
        raise KeyError(profile_id)

    def raw_to_ty(self, raw: RawTy, depth: int = 0) -> Ty:
        if raw.tag == "var":
            ref = raw.args[0]
            if ref.tag == "bound":
                return Ty.var(ref.index)
            if ref.tag == "free":
                return Ty.var(depth + ref.index)
            raise AssertionError(f"unresolved profile {ref.index}")
        if raw.tag == "base":
            return Ty.base(raw.args[0])
        if raw.tag == "star":
            return STAR
        if raw.tag == "arr":
            return Ty.arr(
                self.raw_to_ty(raw.args[0], depth),
                self.raw_to_ty(raw.args[1], depth),
            )
        if raw.tag == "all":
            return Ty.all(self.raw_to_ty(raw.args[0], depth + 1))
        raise ValueError(raw)


def endpoint_mlb(left: Ty, right: Ty) -> Ty | None:
    """Return the endpoint-canonical MLB candidate, if one exists."""

    return EndpointMlbSolver().mlb(left, right)


def main() -> int:
    examples = [
        (Ty.all(Ty.arr(Ty.var(0), STAR)), Ty.all(Ty.arr(STAR, Ty.var(0)))),
        (Ty.all(STAR), Ty.all(STAR)),
        (Ty.all(Ty.arr(Ty.var(0), Ty.var(0))), STAR),
        (
            Ty.all(Ty.all(Ty.arr(Ty.var(1), Ty.var(0)))),
            Ty.all(Ty.all(Ty.arr(Ty.var(1), Ty.var(0)))),
        ),
    ]
    for left, right in examples:
        result = endpoint_mlb(left, right)
        result_text = pp_ty(result) if result else "nothing"
        print(f"{pp_ty(left)} /\\ {pp_ty(right)} = {result_text}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
