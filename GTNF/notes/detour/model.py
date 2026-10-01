#!/usr/bin/env python3
"""Finite executable model of GTSFImp type consistency and imprecision.

The syntax, side conditions, and environment changes follow:

* GTSFImp/Types.agda
* GTSFImp/Consistency.agda
* GTSFImp/Imprecision.agda
* GTSFImp/Consistency2.agda

Run ``python3 model.py --self-test`` for local checks and
``python3 model.py --search --max-size N`` for the exhaustive searches used
by REPORT.md.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import dataclass
from enum import Enum
from functools import cache
from itertools import product
from typing import Sequence


# ---------------------------------------------------------------------------
# Types
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Var:
    index: int


@dataclass(frozen=True, slots=True)
class Base:
    name: str


@dataclass(frozen=True, slots=True)
class Star:
    pass


@dataclass(frozen=True, slots=True)
class Arrow:
    domain: "Type"
    codomain: "Type"


@dataclass(frozen=True, slots=True)
class All:
    body: "Type"


Type = Var | Base | Star | Arrow | All

NAT = Base("N")
BOOL = Base("B")
STAR = Star()


def type_size(ty: Type) -> int:
    if isinstance(ty, (Var, Base, Star)):
        return 1
    if isinstance(ty, Arrow):
        return 1 + type_size(ty.domain) + type_size(ty.codomain)
    return 1 + type_size(ty.body)


def shift(ty: Type, cutoff: int = 0) -> Type:
    """Agda's ``renameᵗ suc``, with binder-aware lifting."""

    if isinstance(ty, Var):
        return Var(ty.index + 1) if ty.index >= cutoff else ty
    if isinstance(ty, (Base, Star)):
        return ty
    if isinstance(ty, Arrow):
        return Arrow(shift(ty.domain, cutoff), shift(ty.codomain, cutoff))
    return All(shift(ty.body, cutoff + 1))


def occurs(ty: Type, index: int) -> bool:
    """Decision version of ``index ∈ᵗ ty``."""

    if isinstance(ty, Var):
        return ty.index == index
    if isinstance(ty, (Base, Star)):
        return False
    if isinstance(ty, Arrow):
        return occurs(ty.domain, index) or occurs(ty.codomain, index)
    return occurs(ty.body, index + 1)


def nonvar(ty: Type) -> bool:
    return not isinstance(ty, Var)


def nonstar(ty: Type) -> bool:
    return not isinstance(ty, Star)


def atom(ty: Type) -> bool:
    return isinstance(ty, (Var, Base, Star))


def well_scoped(ty: Type, depth: int) -> bool:
    if isinstance(ty, Var):
        return 0 <= ty.index < depth
    if isinstance(ty, (Base, Star)):
        return True
    if isinstance(ty, Arrow):
        return well_scoped(ty.domain, depth) and well_scoped(ty.codomain, depth)
    return well_scoped(ty.body, depth + 1)


def _fresh_name(used: set[str]) -> str:
    stems = ("X", "Y", "Z", "U", "V", "W")
    for stem in stems:
        if stem not in used:
            return stem
    serial = 1
    while True:
        for stem in stems:
            candidate = f"{stem}{serial}"
            if candidate not in used:
                return candidate
        serial += 1


def pretty_type(ty: Type, depth: int = 0) -> str:
    """Render intrinsically scoped syntax with names instead of indices."""

    free = ["X", "Y", "Z", "U", "V", "W"]
    if depth > len(free):
        free += [f"X{i}" for i in range(len(free), depth)]
    env = free[:depth]

    return _pretty_type_with_names(ty, env, 0)


def _pretty_type_with_names(
    value: Type, names: list[str], precedence: int
) -> str:
    if isinstance(value, Var):
        return names[value.index]
    if isinstance(value, Base):
        return "ℕ" if value.name == "N" else "𝔹"
    if isinstance(value, Star):
        return "★"
    if isinstance(value, Arrow):
        left = _pretty_type_with_names(value.domain, names, 2)
        right = _pretty_type_with_names(value.codomain, names, 1)
        text = f"{left}→{right}"
        return f"({text})" if precedence > 1 else text
    binder = _fresh_name(set(names))
    text = f"∀{binder}. {_pretty_type_with_names(value.body, [binder, *names], 0)}"
    return f"({text})" if precedence > 0 else text


def type_key(ty: Type) -> tuple:
    if isinstance(ty, Var):
        return (0, ty.index)
    if isinstance(ty, Base):
        return (1, ty.name)
    if isinstance(ty, Star):
        return (2,)
    if isinstance(ty, Arrow):
        return (3, type_key(ty.domain), type_key(ty.codomain))
    return (4, type_key(ty.body))


@cache
def types_exact(depth: int, size: int) -> tuple[Type, ...]:
    if size < 1:
        return ()
    values: list[Type] = []
    if size == 1:
        values.extend(Var(i) for i in range(depth))
        values.extend((NAT, BOOL, STAR))
    if size >= 2:
        values.extend(All(body) for body in types_exact(depth + 1, size - 1))
    if size >= 3:
        for left_size in range(1, size - 1):
            right_size = size - 1 - left_size
            values.extend(
                Arrow(left, right)
                for left in types_exact(depth, left_size)
                for right in types_exact(depth, right_size)
            )
    return tuple(sorted(set(values), key=type_key))


def types_upto(depth: int, bound: int) -> tuple[Type, ...]:
    return tuple(
        ty for size in range(1, bound + 1) for ty in types_exact(depth, size)
    )


# ---------------------------------------------------------------------------
# Consistency modes, ground types, and declarative evidence
# ---------------------------------------------------------------------------


class Mode(Enum):
    XX = "X~X"
    X_STAR = "X~*"
    STAR_X = "*~X"
    CROSS = "*~X~*"


Env = tuple[Mode, ...]


def flip_mode(mode: Mode) -> Mode:
    return {
        Mode.XX: Mode.XX,
        Mode.X_STAR: Mode.STAR_X,
        Mode.STAR_X: Mode.X_STAR,
        Mode.CROSS: Mode.CROSS,
    }[mode]


def flip_env(env: Env) -> Env:
    return tuple(flip_mode(mode) for mode in env)


def ext_env(env: Env) -> Env:
    return (Mode.XX, *env)


def inst_env(env: Env) -> Env:
    return (Mode.X_STAR, *env)


def gen_env(env: Env) -> Env:
    return (Mode.STAR_X, *env)


def identity_consistency_env(depth: int) -> Env:
    return (Mode.CROSS,) * depth


@cache
def ground_types(depth: int) -> tuple[Type, ...]:
    """All inhabitants of Agda's ``Ground`` at this context depth."""

    return (
        *(Var(i) for i in range(depth)),
        NAT,
        BOOL,
        Arrow(STAR, STAR),
        All(STAR),
    )


def ground(ty: Type, depth: int) -> bool:
    return ty in ground_types(depth)


def ground_to_star_gate(env: Env, ty: Type) -> bool:
    if ty == Arrow(STAR, STAR) or isinstance(ty, Base) or ty == All(STAR):
        return True
    return isinstance(ty, Var) and env[ty.index] in (Mode.X_STAR, Mode.CROSS)


def star_to_ground_gate(env: Env, ty: Type) -> bool:
    if ty == Arrow(STAR, STAR) or isinstance(ty, Base) or ty == All(STAR):
        return True
    return isinstance(ty, Var) and env[ty.index] in (Mode.STAR_X, Mode.CROSS)


@dataclass(frozen=True, slots=True)
class Evidence:
    ctor: str
    left: Type
    right: Type
    children: tuple["Evidence", ...] = ()
    ground: Type | None = None


def pretty_evidence(evidence: Evidence, depth: int = 0) -> str:
    free = ["X", "Y", "Z", "U", "V", "W"]
    if depth > len(free):
        free += [f"X{i}" for i in range(len(free), depth)]

    def go(value: Evidence, names: list[str]) -> str:
        ctor = value.ctor
        if ctor == "id":
            return f"id[{_pretty_type_with_names(value.left, names, 0)}]"
        if ctor == "arrow":
            return f"({go(value.children[0], names)} ↦ {go(value.children[1], names)})"
        if ctor == "tag":
            return f"({go(value.children[0], names)})!"
        if ctor == "check":
            return f"？({go(value.children[0], names)})"
        if ctor in ("all", "inst", "gen"):
            binder = _fresh_name(set(names))
            label = {"all": "∀ᶜ", "inst": "inst", "gen": "gen"}[ctor]
            return f"{label}({go(value.children[0], [binder, *names])})"
        return ctor

    return go(evidence, free[:depth])


FULL = "full"
OVERLAP_BAN = "overlap-ban"
ALL_ALL_BAN = "all-all-ban"
POLICIES = (FULL, OVERLAP_BAN, ALL_ALL_BAN)


def _structural_all_possible(env: Env, left: All, right: All) -> bool:
    return bool(enumerate_evidence(ext_env(env), left.body, right.body, FULL))


@cache
def enumerate_evidence(
    env: Env, left: Type, right: Type, policy: str = FULL
) -> tuple[Evidence, ...]:
    """Enumerate every declarative derivation, in canonical preference order.

    The order is structural first (including ``∀ᶜ``), then ``inst``, then
    ``gen``, then the two bottom rules. Tags and checks enumerate the finite
    Agda ``Ground`` family in its displayed constructor order.
    """

    if policy not in POLICIES:
        raise ValueError(f"unknown consistency policy: {policy}")
    if len(env) == 0:
        assert well_scoped(left, 0) and well_scoped(right, 0)

    result: list[Evidence] = []

    if left == right and atom(left):
        result.append(Evidence("id", left, right))

    if isinstance(left, Arrow) and isinstance(right, Arrow):
        domains = enumerate_evidence(
            flip_env(env), right.domain, left.domain, policy
        )
        codomains = enumerate_evidence(
            env, left.codomain, right.codomain, policy
        )
        result.extend(
            Evidence("arrow", left, right, (domain, codomain))
            for domain, codomain in product(domains, codomains)
        )

    if isinstance(left, All) and isinstance(right, All):
        result.extend(
            Evidence("all", left, right, (child,))
            for child in enumerate_evidence(
                ext_env(env), left.body, right.body, policy
            )
        )

    if isinstance(right, Star) and nonstar(left):
        for middle in ground_types(len(env)):
            if ground_to_star_gate(env, middle):
                result.extend(
                    Evidence("tag", left, right, (child,), middle)
                    for child in enumerate_evidence(env, left, middle, policy)
                )

    if isinstance(left, Star) and nonstar(right):
        for middle in ground_types(len(env)):
            if star_to_ground_gate(env, middle):
                result.extend(
                    Evidence("check", left, right, (child,), middle)
                    for child in enumerate_evidence(env, middle, right, policy)
                )

    both_all = isinstance(left, All) and isinstance(right, All)
    overlap = both_all and _structural_all_possible(env, left, right)

    allow_inst = isinstance(left, All) and nonvar(left.body) and occurs(
        left.body, 0
    ) and not isinstance(right, Star)
    if policy == OVERLAP_BAN and overlap:
        allow_inst = False
    if policy == ALL_ALL_BAN and isinstance(right, All):
        allow_inst = False
    if allow_inst:
        result.extend(
            Evidence("inst", left, right, (child,))
            for child in enumerate_evidence(
                inst_env(env), left.body, shift(right), policy
            )
        )

    allow_gen = isinstance(right, All) and nonvar(right.body) and occurs(
        right.body, 0
    ) and not isinstance(left, Star)
    if policy == OVERLAP_BAN and overlap:
        allow_gen = False
    if policy == ALL_ALL_BAN and isinstance(left, All):
        allow_gen = False
    if allow_gen:
        result.extend(
            Evidence("gen", left, right, (child,))
            for child in enumerate_evidence(
                gen_env(env), shift(left), right.body, policy
            )
        )

    if left == All(Var(0)) and right == All(STAR):
        result.append(Evidence("bot-elim", left, right))
    if left == All(STAR) and right == All(Var(0)):
        result.append(Evidence("bot-intro", left, right))

    return tuple(result)


def canonical_evidence(
    env: Env, left: Type, right: Type, policy: str = FULL
) -> Evidence | None:
    choices = enumerate_evidence(env, left, right, policy)
    return choices[0] if choices else None


def consistency(env: Env, left: Type, right: Type, policy: str = FULL) -> bool:
    return canonical_evidence(env, left, right, policy) is not None


def is_syntactic_detour(evidence: Evidence) -> bool:
    here = (
        evidence.ctor in ("inst", "gen")
        and isinstance(evidence.left, All)
        and isinstance(evidence.right, All)
    )
    return here or any(is_syntactic_detour(child) for child in evidence.children)


def is_overlap_detour(env: Env, evidence: Evidence) -> bool:
    here = (
        evidence.ctor in ("inst", "gen")
        and isinstance(evidence.left, All)
        and isinstance(evidence.right, All)
        and _structural_all_possible(env, evidence.left, evidence.right)
    )
    if here:
        return True
    if evidence.ctor == "arrow":
        return is_overlap_detour(flip_env(env), evidence.children[0]) or (
            is_overlap_detour(env, evidence.children[1])
        )
    if evidence.ctor == "all":
        return is_overlap_detour(ext_env(env), evidence.children[0])
    if evidence.ctor == "inst":
        return is_overlap_detour(inst_env(env), evidence.children[0])
    if evidence.ctor == "gen":
        return is_overlap_detour(gen_env(env), evidence.children[0])
    return any(is_overlap_detour(env, child) for child in evidence.children)


# ---------------------------------------------------------------------------
# Type imprecision
# ---------------------------------------------------------------------------


class ImpMode(Enum):
    SAME = "X<=X"
    DYNAMIC = "X<=*"


ImpEnv = tuple[ImpMode, ...]


def identity_imp_env(depth: int) -> ImpEnv:
    return (ImpMode.SAME,) * depth


def imp_ext(env: ImpEnv) -> ImpEnv:
    return (ImpMode.SAME, *env)


def imp_inst(env: ImpEnv) -> ImpEnv:
    return (ImpMode.DYNAMIC, *env)


@dataclass(frozen=True, slots=True)
class ImpEvidence:
    ctor: str
    left: Type
    right: Type
    children: tuple["ImpEvidence", ...] = ()


@cache
def imprecision_evidence(
    env: ImpEnv, left: Type, right: Type
) -> ImpEvidence | None:
    """Decision procedure for ``μ ⊢ left ⊑ right``.

    The universal-to-star branch follows ``Consistency2.all-choice`` exactly;
    this also makes the selected proof agree with Agda's uniqueness theorem.
    """

    if left == STAR and right == STAR:
        return ImpEvidence("star", left, right)
    if isinstance(left, Base) and left == right:
        return ImpEvidence("base", left, right)
    if isinstance(left, Var) and left == right:
        return ImpEvidence("var", left, right)
    if isinstance(left, Arrow) and isinstance(right, Arrow):
        domain = imprecision_evidence(env, left.domain, right.domain)
        codomain = imprecision_evidence(env, left.codomain, right.codomain)
        if domain and codomain:
            return ImpEvidence("arrow", left, right, (domain, codomain))
        return None
    if isinstance(left, All) and isinstance(right, All):
        body = imprecision_evidence(imp_ext(env), left.body, right.body)
        if body:
            return ImpEvidence("all", left, right, (body,))

    if isinstance(right, Star):
        if isinstance(left, Arrow):
            domain = imprecision_evidence(env, left.domain, STAR)
            codomain = imprecision_evidence(env, left.codomain, STAR)
            if domain and codomain:
                return ImpEvidence("arrow-star", left, right, (domain, codomain))
            return None
        if isinstance(left, Base):
            return ImpEvidence("base-star", left, right)
        if isinstance(left, Var):
            if env[left.index] == ImpMode.DYNAMIC:
                return ImpEvidence("var-star", left, right)
            return None
        if isinstance(left, All):
            body = left.body
            if body == Var(0):
                return ImpEvidence("bot-star", left, right)
            if body == STAR:
                return ImpEvidence("allstar-star", left, right)
            if nonvar(body) and occurs(body, 0):
                child = imprecision_evidence(imp_inst(env), body, STAR)
                if child:
                    return ImpEvidence("all-drop", left, right, (child,))
                return None
            if nonstar(body):
                child = imprecision_evidence(imp_ext(env), body, STAR)
                if child:
                    return ImpEvidence("all-star", left, right, (child,))
                return None

    if isinstance(left, All) and nonvar(left.body) and occurs(left.body, 0):
        child = imprecision_evidence(imp_inst(env), left.body, shift(right))
        if child:
            return ImpEvidence("all-drop", left, right, (child,))

    if left == All(Var(0)) and right == All(STAR):
        return ImpEvidence("bot-elim", left, right)
    return None


def imprecise(env: ImpEnv, left: Type, right: Type) -> bool:
    return imprecision_evidence(env, left, right) is not None


# ---------------------------------------------------------------------------
# Exact executable counterpart of Consistency2.lower?
# ---------------------------------------------------------------------------


def all_dynamic(env: ImpEnv, ty: Type) -> bool:
    if isinstance(ty, Var):
        return env[ty.index] == ImpMode.DYNAMIC
    if isinstance(ty, (Base, Star)):
        return True
    if isinstance(ty, Arrow):
        return all_dynamic(env, ty.domain) and all_dynamic(env, ty.codomain)
    return all_dynamic(imp_inst(env), ty.body)


@cache
def lower_bound(
    left_env: ImpEnv, right_env: ImpEnv, left: Type, right: Type
) -> Type | None:
    """The lower type selected by ``Consistency2.lowerAcc``."""

    if isinstance(right, Star):
        return left if all_dynamic(right_env, left) else None
    if isinstance(left, Star):
        return right if all_dynamic(left_env, right) else None
    if isinstance(left, Var) and isinstance(right, Var):
        return left if left == right else None
    if isinstance(left, Base) and isinstance(right, Base):
        return left if left == right else None
    if isinstance(left, Arrow) and isinstance(right, Arrow):
        domain = lower_bound(
            right_env, left_env, right.domain, left.domain
        )
        if domain is None:
            return None
        codomain = lower_bound(
            left_env, right_env, left.codomain, right.codomain
        )
        return Arrow(domain, codomain) if codomain is not None else None
    if isinstance(left, All) and isinstance(right, All):
        body = lower_bound(
            imp_ext(left_env), imp_ext(right_env), left.body, right.body
        )
        if body is not None:
            return All(body)
        body = lower_bound(
            imp_ext(left_env), imp_inst(right_env), left.body, shift(right)
        )
        if body is not None and nonvar(body) and occurs(body, 0):
            return All(body)
        body = lower_bound(
            imp_inst(left_env), imp_ext(right_env), shift(left), right.body
        )
        if body is not None and nonvar(body) and occurs(body, 0):
            return All(body)
        if left.body == Var(0) and right.body == STAR:
            return All(Var(0))
        if left.body == STAR and right.body == Var(0):
            return All(Var(0))
        return None
    if isinstance(left, All):
        body = lower_bound(
            imp_ext(left_env), imp_inst(right_env), left.body, shift(right)
        )
        if body is not None and nonvar(body) and occurs(body, 0):
            return All(body)
        return None
    if isinstance(right, All):
        body = lower_bound(
            imp_inst(left_env), imp_ext(right_env), shift(left), right.body
        )
        if body is not None and nonvar(body) and occurs(body, 0):
            return All(body)
        return None
    return None


def agda_lower(left: Type, right: Type, depth: int = 0) -> Type | None:
    env = identity_imp_env(depth)
    return lower_bound(env, env, left, right)


# ---------------------------------------------------------------------------
# Structural alignment for Q1
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Alignment:
    ok: bool
    path: str = "root"
    reason: str = ""


def imp_contains(evidence: ImpEvidence, ctor: str) -> bool:
    return evidence.ctor == ctor or any(
        imp_contains(child, ctor) for child in evidence.children
    )


def aligned(
    precise: Evidence,
    imprecise: Evidence,
    env: ImpEnv,
    path: str = "root",
) -> Alignment:
    """Compare canonical derivations using the exceptions in the question.

    A subtree is opaque once either endpoint on the less precise side is ★.
    An ``all-drop`` imprecision step may likewise account for one extra
    ``inst`` (left endpoint) or ``gen`` (right endpoint) in the precise
    derivation.
    """

    if isinstance(imprecise.left, Star) or isinstance(imprecise.right, Star):
        return Alignment(True)
    left_imp = imprecision_evidence(env, precise.left, imprecise.left)
    right_imp = imprecision_evidence(env, precise.right, imprecise.right)
    if left_imp is None or right_imp is None:
        return Alignment(False, path, "child endpoints are not imprecise")
    if left_imp.ctor == "bot-elim" or right_imp.ctor == "bot-elim":
        return Alignment(True)
    if precise.ctor.startswith("bot-") or imprecise.ctor.startswith("bot-"):
        return Alignment(True)
    if (
        imp_contains(left_imp, "all-drop")
        or imp_contains(right_imp, "all-drop")
    ) and any(
        ctor in ("inst", "gen")
        for ctor in (precise.ctor, imprecise.ctor)
    ):
        return Alignment(True)
    if precise.ctor != imprecise.ctor:
        return Alignment(
            False,
            path,
            f"{precise.ctor} versus {imprecise.ctor}",
        )
    if len(precise.children) != len(imprecise.children):
        return Alignment(False, path, "different child counts")
    if not precise.children:
        return Alignment(True)
    if precise.ctor == "arrow":
        first = aligned(
            precise.children[0], imprecise.children[0], env, path + ".domain"
        )
        if not first.ok:
            return first
        return aligned(
            precise.children[1], imprecise.children[1], env, path + ".codomain"
        )
    if precise.ctor == "all":
        return aligned(
            precise.children[0],
            imprecise.children[0],
            imp_ext(env),
            path + ".body",
        )
    if precise.ctor == "inst":
        return aligned(
            precise.children[0],
            imprecise.children[0],
            imp_ext(env),
            path + ".inst",
        )
    if precise.ctor == "gen":
        return aligned(
            precise.children[0],
            imprecise.children[0],
            imp_ext(env),
            path + ".gen",
        )
    # A matching tag/check already has ★ at one less precise endpoint and was
    # discharged above. No other constructor has children.
    return Alignment(True)


# ---------------------------------------------------------------------------
# Exhaustive searches
# ---------------------------------------------------------------------------


def _quad_key(item: dict) -> tuple:
    values = item["types"]
    return (
        sum(type_size(value) for value in values),
        tuple(type_size(value) for value in values),
        tuple(type_key(value) for value in values),
    )


def _pair_key(pair: tuple[Type, Type]) -> tuple:
    left, right = pair
    return (
        type_size(left) + type_size(right),
        type_size(left),
        type_key(left),
        type_key(right),
    )


def _unordered_pair(left: Type, right: Type) -> tuple[Type, Type]:
    return (left, right) if type_key(left) <= type_key(right) else (right, left)


def search_context(depth: int, bound: int) -> dict:
    started = time.perf_counter()
    types = types_upto(depth, bound)
    cenv = identity_consistency_env(depth)
    ienv = identity_imp_env(depth)

    imp_targets: dict[Type, tuple[Type, ...]] = {
        left: tuple(right for right in types if imprecise(ienv, left, right))
        for left in types
    }
    canonical: dict[tuple[Type, Type], Evidence] = {}
    for left in types:
        for right in types:
            evidence = canonical_evidence(cenv, left, right)
            if evidence is not None:
                canonical[left, right] = evidence

    q1: list[dict] = []
    q1_candidates = 0
    for (left, right), evidence in canonical.items():
        for left_prime in imp_targets[left]:
            for right_prime in imp_targets[right]:
                evidence_prime = canonical.get((left_prime, right_prime))
                if evidence_prime is None:
                    continue
                q1_candidates += 1
                comparison = aligned(evidence, evidence_prime, ienv)
                if not comparison.ok:
                    q1.append(
                        {
                            "types": (left, left_prime, right, right_prime),
                            "precise": evidence,
                            "imprecise": evidence_prime,
                            "path": comparison.path,
                            "reason": comparison.reason,
                        }
                    )
    q1.sort(key=_quad_key)

    q2: dict[str, dict] = {}
    for policy in (OVERLAP_BAN, ALL_ALL_BAN):
        allowed: dict[tuple[Type, Type], Evidence] = {}
        for left in types:
            for right in types:
                evidence = canonical_evidence(cenv, left, right, policy)
                if evidence is not None:
                    allowed[left, right] = evidence

        failures: list[dict] = []
        candidates = 0
        for (left, right), evidence in allowed.items():
            for left_prime in imp_targets[left]:
                for right_prime in imp_targets[right]:
                    candidates += 1
                    if (left_prime, right_prime) not in allowed:
                        failures.append(
                            {
                                "types": (
                                    left,
                                    left_prime,
                                    right,
                                    right_prime,
                                ),
                                "precise": evidence,
                                "full_target": canonical.get(
                                    (left_prime, right_prime)
                                ),
                            }
                        )
        failures.sort(key=_quad_key)

        rejected = {
            _unordered_pair(left, right)
            for (left, right) in canonical
            if (left, right) not in allowed
        }
        rejected_pairs = sorted(rejected, key=_pair_key)
        q2[policy] = {
            "candidate_count": candidates,
            "failures": failures,
            "rejected_pairs": rejected_pairs,
            "ordered_rejected_count": sum(
                1 for pair in canonical if pair not in allowed
            ),
        }

    elapsed = time.perf_counter() - started
    return {
        "depth": depth,
        "bound": bound,
        "type_count": len(types),
        "consistency_pair_count": len(canonical),
        "imprecision_pair_count": sum(map(len, imp_targets.values())),
        "q1_candidate_count": q1_candidates,
        "q1": q1,
        "q2": q2,
        "seconds": elapsed,
    }


def _serial_type(ty: Type, depth: int) -> str:
    return pretty_type(ty, depth)


def serial_result(result: dict, max_examples: int | None = None) -> dict:
    depth = result["depth"]

    def cap(values: Sequence) -> Sequence:
        return values if max_examples is None else values[:max_examples]

    q1 = [
        {
            "A": _serial_type(item["types"][0], depth),
            "A_prime": _serial_type(item["types"][1], depth),
            "C": _serial_type(item["types"][2], depth),
            "C_prime": _serial_type(item["types"][3], depth),
            "evidence": pretty_evidence(item["precise"], depth),
            "evidence_prime": pretty_evidence(item["imprecise"], depth),
            "path": item["path"],
            "reason": item["reason"],
        }
        for item in cap(result["q1"])
    ]
    q2 = {}
    for policy, values in result["q2"].items():
        failures = [
            {
                "A": _serial_type(item["types"][0], depth),
                "A_prime": _serial_type(item["types"][1], depth),
                "C": _serial_type(item["types"][2], depth),
                "C_prime": _serial_type(item["types"][3], depth),
                "source_evidence": pretty_evidence(item["precise"], depth),
                "full_target_evidence": (
                    pretty_evidence(item["full_target"], depth)
                    if item["full_target"]
                    else None
                ),
            }
            for item in cap(values["failures"])
        ]
        rejected = [
            {
                "left": _serial_type(pair[0], depth),
                "right": _serial_type(pair[1], depth),
            }
            for pair in cap(values["rejected_pairs"])
        ]
        q2[policy] = {
            "candidate_count": values["candidate_count"],
            "failure_count": len(values["failures"]),
            "failures": failures,
            "ordered_rejected_count": values["ordered_rejected_count"],
            "unordered_rejected_count": len(values["rejected_pairs"]),
            "rejected_pairs": rejected,
        }
    return {
        "depth": depth,
        "bound": result["bound"],
        "type_count": result["type_count"],
        "consistency_pair_count": result["consistency_pair_count"],
        "imprecision_pair_count": result["imprecision_pair_count"],
        "q1_candidate_count": result["q1_candidate_count"],
        "q1_failure_count": len(result["q1"]),
        "q1": q1,
        "q2": q2,
        "seconds": round(result["seconds"], 6),
    }


# ---------------------------------------------------------------------------
# Regression examples and command line
# ---------------------------------------------------------------------------


IDENTITY = All(Arrow(Var(0), Var(0)))
LEFT_STAR_IDENTITY = All(Arrow(Var(0), STAR))


def self_test() -> None:
    empty: Env = ()
    assert shift(All(Arrow(Var(0), Var(1)))) == All(
        Arrow(Var(0), Var(2))
    )
    assert occurs(Arrow(Var(0), STAR), 0)
    assert not occurs(All(Var(0)), 0)

    identity_evidence = enumerate_evidence(empty, IDENTITY, IDENTITY)
    assert identity_evidence
    assert identity_evidence[0].ctor == "all"
    detours = [choice for choice in identity_evidence if is_syntactic_detour(choice)]
    # GTSFImp consistency has no sequencing rule: unlike GTNF's explicit
    # coercions, it cannot compose X~★ and ★~Y to derive X~Y here.
    assert not detours

    cross = (Mode.CROSS,)
    assert consistency(cross, Var(0), STAR)
    assert consistency(cross, STAR, Var(0))
    assert not consistency((Mode.XX,), Var(0), STAR)
    assert not consistency((Mode.XX,), STAR, Var(0))
    assert consistency((Mode.X_STAR,), Var(0), STAR)
    assert not consistency((Mode.X_STAR,), STAR, Var(0))
    assert not consistency((Mode.STAR_X,), Var(0), STAR)
    assert consistency((Mode.STAR_X,), STAR, Var(0))
    assert agda_lower(Var(0), STAR, depth=1) is None

    all_star = All(STAR)
    nested_outer = All(All(Var(1)))
    detour_only = enumerate_evidence(empty, all_star, nested_outer)
    assert detour_only and all(is_syntactic_detour(e) for e in detour_only)
    assert enumerate_evidence(empty, all_star, nested_outer, OVERLAP_BAN)
    assert not enumerate_evidence(empty, all_star, nested_outer, ALL_ALL_BAN)

    assert imprecise((), NAT, STAR)
    assert imprecise((), IDENTITY, IDENTITY)
    assert not imprecise((), STAR, NAT)

    examples = validation_examples()
    for left, right, expected in examples:
        actual = agda_lower(left, right)
        assert actual == expected, (
            pretty_type(left),
            pretty_type(right),
            pretty_type(actual) if actual else None,
            pretty_type(expected) if expected else None,
        )
        assert consistency(empty, left, right) == (expected is not None)


def validation_examples() -> tuple[tuple[Type, Type, Type | None], ...]:
    bottom = All(Var(0))
    all_star = All(STAR)
    dynamic_arrow = Arrow(STAR, STAR)
    return (
        (NAT, NAT, NAT),
        (NAT, BOOL, None),
        (NAT, STAR, NAT),
        (STAR, BOOL, BOOL),
        (Arrow(NAT, BOOL), dynamic_arrow, Arrow(NAT, BOOL)),
        (IDENTITY, IDENTITY, IDENTITY),
        (IDENTITY, dynamic_arrow, IDENTITY),
        (bottom, all_star, bottom),
        (all_star, bottom, bottom),
        (bottom, STAR, bottom),
        (LEFT_STAR_IDENTITY, IDENTITY, None),
        (All(All(Var(1))), All(All(Var(1))), All(All(Var(1)))),
    )


def print_validation() -> None:
    rows = []
    for left, right, expected in validation_examples():
        evidence = enumerate_evidence((), left, right)
        rows.append(
            {
                "left": pretty_type(left),
                "right": pretty_type(right),
                "lower": pretty_type(expected) if expected else None,
                "evidence_count": len(evidence),
                "canonical": pretty_evidence(evidence[0]) if evidence else None,
                "has_syntactic_detour": any(
                    is_syntactic_detour(choice) for choice in evidence
                ),
            }
        )
    closed = types_upto(0, 5)
    disagreements = []
    for left in closed:
        for right in closed:
            declarative = consistency((), left, right)
            selected = agda_lower(left, right) is not None
            if declarative != selected:
                disagreements.append(
                    {
                        "left": pretty_type(left),
                        "right": pretty_type(right),
                        "declarative": declarative,
                        "lower": selected,
                    }
                )
    print(
        json.dumps(
            {
                "normalization_examples": rows,
                "closed_crosscheck": {
                    "bound": 5,
                    "type_count": len(closed),
                    "pair_count": len(closed) ** 2,
                    "disagreements": disagreements,
                },
            },
            indent=2,
            ensure_ascii=False,
        )
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--validation", action="store_true")
    parser.add_argument("--search", action="store_true")
    parser.add_argument("--max-size", type=int, default=5)
    parser.add_argument(
        "--max-examples",
        type=int,
        default=None,
        help="limit displayed examples without limiting the search",
    )
    parser.add_argument(
        "--depths",
        type=int,
        nargs="*",
        default=(0, 1),
        help="context depths to search (the report uses 0 and 1)",
    )
    args = parser.parse_args()

    if args.self_test:
        self_test()
        print("self-test: OK")
    if args.validation:
        print_validation()
    if args.search:
        results = [search_context(depth, args.max_size) for depth in args.depths]
        print(
            json.dumps(
                [serial_result(result, args.max_examples) for result in results],
                indent=2,
                ensure_ascii=False,
            )
        )
    if not (args.self_test or args.validation or args.search):
        parser.print_help()


if __name__ == "__main__":
    main()
