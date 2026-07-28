#!/usr/bin/env python3
"""Audit strict DGG import cones and importer-free proof modules."""

from __future__ import annotations

import re
import sys
from collections import deque
from pathlib import Path


GTSF_ROOT = Path(__file__).resolve().parent.parent

# These are the canonical strict checks whose entire local import cones must
# remain free of permissive Agda options.
STRICT_DGG_ROOT_MODULES = (
    "DynamicGradualGuarantee",
    "proof.DGG.Core.NuDGGStrictSpine",
    "proof.DGG.Core.NuDGGUnassembledProofsStrictSpine",
    "proof.DGG.TerminalBackward.NuDGGTerminalBackwardStrictSpine",
    "proof.DGG.TerminalForward.NuDGGTerminalForwardStrictSpine",
)

# These spines inventory strict-looking `Proof` modules that do not yet feed a
# canonical `Lemma`, including focused subarchitectures that are not themselves
# public DGG roots. A focused Agda check, not membership here, establishes that
# an inventory spine is actually complete.
STRICT_PROOF_INVENTORY_ROOT_MODULES = (
    "proof.DGG.Core.NuDGGStrictSpine",
    "proof.DGG.Core.NuDGGUnassembledProofsStrictSpine",
    "proof.DGG.TerminalBackward.NuDGGTerminalBackwardStrictSpine",
    "proof.DGG.TerminalForward.NuDGGTerminalForwardStrictSpine",
    "proof.PairedLambda.Terminal."
    "NuImprecisionPairedTargetClosingStrictSpine",
    "proof.Right.SourceAll.ClosingValues."
    "NuImprecisionRightSourceAllStrictSpine",
)

# These importer-free `Proof` modules look complete to a source-only audit but
# currently fail strict Agda checking against the canonical definitions.  They
# are deliberately excluded from the completed-proof aggregate until their
# recorded proof obligations are repaired.
KNOWN_INCOMPLETE_PROOF_MODULES = (
    "proof.DGG.TerminalForward."
    "NuDGGTerminalForwardIntegrationProof",
)

# These modules are intentionally checked or read as independent roots.  Keep
# this list explicit: naming conventions alone do not establish that a module
# is still a useful regression, counterexample, example, or integration root.
INTENDED_STANDALONE_ROOT_MODULES = (
    *STRICT_DGG_ROOT_MODULES,
    "proof.Compilation.CompileDynamicApplicationTest",
    "proof.Compilation.GenSafeMismatchBlameRegression",
    "proof.Core.Permutation.ForallPermutationTest",
    "proof.DGG.Design.EndpointMLBSelectedRouteShapeSquareCounterexample",
    "proof.EndpointMLB.Core.EndpointCanonicalMLBTest",
    "proof.EndpointMLB.Core.MLBGlbCounterexample",
    "proof.EndpointMLB.Core.MLBGlbExample",
    "proof.EndpointMLB.Core.MlbTypeTest",
    "proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleFactorCounterexample",
    "proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleTest",
    "proof.PairedLambda.Conversions."
    "NuImprecisionPairedLambdaTargetClosing"
    "LambdaLambdaConversionRotationCounterexample",
    "proof.PairedLambda.Core."
    "NuImprecisionPairedLambdaTargetClosingRelationCounterexample",
    "proof.PairedLambda.Terminal."
    "NuImprecisionPairedTargetClosingStrictSpine",
    "proof.Quotient.NuImprecisionQuotientToOrdinaryCounterexample",
    "proof.Right.Core."
    "NuImprecisionRightOpenedInstantiationIndexCounterexample",
    "proof.Right.SourceAll.ClosingValues."
    "NuImprecisionRightSourceAllStrictSpine",
    "proof.Source.CastSequence."
    "NuImprecisionSourceCastSequenceMidpointCounterexample",
    "proof.Source.Core."
    "NuImprecisionSourceGenTargetGroundAgreementCounterexample",
    "proof.Source.Core."
    "NuImprecisionSourceOnlyContextFactorCounterexample",
    "proof.Source.SealTag."
    "NuImprecisionSourceSealCancellationCounterexample",
    "proof.WorldCoherent.Right.Target.WidenNarrow."
    "NuImprecisionWorldCoherentRightTargetNarrowUntagRootCounterexample",
    "proof.WorldCoherent.Right.Target.WidenNarrow."
    "NuImprecisionWorldCoherentRightTargetWidenInstantiation"
    "PairedPostBetaCatchupRegression",
)

IMPORT_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])(?:open\s+)?import\s+"
    r"([A-Za-z][A-Za-z0-9_.-]*)"
)
OPTIONS_RE = re.compile(r"\{\-\#\s*OPTIONS\b(.*?)\#-\}", re.DOTALL)
PERMISSIVE_OPTIONS = (
    "--allow-incomplete-matches",
    "--allow-unsolved-metas",
)


def agda_files() -> list[Path]:
    """Return canonical GTSF .agda files in stable order."""
    files = list(GTSF_ROOT.glob("*.agda"))
    files.extend((GTSF_ROOT / "proof").rglob("*.agda"))
    return sorted(
        (path.relative_to(GTSF_ROOT) for path in files),
        key=lambda path: path.as_posix(),
    )


def module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def strip_comments_and_strings(source: str) -> str:
    """Keep code and pragmas while blanking nested comments and strings."""
    result: list[str] = []
    index = 0
    block_depth = 0

    while index < len(source):
        if block_depth:
            if source.startswith("{-", index):
                block_depth += 1
                result.extend("  ")
                index += 2
            elif source.startswith("-}", index):
                block_depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
            continue

        if source.startswith("{-#", index):
            end = source.find("#-}", index + 3)
            if end == -1:
                result.append(source[index:])
                break
            end += 3
            result.append(source[index:end])
            index = end
        elif source.startswith("--", index):
            end = source.find("\n", index + 2)
            if end == -1:
                result.extend(" " * (len(source) - index))
                break
            result.extend(" " * (end - index))
            index = end
        elif source.startswith("{-", index):
            block_depth = 1
            result.extend("  ")
            index += 2
        elif source[index] == '"':
            result.append(" ")
            index += 1
            while index < len(source):
                if source[index] == "\\" and index + 1 < len(source):
                    result.extend("  ")
                    index += 2
                elif source[index] == '"':
                    result.append(" ")
                    index += 1
                    break
                else:
                    result.append("\n" if source[index] == "\n" else " ")
                    index += 1
        else:
            result.append(source[index])
            index += 1

    return "".join(result)


def enabled_permissive_options(source: str) -> tuple[str, ...]:
    flags: set[str] = set()
    for options in OPTIONS_RE.findall(source):
        words = options.split()
        flags.update(flag for flag in PERMISSIVE_OPTIONS if flag in words)
    return tuple(sorted(flags))


def import_path(
    graph: dict[str, tuple[str, ...]], root: str, target: str
) -> tuple[str, ...]:
    queue = deque([root])
    parent: dict[str, str | None] = {root: None}

    while queue:
        current = queue.popleft()
        if current == target:
            path: list[str] = []
            while current is not None:
                path.append(current)
                current = parent[current]  # type: ignore[assignment]
            return tuple(reversed(path))
        for imported in graph[current]:
            if imported not in parent:
                parent[imported] = current
                queue.append(imported)

    raise AssertionError(f"{target} is not reachable from {root}")


def reachable_modules(
    graph: dict[str, tuple[str, ...]], root: str
) -> tuple[str, ...]:
    seen: set[str] = set()
    pending = [root]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        pending.extend(reversed(graph[current]))
    return tuple(sorted(seen))


def main() -> int:
    paths = agda_files()
    path_by_module = {module_name(path): path for path in paths}
    if len(path_by_module) != len(paths):
        print("error: duplicate local Agda module names", file=sys.stderr)
        return 1

    graph: dict[str, tuple[str, ...]] = {}
    permissive: dict[str, tuple[str, ...]] = {}
    sources: dict[str, str] = {}
    unresolved_local_imports: dict[str, tuple[str, ...]] = {}
    for module, path in sorted(path_by_module.items()):
        source = strip_comments_and_strings(
            (GTSF_ROOT / path).read_text(encoding="utf-8")
        )
        sources[module] = source
        imports = set(IMPORT_RE.findall(source))
        graph[module] = tuple(
            sorted(
                {
                    imported
                    for imported in imports
                    if imported in path_by_module and imported != module
                }
            )
        )
        unresolved = tuple(
            sorted(
                imported
                for imported in imports
                if imported.startswith("proof.")
                and imported not in path_by_module
            )
        )
        if unresolved:
            unresolved_local_imports[module] = unresolved
        flags = enabled_permissive_options(source)
        if flags:
            permissive[module] = flags

    missing_strict = sorted(
        set(STRICT_DGG_ROOT_MODULES).difference(path_by_module)
    )
    missing_intended = sorted(
        set(INTENDED_STANDALONE_ROOT_MODULES).difference(path_by_module)
    )
    missing_incomplete = sorted(
        set(KNOWN_INCOMPLETE_PROOF_MODULES).difference(path_by_module)
    )
    missing_inventory = sorted(
        set(STRICT_PROOF_INVENTORY_ROOT_MODULES).difference(path_by_module)
    )
    if (
        missing_strict
        or missing_intended
        or missing_incomplete
        or missing_inventory
    ):
        for module in missing_strict:
            print(f"error: strict DGG root is missing: {module}", file=sys.stderr)
        for module in missing_intended:
            print(
                f"error: intended standalone root is missing: {module}",
                file=sys.stderr,
            )
        for module in missing_incomplete:
            print(
                f"error: known incomplete Proof module is missing: {module}",
                file=sys.stderr,
            )
        for module in missing_inventory:
            print(
                f"error: strict Proof inventory root is missing: {module}",
                file=sys.stderr,
            )
        return 1

    print("Local proof import resolution:")
    if unresolved_local_imports:
        for importer, unresolved in unresolved_local_imports.items():
            print(f"  FAIL {importer}")
            for imported in unresolved:
                print(f"    missing {imported}")
    else:
        print("  PASS (all proof.* imports resolve)")

    print()
    print("Strict DGG import safety:")
    unsafe_count = 0
    for root in STRICT_DGG_ROOT_MODULES:
        reachable = reachable_modules(graph, root)
        unsafe = [module for module in reachable if module in permissive]
        if not unsafe:
            print(f"  PASS {root} ({len(reachable)} local modules)")
            continue

        unsafe_count += len(unsafe)
        print(f"  FAIL {root} ({len(unsafe)} permissive imports)")
        for module in unsafe:
            flags = ", ".join(permissive[module])
            chain = " -> ".join(import_path(graph, root, module))
            print(f"    {module}: {flags}")
            print(f"      via {chain}")

    importers: dict[str, set[str]] = {
        module: set() for module in path_by_module
    }
    for importer, imports in graph.items():
        for imported in imports:
            importers[imported].add(importer)

    intended = set(INTENDED_STANDALONE_ROOT_MODULES)
    known_incomplete = set(KNOWN_INCOMPLETE_PROOF_MODULES)
    imported_incomplete = [
        module
        for module in KNOWN_INCOMPLETE_PROOF_MODULES
        if importers[module]
    ]
    lemma_cone: set[str] = set()
    for module, path in path_by_module.items():
        if path.name.endswith("Lemma.agda"):
            lemma_cone.update(reachable_modules(graph, module))

    inventory_cone: set[str] = set()
    for root in STRICT_PROOF_INVENTORY_ROOT_MODULES:
        inventory_cone.update(reachable_modules(graph, root))

    strict_proofs = {
        module
        for module, path in sorted(path_by_module.items())
        if path.name.endswith("Proof.agda")
        and module not in permissive
        and "{!" not in sources[module]
        and not re.search(r"(?:^|\n)\s*postulate\b", sources[module])
    }
    without_lemma = strict_proofs.difference(lemma_cone)
    unaggregated_proofs = sorted(
        module
        for module in without_lemma
        if module not in inventory_cone
        and module not in known_incomplete
    )
    candidates = [
        module
        for module, path in sorted(path_by_module.items())
        if path.parts[0] == "proof"
        and not importers[module]
        and module not in intended
        and module not in known_incomplete
    ]

    print()
    print("Known incomplete strict Proof modules (excluded from aggregate):")
    for module in KNOWN_INCOMPLETE_PROOF_MODULES:
        print(f"  {path_by_module[module].as_posix()}")
        if importers[module]:
            joined = ", ".join(sorted(importers[module]))
            print(f"    FAIL unexpectedly imported by: {joined}")

    print()
    print("Proof modules with zero in-repo importers (review candidates):")
    if candidates:
        for module in candidates:
            print(f"  {path_by_module[module].as_posix()}")
    else:
        print("  (none)")

    print()
    print(
        "Strict-looking Proof modules with no Lemma consumer "
        "and no inventory spine:"
    )
    if unaggregated_proofs:
        for module in unaggregated_proofs:
            print(f"  {path_by_module[module].as_posix()}")
    else:
        print("  (none)")

    print()
    print("Proof inventory coverage:")
    print(f"  {len(strict_proofs)} strict-looking Proof modules")
    print(f"  {len(without_lemma)} without a transitive Lemma consumer")
    print(
        f"  {len(without_lemma.intersection(inventory_cone))} "
        "covered by a strict inventory spine"
    )
    print(
        f"  {len(without_lemma.intersection(known_incomplete))} "
        "known incomplete and explicitly excluded"
    )

    print()
    print(
        "Summary: "
        f"{len(STRICT_DGG_ROOT_MODULES)} strict roots, "
        f"{sum(map(len, unresolved_local_imports.values()))} "
        "unresolved local imports, "
        f"{unsafe_count} unsafe root/module pairs, "
        f"{len(KNOWN_INCOMPLETE_PROOF_MODULES)} known incomplete Proof modules, "
        f"{len(candidates)} review candidates, "
        f"{len(unaggregated_proofs)} uninventoried Proof modules"
    )
    return 1 if (
        unresolved_local_imports
        or unsafe_count
        or imported_incomplete
        or unaggregated_proofs
    ) else 0


if __name__ == "__main__":
    sys.exit(main())
