# GTLC/agda note

This directory contains the Agda development for GTLC, its cast-calculus
compilation target, and gradual-guarantee metatheory.

## Public/audited surface (`GTLC/agda/`)

The top-level files are the trust-facing API: language definitions and theorem
statements/wrappers.

- `Types.agda`: type grammar, consistency, precision, and helper lemmas.
- `Contexts.agda`: contexts, lookup, and context precision.
- `GTLC.agda`: source language terms, typing, and precision.
- `Coercions.agda`: coercion language used by compilation.
- `CastCalculus.agda`: cast-calculus terms, typing, and reduction.
- `Compile.agda`: compilation from GTLC typing derivations.
- `MetaTheory.agda`: public theorem statements for cast type safety, GTLC type
  safety (via compilation), and static/dynamic gradual guarantees.
- `All.agda`: aggregate driver for checking the public surface.

Compatibility wrappers are also provided:

- `StaticGradualGuarantee.agda`
- `DynamicGradualGuarantee.agda`

## Private proof implementation (`GTLC/agda/proof/`)

Proof scripts and implementation details live in `proof/`.

- `proof/StaticGradualGuarantee.agda`
- `proof/DynamicGradualGuaranteeCore.agda`
- `proof/DynamicGradualGuarantee.agda`
- `proof/CastSafety.agda`
- `proof/TypeSafety.agda`
- `proof/CastCalculusMeta.agda`
- `proof/CompileMeta.agda`

Work-in-progress modules are isolated in `proof/wip/` and are intentionally not
part of the public check driver.

## Checks

From `GTLC/agda/`:

- `make agda`: runs `agda -v0 All.agda`.
- `make postulate-check`: checks top-level and `proof/*.agda` for `postulate`
  and interaction holes.
- `make check`: runs both checks.
