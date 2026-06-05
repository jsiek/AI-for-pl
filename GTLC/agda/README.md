# GTLC/agda note

This directory contains the Agda development for GTLC, its cast-calculus
compilation target, and gradual-guarantee metatheory.

## Public/audited surface (`GTLC/agda/`)

The top-level files are the trust-facing API: language definitions and theorem
statements.

- `Types.agda`: type grammar, consistency, precision, and helper lemmas.
- `Contexts.agda`: contexts, lookup, context precision, and source context
  imprecision.
- `GTLC.agda`: source language terms, typing, and precision.
- `Coercions.agda`: coercion language used by compilation, including public
  coercion reduction/equivalence vocabulary and the structural normal-form
  grammar (`_⇨ⁿ_`, `_⇨ᵗ_`, `_⇨ᵐ_`) used to state normalization.
- `CastCalculus.agda`: cast-calculus terms, typing, and reduction.
- `Compile.agda`: compilation from GTLC typing derivations.
- `DynamicGradualGuaranteeDefinitions.agda`: public source runtime
  observations used to state the dynamic gradual guarantee.
- `MetaTheory.agda`: public theorem statements for coercion normalization,
  cast type safety, GTLC type safety (via compilation), and static/dynamic
  gradual guarantees. The coercion-normalization theorem states that every
  well-typed coercion reduces, up to coercion equivalence, to a structural
  coercion normal form. A separate public theorem states that structural
  coercion normal forms are irreducible.
- `All.agda`: aggregate driver for checking the public surface.

## Private proof implementation (`GTLC/agda/proof/`)

Proof scripts and implementation details live in `proof/`.

- `proof/StaticGradualGuarantee.agda`
- `proof/StaticGradualGuaranteeDefinitions.agda`
- `proof/DynamicGradualGuaranteeCore.agda`
- `proof/DynamicGradualGuarantee.agda`
- `proof/CastSafety.agda`
- `proof/TypeSafety.agda`
- `proof/CastCalculusMeta.agda`
- `proof/CompileMeta.agda`
- `proof/CoercionReduction.agda`: quotiented coercion syntax, reduction, and
  quotient normalizer used internally by the coercion-normalization proof.
- `proof/CoercionEquality.agda`: quotient equality lemmas used internally by
  coercion normalization.
- `proof/CoercionNormalization.agda`: private implementation of coercion
  normalization, including the bridge between coercions and quotiented
  coercions.

Work-in-progress modules are isolated in `proof/wip/` and are intentionally not
part of the public check driver.

## Checks

From `GTLC/agda/`:

- `make agda`: runs `agda -v0 All.agda`.
- `make postulate-check`: checks top-level and `proof/*.agda` for `postulate`
  and interaction holes.
- `make check`: runs both checks.
