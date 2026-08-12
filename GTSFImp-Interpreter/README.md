# `GTSFImp-Interpreter`

This sibling of `GTSF-Interpreter` reuses the intrinsic cast language and
proof-carrying evaluator in `GTSFImp/`. It does not duplicate the reduction
engine.

The port currently contains:

- `Interpreter.agda`: fuel-bounded return/blame outcomes and LR entry points;
- `NarrowWiden.agda`: polarized widening and narrowing derivations;
- `proof/NarrowWidenIsomorphism.agda`: mutually inverse translations, with
  both round trips proved, between `Imprecision` and each polarization;
- `LR/World.agda`: paired fresh world extensions and lifting through futures;
- `LR/Computation.agda`: the three directed DGG observations;
- `LR/LogicalRelation.agda`: a step-indexed LR indexed canonically by
  `Imprecision`, plus `ValueNarrowing` obtained by reindexing through the
  derivation isomorphism;
- `LR/DynamicPayload.agda`: base, function, variable, and universal ground
  introduction cases for `DynamicPayloadRelated`.

## Why imprecision and narrowing give the same LR index

For `p : μ ⊢ Aᴾ ⊑ Aᴵ`, the narrowing endpoint order is reversed:

```text
Imprecision μ Aᴾ Aᴵ   ≅   Narrowing μ Aᴵ Aᴾ
```

At functions, an imprecision domain premise is converted to a `Widening`
premise inside `Narrowing`; converting that premise back recovers the original
imprecision derivation. Thus narrowing is contravariantly *presented*, while
the complete derivation tree is isomorphic to covariant imprecision. The four
round-trip proofs make this stronger than mere equivalence of inhabitation.

The logical relation uses `Imprecision` as its canonical structural index and
defines `ValueNarrowing` by the inverse half of this isomorphism. This avoids
duplicating the semantic clauses without choosing a weaker theorem.

## Deliberate draft boundaries

The structural clauses are complete for `★ ⊑ ★`, ordinary functions, and
paired universals. The other gradual constructors currently impose endpoint
valuehood and typing only. In particular, universal-to-non-universal cases can
allocate on just one side. `PairedReturns` intentionally exposes the present
restriction that two successful evaluations end in one shared type-context
size; finishing those cases needs an asymmetric world alignment rather than a
silent transport.

Run `make -C GTSFImp-Interpreter check` from the repository root.
