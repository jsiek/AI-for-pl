# T14 M2 residuals

Scope: D15 migration stage M2, covering the middle target-chain and
source-strip consumers plus the catchup structural endpoint helpers.

## Carried residual R1. `TerminusRebuildProbe.InstanceB.tagged-input`

The M1 residual remains blocked after the source-star package pass.  The
needed endpoint is still an occupied source-only `seal X ★` opening:

```agda
CTI2.conceal⊑²
  (CTI2.seal-partner-ok CTI2.name-protected-target)
  (mono-refl {W = W}) (CTI2.tag-rebase-varᴸ rb-X-Y)
  CTI2.same-[] source-seal-⊢ premise-casts² X⊑★-W
```

D15 admits source-only `seal X ★` only through
`conceal⊑²-seal-star-open`, which requires
`NoTargetOccupantAtSource W X`.  Instance B intentionally has target
`Y` aligned with source `X`, so that occupancy premise is false.  The
matched inner chain remains checked, but it does not reconstruct this
old occupied source-only wrapper without a different matched-package
surface.

## Residual R2. `SealTransferCore.seal-transfer`

`seal-transfer` still has a dynamic stripped branch that rebuilds:

```agda
CTI2.conceal⊑²
  (CTI2.seal-partner-ok (seal-ok {P = P}))
```

This branch consumes an abstract `SealPartnerOK` from the target-strip
route.  The local data are not enough to split it into the D15
alternatives: source-only `seal X ★` needs an explicit
`NoTargetOccupantAtSource`, while non-star source seals need a
`SourceConcealOK` endpoint.  Converting this branch requires a split
target-strip endpoint interface rather than a constructor swap.

## Residual R3. `TargetChainProof.target-source-star-at`

The direct source-star/name-protected branch now routes to the payload
case.  Four recursive re-emission branches still synthesize the old
occupied source-only wrapper around residual target-chain data:

```agda
CTI2.conceal⊑²
  (CTI2.seal-partner-ok CTI2.name-protected-target)
```

These branches are exactly the occupied source-star cases excluded from
`conceal⊑²-seal-star-open`.  They need a richer matched source-star
package route that preserves the residual/payload square, not a local
no-target transport.

## Residual R4. `SourceStripProof.source-tag-seal-core-tagged`

The `★` target-strip data re-emitter still builds the same old
name-protected source-only wrapper.  The target-strip package exposes
the boundary, target seal membership, premise, and re-emitter, but it
does not expose `NoTargetOccupantAtSource`, and `conceal⊑²-source-ok`
is inapplicable because the source seal payload is `★`.

## Residual R5. Structural name-instantiation source replay

`StructuralCatchupRightDef` now has checked structural catchup helpers
for `conceal⊑²-seal-star-open` and `conceal⊑²-source-ok`.  The broader
`StructuralNameInstantiationProof` replay path still has only the old
abstract `SourceConcealPartnerOK` surface.  Isolated checking of that
module timed out without diagnostics, so the surface expansion was not
attempted in M2.  Converting it requires a narrow source-ok/no-target
surface through `StructuralStrictViewSurfaces`.
