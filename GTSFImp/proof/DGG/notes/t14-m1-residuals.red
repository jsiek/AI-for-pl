# T14 M1 residuals

Scope: D15 migration stage M1, covering the core CTI2-adjacent
projection/transport tier and the low-level inversion/probe tier only.

## Residual R1. `TerminusRebuildProbe.InstanceB.tagged-input`

The old witness used the removed source-only occupied `seal X ★`
name-protected route:

```agda
CTI2.conceal⊑²
  (CTI2.seal-partner-ok CTI2.name-protected-target)
  (mono-refl {W = W}) (CTI2.tag-rebase-varᴸ rb-X-Y)
  CTI2.same-[] source-seal-⊢ premise-casts² X⊑★-W
```

Under D15, the source-only `seal X ★` opening rule is available only
through `conceal⊑²-seal-star-open`, which requires
`NoTargetOccupantAtSource W X`.  Instance B is intentionally occupied:
`Y` is aligned with source `X` in `W`, so the occupancy gate is closed.

The matched-chain pieces remain checked in `TerminusRebuildProbe`:

- the inner source/target `seal X ★` to `seal Y₂ ★` pairing through
  `conceal⊑conceal²`;
- the outer target-only `seal Y (＇ Y₂)` chain through `⊑conceal²`;
- the casted premise `premise-casts²`.

Reassembling the old final tagged endpoint requires the later
source-star package migration rather than a narrow M1 transport edit.
The checked old direct witness was therefore removed from the probe.

## Stage-Deferred Legacy Coverage

The tier-1 transport modules and low-level inversion modules still have
totality branches for the legacy `conceal⊑²` constructor because the
constructor itself is not deleted until the final migration stage.  These
branches preserve coverage only; new M1 construction sites were moved to
`conceal⊑²-source-ok` or routed to the residual above.
