# NS-4 stage 1q resister: residual discharge provenance at segment stop

Date: 2026-08-14

Status: resolved for the amended stop/discharge interface.  General worker
assembly remains open under stage 1r.

What landed in live Agda:

- `CastFrameClass` is fuel-indexed and includes the stop marker
  `cast-residual : suc (castSize c) < fuel → CastFrameClass c`.
- `spine-typed-inst-child` builds the generated safe-inst child spine and
  marks `↑ᶜ (close-instᶜ c)` as a residual stop using the supplied strict
  bound.
- `StructuralNameInstantiationᵀ` and `StructuralValueInstantiationᵀ` now take
  the fuel-knot arguments:

```agda
FuelStepSurface fuel
Catchup⁻Embedᵀ
inst-alloc-decreaseᵀ
```

The exact fuel-discharge surface intended at a stop is:

```agda
FuelStepSurface.smaller-extra fuel-step residual<fuel
```

where:

```agda
residual<fuel : suc (castSize residual-cast) < fuel
```

This gives `ExtraCastRightAt (suc (castSize residual-cast))`, and the
residual call then uses:

```agda
n<1+n (castSize residual-cast)
```

as the cast-size argument required by `ExtraCastRightAt`.

Resister
--------

The generic residual-stop continuation has the fuel bound, but the live
extra-cast surface also requires cast provenance at the current value:

```agda
ECR.CatchupCast {W = W} {A = A} p M′ residual-cast q
```

The available embedding argument has type:

```agda
Catchup⁻Embedᵀ
```

so the worker can build the full `CatchupCast` only if it also has:

```agda
CatchupCast⁻ {W = W} {A = A} p residual-cast q
```

The current segmented stop marker carries only:

```agda
suc (castSize residual-cast) < fuel
```

and the current `TargetFrameAbsorptionChain.tfa-cast` carries the post-cast
endpoint and tail chain, but not `CatchupCast⁻` provenance.  Therefore the
worker cannot make the generic residual-discharge call without inventing
provenance or reshaping an existing surface.

For the generated safe-inst residual specifically, the needed provenance is
morally the existing `inst-residual-provenance` route:

```agda
CatchupCast⁻ p (↑ᶜ (close-instᶜ c′)) q
```

but the generic segment stop no longer retains that generation-site evidence.
Adding it to `cast-residual` would violate the supervisor ruling that the stop
marker carry only the fuel bound.  Changing `ExtraCastRightAt` would reshape
M4's live Def surface.  This chunk therefore stops at the interface gap.

Consequence
-----------

The target segment status is:

- β/name, type transport, reveal/conceal administration: supported by the
  existing typed-spine and target-step/decomposition infrastructure.
- generated `Λ`, `∀`, `gen`, reveal, conceal child spines: typed surfaces are
  live.
- generated safe-inst residual: typed and marked as a stop.
- residual discharge and worker assembly: blocked until the continuation has
  a `CatchupCast⁻` source for the stopped residual, without changing M4's
  `ExtraCastRightAt` Def.

No live relation was changed, and no postulate, hole, catch-all, or weakened
statement was added.


AMENDED RESOLUTION postscript, 2026-08-15
-----------------------------------------

The supervisor-amended stop interface is now live in:

`GTSFImp/proof/DGG/Catchup/StructuralSpineTypingDef.agda`

The residual stop carries both the strict fuel bound and a provenance family:

```agda
ResidualFrameProvenance c =
  ∀ {χs W Aₛ p q} →
    CatchupCast⁻ p (applyConsistencies χs c) q
```

```agda
cast-residual :
    suc (castSize c) < fuel
  → ResidualFrameProvenance c
  → CastFrameClass c
```

The discharge call requested in this note is checked in:

`GTSFImp/proof/DGG/Catchup/StructuralInstantiationDescentProof.agda`

as `residual-cast-stop-package`.  It calls:

```agda
FuelStepSurface.smaller-extra fuel-step residual<fuel
  rel vM vV c (n<1+n (castSize c)) q
  (catchup⁻-embed _ (prov {χs = []} {p = p} {q = q}))
```

This closes the original interface gap without changing M4's live Def
surfaces.  The structural worker still cannot be assembled completely: the
opened `∀` residual provenance site is tracked separately in
`ns4-stage-1r-opened-all-provenance-resister.red`.
