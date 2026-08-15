# NS-4 stage 1v resister: strict-view delegate is outside the worker surface

Date: 2026-08-15

Status: resolved.

The residual-tail continuation route requested for stage 1v is now landed as a
live checked field on `StructuralNameChainPlan`:

```agda
residual-tail-child :
  ...
  → (V ⟨ c ⟩) —↠[ χs ] N
  → W′ ∣ ECR.mapCtxᴿ ext γ ⊢²
      M ⊑ N ∶ ECR.transport⊑ᵂ ext qC
  → StructuralTargetInstantiationPackage W V (cast-frame c ▻ⁱ spine)
  → Σ[ child-spine ∈
        InstantiationSpine (applyTys χs C) (applyTys χs E) ]
    Σ[ child-plan ∈
        StructuralNamePostPlan W′ A (applyTys χs E)
          (ECR.transport⊑ᵂ ext q) ]
    Σ[ child-chain-plan ∈
        StructuralNameChainPlan {fuel = fuel} W′
          (ECR.mapCtxᴿ ext γ) A (applyTys χs E)
          (ECR.transport⊑ᵂ ext q) child-plan ]
    Σ[ child-chain ∈
        TargetFrameAbsorptionChain W′ (ECR.mapCtxᴿ ext γ)
          A child-spine (ECR.transport⊑ᵂ ext q) ]
    Σ[ child-typed ∈ SpineTypedʷ {fuel = fuel} W′ child-spine ]
    Σ[ child-target ∈
        StructuralTargetInstantiationPackage W′ N child-spine ]
      pendingCastMass vN child-spine <
        pendingCastMass vV (cast-frame c ▻ⁱ spine)
      ×
      (child recursive final relation → caller final relation)
```

This is the generator-supplied recursive continuation shape: after
`residual-cast-stop-package` discharges the residual cast, the worker can recur
on `N`, `child-spine`, `child-plan`, `child-chain-plan`, `child-chain`,
`child-typed`, and `child-target`, using the supplied strict
`pendingCastMass` decrease.  The final function is the caller-trace alignment
from the generated residual discharge and tail replay back to the original
target package.

## Blocking mismatch

The remaining obstacle is not the residual tail.  The exact public worker
surface is still:

```agda
StructuralNameInstantiationᵀ =
  ... →
  StructuralNamePostPlan W A E q →
  StructuralNameChainPlan {fuel = fuel} W γ A E q plan →
  W ∣ γ ⊢² M ⊑ V ∶ p →
  Value M →
  Value V →
  AllValueView V →
  ... →
  StructuralTargetInstantiationPackage W V
    (name-type-app-frame B X refl refl ▻ⁱ spine) →
  ...
```

The stage-1t ruling deliberately delegates strict target-head cases to the
five higher-order strict-view surfaces:

```agda
StructuralStrictViewSurfaces.Λ-cell
StructuralStrictViewSurfaces.∀-cast-cell
StructuralStrictViewSurfaces.gen-cell
StructuralStrictViewSurfaces.reveal-cell
StructuralStrictViewSurfaces.conceal-cell
```

Those surfaces are live statements in
`StructuralStrictViewSurfaceDef.agda`, but they are not fields of
`StructuralNameChainPlan`, and they are not arguments of
`StructuralNameInstantiationᵀ`.  Therefore an exact closed inhabitant of
`StructuralNameInstantiationᵀ` cannot call the delegated strict cases without
either:

1. changing the worker surface so it receives `StructuralStrictViewSurfaces`;
2. moving equivalent strict-child fields into the hereditary chain-plan
   package; or
3. proving the five strict children directly in the worker, which contradicts
   the stage-1t delegation boundary.

The public value adapter still composes with the current worker signature
because the signature itself was not changed.  It remains a thin call through
`erase-structural-name-root`.

No live term-imprecision relation, reduction relation, M4 Def surface,
`InstSpineDescentPackage`, `CatchupCast⁻` constructor, or public adapter was
weakened.  No postulate, hole, or catch-all case was added.

RESOLVED postscript, 2026-08-15
--------------------------------

The signature obstruction recorded here is closed in live Agda:

- `StructuralNameInstantiationᵀ` now receives the
  `StructuralStrictViewSurfaces` bundle.
- `StructuralValueInstantiationᵀ` receives the same bundle and passes it
  through to the name worker.
- `StructuralStrictViewSurfaces` includes `conceal-equal-ok :
  StructuralNameConcealEqualOKᵀ`.
- The equal-helper skeletons in
  `StructuralNameInstantiationProof.agda` thread the bundle through recursive
  worker calls and use `conceal-equal-ok` for source conceal replay.

The next open worker blocker is not the strict-view surface argument.  It is
the non-name `safe-inst` residual stop data recorded in
`ns4-stage-1w-safe-inst-residual-bound-resister.red`.


FINAL RESOLVED postscript, 2026-08-15
-------------------------------------

The successor safe-inst residual blocker is closed.  The worker consumes the
`cast-safe` parent bound/provenance data and constructs the typed safe-inst
child with the generated residual `↑ᶜ (close-instᶜ c)`.

`StructuralNameInstantiationᵀ` is now inhabited by the checked worker in
`StructuralNameInstantiationProof.agda`.
