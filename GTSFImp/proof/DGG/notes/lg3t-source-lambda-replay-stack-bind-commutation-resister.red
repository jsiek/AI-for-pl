# LG-3t source-Λ replay stack bind-commutation resister

Date: 2026-08-17

Status:

- Checked chunk `6fcba292` adds the internal
  `StructuralCatchupRightPayload` alias, `SourceΛReplayStack`, and
  `source-Λ-stack-unlift`.
- `StructuralWorldEvidenceProof` now exposes the target-context/store equalities
  used by source-Λ replay:
  `liftCtxᴸ-target-ctx`, `smartCommaLift-target-store`, and
  `smartLiftCtxᴸ-target-ctx`.
- The required gate passed:
  `cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check`
  with `postulate-check: OK (no postulates; NON_COVERING at legacy baseline)`.

## Remaining missing datum

The stack certificate now has a finite fold, but the value worker still cannot
assemble the source-Λ rows because the target-bind rows have no checked
commutation over an arbitrary pending source-binder stack.

The missing theorem is a stack child construction of this shape:

```agda
source-Λ-stack-target-bind-child :
  SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → (ins₀ : TE.TargetInsert wk↪ᵗ π₀ W₀ W₀¹)
  → (follows₀ : CTI2.targetStoreʷ W₀¹ ≡
      applyStores (bind R ∷ []) (CTI2.targetStoreʷ W₀))
  → (ins : TE.TargetInsert wk↪ᵗ π W W¹)
  → (follows : CTI2.targetStoreʷ W¹ ≡
      applyStores (bind R ∷ []) (CTI2.targetStoreʷ W))
  → SourceΛReplayStack
      W₀¹ (ECR.mapCtxᴿ (target-insert-bind-world-extendᴿ ins₀ follows₀) γ₀)
      M₀
      (ECR.transport⊑ᵂ
        (target-insert-bind-world-extendᴿ ins₀ follows₀) q₀)
      W¹ (ECR.mapCtxᴿ (target-insert-bind-world-extendᴿ ins follows) γ)
      M
      (ECR.transport⊑ᵂ
        (target-insert-bind-world-extendᴿ ins follows) q)
```

The plain-Λ branch of that theorem must supply the lifted one-bind endpoint:

```agda
StructuralWorldExtendᴿ (bind R ∷ [])
  (CTI2.liftWorldLeft X⊑★ W)
  (CTI2.liftWorldLeft X⊑★ W¹)
```

and rebuild:

```agda
CTI2.LiftCtxᴸ X⊑★
  (ECR.mapCtxᴿ ext γ)
  (ECR.mapCtxᴿ extᴸ γᴸ)
```

Diagram:
Λ U      ⊑      F
 |              |
 |              |
 U        ⊑     F

where the bottom row is at
`CTI2.liftWorldLeft X⊑★ W¹` and the top row is at `W¹`.

The smart-Λ branch must do the same through
`structural-smart-liftᴸ (structural-bind ins follows structural-[]) liftW`,
rebuilding the inserted smart endpoint and transporting target typing with:

```agda
smartCommaLift-target-store
smartLiftCtxᴸ-target-ctx
```

## Why this blocks F2/LG-3 assembly

The derivation-primary value worker needs an internal stack-indexed entry:

```agda
structural-value-catchup-stack-at :
  SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → Value M
  → W ∣ γ ⊢² M ⊑ M″ ∶ q
  → TargetCastBound fuel rel
  → StructuralCatchupRightPayload W₀ γ₀ M₀ M″ q₀
```

Base rows fold with `source-Λ-stack-unlift`.  Plain/smart source-Λ rows extend
the stack and recurse.  Target-bind rows must call
`source-Λ-stack-target-bind-child`; without it, nested source Λ under target
allocation reproduces the LG-3q obstruction:

```agda
planᵇ : StructuralWorldExtendᴿ χs
  (CTI2.liftWorldLeft X⊑★ W) Wᵇ
```

but `structural-Λ-replay` needs an outer endpoint:

```agda
plan₀ : StructuralWorldExtendᴿ χs W W′
```

with the child relation specifically at
`CTI2.liftWorldLeft X⊑★ W′`.

Until that stack-over-bind theorem exists, the value `Λ⊑²` and
`Λ⊑²-smart-comma` rows cannot synthesize their frame replay functions, so the
full `StructuralValueCatchupRightAt` factory, the structural factories, and the
public `FuelKnot` instantiation remain unassembled.
