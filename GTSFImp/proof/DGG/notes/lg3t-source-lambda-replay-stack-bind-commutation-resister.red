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

## LG-3u stop postscript, 2026-08-17

The one-bind geometry was isolated in a scratch module and reaches the expected
frame cases:

- base chooses the supplied root bind and rebuilds `source-Λ-stack-id`;
- the plain frame computes the current endpoint with
  `TE.liftLeftTargetInsert` and the lifted one-bind endpoint
  `target-insert-bind-world-extendᴿ`;
- the smart frame can use `structural-smart-liftᴸ` over the one-bind
  structural plan, which delegates to the existing smart-alias and smart-fresh
  insert families.

The scratch was then deleted.  No live module was changed.

The remaining obstruction is not the target insertion or smart guard data.  It
is the replay closure required by the current `SourceΛReplayStack` constructors
after the target context has been extended.

For the plain frame, after recursively transporting the parent stack over a
root bind, the constructor for the transported frame requires a new closure of
this shape:

```agda
∀ {M″ : Term (suc Δᴿ)}
→ StructuralCatchupRightPayload
    (CTI2.liftWorldLeft X⊑★ W¹)
    (ECR.mapCtxᴿ
      (target-insert-bind-world-extendᴿ
        (TE.liftLeftTargetInsert ins) follows)
      γᴸ)
    U M″
    (ECR.transport⊑ᵂ
      (target-insert-bind-world-extendᴿ
        (TE.liftLeftTargetInsert ins) follows)
      p)
→ StructuralCatchupRightPayload
    W¹
    (ECR.mapCtxᴿ (target-insert-bind-world-extendᴿ ins follows) γ)
    (Λ U) M″
    (ECR.transport⊑ᵂ
      (target-insert-bind-world-extendᴿ ins follows)
      q)
```

The frame already stored on the old stack has the analogous closure only at the
old target context:

```agda
∀ {M″ : Term Δᴿ}
→ StructuralCatchupRightPayload
    (CTI2.liftWorldLeft X⊑★ W) γᴸ U M″ p
→ StructuralCatchupRightPayload W γ (Λ U) M″ q
```

`TargetBindLift` and `StructuralWorldEvidenceProof` supply the moved endpoint,
target-store equality, context lift, and smart guard insertion data, but they do
not synthesize this target-bind-parametric replay closure for arbitrary
`M″ : Term (suc Δᴿ)` and arbitrary future
`StructuralCatchupRightPayload` starting at the bound child world.

The smart frame has the same missing datum with `SmartCommaLiftᴸ W¹ Wᵐ¹` and
`SmartLiftCtxᴸ` at the bound endpoint:

```agda
∀ {M″ : Term (suc Δᴿ)}
→ StructuralCatchupRightPayload Wᵐ¹ γᵐ¹ U M″ pᵐ¹
→ StructuralCatchupRightPayload W¹ γ¹ (Λ U) M″ q¹
```

This is a surface gap in the finite stack certificate, not a relation defect.
One of the following additional data shapes is needed before
`source-Λ-stack-target-bind-child` can be total:

- make source-Λ stack frames carry bind-parametric replay families, not only a
  replay closure fixed to the current target context;
- replace the closure field with frame data plus a plan-indexed unlift helper
  that recurses over `StructuralWorldExtendᴿ` and handles target-bind rows by
  transporting the stack before continuing; or
- restrict the replay-closure domain from arbitrary
  `StructuralCatchupRightPayload` to a generated stack-compatible payload
  invariant that records every prior bind commute.

Without one of those strengthened surfaces, the theorem can build the extended
worlds and frame evidence but cannot fill the constructor's post-bind replay
field.  Therefore F2, the stack-indexed value worker, the concrete structural
factories, and the public `FuelKnot` assembly remain unassembled.

Gate before and after this note-only stop:

```text
cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check
```

Result:

```text
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

No CTI relation, live imprecision relation, reduction relation, or protected
surface was changed.

## RESOLVED postscript, 2026-08-17, LG-3v

Resolved by commit `77e559ea`.

`SourceΛReplayStack` frames now carry only data:

- plain source-Λ frames store `NonVar A`, `zero ∈ᵗ A`, `LiftCtxᴸ`, and
  `Value U`;
- smart source-Λ frames store the same source-side data plus
  `SmartCommaLiftᴸ` and `SmartLiftCtxᴸ`;
- no constructor stores a replay closure over `Term Δᴿ`.

The replacement surface is:

- `source-Λ-stack-replay-here`, which folds a same-target endpoint relation by
  applying `structural-Λ-replay` / `structural-smart-Λ-replay`;
- `SourceΛReplayStackTransport` and `source-Λ-stack-transport`, which map a
  stack along a supplied root `StructuralWorldExtendᴿ` trace;
- `source-Λ-stack-target-bind-child`, the one-bind specialization.  The base
  row uses the root bind, the plain row uses `structural-lift-left` and hence
  `TE.liftLeftTargetInsert`, and the smart row uses
  `structural-smart-liftᴸ`;
- `source-Λ-stack-unlift-plan`, which consumes the transported stack endpoint
  and replays it back to the transported root.

The old missing post-bind replay closure is gone because replay is now derived
from frame data at the use site.  The checked gate for the landed support
chunk was:

```text
cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check
```

Result:

```text
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

This resolves the closure-field resister recorded above.  Full LG-3 assembly
is still stopped by the separate active extra-cast factory datum recorded in
`lg3-target-cast-multistep-worker-resister.red`.
