T5 NS-4 stage 2 proposal: conceal-equal target partner preservation

Date: 2026-08-17

Status: blocked by the standing major-surface rule.

The fixed stage-2 field is:

```agda
conceal-equal-ok :
  StructuralNameConcealEqualOKᵀ
```

The consumer is the source-conceal equal branch in
`StructuralNameInstantiationProof.agda`:

```agda
structural-conceal-replay
  (StructuralTargetInstantiationPackage.structural-ext target)
  mono rb sc c⊢
  (StructuralStrictViewSurfaces.conceal-equal-ok surfaces rb ok
    spine target)
  ...
```

The required transport is:

```agda
ok :
  CTI2.SourceConcealPartnerOK Wᵖ U c Xᴿ? V

target :
  StructuralTargetInstantiationPackage W V
    (name-type-app-frame B X refl refl ▻ⁱ spine)
```

to:

```agda
CTI2.SourceConcealPartnerOK
  (StructuralTagRebaseAtᴸResult.Wᵖ′
    (structural-tag-rebase-atᴸ
      (StructuralTargetInstantiationPackage.structural-ext target) rb))
  U c
  (mapPivotChanges
    (StructuralTargetInstantiationPackage.χs target) Xᴿ?)
  (StructuralTargetInstantiationPackage.final target)
```

The structural world part is already checked by
`structural-tag-rebase-atᴸ`.  The missing part is preserving the
`SourceConcealPartnerOK` witness across the target package's reduction and
spine endpoint.

Proposed checked statement
--------------------------

The direct statement can be the fixed field itself:

```agda
structural-conceal-equal-ok :
  StructuralNameConcealEqualOKᵀ
```

If kept as a reusable helper, the equivalent target-package statement is:

```agda
structural-target-source-conceal-partner : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V : Term Δᴿ} {B E : Ty Δᴿ}
    {spine : InstantiationSpine B E}
  → (target : StructuralTargetInstantiationPackage W V spine)
  → ∀ {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {U : Term Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′} {Xᴸ? Xᴿ?}
  → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → CTI2.SourceConcealPartnerOK Wᵖ U c Xᴿ? V
  → let child = structural-tag-rebase-atᴸ
          (StructuralTargetInstantiationPackage.structural-ext target) rb
     in CTI2.SourceConcealPartnerOK
          (StructuralTagRebaseAtᴸResult.Wᵖ′ child) U c
          (mapPivotChanges
            (StructuralTargetInstantiationPackage.χs target) Xᴿ?)
          (StructuralTargetInstantiationPackage.final target)
```

Why this is a surface issue
---------------------------

For `fun`, `∀`, and `id` source conceals, the result is constructor-immediate.
For source `seal`, however, `SourceConcealPartnerOK` depends on the target
endpoint shape through `SealPartnerOK`.  The current
`StructuralTargetInstantiationPackage` records the structural trace,
reduction, final term, and final value, but it does not carry the endpoint
partner transport fields that `StructuralCatchupRightResult` carries:

```agda
source-conceal-endpoint-partner :
  ...
  → CTI2.SourceConcealPartnerOK W₀ P c Xᴿ? M″
  → CTI2.SourceConcealPartnerOK W₀′ P c
      (mapPivotChanges χs Xᴿ?) N′
```

Adding that information to the target package would be a Def-level surface
change, which the task forbids.  Proving it externally would require a new
target-spine endpoint-partner preservation theorem for seal partners.  Per the
task rule, this proposal records the statement and does not implement the new
surface.

