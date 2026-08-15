# NS-4 stage 1t assembly blocker: non-name child continuations

Date: 2026-08-15

Status: open.

Scope correction applied:

The strict target-wrapper child relations from
`ns4-stage-1s-strict-child-relation-resister.red` are not stage-1 obligations.
The stage-1 worker delegates those cases to the five higher-order strict view
surfaces and consumes their returned `StructuralStrictChild` data.

What closed in live Agda:

- `StructuralValueInstantiationᵀ` now takes the assembled
  `StructuralNameInstantiationᵀ`, the hereditary source/chain plans, and the
  root `StructuralTargetInstantiationPackage`.
- `structural-value-instantiation` is checked as a thin adapter through
  `erase-structural-name-root`.
- The root-normalizer plan is superseded by caller-supplied target geometry.

Remaining blocker
-----------------

The general `StructuralNameInstantiationᵀ` worker still cannot be expressed
from the current non-name frame contracts without adding fields.

### Missing field 1. Target-bind source/chain continuation for `safe-inst`

In the non-name frame:

```agda
cast-frame ((inst c) B≢★) ▻ⁱ spine
```

`structural-target-inst-peel` returns the allocated child target package:

```agda
StructuralTargetInstantiationPackage W₁ (⇑ᵗᵐ V)
  (name-type-app-frame (applyBody (bind ★) A) Fin.zero refl refl ▻ⁱ
   type-transport-frame (applyBody-open-zero A) ▻ⁱ
   reveal-frame (〖 Fin.zero , ★ ↑ A 〗) ▻ⁱ
   type-transport-frame
     (trans (replace-zero-open A ★)
       (sym (renameᵗ-wk-eq (A [ ★ ]ᵗ)))) ▻ⁱ
   cast-frame (↑ᶜ (close-instᶜ c)) ▻ⁱ
   type-transport-frame (renameᵗ-wk-eq B) ▻ⁱ
   mapInstantiationSpine (bind ★) spine)
```

The worker can obtain the target-inserted child relation by target insertion,
and the mass decrease is exactly `inst-primary-decreases`.  The child spine is
typed by `spine-typed-inst-child`.

The missing continuation is:

```agda
child-plan :
  StructuralNamePostPlan W₁ Aₛ (applyTy (bind ★) E)
    (ECR.transport⊑ᵂ ext₁ q)

child-chain-plan :
  StructuralNameChainPlan {fuel = fuel} W₁
    (ECR.mapCtxᴿ ext₁ γ) Aₛ (applyTy (bind ★) E)
    (ECR.transport⊑ᵂ ext₁ q) child-plan
```

where:

```agda
ext₁ = target-insert-bind-world-extendᴿ ins follows
```

The parent inputs only provide:

```agda
plan : StructuralNamePostPlan W Aₛ E q
chain-plan : StructuralNameChainPlan {fuel = fuel} W γ Aₛ E q plan
```

There is no live field or lemma transporting this hereditary source/chain
plan across a target-only bind.  The current strict view surfaces avoid this
by returning `child-plan` and `child-chain-plan` explicitly in
`StructuralStrictChild`, but the non-name `safe-inst` frame has no analogous
continuation surface.

### Missing field 2. Relation to reveal/conceal one-step reducts

For a non-name reveal frame:

```agda
reveal-frame c ▻ⁱ spine
```

`target-frame-reveal-absorption` produces a relation to the framed term:

```agda
W ∣ γ ⊢² M ⊑ V ↑ c ∶ qC
```

If `structural-reveal-frame-outcome` classifies `V ↑ c` as a value, the worker
can recurse on `V ↑ c` and the tail spine.

If it classifies the frame as one keep step:

```agda
(V ↑ c) —→[ keep ] V₁
Value V₁
```

then `structural-target-reveal-frame-keep-peel` returns the target child:

```agda
StructuralTargetInstantiationPackage W V₁
  (mapInstantiationSpine keep spine)
```

The recursive call still needs:

```agda
W ∣ γ ⊢² M ⊑ V₁ ∶ qC
```

No current field in `TargetFrameAbsorptionChain.tfa-reveal` supplies this
relation-to-reduct evidence.  Its transport field only moves the premise
relation into the rebased world needed by `⊑reveal²`; it does not cross the
target keep step.  The `conceal-frame` branch has the same missing field for
`TargetFrameAbsorptionChain.tfa-conceal`.

Required surface additions
--------------------------

To express the worker without changing the live term-imprecision relation, add
one of the following:

- a target-bind continuation field for non-name allocating frames, providing
  the transported `StructuralNamePostPlan` and `StructuralNameChainPlan`; and
- reveal/conceal keep-reduct relation fields in `TargetFrameAbsorptionChain`,
  or an equivalent one-step target-administration catch-up lemma that produces
  the relation to `V₁`.

No strict target-wrapper inversion is requested here; that remains delegated
to the strict view surface inhabitants by design.
