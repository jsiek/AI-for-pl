# NS-4 stage 1u residual-tail resister

Date: 2026-08-15

Status: open.

The two stage-1t contract gaps were closed in live statements:

- target-only bind continuation uses hereditary `target-bind-child` fields on
  `StructuralNamePostPlan` and `StructuralNameChainPlan`;
- reveal/conceal keep discharges use supplied keep-reduct relation evidence
  and keep-mapped child chains on `TargetFrameAbsorptionChain`.

The next worker attempt exposed a separate residual-cast tail blocker.

## Blocking shape

In the non-name cast-frame branch the typed spine can be:

```agda
st-cast (cast-residual residual<fuel residual-prov) typedTail
```

for a pending frame:

```agda
cast-frame c ▻ⁱ spine
```

The absorption chain gives:

```agda
qC : A ⊑ᵂ⟨ W ⟩ C
W ∣ γ ⊢² M ⊑ V ⟨ c ⟩ ∶ qC
TargetFrameAbsorptionChain W γ A spine q
```

The existing residual helper is only a stop package for the bare residual cast:

```agda
residual-cast-stop-package :
  ...
  → InstSpineDescentPackage W γ M (V ⟨ c ⟩) qC
```

It does not provide a structural package or relation for the whole pending
tail:

```agda
applyInstantiationSpine (V ⟨ c ⟩) spine
```

The caller also has:

```agda
target : StructuralTargetInstantiationPackage W V
  (cast-frame c ▻ⁱ spine)
```

but there is no prefix-alignment theorem showing that the residual stop
reduction is the prefix of this caller target trace, nor a way to split the
caller trace after the residual stop value and continue with `spine`.

## Needed contract

Do not weaken `CastTermImprecision2` or the reduction relation.

One of these statement-level surfaces is needed:

- a residual-cast-with-tail theorem that composes
  `residual-cast-stop-package` with the remaining typed/absorbed spine and the
  caller target package; or
- a supplied residual-tail field owned by the frame generator/absorption chain,
  producing the final relation for `cast-frame c ▻ⁱ spine` when the
  `CastFrameClass` is `cast-residual`.

The second route matches the stage-1u keep-reduct decision: the generator that
created the residual frame owns the evidence that its target trace and
relational catch-up are aligned with the remaining tail.

## Extra closed surface

The strict-view child record also needed the value proof for its child term.
This is now a live statement field:

```agda
child-value : Value V
```

on `StructuralStrictChild`.  The recursive worker needs this for strict Λ
children such as:

```agda
V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗
```

and for the corresponding rank decrease.
