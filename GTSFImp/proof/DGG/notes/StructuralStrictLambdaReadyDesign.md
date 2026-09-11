# Value-ready strict `Λ` children

## Status and scope

This note audits the strict-worker boundary at a target `β-Λ` step.  The live
repair keeps `StructuralStrictChild.child-value` and the value-only recursive
worker unchanged.  The child passed to that worker is the body value `V`; the
administrative reveal produced by `β-Λ` is the first pending spine frame.

`notes/probes/StructuralStrictLambdaReadyProbe.agda` checks under `--safe`:

- the exact reframing of the existing peeled target package;
- assembly of the value-ready `StructuralStrictChild` once its producer facts
  are supplied;
- equality of the old and new pending cast mass; and
- strict decrease of the administrative rank.

The relation-side strict producer remains **schematic and unproved**.  The
canonical spine, target peel, strict surface, spine typing, mass/rank proofs,
and recursive worker are now live.  This work changes neither
`CastTermImprecision` nor `CtxImp`.

## The obstruction is at the worker boundary

The trusted target reduction has the whole-term step

```text
applyInstantiationSpine ((Λ V) ⦂∀ B [ ＇ X ]) spine
  —→[ bind (＇ X) ]
applyInstantiationSpine
  (V ↑ 〖 zero , ⇑ᵗ (＇ X) ↑ B 〗)
  (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
   mapInstantiationSpine (bind (＇ X)) spine)
```

This is the `β-Λ` case in `Reduction` and is the shape inverted by
`structural-target-Λ-peel` in
`Catchup/StructuralTargetLambdaPeelProof.agda`.  It does not say that the
immediate reduct is a value.

The former `StructuralΛStrictSurfaceᵀ` returned a
`StructuralStrictChild` whose target term is

```agda
V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗
```

and therefore requires

```agda
Value (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
```

For `B = ★`, the generated reveal is administrative and the term is not a
value.  `StructuralStrictAllocationProducerProbe.agda` checks the resulting
contradiction.  This is not a failure of `β-Λ`; it is a mismatch between an
immediate reduct and a worker whose recursive states intentionally begin with
values.

## Canonical value-ready state

The immediate reduct with its tail is definitionally the body value with the
reveal moved into the spine:

```text
applyInstantiationSpine (V ↑ cX) tail
  = applyInstantiationSpine V (reveal-frame cX ▻ⁱ tail)
```

The following is a genuine reusable state constructor, not a name for a proof
obligation:

```agda
lambda-ready-child-spine : ∀ {Δ} {B : Ty (suc Δ)} {E : Ty Δ}
    {X : TyVar Δ}
  → InstantiationSpine (B [ ＇ X ]ᵗ) E
  → InstantiationSpine B (applyTy (bind (＇ X)) E)
lambda-ready-child-spine {B = B} {X = X} spine =
  reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
  type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
  mapInstantiationSpine (bind (＇ X)) spine
```

It should live with `InstantiationSpine`, in
`Catchup/StructuralValueInstantiationStateDef.agda`, because target peeling,
strict surfaces, spine typing, rank, and the worker all need the same state.

`structural-target-frame` already proves the exact package conversion:

```agda
StructuralTargetInstantiationPackage W₁ (V ↑ cX) tail
  → StructuralTargetInstantiationPackage W₁ V
      (reveal-frame cX ▻ⁱ tail)
```

It preserves the package's world extension, final term, final value, and full
reduction trace.  No reduction or relation transport is hidden here.

## Live `Λ` surface

The canonical `structural-target-Λ-peel` result exposes the reframed
package directly:

```agda
child-target : StructuralTargetInstantiationPackage W₁ V
  (lambda-ready-child-spine {B = B} {X = X} spine)
```

Internally, the peel constructs the raw package and applies
`structural-target-frame` once.  The closed-world API should replace the old
peeled shape rather than retain a second wrapper lemma.

With that canonical peel result, the live strict surface is:

```agda
StructuralΛStrictSurfaceᵀ : Set₁
StructuralΛStrictSurfaceᵀ =
  ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {π : Δ ↪ᵗ Δ₁}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → W CTIR.∣ γ ⊢² M ⊑ Λ V ∶ p
  → Value M
  → Value V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ A
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTI2.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTI2.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁ V
      (lambda-ready-child-spine {B = B} {X = X} spine))
  → let ext₁ = target-insert-bind-world-extendᴿ ins follows
     in StructuralStrictChild {fuel = fuel} W₁
          (ECR.mapCtxᴿ ext₁ γ) M V A B
          (applyTy (bind (＇ X)) E)
          (lambda-ready-child-spine {B = B} {X = X} spine)
          (ECR.transport⊑ᵂ ext₁ q) child-target
```

`StructuralStrictChild` itself is retained verbatim, including
`child-value : Value V`.  The crucial index changes are:

```text
target term:  V ↑ cX       becomes  V
target type:  replaceTy … B becomes  B
spine:        tail          becomes  reveal-frame cX ▻ⁱ tail
```

Consequently the producer must establish the compositional facts at the input
of the reveal:

```agda
child-endpoint : A CTI2.⊑ᵂ⟨ W₁ ⟩ B
child-relation : W₁ CTIR.∣ ECR.mapCtxᴿ ext₁ γ
  ⊢² M ⊑ V ∶ child-endpoint
child-chain : TargetFrameAbsorptionChain W₁
  (ECR.mapCtxᴿ ext₁ γ) A
  (lambda-ready-child-spine spine) (ECR.transport⊑ᵂ ext₁ q)
child-typed : SpineTypedʷ W₁ (lambda-ready-child-spine spine)
```

The first reveal frame then uses the ordinary `tfa-reveal` path to construct
the post-reveal relation or to consume its one administrative keep step.  The
probe assumes these producer facts; it does **not** prove that current
inversion/provenance infrastructure can construct them.

## Termination remains structural

The new state does not consume cast fuel.  Reveal frames contribute zero to
`spineCastMass`, so the checked equality is:

```agda
pendingCastMass vV (lambda-ready-child-spine spine) ≡
pendingCastMass (CT.Λ vV)
  (name-type-app-frame B X refl refl ▻ⁱ spine)
```

The administrative rank decreases immediately because the parent name frame
is gone and reveal frames do not count as name frames:

```agda
pendingRank vV (lambda-ready-child-spine spine) <ʳ
pendingRank (CT.Λ vV)
  (name-type-app-frame B X refl refl ▻ⁱ spine)
```

Thus the recursive call remains the existing value-recursive call, using
`vV`; it needs neither a new recursive phase nor a fuel decrease.

## Why the broader alternatives are worse

### `StructuralFrameOutcome`

`StructuralFrameOutcome` correctly classifies a reveal around a value as
either already a value or one keep step from a value.  The generic reveal-frame
branch of `structural-value-spine-instantiation-acc` already consumes it.
Putting that outcome in `StructuralStrictChild` would duplicate this branch and
would still require post-step relation, provenance, chain, typing, target
package, and termination transport.  It does not solve the producer problem.

### `ValueCatchupRightAt fuel`

This surface normalizes an arbitrary related target term and may return a new
store and world.  It also requires `TargetCastBound fuel`.  A single known
reveal frame already has a typed structural path, so invoking general catchup
would discard the spine structure and add unnecessary world/fuel composition.

### `StructuralInstantiationDescentPackage`

This is a completed target-normalization result containing the final relation.
Returning it from the `Λ` cell would make a local producer perform the
worker's recursive job and would collapse the strict-view/worker separation.

### Non-value recursive states

Allowing the worker to recurse on `V ↑ cX` without a value would invalidate the
worker's frame classification and its `pendingCastMass`/`pendingRank` measures,
both of which are indexed by a `Value`.  It is a much larger redesign with no
semantic benefit here.

## Completed migration and remaining producer

The canonical `lambda-ready-child-spine`, reframed target peel, strict-surface
indices, recursive call on `V`/`vV`, value-ready mass and rank proofs, and
spine typing are now live.  The old wrapped child shape and its helper lemmas
have no compatibility aliases.

The remaining `Λ-cell` producer must construct the body relation at
`child-endpoint : A ⊑ B`, its exact child-target-indexed term provenance, and
the reveal-first absorption chain.  This is the remaining substantive,
unproved obligation; it is not derivable from the bookkeeping-only inputs of
the current abstract strict cell.

`StructuralStrictViewSurfaces`, `StructuralInstantiationDescentProof`, and
`InstInversionDef` only carry the `Λ-cell` surface transitively.  They need no
new outcome type or algorithm.  No change is indicated for CTI, world
invariants, target-bind authorization, or general value catchup.
