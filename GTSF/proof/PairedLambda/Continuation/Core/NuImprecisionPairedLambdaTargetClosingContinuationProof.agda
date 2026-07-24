module
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationProof
  where

-- File Charter:
--   * Interprets a proof-relevant paired-lambda target-closing frame view into
--     the continuation-indexed closing motive.
--   * Delegates the fifteen semantic cases to continuation handlers.
--   * Prepends store prefixes and all five target-only frames to the pending
--     continuation before recursively interpreting the inner frame spine.
--   * Refines the fused leaf's source equality before dispatching its handler.
--   * Initializes continuation-polymorphic leaf handlers and discharges the
--     final public theorem with the reflexive pending continuation.
--   * Contains no target-frame capability, postulate, hole, permissive option,
--     or canonical handler assembly.

open import Agda.Builtin.Equality using (refl)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  ( paired-conversion
  ; paired-widening
  )
open import Types using (Ty; TyCtx; `∀)
open import
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationHandlersDef
  using
  ( PairedLambdaTargetClosingContinuationHandlers
  ; handle-frame-cast⊒⊑
  ; handle-frame-cast⊑⊑
  ; handle-frame-conv↑⊑
  ; handle-frame-conv↓⊑
  ; handle-frame-gen-all
  ; handle-frame-paired-conversion
  ; handle-frame-paired-widening
  ; handle-frame-up-gen-all
  ; handle-frame-up-id
  ; handle-leaf-gen-ground
  ; handle-leaf-gen-ν
  ; handle-leaf-instβ
  ; handle-leaf-up-gen
  ; handle-leaf-Λ
  ; handle-leaf-ΛΛ
  )
open import proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef using
  ( PairedLambdaTargetClosingLeaf
  ; PairedLambdaTargetClosingFrames
  ; PairedLambdaTargetClosingFrameView
  ; closing-frame-view
  ; frame-cast⊒⊑
  ; frame-cast⊑⊑
  ; frame-conv↑⊑
  ; frame-conv↓⊑
  ; frame-gen-all
  ; frame-conv⊑conv
  ; frame-prefix
  ; frame-refl
  ; frame-up-gen-all
  ; frame-up-id
  ; frame-⊑cast⊒
  ; frame-⊑cast⊑
  ; frame-⊑cast⊑id
  ; frame-⊑conv↑
  ; frame-⊑conv↓
  ; leaf-gen-ground
  ; leaf-gen-ν
  ; leaf-instβ
  ; leaf-up-gen
  ; leaf-Λ
  ; leaf-ΛΛ
  )
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using
  ( PairedLambdaTargetClosingFrameClosingMotiveᴷ
  ; pending-prefix
  ; pending-refl
  ; pending-⊑cast⊒
  ; pending-⊑cast⊑
  ; pending-⊑cast⊑id
  ; pending-⊑conv↑
  ; pending-⊑conv↓
  )
open import
  proof.Source.NuPaired.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingDef
  using
  (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ)


interpret-paired-lambda-target-closing-continuation-frames :
  (handlers : PairedLambdaTargetClosingContinuationHandlers) →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ W W′ : Term} {F₀ A′ F B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ `∀ F₀ ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingLeaf ρ₀
    L L′ (`∀ F₀) A′ p →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ
    ρ₀ L L′ F₀ A′ p →
  PairedLambdaTargetClosingFrames ρ₀ L L′ (`∀ F₀) A′ p
    ρ W W′ (`∀ F) B′ q →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ
    ρ W W′ F B′ q
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial frame-refl =
  initial
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial (frame-prefix frames prefix W⊢ W′⊢) =
  λ pending →
    interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames
      (pending-prefix prefix W⊢ W′⊢ pending)
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial (frame-cast⊒⊑ frames mode seal★ c⊒ r) =
  handle-frame-cast⊒⊑ handlers
    (interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames)
    (closing-frame-view leaf frames)
    mode seal★ c⊒ r
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial (frame-cast⊑⊑ frames mode seal★ c⊑ r) =
  handle-frame-cast⊑⊑ handlers
    (interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames)
    (closing-frame-view leaf frames)
    mode seal★ c⊑ r
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial (frame-conv↑⊑ frames c↑ r) =
  handle-frame-conv↑⊑ handlers
    (interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames)
    (closing-frame-view leaf frames)
    c↑ r
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial (frame-conv↓⊑ frames c↓ r) =
  handle-frame-conv↓⊑ handlers
    (interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames)
    (closing-frame-view leaf frames)
    c↓ r
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial
    (frame-gen-all frames mode seal★ hA occ c⊢ cⁿ r) =
  handle-frame-gen-all handlers
    (interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames)
    (closing-frame-view leaf frames)
    mode seal★ hA occ c⊢ cⁿ
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial (frame-⊑cast⊒ frames inert mode seal★ c⊒ r) =
  λ pending →
    interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames
      (pending-⊑cast⊒ inert mode seal★ c⊒ pending)
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial (frame-⊑cast⊑ frames inert mode seal★ c⊑ r) =
  λ pending →
    interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames
      (pending-⊑cast⊑ inert mode seal★ c⊑ pending)
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial (frame-⊑cast⊑id frames inert seal★ c⊑ r) =
  λ pending →
    interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames
      (pending-⊑cast⊑id inert seal★ c⊑ pending)
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial (frame-⊑conv↑ frames inert c↑ r) =
  λ pending →
    interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames
      (pending-⊑conv↑ inert c↑ pending)
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial (frame-⊑conv↓ frames inert c↓ r) =
  λ pending →
    interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames
      (pending-⊑conv↓ inert c↓ pending)
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial
    (frame-conv⊑conv frames inert (paired-conversion conversion)) =
  handle-frame-paired-conversion handlers
    (interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert conversion
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial
    (frame-conv⊑conv frames inert
      (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑
        compatible)) =
  handle-frame-paired-widening handlers
    (interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert mode seal★ c⊑ mode′ seal★′ c′⊑ compatible
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial
    (frame-up-id frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  handle-frame-up-id handlers
    (interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert-d′ inert-u′ d⊒ d′⊒ qD widening q
interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf initial
    (frame-up-gen-all frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  handle-frame-up-gen-all handlers
    (interpret-paired-lambda-target-closing-continuation-frames handlers
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert-d′ inert-u′ d⊒ d′⊒ qD widening q


interpret-paired-lambda-target-closing-continuation-view :
  PairedLambdaTargetClosingContinuationHandlers →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameView ρ W W′ (`∀ F) B′ q →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ
    ρ W W′ F B′ q
interpret-paired-lambda-target-closing-continuation-view handlers
    (closing-frame-view
      leaf@(leaf-ΛΛ liftρ liftγ vV noV vV′ noV′ V⊑V′) frames) =
  interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf
    (handle-leaf-ΛΛ handlers
      liftρ liftγ vV noV vV′ noV′ V⊑V′)
    frames
interpret-paired-lambda-target-closing-continuation-view handlers
    (closing-frame-view
      leaf@(leaf-Λ occ liftρ liftγ vV noV vN′ noN′ V⊑N′) frames) =
  interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf
    (handle-leaf-Λ handlers
      occ liftρ liftγ vV noV vN′ noN′ V⊑N′)
    frames
interpret-paired-lambda-target-closing-continuation-view handlers
    (closing-frame-view
      leaf@(leaf-instβ prefix mode seal★ inst⊑ liftρ liftρᴿ
        vW noW vW′ noW′ inert body f assm hτ hσ
        store-emb eqM eqM′ refl eqA′ p
        vM noM closedM vM′ noM′ closedM′ M⊢ M′⊢)
      frames) =
  interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf
    (handle-leaf-instβ handlers
      prefix mode seal★ inst⊑ liftρ liftρᴿ
      vW noW vW′ noW′ inert body f assm hτ hσ
      store-emb eqM eqM′ refl eqA′ p
      vM noM closedM vM′ noM′ closedM′ M⊢ M′⊢)
    frames
interpret-paired-lambda-target-closing-continuation-view handlers
    (closing-frame-view
      leaf@(leaf-gen-ν vV noV vN′ noN′ mode seal★ hA occ-g c= cⁿ
        V⊑N′ occ-r r)
      frames) =
  interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf
    (handle-leaf-gen-ν handlers
      vV noV vN′ noN′ mode seal★ hA occ-g c= cⁿ V⊑N′ occ-r)
    frames
interpret-paired-lambda-target-closing-continuation-view handlers
    (closing-frame-view
      leaf@(leaf-gen-ground mode seal★ c⊒ gH
        vV noV vW noW W⊢ V⊑Wtag q)
      frames) =
  interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf
    (handle-leaf-gen-ground handlers
      mode seal★ c⊒ gH vV noV vW noW W⊢ V⊑Wtag q)
    frames
interpret-paired-lambda-target-closing-continuation-view handlers
    (closing-frame-view
      leaf@(leaf-up-gen vM noM vM′ noM′ inert-d′ inert-u′
        d⊒ d′⊒ M⊑M′ qD widening q)
      frames) =
  interpret-paired-lambda-target-closing-continuation-frames handlers
    leaf
    (handle-leaf-up-gen handlers
      vM noM vM′ noM′ inert-d′ inert-u′
      d⊒ d′⊒ M⊑M′ qD widening q)
    frames


paired-lambda-target-closing-continuation-proofᵀ :
  PairedLambdaTargetClosingContinuationHandlers →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ
paired-lambda-target-closing-continuation-proofᵀ
    handlers prefix coherent exclusive wfL
    h⇑A reveal liftν lift∀ view conversion =
  interpret-paired-lambda-target-closing-continuation-view handlers view
    pending-refl prefix coherent exclusive wfL
    h⇑A reveal liftν lift∀ conversion
