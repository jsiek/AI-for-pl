module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingProof
  where

-- File Charter:
--   * Interprets a proof-relevant paired-lambda target-closing frame view.
--   * Delegates the thirteen semantic cases to an explicit handler record and
--     all five target-only cases to one shared target-frame capability.
--   * Carries the original leaf through frame recursion and reconstructs the
--     exact inner frame view at every non-leaf semantic boundary.
--   * Handles reflexivity and store-prefix composition structurally.
--   * Contains no canonical assembly, postulate, hole, or permissive option.

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  ( PairedCast
  ; paired-conversion
  ; paired-widening
  )
open import Types using (Ty; TyCtx; `∀)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using
  ( PairedLambdaTargetClosingFrameClosingHandlers
  ; PairedLambdaTargetClosingFrameClosingMotive
  ; handle-frame-cast⊒⊑
  ; handle-frame-cast⊑⊑
  ; handle-frame-conv↑⊑
  ; handle-frame-conv↓⊑
  ; handle-frame-gen-all
  ; handle-frame-paired-conversion
  ; handle-frame-paired-widening
  ; handle-frame-up-gen-all
  ; handle-frame-up-id
  ; handle-leaf-gen-ν
  ; handle-leaf-up-gen
  ; handle-leaf-Λ
  ; handle-leaf-ΛΛ
  )
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameDef
  using (PairedLambdaTargetClosingFrameClosingTargetFrameᵀ)
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
  ; leaf-gen-ν
  ; leaf-up-gen
  ; leaf-Λ
  ; leaf-ΛΛ
  )
open import
  proof.Source.NuPaired.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingDef
  using
  (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using (store-imp-prefix-transⁱ)


interpret-paired-lambda-target-closing-frames :
  (handlers : PairedLambdaTargetClosingFrameClosingHandlers) →
  PairedLambdaTargetClosingFrameClosingTargetFrameᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ W W′ : Term} {F₀ A′ F B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ `∀ F₀ ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingLeaf ρ₀
    L L′ (`∀ F₀) A′ p →
  PairedLambdaTargetClosingFrameClosingMotive ρ₀ L L′ F₀ A′ p →
  PairedLambdaTargetClosingFrames ρ₀ L L′ (`∀ F₀) A′ p
    ρ W W′ (`∀ F) B′ q →
  PairedLambdaTargetClosingFrameClosingMotive ρ W W′ F B′ q
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial frame-refl =
  initial
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial (frame-prefix frames prefix _ _) =
  λ prefix′ coherent exclusive wfL h⇑A reveal liftν lift∀ conversion →
    interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames
      (store-imp-prefix-transⁱ prefix prefix′)
      coherent exclusive wfL h⇑A reveal liftν lift∀ conversion
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial (frame-cast⊒⊑ frames mode seal★ c⊒ r) =
  handle-frame-cast⊒⊑ handlers
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    mode seal★ c⊒ r
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial (frame-cast⊑⊑ frames mode seal★ c⊑ r) =
  handle-frame-cast⊑⊑ handlers
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    mode seal★ c⊑ r
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial (frame-conv↑⊑ frames c↑ r) =
  handle-frame-conv↑⊑ handlers
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    c↑ r
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial (frame-conv↓⊑ frames c↓ r) =
  handle-frame-conv↓⊑ handlers
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    c↓ r
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial
    (frame-gen-all frames mode seal★ hA occ c⊢ cⁿ r) =
  handle-frame-gen-all handlers
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    mode seal★ hA occ c⊢ cⁿ
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial (frame-⊑cast⊒ frames inert mode seal★ c⊒ r) =
  target-frame
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊒))))
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial (frame-⊑cast⊑ frames inert mode seal★ c⊑ r) =
  target-frame
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert (inj₂ (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊑)))))
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial (frame-⊑cast⊑id frames inert seal★ c⊑ r) =
  target-frame
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert (inj₂ (inj₂ (inj₂ (inj₂ (seal★ , c⊑)))))
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial (frame-⊑conv↑ frames inert c↑ r) =
  target-frame
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert (inj₁ (_ , _ , _ , c↑))
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial (frame-⊑conv↓ frames inert c↓ r) =
  target-frame
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert (inj₂ (inj₁ (_ , _ , _ , c↓)))
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial
    (frame-conv⊑conv frames inert (paired-conversion conversion)) =
  handle-frame-paired-conversion handlers
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert conversion
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial
    (frame-conv⊑conv frames inert
      (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑
        compatible)) =
  handle-frame-paired-widening handlers
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert mode seal★ c⊑ mode′ seal★′ c′⊑ compatible
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial
    (frame-up-id frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  handle-frame-up-id handlers
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert-d′ inert-u′ d⊒ d′⊒ qD widening q
interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf initial
    (frame-up-gen-all frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  handle-frame-up-gen-all handlers
    (interpret-paired-lambda-target-closing-frames handlers target-frame
      leaf initial frames)
    (closing-frame-view leaf frames)
    inert-d′ inert-u′ d⊒ d′⊒ qD widening q


interpret-paired-lambda-target-closing-view :
  PairedLambdaTargetClosingFrameClosingHandlers →
  PairedLambdaTargetClosingFrameClosingTargetFrameᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameView ρ W W′ (`∀ F) B′ q →
  PairedLambdaTargetClosingFrameClosingMotive ρ W W′ F B′ q
interpret-paired-lambda-target-closing-view handlers target-frame
    (closing-frame-view
      leaf@(leaf-ΛΛ liftρ liftγ vV noV vV′ noV′ V⊑V′) frames) =
  interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf
    (handle-leaf-ΛΛ handlers
      liftρ liftγ vV noV vV′ noV′ V⊑V′)
    frames
interpret-paired-lambda-target-closing-view handlers target-frame
    (closing-frame-view
      leaf@(leaf-Λ occ liftρ liftγ vV noV vN′ noN′ V⊑N′) frames) =
  interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf
    (handle-leaf-Λ handlers
      occ liftρ liftγ vV noV vN′ noN′ V⊑N′)
    frames
interpret-paired-lambda-target-closing-view handlers target-frame
    (closing-frame-view
      leaf@(leaf-gen-ν vV noV vN′ noN′ mode seal★ hA occ-g c= cⁿ
        V⊑N′ occ-r r)
      frames) =
  interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf
    (handle-leaf-gen-ν handlers
      vV noV vN′ noN′ mode seal★ hA occ-g c= cⁿ V⊑N′ occ-r)
    frames
interpret-paired-lambda-target-closing-view handlers target-frame
    (closing-frame-view
      leaf@(leaf-up-gen vM noM vM′ noM′ inert-d′ inert-u′
        d⊒ d′⊒ M⊑M′ qD widening q)
      frames) =
  interpret-paired-lambda-target-closing-frames handlers target-frame
    leaf
    (handle-leaf-up-gen handlers
      vM noM vM′ noM′ inert-d′ inert-u′
      d⊒ d′⊒ M⊑M′ qD widening q)
    frames


paired-lambda-target-closing-frame-closing-proofᵀ :
  PairedLambdaTargetClosingFrameClosingHandlers →
  PairedLambdaTargetClosingFrameClosingTargetFrameᵀ →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ
paired-lambda-target-closing-frame-closing-proofᵀ
    handlers target-frame prefix coherent exclusive wfL
    h⇑A reveal liftν lift∀ view conversion =
  interpret-paired-lambda-target-closing-view handlers target-frame view
    prefix coherent exclusive wfL h⇑A reveal liftν lift∀ conversion
