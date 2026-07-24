module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersProof
  where

-- File Charter:
--   * Assembles all fifteen semantic frame-closing handlers from the exact
--     leaf and fused-frame theorem boundaries.
--   * Requires the fused instantiation-beta leaf as an explicit higher-order
--     capability, leaving its semantic proof to the next layer.
--   * Composes the already checked index and paired-conversion dispatchers so
--     the remaining semantic dependencies are visible in one signature.
--   * Contains no semantic leaf implementation, postulate, hole, permissive
--     option, broad simulation import, or canonical `Lemma` assembly.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; inst
  )
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Imprecision using (⇑ᴿᵢ)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  ( Closedᵐ
  ; No•
  ; Term
  ; Value
  ; Λ_
  ; _⟨_⟩
  ; renameᵗᵐ
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Renameᵗ
  ; Ty
  ; TyCtx
  ; renameᵗ
  ; wf★
  ; ★
  ; `∀
  ; ⇑ᵗ
  )
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (rename-assm²ᵢ)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using
  ( PairedLambdaTargetClosingFrameClosingHandlers
  ; PairedLambdaTargetClosingFrameClosingMotive
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)
open import
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingGenLeafNuClosingProof
  using (paired-lambda-target-closing-gen-leaf-ν-closing-proofᵀ)
open import
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingGenGroundLeafClosingDef
  using (PairedLambdaTargetClosingGenGroundLeafClosingᵀ)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingGenLeafNuConversionRotationProof
  using
  (paired-lambda-target-closing-gen-leaf-ν-conversion-rotation-proofᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Core.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafClosingProof
  using
  ( paired-lambda-target-closing-lambda-lambda-leaf-closing-proofᵀ
  ; paired-lambda-target-closing-lambda-lambda-leaf-handler-proofᵀ
  )
open import
  proof.PairedLambda.LambdaLeaves.Conversion.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafPairedConversionCasesDef
  using (PairedLambdaTargetClosingLambdaLambdaLeafPairedConcealClosingᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Conversion.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafPairedConversionCasesProof
  using
  ( paired-lambda-target-closing-lambda-lambda-leaf-paired-conceal-closing-proofᵀ
  ; paired-lambda-target-closing-lambda-lambda-leaf-paired-reveal-closing-proofᵀ
  )
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingDef
  using
  (PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingDef
  using
  (PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Core.NuImprecisionPairedLambdaTargetClosingLambdaLeafClosingProof
  using (paired-lambda-target-closing-lambda-leaf-handler-proofᵀ)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  using (PairedLambdaTargetClosingNuPairedConversionRotationᵀ)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedConversionFrameClosingProof
  using
  ( paired-lambda-target-closing-paired-conversion-frame-closing-proofᵀ
  ; paired-lambda-target-closing-paired-conversion-frame-handler-proofᵀ
  )
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedConversionFramePairedConversionCasesDef
  using
  ( PairedLambdaTargetClosingPairedConversionFramePairedConcealClosingᵀ
  ; PairedLambdaTargetClosingPairedConversionFramePairedRevealClosingᵀ
  )
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameClosingProof
  using
  ( paired-lambda-target-closing-paired-widening-frame-compatible-cases-proofᵀ
  ; paired-lambda-target-closing-paired-widening-frame-handler-proofᵀ
  )
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleCasesDef
  using
  (PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreDef
  using
  (PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertProof
  using
  (paired-lambda-target-closing-paired-widening-frame-compatible-source-inert-proofᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceAll.NuImprecisionPairedLambdaTargetClosingSourceAllFrameAllIndexClosingDef
  using (PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceAll.NuImprecisionPairedLambdaTargetClosingSourceAllFrameClosingProof
  using
  ( paired-lambda-target-closing-source-all-conceal-frame-closing-proofᵀ
  ; paired-lambda-target-closing-source-all-narrowing-frame-closing-proofᵀ
  ; paired-lambda-target-closing-source-all-reveal-frame-closing-proofᵀ
  ; paired-lambda-target-closing-source-all-widening-frame-closing-proofᵀ
  )
open import
  proof.PairedLambda.SourceFrames.SourceAll.NuImprecisionPairedLambdaTargetClosingSourceAllFrameCommutationProof
  using (paired-lambda-target-closing-source-all-frame-commutation-proofᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameClosingProof
  using (paired-lambda-target-closing-source-gen-frame-closing-proofᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameCommutationProof
  using (paired-lambda-target-closing-source-gen-frame-commutation-proofᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFramePairedConversionCasesProof
  using
  ( paired-lambda-target-closing-source-gen-frame-paired-conceal-closing-proofᵀ
  ; paired-lambda-target-closing-source-gen-frame-paired-reveal-closing-proofᵀ
  )
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingDef
  using (PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingDef
  using (PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreDef
  using
  (PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingProof
  using
  (paired-lambda-target-closing-source-gen-frame-structural-reveal-closing-proofᵀ)
open import
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpGenAllFrameClosingProof
  using
  ( paired-lambda-target-closing-up-gen-all-frame-handler-proofᵀ
  ; paired-lambda-target-closing-up-gen-all-frame-widening-cases-proofᵀ
  )
open import
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpGenAllFrameWideningCasesDef
  using
  ( PairedLambdaTargetClosingUpGenAllFrameQuotientCastWideningClosingᵀ
  ; PairedLambdaTargetClosingUpGenAllFrameQuotientIdWideningClosingᵀ
  )
open import
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpGenLeafAllIndexClosingDef
  using (PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpGenLeafClosingProof
  using
  ( paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ
  ; paired-lambda-target-closing-up-gen-leaf-handler-proofᵀ
  )
open import
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpIdFrameClosingProof
  using
  ( paired-lambda-target-closing-up-id-frame-handler-proofᵀ
  ; paired-lambda-target-closing-up-id-frame-widening-cases-proofᵀ
  )
open import
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpIdFrameWideningCasesDef
  using
  ( PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ
  ; PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ
  )


paired-lambda-target-closing-frame-closing-handlers-proofᵀ :
  (inst-beta :
      ∀ {Φ Φ₀ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
        {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          (suc Θᴸ) (suc Θᴿ)}
        {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
        {τ σ : Renameᵗ}
        {W W′ M M′ : Term}
        {A′ B C D F : Ty}
        {s : Coercion} {μ : ModeEnv} {r} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Θᴿ ∣ rightStoreⁱ ρ₀
      ⊢ inst B s ∶ `∀ C ⊑ B →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀) ρ₀ ρ∀ →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ₀) ρ⁺ ρᴿ⁺ →
    Value W →
    No• W →
    Value W′ →
    No• W′ →
    Inert s →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
      ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ∀ ∣ []
      ⊢ᴺ W ⊑ W′ ⦂ D ⊑ C ∶ r →
    (f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ) →
    (assm :
      ∀ {a} → a ∈ ⇑ᴿᵢ Φ₀ →
        rename-assm²ᵢ τ σ a ∈ Φ) →
    (hτ : TyRenameWf Θᴸ Δᴸ τ) →
    (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ) →
    RelStoreEmbeddingⁱ τ σ
      (store-right zero ★ wf★ ∷ ρᴿ⁺) ρ →
    renameᵗᵐ τ (Λ W) ≡ M →
    renameᵗᵐ σ (W′ ⟨ s ⟩) ≡ M′ →
    renameᵗ τ (`∀ D) ≡ `∀ F →
    renameᵗ σ (⇑ᵗ B) ≡ A′ →
    (p : Φ ∣ Δᴸ ⊢ `∀ F ⊑ A′ ⊣ Δᴿ) →
    Value M →
    No• M →
    Closedᵐ M →
    Value M′ →
    No• M′ →
    Closedᵐ M′ →
    Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ `∀ F →
    Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ A′ →
    PairedLambdaTargetClosingFrameClosingMotive ρ
      M M′ F A′ p) →
  PairedLambdaTargetClosingNuPairedConversionRotationᵀ →
  PairedLambdaTargetClosingGenGroundLeafClosingᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ →
  PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ →
  PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreᵀ →
  PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ →
  PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ →
  PairedLambdaTargetClosingPairedConversionFramePairedRevealClosingᵀ →
  PairedLambdaTargetClosingPairedConversionFramePairedConcealClosingᵀ →
  PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ →
  PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ →
  PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ →
  PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ →
  PairedLambdaTargetClosingUpGenAllFrameQuotientIdWideningClosingᵀ →
  PairedLambdaTargetClosingUpGenAllFrameQuotientCastWideningClosingᵀ →
  PairedLambdaTargetClosingFrameClosingHandlers
paired-lambda-target-closing-frame-closing-handlers-proofᵀ
    inst-beta rotate gen-ground
    lambda-lambda-reveal lambda-lambda-conceal up-gen-all-index
    source-gen-reveal source-gen-conceal source-all-all-index
    paired-conversion-reveal paired-conversion-conceal
    paired-widening-source-inert
    paired-widening-target-inert-bridge up-id-id up-id-cast
    up-gen-all-id up-gen-all-cast =
  record
    { handle-leaf-ΛΛ =
        paired-lambda-target-closing-lambda-lambda-leaf-handler-proofᵀ
          (paired-lambda-target-closing-lambda-lambda-leaf-closing-proofᵀ
            (paired-lambda-target-closing-lambda-lambda-leaf-paired-reveal-closing-proofᵀ
              lambda-lambda-reveal)
            (paired-lambda-target-closing-lambda-lambda-leaf-paired-conceal-closing-proofᵀ
              lambda-lambda-conceal))
    ; handle-leaf-Λ =
        paired-lambda-target-closing-lambda-leaf-handler-proofᵀ rotate
    ; handle-leaf-instβ = inst-beta
    ; handle-leaf-gen-ν =
        paired-lambda-target-closing-gen-leaf-ν-closing-proofᵀ
          (paired-lambda-target-closing-gen-leaf-ν-conversion-rotation-proofᵀ
            rotate)
    ; handle-leaf-gen-ground = gen-ground
    ; handle-leaf-up-gen =
        paired-lambda-target-closing-up-gen-leaf-handler-proofᵀ
          (paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ
            rotate up-gen-all-index)
    ; handle-frame-gen-all =
        paired-lambda-target-closing-source-gen-frame-closing-proofᵀ
          (paired-lambda-target-closing-source-gen-frame-commutation-proofᵀ
            (paired-lambda-target-closing-source-gen-frame-paired-reveal-closing-proofᵀ
              source-gen-structural-reveal)
            (paired-lambda-target-closing-source-gen-frame-paired-conceal-closing-proofᵀ
              source-gen-conceal))
    ; handle-frame-cast⊒⊑ =
        paired-lambda-target-closing-source-all-narrowing-frame-closing-proofᵀ
          source-all-commutation
    ; handle-frame-cast⊑⊑ =
        paired-lambda-target-closing-source-all-widening-frame-closing-proofᵀ
          source-all-commutation
    ; handle-frame-conv↑⊑ =
        paired-lambda-target-closing-source-all-reveal-frame-closing-proofᵀ
          source-all-commutation
    ; handle-frame-conv↓⊑ =
        paired-lambda-target-closing-source-all-conceal-frame-closing-proofᵀ
          source-all-commutation
    ; handle-frame-paired-conversion =
        paired-lambda-target-closing-paired-conversion-frame-handler-proofᵀ
          (paired-lambda-target-closing-paired-conversion-frame-closing-proofᵀ
            paired-conversion-reveal paired-conversion-conceal)
    ; handle-frame-paired-widening =
        paired-lambda-target-closing-paired-widening-frame-handler-proofᵀ
          (paired-lambda-target-closing-paired-widening-frame-compatible-cases-proofᵀ
            (paired-lambda-target-closing-paired-widening-frame-compatible-source-inert-proofᵀ
              paired-widening-source-inert)
            paired-widening-target-inert-bridge)
    ; handle-frame-up-id =
        paired-lambda-target-closing-up-id-frame-handler-proofᵀ
          (paired-lambda-target-closing-up-id-frame-widening-cases-proofᵀ
            up-id-id up-id-cast)
    ; handle-frame-up-gen-all =
        paired-lambda-target-closing-up-gen-all-frame-handler-proofᵀ
          (paired-lambda-target-closing-up-gen-all-frame-widening-cases-proofᵀ
            up-gen-all-id up-gen-all-cast)
    }
  where
  source-all-commutation =
    paired-lambda-target-closing-source-all-frame-commutation-proofᵀ
      rotate source-all-all-index

  source-gen-core :
    PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreᵀ
  source-gen-core
      {q = q} {r = r} {p = p} {pX = pX}
      vV noV vN′ noN′ relation mode seal h∀F occ-B g⊢ gⁿ
      inner prefix h⇑A final-reveal liftν lift∀ corresponds
      source-reveal target-reveal =
    source-gen-reveal {q = q} {r = r} {p = p} {pX = pX}
      vV noV vN′ noN′ relation mode seal h∀F occ-B g⊢ gⁿ
      inner prefix h⇑A final-reveal liftν lift∀ corresponds
      source-reveal target-reveal

  source-gen-structural-reveal :
    PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ
  source-gen-structural-reveal
      {q = q} {r = r} {p = p} {pX = pX}
      vV noV vN′ noN′ relation framed inner prefix h⇑A
      final-reveal liftν lift∀ corresponds source-reveal target-reveal =
    paired-lambda-target-closing-source-gen-frame-structural-reveal-closing-proofᵀ
      (λ {Φ} {Δᴸ} {Δᴿ} {ρ₀} {ρ} {ρν} {ρ∀}
          {V} {N′} {F} {B} {B′} {A} {C′} {D} {E} {X} {X′}
          {g} {c} {c′} {t} {η} {η′} {θ} {μ} {α} {β}
          {q} {r} {p} {pX}
          vV noV vN′ noN′ relation mode seal h∀F occ-B g⊢ gⁿ
          inner prefix h⇑A final-reveal liftν lift∀ corresponds
          source-reveal target-reveal →
        source-gen-reveal
          {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
          {ρ₀ = ρ₀} {ρ = ρ} {ρν = ρν} {ρ∀ = ρ∀}
          {V = V} {N′ = N′} {F = F} {B = B} {B′ = B′}
          {A = A} {C′ = C′} {D = D} {E = E} {X = X} {X′ = X′}
          {g = g} {c = c} {c′ = c′} {t = t}
          {η = η} {η′ = η′} {θ = θ} {μ = μ} {α = α} {β = β}
          {q = q} {r = r} {p = p} {pX = pX}
          vV noV vN′ noN′ relation mode seal h∀F occ-B g⊢ gⁿ
          inner prefix h⇑A final-reveal liftν lift∀ corresponds
          source-reveal target-reveal)
      {q = q} {r = r} {p = p} {pX = pX}
      vV noV vN′ noN′ relation framed inner prefix h⇑A
      final-reveal liftν lift∀ corresponds source-reveal target-reveal
