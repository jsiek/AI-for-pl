module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingCapabilitiesDef
  where

-- File Charter:
--   * Bundles the exact semantic capabilities required by the paired-lambda
--     target-closing frame-closing assembly.
--   * Gives upper assemblies one explicit dependency boundary while retaining
--     the independently checkable statements of all twenty-two capabilities.
--   * Keeps the fused instantiation-beta capability fully inline instead of
--     naming an unproved semantic theorem boundary.
--   * Contains no proofs, postulates, holes, permissive options, or imports of
--     proof implementations.

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
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameCasesDef
  using
  ( PairedLambdaTargetClosingFrameClosingTargetConcealᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetIdOnlyWideningᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetNarrowingᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetWideningᵀ
  )
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetRevealCoreDef
  using (PairedLambdaTargetClosingFrameClosingTargetRevealCoreᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingDef
  using
  (PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingDef
  using
  (PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedConversionFramePairedConversionCasesDef
  using
  ( PairedLambdaTargetClosingPairedConversionFramePairedConcealClosingᵀ
  ; PairedLambdaTargetClosingPairedConversionFramePairedRevealClosingᵀ
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
  proof.PairedLambda.SourceFrames.SourceAll.NuImprecisionPairedLambdaTargetClosingSourceAllFrameAllIndexClosingDef
  using (PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingDef
  using (PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreDef
  using
  (PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreᵀ)
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
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpIdFrameWideningCasesDef
  using
  ( PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ
  ; PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ
  )
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetStructuralHalfSquareDef
  using
  ( PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ
  ; PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)


record PairedLambdaTargetClosingFrameClosingCapabilities : Set₁ where
  field
    cap-inst-beta :
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
        M M′ F A′ p

    cap-fresh-path-target-structural-reveal-half-square :
      PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ
    cap-fresh-path-target-structural-conceal-half-square :
      PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ
    cap-lambda-lambda-structural-reveal :
      PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ
    cap-lambda-lambda-structural-conceal :
      PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ
    cap-up-gen-leaf-all-index :
      PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ
    cap-source-gen-structural-reveal-core :
      PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreᵀ
    cap-source-gen-structural-conceal :
      PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ
    cap-source-all-all-index :
      PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ
    cap-paired-conversion-reveal :
      PairedLambdaTargetClosingPairedConversionFramePairedRevealClosingᵀ
    cap-paired-conversion-conceal :
      PairedLambdaTargetClosingPairedConversionFramePairedConcealClosingᵀ
    cap-paired-widening-source-inert-core :
      PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ
    cap-paired-widening-target-inert-bridge :
      PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ
    cap-up-id-quotient-id-widening :
      PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ
    cap-up-id-quotient-cast-widening :
      PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ
    cap-up-gen-all-quotient-id-widening :
      PairedLambdaTargetClosingUpGenAllFrameQuotientIdWideningClosingᵀ
    cap-up-gen-all-quotient-cast-widening :
      PairedLambdaTargetClosingUpGenAllFrameQuotientCastWideningClosingᵀ
    cap-target-reveal-core :
      PairedLambdaTargetClosingFrameClosingTargetRevealCoreᵀ
    cap-target-conceal :
      PairedLambdaTargetClosingFrameClosingTargetConcealᵀ
    cap-target-narrowing :
      PairedLambdaTargetClosingFrameClosingTargetNarrowingᵀ
    cap-target-widening :
      PairedLambdaTargetClosingFrameClosingTargetWideningᵀ
    cap-target-id-only-widening :
      PairedLambdaTargetClosingFrameClosingTargetIdOnlyWideningᵀ
