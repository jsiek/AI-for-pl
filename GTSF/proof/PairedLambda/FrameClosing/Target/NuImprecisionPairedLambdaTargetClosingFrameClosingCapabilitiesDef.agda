module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingCapabilitiesDef
  where

-- File Charter:
--   * Bundles the exact semantic capabilities required by the paired-lambda
--     target-closing frame-closing assembly.
--   * Gives upper assemblies one explicit dependency boundary while retaining
--     the independently checkable statements of all twenty-two capabilities.
--   * Keeps the embedded target-instantiation capability fully inline instead
--     of naming an unproved semantic theorem boundary.
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
open import ImprecisionComposition using (ImprecisionShape)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
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
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (rename-assm²ᵢ)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (EmbeddedTargetInstantiationCreation)
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
    cap-target-instantiation :
        ∀ {Φ Φ₀ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
          {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
            (suc Θᴸ) (suc Θᴿ)}
          {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
          {W W′ V V′ : Term} {A′ B C D F : Ty}
          {s c′ : Coercion} {μ : ModeEnv} {r}
          {f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ}
          {p : Φ ∣ Δᴸ ⊢ `∀ F ⊑ A′ ⊣ Δᴿ}
          {body-shape : ImprecisionShape} →
      EmbeddedTargetInstantiationCreation
        {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
        {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
        {W = W} {W′ = W′} {B = B} {C = C} {D = D}
        {s = s} {μ = μ} {r = r} {f = f}
        {body-shape = body-shape}
        (StoreImpPrefix ρ₀ ρ⁺)
        (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ∀ ∣ []
          ⊢ᴺ W ⊑ W′ ⦂ D ⊑ C ∶ r)
        {Ψ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        ρ (Λ V) (V′ ⟨ c′ ⟩) (`∀ F) A′ p →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (Λ V) (V′ ⟨ c′ ⟩) F A′ p

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
