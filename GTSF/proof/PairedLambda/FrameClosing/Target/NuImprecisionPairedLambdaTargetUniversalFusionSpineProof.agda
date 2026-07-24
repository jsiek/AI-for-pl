module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetUniversalFusionSpineProof
  where

-- File Charter:
--   * Folds the framed recursive universal fusion spine back to quotiented
--     term imprecision.
--   * Takes the pure-spine and paired-lambda-frame folds as explicit theorem
--     dependencies and imports neither implementation.
--   * Contains no extraction, simulation result, Resume dependency, postulate,
--     hole, permissive option, termination bypass, or catch-all clause.

open import Data.List using ([])
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  (StoreImp)
open import NuTerms using
  (Term)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_; Λ⊑instβᵀ)
open import Types using
  (Ty; TyCtx; `∀)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrames)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetUniversalFusionSpineDef
  using
  ( PairedLambdaTargetUniversalFusionSpineRelationᵀ
  ; framed-fusion-pure
  ; framed-fusion-step
  )
open import
  proof.Target.Administration.NuImprecisionTargetUniversalFusionSpineDef
  using (TargetUniversalFusionSpineRelationᵀ)


paired-lambda-target-universal-fusion-spine-relation-proofᵀ :
  TargetUniversalFusionSpineRelationᵀ →
  (∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ W W′ : Term} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ A ⊑ A′ ∶ p →
    PairedLambdaTargetClosingFrames
      ρ₀ L L′ A A′ p ρ W W′ B B′ q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ W ⊑ W′ ⦂ B ⊑ B′ ∶ q) →
  PairedLambdaTargetUniversalFusionSpineRelationᵀ
paired-lambda-target-universal-fusion-spine-relation-proofᵀ
    pure-fold frame-fold (framed-fusion-pure pure frames) =
  frame-fold (pure-fold pure) frames
paired-lambda-target-universal-fusion-spine-relation-proofᵀ
    pure-fold frame-fold
    (framed-fusion-step
      prefix mode seal★ inst⊑ liftρ liftρᴿ
      vW noW vW′ noW′ inert tail f
      assm hτ hσ store-emb
      source-eq target-eq source-type-eq target-type-eq p
      final-v final-no final-closed
      final-v′ final-no′ final-closed′
      source-typing target-typing frames) =
  frame-fold
    (Λ⊑instβᵀ
      prefix mode seal★ inst⊑ liftρ liftρᴿ
      vW noW vW′ noW′ inert
      (paired-lambda-target-universal-fusion-spine-relation-proofᵀ
        pure-fold frame-fold tail)
      f assm hτ hσ store-emb
      source-eq target-eq source-type-eq target-type-eq p
      final-v final-no final-closed
      final-v′ final-no′ final-closed′
      source-typing target-typing)
    frames
