module
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameDef
  where

-- File Charter:
--   * Defines the one shared target-only frame capability needed by the
--     paired-lambda target-closing frame interpreter.
--   * Keeps reveal, conceal, narrowing, widening, and identity-mode widening
--     as explicit alternatives in one theorem statement.
--   * Contains no implementation, semantic handler, postulate, or permissive
--     option.

open import Coercions using (Coercion; Inert; ModeEnv; id-onlyᵈ)
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_; _∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)


PairedLambdaTargetClosingFrameClosingTargetFrameᵀ : Set₁
PairedLambdaTargetClosingFrameClosingTargetFrameᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ C′ : Ty} {c′ : Coercion}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameClosingMotive ρ W W′ F B′ q →
  Inert c′ →
  ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ c′ B′ C′)
   ⊎
   (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ c′ B′ C′)
   ⊎
   (∃[ μ′ ]
      CastMode μ′ ×
      SealModeStore★ μ′ (rightStoreⁱ ρ) ×
      (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ B′ ⊒ C′))
   ⊎
   (∃[ μ′ ]
      CastMode μ′ ×
      SealModeStore★ μ′ (rightStoreⁱ ρ) ×
      (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ B′ ⊑ C′))
   ⊎
   (SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) ×
    (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ c′ ∶ B′ ⊑ C′))) →
  PairedLambdaTargetClosingFrameClosingMotive
    ρ W (W′ ⟨ c′ ⟩) F C′ r
