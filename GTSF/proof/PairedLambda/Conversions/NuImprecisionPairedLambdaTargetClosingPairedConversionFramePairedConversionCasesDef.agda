module
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedConversionFramePairedConversionCasesDef
  where

-- File Charter:
--   * Defines the exact reveal and conceal constructor branches required by
--     paired-conversion-frame target closing.
--   * Keeps the recursive closing result, proof-relevant frame view, external
--     paired conversion fields, both allocation lifts, and final reveal fused
--     in each branch.
--   * Contains no dispatcher, implementation, postulate, hole, permissive
--     option, broad simulation import, recursive frame closer, or handler
--     adapter.

import Coercions as C
open import Coercions using (Coercion; Inert; ModeEnv)
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuTerms using (Term; ⇑ᵗᵐ; _•; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedConversion
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; TyVar
  ; WfTy
  ; `∀
  ; extᵗ
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


PairedLambdaTargetClosingPairedConversionFramePairedRevealClosingᵀ : Set₁
PairedLambdaTargetClosingPairedConversionFramePairedRevealClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ C′ X X′ : Ty}
    {d d′ : Coercion} {η η′ : ModeEnv} {α β : TyVar}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameClosingMotive ρ₀
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ₀
    W W′ (`∀ B) B′ q →
  Inert d′ →
  StoreCorresponds ρ₀ α X β X′ pX →
  RevealConversion η Δᴸ (leftStoreⁱ ρ₀) α X
    (C.`∀ d) (`∀ B) (`∀ C) →
  RevealConversion η′ Δᴿ (rightStoreⁱ ρ₀) β X′
    d′ B′ C′ →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {A C₀′ D E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C₀′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C₀′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ C} {C′} {`∀ (`∀ E)} {`∀ C₀′} r (∀ⁱ s) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ
      (((⇑ᵗᵐ (W ⟨ C.`∀ d ⟩)) •) ⟨ c ⟩)
        ⟨ C.`∀ t ⟩
      ⊑ (W′ ⟨ d′ ⟩) ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C₀′ ∶ ⊑-source-liftνᵢ p


PairedLambdaTargetClosingPairedConversionFramePairedConcealClosingᵀ : Set₁
PairedLambdaTargetClosingPairedConversionFramePairedConcealClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ C′ X X′ : Ty}
    {d d′ : Coercion} {η η′ : ModeEnv} {α β : TyVar}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameClosingMotive ρ₀
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ₀
    W W′ (`∀ B) B′ q →
  Inert d′ →
  StoreCorresponds ρ₀ α X β X′ pX →
  ConcealConversion η Δᴸ (leftStoreⁱ ρ₀) α X
    (C.`∀ d) (`∀ B) (`∀ C) →
  ConcealConversion η′ Δᴿ (rightStoreⁱ ρ₀) β X′
    d′ B′ C′ →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {A C₀′ D E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C₀′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C₀′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ C} {C′} {`∀ (`∀ E)} {`∀ C₀′} r (∀ⁱ s) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ
      (((⇑ᵗᵐ (W ⟨ C.`∀ d ⟩)) •) ⟨ c ⟩)
        ⟨ C.`∀ t ⟩
      ⊑ (W′ ⟨ d′ ⟩) ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C₀′ ∶ ⊑-source-liftνᵢ p
