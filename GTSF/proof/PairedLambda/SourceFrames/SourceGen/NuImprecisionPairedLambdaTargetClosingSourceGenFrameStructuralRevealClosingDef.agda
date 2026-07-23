module
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingDef
  where

-- File Charter:
--   * Defines the structural core of the source-generic-frame paired-reveal
--     closing branch after both universal reveal conversions are inverted.
--   * Retains the recursive closing result, generic-frame relation, source
--     allocation, conversion correspondence, both inner reveals, and final
--     reveal as one fused reduction/commutation step.
--   * Contains no implementation, postulate, hole, permissive option, broad
--     simulation import, or recursive frame closer.

import Coercions as C
open import Coercions using (Coercion; ModeEnv)
open import Conversion using (RevealConversion)
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
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuStore using (StoreWf)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
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
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ : Set₁
PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {V N′ : Term} {F B B′ A C′ D E X X′ : Ty}
    {g c c′ t : Coercion} {η η′ θ : ModeEnv}
    {α β : TyVar}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ `∀ B′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
  Value V → No• V → Value N′ → No• N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ `∀ F ⊑ `∀ B′ ∶ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⟨ C.gen (`∀ F) g ⟩ ⊑ N′
      ⦂ `∀ B ⊑ `∀ B′ ∶ ∀ⁱ r →
  PairedLambdaTargetClosingFrameClosingMotive ρ₀
    V N′ F (`∀ B′) q →
  StoreImpPrefix ρ₀ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion (C.extᵈ θ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  StoreCorresponds ρ α X β X′ pX →
  RevealConversion (C.extᵈ η) (suc Δᴸ) (⟰ᵗ (leftStoreⁱ ρ))
    (suc α) (⇑ᵗ X) c B (`∀ E) →
  RevealConversion (C.extᵈ η′) (suc Δᴿ) (⟰ᵗ (rightStoreⁱ ρ))
    (suc β) (⇑ᵗ X′) c′ B′ C′ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ (((⇑ᵗᵐ (V ⟨ C.gen (`∀ F) g ⟩)) •) ⟨ c ⟩)
        ⟨ C.`∀ t ⟩
      ⊑ N′ ⟨ C.`∀ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C′ ∶ ⊑-source-liftνᵢ p
