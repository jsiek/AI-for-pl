module
  proof.PairedLambda.LambdaLeaves.MatchedUnseal.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingDef
  where

-- File Charter:
--   * Defines the fused live matched-unseal branch of matched-`Lambda` target
--     closing after source and target reveal inversion.
--   * Fixes the corresponding source type to a universal, so both body
--     endpoints are variables sealed at the matched ambient names.
--   * Retains the final reveal, both allocation lifts, world coherence,
--     source-name exclusivity, and final left-store well-formedness.
--   * Contains no implementation, postulate, hole, permissive option,
--     pre-final-reveal rotation, or broad simulation import.

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
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; Λ_
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
  ; ＇_
  ; `∀
  ; extᵗ
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


PairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingᵀ :
  Set₁
PairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρΛ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {γΛ : CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {V V′ : Term} {α β : TyVar}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ＇ (suc α) ⊑ ＇ (suc β) ⊣ suc Δᴿ} →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρΛ →
  LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] γΛ →
  Value V → No• V → Value V′ → No• V′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρΛ ∣ γΛ
    ⊢ᴺ V ⊑ V′ ⦂ ＇ (suc α) ⊑ ＇ (suc β) ∶ r →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {Aν D F X′ : Ty} {c c′ t : Coercion}
    {η η′ μ : ModeEnv}
    {pX : Φ ∣ Δᴸ ⊢ `∀ F ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ (⇑ᵗ X′) ⊣ Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ
      ⊢ `∀ (renameᵗ (extᵗ suc) F) ⊑ ⇑ᵗ X′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  (h⇑Aν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ Aν) h⇑Aν ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ Aν)) t (renameᵗ (extᵗ suc) F)
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  StoreCorresponds ρ α (`∀ F) β X′ pX →
  RevealConversion (C.extᵈ η) (suc Δᴸ) (⟰ᵗ (leftStoreⁱ ρ))
    (suc α) (⇑ᵗ (`∀ F)) c (＇ (suc α))
      (`∀ (renameᵗ (extᵗ suc) F)) →
  RevealConversion (C.extᵈ η′) (suc Δᴿ) (⟰ᵗ (rightStoreⁱ ρ))
    (suc β) (⇑ᵗ X′) c′ (＇ (suc β)) (⇑ᵗ X′) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ Aν) h⇑Aν ∷ ρν ∣ []
    ⊢ᴺ (((⇑ᵗᵐ (Λ V)) •) ⟨ c ⟩) ⟨ C.`∀ t ⟩
      ⊑ (Λ V′) ⟨ C.`∀ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ (⇑ᵗ X′) ∶ ⊑-source-liftνᵢ p
