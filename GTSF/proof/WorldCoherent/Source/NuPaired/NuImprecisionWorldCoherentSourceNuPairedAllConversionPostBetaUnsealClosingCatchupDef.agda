module
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupDef
  where

-- File Charter:
--   * Defines fused fresh-unseal cancellation and target closing after a
--     source-only allocation and paired universal conversion.
--   * Keeps paired reveal and conceal together because no intermediate
--     source-only precision index exists for the active unseal branch.
--   * Contains no implementation, dispatcher, or permissive option.

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
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; store-left
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( PairedConversion
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx; WfTy; ＇_; `∀; ⇑ᵗ)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ :
  Set₁
WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {V V′ : Term} {A C′ F F′ : Ty}
    {c c′ : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ F ⊑ F′ ⊣ suc Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ＇ zero ⊑ C′ ⊣ suc Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  WfTy Δᴸ A →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴸ)
    (leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρν))
    zero (⇑ᵗ A) (C.unseal zero (⇑ᵗ A))
    (＇ zero) (⇑ᵗ A) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  PairedConversion Φ Δᴸ Δᴿ ρ
    (C.`∀ c) (C.`∀ c′)
    {`∀ F} {`∀ F′} {`∀ (＇ zero)} {`∀ C′}
    (∀ⁱ r) (∀ⁱ q) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ F ⊑ `∀ F′ ∶ ∀ⁱ r →
  WorldCoherentLeftCatchupIndexedResult
    {N = (((⇑ᵗᵐ V) •) ⟨ c ⟩)
      ⟨ C.unseal zero (⇑ᵗ A) ⟩}
    {V′ = V′ ⟨ C.`∀ c′ ⟩}
    {ρ = store-left zero (⇑ᵗ A) h⇑A ∷ ρν}
    (⊑-source-liftνᵢ p)
