module proof.NuImprecisionWorldCoherentQuotientInstFunTagCatchupDef where

-- File Charter:
--   * Defines world-coherent catch-up for the eager quotient-inst/function-tag
--     residual introduced by DualGenSafe widening.
--   * Keeps the leading instantiation and trailing ground tag visible in the
--     contract so final quotient assembly cannot confuse it with plain inst.
--   * Contains no implementation or recursive simulation dependency.

import Coercions as C
open import Coercions using (_!; _︔_)
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; ★; _⇒_)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentQuotientInstFunTagCatchupᵀ : Set₁
WorldCoherentQuotientInstFunTagCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term} {B D D′ A A′ : Ty}
    {d d′ s u′ : C.Coercion}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK
    ((V ⟨ d ⟩) ⟨ C.inst B s ︔ ((★ ⇒ ★) !) ⟩) →
  Value (V ⟨ d ⟩) →
  No• (V ⟨ d ⟩) →
  Value V′ →
  No• V′ →
  C.Inert d′ →
  C.Inert u′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩ ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s ︔ ((★ ⇒ ★) !)) u′ D D′ A A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ C.inst B s ︔ ((★ ⇒ ★) !) ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
