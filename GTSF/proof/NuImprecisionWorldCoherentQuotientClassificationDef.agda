module proof.NuImprecisionWorldCoherentQuotientClassificationDef where

-- File Charter:
--   * Defines coherent classification of one terminal quotient down-up node.
--   * Returns either a complete coherent catch-up, a plain outer-inst
--     residual, or the eager outer-inst/function-tag residual, together with
--     source value and reduction evidence.
--   * Contains no classifier implementation or recursive dispatcher import.

import Coercions as C
open import Coercions using (_!; _︔_; ⇑ᶜ)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (_—↠[_]_; bind; keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using
  (No•; Term; Value; blame; ⇑ᵗᵐ; _•; _⟨_⟩)
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


WorldCoherentQuotientClassificationᵀ : Set₁
WorldCoherentQuotientClassificationᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V V′ : Term}
    {D D′ A A′ : Ty} {d d′ u u′ : C.Coercion}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  Value V′ →
  No• V′ →
  C.Inert d′ →
  C.Inert u′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩
    ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  ((Value V × No• V) ⊎ V ≡ blame) →
  WorldCoherentLeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ C.inst B s) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ bind ★ ∷ [] ]
          ((⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩) ×
      Value (V ⟨ d ⟩) × No• (V ⟨ d ⟩)
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ (C.inst B s ︔ ((★ ⇒ ★) !))) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ keep ∷ bind ★ ∷ [] ]
          ((((⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
            ⟨ ⇑ᶜ ((★ ⇒ ★) !) ⟩)) ×
      Value (V ⟨ d ⟩) × No• (V ⟨ d ⟩)
