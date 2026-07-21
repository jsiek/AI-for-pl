module proof.NuImprecisionSourceTagCancellationDef where

-- File Charter:
--   * Defines exact cancellation of one terminal source ground tag.
--   * Keeps the tag label identical in the premise and replacement source
--     type, excluding unrelated-label cancellation.
--   * Contains no implementation, store invariant, or simulation dependency.

open import Coercions using (_!)
open import Data.List using ([])
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ground; Ty; ★)


SourceTagCancellationᵀ : Set₁
SourceTagCancellationᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V W : Term} {B G : Ty}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ ★ ⊑ B ⊣ Δᴿ} →
  Ground G →
  Value V →
  Value W →
  No• W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⟨ G ! ⟩ ⊑ W ⦂ ★ ⊑ B ∶ p →
  (q : Φ ∣ Δᴸ ⊢ G ⊑ B ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ G ⊑ B ∶ q
