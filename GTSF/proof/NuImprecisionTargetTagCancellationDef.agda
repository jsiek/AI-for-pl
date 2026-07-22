module proof.NuImprecisionTargetTagCancellationDef where

-- File Charter:
--   * Defines cancellation of one terminal target ground tag.
--   * Returns equality of the discovered tag label with the requested ground
--     type and the ordinary relation at the requested precision index.
--   * Retained as a refuted generalized boundary: a source `gen` can be
--     related to a target carrying a different ground tag.
--   * Contains no implementation, result carrier, or simulation dependency.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (_!)
open import Data.List using ([])
open import Data.Product using (_×_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ground; Ty; ★)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)


TargetTagCancellationᵀ : Set₁
TargetTagCancellationᵀ =
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {A G H : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ} →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  Ground H →
  Value V →
  No• V →
  Value W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⟨ G ! ⟩ ⦂ A ⊑ ★ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ) →
  G ≡ H ×
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ A ⊑ H ∶ q
