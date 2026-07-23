module proof.Target.SealTag.NuImprecisionTargetSealCancellationDef where

-- File Charter:
--   * Defines exact-world cancellation of a terminal target seal.
--   * Exposes world coherence and target-store well-formedness explicitly.
--   * Contains no implementation or simulation dependency.

open import Coercions using (seal)
open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyVar; ＇_)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


TargetSealCancellationᵀ : Set₁
TargetSealCancellationᵀ =
  ∀ {Φ Δᴸ Δᴿ} {W V : Term} {A X X′ : Ty} {β : TyVar}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ β ⊣ Δᴿ} →
  WorldCoherent ρ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  Value W →
  No• W →
  Value V →
  (β , X′) ∈ rightStoreⁱ ρ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ V ⟨ seal X β ⟩ ⦂ A ⊑ ＇ β ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ X′ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ V ⦂ A ⊑ X′ ∶ q
