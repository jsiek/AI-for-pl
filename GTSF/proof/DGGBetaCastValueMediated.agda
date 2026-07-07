module proof.DGGBetaCastValueMediated where

-- File Charter:
--   * Public mediated-store DGG value/wrap wrapper for target
--     beta-through-function-cast steps.
--   * Delegates the large structural recursion to
--     `DGGBetaCastValueShapeMediated`.
--   * Kept small so the beta-cast application packaging module remains quick
--     to reload.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import Mediation
open import MediatedNarrowing
open import proof.CatchupSeparated using (applyLeftChanges)
open import proof.DGGBetaCastValueShapeMediated using
  (mediated-dgg-beta-cast-value-shape)

------------------------------------------------------------------------
-- Value-shape public wrapper
------------------------------------------------------------------------

mediated-dgg-beta-cast-value :
  ∀ {ΔL ΔR ρ L R V′ W′ c d pᵈ p q A A′ B B′} →
  Value L →
  No• L →
  Value R →
  No• R →
  Value V′ →
  Value W′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ W′ ∶ pᵈ ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta-cast-value
    vL noL vR noR vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  let
    χs , N , ΔL′ , ρ′ , red , ΔL′≡ , ρ′≡ , N⊒target =
      mediated-dgg-beta-cast-value-shape
        vL noL vR noR vV′ vW′ L⊒V′cd refl p-domainᶜ R⊒W′
  in
  χs , N , ΔL′ , ρ′ , _ , _ , _ , red ,
  ΔL′≡ , ρ′≡ , refl , refl , N⊒target
