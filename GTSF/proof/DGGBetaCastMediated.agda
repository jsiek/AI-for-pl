module proof.DGGBetaCastMediated where

-- File Charter:
--   * Mediated-store DGG application dispatcher for target
--     beta-through-function-cast steps.
--   * Delegates catchup-heavy source application packaging to
--     `DGGBetaCastCatchupMediated`.
--   * Keeps the main `DynamicGradualGuaranteeMediated` module slim.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; ∃-syntax)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import Mediation
open import MediatedNarrowing
open import proof.CatchupSeparated using (applyLeftChanges)
open import proof.DGGBetaCastCatchupMediated using
  ( mediated-dgg-beta-cast-left-first
  ; mediated-dgg-beta-cast-right-first
  )

------------------------------------------------------------------------
-- Application beta-cast dispatch
------------------------------------------------------------------------

mediated-dgg-beta-cast :
  ∀ {ΔL ΔR ρ L R V′ W′ c d p q A A′ B B′} →
  RuntimeOK (L · R) →
  Value V′ →
  Value W′ →
  (p↦qᶜ :
    ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ᵐ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ W′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
      ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta-cast (ok-no (no•-· noL noR))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-left-first
    (ok-no noL) (ok-no noR) noR
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₁ okL noR)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-left-first
    okL (ok-no noR) noR
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-no noR))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-left-first
    (ok-no noL) (ok-no noR) noR
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-• vV noV))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-• vV noV)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-·₁ okR₁ noR₂))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-·₁ okR₁ noR₂)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-·₂ vR₁ noR₁ okR₂))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-·₂ vR₁ noR₁ okR₂)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-ν okR))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-ν okR)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-⊕₁ okR₁ noR₂))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-⊕₁ okR₁ noR₂)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-⊕₂ vR₁ noR₁ okR₂))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-⊕₂ vR₁ noR₁ okR₂)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-⟨⟩ okR))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-⟨⟩ okR)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
