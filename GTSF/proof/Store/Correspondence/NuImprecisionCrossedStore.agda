module proof.Store.Correspondence.NuImprecisionCrossedStore where

-- File Charter:
--   * Defines the low-fanout crossed two-allocation relational-store fixture.
--   * Proves its physical left/right projections and its two correspondence
--     links.
--   * Excludes the core relational-store definition and term imprecision.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Types using (Ty; TyCtx; WfTy)
open import
  proof.Store.Core.NuImprecisionRelationalStoreDef


crossedStoreⁱ :
  ∀ {Φ Δᴸ Δᴿ A₀ A₁ B₀ B₁} →
  WfTy Δᴸ A₀ →
  WfTy Δᴸ A₁ →
  WfTy Δᴿ B₀ →
  WfTy Δᴿ B₁ →
  (p₀₁ : Φ ∣ Δᴸ ⊢ A₀ ⊑ B₁ ⊣ Δᴿ) →
  (p₁₀ : Φ ∣ Δᴸ ⊢ A₁ ⊑ B₀ ⊣ Δᴿ) →
  StoreImp Φ Δᴸ Δᴿ →
  StoreImp Φ Δᴸ Δᴿ
crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ =
  store-left zero _ hA₀ ∷
  store-left (suc zero) _ hA₁ ∷
  store-right zero _ hB₀ ∷
  store-right (suc zero) _ hB₁ ∷
  store-link zero _ (suc zero) _ p₀₁ ∷
  store-link (suc zero) _ zero _ p₁₀ ∷
  ρ


leftStoreⁱ-crossed :
  ∀ {Φ Δᴸ Δᴿ A₀ A₁ B₀ B₁}
    {hA₀ : WfTy Δᴸ A₀} {hA₁ : WfTy Δᴸ A₁}
    {hB₀ : WfTy Δᴿ B₀} {hB₁ : WfTy Δᴿ B₁}
    {p₀₁ : Φ ∣ Δᴸ ⊢ A₀ ⊑ B₁ ⊣ Δᴿ}
    {p₁₀ : Φ ∣ Δᴸ ⊢ A₁ ⊑ B₀ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  leftStoreⁱ (crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ)
    ≡ (zero , A₀) ∷ (suc zero , A₁) ∷ leftStoreⁱ ρ
leftStoreⁱ-crossed = refl


rightStoreⁱ-crossed :
  ∀ {Φ Δᴸ Δᴿ A₀ A₁ B₀ B₁}
    {hA₀ : WfTy Δᴸ A₀} {hA₁ : WfTy Δᴸ A₁}
    {hB₀ : WfTy Δᴿ B₀} {hB₁ : WfTy Δᴿ B₁}
    {p₀₁ : Φ ∣ Δᴸ ⊢ A₀ ⊑ B₁ ⊣ Δᴿ}
    {p₁₀ : Φ ∣ Δᴸ ⊢ A₁ ⊑ B₀ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  rightStoreⁱ (crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ)
    ≡ (zero , B₀) ∷ (suc zero , B₁) ∷ rightStoreⁱ ρ
rightStoreⁱ-crossed = refl


crossedStoreⁱ-new-old :
  ∀ {Φ Δᴸ Δᴿ A₀ A₁ B₀ B₁}
    {hA₀ : WfTy Δᴸ A₀} {hA₁ : WfTy Δᴸ A₁}
    {hB₀ : WfTy Δᴿ B₀} {hB₁ : WfTy Δᴿ B₁}
    {p₀₁ : Φ ∣ Δᴸ ⊢ A₀ ⊑ B₁ ⊣ Δᴿ}
    {p₁₀ : Φ ∣ Δᴸ ⊢ A₁ ⊑ B₀ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreCorresponds
    (crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ)
    zero A₀ (suc zero) B₁ p₀₁
crossedStoreⁱ-new-old =
  correspondence-linked
    (there (there (there (there (here refl)))))


crossedStoreⁱ-old-new :
  ∀ {Φ Δᴸ Δᴿ A₀ A₁ B₀ B₁}
    {hA₀ : WfTy Δᴸ A₀} {hA₁ : WfTy Δᴸ A₁}
    {hB₀ : WfTy Δᴿ B₀} {hB₁ : WfTy Δᴿ B₁}
    {p₀₁ : Φ ∣ Δᴸ ⊢ A₀ ⊑ B₁ ⊣ Δᴿ}
    {p₁₀ : Φ ∣ Δᴸ ⊢ A₁ ⊑ B₀ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreCorresponds
    (crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ)
    (suc zero) A₁ zero B₀ p₁₀
crossedStoreⁱ-old-new =
  correspondence-linked
    (there (there (there (there (there (here refl))))))
