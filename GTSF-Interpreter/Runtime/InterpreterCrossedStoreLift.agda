module Runtime.InterpreterCrossedStoreLift where

-- File Charter:
--   * Constructs the second relational-store lift used by an adjacent
--     universal exchange and records the two unary store equations.
--   * Uses only static store and type-renaming metatheory.
--   * Contains no interpreter execution, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import ImprecisionWf using (swapRight∀∀ᵢ)
import NuTermImprecision as NTI
open import proof.MaximalLowerBoundsWf using
  ( ∀ᵢᶜ
  ; ⊑-crossed-double-lift∀∀ᵢ
  )
open import proof.TypeProperties using
  (TyRenameWf-suc; renameᵗ-preserves-WfTy)
open import Types


left-store-double-lift :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : NTI.StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : NTI.StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  NTI.LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  ⟰ᵗ (⟰ᵗ (NTI.leftStoreⁱ ρ₀)) ≡ NTI.leftStoreⁱ ρ₂
left-store-double-lift liftρ₁ liftρ₂ =
  trans
    (cong ⟰ᵗ (sym (NTI.leftStoreⁱ-lift liftρ₁)))
    (sym (NTI.leftStoreⁱ-lift liftρ₂))


right-store-double-lift :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : NTI.StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : NTI.StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  NTI.LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  ⟰ᵗ (⟰ᵗ (NTI.rightStoreⁱ ρ₀)) ≡ NTI.rightStoreⁱ ρ₂
right-store-double-lift liftρ₁ liftρ₂ =
  trans
    (cong ⟰ᵗ (sym (NTI.rightStoreⁱ-lift liftρ₁)))
    (sym (NTI.rightStoreⁱ-lift liftρ₂))


crossed-lift-store :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : NTI.StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  ∃[ ρ₂ ] NTI.LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂
crossed-lift-store NTI.lift-store-[] =
  [] , NTI.lift-store-[]
crossed-lift-store
    (NTI.lift-store-∷ {p = p} liftρ)
    with crossed-lift-store liftρ
crossed-lift-store
    (NTI.lift-store-∷ {p = p} liftρ)
    | ρ₂ , liftρ₂ =
  _ , NTI.lift-store-∷
    {p′ = ⊑-crossed-double-lift∀∀ᵢ p}
    liftρ₂
crossed-lift-store
    (NTI.lift-store-left {hA′ = hA′} liftρ)
    with crossed-lift-store liftρ
crossed-lift-store
    (NTI.lift-store-left {hA′ = hA′} liftρ)
    | ρ₂ , liftρ₂ =
  _ , NTI.lift-store-left
    {hA′ = renameᵗ-preserves-WfTy hA′ TyRenameWf-suc}
    liftρ₂
crossed-lift-store
    (NTI.lift-store-right {hB′ = hB′} liftρ)
    with crossed-lift-store liftρ
crossed-lift-store
    (NTI.lift-store-right {hB′ = hB′} liftρ)
    | ρ₂ , liftρ₂ =
  _ , NTI.lift-store-right
    {hB′ = renameᵗ-preserves-WfTy hB′ TyRenameWf-suc}
    liftρ₂
crossed-lift-store
    (NTI.lift-store-link {p = p} liftρ)
    with crossed-lift-store liftρ
crossed-lift-store
    (NTI.lift-store-link {p = p} liftρ)
    | ρ₂ , liftρ₂ =
  _ , NTI.lift-store-link
    {p′ = ⊑-crossed-double-lift∀∀ᵢ p}
    liftρ₂
