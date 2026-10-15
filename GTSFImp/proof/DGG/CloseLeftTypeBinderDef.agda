{-# OPTIONS --safe #-}

module proof.DGG.CloseLeftTypeBinderDef where

-- File Charter:
--   * States the CTI induction that closes a source-only static type-binder
--     relation after both endpoints perform runtime type application.
--   * Aligns the fresh source and target runtime binders and adds their
--     structural reveal conversions in the paired bind world.
--   * Exposes the resulting type-imprecision and CTI witnesses inline.

open import Data.Fin using (zero)
open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (Σ-syntax)

open import Types using (Ty; `∀; _[_]ᵗ; ⇑ᵗ)
open import TyStore using (TyStore)
open import Conversion using (〖_,_↑_〗)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; Λ_; _↑_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World


CloseLeftTypeBinderᵀ : Set
CloseLeftTypeBinderᵀ = ∀ {Δᴸ Δᴿ : Nat.ℕ}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {A : Ty Δᴸ} {A′ : Ty Δᴿ}
    {V : Term (Nat.suc Δᴸ)} {V′ : Term (Nat.suc Δᴿ)}
    {C : Ty (Nat.suc Δᴸ)} {C′ : Ty (Nat.suc Δᴿ)}
    {p : C ⊑ᵀ⟨ liftLeftᶜ γ ⟩ `∀ C′}
  → Value V
  → Value V′
  → liftLeftᶜ γ ⊢² V ⊑ Λ V′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ C′ [ A′ ]ᵗ)
  → Σ[ s ∈ ⇑ᵗ (C [ A ]ᵗ) ⊑ᵀ⟨ bindBothᶜ γ q ⟩
        ⇑ᵗ (C′ [ A′ ]ᵗ) ]
      bindBothᶜ γ q ⊢²
        V ↑ 〖 zero , ⇑ᵗ A ↑ C 〗 ⊑
        V′ ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ∶ s
