{-# OPTIONS --safe #-}

module proof.DGG.ClosePairedTypeBinderDef where

-- File Charter:
--   * States the CTI induction that closes a paired static type-binder scope
--     into the paired runtime allocation produced by type application.
--   * Keeps the endpoint terms and types fixed because liftBoth and paired
--     bind have the same embeddings and X⊑X mark; only their stores differ.
--   * Contains no closing proof or simulation result wrapper.

open import Data.List using ([])
import Data.Nat as Nat

open import Types using (Ty)
open import TyStore using (TyStore)
open import CastTerms using (Term; ⟨_,_,_⟩)
open import Imprecision using (X⊑X)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World


ClosePairedTypeBinderᵀ : Set
ClosePairedTypeBinderᵀ = ∀ {Δᴸ Δᴿ : Nat.ℕ}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {A : Ty Δᴸ} {A′ : Ty Δᴿ}
    {M : Term (Nat.suc Δᴸ)} {M′ : Term (Nat.suc Δᴿ)}
    {C : Ty (Nat.suc Δᴸ)} {C′ : Ty (Nat.suc Δᴿ)}
    {p : C ⊑ᵀ⟨ liftBothᶜ X⊑X γ ⟩ C′}
  → (q : A ⊑ᵀ⟨ γ ⟩ A′)
  → liftBothᶜ X⊑X γ ⊢² M ⊑ M′ ∶ p
  → bindBothᶜ γ q ⊢² M ⊑ M′ ∶ p
