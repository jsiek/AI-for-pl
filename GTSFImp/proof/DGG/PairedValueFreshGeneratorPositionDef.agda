{-# OPTIONS --safe #-}

module proof.DGG.PairedValueFreshGeneratorPositionDef where

-- File Charter:
--   * States that related values agree on the structural position of a fresh
--     paired runtime binder in their endpoint types.
--   * Includes value evidence because type imprecision alone admits the
--     uninhabited bottom-to-star case, whose raw type positions differ.
--   * Contains no value-shape induction or simulation result wrapper.

open import Data.List using ([])
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
open import TyStore using (TyStore; store-bind; Z∋)
open import CastTerms using (Term; Value; ⟨_,_,_⟩)
import Imprecision
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition)
open import proof.DGG.World
open import proof.TypeSafety.Preservation using
  (structural-reveal-typing)


PairedValueFreshGeneratorPositionᵀ : Set
PairedValueFreshGeneratorPositionᵀ = ∀ {Δᴸ Δᴿ : Nat.ℕ}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {A : Ty Δᴸ} {A′ : Ty Δᴿ}
    {C : Ty (Nat.suc Δᴸ)} {C′ : Ty (Nat.suc Δᴿ)}
    {V : Term (Nat.suc Δᴸ)} {V′ : Term (Nat.suc Δᴿ)}
    {p : C ⊑ᵀ⟨ liftBothᶜ Imprecision.X⊑X γ ⟩ C′}
  → Value V
  → Value V′
  → liftBothᶜ Imprecision.X⊑X γ ⊢² V ⊑ V′ ∶ p
  → revealGeneratorPosition
      (structural-reveal-typing {Σ = store-bind Σᴸ A} C (Z∋ refl))
    ≡ revealGeneratorPosition
      (structural-reveal-typing {Σ = store-bind Σᴿ A′} C′ (Z∋ refl))
