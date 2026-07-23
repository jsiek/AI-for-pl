module proof.DGG.TerminalForward.NuDGGTerminalForwardClosedDef where

-- File Charter:
--   * Defines the closed forward source-value terminal fact consumed by the
--     three-component DGG boundary.
--   * Keeps its full transported world, stores, types, and value relation
--     visible at the use site.
--   * Contains no implementation, postulate, hole, permissive option, or
--     broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; _—↠[_]_
  )
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)


ClosedForwardSourceValueᵀ : Set₁
ClosedForwardSourceValueᵀ =
  ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  RuntimeOK N →
  RuntimeOK N′ →
  [] ∣ 0 ∣ 0 ∣ [] ∣ [] ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  ∀ V χs →
  N —↠[ χs ] V →
  Value V →
  ∃[ V′ ] (Σ[ χs′ ∈ StoreChanges ]
  (∃[ Φ ] (Σ[ ρ ∈
      StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
  (Σ[ q ∈
      (Φ ∣ applyTyCtxs χs 0
        ⊢ applyTys χs A ⊑ applyTys χs′ B
        ⊣ applyTyCtxs χs′ 0) ]
    ((N′ —↠[ χs′ ] V′) ×
     Value V′ ×
     (leftStoreⁱ ρ ≡ applyStores χs []) ×
     (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
     Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
       ⊢ᴺ V ⊑ V′
       ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))
