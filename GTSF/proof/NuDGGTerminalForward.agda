{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuDGGTerminalForward where

-- File Charter:
--   * Owns the exact forward source-value terminal theorem required by the
--     closed Nu DGG spine.
--   * The statement is frozen and checked; the proof is intentionally the
--     active boundary while source-step simulation and right value catch-up
--     are developed.

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
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuDGGClosedWorld using (empty-store-wf)


forward-source-value-generalᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  ∀ V χs →
  M —↠[ χs ] V →
  Value V →
  ∃[ V′ ] (Σ[ χs′ ∈ StoreChanges ]
  (∃[ Ψ ] (Σ[ ρ′ ∈
      StoreImp Ψ
        (applyTyCtxs χs Δᴸ) (applyTyCtxs χs′ Δᴿ) ]
  (Σ[ q ∈
      (Ψ ∣ applyTyCtxs χs Δᴸ
        ⊢ applyTys χs A ⊑ applyTys χs′ B
        ⊣ applyTyCtxs χs′ Δᴿ) ]
    ((M′ —↠[ χs′ ] V′) ×
     Value V′ ×
     (leftStoreⁱ ρ′ ≡ applyStores χs (leftStoreⁱ ρ)) ×
     (rightStoreⁱ ρ′ ≡ applyStores χs′ (rightStoreⁱ ρ)) ×
     Ψ ∣ applyTyCtxs χs Δᴸ ∣ applyTyCtxs χs′ Δᴿ ∣ ρ′ ∣ []
       ⊢ᴺ V ⊑ V′
       ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))
forward-source-value-generalᵀ = {!!}


forward-source-valueᵀ :
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
forward-source-valueᵀ okN okN′ N⊑N′ =
  forward-source-value-generalᵀ
    empty-store-wf empty-store-wf okN okN′ N⊑N′
