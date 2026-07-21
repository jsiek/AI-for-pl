module
  proof.NuImprecisionLeftSourceAllocationRuntimeTargetBulletDef
  where

-- File Charter:
--   * Defines the canonical target-runtime-bullet leaf for source-allocation
--     runtime transport.
--   * Keeps the original and source-renamed target-lift worlds explicit so
--     the proof can invert their store and context renaming witnesses.
--   * Returns the renamed `⊑αᵀ` relation directly, without a path, result,
--     outcome, or view carrier.
--   * Contains no implementation, postulate, hole, permissive option, or
--     termination bypass.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using
  ( ImpCtx
  ; ⇑ᴿᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftRightCtxⁱ
  ; LiftRightStoreⁱ
  ; StoreImp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; renameᵗᵐ
  ; ⇑ᵗᵐ
  ; _•
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; renameᵗ
  ; ⇑ᵗ
  )
open import proof.MaximalLowerBoundsWf using
  ( νᵢᶜ
  ; rename-assm²-source-νᵢ
  )
open import proof.NuImprecisionSimulationCore using
  ( LeftCtxRenameⁱ
  ; LeftStoreRenameⁱ
  ; ⊑-rename-leftᵢ
  )
open import proof.TypeProperties using (TyRenameWf-suc)


LeftSourceAllocationRuntimeTargetBulletᵀ : Set₁
LeftSourceAllocationRuntimeTargetBulletᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {ρᴸᴿ : StoreImp (νᵢᶜ (⇑ᴿᵢ Φ)) (suc Δᴸ) (suc Δᴿ)}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {γᴸᴿ : CtxImp (νᵢᶜ (⇑ᴿᵢ Φ)) (suc Δᴸ) (suc Δᴿ)}
    {N L′ : Term} {A B C′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ}
    {h⇑A h⇑A′ : WfTy (suc Δᴿ) (⇑ᵗ A)} →
  LeftStoreRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc
    (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ)
    (store-right zero (⇑ᵗ A) h⇑A′ ∷ ρᴸᴿ) →
  LeftCtxRenameⁱ suc rename-assm²-source-νᵢ
    TyRenameWf-suc γᴿ γᴸᴿ →
  No• N →
  Value L′ →
  No• L′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ N ⊑ L′ ⦂ B ⊑ `∀ C′ ∶ q →
  Δᴸ
    ∣ leftStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ)
    ∣ leftCtxⁱ γᴿ ⊢ N ⦂ B →
  suc Δᴿ
    ∣ rightStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ)
    ∣ rightCtxⁱ γᴿ ⊢ (⇑ᵗᵐ L′) • ⦂ C′ →
  νᵢᶜ (⇑ᴿᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ
    ∣ store-right zero (⇑ᵗ A) h⇑A′ ∷ ρᴸᴿ ∣ γᴸᴿ
    ⊢ᴺ renameᵗᵐ suc N ⊑ (⇑ᵗᵐ L′) •
    ⦂ renameᵗ suc B ⊑ C′
    ∶ ⊑-rename-leftᵢ suc rename-assm²-source-νᵢ
      TyRenameWf-suc r
