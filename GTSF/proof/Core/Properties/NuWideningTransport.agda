module proof.Core.Properties.NuWideningTransport where

-- File Charter:
--   * Transports widening evidence through lists of runtime store changes.
--   * Separates generic and mode-preserving widening transport.
--   * Contains no term-imprecision or simulation-result dependency.
--   * Keeps store-change cast transport out of the simulation core.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Coercions using (ModeEnv)
open import NarrowWiden using
  ( widen-renameᵗ
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( applyStores
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  )
open import Store using (StoreIncl-drop)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import proof.Core.Properties.CoercionProperties using (ModeRename)
open import proof.Core.Properties.ReductionProperties using (applyCoercions)
open import proof.Core.Properties.TypePreservation using (applyWiden-typing)
open import proof.Core.Properties.TypeProperties using (TyRenameWf-suc)


apply-widens-typing :
  ∀ {χs μ Δ Σ c A B} →
  CastMode μ →
  SealModeStore★ μ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ μ′ (applyStores χs Σ) ×
    (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
      ⊢ applyCoercions χs c
        ∶ applyTys χs A ⊑ applyTys χs B)
apply-widens-typing {χs = []} {μ = μ} mode seal★ c⊑ =
  μ , mode , seal★ , c⊑
apply-widens-typing {χs = χ ∷ χs} mode seal★ c⊑
    with applyWiden-typing {χ = χ} mode seal★ c⊑
apply-widens-typing {χs = χ ∷ χs} mode seal★ c⊑
    | μ′ , mode′ , seal★′ , c′⊑ =
  apply-widens-typing {χs = χs} mode′ seal★′ c′⊑

apply-fixed-widens-typing :
  ∀ {χs μ Δ Σ c A B} →
  ModeRename suc μ μ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  μ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
    ⊢ applyCoercions χs c
      ∶ applyTys χs A ⊑ applyTys χs B
apply-fixed-widens-typing {χs = []} mode-suc c⊑ = c⊑
apply-fixed-widens-typing {χs = keep ∷ χs} mode-suc c⊑ =
  apply-fixed-widens-typing {χs = χs} mode-suc c⊑
apply-fixed-widens-typing {χs = bind X ∷ χs} mode-suc c⊑ =
  apply-fixed-widens-typing {χs = χs} mode-suc
    (widen-weaken ≤-refl StoreIncl-drop
      (widen-renameᵗ TyRenameWf-suc mode-suc c⊑))
