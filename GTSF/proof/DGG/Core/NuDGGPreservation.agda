module proof.DGG.Core.NuDGGPreservation where

-- File Charter:
--   * Packages Nu store well-formedness preservation across a complete trace.
--   * Complements the existing multi-step typing and runtime preservation
--     theorems with the store invariant needed by terminal simulation.
--   * Depends on the checked one-step Nu preservation theorems.

open import Data.List using ([])

open import NuReduction using
  ( applyStores
  ; applyTyCtxs
  ; _—↠[_]_
  ; ↠-refl
  ; ↠-step
  )
open import NuStore using (StoreWf)
open import NuTerms using (RuntimeOK; _∣_∣_⊢_⦂_)
open import proof.DGG.Core.NuPreservation using
  ( preservation
  ; runtime-preservation
  ; store-preservation
  )


multi-store-preservation :
  ∀ {Δ Σ M N A χs} →
  StoreWf Δ Σ →
  RuntimeOK M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —↠[ χs ] N →
  StoreWf (applyTyCtxs χs Δ) (applyStores χs Σ)
multi-store-preservation wfΣ okM M⊢ ↠-refl = wfΣ
multi-store-preservation wfΣ okM M⊢ (↠-step red reds) =
  multi-store-preservation
    (store-preservation wfΣ M⊢ red)
    (runtime-preservation wfΣ okM M⊢ red)
    (preservation wfΣ okM M⊢ red)
    reds
