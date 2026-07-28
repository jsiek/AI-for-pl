module proof.Core.Properties.NuNarrowingTransport where

-- File Charter:
--   * Transports narrowing evidence through lists of runtime store changes.
--   * Separates generic, mode-preserving, and quotient-spine transport.
--   * Contains no term-imprecision or simulation-result dependency.
--   * Keeps store-change cast transport out of the simulation core.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Coercions using (id-onlyᵈ)
open import NarrowWiden using
  ( narrow-renameᵗ
  ; narrow-weaken
  ; _∣_∣_⊢_∶_⊒_
  )
open import NuReduction using
  ( applyStores
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  )
open import QuotientImprecisionCompatibility using
  (SpineCastMode; gradual↓; id-only↓)
open import Store using (StoreIncl-drop)
open import TermTyping using
  (CastMode; SealModeStore★)
open import proof.Core.Properties.CoercionProperties using
  (ModeRename; modeRename-id-only)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import proof.Core.Properties.TypePreservation using
  (applyNarrow-typing)
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-suc)


apply-narrows-typing :
  ∀ {χs μ Δ Σ c A B} →
  CastMode μ →
  SealModeStore★ μ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ μ′ (applyStores χs Σ) ×
    (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
      ⊢ applyCoercions χs c
        ∶ applyTys χs A ⊒ applyTys χs B)
apply-narrows-typing {χs = []} {μ = μ} mode seal★ c⊒ =
  μ , mode , seal★ , c⊒
apply-narrows-typing {χs = χ ∷ χs} mode seal★ c⊒
    with applyNarrow-typing {χ = χ} mode seal★ c⊒
apply-narrows-typing {χs = χ ∷ χs} mode seal★ c⊒
    | μ′ , mode′ , seal★′ , c′⊒ =
  apply-narrows-typing {χs = χs} mode′ seal★′ c′⊒


apply-fixed-narrows-typing :
  ∀ {χs μ Δ Σ c A B} →
  ModeRename suc μ μ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  μ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
    ⊢ applyCoercions χs c
      ∶ applyTys χs A ⊒ applyTys χs B
apply-fixed-narrows-typing {χs = []} mode-suc c⊒ = c⊒
apply-fixed-narrows-typing {χs = keep ∷ χs} mode-suc c⊒ =
  apply-fixed-narrows-typing {χs = χs} mode-suc c⊒
apply-fixed-narrows-typing {χs = bind X ∷ χs} mode-suc c⊒ =
  apply-fixed-narrows-typing {χs = χs} mode-suc
    (narrow-weaken ≤-refl StoreIncl-drop
      (narrow-renameᵗ TyRenameWf-suc mode-suc c⊒))


apply-spine-narrows-typing :
  ∀ {χs μ Δ Σ c A B} →
  SpineCastMode Σ μ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  ∃[ μ′ ]
    (SpineCastMode (applyStores χs Σ) μ′ ×
    (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
      ⊢ applyCoercions χs c
        ∶ applyTys χs A ⊒ applyTys χs B))
apply-spine-narrows-typing {χs = χs} id-only↓ c⊒ =
  id-onlyᵈ , id-only↓ ,
  apply-fixed-narrows-typing
    {χs = χs} (modeRename-id-only suc) c⊒
apply-spine-narrows-typing {χs = χs}
    (gradual↓ mode seal★) c⊒
    with apply-narrows-typing {χs = χs} mode seal★ c⊒
apply-spine-narrows-typing {χs = χs}
    (gradual↓ mode seal★) c⊒
    | μ′ , mode′ , seal★′ , c′⊒ =
  μ′ , gradual↓ mode′ seal★′ , c′⊒
