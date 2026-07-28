module TypeSafety where

-- File Charter:
--   * Public type-safety theorem for GTPLC.
--   * Combines multi-step preservation with progress for the final term.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Types
open import TyStore
open import Terms
open import Reduction
open import proof.Progress using (done; step; crash; progress)
open import proof.Preservation using (multi-preservation)

type-safety : ∀ {Δ : TyCtx}{Σ : TyStore}{M N : Term}
  {A : Ty}{χs : StoreChanges}
  → StoreWf Δ Σ
  → Δ ∣ Σ ∣ [] ⊢ M ⦂ A
  → M —↠[ χs ] N
  → (∃[ χ ] ∃[ N′ ] (N —→[ χ ] N′))
      ⊎ Value N ⊎ (N ≡ blame)
type-safety wfΣ M⊢ M—↠N
    with progress (multi-preservation wfΣ M⊢ M—↠N)
type-safety wfΣ M⊢ M—↠N | step {χ = χ} {N = N′} N→N′ =
  inj₁ (χ , N′ , N→N′)
type-safety wfΣ M⊢ M—↠N | done vN =
  inj₂ (inj₁ vN)
type-safety wfΣ M⊢ M—↠N | crash eq =
  inj₂ (inj₂ eq)
