module EvalFresh where

-- File Charter:
--   * Fuel-bounded evaluator for closed extrinsic-inst PolyUpDown terms.
--   * Produces an explicit store-threaded reduction sequence by iterating
--   * `progress` and using `preservation-step` to continue on the next term.
--   * Uses `ReductionFresh` where fresh seals are allocated as `length Σ`.
--   * Stops on values, blame, or when gas runs out.

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.List using ([])
open import Data.Product using (Σ; Σ-syntax; _,_)

open import Types
open import Store
open import Terms
open import ReductionFresh
open import ProgressFresh
open import PreservationFresh

------------------------------------------------------------------------
-- Fuel-bounded evaluation
------------------------------------------------------------------------

postulate
  storeWf-step :
    ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{Γ : Ctx}{M M′ : Term}{A : Ty} →
    (wfΣ : StoreWf Δ Ψ Σ) →
    (M⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A) →
    (M→M′ : Σ ∣ M —→ Σ′ ∣ M′) →
    (eqΨ : StepCtxExact (step-ctx-shape M→M′) Ψ Ψ′) →
    (M′⊢ : Δ ∣ Ψ′ ∣ Σ′ ∣ Γ ⊢ M′ ⦂ A) →
    StoreWf Δ Ψ′ Σ′

eval :
  ∀ {Ψ}{Σ₀ : Store}{M : Term}{A : Ty} →
  (wfΣ₀ : StoreWf 0 Ψ Σ₀) →
  (gas : ℕ) →
  (M⊢ : 0 ∣ Ψ ∣ Σ₀ ∣ [] ⊢ M ⦂ A) →
  Σ[ Ψ′ ∈ SealCtx ]
  Σ[ Σ′ ∈ Store ]
  Σ[ N ∈ Term ]
  Σ[ A′ ∈ Ty ]
  Σ[ N⊢ ∈ (0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ N ⦂ A′) ]
    (Σ₀ ∣ M —↠ Σ′ ∣ N)
eval {Ψ} {Σ₀} {M} {A} wfΣ₀ zero M⊢ =
  Ψ , Σ₀ , M , A , M⊢ , (M ∎)
eval {Ψ} {Σ₀} {M} {A} wfΣ₀ (suc gas) M⊢ with progress M⊢
... | done v = Ψ , Σ₀ , M , A , M⊢ , (M ∎)
... | crash b = Ψ , Σ₀ , M , A , M⊢ , (M ∎)
... | step {N = N} M→N with preservation-step wfΣ₀ M⊢ M→N
...   | Ψ₁ , eqΨ₁ , N⊢ with eval (storeWf-step wfΣ₀ M⊢ M→N eqΨ₁ N⊢) gas N⊢
...     | Ψ₂ , Σ₂ , K , C , K⊢ , N—↠K =
          Ψ₂ , Σ₂ , K , C , K⊢ , (M —→⟨ M→N ⟩ N—↠K)
