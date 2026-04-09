module Eval where

-- File Charter:
--   * Fuel-bounded evaluator for closed extrinsic PolyUpDown terms.
--   * Produces an explicit store-threaded reduction sequence by iterating
--   * `progress` and using `preservation-step` to continue on the next term.
--   * Stops on values, blame, or when gas runs out.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([])
open import Data.Product using (Σ; Σ-syntax; _,_)

open import Types
open import Store
open import Terms
open import Reduction
open import Progress
open import Preservation

------------------------------------------------------------------------
-- Fuel-bounded evaluation
------------------------------------------------------------------------

eval :
  ∀ {Ψ}{Σ₀ : Store}{M : Term}{A : Ty} →
  (uΣ₀ : Uniqueˢ Σ₀) →
  (gas : ℕ) →
  (M⊢ : 0 ∣ Ψ ∣ Σ₀ ∣ [] ⊢ M ⦂ A) →
  Σ[ Ψ′ ∈ SealCtx ]
  Σ[ Σ′ ∈ Store ]
  Σ[ N ∈ Term ]
  Σ[ A′ ∈ Ty ]
  Σ[ N⊢ ∈ (0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ N ⦂ A′) ]
    (Σ₀ ∣ M —↠ Σ′ ∣ N)
eval {Ψ} {Σ₀} {M} {A} uΣ₀ zero M⊢ =
  Ψ , Σ₀ , M , A , M⊢ , (M ∎)
eval {Ψ} {Σ₀} {M} {A} uΣ₀ (suc gas) M⊢ with progress M⊢
... | done v = Ψ , Σ₀ , M , A , M⊢ , (M ∎)
... | crash b = Ψ , Σ₀ , M , A , M⊢ , (M ∎)
... | step {N = N} M→N with preservation-step uΣ₀ M⊢ M→N
...   | Ψ₁ , hρ , N⊢ with eval (unique-store-step uΣ₀ M→N) gas N⊢
...     | Ψ₂ , Σ₂ , K , C , K⊢ , N—↠K =
          Ψ₂ , Σ₂ , K , C , K⊢ , (M —→⟨ M→N ⟩ N—↠K)
