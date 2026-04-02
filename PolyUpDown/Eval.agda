module Eval where

-- File Charter:
--   * Fuel-bounded evaluator for closed PolyUpDown terms.
--   * Produces an explicit reduction sequence by iterating `progress`.
--   * Stops on values, blame, or when gas runs out.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([])
open import Data.Product using (Σ; Σ-syntax; _,_)

open import Types
open import Store
open import Terms
open import Reduction
open import Progress

------------------------------------------------------------------------
-- Fuel-bounded evaluation
------------------------------------------------------------------------

eval :
  ∀ {Ψ}{Σ₀ : Store 0 Ψ}{A : Ty 0 Ψ} →
  (uΣ₀ : Uniqueˢ Σ₀) →
  (gas : ℕ) →
  (M : 0 ∣ Ψ ∣ Σ₀ ∣ [] ⊢ A) →
  Σ[ Ψ′ ∈ SealCtx ]
  Σ[ Σ′ ∈ Store 0 Ψ′ ]
  Σ[ A′ ∈ Ty 0 Ψ′ ]
  Σ[ N ∈ (0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ A′) ]
    (M —↠ N)
eval {Ψ} {Σ₀} {A} uΣ₀ zero M = Ψ , Σ₀ , A , M , (M ∎)
eval {Ψ} {Σ₀} {A} uΣ₀ (suc gas) M with progress uΣ₀ M
... | done v = Ψ , Σ₀ , A , M , (M ∎)
... | crash b = Ψ , Σ₀ , A , M , (M ∎)
... | step {N = N} M→N with eval (unique-store-step uΣ₀ M→N) gas N
...   | (Ψ″ , Σ″ , C , K , N—↠K) = Ψ″ , Σ″ , C , K , (M —→⟨ M→N ⟩ N—↠K)
