module TypeSafety where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import PolyBlame
open import Progress
open import Preservation

------------------------------------------------------------------------
-- Type safety as progress + preservation
------------------------------------------------------------------------

type-safety :
  ∀ {Σ Π M N A} →
  0 ∣ Σ ⊢ [] ⊢ M ⦂ A →
  StoreUnique Σ →
  WfStore Σ →
  (Σ ⊲ M) —↠ (Π ⊲ N) →
  Progress Π N
type-safety hM hΣ hWF ms with multi-preservation hM hΣ hWF ms
... | (hN , hExt , hΠ , hWFΠ) = progress hN

------------------------------------------------------------------------
-- PLFA-style evaluator with gas
------------------------------------------------------------------------

data Finished : Config → Set where
  done      : ∀ {Σ M} → Value M → Finished (Σ ⊲ M)
  crashed   : ∀ {Σ M} → M ≡ blame → Finished (Σ ⊲ M)
  out-of-gas : ∀ {Σ M} → Finished (Σ ⊲ M)

data Steps (c : Config) : Set where
  steps : ∀ {c'} → c —↠ c' → Finished c' → Steps c

eval :
  (fuel : ℕ) →
  ∀ {Σ M A} →
  StoreUnique Σ →
  WfStore Σ →
  0 ∣ Σ ⊢ [] ⊢ M ⦂ A →
  Steps (Σ ⊲ M)
eval zero hΣ hWF hM = steps (_ ∎) out-of-gas
eval (suc fuel) hΣ hWF hM with progress hM
... | done v = steps (_ ∎) (done v)
... | crash eq = steps (_ ∎) (crashed eq)
... | step {Σ' = Π} {N = N} s with preservation hM hΣ hWF s
...   | (hN , hExt , hΠ , hWFΠ) with eval fuel hΠ hWFΠ hN
...   | steps ms fin = steps (_ —→⟨ s ⟩ ms) fin

run :
  (fuel : ℕ) →
  ∀ {M A} →
  0 ∣ [] ⊢ [] ⊢ M ⦂ A →
  Steps ([] ⊲ M)
run fuel hM = eval fuel tt (λ ()) hM
