module Eval where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import PolyBlame
import Progress as Prog
open import Preservation using
  ( StoreUnique
  ; WfStore
  ; preservation
  )

------------------------------------------------------------------------
-- PLFA-style fuel and evaluation result
------------------------------------------------------------------------

data Gas : Set where
  gas : ℕ → Gas

data Finished (Σ : Store) (M : Term) : Set where
  done       : Value M → Finished Σ M
  crashed    : M ≡ blame → Finished Σ M
  out-of-gas : Finished Σ M

data Steps (Σ : Store) (M : Term) : Set where
  steps :
    {Π : Store} {N : Term} →
    (Σ ⊲ M) —↠ (Π ⊲ N) →
    Finished Π N →
    Steps Σ M

------------------------------------------------------------------------
-- Evaluator (parameterized by progress)
------------------------------------------------------------------------

eval-ℕ :
  (prog : ∀ {Σ M A} → 0 ∣ Σ ⊢ [] ⊢ M ⦂ A → Prog.Progress Σ M) →
  ∀ {Σ M A} →
  ℕ →
  StoreUnique Σ →
  WfStore Σ →
  0 ∣ Σ ⊢ [] ⊢ M ⦂ A →
  Steps Σ M
eval-ℕ prog zero hΣ hWF hM =
  steps (_ ∎) out-of-gas
eval-ℕ prog (suc n) hΣ hWF hM with prog hM
... | Prog.done vM =
  steps (_ ∎) (done vM)
... | Prog.crash m≡blame =
  steps (_ ∎) (crashed m≡blame)
... | Prog.step {Σ' = Π} {N = N} M↦N with preservation hM hΣ hWF M↦N
...   | (hN , hExt , hΠ , hWFΠ) with eval-ℕ prog n hΠ hWFΠ hN
...     | steps M'↠N fin =
  steps (_ —→⟨ M↦N ⟩ M'↠N) fin

eval :
  (prog : ∀ {Σ M A} → 0 ∣ Σ ⊢ [] ⊢ M ⦂ A → Prog.Progress Σ M) →
  ∀ {Σ M A} →
  Gas →
  StoreUnique Σ →
  WfStore Σ →
  0 ∣ Σ ⊢ [] ⊢ M ⦂ A →
  Steps Σ M
eval prog (gas n) hΣ hWF hM = eval-ℕ prog n hΣ hWF hM

run :
  (prog : ∀ {Σ M A} → 0 ∣ Σ ⊢ [] ⊢ M ⦂ A → Prog.Progress Σ M) →
  ∀ {M A} →
  Gas →
  0 ∣ [] ⊢ [] ⊢ M ⦂ A →
  Steps [] M
run prog g hM = eval prog g tt (λ ()) hM
