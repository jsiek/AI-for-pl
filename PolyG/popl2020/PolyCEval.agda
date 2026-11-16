module PolyCEval where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₂)

open import PolyC
import PolyCProgress as Prog
open import PolyCPreservation using (_∣_⊢_⊢_⦂ʳ_; preservation; embed)

------------------------------------------------------------------------
-- Reflexive-transitive closure of small-step reduction
------------------------------------------------------------------------

infixr 2 _↦⟨_⟩_
infix 2 _⊢_↦*_⊢_

data _⊢_↦*_⊢_ : Store → Term → Store → Term → Set where
  refl↦* :
    {Σ : Store} {M : Term} →
    Σ ⊢ M ↦* Σ ⊢ M

  _↦⟨_⟩_ :
    (Σ : Store) {M : Term} {Σ' Σ'' : Store} {M' M'' : Term} →
    Σ ⊢ M ↦ Σ' ⊢ M' →
    Σ' ⊢ M' ↦* Σ'' ⊢ M'' →
    Σ ⊢ M ↦* Σ'' ⊢ M''

------------------------------------------------------------------------
-- PLFA-style fuel and evaluation result
------------------------------------------------------------------------

data Gas : Set where
  gas : ℕ → Gas

data Finished (Σ : Store) (M : Term) : Set where
  done       : Value M → Finished Σ M
  crashed    : M ≡ err → Finished Σ M
  out-of-gas : Finished Σ M

data Steps (Σ : Store) (M : Term) : Set where
  steps :
    {Σ' : Store} {N : Term} →
    Σ ⊢ M ↦* Σ' ⊢ N →
    Finished Σ' N →
    Steps Σ M

------------------------------------------------------------------------
-- Evaluator (parameterized by runtime progress)
------------------------------------------------------------------------

evalʳ-ℕ :
  (progʳ : ∀ {Δ Σ M A} → Δ ∣ Σ ⊢ [] ⊢ M ⦂ʳ A → Prog.Progress Σ M) →
  ∀ {Δ Σ M A} →
  ℕ →
  Δ ∣ Σ ⊢ [] ⊢ M ⦂ʳ A →
  Steps Σ M
evalʳ-ℕ progʳ zero hM =
  steps refl↦* out-of-gas
evalʳ-ℕ progʳ (suc n) hM with progʳ hM
... | Prog.done vM =
  steps refl↦* (done vM)
... | Prog.crash m≡err =
  steps refl↦* (crashed m≡err)
... | Prog.step {Σ' = Σ'} {N = N} M↦N with preservation hM M↦N
...   | ext×hN with evalʳ-ℕ progʳ n (proj₂ ext×hN)
...     | steps M'↦*N fin =
  steps (_ ↦⟨ M↦N ⟩ M'↦*N) fin

evalʳ :
  (progʳ : ∀ {Δ Σ M A} → Δ ∣ Σ ⊢ [] ⊢ M ⦂ʳ A → Prog.Progress Σ M) →
  ∀ {Δ Σ M A} →
  Gas →
  Δ ∣ Σ ⊢ [] ⊢ M ⦂ʳ A →
  Steps Σ M
evalʳ progʳ (gas n) hM = evalʳ-ℕ progʳ n hM

-- Convenient front-end for source-typed closed programs.
eval :
  (progʳ : ∀ {Δ Σ M A} → Δ ∣ Σ ⊢ [] ⊢ M ⦂ʳ A → Prog.Progress Σ M) →
  ∀ {Δ Σ M A} →
  Gas →
  Δ ⊢ [] ⊢ M ⦂ A →
  Steps Σ M
eval progʳ g hM = evalʳ progʳ g (embed hM)

run :
  (progʳ : ∀ {Δ Σ M A} → Δ ∣ Σ ⊢ [] ⊢ M ⦂ʳ A → Prog.Progress Σ M) →
  ∀ {Δ M A} →
  Gas →
  Δ ⊢ [] ⊢ M ⦂ A →
  Steps [] M
run progʳ g hM = eval progʳ g hM
