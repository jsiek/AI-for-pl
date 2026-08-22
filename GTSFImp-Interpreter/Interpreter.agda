module Interpreter where

-- File Charter:
--   * Presents GTSFImp's executable evaluator through the outcome-oriented
--     interface used by the direct interpreter development.
--   * Preserves the evaluator's proof-carrying return and blame traces.
--   * Supplies application, type-instantiation, cast, reveal, and conceal
--     entry points for the logical relation without duplicating reduction.

open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero)

open import Types
open import TyStore
open import CastTerms
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import Reduction using (StoreChanges; _—↠[_]_)
import Eval as E

StepIndex : Set
StepIndex = ℕ

data Outcome {Δ : TyCtx} (M : Term Δ) : Set where
  timed : Outcome M

  returned :
    E.EvalResult M →
    Outcome M

  blamed : ∀ {Δ′}
    → (changes : StoreChanges Δ Δ′)
    → M —↠[ changes ] blame
    → Outcome M

interpretFrom : ∀ {Δ}
  → TyStore Δ
  → StepIndex
  → (M : Term Δ)
  → Outcome M
interpretFrom Σ gas M with E.evalFrom Σ gas M
interpretFrom Σ gas M | nothing = timed
interpretFrom Σ gas M | just (E.returned result′) = returned result′
interpretFrom Σ gas M | just (E.blamed changes trace) =
  blamed changes trace

run : StepIndex → (M : Term zero) → Outcome M
run gas M = interpretFrom store-empty gas M

applyValueFrom : ∀ {Δ}
  → TyStore Δ
  → StepIndex
  → (V U : Term Δ)
  → Outcome (V · U)
applyValueFrom Σ gas V U = interpretFrom Σ gas (V · U)

instantiateValueFrom : ∀ {Δ}
  → TyStore Δ
  → StepIndex
  → (V : Term Δ)
  → (B : Ty (Data.Nat.suc Δ))
  → (A : Ty Δ)
  → Outcome (V ⦂∀ B [ A ])
instantiateValueFrom Σ gas V B A =
  interpretFrom Σ gas (V ⦂∀ B [ A ])

castValueFrom : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → TyStore Δ
  → StepIndex
  → (V : Term Δ)
  → (c : μ ⊢ A ∼ B)
  → Outcome (V ⟨ c ⟩)
castValueFrom Σ gas V c = interpretFrom Σ gas (V ⟨ c ⟩)

revealValueFrom : ∀ {Δ A B}
  → TyStore Δ
  → StepIndex
  → (V : Term Δ)
  → (c : Conv↑ Δ A B)
  → Outcome (V ↑ c)
revealValueFrom Σ gas V c = interpretFrom Σ gas (V ↑ c)

concealValueFrom : ∀ {Δ A B}
  → TyStore Δ
  → StepIndex
  → (V : Term Δ)
  → (c : Conv↓ Δ A B)
  → Outcome (V ↓ c)
concealValueFrom Σ gas V c = interpretFrom Σ gas (V ↓ c)

data Terminal {Δ : TyCtx} {M : Term Δ} : Outcome M → Set where
  terminal-returned : ∀ {result} → Terminal (returned result)

  terminal-blamed : ∀ {Δ′}
    {changes : StoreChanges Δ Δ′}
    {trace : M —↠[ changes ] blame} →
    Terminal (blamed changes trace)
