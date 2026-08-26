module LR-narrow.Context.ClosureApplication where

-- File Charter:
--   * Lifts related closure-body computations through one `applyValue` call.
--   * Accounts exactly for the one fuel unit consumed by closure application.
--   * Contains the reusable successor-index theorem.
--   * Performs no provisional LR case analysis.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter using
  ( Environment
  ; Value
  ; applyValue
  ; closure
  ; interpret
  )
  renaming (World to RuntimeWorld)
open import LR-narrow.LogicalRelation
open import LR-narrow.World
open import NuTerms using (Term)
open import Types using (Ty; TyCtx)

closure-applications-related : ∀
    {Φ} {Δᴸ Δᴿ : TyCtx} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {w : World} {I : Interpretation {Φ} {Δᴸ} {Δᴿ} w}
    {k : ℕ} {γ γ′ : Environment} {N N′ : Term}
    {U U′ : Value}
  → ComputationsRelated (ValueNarrowing p) I k
      (λ n → interpret (left-world w) (U ∷ γ) (left-types I) N n)
      (λ n → interpret (right-world w) (U′ ∷ γ′)
        (right-types I) N′ n)
  → ComputationsRelated (ValueNarrowing p) I (suc k)
      (λ n → applyValue (left-world w)
        (closure N γ (left-types I)) U n)
      (λ n → applyValue (right-world w)
        (closure N′ γ′ (right-types I)) U′ n)
closure-applications-related {p = p} {w = w} {I = I} {k = k}
    {γ = γ} {γ′ = γ′} {N = N} {N′ = N′}
    {U = U} {U′ = U′} body = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = forward-blameᶜ
  }
  where
  forward : ∀ {n W V}
    → n ≤ suc k
    → applyValue (left-world w)
        (closure N γ (left-types I)) U n ≡ Interpreter.returned W V
    →
      (Σ[ m ∈ ℕ ]
       Σ[ W′ ∈ RuntimeWorld ]
       Σ[ V′ ∈ Value ]
       Σ[ future ∈ World ]
       Σ[ futureᵢ ∈ Interpretation future ]
         (futureᵢ ⊒ⁱ I) ×
         (left-world future ≡ W) ×
         (right-world future ≡ W′) ×
         (applyValue (right-world w)
           (closure N′ γ′ (right-types I)) U′ m ≡
           Interpreter.returned W′ V′) ×
         ValueNarrowing p futureᵢ (suc k ∸ n) V V′)
      ⊎
      (Σ[ m ∈ ℕ ]
       Σ[ W′ ∈ RuntimeWorld ]
       Σ[ future ∈ World ]
       Σ[ futureᵢ ∈ Interpretation future ]
         (futureᵢ ⊒ⁱ I) ×
         (left-world future ≡ W) ×
         (right-world future ≡ W′) ×
         (applyValue (right-world w)
           (closure N′ γ′ (right-types I)) U′ m ≡
           Interpreter.blamed W′))
  forward {n = Data.Nat.zero} n≤k ()
  forward {n = suc n} (Data.Nat.s≤s n≤k) result
      with forward-return body n≤k result
  forward {n = suc n} (Data.Nat.s≤s n≤k) result
      | inj₁ (m , W′ , V′ , future , futureᵢ , growth ,
          left-eq , right-eq , right-result , related) =
    inj₁ (suc m , W′ , V′ , future , futureᵢ , growth ,
      left-eq , right-eq , right-result , related)
  forward {n = suc n} (Data.Nat.s≤s n≤k) result
      | inj₂ (m , W′ , future , futureᵢ , growth ,
          left-eq , right-eq , right-result) =
    inj₂ (suc m , W′ , future , futureᵢ , growth ,
      left-eq , right-eq , right-result)

  backward : ∀ {n W′ V′}
    → n ≤ suc k
    → applyValue (right-world w)
        (closure N′ γ′ (right-types I)) U′ n ≡
        Interpreter.returned W′ V′
    → Σ[ m ∈ ℕ ]
      Σ[ W ∈ RuntimeWorld ]
      Σ[ V ∈ Value ]
      Σ[ future ∈ World ]
      Σ[ futureᵢ ∈ Interpretation future ]
        (futureᵢ ⊒ⁱ I) ×
        (left-world future ≡ W) ×
        (right-world future ≡ W′) ×
        (applyValue (left-world w)
          (closure N γ (left-types I)) U m ≡
          Interpreter.returned W V) ×
        ValueNarrowing p futureᵢ (suc k ∸ n) V V′
  backward {n = Data.Nat.zero} n≤k ()
  backward {n = suc n} (Data.Nat.s≤s n≤k) result
      with backward-return body n≤k result
  backward {n = suc n} (Data.Nat.s≤s n≤k) result
      | m , W , V , future , futureᵢ , growth ,
        left-eq , right-eq , left-result , related =
    suc m , W , V , future , futureᵢ , growth ,
    left-eq , right-eq , left-result , related

  forward-blameᶜ : ∀ {n W}
    → n ≤ suc k
    → applyValue (left-world w)
        (closure N γ (left-types I)) U n ≡ Interpreter.blamed W
    → Σ[ m ∈ ℕ ]
      Σ[ W′ ∈ RuntimeWorld ]
      Σ[ future ∈ World ]
      Σ[ futureᵢ ∈ Interpretation future ]
        (futureᵢ ⊒ⁱ I) ×
        (left-world future ≡ W) ×
        (right-world future ≡ W′) ×
        (applyValue (right-world w)
          (closure N′ γ′ (right-types I)) U′ m ≡
          Interpreter.blamed W′)
  forward-blameᶜ {n = Data.Nat.zero} n≤k ()
  forward-blameᶜ {n = suc n} (Data.Nat.s≤s n≤k) result
      with forward-blame body n≤k result
  forward-blameᶜ {n = suc n} (Data.Nat.s≤s n≤k) result
      | m , W′ , future , futureᵢ , growth ,
        left-eq , right-eq , right-result =
    suc m , W′ , future , futureᵢ , growth ,
    left-eq , right-eq , right-result
