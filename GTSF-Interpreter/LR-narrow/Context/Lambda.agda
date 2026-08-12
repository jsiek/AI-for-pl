module LR-narrow.Context.Lambda where

-- File Charter:
--   * Proves the semantic context lemma for ordinary term abstraction.
--   * Reduces closure application to the body context lemma at one less fuel.
--   * Keeps the unary closure certificate explicit and uses no provisional
--     dynamic or precise-right universal LR clause.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Unit.Polymorphic.Base using (tt)

open import ImprecisionWf using (_↦_; _∣_⊢_⊑_⊣_)
open import Interpreter using
  ( Environment
  ; Value
  ; blamed
  ; closure
  ; interpret
  ; returned
  )
  renaming (World to RuntimeWorld)
open import LR-narrow.Context.ClosureApplication
open import LR-narrow.Context.KripkeRefl
open import LR-narrow.Context.TermRelation
open import LR-narrow.Context.ValueDownward
open import LR-narrow.LogicalRelation
open import LR-narrow.World
open import NuTerms using (Term; ƛ_)
open import Types using (Ty; TyCtx)

lambda-context : ∀
    {Φ} {Δᴸ Δᴿ : TyCtx}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {w : World} {I : Interpretation {Φ} {Δᴸ} {Δᴿ} w}
    {k : ℕ} {γ γ′ : Environment} {N N′ : Term}
  → TypedClosedEndpoints (pA ↦ pB) I
      (closure N γ (left-types I))
      (closure N′ γ′ (right-types I))
  → (∀ {future}
      (J : Interpretation {Φ} {Δᴸ} {Δᴿ} future)
      → J ⊒ⁱ I
      → (j : ℕ)
      → ∀ {U U′}
      → ValueNarrowing pA J j U U′
      → TermRelation pB J j (U ∷ γ) (U′ ∷ γ′) N N′)
  → TermRelation (pA ↦ pB) I k γ γ′ (ƛ N) (ƛ N′)
lambda-context {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {pA = pA} {pB = pB} {w = w} {I = I} {k = k}
    {γ = γ} {γ′ = γ′} {N = N} {N′ = N′} endpoints body = record
  { forward-return = lambda-forward
  ; backward-return = lambda-backward
  ; forward-blame = lambda-forward-blame
  }
  where
  closure-functions : (j : ℕ)
    → FunctionsRelated pA pB I j
        (closure N γ (left-types I))
        (closure N′ γ′ (right-types I))
  closure-functions zero = tt
  closure-functions (suc j) = closure-head , closure-functions j
    where
    closure-head : ∀ {future}
      (J : Interpretation {Φ} {Δᴸ} {Δᴿ} future)
      → ∀ {U U′}
      → J ⊒ⁱ I
      → ValueNarrowing pA J (suc j) U U′
      → ComputationsRelated (ValueNarrowing pB) J (suc j)
          (λ n → Interpreter.applyValue (left-world future)
            (closure N γ (left-types I)) U n)
          (λ n → Interpreter.applyValue (right-world future)
            (closure N′ γ′ (right-types I)) U′ n)
    closure-head J {U} {U′}
        growth@(future-interpretation future-growth refl refl atoms-eq)
        argument =
      closure-applications-related
        (body J growth j (value-narrowing-downward argument))

  closures-related : (j : ℕ)
    → ValueNarrowing (pA ↦ pB) I j
        (closure N γ (left-types I))
        (closure N′ γ′ (right-types I))
  closures-related zero = endpoints
  closures-related (suc j) = endpoints , closure-functions j

  lambda-forward : ∀ {n W V}
    → n ≤ k
    → interpret (left-world w) γ (left-types I) (ƛ N) n
        ≡ returned W V
    →
      (Σ[ m ∈ ℕ ]
       Σ[ W′ ∈ RuntimeWorld ]
       Σ[ V′ ∈ Value ]
       Σ[ future ∈ World ]
       Σ[ futureᵢ ∈ Interpretation future ]
         (futureᵢ ⊒ⁱ I) ×
         (left-world future ≡ W) ×
         (right-world future ≡ W′) ×
         (interpret (right-world w) γ′ (right-types I) (ƛ N′) m
           ≡ returned W′ V′) ×
         ValueNarrowing (pA ↦ pB) futureᵢ (k ∸ n) V V′)
      ⊎
      (Σ[ m ∈ ℕ ]
       Σ[ W′ ∈ RuntimeWorld ]
       Σ[ future ∈ World ]
       Σ[ futureᵢ ∈ Interpretation future ]
         (futureᵢ ⊒ⁱ I) ×
         (left-world future ≡ W) ×
         (right-world future ≡ W′) ×
         (interpret (right-world w) γ′ (right-types I) (ƛ N′) m
           ≡ blamed W′))
  lambda-forward {n = zero} n≤k ()
  lambda-forward {n = suc n} n≤k refl =
    inj₁
      (suc n , right-world w , closure N′ γ′ (right-types I) ,
       w , I , interpretation-⊒ⁱ-refl I , refl , refl , refl ,
       closures-related (k ∸ suc n))

  lambda-backward : ∀ {n W′ V′}
    → n ≤ k
    → interpret (right-world w) γ′ (right-types I) (ƛ N′) n
        ≡ returned W′ V′
    → Σ[ m ∈ ℕ ]
      Σ[ W ∈ RuntimeWorld ]
      Σ[ V ∈ Value ]
      Σ[ future ∈ World ]
      Σ[ futureᵢ ∈ Interpretation future ]
        (futureᵢ ⊒ⁱ I) ×
        (left-world future ≡ W) ×
        (right-world future ≡ W′) ×
        (interpret (left-world w) γ (left-types I) (ƛ N) m
          ≡ returned W V) ×
        ValueNarrowing (pA ↦ pB) futureᵢ (k ∸ n) V V′
  lambda-backward {n = zero} n≤k ()
  lambda-backward {n = suc n} n≤k refl =
    suc n , left-world w , closure N γ (left-types I) ,
    w , I , interpretation-⊒ⁱ-refl I , refl , refl , refl ,
    closures-related (k ∸ suc n)

  lambda-forward-blame : ∀ {n W}
    → n ≤ k
    → interpret (left-world w) γ (left-types I) (ƛ N) n
        ≡ blamed W
    → Σ[ m ∈ ℕ ]
      Σ[ W′ ∈ RuntimeWorld ]
      Σ[ future ∈ World ]
      Σ[ futureᵢ ∈ Interpretation future ]
        (futureᵢ ⊒ⁱ I) ×
        (left-world future ≡ W) ×
        (right-world future ≡ W′) ×
        (interpret (right-world w) γ′ (right-types I) (ƛ N′) m
          ≡ blamed W′)
  lambda-forward-blame {n = zero} n≤k ()
  lambda-forward-blame {n = suc n} n≤k ()
