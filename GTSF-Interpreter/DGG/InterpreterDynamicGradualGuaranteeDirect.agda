module DGG.InterpreterDynamicGradualGuaranteeDirect where

-- File Charter:
--   * States interpreter DGG obligations directly with equations about `run`.
--   * Does not import `Core.InterpreterObservations` or introduce convergence,
--     blame, error, or divergence predicates.
--   * Separates same-index returned-value compatibility from the four full
--     DGG obligations, whose matching executions may require different fuel.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; proj₁; ∃-syntax)
open import Data.Sum using (_⊎_)

open import Compile using (compileᵀ)
open import Ctx using (ctxWf-[])
open import GradualTermImprecision using
  ( _∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_
  ; gradual-term-imprecision-source-typing
  ; gradual-term-imprecision-target-typing
  )
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import NuTerms using (Term)
open import Types

compiled-leftᴰ :
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Term
compiled-leftᴰ M⊑M′ =
  proj₁
    (compileᵀ ctxWf-[]
      (gradual-term-imprecision-source-typing M⊑M′))

compiled-rightᴰ :
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Term
compiled-rightᴰ M⊑M′ =
  proj₁
    (compileᵀ ctxWf-[]
      (gradual-term-imprecision-target-typing M⊑M′))

SemanticValuePrecisionᴰ : Set₁
SemanticValuePrecisionᴰ =
  World → Value → World → Value → Set

------------------------------------------------------------------------
-- Same-index compatibility is useful, but is not a complete DGG
------------------------------------------------------------------------

SameIndexReturnedCompatibility :
  SemanticValuePrecisionᴰ →
  Set₁
SameIndexReturnedCompatibility value⊑ =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  ∀ n W V W′ V′ →
  run (compiled-leftᴰ M⊑M′) n ≡ returned W V →
  run (compiled-rightᴰ M⊑M′) n ≡ returned W′ V′ →
  value⊑ W V W′ V′

------------------------------------------------------------------------
-- 1. A left return forces a related right return
------------------------------------------------------------------------

ForwardValueDGGDirect :
  SemanticValuePrecisionᴰ →
  Set₁
ForwardValueDGGDirect value⊑ =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  ∀ n W V →
  run (compiled-leftᴰ M⊑M′) n ≡ returned W V →
  ∃[ m ] (∃[ W′ ] (∃[ V′ ]
    ((run (compiled-rightᴰ M⊑M′) m ≡ returned W′ V′) ×
     value⊑ W V W′ V′)))

------------------------------------------------------------------------
-- 2. Timeout at every left index forces timeout at every right index
------------------------------------------------------------------------

ForwardDivergenceDGGDirect : Set₁
ForwardDivergenceDGGDirect =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  (∀ n → ∃[ W ] (run (compiled-leftᴰ M⊑M′) n ≡ timed W)) →
  ∀ n →
  ∃[ W′ ] (run (compiled-rightᴰ M⊑M′) n ≡ timed W′)

------------------------------------------------------------------------
-- 3. A right return forces a related left return or eventual left blame
------------------------------------------------------------------------

BackwardValueDGGDirect :
  SemanticValuePrecisionᴰ →
  Set₁
BackwardValueDGGDirect value⊑ =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  ∀ n W′ V′ →
  run (compiled-rightᴰ M⊑M′) n ≡ returned W′ V′ →
    (∃[ m ] (∃[ W ] (∃[ V ]
      ((run (compiled-leftᴰ M⊑M′) m ≡ returned W V) ×
       value⊑ W V W′ V′))))
    ⊎ (∃[ m ] (∃[ W ]
      (run (compiled-leftᴰ M⊑M′) m ≡ blamed W)))

------------------------------------------------------------------------
-- 4. Right timeout at every index forces left timeout or blame at each index
------------------------------------------------------------------------

BackwardDivergenceDGGDirect : Set₁
BackwardDivergenceDGGDirect =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  (∀ n →
    ∃[ W′ ] (run (compiled-rightᴰ M⊑M′) n ≡ timed W′)) →
  ∀ n →
    (∃[ W ] (run (compiled-leftᴰ M⊑M′) n ≡ timed W))
    ⊎ (∃[ W ] (run (compiled-leftᴰ M⊑M′) n ≡ blamed W))
