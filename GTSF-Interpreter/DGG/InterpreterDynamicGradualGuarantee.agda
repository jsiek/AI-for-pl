module DGG.InterpreterDynamicGradualGuarantee where

-- File Charter:
--   * States the four interpreter DGG obligations as separate propositions.
--   * Uses positive fuel-indexed divergence and excludes the error alternative
--     from every allowed observable behavior.
--   * Leaves semantic value precision as the explicit logical-relation
--     boundary for closures, proxies, tags, seals, and allocation worlds.

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
open import Core.InterpreterObservations
open import NuTerms using (Term)
open import Types

compiled-leftᴵ :
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Term
compiled-leftᴵ M⊑M′ =
  proj₁
    (compileᵀ ctxWf-[]
      (gradual-term-imprecision-source-typing M⊑M′))

compiled-rightᴵ :
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Term
compiled-rightᴵ M⊑M′ =
  proj₁
    (compileᵀ ctxWf-[]
      (gradual-term-imprecision-target-typing M⊑M′))

SemanticValuePrecision : Set₁
SemanticValuePrecision =
  World → Value → World → Value → Set

------------------------------------------------------------------------
-- 1. Left value implies a related right value
------------------------------------------------------------------------

ForwardValueDGG : SemanticValuePrecision → Set₁
ForwardValueDGG value⊑ =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  ∀ {W V} →
  compiled-leftᴵ M⊑M′ ⇓ᴵ[ W ] V →
  ∃[ W′ ] (∃[ V′ ]
    ((compiled-rightᴵ M⊑M′ ⇓ᴵ[ W′ ] V′) ×
     value⊑ W V W′ V′))

------------------------------------------------------------------------
-- 2. Left divergence implies right divergence
------------------------------------------------------------------------

ForwardDivergenceDGG : Set₁
ForwardDivergenceDGG =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  Divergesᴵ (compiled-leftᴵ M⊑M′) →
  Divergesᴵ (compiled-rightᴵ M⊑M′)

------------------------------------------------------------------------
-- 3. Right value implies a related left value or left blame
------------------------------------------------------------------------

BackwardValueDGG : SemanticValuePrecision → Set₁
BackwardValueDGG value⊑ =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  ∀ {W′ V′} →
  compiled-rightᴵ M⊑M′ ⇓ᴵ[ W′ ] V′ →
    (∃[ W ] (∃[ V ]
      ((compiled-leftᴵ M⊑M′ ⇓ᴵ[ W ] V) ×
       value⊑ W V W′ V′)))
    ⊎ Blamesᴵ (compiled-leftᴵ M⊑M′)

------------------------------------------------------------------------
-- 4. Right divergence implies left divergence or left blame
------------------------------------------------------------------------

BackwardDivergenceDGG : Set₁
BackwardDivergenceDGG =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  Divergesᴵ (compiled-rightᴵ M⊑M′) →
  Divergesᴵ (compiled-leftᴵ M⊑M′)
    ⊎ Blamesᴵ (compiled-leftᴵ M⊑M′)
