module alt.probes.SmartInjectionInertCounterexample where

-- File Charter:
--   * Retains the history of the all-inert smart-injection counterexample and
--     records the U46 stratified resolution.
--   * For dependent `∀ X. X ⇒ X`, the plan deliberately exposes an inst cast.
--     The resulting public injection is typed at ★ and immediately takes the
--     ordinary `β-inst` step instead of being misclassified as a value.
--
-- Before U46 this file proved that no all-Inert chain could remove the bound
-- occurrence.  The new design accepts that fact: dependent universals use a
-- transient inst-headed core, while binder-independent universals use ∀X.★.

open import Data.Fin using (zero)
open import Data.List using ([])
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Consistency
open import Primitives
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaPreservation using (⊢smart-inj★; preserve)

dependentType : Ty 0
dependentType = `∀ (＇ zero ⇒ ＇ zero)

dependent-to-function : _∼_ dependentType (★ ⇒ ★)
dependent-to-function =
  (inst_ ⦃ z∈A = ∈-fun-left var-∈ ⦄
    (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
      (id (＇ zero)) ⦃ nonstar-X ⦄ ↦
     _! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
      (id (＇ zero)) ⦃ nonstar-X ⦄))
    (λ ())

dependent-to-function-not-inert : ¬ Inert dependent-to-function
dependent-to-function-not-inert ()

emptyEnv : TyEnv zero zero Vec.[]
emptyEnv = ∅

polyId : Term zero zero
polyId = Λ (ƛ ＇ zero ˙ ` zero)

polyId-value : Value polyId
polyId-value = Λ (ƛ ＇ zero ˙ ` zero)

polyId-typed : emptyEnv ∣ [] ⊢ polyId ⦂ dependentType
polyId-typed = ⊢Λ (⊢ƛ (⊢` Z))

dependent-plan-shape :
  smart-inj★ polyId dependentType ≡
    (polyId ⟨ dependent-to-function ⟩)
      ⟨ _! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄
        (idᵍ ★⇒★) ⦃ nonstar-⇒ ⦄ ⟩
dependent-plan-shape = refl

dependent-smart-typed :
  emptyEnv ∣ [] ⊢ smart-inj★ polyId dependentType ⦂ ★
dependent-smart-typed = ⊢smart-inj★ polyId-typed

dependent-smart-steps :
  Σ[ M′ ∈ Term zero zero ]
    (emptyEnv ⊢ smart-inj★ polyId dependentType —→ M′)
dependent-smart-steps =
  _ , ξ-⟨⟩
    (β-inst ⦃ z∈A = ∈-fun-left var-∈ ⦄ polyId-value (λ ()))

dependent-smart-preserved :
  Σ[ M′ ∈ Term zero zero ]
    ((emptyEnv ⊢ smart-inj★ polyId dependentType —→ M′)
      × (emptyEnv ∣ [] ⊢ M′ ⦂ ★))
dependent-smart-preserved =
  _ , (ξ-⟨⟩
    (β-inst ⦃ z∈A = ∈-fun-left var-∈ ⦄ polyId-value (λ ()))) ,
    preserve dependent-smart-typed
      (ξ-⟨⟩
        (β-inst ⦃ z∈A = ∈-fun-left var-∈ ⦄ polyId-value (λ ())))

------------------------------------------------------------------------
-- Binder-independent ∀ keeps its ∀X.★ box and can be observed as ∀X.★
------------------------------------------------------------------------

constantType : Ty zero
constantType = `∀ (‵ `ℕ)

constantAllCast : _∼_ constantType (`∀ ★)
constantAllCast =
  ∀ᶜ (_! ⦃ Gᵍ = ‵ `ℕ ⦄
    (id {μ = extᵐ idᶜ} (‵ `ℕ)) ⦃ nonstar-ι ⦄)

polySeven : Term zero zero
polySeven = Λ ($ (κℕ 7))

polySeven-value : Value polySeven
polySeven-value = Λ ($ (κℕ 7))

polySeven-typed : emptyEnv ∣ [] ⊢ polySeven ⦂ constantType
polySeven-typed = ⊢Λ (⊢$ (κℕ 7))

constant-smart-typed :
  emptyEnv ∣ [] ⊢ smart-inj★ polySeven constantType ⦂ ★
constant-smart-typed = ⊢smart-inj★ polySeven-typed

constantObservation : Term zero zero
constantObservation =
  (smart-inj★ polySeven constantType
    ⟨ ？ (idᵍ {μ = idᶜ} ∀★) ⟩) ⦂∀ ★ [ ‵ `ℕ ]

constantAfterProjection : Term zero zero
constantAfterProjection =
  (polySeven ⟨ constantAllCast ⟩) ⦂∀ ★ [ ‵ `ℕ ]

constantAfterInstantiation : Term zero zero
constantAfterInstantiation =
  (polySeven ⦂∀ (‵ `ℕ) [ ‵ `ℕ ])
    ⟨ (_! ⦃ Gᵍ = ‵ `ℕ ⦄
      (id {μ = extᵐ idᶜ} (‵ `ℕ)) ⦃ nonstar-ι ⦄)
      [ ‵ `ℕ ]ᶜ ⟩

constant-project-step :
  emptyEnv ⊢ constantObservation —→ constantAfterProjection
constant-project-step = ξ-• (tag-untag (polySeven-value 《 all 》))

constant-instantiate-step :
  emptyEnv ⊢ constantAfterProjection —→ constantAfterInstantiation
constant-instantiate-step = β-∀ polySeven-value refl

forall-box-survives-star :
  (emptyEnv ⊢ constantObservation —→ constantAfterProjection)
  × (emptyEnv ⊢ constantAfterProjection —→ constantAfterInstantiation)
forall-box-survives-star = constant-project-step , constant-instantiate-step

------------------------------------------------------------------------
-- Checked limit of the approved dependent-∀ formulation
------------------------------------------------------------------------

variableOnlyType : Ty zero
variableOnlyType = `∀ (＇ zero)

variableBody-not-nonvar : ¬ NonVar {Δ = suc zero} (＇ zero)
variableBody-not-nonvar ()

variableOnly-plan-shape : ∀ {Θ} (V : Term Θ zero)
  → smart-inj★ V variableOnlyType ≡
      (V ⟨ bot-elim ⟩)
        ⟨ _! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄
          (idᵍ ∀★) ⦃ nonstar-∀ ⦄ ⟩
variableOnly-plan-shape V = refl
