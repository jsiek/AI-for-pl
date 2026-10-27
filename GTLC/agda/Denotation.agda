module Denotation where

-- File Charter:
--   * The denotational semantics of the cast calculus in the graph model with
--     errors (GraphModel): coercions denote functions on value sets, terms
--     denote sets under an environment of value sets.
--   * A term that blames denotes a set that holds ω; one that diverges, the
--     empty set.  Evaluation order is that of the reduction relation: the
--     nesting of the binds.

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import Contexts using (Var)
open import Coercions
open import CastCalculus
open import GraphModel
open import DynamicGradualGuaranteeDefinitions using (Observation; nat-obs; fun-obs)

------------------------------------------------------------------------
-- Coercions
------------------------------------------------------------------------

-- the injection of the values of X at type A into ★
inj : Ty → 𝒫 → 𝒫
inj A X (tag t v) = tagTy t ≡ A × v ∈ X
inj A X (nat n) = ⊥
inj A X (V ⟼ w) = ⊥
inj A X ν = ⊥
inj A X ω = ⊥

-- the projection from ★ to A: the payloads tagged A, and ω for any other tag
proj : Ty → 𝒫 → 𝒫
proj A X w =
  (Σ[ t ∈ Tag ] (tagTy t ≡ A × tag t w ∈ X))
  ⊎ (w ≡ ω × Σ[ t ∈ Tag ] Σ[ v ∈ Val ] (tag t v ∈ X × tagTy t ≢ A))

⟦_⟧ᶜ : Coercion → 𝒫 → 𝒫
⟦ idᶜ A ⟧ᶜ X = X
⟦ A ! ⟧ᶜ X = inj A X
⟦ A `? ⟧ᶜ X = proj A X
⟦ c ↦ d ⟧ᶜ X =
  guard X (Λ (λ Y → ⟦ c ⟧ᶜ Y ≫= λ Y₁ → (X ● Y₁) ≫= ⟦ d ⟧ᶜ))
⟦ c ⨟ d ⟧ᶜ X = ⟦ c ⟧ᶜ X ≫= ⟦ d ⟧ᶜ
⟦ ⊥ᶜ A ⇨ B at ℓ ⟧ᶜ X = guard X ⌈ ω ⌉

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

Env : Set₁
Env = Var → 𝒫

infixr 5 _•_

_•_ : 𝒫 → Env → Env
(D • ρ) zero = D
(D • ρ) (suc x) = ρ x

⟦_⟧ : Termᶜ → Env → 𝒫
⟦ ` x ⟧ ρ = ρ x
⟦ $ n ⟧ ρ = ⌈ nat n ⌉
⟦ ƛ A ⇒ N ⟧ ρ = Λ (λ Y → ⟦ N ⟧ (Y • ρ))
⟦ L · M ⟧ ρ = ⟦ L ⟧ ρ ≫= λ F → ⟦ M ⟧ ρ ≫= λ X → F ● X
⟦ cast M [ c ] ⟧ ρ = ⟦ M ⟧ ρ ≫= ⟦ c ⟧ᶜ
⟦ blame ⟧ ρ = ⌈ ω ⌉

-- the environment of a closed term
ρ₀ : Env
ρ₀ x d = ⊥

------------------------------------------------------------------------
-- Observations of denotational values
------------------------------------------------------------------------

obs : Val → Observation
obs (nat n) = nat-obs n
obs (V ⟼ w) = fun-obs
obs ν = fun-obs
obs ω = fun-obs
obs (tag t d) = obs d
