module LR.LogicalRelation where

-- File Charter:
--   * Defines the first step-indexed Kripke logical relation for direct
--     interpreter values and computations.
--   * Treats function and universal types structurally while leaving gradual
--     boundary cases as explicit atomic relations.
--   * Uses interpreter fuel only to observe computations; the logical step
--     index decreases at every recursive use of the value relation.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)

import Interpreter as I
open import Interpreter using
  ( Outcome
  ; SealName
  ; Value
  ; applyValue
  ; blamed
  ; constant
  ; instantiateValue
  ; returned
  )
  renaming (World to RuntimeWorld)
open import LR.Atoms
open import LR.World
open import Primitives using (κℕ)
open import Typing.InterpreterSemanticTypingCore using
  ( SemanticType
  ; ValueTyping
  ; base-type
  ; bound-type
  ; liftSemantic
  ; nominal-type
  ; polymorphic-type
  ; _⇒ᵛ_
  ; unbound-type
  )
open import Types using (Base; `ℕ)

------------------------------------------------------------------------
-- Relational type codes and their two semantic endpoints
------------------------------------------------------------------------

AtomEnvironment : Set₁
AtomEnvironment = List Atom

data RelationalType : Set₁ where
  variable-relation : ℕ → RelationalType

  base-relation : Base → RelationalType

  nominal-relation : SealName → SealName → RelationalType

  boundary-relation : Atom → RelationalType

  _⇒ʳ_ : RelationalType
    → RelationalType
    → RelationalType

  ∀ʳ_ : RelationalType → RelationalType

infixr 7 _⇒ʳ_
infix 6 ∀ʳ_

lookup-atom : AtomEnvironment → ℕ → Maybe Atom
lookup-atom [] X = nothing
lookup-atom (a ∷ ρ) zero = just a
lookup-atom (a ∷ ρ) (suc X) = lookup-atom ρ X

data EmptyRelation (n : ℕ) (V V′ : Value) : Set where

empty-relation : StepIndexedRelation
empty-relation = EmptyRelation

empty-relation-downward : DownwardClosed empty-relation
empty-relation-downward {n} {V} {V′} ()

binder-atom : Atom
binder-atom = record
  { left-type = bound-type zero
  ; right-type = bound-type zero
  ; relation = empty-relation
  ; relation-downward = empty-relation-downward
  }

lift-atom : Atom → Atom
lift-atom a =
  atom (liftSemantic (left-type a)) (liftSemantic (right-type a))
    (relation a) (relation-downward a)

left-type-of : AtomEnvironment → RelationalType → SemanticType
left-type-of ρ (variable-relation X) with lookup-atom ρ X
left-type-of ρ (variable-relation X) | nothing = unbound-type X
left-type-of ρ (variable-relation X) | just a = left-type a
left-type-of ρ (base-relation ι) = base-type ι
left-type-of ρ (nominal-relation α α′) = nominal-type (I.seal-name α)
left-type-of ρ (boundary-relation a) = left-type a
left-type-of ρ (A ⇒ʳ B) = left-type-of ρ A ⇒ᵛ left-type-of ρ B
left-type-of ρ (∀ʳ A) =
  polymorphic-type (left-type-of (binder-atom ∷ map lift-atom ρ) A)

right-type-of : AtomEnvironment → RelationalType → SemanticType
right-type-of ρ (variable-relation X) with lookup-atom ρ X
right-type-of ρ (variable-relation X) | nothing = unbound-type X
right-type-of ρ (variable-relation X) | just a = right-type a
right-type-of ρ (base-relation ι) = base-type ι
right-type-of ρ (nominal-relation α α′) = nominal-type (I.seal-name α′)
right-type-of ρ (boundary-relation a) = right-type a
right-type-of ρ (A ⇒ʳ B) = right-type-of ρ A ⇒ᵛ right-type-of ρ B
right-type-of ρ (∀ʳ A) =
  polymorphic-type (right-type-of (binder-atom ∷ map lift-atom ρ) A)

------------------------------------------------------------------------
-- Typed atoms and terminal observations of computations
------------------------------------------------------------------------

record ValueAtom
    (ρ : AtomEnvironment) (A : RelationalType)
    (w : World) (V V′ : Value) : Set₁ where
  constructor value-atom
  field
    left-typed : ValueTyping (left-world w) V (left-type-of ρ A)
    right-typed : ValueTyping (right-world w) V′ (right-type-of ρ A)

open ValueAtom public

Computation : Set
Computation = ℕ → Outcome

ValueRelation : Set₂
ValueRelation = ℕ → World → Value → Value → Set₁

record ComputationsRelated
    (R : ValueRelation) (k : ℕ) (w : World)
    (left right : Computation) : Set₁ where
  field
    forward-return : ∀ {n U V}
      → n ≤ k
      → left n ≡ returned U V
      → Σ[ m ∈ ℕ ]
        Σ[ U′ ∈ RuntimeWorld ]
        Σ[ V′ ∈ Value ]
        Σ[ future ∈ World ]
          (future ⊋ w) ×
          (left-world future ≡ U) ×
          (right-world future ≡ U′) ×
          (right m ≡ returned U′ V′) ×
          R (k ∸ n) future V V′

    backward-return : ∀ {n U′ V′}
      → n ≤ k
      → right n ≡ returned U′ V′
      →
        (Σ[ m ∈ ℕ ]
         Σ[ U ∈ RuntimeWorld ]
         Σ[ V ∈ Value ]
         Σ[ future ∈ World ]
           (future ⊋ w) ×
           (left-world future ≡ U) ×
           (right-world future ≡ U′) ×
           (left m ≡ returned U V) ×
           R (k ∸ n) future V V′)
        ⊎
        (Σ[ m ∈ ℕ ]
         Σ[ U ∈ RuntimeWorld ]
         Σ[ future ∈ World ]
           (future ⊋ w) ×
           (left-world future ≡ U) ×
           (right-world future ≡ U′) ×
           (left m ≡ blamed U))

open ComputationsRelated public

data SameBaseValue : Base → Value → Value → Set where
  same-natural : ∀ n
    → SameBaseValue `ℕ (constant (κℕ n)) (constant (κℕ n))

------------------------------------------------------------------------
-- Step-indexed, Kripke value relation
------------------------------------------------------------------------

mutual

  𝒱 : AtomEnvironment → RelationalType
    → ℕ → World → Value → Value → Set₁

  𝒱 ρ A zero w V V′ =
    ValueAtom ρ A w V V′

  𝒱 ρ (variable-relation X) (suc k) w V V′
      with lookup-atom ρ X
  𝒱 ρ (variable-relation X) (suc k) w V V′ | nothing =
    ValueAtom ρ (variable-relation X) w V V′ × ⊥
  𝒱 ρ (variable-relation X) (suc k) w V V′ | just a =
    ValueAtom ρ (variable-relation X) w V V′ × AtomHolds a k V V′

  𝒱 ρ (base-relation ι) (suc k) w V V′ =
    ValueAtom ρ (base-relation ι) w V V′ × SameBaseValue ι V V′

  𝒱 ρ (nominal-relation α α′) (suc k) w V V′ =
    ValueAtom ρ (nominal-relation α α′) w V V′ ×
    Σ[ a ∈ Atom ]
      (atoms w ∋ α ↔ α′ ∶ a) × AtomHolds a k V V′

  𝒱 ρ (boundary-relation a) (suc k) w V V′ =
    ValueAtom ρ (boundary-relation a) w V V′ × AtomHolds a k V V′

  𝒱 ρ (A ⇒ʳ B) (suc k) w V V′ =
    ValueAtom ρ (A ⇒ʳ B) w V V′ ×
    FunctionsRelated ρ A B k w V V′

  𝒱 ρ (∀ʳ A) (suc k) w V V′ =
    ValueAtom ρ (∀ʳ A) w V V′ ×
    UniversalsRelated ρ A k w V V′

  FunctionsRelated : AtomEnvironment → RelationalType → RelationalType
    → ℕ → World → Value → Value → Set₁

  FunctionsRelated ρ A B zero w V V′ =
    ∀ {future U U′}
    → future ⊋ w
    → 𝒱 ρ A zero future U U′
    → ComputationsRelated (𝒱 ρ B) zero future
        (λ n → applyValue (left-world future) V U n)
        (λ n → applyValue (right-world future) V′ U′ n)

  FunctionsRelated ρ A B (suc k) w V V′ =
    (∀ {future U U′}
      → future ⊋ w
      → 𝒱 ρ A (suc k) future U U′
      → ComputationsRelated (𝒱 ρ B) (suc k) future
          (λ n → applyValue (left-world future) V U n)
          (λ n → applyValue (right-world future) V′ U′ n))
    × FunctionsRelated ρ A B k w V V′

  UniversalsRelated : AtomEnvironment → RelationalType
    → ℕ → World → Value → Value → Set₁

  UniversalsRelated ρ A zero w V V′ =
    ∀ {future}
    → future ⊋ w
    → (e : SealAtom)
    → e ∈ atoms future
    → ComputationsRelated (𝒱 (semantic-atom e ∷ ρ) A) zero future
        (λ n → instantiateValue
          (left-world future) (left-name e) V n)
        (λ n → instantiateValue
          (right-world future) (right-name e) V′ n)

  UniversalsRelated ρ A (suc k) w V V′ =
    (∀ {future}
      → future ⊋ w
      → (e : SealAtom)
      → e ∈ atoms future
      → ComputationsRelated
          (𝒱 (semantic-atom e ∷ ρ) A) (suc k) future
          (λ n → instantiateValue
            (left-world future) (left-name e) V n)
          (λ n → instantiateValue
            (right-world future) (right-name e) V′ n))
    × UniversalsRelated ρ A k w V V′
