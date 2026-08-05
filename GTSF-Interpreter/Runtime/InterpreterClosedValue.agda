module Runtime.InterpreterClosedValue where

-- File Charter:
--   * Gives a proof-relevant graph for `closeValue`.
--   * Records exact fresh abstract names below nested `Λ`.
--   * Supports semantic typing and name substitution without adding runtime
--     constructors to the official value grammar.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.Maybe using (just)

open import Coercions using (Coercion)
import Coercions
open import Interpreter
import NuTerms as N
open import Types using (Ground; Ty; TyVar)

data ClosedValue
    (γ : Environment) (θ : TypeEnvironment) :
    ∀ {V} → N.Value V → Value → Set where
  closed-closure :
    ∀ {N} →
    ClosedValue γ θ (N.ƛ N)
      (closure N γ θ)

  closed-type-abstraction :
    ∀ {V U X}
      {vV : N.Value V} →
    abstract-name X ∉ θ →
    ClosedValue γ (abstract-name X ∷ θ) vV U →
    ClosedValue γ θ (N.Λ vV)
      (type-abstraction X U)

  closed-constant :
    ∀ κ →
    ClosedValue γ θ (N.$ κ)
      (constant κ)

  closed-tagged :
    ∀ {V U G}
      {vV : N.Value V}
      {gG : Ground G} →
    ClosedValue γ θ vV U →
    ClosedValue γ θ (vV N.⟨ Coercions._! G ⟩)
      (tagged gG θ U)

  closed-sealed :
    ∀ {V U A X α}
      {vV : N.Value V} →
    lookup θ X ≡ just (seal-name α) →
    ClosedValue γ θ vV U →
    ClosedValue γ θ (vV N.⟨ Coercions.seal A X ⟩)
      (sealed α U)

  closed-function-proxy :
    ∀ {V U p q}
      {vV : N.Value V} →
    ClosedValue γ θ vV U →
    ClosedValue γ θ (vV N.⟨ p Coercions.↦ q ⟩)
      (function-proxy p q θ U)

  closed-forall-proxy :
    ∀ {V U c}
      {vV : N.Value V} →
    ClosedValue γ θ vV U →
    ClosedValue γ θ (vV N.⟨ Coercions.`∀ c ⟩)
      (forall-proxy c θ U)

  closed-generalized :
    ∀ {V U A c}
      {vV : N.Value V} →
    ClosedValue γ θ vV U →
    ClosedValue γ θ (vV N.⟨ Coercions.gen A c ⟩)
      (generalized A c θ U)
