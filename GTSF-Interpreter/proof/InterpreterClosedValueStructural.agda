module proof.InterpreterClosedValueStructural where

-- File Charter:
--   * Derives scope and abstract-name freshness from `ClosedValue`.
--   * Relates the deterministic abstract-name supply to list freshness.
--   * Contains no typing, evaluation, or reduction argument.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_; _⊔_; zero; suc)
open import Data.Nat.Properties using (n≮n; ≤-trans)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≢_; cong)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary using (yes; no)

import Coercions
open import Interpreter
open import Runtime.InterpreterClosedValue
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
import NuTerms as N
open import proof.InterpreterClosedValueProof using
  ( abstract-index-bound
  ; closedValue-replace
  ; replaceName-head
  )

lookup-seal-allocated :
  ∀ {W θ X α} →
  TypeEnvironmentScoped W θ →
  lookup θ X ≡ just (seal-name α) →
  Allocated W α
lookup-seal-allocated []-scoped ()
lookup-seal-allocated
    {X = zero} (abstract-scoped ∷-scoped θ-ok) ()
lookup-seal-allocated
    {X = zero} (seal-scoped α-ok ∷-scoped θ-ok) refl =
  α-ok
lookup-seal-allocated
    {X = suc X} (name-ok ∷-scoped θ-ok) lookup-eq =
  lookup-seal-allocated θ-ok lookup-eq

mutual

  closed-value-scoped :
    ∀ {W γ θ V U}
      {vV : N.Value V} →
    EnvironmentScoped W γ →
    TypeEnvironmentScoped W θ →
    ClosedValue γ θ vV U →
    ValueScoped W U
  closed-value-scoped γ-ok θ-ok closed-closure =
    closure-scoped γ-ok θ-ok
  closed-value-scoped γ-ok θ-ok
      (closed-type-abstraction fresh body) =
    type-abstraction-scoped
      (closed-value-scoped γ-ok
        (abstract-scoped ∷-scoped θ-ok) body)
  closed-value-scoped γ-ok θ-ok (closed-constant κ) =
    constant-scoped
  closed-value-scoped γ-ok θ-ok (closed-tagged body) =
    tagged-scoped θ-ok (closed-value-scoped γ-ok θ-ok body)
  closed-value-scoped γ-ok θ-ok
      (closed-sealed lookup-eq body) =
    sealed-scoped
      (lookup-seal-allocated θ-ok lookup-eq)
      (closed-value-scoped γ-ok θ-ok body)
  closed-value-scoped γ-ok θ-ok
      (closed-function-proxy body) =
    function-proxy-scoped θ-ok
      (closed-value-scoped γ-ok θ-ok body)
  closed-value-scoped γ-ok θ-ok
      (closed-forall-proxy body) =
    forall-proxy-scoped θ-ok
      (closed-value-scoped γ-ok θ-ok body)
  closed-value-scoped γ-ok θ-ok
      (closed-generalized body) =
    generalized-scoped θ-ok
      (closed-value-scoped γ-ok θ-ok body)

abstract-name-injective :
  ∀ {X Y} →
  abstract-name X ≡ abstract-name Y →
  X ≡ Y
abstract-name-injective refl =
  refl

fresh-under-distinct-name :
  ∀ {X Y θ} →
  X ≢ Y →
  abstract-name X ∉ θ →
  abstract-name X ∉ abstract-name Y ∷ θ
fresh-under-distinct-name X≢Y X-fresh (here name-eq) =
  X≢Y (abstract-name-injective name-eq)
fresh-under-distinct-name X≢Y X-fresh (there X∈) =
  X-fresh X∈

closed-value-name-fresh :
  ∀ {γ θ V U X}
    {vV : N.Value V} →
  abstract-name X ∉ θ →
  ClosedValue γ θ vV U →
  NameFresh X U
closed-value-name-fresh X-fresh closed-closure =
  fresh-closure X-fresh
closed-value-name-fresh {X = X} X-fresh
    (closed-type-abstraction {X = Y} Y-fresh body)
    with X ≟Name Y
closed-value-name-fresh {X = X} X-fresh
    (closed-type-abstraction {X = .X} Y-fresh body)
    | yes refl =
  fresh-type-abstraction-bound
closed-value-name-fresh {X = X} X-fresh
    (closed-type-abstraction {X = Y} Y-fresh body)
    | no X≢Y =
  fresh-type-abstraction-free X≢Y
    (closed-value-name-fresh
      (fresh-under-distinct-name X≢Y X-fresh) body)
closed-value-name-fresh X-fresh (closed-constant κ) =
  fresh-constant
closed-value-name-fresh X-fresh (closed-tagged body) =
  fresh-tagged X-fresh (closed-value-name-fresh X-fresh body)
closed-value-name-fresh X-fresh
    (closed-sealed lookup-eq body) =
  fresh-sealed (closed-value-name-fresh X-fresh body)
closed-value-name-fresh X-fresh
    (closed-function-proxy body) =
  fresh-function-proxy X-fresh
    (closed-value-name-fresh X-fresh body)
closed-value-name-fresh X-fresh
    (closed-forall-proxy body) =
  fresh-forall-proxy X-fresh
    (closed-value-name-fresh X-fresh body)
closed-value-name-fresh X-fresh
    (closed-generalized body) =
  fresh-generalized X-fresh
    (closed-value-name-fresh X-fresh body)

suc-max-self :
  ∀ n →
  suc n ⊔ n ≡ suc n
suc-max-self zero =
  refl
suc-max-self (suc n) =
  cong suc (suc-max-self n)

next-generated-abstract-index :
  ∀ θ →
  nextAbstractIndex
    (abstract-name (nextAbstractName θ) ∷ θ) ≡
    suc (nextAbstractIndex θ)
next-generated-abstract-index θ =
  suc-max-self (nextAbstractIndex θ)

abstract-name-fresh-at :
  ∀ {θ X} →
  nextAbstractIndex θ ≤ X →
  abstract-name (type-name X) ∉ θ
abstract-name-fresh-at {θ} {X} θ≤X name∈ =
  n≮n X
    (≤-trans (abstract-index-bound name∈) θ≤X)

next-abstract-fresh-below :
  ∀ {θ θ′} →
  nextAbstractIndex θ′ ≤ nextAbstractIndex θ →
  abstract-name (nextAbstractName θ) ∉ θ′
next-abstract-fresh-below =
  abstract-name-fresh-at

closed-value-instantiate-head :
  ∀ {γ θ V U X α}
    {vV : N.Value V} →
  (fresh : abstract-name X ∉ θ) →
  ClosedValue γ (abstract-name X ∷ θ) vV U →
  ClosedValue γ (seal-name α ∷ θ) vV
    (substituteName X α U)
closed-value-instantiate-head
    {γ = γ} {θ} {U = U} {X} {α} {vV = vV}
    fresh body =
  subst
    (λ θ′ →
      ClosedValue γ θ′ vV (substituteName X α U))
    (replaceName-head fresh)
    (closedValue-replace {X = X} {α = α} (here refl) body)

closed-value-cast-body :
  ∀ {γ θ M U c}
    {vM : N.Value M} {ic : Coercions.Inert c} →
  ClosedValue γ θ (vM N.⟨ ic ⟩) U →
  Σ[ V ∈ Value ] ClosedValue γ θ vM V
closed-value-cast-body (closed-tagged body) =
  _ , body
closed-value-cast-body (closed-sealed lookup-eq body) =
  _ , body
closed-value-cast-body (closed-function-proxy body) =
  _ , body
closed-value-cast-body (closed-forall-proxy body) =
  _ , body
closed-value-cast-body (closed-generalized body) =
  _ , body
