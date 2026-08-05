module proof.InterpreterClosedValueProof where

-- File Charter:
--   * Relates successful `closeValue` calls to `ClosedValue`.
--   * Proves freshness of generated abstract names.
--   * Proves that replacing a live abstract name by a seal commutes with the
--     proof-relevant close graph.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≤_; zero; suc; z≤n)
open import Data.Nat.Properties using
  ( m≤m⊔n
  ; m≤n⇒m≤o⊔n
  ; n≤1+n
  ; n≮n
  ; ≤-refl
  ; ≤-trans
  )
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≢_; cong; subst; sym)

open import Coercions using (Inert)
import Coercions
open import Interpreter
open import Runtime.InterpreterClosedValue
import NuTerms as N

------------------------------------------------------------------------
-- Fresh abstract names
------------------------------------------------------------------------

abstract-index-bound :
  ∀ {θ x} →
  abstract-name (type-name x) ∈ θ →
  suc x ≤ nextAbstractIndex θ
abstract-index-bound {θ = abstract-name (type-name y) ∷ θ}
    (here refl) =
  m≤m⊔n (suc y) (nextAbstractIndex θ)
abstract-index-bound {θ = abstract-name (type-name y) ∷ θ}
    (there x∈) =
  m≤n⇒m≤o⊔n (suc y) (abstract-index-bound x∈)
abstract-index-bound {θ = seal-name α ∷ θ} (there x∈) =
  ≤-trans (abstract-index-bound x∈)
    (n≤1+n (nextAbstractIndex θ))

next-abstract-fresh :
  ∀ θ →
  abstract-name (nextAbstractName θ) ∉ θ
next-abstract-fresh θ name∈ =
  n≮n (nextAbstractIndex θ)
    (abstract-index-bound name∈)

------------------------------------------------------------------------
-- Successful close calls
------------------------------------------------------------------------

closeValue-closed :
  ∀ {V U γ θ} →
  (vV : N.Value V) →
  closeValue vV γ θ ≡ just U →
  ClosedValue γ θ vV U
closeValue-closed (N.ƛ N) refl =
  closed-closure
closeValue-closed {γ = γ} {θ} (N.Λ vV) eq
    with closeValue vV γ
      (abstract-name (nextAbstractName θ) ∷ θ) in body-eq
closeValue-closed {γ = γ} {θ} (N.Λ vV) eq
    | just U with eq
closeValue-closed {γ = γ} {θ} (N.Λ vV) eq
    | just U | refl =
  closed-type-abstraction
    (next-abstract-fresh θ)
    (closeValue-closed vV body-eq)
closeValue-closed {γ = γ} {θ} (N.Λ vV) ()
    | nothing
closeValue-closed (N.$ κ) refl =
  closed-constant κ
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions._! G ⟩) eq
    with ground? θ G | closeValue vV γ θ in body-eq
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions._! G ⟩) eq
    | yes runtime-ground | just U with eq
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions._! G ⟩) eq
    | yes runtime-ground | just U | refl =
  closed-tagged (closeValue-closed vV body-eq)
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions._! G ⟩) ()
    | yes runtime-ground | nothing
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions._! G ⟩) ()
    | no not-runtime-ground | result
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.seal A X ⟩) eq
    with lookup θ X in name-eq | closeValue vV γ θ in body-eq
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.seal A X ⟩) eq
    | just (seal-name α) | just U with eq
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.seal A X ⟩) eq
    | just (seal-name α) | just U | refl =
  closed-sealed name-eq (closeValue-closed vV body-eq)
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.seal A X ⟩) ()
    | just (seal-name α) | nothing
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.seal A X ⟩) ()
    | just (abstract-name Y) | result
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.seal A X ⟩) ()
    | nothing | result
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ p Coercions.↦ q ⟩) eq
    with closeValue vV γ θ in body-eq
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ p Coercions.↦ q ⟩) eq
    | just U with eq
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ p Coercions.↦ q ⟩) eq
    | just U | refl =
  closed-function-proxy (closeValue-closed vV body-eq)
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ p Coercions.↦ q ⟩) () | nothing
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.`∀ c ⟩) eq
    with closeValue vV γ θ in body-eq
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.`∀ c ⟩) eq
    | just U with eq
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.`∀ c ⟩) eq
    | just U | refl =
  closed-forall-proxy (closeValue-closed vV body-eq)
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.`∀ c ⟩) () | nothing
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.gen A c ⟩) eq
    with closeValue vV γ θ in body-eq
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.gen A c ⟩) eq
    | just U with eq
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.gen A c ⟩) eq
    | just U | refl =
  closed-generalized (closeValue-closed vV body-eq)
closeValue-closed {γ = γ} {θ}
    (vV N.⟨ Coercions.gen A c ⟩) () | nothing

------------------------------------------------------------------------
-- Abstract-name replacement
------------------------------------------------------------------------

abstract-membership-replace :
  ∀ {θ X Y α} →
  X ≢ Y →
  abstract-name Y ∉ θ →
  abstract-name Y ∉ replaceName X α θ
abstract-membership-replace {θ = []} X≢Y Y∉ ()
abstract-membership-replace
    {θ = abstract-name Z ∷ θ} {X} {Y} {α}
    X≢Y Y∉ Y∈
    with X ≟Name Z
abstract-membership-replace
    {θ = abstract-name .X ∷ θ} {X} {Y} {α}
    X≢Y Y∉ (there Y∈) | yes refl =
  abstract-membership-replace X≢Y
    (λ Y∈′ → Y∉ (there Y∈′)) Y∈
abstract-membership-replace
    {θ = abstract-name .X ∷ θ} {X} {Y} {α}
    X≢Y Y∉ (here ()) | yes refl
abstract-membership-replace
    {θ = abstract-name Z ∷ θ} {X} {Y} {α}
    X≢Y Y∉ (here refl) | no X≢Z =
  Y∉ (here refl)
abstract-membership-replace
    {θ = abstract-name Z ∷ θ} {X} {Y} {α}
    X≢Y Y∉ (there Y∈) | no X≢Z =
  abstract-membership-replace X≢Y
    (λ Y∈′ → Y∉ (there Y∈′)) Y∈
abstract-membership-replace
    {θ = seal-name β ∷ θ} X≢Y Y∉ (there Y∈) =
  abstract-membership-replace X≢Y
    (λ Y∈′ → Y∉ (there Y∈′)) Y∈

lookup-seal-replace :
  ∀ {θ X Y α β} →
  lookup θ Y ≡ just (seal-name β) →
  lookup (replaceName X α θ) Y ≡ just (seal-name β)
lookup-seal-replace {θ = []} ()
lookup-seal-replace
    {θ = abstract-name Z ∷ θ} {X} {zero} eq
    with X ≟Name Z
lookup-seal-replace
    {θ = abstract-name .X ∷ θ} {X} {zero} ()
    | yes refl
lookup-seal-replace
    {θ = abstract-name Z ∷ θ} {X} {zero} ()
    | no X≢Z
lookup-seal-replace
    {θ = abstract-name Z ∷ θ} {X} {suc Y} eq
    with X ≟Name Z
lookup-seal-replace
    {θ = abstract-name .X ∷ θ} {X} {suc Y} {α} {β} eq
    | yes refl =
  lookup-seal-replace
    {θ = θ} {X = X} {Y = Y} {α = α} {β = β} eq
lookup-seal-replace
    {θ = abstract-name Z ∷ θ} {X} {suc Y} {α} {β} eq
    | no X≢Z =
  lookup-seal-replace
    {θ = θ} {X = X} {Y = Y} {α = α} {β = β} eq
lookup-seal-replace {θ = seal-name β ∷ θ} {Y = zero} refl =
  refl
lookup-seal-replace
    {θ = seal-name β′ ∷ θ} {X} {Y = suc Y} {α} {β} eq =
  lookup-seal-replace
    {θ = θ} {X = X} {Y = Y} {α = α} {β = β} eq

replaceName-cons-no :
  ∀ {X Y α θ} →
  X ≢ Y →
  replaceName X α (abstract-name Y ∷ θ) ≡
    abstract-name Y ∷ replaceName X α θ
replaceName-cons-no {X} {Y} X≢Y with X ≟Name Y
replaceName-cons-no {X} {.X} X≢X | yes refl =
  ⊥-elim (X≢X refl)
replaceName-cons-no {X} {Y} X≢Y | no X≢Y′ =
  refl

replaceName-fresh :
  ∀ {X α θ} →
  abstract-name X ∉ θ →
  replaceName X α θ ≡ θ
replaceName-fresh {θ = []} fresh =
  refl
replaceName-fresh {X} {α}
    {θ = abstract-name Y ∷ θ} fresh
    with X ≟Name Y
replaceName-fresh {X} {α}
    {θ = abstract-name .X ∷ θ} fresh
    | yes refl =
  ⊥-elim (fresh (here refl))
replaceName-fresh {X} {α}
    {θ = abstract-name Y ∷ θ} fresh
    | no X≢Y
    rewrite replaceName-fresh {X = X} {α = α} {θ = θ}
      (λ X∈ → fresh (there X∈)) =
  refl
replaceName-fresh {X} {α}
    {θ = seal-name β ∷ θ} fresh
    rewrite replaceName-fresh {X = X} {α = α} {θ = θ}
      (λ X∈ → fresh (there X∈)) =
  refl

replaceName-head :
  ∀ {X α θ} →
  abstract-name X ∉ θ →
  replaceName X α (abstract-name X ∷ θ) ≡ seal-name α ∷ θ
replaceName-head {X} {α} {θ} fresh with X ≟Name X
replaceName-head {X} {α} {θ} fresh | yes refl
    rewrite replaceName-fresh {X = X} {α = α} {θ = θ} fresh =
  refl
replaceName-head {X} {α} {θ} fresh | no X≢X =
  ⊥-elim (X≢X refl)

closedValue-replace :
  ∀ {V U γ θ X α}
    {vV : N.Value V} →
  abstract-name X ∈ θ →
  ClosedValue γ θ vV U →
  ClosedValue γ (replaceName X α θ) vV
    (substituteName X α U)
closedValue-replace X∈ closed-closure =
  closed-closure
closedValue-replace
    {γ = γ} {θ = θ} {X = X} {α}
    X∈
    (closed-type-abstraction
      {V = Vbody} {U = Ubody} {X = Y} {vV = vBody}
      Y-fresh body)
    with X ≟Name Y
closedValue-replace
    {γ = γ} {θ = θ} {X = .Y} {α}
    X∈
    (closed-type-abstraction
      {V = Vbody} {U = Ubody} {X = Y} {vV = vBody}
      Y-fresh body)
    | yes refl =
  ⊥-elim (Y-fresh X∈)
closedValue-replace
    {γ = γ} {θ = θ} {X = X} {α}
    X∈
    (closed-type-abstraction
      {V = Vbody} {U = Ubody} {X = Y} {vV = vBody}
      Y-fresh body)
    | no X≢Y =
  closed-type-abstraction
    (abstract-membership-replace X≢Y Y-fresh)
    (subst
      (λ θ′ →
        ClosedValue γ θ′ vBody (substituteName X α Ubody))
      (replaceName-cons-no X≢Y)
      (closedValue-replace {X = X} {α = α}
        (there X∈) body))
closedValue-replace X∈ (closed-constant κ) =
  closed-constant κ
closedValue-replace X∈ (closed-tagged body) =
  closed-tagged (closedValue-replace X∈ body)
closedValue-replace
    {θ = θ} {X = X} {α}
    X∈
    (closed-sealed {X = Y} {α = β} name-eq body) =
  closed-sealed
    (lookup-seal-replace
      {θ = θ} {X = X} {Y = Y} {α = α} {β = β}
      name-eq)
    (closedValue-replace {X = X} {α = α} X∈ body)
closedValue-replace X∈ (closed-function-proxy body) =
  closed-function-proxy (closedValue-replace X∈ body)
closedValue-replace X∈ (closed-forall-proxy body) =
  closed-forall-proxy (closedValue-replace X∈ body)
closedValue-replace X∈ (closed-generalized body) =
  closed-generalized (closedValue-replace X∈ body)
