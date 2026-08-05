module proof.InterpreterCloseValueInstantiationProof where

-- File Charter:
--   * Proves that `closeValue` commutes with replacing a live abstract name.
--   * Handles nested type abstractions using membership and supply equality.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using
  (_≢_; cong; sym; trans)
open import Relation.Nullary using (yes; no)

import Coercions as C
open import Interpreter
import NuTerms as N
open import proof.InterpreterClosedValueProof using
  ( lookup-seal-replace
  ; next-abstract-fresh
  ; replaceName-cons-no
  ; replaceName-head
  )
open import proof.InterpreterClosedValueStructural using
  (next-generated-abstract-index)
open import Types using (Ground; ★⇒★; ＇_; ‵_)


ground-irrelevant :
  ∀ {G} →
  (g h : Ground G) →
  g ≡ h
ground-irrelevant (＇ X) (＇ .X) =
  refl
ground-irrelevant (‵ ι) (‵ .ι) =
  refl
ground-irrelevant ★⇒★ ★⇒★ =
  refl


runtime-ground-replace :
  ∀ {θ G X α} →
  RuntimeGround θ G →
  RuntimeGround (replaceName X α θ) G
runtime-ground-replace {θ = θ} {X = X} {α}
    (seal-variable-ground {X = Y} {α = β} name-eq) =
  seal-variable-ground
    (lookup-seal-replace
      {θ = θ} {X = X} {Y = Y} {α = α} {β = β} name-eq)
runtime-ground-replace (base-ground ι) =
  base-ground ι
runtime-ground-replace function-ground =
  function-ground


next-name-equal :
  ∀ {θ θ′} →
  nextAbstractIndex θ ≡ nextAbstractIndex θ′ →
  nextAbstractName θ ≡ nextAbstractName θ′
next-name-equal supply =
  cong type-name supply


generated-name-distinct :
  ∀ {X θ} →
  abstract-name X ∈ θ →
  X ≢ nextAbstractName θ
generated-name-distinct X∈ refl =
  next-abstract-fresh _ X∈


replaceName-generated-cons :
  ∀ {X α θ} →
  abstract-name X ∈ θ →
  replaceName X α
    (abstract-name (nextAbstractName θ) ∷ θ) ≡
    abstract-name (nextAbstractName θ) ∷ replaceName X α θ
replaceName-generated-cons X∈ =
  replaceName-cons-no (generated-name-distinct X∈)


replaceName-preserves-generated-supply :
  ∀ {X α θ} →
  (X∈ : abstract-name X ∈ θ) →
  nextAbstractIndex (replaceName X α θ) ≡ nextAbstractIndex θ →
  nextAbstractIndex
    (replaceName X α
      (abstract-name (nextAbstractName θ) ∷ θ)) ≡
  nextAbstractIndex
    (abstract-name (nextAbstractName θ) ∷ θ)
replaceName-preserves-generated-supply {X} {α} {θ} X∈ supply
    rewrite replaceName-generated-cons {X = X} {α = α} X∈
          | supply =
  refl


closeValue-type-abstraction-result :
  ∀ {M γ θ U}
    (vM : N.Value M) →
  closeValue vM γ
    (abstract-name (nextAbstractName θ) ∷ θ) ≡ just U →
  closeValue (N.Λ vM) γ θ ≡
    just (type-abstraction (nextAbstractName θ) U)
closeValue-type-abstraction-result {γ = γ} {θ} vM close-eq
    with closeValue vM γ
      (abstract-name (nextAbstractName θ) ∷ θ)
closeValue-type-abstraction-result vM refl | just U =
  refl
closeValue-type-abstraction-result vM () | nothing


substituteName-type-abstraction-free :
  ∀ {X Y α V} →
  X ≢ Y →
  substituteName X α (type-abstraction Y V) ≡
    type-abstraction Y (substituteName X α V)
substituteName-type-abstraction-free {X} {Y} {α} {V} X≢Y
    with X ≟Name Y
substituteName-type-abstraction-free {X} {.X} {α} {V} X≢X
    | yes refl =
  ⊥-elim (X≢X refl)
substituteName-type-abstraction-free {X} {Y} {α} {V} X≢Y
    | no X≢Y′ =
  refl


mutual

  closeValue-replace :
    ∀ {M γ θ U X α}
      (vM : N.Value M) →
    (X∈ : abstract-name X ∈ θ) →
    nextAbstractIndex (replaceName X α θ) ≡ nextAbstractIndex θ →
    closeValue vM γ θ ≡ just U →
    closeValue vM γ (replaceName X α θ) ≡
      just (substituteName X α U)
  closeValue-replace (N.ƛ M) X∈ supply refl =
    refl
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (N.Λ vM) X∈ supply close-eq
      with closeValue vM γ
        (abstract-name (nextAbstractName θ) ∷ θ) in body-eq
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (N.Λ vM) X∈ supply () | nothing
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (N.Λ vM) X∈ supply refl | just V =
    trans
      (closeValue-type-abstraction-result vM target-body)
      (trans
        (cong
          (λ Y →
            just (type-abstraction Y (substituteName X α V)))
          name-eq)
        (cong just
          (sym
            (substituteName-type-abstraction-free
              (generated-name-distinct X∈)))))
    where
    name-eq :
      nextAbstractName (replaceName X α θ) ≡ nextAbstractName θ
    name-eq =
      next-name-equal
        {θ = replaceName X α θ} {θ′ = θ} supply

    source-name-body :
      closeValue vM γ
        (abstract-name (nextAbstractName θ) ∷
          replaceName X α θ) ≡
      just (substituteName X α V)
    source-name-body =
      closeValue-generated-body-replace vM X∈ supply body-eq

    target-body :
      closeValue vM γ
        (abstract-name
          (nextAbstractName (replaceName X α θ)) ∷
          replaceName X α θ) ≡
      just (substituteName X α V)
    target-body =
      trans
        (cong (closeValue vM γ)
          (cong
            (λ Y → abstract-name Y ∷ replaceName X α θ)
            name-eq))
        source-name-body
  closeValue-replace (N.$ κ) X∈ supply refl =
    refl
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ G C.! ⟩) X∈ supply close-eq
      with ground? θ G | closeValue vM γ θ in body-eq
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ G C.! ⟩) X∈ supply () | no ¬gG | body
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ G C.! ⟩) X∈ supply () | yes gG | nothing
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ G C.! ⟩) X∈ supply refl | yes gG | just V
      with ground? (replaceName X α θ) G
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ G C.! ⟩) X∈ supply refl | yes gG | just V
      | no not-runtime-ground =
    ⊥-elim (not-runtime-ground (runtime-ground-replace gG))
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ G C.! ⟩) X∈ supply refl | yes gG | just V
      | yes gG′
      rewrite closeValue-replace vM X∈ supply body-eq =
    cong
      (λ g → just (tagged g (replaceName X α θ)
        (substituteName X α V)))
      (ground-irrelevant
        (runtime-ground-syntax gG′)
        (runtime-ground-syntax gG))
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.seal A Y ⟩) X∈ supply close-eq
      with lookup θ Y in lookup-eq | closeValue vM γ θ in body-eq
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.seal A Y ⟩) X∈ supply ()
      | nothing | body
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.seal A Y ⟩) X∈ supply ()
      | just (abstract-name Z) | body
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.seal A Y ⟩) X∈ supply ()
      | just (seal-name β) | nothing
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.seal A Y ⟩) X∈ supply refl
      | just (seal-name β) | just V
      rewrite lookup-seal-replace
                {θ = θ} {X = X} {Y = Y} {α = α} lookup-eq
            | closeValue-replace vM X∈ supply body-eq =
    refl
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ c C.↦ d ⟩) X∈ supply close-eq
      with closeValue vM γ θ in body-eq
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ c C.↦ d ⟩) X∈ supply () | nothing
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ c C.↦ d ⟩) X∈ supply refl | just V
      rewrite closeValue-replace vM X∈ supply body-eq =
    refl
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.`∀ c ⟩) X∈ supply close-eq
      with closeValue vM γ θ in body-eq
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.`∀ c ⟩) X∈ supply () | nothing
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.`∀ c ⟩) X∈ supply refl | just V
      rewrite closeValue-replace vM X∈ supply body-eq =
    refl
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.gen A c ⟩) X∈ supply close-eq
      with closeValue vM γ θ in body-eq
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.gen A c ⟩) X∈ supply () | nothing
  closeValue-replace {γ = γ} {θ} {X = X} {α}
      (vM N.⟨ C.gen A c ⟩) X∈ supply refl | just V
      rewrite closeValue-replace vM X∈ supply body-eq =
    refl


  closeValue-generated-body-replace :
    ∀ {M γ θ U X α}
      (vM : N.Value M) →
    (X∈ : abstract-name X ∈ θ) →
    (supply :
      nextAbstractIndex (replaceName X α θ) ≡
      nextAbstractIndex θ) →
    closeValue vM γ
      (abstract-name (nextAbstractName θ) ∷ θ) ≡ just U →
    closeValue vM γ
      (abstract-name (nextAbstractName θ) ∷ replaceName X α θ) ≡
      just (substituteName X α U)
  closeValue-generated-body-replace
      {γ = γ} {θ} {X = X} {α} vM X∈ supply close-eq =
    trans
      (cong (closeValue vM γ)
        (sym (replaceName-generated-cons {X = X} {α = α} X∈)))
      (closeValue-replace
        vM
        (there X∈)
        (replaceName-preserves-generated-supply X∈ supply)
        close-eq)


generated-head-supply :
  ∀ {θ α} →
  nextAbstractIndex
    (replaceName (nextAbstractName θ) α
      (abstract-name (nextAbstractName θ) ∷ θ)) ≡
  nextAbstractIndex
    (abstract-name (nextAbstractName θ) ∷ θ)
generated-head-supply {θ} {α} =
  trans
    (cong nextAbstractIndex
      (replaceName-head (next-abstract-fresh θ)))
    (sym (next-generated-abstract-index θ))


closeValue-instantiate-generated :
  ∀ {M γ θ U α}
    (vM : N.Value M) →
  closeValue vM γ
    (abstract-name (nextAbstractName θ) ∷ θ) ≡ just U →
  closeValue vM γ (seal-name α ∷ θ) ≡
    just (substituteName (nextAbstractName θ) α U)
closeValue-instantiate-generated {γ = γ} {θ} {U} {α} vM close-eq =
  trans
    (cong (closeValue vM γ)
      (sym
        (replaceName-head
          {X = nextAbstractName θ} {α = α}
          (next-abstract-fresh θ))))
    (closeValue-replace
      vM (here refl)
      (generated-head-supply {θ = θ} {α = α}) close-eq)
