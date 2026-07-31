module proof.ImprecisionComposition where

-- File Charter:
--   * Composes one-context GTPLC narrowing and widening bundles.
--   * Normalizes identity, function, and universal composition.
--   * Uses typed sequencing for the remaining closure cases.
--   * Proves the raw-coercion left and right identity laws.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import TyStore
open import Coercions
open import NarrowWiden

uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

------------------------------------------------------------------------
-- Structural identity coercions
------------------------------------------------------------------------

data Identity : Coercion → Set where
  identity-id : Identity id
  identity-fun : ∀ {c d}
    → Identity c
    → Identity d
    → Identity (c ↦ d)
  identity-all : ∀ {c}
    → Identity c
    → Identity (`∀ c)

identity? : ∀ c → Dec (Identity c)
identity? id = yes identity-id
identity? (c ︔ d) = no (λ ())
identity? (c ↦ d) with identity? c | identity? d
identity? (c ↦ d) | yes c-id | yes d-id =
  yes (identity-fun c-id d-id)
identity? (c ↦ d) | no c-not-id | _ =
  no (λ { (identity-fun c-id d-id) → c-not-id c-id })
identity? (c ↦ d) | yes c-id | no d-not-id =
  no (λ { (identity-fun c-id′ d-id) → d-not-id d-id })
identity? (`∀ c) with identity? c
identity? (`∀ c) | yes c-id = yes (identity-all c-id)
identity? (`∀ c) | no c-not-id =
  no (λ { (identity-all c-id) → c-not-id c-id })
identity? (G !) = no (λ ())
identity? (G ？) = no (λ ())
identity? (seal X) = no (λ ())
identity? (unseal X) = no (λ ())
identity? (gen c) = no (λ ())
identity? (inst c) = no (λ ())
identity? error = no (λ ())

mutual

  identity-narrowing-endpoints : ∀ {μ Δ Σ c A B}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → Identity c
    → A ≡ B
  identity-narrowing-endpoints (idᵃ a hA) identity-id = refl
  identity-narrowing-endpoints (p ↦ q)
      (identity-fun p-id q-id) =
    cong₂ _⇒_
      (sym (identity-widening-endpoints p p-id))
      (identity-narrowing-endpoints q q-id)
  identity-narrowing-endpoints (∀ⁿ p) (identity-all p-id) =
    cong `∀ (identity-narrowing-endpoints p p-id)
  identity-narrowing-endpoints (seqⁿ p q) ()
  identity-narrowing-endpoints (untag G hG allowed G꞉B) ()
  identity-narrowing-endpoints
      (untag-seq G hG allowed G꞉A p A≢B) ()
  identity-narrowing-endpoints (seal X<Δ hA X,A∈Σ allowed) ()
  identity-narrowing-endpoints
      (seal-seq p X<Δ X,B∈Σ allowed A≢B) ()
  identity-narrowing-endpoints
      (seal-head X<Δ hA X,A∈Σ allowed p X≢B) ()
  identity-narrowing-endpoints
      (gen nonvarA zero∈A hB p B≢★) ()

  identity-widening-endpoints : ∀ {μ Δ Σ c A B}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → Identity c
    → A ≡ B
  identity-widening-endpoints (idᵃ a hA) identity-id = refl
  identity-widening-endpoints (p ↦ q)
      (identity-fun p-id q-id) =
    cong₂ _⇒_
      (sym (identity-narrowing-endpoints p p-id))
      (identity-widening-endpoints q q-id)
  identity-widening-endpoints (∀ʷ p) (identity-all p-id) =
    cong `∀ (identity-widening-endpoints p p-id)
  identity-widening-endpoints (seqʷ p q) ()
  identity-widening-endpoints (tag G hG allowed G꞉A) ()
  identity-widening-endpoints
      (tag-seq G p hG allowed G꞉B A≢B) ()
  identity-widening-endpoints (unseal X<Δ hA X,A∈Σ allowed) ()
  identity-widening-endpoints
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B) ()
  identity-widening-endpoints
      (unseal-tail p X<Δ hB X,B∈Σ allowed A≢X) ()
  identity-widening-endpoints
      (inst nonvarA zero∈A hB p B≢★) ()

------------------------------------------------------------------------
-- Composition
------------------------------------------------------------------------

infixl 6 _⨟ⁿ_
infixl 6 _⨟ʷ_

mutual

  _⨟ⁿ_ : ∀ {μ Δ Σ A B C}
    → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
    → μ ∣ Δ ∣ Σ ⊢ B ⊒ C
    → μ ∣ Δ ∣ Σ ⊢ A ⊒ C
  _⨟ⁿ_ (c , p) (d , q) with identity? c | identity? d
  _⨟ⁿ_ (c , p) (d , q) | yes c-id | _
      rewrite identity-narrowing-endpoints p c-id =
    d , q
  _⨟ⁿ_ (c , p) (d , q) | no c-not-id | yes d-id
      rewrite identity-narrowing-endpoints q d-id =
    c , p
  _⨟ⁿ_ ((c ↦ d) , (p₁ ↦ p₂)) ((e ↦ f) , (q₁ ↦ q₂))
      | no c↦d-not-id | no e↦f-not-id
      with (e , q₁) ⨟ʷ (c , p₁) | (d , p₂) ⨟ⁿ (f , q₂)
  _⨟ⁿ_ ((c ↦ d) , (p₁ ↦ p₂)) ((e ↦ f) , (q₁ ↦ q₂))
      | no c↦d-not-id | no e↦f-not-id
      | g , r₁ | h , r₂ =
    (g ↦ h) , (r₁ ↦ r₂)
  _⨟ⁿ_ (`∀ c , ∀ⁿ p) (`∀ d , ∀ⁿ q)
      | no ∀c-not-id | no ∀d-not-id
      with (c , p) ⨟ⁿ (d , q)
  _⨟ⁿ_ (`∀ c , ∀ⁿ p) (`∀ d , ∀ⁿ q)
      | no ∀c-not-id | no ∀d-not-id | e , r =
    `∀ e , ∀ⁿ r
  _⨟ⁿ_ (c , p) (d , q) | no c-not-id | no d-not-id =
    (c ︔ d) , seqⁿ p q

  _⨟ʷ_ : ∀ {μ Δ Σ A B C}
    → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
    → μ ∣ Δ ∣ Σ ⊢ B ⊑ C
    → μ ∣ Δ ∣ Σ ⊢ A ⊑ C
  _⨟ʷ_ (c , p) (d , q) with identity? c | identity? d
  _⨟ʷ_ (c , p) (d , q) | yes c-id | _
      rewrite identity-widening-endpoints p c-id =
    d , q
  _⨟ʷ_ (c , p) (d , q) | no c-not-id | yes d-id
      rewrite identity-widening-endpoints q d-id =
    c , p
  _⨟ʷ_ ((c ↦ d) , (p₁ ↦ p₂)) ((e ↦ f) , (q₁ ↦ q₂))
      | no c↦d-not-id | no e↦f-not-id
      with (e , q₁) ⨟ⁿ (c , p₁) | (d , p₂) ⨟ʷ (f , q₂)
  _⨟ʷ_ ((c ↦ d) , (p₁ ↦ p₂)) ((e ↦ f) , (q₁ ↦ q₂))
      | no c↦d-not-id | no e↦f-not-id
      | g , r₁ | h , r₂ =
    (g ↦ h) , (r₁ ↦ r₂)
  _⨟ʷ_ (`∀ c , ∀ʷ p) (`∀ d , ∀ʷ q)
      | no ∀c-not-id | no ∀d-not-id
      with (c , p) ⨟ʷ (d , q)
  _⨟ʷ_ (`∀ c , ∀ʷ p) (`∀ d , ∀ʷ q)
      | no ∀c-not-id | no ∀d-not-id | e , r =
    `∀ e , ∀ʷ r
  _⨟ʷ_ (c , p) (d , q) | no c-not-id | no d-not-id =
    (c ︔ d) , seqʷ p q

------------------------------------------------------------------------
-- Identity laws
------------------------------------------------------------------------

left-id-composition : ∀ {μ Δ Σ A B}
  → (i : μ ∣ Δ ∣ Σ ⊢ A ⊒ A)
  → Identity (proj₁ i)
  → (p : μ ∣ Δ ∣ Σ ⊢ A ⊒ B)
  → proj₁ (i ⨟ⁿ p) ≡ proj₁ p
left-id-composition (c , p) c-id q with identity? c
left-id-composition (c , p) c-id q | yes c-id′
    with identity? (proj₁ q)
left-id-composition (c , p) c-id q | yes c-id′ | yes q-id
    rewrite uip (identity-narrowing-endpoints p c-id′) refl =
  refl
left-id-composition (c , p) c-id q | yes c-id′ | no q-not-id
    rewrite uip (identity-narrowing-endpoints p c-id′) refl =
  refl
left-id-composition (c , p) c-id q | no c-not-id =
  ⊥-elim (c-not-id c-id)

left-id-compositionʷ : ∀ {μ Δ Σ A B}
  → (i : μ ∣ Δ ∣ Σ ⊢ A ⊑ A)
  → Identity (proj₁ i)
  → (p : μ ∣ Δ ∣ Σ ⊢ A ⊑ B)
  → proj₁ (i ⨟ʷ p) ≡ proj₁ p
left-id-compositionʷ (c , p) c-id q with identity? c
left-id-compositionʷ (c , p) c-id q | yes c-id′
    with identity? (proj₁ q)
left-id-compositionʷ (c , p) c-id q | yes c-id′ | yes q-id
    rewrite uip (identity-widening-endpoints p c-id′) refl =
  refl
left-id-compositionʷ (c , p) c-id q | yes c-id′ | no q-not-id
    rewrite uip (identity-widening-endpoints p c-id′) refl =
  refl
left-id-compositionʷ (c , p) c-id q | no c-not-id =
  ⊥-elim (c-not-id c-id)

------------------------------------------------------------------------
-- Equality of bundled coercions
------------------------------------------------------------------------

infix 4 _≐ⁿ_
infix 4 _≐ʷ_

_≐ⁿ_ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → Set
p ≐ⁿ q = proj₁ p ≡ proj₁ q

_≐ʷ_ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → Set
p ≐ʷ q = proj₁ p ≡ proj₁ q
