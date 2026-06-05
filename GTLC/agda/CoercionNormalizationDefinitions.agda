module CoercionNormalizationDefinitions where

-- File Charter:
--   * Shared public vocabulary for the bridge between coercions and
--     quotiented coercions.
--   * Defines the translations, coercion reduction/equivalence relations,
--     typed quotient equivalence, and irreducibility predicate.
--   * Proof scripts and normalization live in `proof/CoercionNormalization.agda`;
--     public theorem wrappers live in `CoercionNormalization.agda`.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

open import Types
open import Coercions
import CoercionReduction as Quot
import CoercionEquality as QuotEq

coercion→quotiented : Coercion → Quot.Coercion
coercion→quotiented (idᶜ A) = []
coercion→quotiented (G !) = Quot.singleᶜ (Quot._! G)
coercion→quotiented (((_`? {ℓ = ℓ}) G)) =
  Quot.singleᶜ (Quot._？_ G ℓ)
coercion→quotiented (c ↦ d) =
  Quot.singleᶜ (Quot._↦_ (coercion→quotiented c)
                           (coercion→quotiented d))
coercion→quotiented (c ⨟ d) =
  Quot._⨟_ (coercion→quotiented c) (coercion→quotiented d)
coercion→quotiented (⊥ᶜ A ⇨ B at ℓ) =
  Quot.singleᶜ (Quot.⊥ᶜ_⇨_at_ A B ℓ)

coercion→quotiented-wt : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → Quot.⊢_⦂_⇨_ (coercion→quotiented c) A B
coercion→quotiented-wt ⊢idᶜ = Quot.⊢[]
coercion→quotiented-wt (⊢! g) = Quot.⊢singleᶜ (Quot.⊢! g)
coercion→quotiented-wt (⊢? g) = Quot.⊢singleᶜ (Quot.⊢? g)
coercion→quotiented-wt (⊢↦ cwt dwt) =
  Quot.⊢singleᶜ (Quot.⊢↦ (coercion→quotiented-wt cwt)
                           (coercion→quotiented-wt dwt))
coercion→quotiented-wt (⊢⨟ cwt dwt) =
  Quot.⊢⨟ (coercion→quotiented-wt cwt) (coercion→quotiented-wt dwt)
coercion→quotiented-wt ⊢⊥ = Quot.⊢singleᶜ Quot.⊢⊥

infix 4 _—→ᶜʳ_
infix 4 _—↠ᶜʳ_
infix 4 _≈ᶜʳ_
infix 4 _—↠≈ᶜʳ_
infix 4 _;ᶜʳ_—→_
infix 3 _∎ᶜʳ
infixr 2 _—→ᶜʳ⟨_⟩_

data _;ᶜʳ_—→_ : Coercion → Coercion → Coercion → Set where
  β-idLᶜʳ : ∀ {A c}
    → idᶜ A ;ᶜʳ c —→ c

  β-idRᶜʳ : ∀ {B c}
    → c ;ᶜʳ idᶜ B —→ c

  β-proj-inj-okᶜʳ : ∀ {G ℓ}
    → G ! ;ᶜʳ ((_`? {ℓ = ℓ}) G) —→ idᶜ G

  β-proj-inj-badᶜʳ : ∀ {G H ℓ}
    → G ≢ H
    → G ! ;ᶜʳ ((_`? {ℓ = ℓ}) H) —→ (⊥ᶜ G ⇨ H at ℓ)

  β-↦ᶜʳ : ∀ {c d c′ d′}
    → (c ↦ d) ;ᶜʳ (c′ ↦ d′) —→ ((c′ ⨟ c) ↦ (d ⨟ d′))

  β-⊥Lᶜʳ : ∀ {A B C d ℓ}
    → ⊢ d ⦂ B ⇨ C
    → (⊥ᶜ A ⇨ B at ℓ) ;ᶜʳ d —→ (⊥ᶜ A ⇨ C at ℓ)

  β-!⊥ᶜʳ : ∀ {G B ℓ}
    → G ! ;ᶜʳ (⊥ᶜ ★ ⇨ B at ℓ) —→ (⊥ᶜ G ⇨ B at ℓ)

  β-↦⊥ᶜʳ : ∀ {c d A B C D E ℓ}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → (c ↦ d) ;ᶜʳ (⊥ᶜ (C ⇒ D) ⇨ E at ℓ)
      —→ (⊥ᶜ (A ⇒ B) ⇨ E at ℓ)

data _—→ᶜʳ_ : Coercion → Coercion → Set where
  ξ-pairᶜʳ : ∀ {c d e}
    → c ;ᶜʳ d —→ e
    → (c ⨟ d) —→ᶜʳ e

  ξ-⨟₁ᶜʳ : ∀ {c c′ d}
    → c —→ᶜʳ c′
    → (c ⨟ d) —→ᶜʳ (c′ ⨟ d)

  ξ-⨟₂ᶜʳ : ∀ {c d d′}
    → d —→ᶜʳ d′
    → (c ⨟ d) —→ᶜʳ (c ⨟ d′)

  ξ-↦₁ᶜʳ : ∀ {c c′ d}
    → c —→ᶜʳ c′
    → (c ↦ d) —→ᶜʳ (c′ ↦ d)

  ξ-↦₂ᶜʳ : ∀ {c d d′}
    → d —→ᶜʳ d′
    → (c ↦ d) —→ᶜʳ (c ↦ d′)

data _—↠ᶜʳ_ : Coercion → Coercion → Set where
  _∎ᶜʳ : (c : Coercion) → c —↠ᶜʳ c

  _—→ᶜʳ⟨_⟩_ : (c : Coercion) {d e : Coercion}
    → c —→ᶜʳ d
    → d —↠ᶜʳ e
    → c —↠ᶜʳ e

data _≈ᶜʳ_ : Coercion → Coercion → Set where
  ≈ᶜʳ-refl : ∀ {c}
    → c ≈ᶜʳ c

  ≈ᶜʳ-sym : ∀ {c d}
    → c ≈ᶜʳ d
    → d ≈ᶜʳ c

  ≈ᶜʳ-trans : ∀ {c d e}
    → c ≈ᶜʳ d
    → d ≈ᶜʳ e
    → c ≈ᶜʳ e

  ≈ᶜʳ-⨟ : ∀ {c c′ d d′}
    → c ≈ᶜʳ c′
    → d ≈ᶜʳ d′
    → (c ⨟ d) ≈ᶜʳ (c′ ⨟ d′)

  ≈ᶜʳ-↦ : ∀ {c c′ d d′}
    → c ≈ᶜʳ c′
    → d ≈ᶜʳ d′
    → (c ↦ d) ≈ᶜʳ (c′ ↦ d′)

  ≈ᶜʳ-idL : ∀ {A c}
    → (idᶜ A ⨟ c) ≈ᶜʳ c

  ≈ᶜʳ-idR : ∀ {B c}
    → (c ⨟ idᶜ B) ≈ᶜʳ c

  ≈ᶜʳ-assoc : ∀ {c d e}
    → ((c ⨟ d) ⨟ e) ≈ᶜʳ (c ⨟ (d ⨟ e))

data _—↠≈ᶜʳ_ : Coercion → Coercion → Set where
  ≈ᶜʳ-done : ∀ {c d}
    → c ≈ᶜʳ d
    → c —↠≈ᶜʳ d

  step≈ᶜʳ : ∀ {c d e}
    → c —→ᶜʳ d
    → d —↠≈ᶜʳ e
    → c —↠≈ᶜʳ e

  eq≈ᶜʳ : ∀ {c d e}
    → c ≈ᶜʳ d
    → d —↠≈ᶜʳ e
    → c —↠≈ᶜʳ e

record Irreducible (c : Coercion) : Set where
  constructor irred
  field
    no-step : ∀ {d} → ¬ (c —→ᶜʳ d)

mutual
  quotiented-crcn→coercion : ∀ {c A B}
    → Quot.⊢_⦂_⇨ᶜ_ c A B
    → Σ[ d ∈ Coercion ] ⊢ d ⦂ A ⇨ B
  quotiented-crcn→coercion (Quot.⊢! g) = _ ! , ⊢! g
  quotiented-crcn→coercion (Quot.⊢? {G = G} {ℓ = ℓ} g) =
    (_`? {ℓ = ℓ}) G , ⊢? g
  quotiented-crcn→coercion (Quot.⊢↦ cwt dwt)
    with quotiented→coercion cwt | quotiented→coercion dwt
  ... | c , cwt′ | d , dwt′ = c ↦ d , ⊢↦ cwt′ dwt′
  quotiented-crcn→coercion (Quot.⊢⊥ {A = A} {B = B} {ℓ = ℓ}) =
    ⊥ᶜ A ⇨ B at ℓ , ⊢⊥

  quotiented→coercion : ∀ {c A B}
    → Quot.⊢_⦂_⇨_ c A B
    → Σ[ d ∈ Coercion ] ⊢ d ⦂ A ⇨ B
  quotiented→coercion Quot.⊢[] = idᶜ _ , ⊢idᶜ
  quotiented→coercion (Quot.⊢∷ cwt Quot.⊢[]) =
    quotiented-crcn→coercion cwt
  quotiented→coercion (Quot.⊢∷ cwt (Quot.⊢∷ dwt restwt))
    with quotiented-crcn→coercion cwt
       | quotiented→coercion (Quot.⊢∷ dwt restwt)
  ... | c , cwt′ | d , dwt′ = c ⨟ d , ⊢⨟ cwt′ dwt′

record TypedCoercionEq (A B : Ty) (c d : Coercion) : Set where
  constructor typed-coercion-eq
  field
    left-wt : ⊢ c ⦂ A ⇨ B
    right-wt : ⊢ d ⦂ A ⇨ B
    quotiented-eq : QuotEq._≈ᶜ_ (coercion→quotiented c)
                                  (coercion→quotiented d)
