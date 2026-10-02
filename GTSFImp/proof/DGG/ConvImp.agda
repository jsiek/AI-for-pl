module proof.DGG.ConvImp where

-- File Charter:
--   * Occurrence transport along generator-indexed conversion typing.
--   * A conversion generated at X with representation R only rewrites
--     occurrences of X. Any other variable Y occurs in one endpoint iff it
--     occurs in the other, provided Y is absent from R.
--   * Transports both _∈ᵗ_ and _∉ᵗ_ in both directions because an arrow
--     conversion reverses its domain component.
--   * Recovers direct store membership for a conversion's generator.
--   * Specializes transport to a universal binder, where the generator is
--     shifted and the transported variable is zero.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import Types
open import TyStore using (TyStore; store-lift; _∋_⦂_; S-lift∋)
open import Conversion using (Conv↑; Conv↓)
import Conversion as Conv
open import proof.ImprecisionConsistency using
  (fin-suc-injective; shift-injectiveᵗ; shift-not-occurs;
   zero-absent-shift)

------------------------------------------------------------------------
-- Occurrence and non-occurrence are contradictory
------------------------------------------------------------------------

occurs-absent-⊥ : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∈ᵗ A
  → X ∉ᵗ A
    ---------
  → ⊥
occurs-absent-⊥ var-∈ (∉-var X≢X) = ≢ᶠ→≢ X≢X refl
occurs-absent-⊥ (∈-fun-left X∈A) (∉-fun X∉A X∉B) =
  occurs-absent-⊥ X∈A X∉A
occurs-absent-⊥ (∈-fun-right X∉A′ X∈B) (∉-fun X∉A X∉B) =
  occurs-absent-⊥ X∈B X∉B
occurs-absent-⊥ (∈-all X∈A) (∉-all X∉A) =
  occurs-absent-⊥ X∈A X∉A

------------------------------------------------------------------------
-- Generator membership
------------------------------------------------------------------------

mutual
  conv↑-generator∈ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
      {R A B : Ty Δ} {c : Conv↑ Δ A B}
    → Σ Conv.⊢↑[ X ⦂ R ] c
      --------------------
    → Σ ∋ X ⦂ R
  conv↑-generator∈ (Conv.⊢↑-unseal X∈) = X∈
  conv↑-generator∈ (Conv.⊢↑-⇒ c⊢ d⊢) = conv↓-generator∈ c⊢
  conv↑-generator∈ (Conv.⊢↑-∀ eq c⊢)
      with conv↑-generator∈ c⊢
  conv↑-generator∈ (Conv.⊢↑-∀ eq c⊢) | S-lift∋ X∈ eq′
      with shift-injectiveᵗ (trans (sym eq′) eq)
  conv↑-generator∈ (Conv.⊢↑-∀ eq c⊢) | S-lift∋ X∈ eq′ | refl =
    X∈
  conv↑-generator∈ (Conv.⊢↑-id-var X∈ X≢Y) = X∈
  conv↑-generator∈ (Conv.⊢↑-id-base X∈) = X∈
  conv↑-generator∈ (Conv.⊢↑-id-star X∈) = X∈

  conv↓-generator∈ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
      {R A B : Ty Δ} {c : Conv↓ Δ A B}
    → Σ Conv.⊢↓[ X ⦂ R ] c
      --------------------
    → Σ ∋ X ⦂ R
  conv↓-generator∈ (Conv.⊢↓-seal X∈) = X∈
  conv↓-generator∈ (Conv.⊢↓-⇒ c⊢ d⊢) = conv↑-generator∈ c⊢
  conv↓-generator∈ (Conv.⊢↓-∀ eq c⊢)
      with conv↓-generator∈ c⊢
  conv↓-generator∈ (Conv.⊢↓-∀ eq c⊢) | S-lift∋ X∈ eq′
      with shift-injectiveᵗ (trans (sym eq′) eq)
  conv↓-generator∈ (Conv.⊢↓-∀ eq c⊢) | S-lift∋ X∈ eq′ | refl =
    X∈
  conv↓-generator∈ (Conv.⊢↓-id-var X∈ X≢Y) = X∈
  conv↓-generator∈ (Conv.⊢↓-id-base X∈) = X∈
  conv↓-generator∈ (Conv.⊢↓-id-star X∈) = X∈

------------------------------------------------------------------------
-- Freshness beneath a type binder
------------------------------------------------------------------------

lift-generator-fresh : ∀ {Δ} {Y : TyVar Δ} {R : Ty Δ}
    {R′ : Ty (Nat.suc Δ)}
  → R′ ≡ ⇑ᵗ R
  → Y ∉ᵗ R
    --------------
  → Fin.suc Y ∉ᵗ R′
lift-generator-fresh refl Y∉R = shift-not-occurs Y∉R

------------------------------------------------------------------------
-- Occurrence transport along a generated conversion
------------------------------------------------------------------------

mutual
  conv↑-occurs-pre : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {R A B : Ty Δ} {c : Conv↑ Δ A B}
    → Σ Conv.⊢↑[ X ⦂ R ] c
    → Y ≢ X
    → Y ∉ᵗ R
    → Y ∈ᵗ A
      -------
    → Y ∈ᵗ B
  conv↑-occurs-pre (Conv.⊢↑-unseal X∈) Y≢X Y∉R var-∈ =
    ⊥-elim (Y≢X refl)
  conv↑-occurs-pre (Conv.⊢↑-⇒ c⊢ d⊢) Y≢X Y∉R
      (∈-fun-left Y∈A) =
    ∈-fun-left (conv↓-occurs-post c⊢ Y≢X Y∉R Y∈A)
  conv↑-occurs-pre (Conv.⊢↑-⇒ c⊢ d⊢) Y≢X Y∉R
      (∈-fun-right Y∉A Y∈B) =
    ∈-fun-right (conv↓-absent-post c⊢ Y≢X Y∉R Y∉A)
      (conv↑-occurs-pre d⊢ Y≢X Y∉R Y∈B)
  conv↑-occurs-pre (Conv.⊢↑-∀ eq c⊢) Y≢X Y∉R (∈-all Y∈A) =
    ∈-all
      (conv↑-occurs-pre c⊢
        (λ eq′ → Y≢X (fin-suc-injective eq′))
        (lift-generator-fresh eq Y∉R) Y∈A)
  conv↑-occurs-pre (Conv.⊢↑-id-var X∈ X≢Z) Y≢X Y∉R Y∈Z = Y∈Z
  conv↑-occurs-pre (Conv.⊢↑-id-base X∈) Y≢X Y∉R ()
  conv↑-occurs-pre (Conv.⊢↑-id-star X∈) Y≢X Y∉R ()

  conv↑-occurs-post : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {R A B : Ty Δ} {c : Conv↑ Δ A B}
    → Σ Conv.⊢↑[ X ⦂ R ] c
    → Y ≢ X
    → Y ∉ᵗ R
    → Y ∈ᵗ B
      -------
    → Y ∈ᵗ A
  conv↑-occurs-post (Conv.⊢↑-unseal X∈) Y≢X Y∉R Y∈R =
    ⊥-elim (occurs-absent-⊥ Y∈R Y∉R)
  conv↑-occurs-post (Conv.⊢↑-⇒ c⊢ d⊢) Y≢X Y∉R
      (∈-fun-left Y∈A′) =
    ∈-fun-left (conv↓-occurs-pre c⊢ Y≢X Y∉R Y∈A′)
  conv↑-occurs-post (Conv.⊢↑-⇒ c⊢ d⊢) Y≢X Y∉R
      (∈-fun-right Y∉A′ Y∈B′) =
    ∈-fun-right (conv↓-absent-pre c⊢ Y≢X Y∉R Y∉A′)
      (conv↑-occurs-post d⊢ Y≢X Y∉R Y∈B′)
  conv↑-occurs-post (Conv.⊢↑-∀ eq c⊢) Y≢X Y∉R (∈-all Y∈B) =
    ∈-all
      (conv↑-occurs-post c⊢
        (λ eq′ → Y≢X (fin-suc-injective eq′))
        (lift-generator-fresh eq Y∉R) Y∈B)
  conv↑-occurs-post (Conv.⊢↑-id-var X∈ X≢Z) Y≢X Y∉R Y∈Z = Y∈Z
  conv↑-occurs-post (Conv.⊢↑-id-base X∈) Y≢X Y∉R ()
  conv↑-occurs-post (Conv.⊢↑-id-star X∈) Y≢X Y∉R ()

  conv↓-occurs-pre : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {R A B : Ty Δ} {c : Conv↓ Δ A B}
    → Σ Conv.⊢↓[ X ⦂ R ] c
    → Y ≢ X
    → Y ∉ᵗ R
    → Y ∈ᵗ A
      -------
    → Y ∈ᵗ B
  conv↓-occurs-pre (Conv.⊢↓-seal X∈) Y≢X Y∉R Y∈R =
    ⊥-elim (occurs-absent-⊥ Y∈R Y∉R)
  conv↓-occurs-pre (Conv.⊢↓-⇒ c⊢ d⊢) Y≢X Y∉R
      (∈-fun-left Y∈A) =
    ∈-fun-left (conv↑-occurs-post c⊢ Y≢X Y∉R Y∈A)
  conv↓-occurs-pre (Conv.⊢↓-⇒ c⊢ d⊢) Y≢X Y∉R
      (∈-fun-right Y∉A Y∈B) =
    ∈-fun-right (conv↑-absent-post c⊢ Y≢X Y∉R Y∉A)
      (conv↓-occurs-pre d⊢ Y≢X Y∉R Y∈B)
  conv↓-occurs-pre (Conv.⊢↓-∀ eq c⊢) Y≢X Y∉R (∈-all Y∈A) =
    ∈-all
      (conv↓-occurs-pre c⊢
        (λ eq′ → Y≢X (fin-suc-injective eq′))
        (lift-generator-fresh eq Y∉R) Y∈A)
  conv↓-occurs-pre (Conv.⊢↓-id-var X∈ X≢Z) Y≢X Y∉R Y∈Z = Y∈Z
  conv↓-occurs-pre (Conv.⊢↓-id-base X∈) Y≢X Y∉R ()
  conv↓-occurs-pre (Conv.⊢↓-id-star X∈) Y≢X Y∉R ()

  conv↓-occurs-post : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {R A B : Ty Δ} {c : Conv↓ Δ A B}
    → Σ Conv.⊢↓[ X ⦂ R ] c
    → Y ≢ X
    → Y ∉ᵗ R
    → Y ∈ᵗ B
      -------
    → Y ∈ᵗ A
  conv↓-occurs-post (Conv.⊢↓-seal X∈) Y≢X Y∉R var-∈ =
    ⊥-elim (Y≢X refl)
  conv↓-occurs-post (Conv.⊢↓-⇒ c⊢ d⊢) Y≢X Y∉R
      (∈-fun-left Y∈A′) =
    ∈-fun-left (conv↑-occurs-pre c⊢ Y≢X Y∉R Y∈A′)
  conv↓-occurs-post (Conv.⊢↓-⇒ c⊢ d⊢) Y≢X Y∉R
      (∈-fun-right Y∉A′ Y∈B′) =
    ∈-fun-right (conv↑-absent-pre c⊢ Y≢X Y∉R Y∉A′)
      (conv↓-occurs-post d⊢ Y≢X Y∉R Y∈B′)
  conv↓-occurs-post (Conv.⊢↓-∀ eq c⊢) Y≢X Y∉R (∈-all Y∈B) =
    ∈-all
      (conv↓-occurs-post c⊢
        (λ eq′ → Y≢X (fin-suc-injective eq′))
        (lift-generator-fresh eq Y∉R) Y∈B)
  conv↓-occurs-post (Conv.⊢↓-id-var X∈ X≢Z) Y≢X Y∉R Y∈Z = Y∈Z
  conv↓-occurs-post (Conv.⊢↓-id-base X∈) Y≢X Y∉R ()
  conv↓-occurs-post (Conv.⊢↓-id-star X∈) Y≢X Y∉R ()

  conv↑-absent-pre : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {R A B : Ty Δ} {c : Conv↑ Δ A B}
    → Σ Conv.⊢↑[ X ⦂ R ] c
    → Y ≢ X
    → Y ∉ᵗ R
    → Y ∉ᵗ A
      -------
    → Y ∉ᵗ B
  conv↑-absent-pre (Conv.⊢↑-unseal X∈) Y≢X Y∉R Y∉X = Y∉R
  conv↑-absent-pre (Conv.⊢↑-⇒ c⊢ d⊢) Y≢X Y∉R
      (∉-fun Y∉A Y∉B) =
    ∉-fun (conv↓-absent-post c⊢ Y≢X Y∉R Y∉A)
      (conv↑-absent-pre d⊢ Y≢X Y∉R Y∉B)
  conv↑-absent-pre (Conv.⊢↑-∀ eq c⊢) Y≢X Y∉R (∉-all Y∉A) =
    ∉-all
      (conv↑-absent-pre c⊢
        (λ eq′ → Y≢X (fin-suc-injective eq′))
        (lift-generator-fresh eq Y∉R) Y∉A)
  conv↑-absent-pre (Conv.⊢↑-id-var X∈ X≢Z) Y≢X Y∉R Y∉Z = Y∉Z
  conv↑-absent-pre (Conv.⊢↑-id-base X∈) Y≢X Y∉R Y∉ι = Y∉ι
  conv↑-absent-pre (Conv.⊢↑-id-star X∈) Y≢X Y∉R Y∉★ = Y∉★

  conv↑-absent-post : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {R A B : Ty Δ} {c : Conv↑ Δ A B}
    → Σ Conv.⊢↑[ X ⦂ R ] c
    → Y ≢ X
    → Y ∉ᵗ R
    → Y ∉ᵗ B
      -------
    → Y ∉ᵗ A
  conv↑-absent-post (Conv.⊢↑-unseal X∈) Y≢X Y∉R Y∉R′ =
    ∉-var (≢→≢ᶠ Y≢X)
  conv↑-absent-post (Conv.⊢↑-⇒ c⊢ d⊢) Y≢X Y∉R
      (∉-fun Y∉A′ Y∉B′) =
    ∉-fun (conv↓-absent-pre c⊢ Y≢X Y∉R Y∉A′)
      (conv↑-absent-post d⊢ Y≢X Y∉R Y∉B′)
  conv↑-absent-post (Conv.⊢↑-∀ eq c⊢) Y≢X Y∉R (∉-all Y∉B) =
    ∉-all
      (conv↑-absent-post c⊢
        (λ eq′ → Y≢X (fin-suc-injective eq′))
        (lift-generator-fresh eq Y∉R) Y∉B)
  conv↑-absent-post (Conv.⊢↑-id-var X∈ X≢Z) Y≢X Y∉R Y∉Z = Y∉Z
  conv↑-absent-post (Conv.⊢↑-id-base X∈) Y≢X Y∉R Y∉ι = Y∉ι
  conv↑-absent-post (Conv.⊢↑-id-star X∈) Y≢X Y∉R Y∉★ = Y∉★

  conv↓-absent-pre : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {R A B : Ty Δ} {c : Conv↓ Δ A B}
    → Σ Conv.⊢↓[ X ⦂ R ] c
    → Y ≢ X
    → Y ∉ᵗ R
    → Y ∉ᵗ A
      -------
    → Y ∉ᵗ B
  conv↓-absent-pre (Conv.⊢↓-seal X∈) Y≢X Y∉R Y∉R′ =
    ∉-var (≢→≢ᶠ Y≢X)
  conv↓-absent-pre (Conv.⊢↓-⇒ c⊢ d⊢) Y≢X Y∉R
      (∉-fun Y∉A Y∉B) =
    ∉-fun (conv↑-absent-post c⊢ Y≢X Y∉R Y∉A)
      (conv↓-absent-pre d⊢ Y≢X Y∉R Y∉B)
  conv↓-absent-pre (Conv.⊢↓-∀ eq c⊢) Y≢X Y∉R (∉-all Y∉A) =
    ∉-all
      (conv↓-absent-pre c⊢
        (λ eq′ → Y≢X (fin-suc-injective eq′))
        (lift-generator-fresh eq Y∉R) Y∉A)
  conv↓-absent-pre (Conv.⊢↓-id-var X∈ X≢Z) Y≢X Y∉R Y∉Z = Y∉Z
  conv↓-absent-pre (Conv.⊢↓-id-base X∈) Y≢X Y∉R Y∉ι = Y∉ι
  conv↓-absent-pre (Conv.⊢↓-id-star X∈) Y≢X Y∉R Y∉★ = Y∉★

  conv↓-absent-post : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {R A B : Ty Δ} {c : Conv↓ Δ A B}
    → Σ Conv.⊢↓[ X ⦂ R ] c
    → Y ≢ X
    → Y ∉ᵗ R
    → Y ∉ᵗ B
      -------
    → Y ∉ᵗ A
  conv↓-absent-post (Conv.⊢↓-seal X∈) Y≢X Y∉R Y∉X = Y∉R
  conv↓-absent-post (Conv.⊢↓-⇒ c⊢ d⊢) Y≢X Y∉R
      (∉-fun Y∉A′ Y∉B′) =
    ∉-fun (conv↑-absent-pre c⊢ Y≢X Y∉R Y∉A′)
      (conv↓-absent-post d⊢ Y≢X Y∉R Y∉B′)
  conv↓-absent-post (Conv.⊢↓-∀ eq c⊢) Y≢X Y∉R (∉-all Y∉B) =
    ∉-all
      (conv↓-absent-post c⊢
        (λ eq′ → Y≢X (fin-suc-injective eq′))
        (lift-generator-fresh eq Y∉R) Y∉B)
  conv↓-absent-post (Conv.⊢↓-id-var X∈ X≢Z) Y≢X Y∉R Y∉Z = Y∉Z
  conv↓-absent-post (Conv.⊢↓-id-base X∈) Y≢X Y∉R Y∉ι = Y∉ι
  conv↓-absent-post (Conv.⊢↓-id-star X∈) Y≢X Y∉R Y∉★ = Y∉★

------------------------------------------------------------------------
-- Corollaries for the universal binder
------------------------------------------------------------------------

zero-pivot-fresh : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R : Ty (Nat.suc Δ)}
  → store-lift Σ ∋ Fin.suc X ⦂ R
    -----------------------------
  → Fin.zero ∉ᵗ R
zero-pivot-fresh (S-lift∋ X∈ refl) = zero-absent-shift _

conv↑-zero-pre : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R A B : Ty (Nat.suc Δ)} {c : Conv↑ (Nat.suc Δ) A B}
  → store-lift Σ Conv.⊢↑[ Fin.suc X ⦂ R ] c
  → Fin.zero ∈ᵗ A
    --------------
  → Fin.zero ∈ᵗ B
conv↑-zero-pre c⊢ =
  conv↑-occurs-pre c⊢ (λ ())
    (zero-pivot-fresh (conv↑-generator∈ c⊢))

conv↑-zero-post : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R A B : Ty (Nat.suc Δ)} {c : Conv↑ (Nat.suc Δ) A B}
  → store-lift Σ Conv.⊢↑[ Fin.suc X ⦂ R ] c
  → Fin.zero ∈ᵗ B
    --------------
  → Fin.zero ∈ᵗ A
conv↑-zero-post c⊢ =
  conv↑-occurs-post c⊢ (λ ())
    (zero-pivot-fresh (conv↑-generator∈ c⊢))

conv↓-zero-pre : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R A B : Ty (Nat.suc Δ)} {c : Conv↓ (Nat.suc Δ) A B}
  → store-lift Σ Conv.⊢↓[ Fin.suc X ⦂ R ] c
  → Fin.zero ∈ᵗ A
    --------------
  → Fin.zero ∈ᵗ B
conv↓-zero-pre c⊢ =
  conv↓-occurs-pre c⊢ (λ ())
    (zero-pivot-fresh (conv↓-generator∈ c⊢))

conv↓-zero-post : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R A B : Ty (Nat.suc Δ)} {c : Conv↓ (Nat.suc Δ) A B}
  → store-lift Σ Conv.⊢↓[ Fin.suc X ⦂ R ] c
  → Fin.zero ∈ᵗ B
    --------------
  → Fin.zero ∈ᵗ A
conv↓-zero-post c⊢ =
  conv↓-occurs-post c⊢ (λ ())
    (zero-pivot-fresh (conv↓-generator∈ c⊢))

------------------------------------------------------------------------
-- Non-variable transport away from the bound variable
------------------------------------------------------------------------

conv↑-nonvar-pre-zero : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R A B : Ty (Nat.suc Δ)} {c : Conv↑ (Nat.suc Δ) A B}
  → store-lift Σ Conv.⊢↑[ Fin.suc X ⦂ R ] c
  → NonVar B
  → Fin.zero ∈ᵗ A
    ----------------
  → NonVar A
conv↑-nonvar-pre-zero (Conv.⊢↑-unseal X∈) Bnv ()
conv↑-nonvar-pre-zero (Conv.⊢↑-⇒ c⊢ d⊢) Bnv zero∈A = nonvar-fun
conv↑-nonvar-pre-zero (Conv.⊢↑-∀ eq c⊢) Bnv zero∈A = nonvar-all
conv↑-nonvar-pre-zero (Conv.⊢↑-id-var X∈ X≢Y) () zero∈A
conv↑-nonvar-pre-zero (Conv.⊢↑-id-base X∈) Bnv ()
conv↑-nonvar-pre-zero (Conv.⊢↑-id-star X∈) Bnv ()

conv↑-nonvar-post-zero : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R A B : Ty (Nat.suc Δ)} {c : Conv↑ (Nat.suc Δ) A B}
  → store-lift Σ Conv.⊢↑[ Fin.suc X ⦂ R ] c
  → NonVar A
  → Fin.zero ∈ᵗ B
    ----------------
  → NonVar B
conv↑-nonvar-post-zero (Conv.⊢↑-unseal X∈) () zero∈B
conv↑-nonvar-post-zero (Conv.⊢↑-⇒ c⊢ d⊢) Anv zero∈B = nonvar-fun
conv↑-nonvar-post-zero (Conv.⊢↑-∀ eq c⊢) Anv zero∈B = nonvar-all
conv↑-nonvar-post-zero (Conv.⊢↑-id-var X∈ X≢Y) () zero∈B
conv↑-nonvar-post-zero (Conv.⊢↑-id-base X∈) Anv ()
conv↑-nonvar-post-zero (Conv.⊢↑-id-star X∈) Anv ()

conv↓-nonvar-pre-zero : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R A B : Ty (Nat.suc Δ)} {c : Conv↓ (Nat.suc Δ) A B}
  → store-lift Σ Conv.⊢↓[ Fin.suc X ⦂ R ] c
  → NonVar B
  → Fin.zero ∈ᵗ A
    ----------------
  → NonVar A
conv↓-nonvar-pre-zero (Conv.⊢↓-seal X∈) () zero∈A
conv↓-nonvar-pre-zero (Conv.⊢↓-⇒ c⊢ d⊢) Bnv zero∈A = nonvar-fun
conv↓-nonvar-pre-zero (Conv.⊢↓-∀ eq c⊢) Bnv zero∈A = nonvar-all
conv↓-nonvar-pre-zero (Conv.⊢↓-id-var X∈ X≢Y) () zero∈A
conv↓-nonvar-pre-zero (Conv.⊢↓-id-base X∈) Bnv ()
conv↓-nonvar-pre-zero (Conv.⊢↓-id-star X∈) Bnv ()

conv↓-nonvar-post-zero : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R A B : Ty (Nat.suc Δ)} {c : Conv↓ (Nat.suc Δ) A B}
  → store-lift Σ Conv.⊢↓[ Fin.suc X ⦂ R ] c
  → NonVar A
  → Fin.zero ∈ᵗ B
    ----------------
  → NonVar B
conv↓-nonvar-post-zero (Conv.⊢↓-seal X∈) Anv ()
conv↓-nonvar-post-zero (Conv.⊢↓-⇒ c⊢ d⊢) Anv zero∈B = nonvar-fun
conv↓-nonvar-post-zero (Conv.⊢↓-∀ eq c⊢) Anv zero∈B = nonvar-all
conv↓-nonvar-post-zero (Conv.⊢↓-id-var X∈ X≢Y) () zero∈B
conv↓-nonvar-post-zero (Conv.⊢↓-id-base X∈) Anv ()
conv↓-nonvar-post-zero (Conv.⊢↓-id-star X∈) Anv ()
