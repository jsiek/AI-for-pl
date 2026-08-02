module proof.Imprecision where

-- File Charter:
--   * Proves that every closed type is less precise than the dynamic type.
--   * Uses occurrence information to choose between structural universal
--     imprecision and instantiation at the dynamic type.
--   * Depends only on Types and Imprecision.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
import Imprecision as I

private

  not-occurs : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
    → X ∉ᵗ A
    → X ∈ᵗ A
    → ⊥
  not-occurs (∉-var X≠Y) var-∈ = X≠Y refl
  not-occurs ∉-base ()
  not-occurs ∉-star ()
  not-occurs (∉-fun X∉A X∉B) (∈-fun-left X∈A) =
    not-occurs X∉A X∈A
  not-occurs (∉-fun X∉A X∉B) (∈-fun-right X∉A′ X∈B) =
    not-occurs X∉B X∈B
  not-occurs (∉-all X∉A) (∈-all X∈A) = not-occurs X∉A X∈A

  dynamic-domain : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    → (∀ X → X ∈ᵗ A ⇒ B → μ X ≡ I.X⊑★)
    → ∀ X → X ∈ᵗ A → μ X ≡ I.X⊑★
  dynamic-domain dynamic X X∈A = dynamic X (∈-fun-left X∈A)

  dynamic-codomain : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    → (∀ X → X ∈ᵗ A ⇒ B → μ X ≡ I.X⊑★)
    → ∀ X → X ∈ᵗ B → μ X ≡ I.X⊑★
  dynamic-codomain {A = A} dynamic X X∈B with occurs? X A
  dynamic-codomain dynamic X X∈B | present X∈A =
    dynamic X (∈-fun-left X∈A)
  dynamic-codomain dynamic X X∈B | absent X∉A =
    dynamic X (∈-fun-right X∉A X∈B)

  dynamic-under-inst : ∀ {Δ} {μ : I.ImpEnv Δ}
      {A : Ty (Nat.suc Δ)}
    → (∀ X → X ∈ᵗ `∀ A → μ X ≡ I.X⊑★)
    → ∀ X → X ∈ᵗ A → I.instᵐ μ X ≡ I.X⊑★
  dynamic-under-inst dynamic zero X∈A = refl
  dynamic-under-inst dynamic (suc X) X∈A =
    dynamic X (∈-all X∈A)

  dynamic-under-ext : ∀ {Δ} {μ : I.ImpEnv Δ}
      {A : Ty (Nat.suc Δ)}
    → (∀ X → X ∈ᵗ `∀ A → μ X ≡ I.X⊑★)
    → zero ∉ᵗ A
    → ∀ X → X ∈ᵗ A → I.extᵐ μ X ≡ I.X⊑★
  dynamic-under-ext dynamic zero∉A zero zero∈A =
    ⊥-elim (not-occurs zero∉A zero∈A)
  dynamic-under-ext dynamic zero∉A (suc X) X∈A =
    dynamic X (∈-all X∈A)

  data Shape : ∀ {Δ} → Ty Δ → Set where
    var-shape : ∀ {Δ} {X : TyVar Δ} → Shape (＇ X)
    base-shape : ∀ {Δ ι} → Shape (‵_ {Δ} ι)
    star-shape : ∀ {Δ} → Shape (★ {Δ})
    fun-shape : ∀ {Δ} {A B : Ty Δ}
      → Shape A
      → Shape B
      → Shape (A ⇒ B)
    all-shape : ∀ {Δ} {A : Ty (Nat.suc Δ)}
      → Shape A
      → Shape (`∀ A)

  shape : ∀ {Δ} (A : Ty Δ) → Shape A
  shape (＇ X) = var-shape
  shape (‵ ι) = base-shape
  shape ★ = star-shape
  shape (A ⇒ B) = fun-shape (shape A) (shape B)
  shape (`∀ A) = all-shape (shape A)

  data AllChoice {Δ : TyCtx} : Ty (Nat.suc Δ) → Set where
    bottom-choice : AllChoice (＇ zero)
    inst-choice : ∀ {A}
      → NonVar A
      → zero ∈ᵗ A
      → AllChoice A
    structural-choice : ∀ {A}
      → zero ∉ᵗ A
      → AllChoice A

  all-choice : ∀ {Δ} (A : Ty (Nat.suc Δ)) → AllChoice A
  all-choice (＇ zero) = bottom-choice
  all-choice (＇ (suc X)) = structural-choice (∉-var (λ ()))
  all-choice (‵ ι) = structural-choice ∉-base
  all-choice ★ = structural-choice ∉-star
  all-choice (A ⇒ B) with occurs? zero (A ⇒ B)
  all-choice (A ⇒ B) | present zero∈A⇒B =
    inst-choice nonvar-fun zero∈A⇒B
  all-choice (A ⇒ B) | absent zero∉A⇒B =
    structural-choice zero∉A⇒B
  all-choice (`∀ A) with occurs? zero (`∀ A)
  all-choice (`∀ A) | present zero∈∀A =
    inst-choice nonvar-all zero∈∀A
  all-choice (`∀ A) | absent zero∉∀A = structural-choice zero∉∀A

  imprecise-star-shape : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty Δ}
    → Shape A
    → (∀ X → X ∈ᵗ A → μ X ≡ I.X⊑★)
    → I._⊢_⊑_ μ A ★
  imprecise-star-shape var-shape dynamic =
    I.X⊑★ (dynamic _ var-∈)
  imprecise-star-shape base-shape dynamic = I.ι⊑★
  imprecise-star-shape star-shape dynamic = I.★⊑★
  imprecise-star-shape (fun-shape shape-A shape-B) dynamic =
    I.⇒⊑★ (imprecise-star-shape shape-A (dynamic-domain dynamic))
      (imprecise-star-shape shape-B (dynamic-codomain dynamic))
  imprecise-star-shape (all-shape {A = A} shape-A) dynamic =
    decide (all-choice A)
    where
    decide : AllChoice A → I._⊢_⊑_ _ (`∀ A) ★
    decide bottom-choice = I.bot⊑★
    decide (inst-choice Anv zero∈A) =
      I.∀⊑ Anv zero∈A
        (imprecise-star-shape shape-A
          (dynamic-under-inst dynamic))
    decide (structural-choice zero∉A) =
      I.∀⊑★
        (imprecise-star-shape shape-A
          (dynamic-under-ext dynamic zero∉A))

imprecise-star : ∀ (A : Ty 0) → I._⊑_ A ★
imprecise-star A = imprecise-star-shape (shape A) (\ ())
