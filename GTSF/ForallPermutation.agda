module ForallPermutation where

-- File Charter:
--   * Defines type equivalence modulo permutations of adjacent `∀` binders.
--   * Presents the quotient as a setoid over raw GTSF types.
--   * Defines directed type imprecision on quotient representatives using the
--     context-indexed ordinary imprecision relation from `ImprecisionWf`.
--   * Exposes canonical domain and codomain projections at arrow endpoints.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (0ℓ)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.Bundles using (Setoid)

open import Types
open import Imprecision using (ImpCtx)
import ImprecisionWf as IWF
open IWF using (_↦_)

------------------------------------------------------------------------
-- Permuting adjacent universal binders
------------------------------------------------------------------------

swap01ᵗ : Renameᵗ
swap01ᵗ zero = suc zero
swap01ᵗ (suc zero) = zero
swap01ᵗ (suc (suc X)) = suc (suc X)

infix 4 _≈∀_
data _≈∀_ : Ty → Ty → Set where
  ≈∀-refl : ∀ {A} → A ≈∀ A
  ≈∀-sym : ∀ {A B} → A ≈∀ B → B ≈∀ A
  ≈∀-trans : ∀ {A B C} → A ≈∀ B → B ≈∀ C → A ≈∀ C

  ≈∀-⇒ : ∀ {A A′ B B′} →
    A ≈∀ A′ →
    B ≈∀ B′ →
    (A ⇒ B) ≈∀ (A′ ⇒ B′)

  ≈∀-∀ : ∀ {A B} →
    A ≈∀ B →
    `∀ A ≈∀ `∀ B

  ≈∀-swap : ∀ {A} →
    `∀ (`∀ A) ≈∀ `∀ (`∀ (renameᵗ swap01ᵗ A))

mutual
  ≈∀-arrow-right :
    ∀ {A B C} →
    A ⇒ B ≈∀ C →
    ∃[ A′ ] ∃[ B′ ] C ≡ A′ ⇒ B′
  ≈∀-arrow-right ≈∀-refl = _ , _ , refl
  ≈∀-arrow-right (≈∀-sym C≈A⇒B) =
    ≈∀-arrow-left C≈A⇒B
  ≈∀-arrow-right (≈∀-trans A⇒B≈C C≈D)
      with ≈∀-arrow-right A⇒B≈C
  ≈∀-arrow-right (≈∀-trans A⇒B≈C C≈D)
      | A′ , B′ , refl =
    ≈∀-arrow-right C≈D
  ≈∀-arrow-right
      (≈∀-⇒ {A′ = A′} {B′ = B′} A≈A′ B≈B′) =
    A′ , B′ , refl

  ≈∀-arrow-left :
    ∀ {A B C} →
    C ≈∀ A ⇒ B →
    ∃[ A′ ] ∃[ B′ ] C ≡ A′ ⇒ B′
  ≈∀-arrow-left ≈∀-refl = _ , _ , refl
  ≈∀-arrow-left (≈∀-sym A⇒B≈C) =
    ≈∀-arrow-right A⇒B≈C
  ≈∀-arrow-left (≈∀-trans C≈D D≈A⇒B)
      with ≈∀-arrow-left D≈A⇒B
  ≈∀-arrow-left (≈∀-trans C≈D D≈A⇒B)
      | A′ , B′ , refl =
    ≈∀-arrow-left C≈D
  ≈∀-arrow-left
      (≈∀-⇒ {A = A′} {B = B′} A≈A′ B≈B′) =
    A′ , B′ , refl

≈∀-arrow-components :
  ∀ {A A′ B B′} →
  A ⇒ B ≈∀ A′ ⇒ B′ →
  (A ≈∀ A′) × (B ≈∀ B′)
≈∀-arrow-components ≈∀-refl =
  ≈∀-refl , ≈∀-refl
≈∀-arrow-components (≈∀-sym equivalence)
    with ≈∀-arrow-components equivalence
≈∀-arrow-components (≈∀-sym equivalence)
    | domain , codomain =
  ≈∀-sym domain , ≈∀-sym codomain
≈∀-arrow-components (≈∀-trans left right)
    with ≈∀-arrow-right left
≈∀-arrow-components (≈∀-trans left right)
    | C , D , refl
    with ≈∀-arrow-components left
       | ≈∀-arrow-components right
≈∀-arrow-components (≈∀-trans left right)
    | C , D , refl
    | A≈C , B≈D
    | C≈A′ , D≈B′ =
  ≈∀-trans A≈C C≈A′ , ≈∀-trans B≈D D≈B′
≈∀-arrow-components (≈∀-⇒ domain codomain) =
  domain , codomain

∀-perm-quotient : Setoid 0ℓ 0ℓ
∀-perm-quotient =
  record
    { Carrier = Ty
    ; _≈_ = _≈∀_
    ; isEquivalence =
        record
          { refl = ≈∀-refl
          ; sym = ≈∀-sym
          ; trans = ≈∀-trans
          }
    }

------------------------------------------------------------------------
-- Imprecision on the `∀`-permutation quotient
------------------------------------------------------------------------

infix 4 _∣_⊢_⊑ᵖ_⊣_
data _∣_⊢_⊑ᵖ_⊣_ (Φ : ImpCtx) (Δᴸ : TyCtx) :
    Ty → Ty → TyCtx → Set where
  quotientᵖ : ∀ {A A′ B′ B Δᴿ} →
    A ≈∀ A′ →
    Φ IWF.∣ Δᴸ ⊢ A′ ⊑ B′ ⊣ Δᴿ →
    B′ ≈∀ B →
    Φ ∣ Δᴸ ⊢ A ⊑ᵖ B ⊣ Δᴿ

⊑ᵖ-arrow-components :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′} →
  Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ →
  (Φ ∣ Δᴸ ⊢ A ⊑ᵖ A′ ⊣ Δᴿ) ×
  (Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ)
⊑ᵖ-arrow-components
    (quotientᵖ left middle right)
    with ≈∀-arrow-right left
       | ≈∀-arrow-left right
⊑ᵖ-arrow-components
    (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    with ≈∀-arrow-components left
       | middle
       | ≈∀-arrow-components right
⊑ᵖ-arrow-components
    (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    | A≈C , B≈D
    | domain ↦ codomain
    | C′≈A′ , D′≈B′ =
  quotientᵖ
    (proj₁ (≈∀-arrow-components left))
    domain
    (proj₁ (≈∀-arrow-components right)) ,
  quotientᵖ
    (proj₂ (≈∀-arrow-components left))
    codomain
    (proj₂ (≈∀-arrow-components right))
