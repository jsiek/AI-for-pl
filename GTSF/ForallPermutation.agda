module ForallPermutation where

-- File Charter:
--   * Defines type equivalence modulo permutations of adjacent `∀` binders.
--   * Presents the quotient as a setoid over raw GTSF types.
--   * Defines directed type imprecision on quotient representatives using the
--     context-indexed ordinary imprecision relation from `ImprecisionWf`.

open import Level using (0ℓ)
open import Data.Nat using (zero; suc)
open import Relation.Binary.Bundles using (Setoid)

open import Types
open import Imprecision using (ImpCtx)
import ImprecisionWf as IWF

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
