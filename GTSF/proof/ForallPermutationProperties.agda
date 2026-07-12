module proof.ForallPermutationProperties where

-- File Charter:
--   * Provides structural introduction and congruence lemmas for quotiented
--     type imprecision.
--   * Provides ordinary imprecision composition with an `idᵢ` derivation on
--     the right, as needed when promoting a raw MLB candidate.
--   * Contains no selector-specific assumptions.

open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; trans)

open import Types
open import ForallPermutation
open import Imprecision using (idᵢ)
open import ImprecisionWf
open import proof.CastImprecision using
  ( ComposeRightCtx
  ; bound-empty
  ; ⊑-trans-compose-right
  )
open import proof.ImprecisionProperties using
  (idᵢ-no-star; idᵢ-var-identity)
open import proof.TypeProperties using
  ( rename-cong; renameᵗ-compose; renameᵗ-id
  ; renameᵗ-preserves-WfTy
  )

------------------------------------------------------------------------
-- Adjacent-binder renaming
------------------------------------------------------------------------

swap01-involutive : ∀ X → swap01ᵗ (swap01ᵗ X) ≡ X
swap01-involutive zero = refl
swap01-involutive (suc zero) = refl
swap01-involutive (suc (suc X)) = refl

ext-swap01-involutive :
  ∀ X → extᵗ swap01ᵗ (extᵗ swap01ᵗ X) ≡ X
ext-swap01-involutive zero = refl
ext-swap01-involutive (suc X) = cong suc (swap01-involutive X)

renameᵗ-swap01-involutive :
  ∀ A → renameᵗ swap01ᵗ (renameᵗ swap01ᵗ A) ≡ A
renameᵗ-swap01-involutive A =
  trans
    (renameᵗ-compose swap01ᵗ swap01ᵗ A)
    (trans (rename-cong swap01-involutive A) (renameᵗ-id A))

renameᵗ-ext-swap01-involutive :
  ∀ A →
  renameᵗ (extᵗ swap01ᵗ) (renameᵗ (extᵗ swap01ᵗ) A) ≡ A
renameᵗ-ext-swap01-involutive A =
  trans
    (renameᵗ-compose (extᵗ swap01ᵗ) (extᵗ swap01ᵗ) A)
    (trans (rename-cong ext-swap01-involutive A) (renameᵗ-id A))

swap01-pres-< :
  ∀ {Δ X} →
  X < suc (suc Δ) →
  swap01ᵗ X < suc (suc Δ)
swap01-pres-< {X = zero} z<s = s<s z<s
swap01-pres-< {X = suc zero} (s<s z<s) = z<s
swap01-pres-< {X = suc (suc X)} (s<s (s<s X<Δ)) =
  s<s (s<s X<Δ)

swap01-preserves-WfTy :
  ∀ {Δ A} →
  WfTy (suc (suc Δ)) A →
  WfTy (suc (suc Δ)) (renameᵗ swap01ᵗ A)
swap01-preserves-WfTy hA = renameᵗ-preserves-WfTy hA swap01-pres-<

≈∀-double-swap :
  ∀ {A B} →
  renameᵗ swap01ᵗ A ≈∀ B →
  `∀ (`∀ A) ≈∀ `∀ (`∀ B)
≈∀-double-swap Aˢ≈B =
  ≈∀-trans ≈∀-swap (≈∀-∀ (≈∀-∀ Aˢ≈B))

≈∀-double-swap-sym :
  ∀ {A B} →
  A ≈∀ renameᵗ swap01ᵗ B →
  `∀ (`∀ A) ≈∀ `∀ (`∀ B)
≈∀-double-swap-sym A≈Bˢ =
  ≈∀-trans
    (≈∀-∀ (≈∀-∀ A≈Bˢ))
    (≈∀-sym ≈∀-swap)

------------------------------------------------------------------------
-- Ordinary composition with identity imprecision on the right
------------------------------------------------------------------------

compose-right-idᵢ :
  ∀ Δ Φ →
  ComposeRightCtx Δ Φ (idᵢ Δ) Φ
compose-right-idᵢ Δ Φ .ComposeRightCtx.compʳ-var-var x∈ y∈ =
  subst (λ Z → (_ ˣ⊑ˣ Z) ∈ Φ) (idᵢ-var-identity y∈) x∈
compose-right-idᵢ Δ Φ .ComposeRightCtx.compʳ-var-star x∈ Y<Δ y★∈ =
  ⊥-elim (idᵢ-no-star y★∈)
compose-right-idᵢ Δ Φ .ComposeRightCtx.compʳ-star x★∈ = x★∈

⊑-trans-right-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A B C} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  idᵢ Δᴿ ∣ Δᴿ ⊢ B ⊑ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ
⊑-trans-right-idᵢ {Φ = Φ} {Δᴿ = Δᴿ} A⊑B B⊑C =
  ⊑-trans-compose-right
    (compose-right-idᵢ Δᴿ Φ)
    (bound-empty {Φ = Φ})
    A⊑B
    B⊑C

------------------------------------------------------------------------
-- Quotient introduction and congruence
------------------------------------------------------------------------

⊑→⊑ᵖ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ᵖ B ⊣ Δᴿ
⊑→⊑ᵖ A⊑B = quotientᵖ ≈∀-refl A⊑B ≈∀-refl

⊑ᵖ-⇒ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′} →
  Φ ∣ Δᴸ ⊢ A ⊑ᵖ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ
⊑ᵖ-⇒ (quotientᵖ A≈C C⊑C′ C′≈A′)
      (quotientᵖ B≈D D⊑D′ D′≈B′) =
  quotientᵖ
    (≈∀-⇒ A≈C B≈D)
    (C⊑C′ ↦ D⊑D′)
    (≈∀-⇒ C′≈A′ D′≈B′)

⊑ᵖ-∀ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
    ⊢ A ⊑ᵖ B ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ᵖ `∀ B ⊣ Δᴿ
⊑ᵖ-∀ (quotientᵖ A≈C C⊑D D≈B) =
  quotientᵖ (≈∀-∀ A≈C) (∀ⁱ C⊑D) (≈∀-∀ D≈B)
