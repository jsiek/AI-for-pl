module proof.ForallPermutationProperties where

-- File Charter:
--   * Provides structural introduction and congruence lemmas for quotiented
--     type imprecision.
--   * Provides ordinary imprecision composition with an `idᵢ` derivation on
--     the right, as needed when promoting a raw MLB candidate.
--   * Contains no selector-specific assumptions.

open import Data.Empty using (⊥-elim)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; ∃-syntax)
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

------------------------------------------------------------------------
-- Outer-forall shape is invariant under permutation equivalence
------------------------------------------------------------------------

mutual
  ≈∀-preserves-all-shape :
    ∀ {A B} →
    A ≈∀ B →
    ∃[ C ] A ≡ `∀ C →
    ∃[ D ] B ≡ `∀ D
  ≈∀-preserves-all-shape ≈∀-refl allA = allA
  ≈∀-preserves-all-shape (≈∀-sym A≈B) allA =
    ≈∀-reflects-all-shape A≈B allA
  ≈∀-preserves-all-shape (≈∀-trans A≈B B≈C) allA =
    ≈∀-preserves-all-shape B≈C
      (≈∀-preserves-all-shape A≈B allA)
  ≈∀-preserves-all-shape (≈∀-⇒ A≈A′ B≈B′) (C , ())
  ≈∀-preserves-all-shape (≈∀-∀ {B = B} A≈B) allA =
    B , refl
  ≈∀-preserves-all-shape (≈∀-swap {A = A}) allA =
    `∀ (renameᵗ swap01ᵗ A) , refl

  ≈∀-reflects-all-shape :
    ∀ {A B} →
    A ≈∀ B →
    ∃[ D ] B ≡ `∀ D →
    ∃[ C ] A ≡ `∀ C
  ≈∀-reflects-all-shape ≈∀-refl allB = allB
  ≈∀-reflects-all-shape (≈∀-sym A≈B) allB =
    ≈∀-preserves-all-shape A≈B allB
  ≈∀-reflects-all-shape (≈∀-trans A≈B B≈C) allC =
    ≈∀-reflects-all-shape A≈B
      (≈∀-reflects-all-shape B≈C allC)
  ≈∀-reflects-all-shape (≈∀-⇒ A≈A′ B≈B′) (D , ())
  ≈∀-reflects-all-shape (≈∀-∀ {A = A} A≈B) allB =
    A , refl
  ≈∀-reflects-all-shape (≈∀-swap {A = A}) allB =
    `∀ A , refl

≈∀-all-right :
  ∀ {A B} →
  `∀ A ≈∀ B →
  ∃[ C ] B ≡ `∀ C
≈∀-all-right {A = A} A≈B =
  ≈∀-preserves-all-shape A≈B (A , refl)

≈∀-all-left :
  ∀ {A B} →
  A ≈∀ `∀ B →
  ∃[ C ] A ≡ `∀ C
≈∀-all-left {B = B} A≈B =
  ≈∀-reflects-all-shape A≈B (B , refl)

⊑ᵖ-all-representatives :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ᵖ `∀ B ⊣ Δᴿ →
  ∃[ C ] ∃[ D ]
    ((`∀ A ≈∀ `∀ C) ×
     (Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ D ⊣ Δᴿ) ×
     (`∀ D ≈∀ `∀ B))
⊑ᵖ-all-representatives
    (quotientᵖ A≈A′ A′⊑B′ B′≈B)
    with ≈∀-all-right A≈A′ | ≈∀-all-left B′≈B
⊑ᵖ-all-representatives
    (quotientᵖ A≈A′ A′⊑B′ B′≈B)
    | C , refl | D , refl =
  C , D , A≈A′ , A′⊑B′ , B′≈B

data AllImprecisionView
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {A B : Ty} :
    (Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ B ⊣ Δᴿ) → Set where
  all-paired :
    (p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
      ⊢ A ⊑ B ⊣ suc Δᴿ) →
    AllImprecisionView (∀ⁱ p)

  all-source :
    (occ : occurs zero A ≡ true) →
    (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ
      ⊢ A ⊑ `∀ B ⊣ Δᴿ) →
    AllImprecisionView (ν occ p)

all-imprecision-view :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ B ⊣ Δᴿ) →
  AllImprecisionView p
all-imprecision-view (∀ⁱ p) = all-paired p
all-imprecision-view (ν occ p) = all-source occ p

⊑ᵖ-all-view :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ᵖ `∀ B ⊣ Δᴿ →
  ∃[ C ] ∃[ D ]
    ((`∀ A ≈∀ `∀ C) ×
     ∃[ p ]
       (AllImprecisionView p × (`∀ D ≈∀ `∀ B)))
⊑ᵖ-all-view (quotientᵖ A≈A′ A′⊑B′ B′≈B)
    with ≈∀-all-right A≈A′ | ≈∀-all-left B′≈B
⊑ᵖ-all-view (quotientᵖ A≈A′ A′⊑B′ B′≈B)
    | C , refl | D , refl =
  C , D , A≈A′ , A′⊑B′ ,
    all-imprecision-view A′⊑B′ , B′≈B

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
