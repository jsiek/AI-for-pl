module proof.Quotient.NuImprecisionQuotientArrowComponents where

-- File Charter:
--   * Decomposes forall-permutation equivalence and quotient precision at
--     arrow endpoints.
--   * Decomposes an arrow-shaped quotient-boundary square into its domain and
--     codomain quotient components and component squares.
--   * Isolates this DGG-specific inversion from the broadly imported general
--     forall-permutation properties module.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using
  (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import ForallPermutation using
  ( _≈∀_
  ; _∣_⊢_⊑ᵖ_⊣_
  ; quotientᵖ
  ; ≈∀-refl
  ; ≈∀-sym
  ; ≈∀-trans
  ; ≈∀-⇒
  ; ≈∀-arrow-left
  ; ≈∀-arrow-right
  ; ≈∀-arrow-components
  ; ⊑ᵖ-arrow-components
  )
open import ImprecisionComposition using
  ( ImprecisionShape
  ; _↦ˢ_
  ; ⌊_⌋
  ; _；_≋_
  ; comp-↦-↦
  ; _⊢_≈∀ˢ_
  ; source-perm-refl
  ; source-perm-sym
  ; source-perm-trans
  ; source-perm-↦
  ; _；⌊_⌋≋ᵖ_；_
  ; quotient-boundary-square
  )
open import ImprecisionWf using (_∣_⊢_⊑_⊣_; _↦_)
open import Types using (Ty; _⇒_)
------------------------------------------------------------------------
-- Arrow-shaped quotient-boundary squares
------------------------------------------------------------------------

mutual
  source-perm-arrow-left-components :
    ∀ {A A′ B B′ : Ty} {p q r : ImprecisionShape}
      {equivalence : A ⇒ B ≈∀ A′ ⇒ B′} →
    equivalence ⊢ (p ↦ˢ q) ≈∀ˢ r →
    ∃[ p′ ] ∃[ q′ ]
      (r ≡ p′ ↦ˢ q′) ×
      (proj₁ (≈∀-arrow-components equivalence) ⊢ p ≈∀ˢ p′) ×
      (proj₂ (≈∀-arrow-components equivalence) ⊢ q ≈∀ˢ q′)

  source-perm-arrow-right-components :
    ∀ {A A′ B B′ : Ty} {p′ q′ r : ImprecisionShape}
      {equivalence : A ⇒ B ≈∀ A′ ⇒ B′} →
    equivalence ⊢ r ≈∀ˢ (p′ ↦ˢ q′) →
    ∃[ p ] ∃[ q ]
      (r ≡ p ↦ˢ q) ×
      (proj₁ (≈∀-arrow-components equivalence) ⊢ p ≈∀ˢ p′) ×
      (proj₂ (≈∀-arrow-components equivalence) ⊢ q ≈∀ˢ q′)

  source-perm-arrow-left-components source-perm-refl =
    _ , _ , refl , source-perm-refl , source-perm-refl
  source-perm-arrow-left-components
      (source-perm-sym permutation)
      with source-perm-arrow-right-components permutation
  source-perm-arrow-left-components
      (source-perm-sym permutation)
      | p′ , q′ , refl , domain , codomain =
    p′ , q′ , refl ,
    source-perm-sym domain , source-perm-sym codomain
  source-perm-arrow-left-components
      (source-perm-trans
        {A≈B = left-equivalence}
        {B≈C = right-equivalence}
        left right)
      with ≈∀-arrow-right left-equivalence
  source-perm-arrow-left-components
      (source-perm-trans
        {A≈B = left-equivalence}
        {B≈C = right-equivalence}
        left right)
      | C , D , refl
      with source-perm-arrow-left-components left
  source-perm-arrow-left-components
      (source-perm-trans
        {A≈B = left-equivalence}
        {B≈C = right-equivalence}
        left right)
      | C , D , refl
      | pᶜ , qᶜ , refl , left-domain , left-codomain
      with source-perm-arrow-left-components right
  source-perm-arrow-left-components
      (source-perm-trans
        {A≈B = left-equivalence}
        {B≈C = right-equivalence}
        left right)
      | C , D , refl
      | pᶜ , qᶜ , refl , left-domain , left-codomain
      | p′ , q′ , refl , right-domain , right-codomain =
    p′ , q′ , refl ,
    source-perm-trans left-domain right-domain ,
    source-perm-trans left-codomain right-codomain
  source-perm-arrow-left-components
      (source-perm-↦ domain codomain) =
    _ , _ , refl , domain , codomain

  source-perm-arrow-right-components source-perm-refl =
    _ , _ , refl , source-perm-refl , source-perm-refl
  source-perm-arrow-right-components
      (source-perm-sym permutation)
      with source-perm-arrow-left-components permutation
  source-perm-arrow-right-components
      (source-perm-sym permutation)
      | p , q , refl , domain , codomain =
    p , q , refl ,
    source-perm-sym domain , source-perm-sym codomain
  source-perm-arrow-right-components
      (source-perm-trans
        {A≈B = left-equivalence}
        {B≈C = right-equivalence}
        left right)
      with ≈∀-arrow-right left-equivalence
  source-perm-arrow-right-components
      (source-perm-trans
        {A≈B = left-equivalence}
        {B≈C = right-equivalence}
        left right)
      | C , D , refl
      with source-perm-arrow-right-components right
  source-perm-arrow-right-components
      (source-perm-trans
        {A≈B = left-equivalence}
        {B≈C = right-equivalence}
        left right)
      | C , D , refl
      | pᶜ , qᶜ , refl , right-domain , right-codomain
      with source-perm-arrow-right-components left
  source-perm-arrow-right-components
      (source-perm-trans
        {A≈B = left-equivalence}
        {B≈C = right-equivalence}
        left right)
      | C , D , refl
      | pᶜ , qᶜ , refl , right-domain , right-codomain
      | p , q , refl , left-domain , left-codomain =
    p , q , refl ,
    source-perm-trans left-domain right-domain ,
    source-perm-trans left-codomain right-codomain
  source-perm-arrow-right-components
      (source-perm-↦ domain codomain) =
    _ , _ , refl , domain , codomain


quotient-boundary-arrow-components :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ D D′}
    {pC : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {qF : Φ ∣ Δᴸ ⊢ C ⇒ D ⊑ᵖ C′ ⇒ D′ ⊣ Δᴿ}
    {sC sB sC′ sB′} →
  (sC ↦ˢ sB) ；⌊ pC ↦ pB ⌋≋ᵖ qF ； (sC′ ↦ˢ sB′) →
  ∃[ qC ] ∃[ qB ]
    (⊑ᵖ-arrow-components qF ≡ (qC , qB)) ×
    (sC ；⌊ pC ⌋≋ᵖ qC ； sC′) ×
    (sB ；⌊ pB ⌋≋ᵖ qB ； sB′)
quotient-boundary-arrow-components
    {qF = quotientᵖ left middle right}
    (quotient-boundary-square
      left-shape left-composition right-shape right-composition)
    with ≈∀-arrow-right left | ≈∀-arrow-left right
quotient-boundary-arrow-components
    {qF = quotientᵖ left middle right}
    (quotient-boundary-square
      left-shape left-composition right-shape right-composition)
    | C , D , refl | C′ , D′ , refl
    with ≈∀-arrow-components left
       | middle
       | ≈∀-arrow-components right
quotient-boundary-arrow-components
    {qF = quotientᵖ left middle right}
    (quotient-boundary-square
      left-shape left-composition right-shape right-composition)
    | C , D , refl | C′ , D′ , refl
    | left-domain , left-codomain
    | middle-domain ↦ middle-codomain
    | right-domain , right-codomain
    with left-composition | right-composition
quotient-boundary-arrow-components
    {qF = quotientᵖ left middle right}
    (quotient-boundary-square
      left-shape left-composition right-shape right-composition)
    | C , D , refl | C′ , D′ , refl
    | left-domain , left-codomain
    | middle-domain ↦ middle-codomain
    | right-domain , right-codomain
    | comp-↦-↦ left-domain-composition left-codomain-composition
    | comp-↦-↦ right-domain-composition right-codomain-composition
    with source-perm-arrow-left-components left-shape
       | source-perm-arrow-right-components right-shape
quotient-boundary-arrow-components
    {qF = quotientᵖ left middle right}
    (quotient-boundary-square
      left-shape left-composition right-shape right-composition)
    | C , D , refl | C′ , D′ , refl
    | left-domain , left-codomain
    | middle-domain ↦ middle-codomain
    | right-domain , right-codomain
    | comp-↦-↦ left-domain-composition left-codomain-composition
    | comp-↦-↦ right-domain-composition right-codomain-composition
    | sCᵐ , sBᵐ , refl , left-domain-shape , left-codomain-shape
    | sC′ᵐ , sB′ᵐ , refl , right-domain-shape , right-codomain-shape =
  quotientᵖ
    (proj₁ (≈∀-arrow-components left))
    middle-domain
    (proj₁ (≈∀-arrow-components right)) ,
  quotientᵖ
    (proj₂ (≈∀-arrow-components left))
    middle-codomain
    (proj₂ (≈∀-arrow-components right)) ,
  refl ,
  quotient-boundary-square
    left-domain-shape
    left-domain-composition
    right-domain-shape
    right-domain-composition ,
  quotient-boundary-square
    left-codomain-shape
    left-codomain-composition
    right-codomain-shape
    right-codomain-composition
