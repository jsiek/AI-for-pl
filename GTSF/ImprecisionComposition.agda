module ImprecisionComposition where

-- File Charter:
--   * Defines the proof-irrelevant structural shape of well-formed type
--     imprecision and its composition relation.
--   * Records the complete polymorphic shape of composition while ignoring
--     assumption-membership, bound, non-vacuity, and safety witnesses.
--   * Relates shapes across proof-relevant source-endpoint `∀` permutations.
--   * Defines quotient-boundary squares through the stored representatives.
--   * Erases ordinary imprecision proofs.
--   * Exposes structural inversion for composition with the star identity.
--   * Contains no cast typing, term imprecision, store invariant, or
--     simulation proof.

open import Agda.Builtin.Equality using (_≡_; refl)
open import ForallPermutation using
  ( _≈∀_
  ; ≈∀-refl
  ; ≈∀-sym
  ; ≈∀-trans
  ; ≈∀-⇒
  ; ≈∀-∀
  ; ≈∀-swap
  ; _∣_⊢_⊑ᵖ_⊣_
  ; quotientᵖ
  )
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_
  ; id★
  ; idˣ
  ; idι
  ; _↦_
  ; ∀ⁱ_
  ; tag_
  ; tag_⇛_
  ; tagˣ
  ; ν
  )


data ImprecisionShape : Set where
  id★ˢ : ImprecisionShape
  idˣˢ : ImprecisionShape
  idιˢ : ImprecisionShape
  _↦ˢ_ : ImprecisionShape → ImprecisionShape → ImprecisionShape
  ∀ˢ_ : ImprecisionShape → ImprecisionShape
  tagιˢ : ImprecisionShape
  tag_⇛ˢ_ : ImprecisionShape → ImprecisionShape → ImprecisionShape
  tagˣˢ : ImprecisionShape
  νˢ_ : ImprecisionShape → ImprecisionShape


infix 4 _⊢_≈∀ˢ_

data _⊢_≈∀ˢ_ :
    ∀ {A B} →
    A ≈∀ B →
    ImprecisionShape →
    ImprecisionShape →
    Set where

  source-perm-refl :
    ∀ {A s} →
    ≈∀-refl {A = A} ⊢ s ≈∀ˢ s

  source-perm-sym :
    ∀ {A B s s′} {A≈B : A ≈∀ B} →
    A≈B ⊢ s ≈∀ˢ s′ →
    ≈∀-sym A≈B ⊢ s′ ≈∀ˢ s

  source-perm-trans :
    ∀ {A B C s s′ s″}
      {A≈B : A ≈∀ B} {B≈C : B ≈∀ C} →
    A≈B ⊢ s ≈∀ˢ s′ →
    B≈C ⊢ s′ ≈∀ˢ s″ →
    ≈∀-trans A≈B B≈C ⊢ s ≈∀ˢ s″

  source-perm-↦ :
    ∀ {A A′ B B′ p p′ q q′}
      {A≈A′ : A ≈∀ A′} {B≈B′ : B ≈∀ B′} →
    A≈A′ ⊢ p ≈∀ˢ p′ →
    B≈B′ ⊢ q ≈∀ˢ q′ →
    ≈∀-⇒ A≈A′ B≈B′ ⊢
      (p ↦ˢ q) ≈∀ˢ (p′ ↦ˢ q′)

  source-perm-tag-⇛ :
    ∀ {A A′ B B′ p p′ q q′}
      {A≈A′ : A ≈∀ A′} {B≈B′ : B ≈∀ B′} →
    A≈A′ ⊢ p ≈∀ˢ p′ →
    B≈B′ ⊢ q ≈∀ˢ q′ →
    ≈∀-⇒ A≈A′ B≈B′ ⊢
      (tag p ⇛ˢ q) ≈∀ˢ (tag p′ ⇛ˢ q′)

  source-perm-∀ :
    ∀ {A B p p′} {A≈B : A ≈∀ B} →
    A≈B ⊢ p ≈∀ˢ p′ →
    ≈∀-∀ A≈B ⊢ ∀ˢ p ≈∀ˢ ∀ˢ p′

  source-perm-ν :
    ∀ {A B p p′} {A≈B : A ≈∀ B} →
    A≈B ⊢ p ≈∀ˢ p′ →
    ≈∀-∀ A≈B ⊢ νˢ p ≈∀ˢ νˢ p′

  source-swap-∀∀ :
    ∀ {A s} →
    ≈∀-swap {A = A} ⊢
      ∀ˢ (∀ˢ s) ≈∀ˢ ∀ˢ (∀ˢ s)

  source-swap-∀ν :
    ∀ {A s} →
    ≈∀-swap {A = A} ⊢
      ∀ˢ (νˢ s) ≈∀ˢ νˢ (∀ˢ s)

  source-swap-ν∀ :
    ∀ {A s} →
    ≈∀-swap {A = A} ⊢
      νˢ (∀ˢ s) ≈∀ˢ ∀ˢ (νˢ s)

  source-swap-νν :
    ∀ {A s} →
    ≈∀-swap {A = A} ⊢
      νˢ (νˢ s) ≈∀ˢ νˢ (νˢ s)


⌊_⌋ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  ImprecisionShape
⌊ id★ ⌋ = id★ˢ
⌊ idˣ x∈ X<Δᴸ Y<Δᴿ ⌋ = idˣˢ
⌊ idι ⌋ = idιˢ
⌊ p ↦ q ⌋ = ⌊ p ⌋ ↦ˢ ⌊ q ⌋
⌊ ∀ⁱ p ⌋ = ∀ˢ ⌊ p ⌋
⌊ tag ι ⌋ = tagιˢ
⌊ tag p ⇛ q ⌋ = tag ⌊ p ⌋ ⇛ˢ ⌊ q ⌋
⌊ tagˣ x★∈ X<Δᴸ ⌋ = tagˣˢ
⌊ ν safe occ p ⌋ = νˢ ⌊ p ⌋


νˢ-injective :
  ∀ {p q : ImprecisionShape} →
  νˢ p ≡ νˢ q →
  p ≡ q
νˢ-injective refl = refl


infix 4 _；_≋_

data _；_≋_ :
    ImprecisionShape →
    ImprecisionShape →
    ImprecisionShape →
    Set where

  comp-id★ :
    id★ˢ ； id★ˢ ≋ id★ˢ

  comp-idˣ-idˣ :
    idˣˢ ； idˣˢ ≋ idˣˢ

  comp-idˣ-tagˣ :
    idˣˢ ； tagˣˢ ≋ tagˣˢ

  comp-idι-idι :
    idιˢ ； idιˢ ≋ idιˢ

  comp-idι-tag :
    idιˢ ； tagιˢ ≋ tagιˢ

  comp-↦-↦ :
    ∀ {p₁ p₂ q₁ q₂ r₁ r₂} →
    p₁ ； q₁ ≋ r₁ →
    p₂ ； q₂ ≋ r₂ →
    (p₁ ↦ˢ p₂) ； (q₁ ↦ˢ q₂) ≋ (r₁ ↦ˢ r₂)

  comp-↦-tag :
    ∀ {p₁ p₂ q₁ q₂ r₁ r₂} →
    p₁ ； q₁ ≋ r₁ →
    p₂ ； q₂ ≋ r₂ →
    (p₁ ↦ˢ p₂) ； (tag q₁ ⇛ˢ q₂) ≋ (tag r₁ ⇛ˢ r₂)

  comp-∀-∀ :
    ∀ {p q r} →
    p ； q ≋ r →
    ∀ˢ p ； ∀ˢ q ≋ ∀ˢ r

  comp-∀-ν :
    ∀ {p q r} →
    p ； q ≋ r →
    ∀ˢ p ； νˢ q ≋ νˢ r

  comp-tag-id★ :
    tagιˢ ； id★ˢ ≋ tagιˢ

  comp-tag-⇛-id★ :
    ∀ {p₁ p₂ r₁ r₂} →
    p₁ ； id★ˢ ≋ r₁ →
    p₂ ； id★ˢ ≋ r₂ →
    (tag p₁ ⇛ˢ p₂) ； id★ˢ ≋ (tag r₁ ⇛ˢ r₂)

  comp-tagˣ-id★ :
    tagˣˢ ； id★ˢ ≋ tagˣˢ

  comp-ν :
    ∀ {p q r} →
    p ； q ≋ r →
    νˢ p ； q ≋ νˢ r


infix 4 _；⌊_⌋≋ᵖ_；_

data _；⌊_⌋≋ᵖ_；_ :
    ImprecisionShape →
    ∀ {Φ Δᴸ Δᴿ A B} →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
    ∀ {C D} →
    Φ ∣ Δᴸ ⊢ C ⊑ᵖ D ⊣ Δᴿ →
    ImprecisionShape →
    Set where

  quotient-boundary-square :
    ∀ {Φ Δᴸ Δᴿ A B C C′ D′ D}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {src : C ≈∀ C′}
      {middle : Φ ∣ Δᴸ ⊢ C′ ⊑ D′ ⊣ Δᴿ}
      {tgt : D′ ≈∀ D}
      {s s′ t t′ r} →
    src ⊢ s ≈∀ˢ t →
    t ； ⌊ p ⌋ ≋ r →
    tgt ⊢ t′ ≈∀ˢ s′ →
    ⌊ middle ⌋ ； t′ ≋ r →
    s ；⌊ p ⌋≋ᵖ (quotientᵖ src middle tgt) ； s′


compose-right-id★ :
  ∀ {p r} →
  p ； id★ˢ ≋ r →
  p ≡ r
compose-right-id★ comp-id★ = refl
compose-right-id★ comp-tag-id★ = refl
compose-right-id★
    (comp-tag-⇛-id★ comp₁ comp₂)
    with compose-right-id★ comp₁
       | compose-right-id★ comp₂
compose-right-id★
    (comp-tag-⇛-id★ comp₁ comp₂)
    | refl | refl = refl
compose-right-id★ comp-tagˣ-id★ = refl
compose-right-id★ (comp-ν comp)
    with compose-right-id★ comp
compose-right-id★ (comp-ν comp) | refl = refl
