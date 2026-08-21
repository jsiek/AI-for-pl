{-# OPTIONS --safe #-}

module proof.DGG.ConversionPivotAlignment where

-- File Charter:
--   * Computes the possibly empty structural position of the generator in a
--     generator-indexed reveal or conceal conversion.
--   * Makes paired conversion rules compare pivot positions independently of
--     endpoint variable names and representation types.
--   * Maps the computed position to the legacy catch-up boundary pivot while
--     that boundary API still distinguishes neutral and active wrappers.
--   * Contains no term-imprecision rules, world transport, or compatibility
--     aliases.

open import Types using (Ty; TyCtx; TyVar)
open import Data.Maybe using (Maybe; just; nothing)
open import TyStore using (TyStore)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Conversion as Conv


data GeneratorPosition : Set where
  generator-absent : GeneratorPosition
  generator-here : GeneratorPosition
  generator-⇒-left : GeneratorPosition → GeneratorPosition
  generator-⇒-right : GeneratorPosition → GeneratorPosition
  generator-⇒-both : GeneratorPosition → GeneratorPosition
    → GeneratorPosition
  generator-∀ : GeneratorPosition → GeneratorPosition


joinGeneratorPositions : GeneratorPosition → GeneratorPosition
  → GeneratorPosition
joinGeneratorPositions generator-absent generator-absent = generator-absent
joinGeneratorPositions left generator-absent = generator-⇒-left left
joinGeneratorPositions generator-absent right = generator-⇒-right right
joinGeneratorPositions left right = generator-⇒-both left right

liftGeneratorPosition : GeneratorPosition → GeneratorPosition
liftGeneratorPosition generator-absent = generator-absent
liftGeneratorPosition position = generator-∀ position


generatorBoundaryPivot : ∀ {Delta : TyCtx}
  → TyVar Delta → GeneratorPosition → Maybe (TyVar Delta)
generatorBoundaryPivot X generator-absent = nothing
generatorBoundaryPivot X generator-here = just X
generatorBoundaryPivot X (generator-⇒-left position) = just X
generatorBoundaryPivot X (generator-⇒-right position) = just X
generatorBoundaryPivot X (generator-⇒-both left right) = just X
generatorBoundaryPivot X (generator-∀ position) = just X


mutual
  revealGeneratorPosition : ∀ {Delta : TyCtx} {Sigma : TyStore Delta}
      {X : TyVar Delta} {R A B : Ty Delta}
      {c : Conv.Conv↑ Delta A B}
    → Sigma Conv.⊢↑[ X ⦂ R ] c
    → GeneratorPosition
  revealGeneratorPosition (Conv.⊢↑-unseal member) = generator-here
  revealGeneratorPosition (Conv.⊢↑-⇒ c⊢ d⊢) =
    joinGeneratorPositions (concealGeneratorPosition c⊢)
      (revealGeneratorPosition d⊢)
  revealGeneratorPosition (Conv.⊢↑-∀ eq c⊢) =
    liftGeneratorPosition (revealGeneratorPosition c⊢)
  revealGeneratorPosition (Conv.⊢↑-id-var member X≠Y) =
    generator-absent
  revealGeneratorPosition (Conv.⊢↑-id-base member) = generator-absent
  revealGeneratorPosition (Conv.⊢↑-id-star member) = generator-absent

  concealGeneratorPosition : ∀ {Delta : TyCtx} {Sigma : TyStore Delta}
      {X : TyVar Delta} {R A B : Ty Delta}
      {c : Conv.Conv↓ Delta A B}
    → Sigma Conv.⊢↓[ X ⦂ R ] c
    → GeneratorPosition
  concealGeneratorPosition (Conv.⊢↓-seal member) = generator-here
  concealGeneratorPosition (Conv.⊢↓-⇒ c⊢ d⊢) =
    joinGeneratorPositions (revealGeneratorPosition c⊢)
      (concealGeneratorPosition d⊢)
  concealGeneratorPosition (Conv.⊢↓-∀ eq c⊢) =
    liftGeneratorPosition (concealGeneratorPosition c⊢)
  concealGeneratorPosition (Conv.⊢↓-id-var member X≠Y) =
    generator-absent
  concealGeneratorPosition (Conv.⊢↓-id-base member) =
    generator-absent
  concealGeneratorPosition (Conv.⊢↓-id-star member) =
    generator-absent


revealGeneratorPosition-store-transport : ∀ {Delta : TyCtx}
    {Sigma Sigma′ : TyStore Delta} {X : TyVar Delta} {R A B : Ty Delta}
    {c : Conv.Conv↑ Delta A B}
  → (eq : Sigma ≡ Sigma′)
  → (c⊢ : Sigma Conv.⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition
      (subst (λ Store → Store Conv.⊢↑[ X ⦂ R ] c) eq c⊢)
    ≡ revealGeneratorPosition c⊢
revealGeneratorPosition-store-transport refl c⊢ = refl

concealGeneratorPosition-store-transport : ∀ {Delta : TyCtx}
    {Sigma Sigma′ : TyStore Delta} {X : TyVar Delta} {R A B : Ty Delta}
    {c : Conv.Conv↓ Delta A B}
  → (eq : Sigma ≡ Sigma′)
  → (c⊢ : Sigma Conv.⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition
      (subst (λ Store → Store Conv.⊢↓[ X ⦂ R ] c) eq c⊢)
    ≡ concealGeneratorPosition c⊢
concealGeneratorPosition-store-transport refl c⊢ = refl


mutual
  revealGeneratorPosition-unique : ∀ {Delta : TyCtx}
      {Sigma : TyStore Delta} {X : TyVar Delta} {R A B : Ty Delta}
      {c : Conv.Conv↑ Delta A B}
    → (c⊢ c⊢′ : Sigma Conv.⊢↑[ X ⦂ R ] c)
    → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c⊢′
  revealGeneratorPosition-unique (Conv.⊢↑-unseal member)
      (Conv.⊢↑-unseal member′) =
    refl
  revealGeneratorPosition-unique (Conv.⊢↑-⇒ c⊢ d⊢)
      (Conv.⊢↑-⇒ c⊢′ d⊢′)
    rewrite concealGeneratorPosition-unique c⊢ c⊢′
      | revealGeneratorPosition-unique d⊢ d⊢′ =
    refl
  revealGeneratorPosition-unique (Conv.⊢↑-∀ refl c⊢)
      (Conv.⊢↑-∀ refl c⊢′)
    rewrite revealGeneratorPosition-unique c⊢ c⊢′ =
    refl
  revealGeneratorPosition-unique (Conv.⊢↑-id-var member X≠Y)
      (Conv.⊢↑-id-var member′ X≠Y′) =
    refl
  revealGeneratorPosition-unique (Conv.⊢↑-id-base member)
      (Conv.⊢↑-id-base member′) =
    refl
  revealGeneratorPosition-unique (Conv.⊢↑-id-star member)
      (Conv.⊢↑-id-star member′) =
    refl

  concealGeneratorPosition-unique : ∀ {Delta : TyCtx}
      {Sigma : TyStore Delta} {X : TyVar Delta} {R A B : Ty Delta}
      {c : Conv.Conv↓ Delta A B}
    → (c⊢ c⊢′ : Sigma Conv.⊢↓[ X ⦂ R ] c)
    → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c⊢′
  concealGeneratorPosition-unique (Conv.⊢↓-seal member)
      (Conv.⊢↓-seal member′) =
    refl
  concealGeneratorPosition-unique (Conv.⊢↓-⇒ c⊢ d⊢)
      (Conv.⊢↓-⇒ c⊢′ d⊢′)
    rewrite revealGeneratorPosition-unique c⊢ c⊢′
      | concealGeneratorPosition-unique d⊢ d⊢′ =
    refl
  concealGeneratorPosition-unique (Conv.⊢↓-∀ refl c⊢)
      (Conv.⊢↓-∀ refl c⊢′)
    rewrite concealGeneratorPosition-unique c⊢ c⊢′ =
    refl
  concealGeneratorPosition-unique (Conv.⊢↓-id-var member X≠Y)
      (Conv.⊢↓-id-var member′ X≠Y′) =
    refl
  concealGeneratorPosition-unique (Conv.⊢↓-id-base member)
      (Conv.⊢↓-id-base member′) =
    refl
  concealGeneratorPosition-unique (Conv.⊢↓-id-star member)
      (Conv.⊢↓-id-star member′) =
    refl
