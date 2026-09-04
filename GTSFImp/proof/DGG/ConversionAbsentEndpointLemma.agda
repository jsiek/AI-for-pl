{-# OPTIONS --safe #-}

module proof.DGG.ConversionAbsentEndpointLemma where

-- File Charter:
--   * Proves the endpoint equality of a well-typed conversion whose
--     generator position is absent.
--   * Exports the mutually dual reveal and conceal facts used to enter
--     recursive proofs beneath structural-identity conversion wrappers.
--   * Depends only on conversion typing and generator-position structure.

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyCtx; TyVar)
open import TyStore using (TyStore)
import Conversion as Conv
open import proof.DGG.ConversionPivotAlignment using
  ( GeneratorPosition; generator-absent; generator-here
  ; generator-⇒-left; generator-⇒-right; generator-⇒-both; generator-∀
  ; joinGeneratorPositions-absent-left
  ; joinGeneratorPositions-absent-right
  ; liftGeneratorPosition; revealGeneratorPosition
  ; concealGeneratorPosition
  )


lift-position-absent : ∀ {position : GeneratorPosition}
  → liftGeneratorPosition position ≡ generator-absent
  → position ≡ generator-absent
lift-position-absent {generator-absent} refl = refl
lift-position-absent {generator-here} ()
lift-position-absent {generator-⇒-left position} ()
lift-position-absent {generator-⇒-right position} ()
lift-position-absent {generator-⇒-both left right} ()
lift-position-absent {generator-∀ position} ()


mutual

  reveal-absent-endpoints : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
      {X : TyVar Δ} {R A B : Ty Δ} {c : Conv.Conv↑ Δ A B}
    → (c⊢ : Σ Conv.⊢↑[ X ⦂ R ] c)
    → revealGeneratorPosition c⊢ ≡ generator-absent
    → A ≡ B
  reveal-absent-endpoints (Conv.⊢↑-unseal member) ()
  reveal-absent-endpoints (Conv.⊢↑-⇒ left right) absent
      with conceal-absent-endpoints left
        (joinGeneratorPositions-absent-left absent)
         | reveal-absent-endpoints right
        (joinGeneratorPositions-absent-right absent)
  reveal-absent-endpoints (Conv.⊢↑-⇒ left right) absent
      | refl | refl = refl
  reveal-absent-endpoints (Conv.⊢↑-∀ refl body) absent
      with reveal-absent-endpoints body (lift-position-absent absent)
  reveal-absent-endpoints (Conv.⊢↑-∀ refl body) absent | refl = refl
  reveal-absent-endpoints (Conv.⊢↑-id-var member X≠Y) refl = refl
  reveal-absent-endpoints (Conv.⊢↑-id-base member) refl = refl
  reveal-absent-endpoints (Conv.⊢↑-id-star member) refl = refl

  conceal-absent-endpoints : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
      {X : TyVar Δ} {R A B : Ty Δ} {c : Conv.Conv↓ Δ A B}
    → (c⊢ : Σ Conv.⊢↓[ X ⦂ R ] c)
    → concealGeneratorPosition c⊢ ≡ generator-absent
    → A ≡ B
  conceal-absent-endpoints (Conv.⊢↓-seal member) ()
  conceal-absent-endpoints (Conv.⊢↓-⇒ left right) absent
      with reveal-absent-endpoints left
        (joinGeneratorPositions-absent-left absent)
         | conceal-absent-endpoints right
        (joinGeneratorPositions-absent-right absent)
  conceal-absent-endpoints (Conv.⊢↓-⇒ left right) absent
      | refl | refl = refl
  conceal-absent-endpoints (Conv.⊢↓-∀ refl body) absent
      with conceal-absent-endpoints body (lift-position-absent absent)
  conceal-absent-endpoints (Conv.⊢↓-∀ refl body) absent | refl = refl
  conceal-absent-endpoints (Conv.⊢↓-id-var member X≠Y) refl = refl
  conceal-absent-endpoints (Conv.⊢↓-id-base member) refl = refl
  conceal-absent-endpoints (Conv.⊢↓-id-star member) refl = refl
