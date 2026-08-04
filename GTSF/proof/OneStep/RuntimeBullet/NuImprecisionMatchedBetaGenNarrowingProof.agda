module
  proof.OneStep.RuntimeBullet.NuImprecisionMatchedBetaGenNarrowingProof
  where

-- File Charter:
--   * Proves the matched post-allocation `β-gen•` narrowing relation from
--     allocation transport for generic narrowing coercions.
--   * Reconstructs one `paired-downᵀ` edge without constructing or bundling
--     either operational reduction step.
--   * Contains no dispatcher, postulate, hole, permissive option, canonical
--     dependency implementation, or legacy allocation-simulation import.

open import CastImprecisionShape using (_⊢ᶜ_⦂_; narrowing)
open import Coercions using
  ( gen
  ; genᵈ
  ; id-onlyᵈ
  ; id-only≤tag-or-idᵈ
  ; tag-or-idᵈ
  )
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import NarrowWiden using
  ( narrow-mode-relax
  ; _∣_∣_⊢_∶_⊒_
  )
open import QuotientImprecisionCompatibility using (gradual↓)
open import QuotientedTermImprecision using
  ( paired-downᵀ
  ; seal★-gen-tag-or-id
  )
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import TermTyping using (cast-gen; cast-tag-or-id)
open import Types using (`∀; ⇑ᵗ; ⟰ᵗ)
open import proof.Core.Properties.CoercionProperties using (ModeIncl-gen)
open import
  proof.OneStep.RuntimeBullet.NuImprecisionMatchedBetaGenNarrowingDef
  using (MatchedPostAllocationBetaGenNarrowingRelationᵀ)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( leftStoreⁱ
  ; leftStoreⁱ-lift
  ; rightStoreⁱ
  ; rightStoreⁱ-lift
  )


matched-post-allocation-β-gen-narrowing-relation-proofᵀ :
  (∀ {μ Δ Σ Aν c A B} →
    μ ∣ Δ ∣ Σ ⊢ gen A c ∶ A ⊒ `∀ B →
    genᵈ μ ∣ suc Δ ∣ (zero , Aν) ∷ ⟰ᵗ Σ
      ⊢ c ∶ ⇑ᵗ A ⊒ B) →
  MatchedPostAllocationBetaGenNarrowingRelationᵀ
matched-post-allocation-β-gen-narrowing-relation-proofᵀ
    allocate-gen-narrowingᵀ
    {Aν = Aν} {Aν′ = Aν′}
    c⊒ c′⊒ c-shape c′-shape pν liftρ V⊑V′ q
    square elimination =
  paired-downᵀ
    V⊑V′
    (gradual↓ (cast-gen cast-tag-or-id) seal★-gen-tag-or-id)
    (narrow-mode-relax (ModeIncl-gen id-only≤tag-or-idᵈ) left-body)
    c-shape
    (gradual↓ (cast-gen cast-tag-or-id) seal★-gen-tag-or-id)
    (narrow-mode-relax (ModeIncl-gen id-only≤tag-or-idᵈ) right-body)
    c′-shape
    square
    elimination
  where
  left-body =
    subst
      (λ Σ → genᵈ id-onlyᵈ ∣ _ ∣ (zero , Aν) ∷ Σ
        ⊢ _ ∶ _ ⊒ _)
      (sym (leftStoreⁱ-lift liftρ))
      (allocate-gen-narrowingᵀ {Aν = Aν} c⊒)

  right-body =
    subst
      (λ Σ → genᵈ id-onlyᵈ ∣ _ ∣ (zero , Aν′) ∷ Σ
        ⊢ _ ∶ _ ⊒ _)
      (sym (rightStoreⁱ-lift liftρ))
      (allocate-gen-narrowingᵀ {Aν = Aν′} c′⊒)
