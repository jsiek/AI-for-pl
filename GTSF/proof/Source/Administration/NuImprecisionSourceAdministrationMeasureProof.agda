module
  proof.Source.Administration.NuImprecisionSourceAdministrationMeasureProof
  where

-- File Charter:
--   * Proves the strict source-administration decreases needed after
--     structural value catch-up reaches a source runtime form.
--   * Covers pending-cast removal, inert absorption, active cancellation,
--     sequence expansion, instantiation, source allocation, and all three
--     runtime-bullet value forms.
--   * Uses one source-allocation equation for both ordinary source `ν` and
--     source-only `νcast`; their typed plans differ but their reduction does
--     not.
--   * Supplies narrowing and widening from the same cast equations.
--   * Deliberately supplies no identity-reentry equation for the current
--     bullet and narrowing adapters: strict descent is irreflexive, so those
--     adapters must be replaced by direct administration.
--   * Contains no semantic recursion, theorem alias, postulate, hole,
--     permissive option, or termination bypass.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using (_∷_; map)
open import Data.Nat using (_<_; suc; zero)
open import Data.Nat.Properties using (<-irrefl; <-trans)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Coercions as C
open import Coercions using
  (Coercion; Inert; gen; inst; renameᶜ; _︔_; `∀; ⇑ᶜ)
open import NuTerms using (Term; Value; Λ_; _⟨_⟩)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value)
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureLemma
  using
  ( inert-value-administration-increaseᵀ
  ; pending-administration-tail-decreaseᵀ
  )
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureProof
  using
  ( all-bullet-rank-decreases
  ; gen-bullet-rank-decreases
  ; inert-rank-decreases
  ; inst-rank-decreases
  ; nu-rank-decreases
  ; pending-administration-shifted-tail-rank-invariant
  ; sequence-rank-decreases
  ; Λ-bullet-rank-decreases
  )
open import
  proof.Source.Administration.NuImprecisionSourceAdministrationState
open import Types using (Ty; singleRenameᵗ)


source-cast-tail-rank-decreases :
  ∀ {V} (vV : Value V) c cs →
  sourceAdministrationRank vV (casts cs) <
    sourceAdministrationRank vV (casts (c ∷ cs))
source-cast-tail-rank-decreases =
  pending-administration-tail-decreaseᵀ


source-cast-inert-rank-decreases :
  ∀ {V c} (vV : Value V) (inert-c : Inert c) cs →
  sourceAdministrationRank vV (casts (c ∷ cs)) ≡
    suc (sourceAdministrationRank (vV ⟨ inert-c ⟩) (casts cs))
source-cast-inert-rank-decreases =
  inert-rank-decreases


source-cast-cancellation-rank-decreases :
  ∀ {V c d} (vV : Value V) (inert-c : Inert c) cs →
  sourceAdministrationRank vV (casts cs) <
    sourceAdministrationRank (vV ⟨ inert-c ⟩) (casts (d ∷ cs))
source-cast-cancellation-rank-decreases {d = d} vV inert-c cs =
  <-trans
    (inert-value-administration-increaseᵀ vV inert-c cs)
    (pending-administration-tail-decreaseᵀ
      (vV ⟨ inert-c ⟩) d cs)


source-cast-sequence-rank-decreases :
  ∀ {V} (vV : Value V) s t cs →
  sourceAdministrationRank vV (casts ((s ︔ t) ∷ cs)) ≡
    suc (sourceAdministrationRank vV (casts (s ∷ t ∷ cs)))
source-cast-sequence-rank-decreases =
  sequence-rank-decreases


source-cast-inst-rank-decreases :
  ∀ {V} (vV : Value V) (B : Ty) c cs →
  sourceAdministrationRank vV (casts (inst B c ∷ cs)) ≡
    suc (suc (suc (sourceAdministrationRank vV (ν c cs))))
source-cast-inst-rank-decreases =
  inst-rank-decreases


source-ν-rank-decreases :
  ∀ {V} (vV : Value V) c cs →
  sourceAdministrationRank vV (ν c cs) ≡
    suc
      (sourceAdministrationRank
        (renameᵗᵐ-preserves-Value suc vV)
        (bullet (c ∷ map ⇑ᶜ cs)))
source-ν-rank-decreases vV c cs =
  trans
    (nu-rank-decreases vV c cs)
    (cong suc
      (sym
        (pending-administration-shifted-tail-rank-invariant
          vV c cs)))


source-Λ-bullet-rank-decreases :
  ∀ {V} (vV : Value V) cs →
  sourceAdministrationRank (Λ vV) (bullet cs) ≡
    suc
      (suc
        (sourceAdministrationRank
          (renameᵗᵐ-preserves-Value (singleRenameᵗ zero) vV)
          (casts cs)))
source-Λ-bullet-rank-decreases =
  Λ-bullet-rank-decreases


source-all-bullet-rank-decreases :
  ∀ {V} (vV : Value V) c cs →
  sourceAdministrationRank (vV ⟨ C.`∀ c ⟩) (bullet cs) ≡
    suc
      (suc
        (suc
          (sourceAdministrationRank vV
            (bullet
              (renameᶜ (singleRenameᵗ zero) c ∷ cs)))))
source-all-bullet-rank-decreases =
  all-bullet-rank-decreases


source-gen-bullet-rank-decreases :
  ∀ {V A} (vV : Value V) c cs →
  sourceAdministrationRank (vV ⟨ C.gen A c ⟩) (bullet cs) ≡
    suc
      (suc
        (suc
          (sourceAdministrationRank vV
            (casts
              (renameᶜ (singleRenameᵗ zero) c ∷ cs)))))
source-gen-bullet-rank-decreases {A = A} vV c cs =
  gen-bullet-rank-decreases {A = A} vV c cs


source-administration-rank-irreflexive :
  ∀ {V} (vV : Value V) state →
  sourceAdministrationRank vV state <
    sourceAdministrationRank vV state →
  ⊥
source-administration-rank-irreflexive vV state =
  <-irrefl refl
