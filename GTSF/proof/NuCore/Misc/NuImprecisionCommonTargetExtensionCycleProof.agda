module proof.NuCore.Misc.NuImprecisionCommonTargetExtensionCycleProof where

-- File Charter:
--   * Proves the common-target-extension cycle by exhaustive recursion over
--     the paired-lower derivation.
--   * A one-sided binder exposes an impossible left- or right-star path from
--     a type to its uniformly renamed copy.
--   * Contains no theorem dependency, postulate, hole, permissive option,
--     conversion, store, term relation, or simulation import.

open import Data.Empty using (⊥)
open import Types using
  ( Renameᵗ
  ; Ty
  ; TyVar
  ; ＇_
  ; ‵_
  ; ★
  ; _⇒_
  ; `∀
  ; extᵗ
  ; renameᵗ
  ; ⇑ᵗ
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleFactor using
  (source-left-exposure-path; source-right-exposure-path)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePairedSpan using
  ( PairedLower
  ; paired-both
  ; paired-left
  ; paired-lower-left
  ; paired-lower-right
  ; paired-neither
  ; paired-right
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePermutation using
  ( LeftStarPath
  ; StarRightPath
  ; no-left-star-path
  ; no-right-star-path
  ; path-arrow₁
  ; path-arrow₂
  ; remove-left-path
  ; remove-left-star-path
  ; remove-right-path
  ; remove-right-star-path
  ; star-path-arrow₁
  ; star-path-arrow₂
  )
open import proof.NuCore.Misc.NuImprecisionCommonTargetExtensionCycleDef using
  (CommonTargetExtensionCycleᵀ)


private
  left-star-path-rename-cycle :
    ∀ {A : Ty} {ρ : Renameᵗ} {X : TyVar} →
    LeftStarPath A (renameᵗ ρ A) X →
    ⊥
  left-star-path-rename-cycle {A = ＇ X} ()
  left-star-path-rename-cycle {A = ‵ ι} ()
  left-star-path-rename-cycle {A = ★} path =
    no-left-star-path path
  left-star-path-rename-cycle {A = A ⇒ B} (path-arrow₁ path) =
    left-star-path-rename-cycle path
  left-star-path-rename-cycle {A = A ⇒ B} (path-arrow₂ path) =
    left-star-path-rename-cycle path
  left-star-path-rename-cycle {A = `∀ A} {ρ = ρ} path =
    left-star-path-rename-cycle
      (remove-right-path (remove-left-path path))

  star-right-path-rename-cycle :
    ∀ {A : Ty} {ρ : Renameᵗ} {X : TyVar} →
    StarRightPath A (renameᵗ ρ A) X →
    ⊥
  star-right-path-rename-cycle {A = ＇ X} ()
  star-right-path-rename-cycle {A = ‵ ι} ()
  star-right-path-rename-cycle {A = ★} path =
    no-right-star-path path
  star-right-path-rename-cycle {A = A ⇒ B}
      (star-path-arrow₁ path) =
    star-right-path-rename-cycle path
  star-right-path-rename-cycle {A = A ⇒ B}
      (star-path-arrow₂ path) =
    star-right-path-rename-cycle path
  star-right-path-rename-cycle {A = `∀ A} {ρ = ρ} path =
    star-right-path-rename-cycle
      (remove-right-star-path (remove-left-star-path path))


common-target-extension-cycle-proofᵀ :
  CommonTargetExtensionCycleᵀ
common-target-extension-cycle-proofᵀ (paired-both lower) =
  common-target-extension-cycle-proofᵀ lower
common-target-extension-cycle-proofᵀ (paired-left occ lower) =
  left-star-path-rename-cycle
    (remove-right-path
      (remove-right-path
        (source-left-exposure-path
          (paired-lower-left lower)
          (paired-lower-right lower)
          occ)))
common-target-extension-cycle-proofᵀ (paired-right occ lower) =
  star-right-path-rename-cycle
    (source-right-exposure-path
      (paired-lower-left lower)
      (paired-lower-right lower)
      occ)
common-target-extension-cycle-proofᵀ (paired-neither occ lower) =
  common-target-extension-cycle-proofᵀ lower
