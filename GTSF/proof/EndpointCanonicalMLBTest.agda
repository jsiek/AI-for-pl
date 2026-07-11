module proof.EndpointCanonicalMLBTest where

-- File Charter:
--   * Regression tests for the executable endpoint-canonical MLB algorithm.
--   * Tests the Agda implementation in `proof.EndpointCanonicalMLB`, not the
--     older assumption-merging `proof.MaximalLowerBounds.mlb?` experiment.
--   * Each theorem is a computation-by-`refl` check for a named edge case from
--     `EndpointCanonicalMLBDesign.md` and the Python reference tests.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe using (just; nothing)

open import Types
open import proof.EndpointCanonicalMLB using (endpointMlb)

NatTy : Ty
NatTy = ‵ `ℕ

BoolTy : Ty
BoolTy = ‵ `𝔹

BadGlbLeftTy : Ty
BadGlbLeftTy = `∀ ((＇ 0) ⇒ ★)

BadGlbRightTy : Ty
BadGlbRightTy = `∀ (★ ⇒ (＇ 0))

BadGlbLowerTy : Ty
BadGlbLowerTy = `∀ (`∀ ((＇ 1) ⇒ (＇ 0)))

RepeatedOneSidedTy : Ty
RepeatedOneSidedTy = `∀ ((＇ 0) ⇒ (＇ 0))

UsedVarBaseTy : Ty
UsedVarBaseTy = `∀ ((＇ 0) ⇒ NatTy)

UsedVarStarTy : Ty
UsedVarStarTy = `∀ ((＇ 0) ⇒ ★)

FirstUseExposureTy : Ty
FirstUseExposureTy = `∀ (`∀ ((＇ 0) ⇒ (＇ 1)))

endpointMlb-bad-glb-pair :
  endpointMlb BadGlbLeftTy BadGlbRightTy ≡ just BadGlbLowerTy
endpointMlb-bad-glb-pair = refl

endpointMlb-bad-glb-pair-reversed :
  endpointMlb BadGlbRightTy BadGlbLeftTy ≡ just BadGlbLowerTy
endpointMlb-bad-glb-pair-reversed = refl

endpointMlb-repeated-one-sided :
  endpointMlb RepeatedOneSidedTy ★ ≡ just RepeatedOneSidedTy
endpointMlb-repeated-one-sided = refl

endpointMlb-repeated-one-sided-right :
  endpointMlb ★ RepeatedOneSidedTy ≡ just RepeatedOneSidedTy
endpointMlb-repeated-one-sided-right = refl

endpointMlb-used-var-left :
  endpointMlb (`∀ (＇ 0)) ★ ≡ just (`∀ (＇ 0))
endpointMlb-used-var-left = refl

endpointMlb-used-var-right :
  endpointMlb ★ (`∀ (＇ 0)) ≡ just (`∀ (＇ 0))
endpointMlb-used-var-right = refl

endpointMlb-used-var-base-left :
  endpointMlb UsedVarBaseTy ★ ≡ just UsedVarBaseTy
endpointMlb-used-var-base-left = refl

endpointMlb-used-var-base-right :
  endpointMlb ★ UsedVarBaseTy ≡ just UsedVarBaseTy
endpointMlb-used-var-base-right = refl

endpointMlb-used-var-star-left :
  endpointMlb UsedVarStarTy ★ ≡ just UsedVarStarTy
endpointMlb-used-var-star-left = refl

endpointMlb-used-var-star-right :
  endpointMlb ★ UsedVarStarTy ≡ just UsedVarStarTy
endpointMlb-used-var-star-right = refl

endpointMlb-unused-left-fails :
  endpointMlb (`∀ ★) ★ ≡ nothing
endpointMlb-unused-left-fails = refl

endpointMlb-unused-right-fails :
  endpointMlb ★ (`∀ ★) ≡ nothing
endpointMlb-unused-right-fails = refl

endpointMlb-unused-base-left-fails :
  endpointMlb (`∀ NatTy) ★ ≡ nothing
endpointMlb-unused-base-left-fails = refl

endpointMlb-unused-base-right-fails :
  endpointMlb ★ (`∀ NatTy) ≡ nothing
endpointMlb-unused-base-right-fails = refl

endpointMlb-unused-base-arrow-left-fails :
  endpointMlb (`∀ (NatTy ⇒ BoolTy)) ★ ≡ nothing
endpointMlb-unused-base-arrow-left-fails = refl

endpointMlb-unused-base-arrow-right-fails :
  endpointMlb ★ (`∀ (NatTy ⇒ BoolTy)) ≡ nothing
endpointMlb-unused-base-arrow-right-fails = refl

endpointMlb-unused-binders-pair :
  endpointMlb (`∀ ★) (`∀ ★) ≡ just (`∀ ★)
endpointMlb-unused-binders-pair = refl

endpointMlb-forall-base-base :
  endpointMlb (`∀ NatTy) (`∀ NatTy) ≡ just (`∀ NatTy)
endpointMlb-forall-base-base = refl

endpointMlb-forall-var-var :
  endpointMlb (`∀ (＇ 0)) (`∀ (＇ 0)) ≡ just (`∀ (＇ 0))
endpointMlb-forall-var-var = refl

endpointMlb-unused-binders-pair-twice :
  endpointMlb (`∀ (`∀ ★)) (`∀ (`∀ ★)) ≡ just (`∀ (`∀ ★))
endpointMlb-unused-binders-pair-twice = refl

endpointMlb-repeated-one-sided-unused-target-fails :
  endpointMlb (`∀ ((＇ 0) ⇒ (＇ 0))) (`∀ (★ ⇒ ★)) ≡ nothing
endpointMlb-repeated-one-sided-unused-target-fails = refl

endpointMlb-repeated-one-sided-unused-target-reversed-fails :
  endpointMlb (`∀ (★ ⇒ ★)) (`∀ ((＇ 0) ⇒ (＇ 0))) ≡ nothing
endpointMlb-repeated-one-sided-unused-target-reversed-fails = refl

endpointMlb-shared-and-one-sided-fails :
  endpointMlb (`∀ ((＇ 0) ⇒ (＇ 0))) (`∀ ((＇ 0) ⇒ ★)) ≡
  nothing
endpointMlb-shared-and-one-sided-fails = refl

endpointMlb-shared-and-one-sided-reversed-fails :
  endpointMlb (`∀ ((＇ 0) ⇒ ★)) (`∀ ((＇ 0) ⇒ (＇ 0))) ≡
  nothing
endpointMlb-shared-and-one-sided-reversed-fails = refl

endpointMlb-one-right-two-left-fails :
  endpointMlb
    (`∀ (`∀ ((＇ 1) ⇒ (＇ 0))))
    (`∀ ((＇ 0) ⇒ (＇ 0))) ≡ nothing
endpointMlb-one-right-two-left-fails = refl

endpointMlb-one-left-two-right-fails :
  endpointMlb
    (`∀ ((＇ 0) ⇒ (＇ 0)))
    (`∀ (`∀ ((＇ 1) ⇒ (＇ 0)))) ≡ nothing
endpointMlb-one-left-two-right-fails = refl

endpointMlb-crossing-exposure-fails :
  endpointMlb (`∀ (`∀ (＇ 1))) (`∀ (`∀ (＇ 0))) ≡ nothing
endpointMlb-crossing-exposure-fails = refl

endpointMlb-crossing-exposure-reversed-fails :
  endpointMlb (`∀ (`∀ (＇ 0))) (`∀ (`∀ (＇ 1))) ≡ nothing
endpointMlb-crossing-exposure-reversed-fails = refl

endpointMlb-matching-two-binder-order :
  endpointMlb (`∀ (`∀ ((＇ 1) ⇒ (＇ 0))))
              (`∀ (`∀ ((＇ 1) ⇒ (＇ 0)))) ≡
  just (`∀ (`∀ ((＇ 1) ⇒ (＇ 0))))
endpointMlb-matching-two-binder-order = refl

endpointMlb-star-star :
  endpointMlb ★ ★ ≡ just ★
endpointMlb-star-star = refl

endpointMlb-base-base :
  endpointMlb NatTy NatTy ≡ just NatTy
endpointMlb-base-base = refl

endpointMlb-free-var-one-identity :
  endpointMlb (＇ 1) (＇ 1) ≡ just (＇ 1)
endpointMlb-free-var-one-identity = refl

endpointMlb-base-star :
  endpointMlb NatTy ★ ≡ just NatTy
endpointMlb-base-star = refl

endpointMlb-star-base :
  endpointMlb ★ BoolTy ≡ just BoolTy
endpointMlb-star-base = refl

endpointMlb-var-star-mismatch :
  endpointMlb (＇ 0) ★ ≡ nothing
endpointMlb-var-star-mismatch = refl

endpointMlb-star-var-mismatch :
  endpointMlb ★ (＇ 0) ≡ nothing
endpointMlb-star-var-mismatch = refl

endpointMlb-base-mismatch :
  endpointMlb NatTy BoolTy ≡ nothing
endpointMlb-base-mismatch = refl

endpointMlb-forall-base-mismatch :
  endpointMlb (`∀ NatTy) (`∀ BoolTy) ≡ nothing
endpointMlb-forall-base-mismatch = refl

endpointMlb-forall-base-mismatch-reversed :
  endpointMlb (`∀ BoolTy) (`∀ NatTy) ≡ nothing
endpointMlb-forall-base-mismatch-reversed = refl

endpointMlb-base-arrow-mismatch :
  endpointMlb NatTy (NatTy ⇒ BoolTy) ≡ nothing
endpointMlb-base-arrow-mismatch = refl

endpointMlb-arrow-base-mismatch :
  endpointMlb (NatTy ⇒ BoolTy) BoolTy ≡ nothing
endpointMlb-arrow-base-mismatch = refl

endpointMlb-var-arrow-mismatch :
  endpointMlb (＇ 0) (NatTy ⇒ BoolTy) ≡ nothing
endpointMlb-var-arrow-mismatch = refl

endpointMlb-arrow-var-mismatch :
  endpointMlb (NatTy ⇒ BoolTy) (＇ 0) ≡ nothing
endpointMlb-arrow-var-mismatch = refl

endpointMlb-arrow-star :
  endpointMlb (NatTy ⇒ BoolTy) ★ ≡ just (NatTy ⇒ BoolTy)
endpointMlb-arrow-star = refl

endpointMlb-star-arrow :
  endpointMlb ★ (NatTy ⇒ BoolTy) ≡ just (NatTy ⇒ BoolTy)
endpointMlb-star-arrow = refl

endpointMlb-arrow-arrow :
  endpointMlb (NatTy ⇒ BoolTy) (NatTy ⇒ BoolTy) ≡
  just (NatTy ⇒ BoolTy)
endpointMlb-arrow-arrow = refl

endpointMlb-nested-forall-blocks :
  endpointMlb
    ((`∀ (＇ 0)) ⇒ (`∀ ★))
    ((`∀ (＇ 0)) ⇒ (`∀ ★)) ≡ just ((`∀ (＇ 0)) ⇒ (`∀ ★))
endpointMlb-nested-forall-blocks = refl

endpointMlb-nested-captures-outer-profile :
  endpointMlb
    (`∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)))
    (`∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))) ≡
  just (`∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)))
endpointMlb-nested-captures-outer-profile = refl

endpointMlb-first-use-does-not-override-exposure :
  endpointMlb ★ FirstUseExposureTy ≡ just FirstUseExposureTy
endpointMlb-first-use-does-not-override-exposure = refl

endpointMlb-first-use-does-not-override-exposure-reversed :
  endpointMlb FirstUseExposureTy ★ ≡ just FirstUseExposureTy
endpointMlb-first-use-does-not-override-exposure-reversed = refl
