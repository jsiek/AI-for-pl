module proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleTest where

-- File Charter:
--   * Computation-by-`refl` regression tests for the simple exhaustive
--     endpoint MLB algorithm in `proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple`.
--   * Checks first-route selection, all-maximal route order, and edge cases
--     around one-sided and unused `forall` binders.
--   * Complements, but does not replace, the efficient endpoint algorithm tests
--     in `proof.EndpointMLB.Core.EndpointCanonicalMLBTest`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)

open import Types
open import proof.EndpointMLB.Core.MLBGlbExample using
  ( glb-bad-A
  ; glb-bad-B
  ; glb-lower-XY
  ; glb-lower-YX
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using
  ( allEndpointMlbs
  ; endpointCtx
  ; rawEndpointMlbs
  ; simpleEndpointMlb
  ; typeCtxBound
  )

NatTy : Ty
NatTy = ‵ `ℕ

BoolTy : Ty
BoolTy = ‵ `𝔹

BadGlbLeftTy : Ty
BadGlbLeftTy = glb-bad-A

BadGlbRightTy : Ty
BadGlbRightTy = glb-bad-B

RepeatedOneSidedTy : Ty
RepeatedOneSidedTy = `∀ ((＇ 0) ⇒ (＇ 0))

FirstUseExposureTy : Ty
FirstUseExposureTy = `∀ (`∀ ((＇ 0) ⇒ (＇ 1)))

simple-typeCtxBound-star :
  typeCtxBound ★ ≡ 0
simple-typeCtxBound-star = refl

simple-typeCtxBound-var :
  typeCtxBound (＇ 2) ≡ 3
simple-typeCtxBound-var = refl

simple-typeCtxBound-bound-forall :
  typeCtxBound (`∀ (＇ 0)) ≡ 0
simple-typeCtxBound-bound-forall = refl

simple-typeCtxBound-free-under-forall :
  typeCtxBound (`∀ (＇ 1)) ≡ 1
simple-typeCtxBound-free-under-forall = refl

simple-endpointCtx :
  endpointCtx (`∀ (＇ 1)) (＇ 2) ≡ 3
simple-endpointCtx = refl

simpleMlbs-bad-glb-routes :
  allEndpointMlbs BadGlbLeftTy BadGlbRightTy ≡
  glb-lower-XY ∷ glb-lower-YX ∷ []
simpleMlbs-bad-glb-routes = refl

simpleMlbs-bad-glb-reversed-routes :
  allEndpointMlbs BadGlbRightTy BadGlbLeftTy ≡
  glb-lower-YX ∷ glb-lower-XY ∷ []
simpleMlbs-bad-glb-reversed-routes = refl

simpleMlb-bad-glb-pair :
  simpleEndpointMlb BadGlbLeftTy BadGlbRightTy ≡ just glb-lower-XY
simpleMlb-bad-glb-pair = refl

simpleMlb-bad-glb-pair-reversed :
  simpleEndpointMlb BadGlbRightTy BadGlbLeftTy ≡ just glb-lower-YX
simpleMlb-bad-glb-pair-reversed = refl

simpleMlb-repeated-one-sided :
  simpleEndpointMlb RepeatedOneSidedTy ★ ≡ just RepeatedOneSidedTy
simpleMlb-repeated-one-sided = refl

simpleMlb-repeated-one-sided-right :
  simpleEndpointMlb ★ RepeatedOneSidedTy ≡ just RepeatedOneSidedTy
simpleMlb-repeated-one-sided-right = refl

simpleMlb-used-var-left :
  simpleEndpointMlb (`∀ (＇ 0)) ★ ≡ just (`∀ (＇ 0))
simpleMlb-used-var-left = refl

simpleMlb-used-var-right :
  simpleEndpointMlb ★ (`∀ (＇ 0)) ≡ just (`∀ (＇ 0))
simpleMlb-used-var-right = refl

simpleMlb-unused-left-fails :
  simpleEndpointMlb (`∀ ★) ★ ≡ nothing
simpleMlb-unused-left-fails = refl

simpleMlb-unused-right-fails :
  simpleEndpointMlb ★ (`∀ ★) ≡ nothing
simpleMlb-unused-right-fails = refl

simpleMlb-unused-base-left-fails :
  simpleEndpointMlb (`∀ NatTy) ★ ≡ nothing
simpleMlb-unused-base-left-fails = refl

simpleMlb-unused-base-right-fails :
  simpleEndpointMlb ★ (`∀ NatTy) ≡ nothing
simpleMlb-unused-base-right-fails = refl

simpleMlb-unused-binders-pair :
  simpleEndpointMlb (`∀ ★) (`∀ ★) ≡ just (`∀ ★)
simpleMlb-unused-binders-pair = refl

simpleMlb-unused-binders-pair-twice :
  simpleEndpointMlb (`∀ (`∀ ★)) (`∀ (`∀ ★)) ≡ just (`∀ (`∀ ★))
simpleMlb-unused-binders-pair-twice = refl

simpleMlb-shared-and-one-sided-fails :
  simpleEndpointMlb (`∀ ((＇ 0) ⇒ (＇ 0))) (`∀ ((＇ 0) ⇒ ★)) ≡
  nothing
simpleMlb-shared-and-one-sided-fails = refl

simpleMlb-one-right-two-left-fails :
  simpleEndpointMlb (`∀ (`∀ ((＇ 1) ⇒ (＇ 0))))
                    (`∀ ((＇ 0) ⇒ (＇ 0))) ≡
  nothing
simpleMlb-one-right-two-left-fails = refl

simpleMlb-crossing-exposure-fails :
  simpleEndpointMlb (`∀ (`∀ (＇ 1))) (`∀ (`∀ (＇ 0))) ≡ nothing
simpleMlb-crossing-exposure-fails = refl

simpleMlb-matching-two-binder-order :
  simpleEndpointMlb (`∀ (`∀ ((＇ 1) ⇒ (＇ 0))))
                    (`∀ (`∀ ((＇ 1) ⇒ (＇ 0)))) ≡
  just (`∀ (`∀ ((＇ 1) ⇒ (＇ 0))))
simpleMlb-matching-two-binder-order = refl

simpleMlb-star-star :
  simpleEndpointMlb ★ ★ ≡ just ★
simpleMlb-star-star = refl

simpleMlbs-star-star :
  allEndpointMlbs ★ ★ ≡ ★ ∷ []
simpleMlbs-star-star = refl

simpleRawMlbs-star-star :
  rawEndpointMlbs ★ ★ ≡ ★ ∷ []
simpleRawMlbs-star-star = refl

simpleMlb-base-star :
  simpleEndpointMlb NatTy ★ ≡ just NatTy
simpleMlb-base-star = refl

simpleMlb-star-base :
  simpleEndpointMlb ★ BoolTy ≡ just BoolTy
simpleMlb-star-base = refl

simpleMlb-base-mismatch :
  simpleEndpointMlb NatTy BoolTy ≡ nothing
simpleMlb-base-mismatch = refl

simpleMlb-arrow-star :
  simpleEndpointMlb (NatTy ⇒ BoolTy) ★ ≡ just (NatTy ⇒ BoolTy)
simpleMlb-arrow-star = refl

simpleMlb-star-arrow :
  simpleEndpointMlb ★ (NatTy ⇒ BoolTy) ≡ just (NatTy ⇒ BoolTy)
simpleMlb-star-arrow = refl

simpleMlb-nested-forall-blocks :
  simpleEndpointMlb ((`∀ (＇ 0)) ⇒ (`∀ ★))
                    ((`∀ (＇ 0)) ⇒ (`∀ ★)) ≡
  just ((`∀ (＇ 0)) ⇒ (`∀ ★))
simpleMlb-nested-forall-blocks = refl

simpleMlb-first-route-preserves-exposure :
  simpleEndpointMlb ★ FirstUseExposureTy ≡ just FirstUseExposureTy
simpleMlb-first-route-preserves-exposure = refl

simpleMlb-first-route-preserves-exposure-reversed :
  simpleEndpointMlb FirstUseExposureTy ★ ≡ just FirstUseExposureTy
simpleMlb-first-route-preserves-exposure-reversed = refl
