module proof.EndpointCanonicalMLBTest where

-- File Charter:
--   * Regression tests for the executable endpoint-canonical MLB algorithm.
--   * Tests the Agda implementation in `proof.EndpointCanonicalMLB`, not the
--     older assumption-merging `proof.MaximalLowerBounds.mlb?` experiment.
--   * Each theorem is a computation-by-`refl` check for a named edge case from
--     `EndpointCanonicalMLBDesign.md` and the Python reference tests.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (s<s; z<s)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; trans)
open import Relation.Nullary using (¬_)

open import Types
open import Imprecision using (idᵢ; ⇑ᵢ; ⇑ᴸᵢ; _ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_
  ; id★
  ; idˣ
  ; tag_
  ; tagˣ
  ; tag_⇛_
  ; ν
  ; ∀ⁱ_
  ; _↦_
  )
open import proof.MLBGlbCounterexample using
  ( glb-bad-A
  ; glb-bad-A⊑A
  ; glb-bad-B
  ; glb-bad-B⊑B
  ; glb-lower-XY
  ; glb-lower-XY⋢YX
  ; glb-lower-XY⊑A
  ; glb-lower-XY⊑B
  ; glb-lower-YX
  ; glb-lower-YX⊑A
  ; glb-lower-YX⊑B
  )
open import proof.EndpointCanonicalMLB using (endpointMlb)
open import proof.EndpointCanonicalMLBProof using
  ( EndpointMlbCoherenceᵢ
  ; EndpointMlbCommonLowerᵢ
  ; EndpointMlbComparableᵢ
  ; EndpointMlbFailureCompleteᵢ
  ; EndpointMlbMaximalᵢ
  ; EndpointMlbSoundᵢ
  ; endpoint-arrow-arrow-maximal-targetᵢ
  ; endpoint-arrow-arrow-sound-targetᵢ
  ; endpoint-canonical-forall-forall-coherence-targetᵢ
  ; endpoint-canonical-forall-forall-maximal-targetᵢ
  ; endpoint-canonical-forall-forall-sound-targetᵢ
  ; endpoint-canonical-forall-forall-to-first-order-coherence-targetᵢ
  ; endpoint-arrow-arrow-coherence-targetᵢ
  ; endpoint-arrow-star-maximal-targetᵢ
  ; endpoint-arrow-star-coherence-targetᵢ
  ; endpoint-arrow-star-sound-targetᵢ
  ; endpoint-arrow-star-to-star-star-coherence-targetᵢ
  ; endpoint-choice-id-selector-comparableᵢ
  ; endpoint-choice-id-selector-coherence-targetᵢ
  ; endpoint-choice-id-selector-maximal-targetᵢ
  ; endpoint-choice-id-selector-sound-targetᵢ
  ; endpoint-common
  ; endpoint-comparable-arrow-arrowᵢ
  ; endpoint-comparable-arrow-starᵢ
  ; endpoint-comparable-base-baseᵢ
  ; endpoint-comparable-base-starᵢ
  ; endpoint-comparable-forall-forall-from-supportᵢ
  ; endpoint-comparable-maximal-targetᵢ
  ; endpoint-comparable-sound-targetᵢ
  ; endpoint-comparable-star-arrowᵢ
  ; endpoint-comparable-star-baseᵢ
  ; endpoint-comparable-first-use-exposure-starᵢ
  ; endpoint-comparable-star-first-use-exposureᵢ
  ; endpoint-comparable-star-starᵢ
  ; endpoint-comparable-to-star-star-coherence-targetᵢ
  ; endpoint-comparable-var-varᵢ
  ; endpoint-forall-var-arrow-var-star-routeᵢ
  ; endpoint-forall-var-arrow-base-to-starᵢ
  ; endpoint-forall-var-arrow-base-starᵢ
  ; endpoint-forall-var-arrow-base-star-routeᵢ
  ; endpoint-forall-var-arrow-star-star-routeᵢ
  ; endpoint-first-use-exposure-star-routeᵢ
  ; endpoint-forall-var-star-routeᵢ
  ; endpoint-forall-var-starᵢ
  ; endpoint-star-first-use-exposure-routeᵢ
  ; endpoint-forall-forall-coherence-targetᵢ
  ; endpoint-forall-forall-sound-targetᵢ
  ; endpoint-forall-forall-supported-coherence-targetᵢ
  ; endpoint-forall-forall-supported-maximal-targetᵢ
  ; endpoint-forall-forall-supported-sound-targetᵢ
  ; endpoint-star-forall-var-arrow-var-routeᵢ
  ; endpoint-star-forall-var-arrow-base-routeᵢ
  ; endpoint-star-forall-var-arrow-star-routeᵢ
  ; endpoint-star-forall-var-routeᵢ
  ; endpoint-star-arrow-maximal-targetᵢ
  ; endpoint-star-arrow-coherence-targetᵢ
  ; endpoint-star-arrow-sound-targetᵢ
  ; endpoint-star-arrow-to-star-star-coherence-targetᵢ
  ; endpoint-canonical-coherence-targetᵢ
  ; endpoint-canonical-maximal-targetᵢ
  ; endpoint-canonical-sound-targetᵢ
  ; endpoint-common-lower-coherence-targetᵢ
  ; endpoint-common-lower-sound-targetᵢ
  ; endpoint-common-lower-to-star-star-coherence-targetᵢ
  ; endpoint-failure-arrow-arrow-codomain-ℕ𝔹ᵢ
  ; endpoint-failure-arrow-arrow-codomain-𝔹ℕᵢ
  ; endpoint-failure-arrow-arrow-codomain-forall-base-leftᵢ
  ; endpoint-failure-arrow-arrow-codomain-forall-base-rightᵢ
  ; endpoint-failure-arrow-arrow-codomain-forall-base-arrow-leftᵢ
  ; endpoint-failure-arrow-arrow-codomain-forall-base-arrow-rightᵢ
  ; endpoint-failure-arrow-arrow-codomain-forall-star-leftᵢ
  ; endpoint-failure-arrow-arrow-codomain-forall-star-rightᵢ
  ; endpoint-failure-arrow-arrow-domain-ℕ𝔹ᵢ
  ; endpoint-failure-arrow-arrow-domain-𝔹ℕᵢ
  ; endpoint-failure-arrow-arrow-domain-forall-base-leftᵢ
  ; endpoint-failure-arrow-arrow-domain-forall-base-rightᵢ
  ; endpoint-failure-arrow-arrow-domain-forall-base-arrow-leftᵢ
  ; endpoint-failure-arrow-arrow-domain-forall-base-arrow-rightᵢ
  ; endpoint-failure-arrow-arrow-domain-forall-star-leftᵢ
  ; endpoint-failure-arrow-arrow-domain-forall-star-rightᵢ
  ; endpoint-failure-arrow-star-codomain-forall-baseᵢ
  ; endpoint-failure-arrow-star-codomain-forall-base-arrowᵢ
  ; endpoint-failure-arrow-star-codomain-forall-starᵢ
  ; endpoint-failure-arrow-star-domain-forall-baseᵢ
  ; endpoint-failure-arrow-star-domain-forall-base-arrowᵢ
  ; endpoint-failure-arrow-star-domain-forall-starᵢ
  ; endpoint-failure-arrow-varᵢ
  ; endpoint-failure-arrow-baseᵢ
  ; endpoint-failure-base-arrowᵢ
  ; endpoint-failure-base-varᵢ
  ; endpoint-failure-base-mismatch-ℕ𝔹ᵢ
  ; endpoint-failure-base-mismatch-𝔹ℕᵢ
  ; endpoint-failure-complete-targetᵢ
  ; endpoint-failure-forall-base-arrow-starᵢ
  ; endpoint-failure-forall-base-mismatch-ℕ𝔹ᵢ
  ; endpoint-failure-forall-base-mismatch-𝔹ℕᵢ
  ; endpoint-failure-forall-arrow-var0-var0-forall-forall-arrow-var1-var0ᵢ
  ; endpoint-failure-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
  ; endpoint-failure-forall-forall-var0-var1ᵢ
  ; endpoint-failure-forall-forall-var1-var0ᵢ
  ; endpoint-failure-forall-arrow-var-var-var-starᵢ
  ; endpoint-failure-forall-arrow-var-var-star-starᵢ
  ; endpoint-failure-forall-arrow-star-star-var-varᵢ
  ; endpoint-failure-forall-arrow-var-star-var-varᵢ
  ; endpoint-failure-forall-base-starᵢ
  ; endpoint-failure-forall-fresh-target-starᵢ
  ; endpoint-failure-forall-star-starᵢ
  ; endpoint-failure-star-varᵢ
  ; endpoint-failure-star-arrow-codomain-forall-baseᵢ
  ; endpoint-failure-star-arrow-codomain-forall-base-arrowᵢ
  ; endpoint-failure-star-arrow-codomain-forall-starᵢ
  ; endpoint-failure-star-arrow-domain-forall-baseᵢ
  ; endpoint-failure-star-arrow-domain-forall-base-arrowᵢ
  ; endpoint-failure-star-arrow-domain-forall-starᵢ
  ; endpoint-failure-star-forall-base-arrowᵢ
  ; endpoint-failure-star-forall-baseᵢ
  ; endpoint-failure-star-forall-fresh-targetᵢ
  ; endpoint-failure-star-forall-starᵢ
  ; endpoint-failure-var-arrowᵢ
  ; endpoint-failure-var-baseᵢ
  ; endpoint-failure-var-starᵢ
  ; endpointMlbCommonLowerTy?
  ; endpoint-mlb-type-from-lower-∀∀-first-order-coherence-targetᵢ
  ; endpoint-mlb-type-from-lower-∀∀-first-order-target-coherenceᵢ
  ; ⊑★-freshᵢ
  ; ⊑-to-base-occurs-falseᵢ
  ; ⊑-to-base-arrow-occurs-falseᵢ
  ; no-common-arrow-var-var-forall-var-star-∀νᵢ
  ; no-common-arrow-var-star-star-var-overlapᵢ
  ; no-common-forall-arrow-var-var-var-starᵢ
  ; no-common-forall-arrow-var-var-star-starᵢ
  ; no-common-forall-arrow-var-var-star-star-body-∀∀ᵢ
  ; no-common-forall-arrow-star-star-var-varᵢ
  ; no-common-forall-arrow-var-star-var-varᵢ
  ; no-common-forall-arrow-var-var-var-star-body-∀∀ᵢ
  ; no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
  ; no-common-forall-forall-var0-var1ᵢ
  ; no-common-forall-forall-var1-var0ᵢ
  ; no-common-forall-var1-var0ᵢ
  ; no-common-target-var-by-occursᵢ
  ; id-no-var-star-overlapᵢ
  ; νctx-no-star-sucᵢ
  ; ∀ctx-no-star-zeroᵢ
  ; ∀ctx-no-var-target-zero-sucᵢ
  ; ∀ctx-only-target-zero-zeroᵢ
  )
open import proof.MaximalLowerBoundsWf using
  ( CommonLowerBoundᵢ
  ; CommonLowerBoundᶜᵢ
  ; ForallNuComparableSupportᵢ
  ; MlbTypeSelectorᵢ
  ; NuForallComparableSupportᵢ
  ; can-arrow-arrow
  ; can-arrow-star
  ; can-base-base
  ; can-base-star
  ; can-star-arrow
  ; can-star-base
  ; can-star-star
  ; can-var-var
  ; canonical-forall-forall-maximal-coherenceᵢ
  ; canonical-first-order-∀∀-supportᵢ
  ; compose-idᵢ
  ; compose-νidᵢ
  ; cᶜ-lowerᵢ
  ; fo-star-star-atᵢ
  ; fo-var-var-atᵢ
  ; choice-idᵢ
  ; leftOnlyᵢ
  ; left-endpoint-∀∀-supportᵢ
  ; mlb-type-comparable-selectorᵢ
  ; mlb-typeᵢ
  ; rightOnlyᵢ
  ; sel-∀ν-arrow-arrowᵢ
  ; sel-∀νᵢ
  ; sel-first-orderᵢ
  ; sel-ν∀ᵢ
  ; sel-ν∀-arrow-arrowᵢ
  ; νᵢᶜ
  ; ν∀-∀lower-directᵢ
  ; ∀ν-∀lower-directᵢ
  ; ∀ᵢᶜ
  ; ⊑-trans-composeᵢ
  ; ⊑-trans-left-idᵢ
  ; fo-star-varᵢ
  ; fo-var-starᵢ
  ; non∀-∀∀-supportᵢ
  )

NatTy : Ty
NatTy = ‵ `ℕ

BoolTy : Ty
BoolTy = ‵ `𝔹

BadGlbLeftTy : Ty
BadGlbLeftTy = glb-bad-A

BadGlbRightTy : Ty
BadGlbRightTy = glb-bad-B

BadGlbLowerTy : Ty
BadGlbLowerTy = glb-lower-XY

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

endpointMlb-repeated-one-sided-unused-body-∀∀-no-commonᵢ :
  ∀ {D} →
  ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)) ∣ 1 ⊢
    D ⊑ ((＇ 0) ⇒ (＇ 0)) ⊣ 1 →
  ¬
    (((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)) ∣ 1 ⊢
      D ⊑ (★ ⇒ ★) ⊣ 1)
endpointMlb-repeated-one-sided-unused-body-∀∀-no-commonᵢ =
  no-common-forall-arrow-var-var-star-star-body-∀∀ᵢ

endpointMlb-repeated-one-sided-unused-no-commonᵢ :
  ∀ {D} →
  idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ ((＇ 0) ⇒ (＇ 0)) ⊣ 0 →
  ¬ (idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ (★ ⇒ ★) ⊣ 0)
endpointMlb-repeated-one-sided-unused-no-commonᵢ =
  no-common-forall-arrow-var-var-star-starᵢ

endpointMlb-repeated-one-sided-unused-reversed-no-commonᵢ :
  ∀ {D} →
  idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ (★ ⇒ ★) ⊣ 0 →
  ¬ (idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ ((＇ 0) ⇒ (＇ 0)) ⊣ 0)
endpointMlb-repeated-one-sided-unused-reversed-no-commonᵢ =
  no-common-forall-arrow-star-star-var-varᵢ

endpointMlb-shared-and-one-sided-fails :
  endpointMlb (`∀ ((＇ 0) ⇒ (＇ 0))) (`∀ ((＇ 0) ⇒ ★)) ≡
  nothing
endpointMlb-shared-and-one-sided-fails = refl

endpointMlb-shared-and-one-sided-reversed-fails :
  endpointMlb (`∀ ((＇ 0) ⇒ ★)) (`∀ ((＇ 0) ⇒ (＇ 0))) ≡
  nothing
endpointMlb-shared-and-one-sided-reversed-fails = refl

endpointMlb-shared-and-one-sided-body-∀∀-no-commonᵢ :
  ∀ {D} →
  ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)) ∣ 1 ⊢
    D ⊑ ((＇ 0) ⇒ (＇ 0)) ⊣ 1 →
  ¬
    (((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)) ∣ 1 ⊢
      D ⊑ ((＇ 0) ⇒ ★) ⊣ 1)
endpointMlb-shared-and-one-sided-body-∀∀-no-commonᵢ =
  no-common-forall-arrow-var-var-var-star-body-∀∀ᵢ

endpointMlb-shared-and-one-sided-body-∀ν-no-commonᵢ :
  ∀ {D} →
  ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)) ∣ 1 ⊢
    D ⊑ ((＇ 0) ⇒ (＇ 0)) ⊣ 1 →
  ¬
    (((0 ˣ⊑★) ∷ ⇑ᴸᵢ (idᵢ 0)) ∣ 1 ⊢
      D ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0)
endpointMlb-shared-and-one-sided-body-∀ν-no-commonᵢ =
  no-common-arrow-var-var-forall-var-star-∀νᵢ

endpointMlb-shared-and-one-sided-no-commonᵢ :
  ∀ {D} →
  idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ ((＇ 0) ⇒ (＇ 0)) ⊣ 0 →
  ¬ (idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0)
endpointMlb-shared-and-one-sided-no-commonᵢ =
  no-common-forall-arrow-var-var-var-starᵢ

endpointMlb-shared-and-one-sided-reversed-no-commonᵢ :
  ∀ {D} →
  idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0 →
  ¬ (idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ ((＇ 0) ⇒ (＇ 0)) ⊣ 0)
endpointMlb-shared-and-one-sided-reversed-no-commonᵢ =
  no-common-forall-arrow-var-star-var-varᵢ

endpointMlb-one-right-two-left-fails :
  endpointMlb (`∀ (`∀ ((＇ 1) ⇒ (＇ 0)))) (`∀ ((＇ 0) ⇒ (＇ 0))) ≡
  nothing
endpointMlb-one-right-two-left-fails = refl

endpointMlb-one-right-two-left-no-commonᵢ :
  ∀ {D} →
  idᵢ 0 ∣ 0 ⊢
    D ⊑ `∀ (`∀ ((＇ 1) ⇒ (＇ 0))) ⊣ 0 →
  ¬
    (idᵢ 0 ∣ 0 ⊢
      D ⊑ `∀ ((＇ 0) ⇒ (＇ 0)) ⊣ 0)
endpointMlb-one-right-two-left-no-commonᵢ =
  no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ

endpointMlb-one-left-two-right-fails :
  endpointMlb (`∀ ((＇ 0) ⇒ (＇ 0))) (`∀ (`∀ ((＇ 1) ⇒ (＇ 0)))) ≡
  nothing
endpointMlb-one-left-two-right-fails = refl

endpointMlb-one-left-two-right-no-commonᵢ :
  ∀ {D} →
  idᵢ 0 ∣ 0 ⊢
    D ⊑ `∀ ((＇ 0) ⇒ (＇ 0)) ⊣ 0 →
  ¬
    (idᵢ 0 ∣ 0 ⊢
      D ⊑ `∀ (`∀ ((＇ 1) ⇒ (＇ 0))) ⊣ 0)
endpointMlb-one-left-two-right-no-commonᵢ p q =
  no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    q
    p

endpointMlb-crossing-exposure-fails :
  endpointMlb (`∀ (`∀ (＇ 1))) (`∀ (`∀ (＇ 0))) ≡ nothing
endpointMlb-crossing-exposure-fails = refl

endpointMlb-crossing-exposure-reversed-fails :
  endpointMlb (`∀ (`∀ (＇ 0))) (`∀ (`∀ (＇ 1))) ≡ nothing
endpointMlb-crossing-exposure-reversed-fails = refl

endpointMlb-crossing-body-var-no-commonᵢ :
  ∀ {D} →
  ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))) ∣
    2 ⊢ D ⊑ ＇ 1 ⊣ 2 →
  ¬
    (((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))) ∣
      2 ⊢ D ⊑ ＇ 0 ⊣ 2)
endpointMlb-crossing-body-var-no-commonᵢ =
  no-common-target-var-by-occursᵢ
    0
    ∀ctx-no-var-target-zero-sucᵢ
    ∀ctx-only-target-zero-zeroᵢ

endpointMlb-crossing-inner-no-commonᵢ :
  ∀ {D} →
  ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)) ∣ 1 ⊢
    D ⊑ `∀ (＇ 1) ⊣ 1 →
  ¬
    (((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)) ∣ 1 ⊢
      D ⊑ `∀ (＇ 0) ⊣ 1)
endpointMlb-crossing-inner-no-commonᵢ =
  no-common-forall-var1-var0ᵢ

endpointMlb-crossing-exposure-no-commonᵢ :
  ∀ {D} →
  idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ (`∀ (＇ 1)) ⊣ 0 →
  ¬ (idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ (`∀ (＇ 0)) ⊣ 0)
endpointMlb-crossing-exposure-no-commonᵢ =
  no-common-forall-forall-var1-var0ᵢ

endpointMlb-crossing-exposure-reversed-no-commonᵢ :
  ∀ {D} →
  idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ (`∀ (＇ 0)) ⊣ 0 →
  ¬ (idᵢ 0 ∣ 0 ⊢ D ⊑ `∀ (`∀ (＇ 1)) ⊣ 0)
endpointMlb-crossing-exposure-reversed-no-commonᵢ =
  no-common-forall-forall-var0-var1ᵢ

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
  endpointMlb ((`∀ (＇ 0)) ⇒ (`∀ ★)) ((`∀ (＇ 0)) ⇒ (`∀ ★)) ≡
  just ((`∀ (＇ 0)) ⇒ (`∀ ★))
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

endpointMlb-certified-bad-glb-pair :
  endpointMlbCommonLowerTy? 0 BadGlbLeftTy BadGlbRightTy ≡
  just BadGlbLowerTy
endpointMlb-certified-bad-glb-pair = refl

endpointMlb-certified-bad-glb-pair-reversed :
  endpointMlbCommonLowerTy? 0 BadGlbRightTy BadGlbLeftTy ≡
  just BadGlbLowerTy
endpointMlb-certified-bad-glb-pair-reversed = refl

endpointMlb-certified-repeated-one-sided :
  endpointMlbCommonLowerTy? 0 RepeatedOneSidedTy ★ ≡
  just RepeatedOneSidedTy
endpointMlb-certified-repeated-one-sided = refl

endpointMlb-bad-glb-commonᵢ :
  EndpointMlbCommonLowerᵢ 0 BadGlbLeftTy BadGlbRightTy
endpointMlb-bad-glb-commonᵢ =
  endpoint-common BadGlbLowerTy refl (glb-lower-XY⊑A , glb-lower-XY⊑B)

endpointMlb-bad-glb-reversed-commonᵢ :
  EndpointMlbCommonLowerᵢ 0 BadGlbRightTy BadGlbLeftTy
endpointMlb-bad-glb-reversed-commonᵢ =
  endpoint-common BadGlbLowerTy refl (glb-lower-XY⊑B , glb-lower-XY⊑A)

bad-glb-lower⊑selfᵢ :
  idᵢ 0 ∣ 0 ⊢ BadGlbLowerTy ⊑ BadGlbLowerTy ⊣ 0
bad-glb-lower⊑selfᵢ =
  ∀ⁱ (∀ⁱ
    ( idˣ (there (here refl)) (s<s z<s) (s<s z<s)
    ↦ idˣ (here refl) z<s z<s
    ))

bad-glb-left⊑starᵢ :
  idᵢ 0 ∣ 0 ⊢ BadGlbLeftTy ⊑ ★ ⊣ 0
bad-glb-left⊑starᵢ =
  ν refl (tag tagˣ (here refl) z<s ⇛ id★)

bad-glb-right⊑starᵢ :
  idᵢ 0 ∣ 0 ⊢ BadGlbRightTy ⊑ ★ ⊣ 0
bad-glb-right⊑starᵢ =
  ν refl (tag id★ ⇛ tagˣ (here refl) z<s)

bad-glb-lower⊑starᵢ :
  idᵢ 0 ∣ 0 ⊢ BadGlbLowerTy ⊑ ★ ⊣ 0
bad-glb-lower⊑starᵢ =
  ν refl
    (ν refl
      ( tag tagˣ (there (here refl)) (s<s z<s)
      ⇛ tagˣ (here refl) z<s
      ))

bad-glb-flipped-commonᵢ :
  CommonLowerBoundᵢ 0 BadGlbLeftTy BadGlbRightTy glb-lower-YX
bad-glb-flipped-commonᵢ = glb-lower-YX⊑A , glb-lower-YX⊑B

bad-glb-flipped-lower-not-above-selectedᵢ :
  ¬ (idᵢ 0 ∣ 0 ⊢ BadGlbLowerTy ⊑ glb-lower-YX ⊣ 0)
bad-glb-flipped-lower-not-above-selectedᵢ = glb-lower-XY⋢YX

bad-glb-endpoint-body-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = leftOnlyᵢ ∷ choice-idᵢ 0}
    (ν refl
      ( idˣ (there (here refl)) (s<s z<s) z<s
      ↦ tagˣ (here refl) z<s
      ))
    (∀ⁱ
      ( tagˣ (there (here refl)) (s<s z<s)
      ↦ idˣ (here refl) z<s z<s
      ))
bad-glb-endpoint-body-routeᵢ =
  sel-ν∀-arrow-arrowᵢ
    refl
    (sel-first-orderᵢ fo-var-starᵢ)
    (sel-first-orderᵢ fo-star-varᵢ)

bad-glb-reversed-endpoint-body-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = rightOnlyᵢ ∷ choice-idᵢ 0}
    (∀ⁱ
      ( tagˣ (there (here refl)) (s<s z<s)
      ↦ idˣ (here refl) z<s z<s
      ))
    (ν refl
      ( idˣ (there (here refl)) (s<s z<s) z<s
      ↦ tagˣ (here refl) z<s
      ))
bad-glb-reversed-endpoint-body-routeᵢ =
  sel-∀ν-arrow-arrowᵢ
    refl
    (sel-first-orderᵢ fo-star-varᵢ)
    (sel-first-orderᵢ fo-var-starᵢ)

bad-glb-reversed-endpoint-body-lowerᵢ :
  mlb-typeᵢ
    {Γ = rightOnlyᵢ ∷ choice-idᵢ 0}
    {Δᶜ = 1}
    {Δᴸ = 0}
    {Δᴿ = 1}
    {A = glb-bad-B}
    {B = (＇ 0) ⇒ ★}
    {C = `∀ ((＇ 1) ⇒ (＇ 0))}
    (∀ⁱ
      ( tagˣ (there (here refl)) (s<s z<s)
      ↦ idˣ (here refl) z<s z<s
      ))
    (ν refl
      ( idˣ (there (here refl)) (s<s z<s) z<s
      ↦ tagˣ (here refl) z<s
      ))
  ≡ `∀ ((＇ 1) ⇒ (＇ 0))
bad-glb-reversed-endpoint-body-lowerᵢ = refl

bad-glb-reversed-endpoint-body-comparable-lowerᵢ :
  cᶜ-lowerᵢ
    (proj₁
      (mlb-type-comparable-selectorᵢ
        bad-glb-reversed-endpoint-body-routeᵢ))
  ≡ `∀ ((＇ 1) ⇒ (＇ 0))
bad-glb-reversed-endpoint-body-comparable-lowerᵢ =
  trans
    (proj₂
      (mlb-type-comparable-selectorᵢ
        bad-glb-reversed-endpoint-body-routeᵢ))
    bad-glb-reversed-endpoint-body-lowerᵢ

bad-glb-endpoint-body-lowerᵢ :
  mlb-typeᵢ
    {Γ = leftOnlyᵢ ∷ choice-idᵢ 0}
    {Δᶜ = 1}
    {Δᴸ = 1}
    {Δᴿ = 0}
    {A = (＇ 0) ⇒ ★}
    {B = glb-bad-B}
    {C = `∀ ((＇ 1) ⇒ (＇ 0))}
    (ν refl
      ( idˣ (there (here refl)) (s<s z<s) z<s
      ↦ tagˣ (here refl) z<s
      ))
    (∀ⁱ
      ( tagˣ (there (here refl)) (s<s z<s)
      ↦ idˣ (here refl) z<s z<s
      ))
  ≡ `∀ ((＇ 1) ⇒ (＇ 0))
bad-glb-endpoint-body-lowerᵢ = refl

bad-glb-endpoint-body-comparable-lowerᵢ :
  cᶜ-lowerᵢ
    (proj₁
      (mlb-type-comparable-selectorᵢ bad-glb-endpoint-body-routeᵢ))
  ≡ `∀ ((＇ 1) ⇒ (＇ 0))
bad-glb-endpoint-body-comparable-lowerᵢ =
  trans
    (proj₂ (mlb-type-comparable-selectorᵢ bad-glb-endpoint-body-routeᵢ))
    bad-glb-endpoint-body-lowerᵢ

bad-glb-endpoint-body-∀ν-direct-∀lowerᵢ :
  ∀ {D} →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ ((＇ 0) ⇒ ★) ⊣ 1 →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ glb-bad-B ⊣ 0 →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢ `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 1 →
  idᵢ 0 ∣ 0 ⊢ `∀ D ⊑ glb-lower-XY ⊣ 0
bad-glb-endpoint-body-∀ν-direct-∀lowerᵢ {D = D} D⊑A D⊑B C⊑D =
  subst
    (λ C → idᵢ 0 ∣ 0 ⊢ `∀ D ⊑ `∀ C ⊣ 0)
    bad-glb-endpoint-body-comparable-lowerᵢ
    (∀ν-∀lower-directᵢ
      (proj₁
        (mlb-type-comparable-selectorᵢ bad-glb-endpoint-body-routeᵢ))
      D⊑A
      D⊑B
      C⊑D)

bad-glb-reversed-endpoint-body-ν∀-direct-∀lowerᵢ :
  ∀ {D} →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ glb-bad-B ⊣ 0 →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ ((＇ 0) ⇒ ★) ⊣ 1 →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢ `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 1 →
  idᵢ 0 ∣ 0 ⊢ `∀ D ⊑ glb-lower-XY ⊣ 0
bad-glb-reversed-endpoint-body-ν∀-direct-∀lowerᵢ
    {D = D} D⊑A D⊑B C⊑D =
  subst
    (λ C → idᵢ 0 ∣ 0 ⊢ `∀ D ⊑ `∀ C ⊣ 0)
    bad-glb-reversed-endpoint-body-comparable-lowerᵢ
    (ν∀-∀lower-directᵢ
      (proj₁
        (mlb-type-comparable-selectorᵢ
          bad-glb-reversed-endpoint-body-routeᵢ))
      D⊑A
      D⊑B
      C⊑D)

bad-glb-body-aligned-∀∀-impossibleᵢ :
  ∀ {D} →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ ((＇ 0) ⇒ ★) ⊣ 1 →
  ¬ (∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ (★ ⇒ (＇ 0)) ⊣ 1)
bad-glb-body-aligned-∀∀-impossibleᵢ =
  no-common-arrow-var-star-star-var-overlapᵢ
    (id-no-var-star-overlapᵢ 1)

bad-glb-selected-body-not-below-right-bodyᵢ :
  ¬
    (∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢
      `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ (★ ⇒ (＇ 0)) ⊣ 1)
bad-glb-selected-body-not-below-right-bodyᵢ (ν occ (p₁ ↦ p₂))
    with ⊑★-freshᵢ (νctx-no-star-sucᵢ ∀ctx-no-star-zeroᵢ) p₁
bad-glb-selected-body-not-below-right-bodyᵢ (ν occ (p₁ ↦ p₂))
    | ()

bad-glb-selected-body-not-below-left-forallᵢ :
  ¬
    (νᵢᶜ (idᵢ 0) ∣ 1 ⊢
      `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0)
bad-glb-selected-body-not-below-left-forallᵢ
    (∀ⁱ ((idˣ (there (here ())) _ _) ↦ p₂))
bad-glb-selected-body-not-below-left-forallᵢ (ν occ ())

bad-glb-body-erased-left-impossibleᵢ :
  ∀ {D} →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0 →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 1 →
  ⊥
bad-glb-body-erased-left-impossibleᵢ D⊑∀A C⊑D =
  bad-glb-selected-body-not-below-left-forallᵢ
    (⊑-trans-left-idᵢ C⊑D D⊑∀A)

bad-glb-endpoint-body-erased-left-impossible-∀lowerᵢ :
  ∀ {D} →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0 →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 1 →
  idᵢ 0 ∣ 0 ⊢ `∀ D ⊑ glb-lower-XY ⊣ 0
bad-glb-endpoint-body-erased-left-impossible-∀lowerᵢ D⊑∀A C⊑D =
  ⊥-elim (bad-glb-body-erased-left-impossibleᵢ D⊑∀A C⊑D)

bad-glb-body-erased-left-aligned-right-impossibleᵢ :
  ∀ {D} →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0 →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ (★ ⇒ (＇ 0)) ⊣ 1 →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 1 →
  ⊥
bad-glb-body-erased-left-aligned-right-impossibleᵢ
    D⊑∀A D⊑B C⊑D =
  bad-glb-selected-body-not-below-right-bodyᵢ
    (⊑-trans-left-idᵢ C⊑D D⊑B)

bad-glb-endpoint-body-ν∀-impossible-∀lowerᵢ :
  ∀ {D} →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0 →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ (★ ⇒ (＇ 0)) ⊣ 1 →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 1 →
  idᵢ 0 ∣ 0 ⊢ `∀ D ⊑ glb-lower-XY ⊣ 0
bad-glb-endpoint-body-ν∀-impossible-∀lowerᵢ D⊑∀A D⊑B C⊑D =
  ⊥-elim
    (bad-glb-body-erased-left-aligned-right-impossibleᵢ
      D⊑∀A
      D⊑B
      C⊑D)

bad-glb-endpoint-body-νν-impossible-∀lowerᵢ :
  ∀ {D} →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0 →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢ D ⊑ glb-bad-B ⊣ 0 →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 1 →
  idᵢ 0 ∣ 0 ⊢ `∀ D ⊑ glb-lower-XY ⊣ 0
bad-glb-endpoint-body-νν-impossible-∀lowerᵢ D⊑∀A D⊑B C⊑D =
  bad-glb-endpoint-body-erased-left-impossible-∀lowerᵢ
    D⊑∀A
    C⊑D

bad-glb-top-∀ν-∀lower-supportᵢ :
  ∀ {D} →
  CommonLowerBoundᶜᵢ
    (idᵢ 0) (idᵢ 0) 0 0 0
    (`∀ ((＇ 0) ⇒ ★))
    glb-bad-B
    (`∀ D) →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 1 →
  idᵢ 0 ∣ 0 ⊢ `∀ D ⊑ glb-lower-XY ⊣ 0
bad-glb-top-∀ν-∀lower-supportᵢ (∀ⁱ D⊑A , ∀ⁱ D⊑B) C⊑D =
  ⊥-elim (bad-glb-body-aligned-∀∀-impossibleᵢ D⊑A D⊑B)
bad-glb-top-∀ν-∀lower-supportᵢ (∀ⁱ D⊑A , ν occ D⊑B) C⊑D =
  bad-glb-endpoint-body-∀ν-direct-∀lowerᵢ D⊑A D⊑B C⊑D
bad-glb-top-∀ν-∀lower-supportᵢ (ν occ D⊑∀A , ∀ⁱ D⊑B) C⊑D =
  bad-glb-endpoint-body-ν∀-impossible-∀lowerᵢ D⊑∀A D⊑B C⊑D
bad-glb-top-∀ν-∀lower-supportᵢ (ν occ D⊑∀A , ν occ′ D⊑B) C⊑D =
  bad-glb-endpoint-body-νν-impossible-∀lowerᵢ D⊑∀A D⊑B C⊑D

bad-glb-top-∀ν-νlower-impossibleᵢ :
  ∀ {D} →
  CommonLowerBoundᶜᵢ
    (idᵢ 0) (idᵢ 0) 0 0 0
    (`∀ ((＇ 0) ⇒ ★))
    glb-bad-B
    D →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 0 →
  ⊥
bad-glb-top-∀ν-νlower-impossibleᵢ common C⊑D =
  bad-glb-selected-body-not-below-left-forallᵢ
    (⊑-trans-composeᵢ
      (compose-νidᵢ (compose-idᵢ 0))
      C⊑D
      (proj₁ common))

bad-glb-top-∀ν-νlower-supportᵢ :
  ∀ {D} →
  CommonLowerBoundᶜᵢ
    (idᵢ 0) (idᵢ 0) 0 0 0
    (`∀ ((＇ 0) ⇒ ★))
    glb-bad-B
    D →
  occurs 0 (`∀ ((＇ 1) ⇒ (＇ 0))) ≡ true →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 0 →
  idᵢ 0 ∣ 0 ⊢ D ⊑ glb-lower-XY ⊣ 0
bad-glb-top-∀ν-νlower-supportᵢ common occC C⊑D =
  ⊥-elim (bad-glb-top-∀ν-νlower-impossibleᵢ common C⊑D)

bad-glb-top-∀ν-supportᵢ :
  ForallNuComparableSupportᵢ
    (idᵢ 0) (idᵢ 0) (idᵢ 0) 0 0 0
    ((＇ 0) ⇒ ★)
    glb-bad-B
    (`∀ ((＇ 1) ⇒ (＇ 0)))
bad-glb-top-∀ν-supportᵢ =
  record
    { ∀ν-∀lower-supportᵢ = bad-glb-top-∀ν-∀lower-supportᵢ
    ; ∀ν-νlower-supportᵢ = bad-glb-top-∀ν-νlower-supportᵢ
    }

bad-glb-reversed-top-ν∀-∀lower-supportᵢ :
  ∀ {D} →
  CommonLowerBoundᶜᵢ
    (idᵢ 0) (idᵢ 0) 0 0 0
    glb-bad-B
    (`∀ ((＇ 0) ⇒ ★))
    (`∀ D) →
  ∀ᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 1 →
  idᵢ 0 ∣ 0 ⊢ `∀ D ⊑ glb-lower-XY ⊣ 0
bad-glb-reversed-top-ν∀-∀lower-supportᵢ
    (∀ⁱ D⊑A , ∀ⁱ D⊑B) C⊑D =
  ⊥-elim (bad-glb-body-aligned-∀∀-impossibleᵢ D⊑B D⊑A)
bad-glb-reversed-top-ν∀-∀lower-supportᵢ
    (∀ⁱ D⊑A , ν occ D⊑∀B) C⊑D =
  ⊥-elim (bad-glb-body-erased-left-impossibleᵢ D⊑∀B C⊑D)
bad-glb-reversed-top-ν∀-∀lower-supportᵢ
    (ν occ D⊑A , ∀ⁱ D⊑B) C⊑D =
  bad-glb-reversed-endpoint-body-ν∀-direct-∀lowerᵢ
    D⊑A
    D⊑B
    C⊑D
bad-glb-reversed-top-ν∀-∀lower-supportᵢ
    (ν occ D⊑A , ν occ′ D⊑∀B) C⊑D =
  ⊥-elim (bad-glb-body-erased-left-impossibleᵢ D⊑∀B C⊑D)

bad-glb-reversed-top-ν∀-νlower-impossibleᵢ :
  ∀ {D} →
  CommonLowerBoundᶜᵢ
    (idᵢ 0) (idᵢ 0) 0 0 0
    glb-bad-B
    (`∀ ((＇ 0) ⇒ ★))
    D →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 0 →
  ⊥
bad-glb-reversed-top-ν∀-νlower-impossibleᵢ common C⊑D =
  bad-glb-selected-body-not-below-left-forallᵢ
    (⊑-trans-composeᵢ
      (compose-νidᵢ (compose-idᵢ 0))
      C⊑D
      (proj₂ common))

bad-glb-reversed-top-ν∀-νlower-supportᵢ :
  ∀ {D} →
  CommonLowerBoundᶜᵢ
    (idᵢ 0) (idᵢ 0) 0 0 0
    glb-bad-B
    (`∀ ((＇ 0) ⇒ ★))
    D →
  occurs 0 (`∀ ((＇ 1) ⇒ (＇ 0))) ≡ true →
  νᵢᶜ (idᵢ 0) ∣ 1 ⊢
    `∀ ((＇ 1) ⇒ (＇ 0)) ⊑ D ⊣ 0 →
  idᵢ 0 ∣ 0 ⊢ D ⊑ glb-lower-XY ⊣ 0
bad-glb-reversed-top-ν∀-νlower-supportᵢ common occC C⊑D =
  ⊥-elim (bad-glb-reversed-top-ν∀-νlower-impossibleᵢ common C⊑D)

bad-glb-reversed-top-ν∀-supportᵢ :
  NuForallComparableSupportᵢ
    (idᵢ 0) (idᵢ 0) (idᵢ 0) 0 0 0
    glb-bad-B
    ((＇ 0) ⇒ ★)
    (`∀ ((＇ 1) ⇒ (＇ 0)))
bad-glb-reversed-top-ν∀-supportᵢ =
  record
    { ν∀-∀lower-supportᵢ = bad-glb-reversed-top-ν∀-∀lower-supportᵢ
    ; ν∀-νlower-supportᵢ = bad-glb-reversed-top-ν∀-νlower-supportᵢ
    }

first-use-exposure⊑selfᵢ :
  idᵢ 0 ∣ 0 ⊢ FirstUseExposureTy ⊑ FirstUseExposureTy ⊣ 0
first-use-exposure⊑selfᵢ =
  ∀ⁱ (∀ⁱ
    ( idˣ (here refl) z<s z<s
    ↦ idˣ (there (here refl)) (s<s z<s) (s<s z<s)
    ))

first-use-exposure⊑starᵢ :
  idᵢ 0 ∣ 0 ⊢ FirstUseExposureTy ⊑ ★ ⊣ 0
first-use-exposure⊑starᵢ =
  ν refl
    (ν refl
      ( tag tagˣ (here refl) z<s
      ⇛ tagˣ (there (here refl)) (s<s z<s)
      ))

endpointMlb-first-use-exposure-commonᵢ :
  EndpointMlbCommonLowerᵢ 0 ★ FirstUseExposureTy
endpointMlb-first-use-exposure-commonᵢ =
  endpoint-common
    FirstUseExposureTy
    refl
    (first-use-exposure⊑starᵢ , first-use-exposure⊑selfᵢ)

endpointMlb-first-use-exposure-reversed-commonᵢ :
  EndpointMlbCommonLowerᵢ 0 FirstUseExposureTy ★
endpointMlb-first-use-exposure-reversed-commonᵢ =
  endpoint-common
    FirstUseExposureTy
    refl
    (first-use-exposure⊑selfᵢ , first-use-exposure⊑starᵢ)

repeated-one-sided⊑selfᵢ :
  idᵢ 0 ∣ 0 ⊢ RepeatedOneSidedTy ⊑ RepeatedOneSidedTy ⊣ 0
repeated-one-sided⊑selfᵢ =
  ∀ⁱ
    ( idˣ (here refl) z<s z<s
    ↦ idˣ (here refl) z<s z<s
    )

repeated-one-sided⊑starᵢ :
  idᵢ 0 ∣ 0 ⊢ RepeatedOneSidedTy ⊑ ★ ⊣ 0
repeated-one-sided⊑starᵢ =
  ν refl
    ( tag tagˣ (here refl) z<s
    ⇛ tagˣ (here refl) z<s
    )

endpointMlb-repeated-one-sided-commonᵢ :
  EndpointMlbCommonLowerᵢ 0 RepeatedOneSidedTy ★
endpointMlb-repeated-one-sided-commonᵢ =
  endpoint-common
    RepeatedOneSidedTy
    refl
    (repeated-one-sided⊑selfᵢ , repeated-one-sided⊑starᵢ)

endpointMlb-certified-base-star :
  endpointMlbCommonLowerTy? 0 NatTy ★ ≡ just NatTy
endpointMlb-certified-base-star = refl

endpointMlb-certified-star-base :
  endpointMlbCommonLowerTy? 0 ★ BoolTy ≡ just BoolTy
endpointMlb-certified-star-base = refl

endpointMlb-certified-unused-left-fails :
  endpointMlbCommonLowerTy? 0 (`∀ ★) ★ ≡ nothing
endpointMlb-certified-unused-left-fails = refl

endpointMlb-certified-unused-base-left-fails :
  endpointMlbCommonLowerTy? 0 (`∀ NatTy) ★ ≡ nothing
endpointMlb-certified-unused-base-left-fails = refl

endpointMlb-certified-unused-base-right-fails :
  endpointMlbCommonLowerTy? 0 ★ (`∀ NatTy) ≡ nothing
endpointMlb-certified-unused-base-right-fails = refl

endpointMlb-certified-unused-base-arrow-left-fails :
  endpointMlbCommonLowerTy? 0 (`∀ (NatTy ⇒ BoolTy)) ★ ≡ nothing
endpointMlb-certified-unused-base-arrow-left-fails = refl

endpointMlb-certified-unused-base-arrow-right-fails :
  endpointMlbCommonLowerTy? 0 ★ (`∀ (NatTy ⇒ BoolTy)) ≡ nothing
endpointMlb-certified-unused-base-arrow-right-fails = refl

endpointMlb-failure-base-mismatch-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 NatTy BoolTy
endpointMlb-failure-base-mismatch-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-base-mismatch-ℕ𝔹ᵢ

endpointMlb-failure-base-mismatch-reversed-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 BoolTy NatTy
endpointMlb-failure-base-mismatch-reversed-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-base-mismatch-𝔹ℕᵢ

endpointMlb-failure-forall-base-mismatch-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (`∀ NatTy) (`∀ BoolTy)
endpointMlb-failure-forall-base-mismatch-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-base-mismatch-ℕ𝔹ᵢ

endpointMlb-failure-forall-base-mismatch-reversed-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (`∀ BoolTy) (`∀ NatTy)
endpointMlb-failure-forall-base-mismatch-reversed-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-base-mismatch-𝔹ℕᵢ

endpointMlb-generic-failure-forall-star-star-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (`∀ ★) ★
endpointMlb-generic-failure-forall-star-star-targetᵢ =
  endpoint-failure-complete-targetᵢ
    (endpoint-failure-forall-fresh-target-starᵢ
      refl
      (λ p → ⊑★-freshᵢ ∀ctx-no-star-zeroᵢ p))

endpointMlb-generic-failure-forall-base-star-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (`∀ NatTy) ★
endpointMlb-generic-failure-forall-base-star-targetᵢ =
  endpoint-failure-complete-targetᵢ
    (endpoint-failure-forall-fresh-target-starᵢ
      refl
      (λ p → ⊑-to-base-occurs-falseᵢ 0 p))

endpointMlb-generic-failure-star-forall-base-arrow-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 ★ (`∀ (NatTy ⇒ BoolTy))
endpointMlb-generic-failure-star-forall-base-arrow-targetᵢ =
  endpoint-failure-complete-targetᵢ
    (endpoint-failure-star-forall-fresh-targetᵢ
      refl
      (λ p → ⊑-to-base-arrow-occurs-falseᵢ 0 p))

endpointMlb-failure-repeated-one-sided-unused-targetᵢ :
  EndpointMlbFailureCompleteᵢ
    0
    (`∀ ((＇ 0) ⇒ (＇ 0)))
    (`∀ (★ ⇒ ★))
endpointMlb-failure-repeated-one-sided-unused-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-arrow-var-var-star-starᵢ

endpointMlb-failure-repeated-one-sided-unused-reversed-targetᵢ :
  EndpointMlbFailureCompleteᵢ
    0
    (`∀ (★ ⇒ ★))
    (`∀ ((＇ 0) ⇒ (＇ 0)))
endpointMlb-failure-repeated-one-sided-unused-reversed-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-arrow-star-star-var-varᵢ

endpointMlb-failure-shared-and-one-sided-targetᵢ :
  EndpointMlbFailureCompleteᵢ
    0
    (`∀ ((＇ 0) ⇒ (＇ 0)))
    (`∀ ((＇ 0) ⇒ ★))
endpointMlb-failure-shared-and-one-sided-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-arrow-var-var-var-starᵢ

endpointMlb-failure-shared-and-one-sided-reversed-targetᵢ :
  EndpointMlbFailureCompleteᵢ
    0
    (`∀ ((＇ 0) ⇒ ★))
    (`∀ ((＇ 0) ⇒ (＇ 0)))
endpointMlb-failure-shared-and-one-sided-reversed-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-arrow-var-star-var-varᵢ

endpointMlb-failure-one-right-two-left-targetᵢ :
  EndpointMlbFailureCompleteᵢ
    0
    (`∀ (`∀ ((＇ 1) ⇒ (＇ 0))))
    (`∀ ((＇ 0) ⇒ (＇ 0)))
endpointMlb-failure-one-right-two-left-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ

endpointMlb-failure-one-left-two-right-targetᵢ :
  EndpointMlbFailureCompleteᵢ
    0
    (`∀ ((＇ 0) ⇒ (＇ 0)))
    (`∀ (`∀ ((＇ 1) ⇒ (＇ 0))))
endpointMlb-failure-one-left-two-right-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-arrow-var0-var0-forall-forall-arrow-var1-var0ᵢ

endpointMlb-failure-crossing-exposure-targetᵢ :
  EndpointMlbFailureCompleteᵢ
    0
    (`∀ (`∀ (＇ 1)))
    (`∀ (`∀ (＇ 0)))
endpointMlb-failure-crossing-exposure-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-forall-var1-var0ᵢ

endpointMlb-failure-crossing-exposure-reversed-targetᵢ :
  EndpointMlbFailureCompleteᵢ
    0
    (`∀ (`∀ (＇ 0)))
    (`∀ (`∀ (＇ 1)))
endpointMlb-failure-crossing-exposure-reversed-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-forall-var0-var1ᵢ

endpointMlb-failure-var-base-targetᵢ :
  EndpointMlbFailureCompleteᵢ 1 (＇ 0) NatTy
endpointMlb-failure-var-base-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-var-baseᵢ

endpointMlb-failure-base-var-targetᵢ :
  EndpointMlbFailureCompleteᵢ 1 BoolTy (＇ 0)
endpointMlb-failure-base-var-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-base-varᵢ

endpointMlb-failure-var-star-targetᵢ :
  EndpointMlbFailureCompleteᵢ 1 (＇ 0) ★
endpointMlb-failure-var-star-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-var-starᵢ

endpointMlb-failure-star-var-targetᵢ :
  EndpointMlbFailureCompleteᵢ 1 ★ (＇ 0)
endpointMlb-failure-star-var-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-star-varᵢ

endpointMlb-failure-unused-left-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (`∀ ★) ★
endpointMlb-failure-unused-left-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-forall-star-starᵢ

endpointMlb-failure-unused-right-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 ★ (`∀ ★)
endpointMlb-failure-unused-right-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-star-forall-starᵢ

endpointMlb-failure-unused-base-left-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (`∀ NatTy) ★
endpointMlb-failure-unused-base-left-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-forall-base-starᵢ

endpointMlb-failure-unused-base-right-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 ★ (`∀ NatTy)
endpointMlb-failure-unused-base-right-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-star-forall-baseᵢ

endpointMlb-failure-unused-base-arrow-left-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (`∀ (NatTy ⇒ BoolTy)) ★
endpointMlb-failure-unused-base-arrow-left-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-forall-base-arrow-starᵢ

endpointMlb-failure-unused-base-arrow-right-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 ★ (`∀ (NatTy ⇒ BoolTy))
endpointMlb-failure-unused-base-arrow-right-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-star-forall-base-arrowᵢ

endpointMlb-failure-base-arrow-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 NatTy (NatTy ⇒ BoolTy)
endpointMlb-failure-base-arrow-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-base-arrowᵢ

endpointMlb-failure-arrow-base-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (NatTy ⇒ BoolTy) BoolTy
endpointMlb-failure-arrow-base-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-arrow-baseᵢ

endpointMlb-failure-var-arrow-targetᵢ :
  EndpointMlbFailureCompleteᵢ 1 (＇ 0) (NatTy ⇒ BoolTy)
endpointMlb-failure-var-arrow-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-var-arrowᵢ

endpointMlb-failure-arrow-var-targetᵢ :
  EndpointMlbFailureCompleteᵢ 1 (NatTy ⇒ BoolTy) (＇ 0)
endpointMlb-failure-arrow-var-targetᵢ =
  endpoint-failure-complete-targetᵢ endpoint-failure-arrow-varᵢ

endpointMlb-failure-arrow-arrow-domain-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (NatTy ⇒ NatTy) (BoolTy ⇒ NatTy)
endpointMlb-failure-arrow-arrow-domain-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-domain-ℕ𝔹ᵢ

endpointMlb-failure-arrow-arrow-domain-reversed-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (BoolTy ⇒ NatTy) (NatTy ⇒ NatTy)
endpointMlb-failure-arrow-arrow-domain-reversed-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-domain-𝔹ℕᵢ

endpointMlb-failure-arrow-arrow-codomain-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ NatTy) (★ ⇒ BoolTy)
endpointMlb-failure-arrow-arrow-codomain-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-codomain-ℕ𝔹ᵢ

endpointMlb-failure-arrow-arrow-codomain-reversed-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ BoolTy) (★ ⇒ NatTy)
endpointMlb-failure-arrow-arrow-codomain-reversed-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-codomain-𝔹ℕᵢ

endpointMlb-failure-arrow-arrow-domain-forall-left-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (((`∀ ★)) ⇒ ★) (★ ⇒ ★)
endpointMlb-failure-arrow-arrow-domain-forall-left-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-domain-forall-star-leftᵢ

endpointMlb-failure-arrow-arrow-domain-forall-right-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ ★) (((`∀ ★)) ⇒ ★)
endpointMlb-failure-arrow-arrow-domain-forall-right-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-domain-forall-star-rightᵢ

endpointMlb-failure-arrow-arrow-codomain-forall-left-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ (`∀ ★)) (★ ⇒ ★)
endpointMlb-failure-arrow-arrow-codomain-forall-left-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-codomain-forall-star-leftᵢ

endpointMlb-failure-arrow-arrow-codomain-forall-right-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ ★) (★ ⇒ (`∀ ★))
endpointMlb-failure-arrow-arrow-codomain-forall-right-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-codomain-forall-star-rightᵢ

endpointMlb-failure-arrow-arrow-domain-forall-base-left-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (((`∀ NatTy)) ⇒ ★) (★ ⇒ ★)
endpointMlb-failure-arrow-arrow-domain-forall-base-left-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-domain-forall-base-leftᵢ

endpointMlb-failure-arrow-arrow-domain-forall-base-right-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ ★) (((`∀ NatTy)) ⇒ ★)
endpointMlb-failure-arrow-arrow-domain-forall-base-right-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-domain-forall-base-rightᵢ

endpointMlb-failure-arrow-arrow-codomain-forall-base-left-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ (`∀ NatTy)) (★ ⇒ ★)
endpointMlb-failure-arrow-arrow-codomain-forall-base-left-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-codomain-forall-base-leftᵢ

endpointMlb-failure-arrow-arrow-codomain-forall-base-right-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ ★) (★ ⇒ (`∀ NatTy))
endpointMlb-failure-arrow-arrow-codomain-forall-base-right-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-codomain-forall-base-rightᵢ

endpointMlb-failure-arrow-arrow-domain-forall-base-arrow-left-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (((`∀ (NatTy ⇒ BoolTy))) ⇒ ★) (★ ⇒ ★)
endpointMlb-failure-arrow-arrow-domain-forall-base-arrow-left-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-domain-forall-base-arrow-leftᵢ

endpointMlb-failure-arrow-arrow-domain-forall-base-arrow-right-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ ★) (((`∀ (NatTy ⇒ BoolTy))) ⇒ ★)
endpointMlb-failure-arrow-arrow-domain-forall-base-arrow-right-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-domain-forall-base-arrow-rightᵢ

endpointMlb-failure-arrow-arrow-codomain-forall-base-arrow-left-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ (`∀ (NatTy ⇒ BoolTy))) (★ ⇒ ★)
endpointMlb-failure-arrow-arrow-codomain-forall-base-arrow-left-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-codomain-forall-base-arrow-leftᵢ

endpointMlb-failure-arrow-arrow-codomain-forall-base-arrow-right-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ ★) (★ ⇒ (`∀ (NatTy ⇒ BoolTy)))
endpointMlb-failure-arrow-arrow-codomain-forall-base-arrow-right-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-arrow-codomain-forall-base-arrow-rightᵢ

endpointMlb-failure-arrow-star-domain-forall-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (((`∀ ★)) ⇒ ★) ★
endpointMlb-failure-arrow-star-domain-forall-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-star-domain-forall-starᵢ

endpointMlb-failure-arrow-star-codomain-forall-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ (`∀ ★)) ★
endpointMlb-failure-arrow-star-codomain-forall-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-star-codomain-forall-starᵢ

endpointMlb-failure-star-arrow-domain-forall-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 ★ (((`∀ ★)) ⇒ ★)
endpointMlb-failure-star-arrow-domain-forall-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-star-arrow-domain-forall-starᵢ

endpointMlb-failure-star-arrow-codomain-forall-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 ★ (★ ⇒ (`∀ ★))
endpointMlb-failure-star-arrow-codomain-forall-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-star-arrow-codomain-forall-starᵢ

endpointMlb-failure-arrow-star-domain-forall-base-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (((`∀ NatTy)) ⇒ ★) ★
endpointMlb-failure-arrow-star-domain-forall-base-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-star-domain-forall-baseᵢ

endpointMlb-failure-arrow-star-codomain-forall-base-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ (`∀ NatTy)) ★
endpointMlb-failure-arrow-star-codomain-forall-base-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-star-codomain-forall-baseᵢ

endpointMlb-failure-star-arrow-domain-forall-base-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 ★ (((`∀ NatTy)) ⇒ ★)
endpointMlb-failure-star-arrow-domain-forall-base-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-star-arrow-domain-forall-baseᵢ

endpointMlb-failure-star-arrow-codomain-forall-base-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 ★ (★ ⇒ (`∀ NatTy))
endpointMlb-failure-star-arrow-codomain-forall-base-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-star-arrow-codomain-forall-baseᵢ

endpointMlb-failure-arrow-star-domain-forall-base-arrow-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (((`∀ (NatTy ⇒ BoolTy))) ⇒ ★) ★
endpointMlb-failure-arrow-star-domain-forall-base-arrow-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-star-domain-forall-base-arrowᵢ

endpointMlb-failure-arrow-star-codomain-forall-base-arrow-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 (★ ⇒ (`∀ (NatTy ⇒ BoolTy))) ★
endpointMlb-failure-arrow-star-codomain-forall-base-arrow-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-arrow-star-codomain-forall-base-arrowᵢ

endpointMlb-failure-star-arrow-domain-forall-base-arrow-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 ★ (((`∀ (NatTy ⇒ BoolTy))) ⇒ ★)
endpointMlb-failure-star-arrow-domain-forall-base-arrow-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-star-arrow-domain-forall-base-arrowᵢ

endpointMlb-failure-star-arrow-codomain-forall-base-arrow-targetᵢ :
  EndpointMlbFailureCompleteᵢ 0 ★ (★ ⇒ (`∀ (NatTy ⇒ BoolTy)))
endpointMlb-failure-star-arrow-codomain-forall-base-arrow-targetᵢ =
  endpoint-failure-complete-targetᵢ
    endpoint-failure-star-arrow-codomain-forall-base-arrowᵢ

endpointMlb-sound-star-star-targetᵢ :
  EndpointMlbSoundᵢ 0 ★ ★
endpointMlb-sound-star-star-targetᵢ =
  endpoint-comparable-sound-targetᵢ endpoint-comparable-star-starᵢ

endpointMlb-maximal-star-star-targetᵢ :
  EndpointMlbMaximalᵢ 0 ★ ★
endpointMlb-maximal-star-star-targetᵢ =
  endpoint-comparable-maximal-targetᵢ endpoint-comparable-star-starᵢ

endpointMlb-sound-base-base-targetᵢ :
  EndpointMlbSoundᵢ 0 NatTy NatTy
endpointMlb-sound-base-base-targetᵢ =
  endpoint-comparable-sound-targetᵢ endpoint-comparable-base-baseᵢ

endpointMlb-maximal-base-base-targetᵢ :
  EndpointMlbMaximalᵢ 0 NatTy NatTy
endpointMlb-maximal-base-base-targetᵢ =
  endpoint-comparable-maximal-targetᵢ endpoint-comparable-base-baseᵢ

endpointMlb-sound-base-base-under∀-targetᵢ :
  EndpointMlbSoundᵢ 1 NatTy NatTy
endpointMlb-sound-base-base-under∀-targetᵢ =
  endpoint-comparable-sound-targetᵢ endpoint-comparable-base-baseᵢ

endpointMlb-sound-base-star-targetᵢ :
  EndpointMlbSoundᵢ 0 NatTy ★
endpointMlb-sound-base-star-targetᵢ =
  endpoint-comparable-sound-targetᵢ endpoint-comparable-base-starᵢ

endpointMlb-maximal-base-star-targetᵢ :
  EndpointMlbMaximalᵢ 0 NatTy ★
endpointMlb-maximal-base-star-targetᵢ =
  endpoint-comparable-maximal-targetᵢ endpoint-comparable-base-starᵢ

endpointMlb-sound-star-base-targetᵢ :
  EndpointMlbSoundᵢ 0 ★ BoolTy
endpointMlb-sound-star-base-targetᵢ =
  endpoint-comparable-sound-targetᵢ endpoint-comparable-star-baseᵢ

endpointMlb-maximal-star-base-targetᵢ :
  EndpointMlbMaximalᵢ 0 ★ BoolTy
endpointMlb-maximal-star-base-targetᵢ =
  endpoint-comparable-maximal-targetᵢ endpoint-comparable-star-baseᵢ

endpointMlb-sound-star-nat-targetᵢ :
  EndpointMlbSoundᵢ 0 ★ NatTy
endpointMlb-sound-star-nat-targetᵢ =
  endpoint-comparable-sound-targetᵢ endpoint-comparable-star-baseᵢ

endpointMlb-maximal-star-nat-targetᵢ :
  EndpointMlbMaximalᵢ 0 ★ NatTy
endpointMlb-maximal-star-nat-targetᵢ =
  endpoint-comparable-maximal-targetᵢ endpoint-comparable-star-baseᵢ

endpointMlb-sound-free-var-one-targetᵢ :
  EndpointMlbSoundᵢ 2 (＇ 1) (＇ 1)
endpointMlb-sound-free-var-one-targetᵢ =
  endpoint-comparable-sound-targetᵢ
    (endpoint-comparable-var-varᵢ (s<s z<s))

endpointMlb-sound-free-var-zero-under-two-targetᵢ :
  EndpointMlbSoundᵢ 2 (＇ 0) (＇ 0)
endpointMlb-sound-free-var-zero-under-two-targetᵢ =
  endpoint-comparable-sound-targetᵢ
    (endpoint-comparable-var-varᵢ z<s)

endpointMlb-maximal-free-var-one-targetᵢ :
  EndpointMlbMaximalᵢ 2 (＇ 1) (＇ 1)
endpointMlb-maximal-free-var-one-targetᵢ =
  endpoint-comparable-maximal-targetᵢ
    (endpoint-comparable-var-varᵢ (s<s z<s))

endpointMlb-maximal-free-var-zero-under-two-targetᵢ :
  EndpointMlbMaximalᵢ 2 (＇ 0) (＇ 0)
endpointMlb-maximal-free-var-zero-under-two-targetᵢ =
  endpoint-comparable-maximal-targetᵢ
    (endpoint-comparable-var-varᵢ z<s)

endpointMlb-sound-free-var-zero-under-one-targetᵢ :
  EndpointMlbSoundᵢ 1 (＇ 0) (＇ 0)
endpointMlb-sound-free-var-zero-under-one-targetᵢ =
  endpoint-comparable-sound-targetᵢ
    (endpoint-comparable-var-varᵢ z<s)

endpointMlb-maximal-free-var-zero-under-one-targetᵢ :
  EndpointMlbMaximalᵢ 1 (＇ 0) (＇ 0)
endpointMlb-maximal-free-var-zero-under-one-targetᵢ =
  endpoint-comparable-maximal-targetᵢ
    (endpoint-comparable-var-varᵢ z<s)

endpointMlb-sound-arrow-star-targetᵢ :
  EndpointMlbSoundᵢ 0 (NatTy ⇒ BoolTy) ★
endpointMlb-sound-arrow-star-targetᵢ =
  endpoint-comparable-sound-targetᵢ
    (endpoint-comparable-arrow-starᵢ
      endpoint-comparable-base-starᵢ
      endpoint-comparable-base-starᵢ
      refl)

endpointMlb-maximal-arrow-star-targetᵢ :
  EndpointMlbMaximalᵢ 0 (NatTy ⇒ BoolTy) ★
endpointMlb-maximal-arrow-star-targetᵢ =
  endpoint-comparable-maximal-targetᵢ
    (endpoint-comparable-arrow-starᵢ
      endpoint-comparable-base-starᵢ
      endpoint-comparable-base-starᵢ
      refl)

endpointMlb-sound-star-arrow-targetᵢ :
  EndpointMlbSoundᵢ 0 ★ (NatTy ⇒ BoolTy)
endpointMlb-sound-star-arrow-targetᵢ =
  endpoint-comparable-sound-targetᵢ
    (endpoint-comparable-star-arrowᵢ
      endpoint-comparable-star-baseᵢ
      endpoint-comparable-star-baseᵢ
      refl)

endpointMlb-maximal-star-arrow-targetᵢ :
  EndpointMlbMaximalᵢ 0 ★ (NatTy ⇒ BoolTy)
endpointMlb-maximal-star-arrow-targetᵢ =
  endpoint-comparable-maximal-targetᵢ
    (endpoint-comparable-star-arrowᵢ
      endpoint-comparable-star-baseᵢ
      endpoint-comparable-star-baseᵢ
      refl)

endpointMlb-sound-arrow-arrow-targetᵢ :
  EndpointMlbSoundᵢ 0 (NatTy ⇒ BoolTy) (NatTy ⇒ BoolTy)
endpointMlb-sound-arrow-arrow-targetᵢ =
  endpoint-comparable-sound-targetᵢ
    (endpoint-comparable-arrow-arrowᵢ
      endpoint-comparable-base-baseᵢ
      endpoint-comparable-base-baseᵢ
      refl)

endpointMlb-maximal-arrow-arrow-targetᵢ :
  EndpointMlbMaximalᵢ 0 (NatTy ⇒ BoolTy) (NatTy ⇒ BoolTy)
endpointMlb-maximal-arrow-arrow-targetᵢ =
  endpoint-comparable-maximal-targetᵢ
    (endpoint-comparable-arrow-arrowᵢ
      endpoint-comparable-base-baseᵢ
      endpoint-comparable-base-baseᵢ
      refl)

endpointMlb-sound-arrow-arrow-structural-targetᵢ :
  EndpointMlbSoundᵢ 0 (NatTy ⇒ NatTy) (NatTy ⇒ NatTy)
endpointMlb-sound-arrow-arrow-structural-targetᵢ =
  endpoint-arrow-arrow-sound-targetᵢ
    endpointMlb-sound-base-base-targetᵢ
    endpointMlb-sound-base-base-targetᵢ
    refl
    refl
    refl

endpointMlb-maximal-arrow-arrow-structural-targetᵢ :
  EndpointMlbMaximalᵢ 0 (NatTy ⇒ NatTy) (NatTy ⇒ NatTy)
endpointMlb-maximal-arrow-arrow-structural-targetᵢ =
  endpoint-arrow-arrow-maximal-targetᵢ
    endpointMlb-maximal-base-base-targetᵢ
    endpointMlb-maximal-base-base-targetᵢ
    refl
    refl
    refl

endpointMlb-sound-arrow-star-structural-targetᵢ :
  EndpointMlbSoundᵢ 0 (NatTy ⇒ NatTy) ★
endpointMlb-sound-arrow-star-structural-targetᵢ =
  endpoint-arrow-star-sound-targetᵢ
    endpointMlb-sound-base-star-targetᵢ
    endpointMlb-sound-base-star-targetᵢ
    refl
    refl
    refl

endpointMlb-maximal-arrow-star-structural-targetᵢ :
  EndpointMlbMaximalᵢ 0 (NatTy ⇒ NatTy) ★
endpointMlb-maximal-arrow-star-structural-targetᵢ =
  endpoint-arrow-star-maximal-targetᵢ
    endpointMlb-maximal-base-star-targetᵢ
    endpointMlb-maximal-base-star-targetᵢ
    refl
    refl
    refl

endpointMlb-sound-star-arrow-structural-targetᵢ :
  EndpointMlbSoundᵢ 0 ★ (NatTy ⇒ NatTy)
endpointMlb-sound-star-arrow-structural-targetᵢ =
  endpoint-star-arrow-sound-targetᵢ
    endpointMlb-sound-star-nat-targetᵢ
    endpointMlb-sound-star-nat-targetᵢ
    refl
    refl
    refl

endpointMlb-maximal-star-arrow-structural-targetᵢ :
  EndpointMlbMaximalᵢ 0 ★ (NatTy ⇒ NatTy)
endpointMlb-maximal-star-arrow-structural-targetᵢ =
  endpoint-star-arrow-maximal-targetᵢ
    endpointMlb-maximal-star-nat-targetᵢ
    endpointMlb-maximal-star-nat-targetᵢ
    refl
    refl
    refl

endpointMlb-sound-matching-two-binder-arrow-targetᵢ :
  EndpointMlbSoundᵢ
    2
    ((＇ 1) ⇒ (＇ 0))
    ((＇ 1) ⇒ (＇ 0))
endpointMlb-sound-matching-two-binder-arrow-targetᵢ =
  endpoint-arrow-arrow-sound-targetᵢ
    endpointMlb-sound-free-var-one-targetᵢ
    endpointMlb-sound-free-var-zero-under-two-targetᵢ
    refl
    refl
    refl

endpointMlb-maximal-matching-two-binder-arrow-targetᵢ :
  EndpointMlbMaximalᵢ
    2
    ((＇ 1) ⇒ (＇ 0))
    ((＇ 1) ⇒ (＇ 0))
endpointMlb-maximal-matching-two-binder-arrow-targetᵢ =
  endpoint-arrow-arrow-maximal-targetᵢ
    endpointMlb-maximal-free-var-one-targetᵢ
    endpointMlb-maximal-free-var-zero-under-two-targetᵢ
    refl
    refl
    refl

endpointMlb-sound-matching-two-binder-inner-targetᵢ :
  EndpointMlbSoundᵢ
    1
    (`∀ ((＇ 1) ⇒ (＇ 0)))
    (`∀ ((＇ 1) ⇒ (＇ 0)))
endpointMlb-sound-matching-two-binder-inner-targetᵢ =
  endpoint-forall-forall-sound-targetᵢ
    endpointMlb-sound-matching-two-binder-arrow-targetᵢ
    refl
    refl

endpointMlb-maximal-matching-two-binder-inner-targetᵢ :
  EndpointMlbMaximalᵢ
    1
    (`∀ ((＇ 1) ⇒ (＇ 0)))
    (`∀ ((＇ 1) ⇒ (＇ 0)))
endpointMlb-maximal-matching-two-binder-inner-targetᵢ =
  endpoint-forall-forall-supported-maximal-targetᵢ
    (endpoint-comparable-arrow-arrowᵢ
      (endpoint-comparable-var-varᵢ (s<s z<s))
      (endpoint-comparable-var-varᵢ z<s)
      refl)
    (canonical-first-order-∀∀-supportᵢ
      (can-arrow-arrow
        (can-var-var (s<s z<s))
        (can-var-var z<s)))
    refl

endpointMlb-comparable-matching-two-binder-inner-targetᵢ :
  EndpointMlbComparableᵢ
    1
    (`∀ ((＇ 1) ⇒ (＇ 0)))
    (`∀ ((＇ 1) ⇒ (＇ 0)))
endpointMlb-comparable-matching-two-binder-inner-targetᵢ =
  endpoint-comparable-forall-forall-from-supportᵢ
    (endpoint-comparable-arrow-arrowᵢ
      (endpoint-comparable-var-varᵢ (s<s z<s))
      (endpoint-comparable-var-varᵢ z<s)
      refl)
    (canonical-first-order-∀∀-supportᵢ
      (can-arrow-arrow
        (can-var-var (s<s z<s))
        (can-var-var z<s)))
    refl

endpointMlb-coherence-free-var-one-under-two-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)))}
    {Δᴸ = 2}
    {Δᴿ = 2}
    {A = ＇ 1}
    {A′ = ＇ 1}
    {B = ＇ 1}
    {B′ = ＇ 1}
    (idˣ (there (here refl)) (s<s z<s) (s<s z<s))
    (idˣ (there (here refl)) (s<s z<s) (s<s z<s))
endpointMlb-coherence-free-var-one-under-two-targetᵢ =
  endpoint-canonical-coherence-targetᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)))}
    {Δᴸ = 2}
    {Δᴿ = 2}
    {A = ＇ 1}
    {A′ = ＇ 1}
    {B = ＇ 1}
    {B′ = ＇ 1}
    (can-var-var (s<s z<s))
    (can-var-var (s<s z<s))
    refl
    refl
    (idˣ (there (here refl)) (s<s z<s) (s<s z<s))
    (idˣ (there (here refl)) (s<s z<s) (s<s z<s))

endpointMlb-coherence-free-var-zero-under-two-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)))}
    {Δᴸ = 2}
    {Δᴿ = 2}
    {A = ＇ 0}
    {A′ = ＇ 0}
    {B = ＇ 0}
    {B′ = ＇ 0}
    (idˣ (here refl) z<s z<s)
    (idˣ (here refl) z<s z<s)
endpointMlb-coherence-free-var-zero-under-two-targetᵢ =
  endpoint-canonical-coherence-targetᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)))}
    {Δᴸ = 2}
    {Δᴿ = 2}
    {A = ＇ 0}
    {A′ = ＇ 0}
    {B = ＇ 0}
    {B′ = ＇ 0}
    (can-var-var z<s)
    (can-var-var z<s)
    refl
    refl
    (idˣ (here refl) z<s z<s)
    (idˣ (here refl) z<s z<s)

endpointMlb-coherence-free-var-zero-under-one-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A = ＇ 0}
    {A′ = ＇ 0}
    {B = ＇ 0}
    {B′ = ＇ 0}
    (idˣ (here refl) z<s z<s)
    (idˣ (here refl) z<s z<s)
endpointMlb-coherence-free-var-zero-under-one-targetᵢ =
  endpoint-canonical-coherence-targetᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A = ＇ 0}
    {A′ = ＇ 0}
    {B = ＇ 0}
    {B′ = ＇ 0}
    (can-var-var z<s)
    (can-var-var z<s)
    refl
    refl
    (idˣ (here refl) z<s z<s)
    (idˣ (here refl) z<s z<s)

endpointMlb-coherence-matching-two-binder-arrow-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)))}
    {Δᴸ = 2}
    {Δᴿ = 2}
    {A = (＇ 1) ⇒ (＇ 0)}
    {A′ = (＇ 1) ⇒ (＇ 0)}
    {B = (＇ 1) ⇒ (＇ 0)}
    {B′ = (＇ 1) ⇒ (＇ 0)}
    ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
     (idˣ (here refl) z<s z<s))
    ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
     (idˣ (here refl) z<s z<s))
endpointMlb-coherence-matching-two-binder-arrow-targetᵢ =
  endpoint-arrow-arrow-coherence-targetᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)))}
    {Δᴸ = 2}
    {Δᴿ = 2}
    {A₁ = ＇ 1}
    {A₁′ = ＇ 1}
    {A₂ = ＇ 0}
    {A₂′ = ＇ 0}
    {B₁ = ＇ 1}
    {B₁′ = ＇ 1}
    {B₂ = ＇ 0}
    {B₂′ = ＇ 0}
    {C₁ = ＇ 1}
    {C₁′ = ＇ 1}
    {C₂ = ＇ 0}
    {C₂′ = ＇ 0}
    {pA₁ = idˣ (there (here refl)) (s<s z<s) (s<s z<s)}
    {pA₂ = idˣ (here refl) z<s z<s}
    {pB₁ = idˣ (there (here refl)) (s<s z<s) (s<s z<s)}
    {pB₂ = idˣ (here refl) z<s z<s}
    refl
    refl
    refl
    refl
    refl
    refl
    endpointMlb-coherence-free-var-one-under-two-targetᵢ
    endpointMlb-coherence-free-var-zero-under-two-targetᵢ

endpointMlb-coherence-matching-two-binder-inner-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A = `∀ ((＇ 1) ⇒ (＇ 0))}
    {A′ = `∀ ((＇ 1) ⇒ (＇ 0))}
    {B = `∀ ((＇ 1) ⇒ (＇ 0))}
    {B′ = `∀ ((＇ 1) ⇒ (＇ 0))}
    (∀ⁱ ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
          (idˣ (here refl) z<s z<s)))
    (∀ⁱ ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
          (idˣ (here refl) z<s z<s)))
endpointMlb-coherence-matching-two-binder-inner-targetᵢ =
  endpoint-forall-forall-coherence-targetᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A = (＇ 1) ⇒ (＇ 0)}
    {A′ = (＇ 1) ⇒ (＇ 0)}
    {B = (＇ 1) ⇒ (＇ 0)}
    {B′ = (＇ 1) ⇒ (＇ 0)}
    {C = (＇ 1) ⇒ (＇ 0)}
    {C′ = (＇ 1) ⇒ (＇ 0)}
    {pA = (idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
           (idˣ (here refl) z<s z<s)}
    {pB = (idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
           (idˣ (here refl) z<s z<s)}
    refl
    refl
    refl
    refl
    endpointMlb-coherence-matching-two-binder-arrow-targetᵢ

endpointMlb-coherence-matching-two-binder-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ (`∀ ((＇ 1) ⇒ (＇ 0)))}
    {A′ = `∀ (`∀ ((＇ 1) ⇒ (＇ 0)))}
    {B = `∀ (`∀ ((＇ 1) ⇒ (＇ 0)))}
    {B′ = `∀ (`∀ ((＇ 1) ⇒ (＇ 0)))}
    (∀ⁱ (∀ⁱ
      ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
       (idˣ (here refl) z<s z<s))))
    (∀ⁱ (∀ⁱ
      ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
       (idˣ (here refl) z<s z<s))))
endpointMlb-coherence-matching-two-binder-targetᵢ =
  endpoint-forall-forall-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ ((＇ 1) ⇒ (＇ 0))}
    {A′ = `∀ ((＇ 1) ⇒ (＇ 0))}
    {B = `∀ ((＇ 1) ⇒ (＇ 0))}
    {B′ = `∀ ((＇ 1) ⇒ (＇ 0))}
    {C = `∀ ((＇ 1) ⇒ (＇ 0))}
    {C′ = `∀ ((＇ 1) ⇒ (＇ 0))}
    {pA = ∀ⁱ
      ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
       (idˣ (here refl) z<s z<s))}
    {pB = ∀ⁱ
      ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
       (idˣ (here refl) z<s z<s))}
    refl
    refl
    refl
    refl
    endpointMlb-coherence-matching-two-binder-inner-targetᵢ

endpointMlb-sound-matching-two-binder-targetᵢ :
  EndpointMlbSoundᵢ
    0
    (`∀ (`∀ ((＇ 1) ⇒ (＇ 0))))
    (`∀ (`∀ ((＇ 1) ⇒ (＇ 0))))
endpointMlb-sound-matching-two-binder-targetᵢ =
  endpoint-forall-forall-sound-targetᵢ
    endpointMlb-sound-matching-two-binder-inner-targetᵢ
    refl
    refl

endpointMlb-comparable-captured-outer-body-targetᵢ :
  EndpointMlbComparableᵢ
    1
    (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))
    (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))
endpointMlb-comparable-captured-outer-body-targetᵢ =
  endpoint-comparable-arrow-arrowᵢ
    endpointMlb-comparable-matching-two-binder-inner-targetᵢ
    (endpoint-comparable-var-varᵢ z<s)
    refl

endpointMlb-sound-captured-outer-body-targetᵢ :
  EndpointMlbSoundᵢ
    1
    (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))
    (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))
endpointMlb-sound-captured-outer-body-targetᵢ =
  endpoint-arrow-arrow-sound-targetᵢ
    endpointMlb-sound-matching-two-binder-inner-targetᵢ
    endpointMlb-sound-free-var-zero-under-one-targetᵢ
    refl
    refl
    refl

endpointMlb-maximal-captured-outer-body-targetᵢ :
  EndpointMlbMaximalᵢ
    1
    (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))
    (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))
endpointMlb-maximal-captured-outer-body-targetᵢ =
  endpoint-arrow-arrow-maximal-targetᵢ
    endpointMlb-maximal-matching-two-binder-inner-targetᵢ
    endpointMlb-maximal-free-var-zero-under-one-targetᵢ
    refl
    refl
    refl

endpointMlb-coherence-captured-outer-body-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A = ((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)}
    {A′ = ((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)}
    {B = ((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)}
    {B′ = ((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)}
    ((∀ⁱ ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
           (idˣ (here refl) z<s z<s))) ↦
     (idˣ (here refl) z<s z<s))
    ((∀ⁱ ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
           (idˣ (here refl) z<s z<s))) ↦
     (idˣ (here refl) z<s z<s))
endpointMlb-coherence-captured-outer-body-targetᵢ =
  endpoint-arrow-arrow-coherence-targetᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A₁ = `∀ ((＇ 1) ⇒ (＇ 0))}
    {A₁′ = `∀ ((＇ 1) ⇒ (＇ 0))}
    {A₂ = ＇ 0}
    {A₂′ = ＇ 0}
    {B₁ = `∀ ((＇ 1) ⇒ (＇ 0))}
    {B₁′ = `∀ ((＇ 1) ⇒ (＇ 0))}
    {B₂ = ＇ 0}
    {B₂′ = ＇ 0}
    {C₁ = `∀ ((＇ 1) ⇒ (＇ 0))}
    {C₁′ = `∀ ((＇ 1) ⇒ (＇ 0))}
    {C₂ = ＇ 0}
    {C₂′ = ＇ 0}
    {pA₁ = ∀ⁱ
      ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
       (idˣ (here refl) z<s z<s))}
    {pA₂ = idˣ (here refl) z<s z<s}
    {pB₁ = ∀ⁱ
      ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
       (idˣ (here refl) z<s z<s))}
    {pB₂ = idˣ (here refl) z<s z<s}
    refl
    refl
    refl
    refl
    refl
    refl
    endpointMlb-coherence-matching-two-binder-inner-targetᵢ
    endpointMlb-coherence-free-var-zero-under-one-targetᵢ

endpointMlb-sound-captured-outer-profile-targetᵢ :
  EndpointMlbSoundᵢ
    0
    (`∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)))
    (`∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)))
endpointMlb-sound-captured-outer-profile-targetᵢ =
  endpoint-forall-forall-sound-targetᵢ
    endpointMlb-sound-captured-outer-body-targetᵢ
    refl
    refl

endpointMlb-maximal-captured-outer-profile-targetᵢ :
  EndpointMlbMaximalᵢ
    0
    (`∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)))
    (`∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)))
endpointMlb-maximal-captured-outer-profile-targetᵢ =
  endpoint-forall-forall-supported-maximal-targetᵢ
    endpointMlb-comparable-captured-outer-body-targetᵢ
    (non∀-∀∀-supportᵢ non∀-⇒)
    refl

endpointMlb-coherence-captured-outer-profile-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))}
    {A′ = `∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))}
    {B = `∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))}
    {B′ = `∀ (((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0))}
    (∀ⁱ
      (((∀ⁱ ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
              (idˣ (here refl) z<s z<s))) ↦
        (idˣ (here refl) z<s z<s))))
    (∀ⁱ
      (((∀ⁱ ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
              (idˣ (here refl) z<s z<s))) ↦
        (idˣ (here refl) z<s z<s))))
endpointMlb-coherence-captured-outer-profile-targetᵢ =
  endpoint-forall-forall-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)}
    {A′ = ((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)}
    {B = ((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)}
    {B′ = ((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)}
    {C = ((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)}
    {C′ = ((`∀ ((＇ 1) ⇒ (＇ 0)))) ⇒ (＇ 0)}
    {pA = ((∀ⁱ
      ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
       (idˣ (here refl) z<s z<s))) ↦
      (idˣ (here refl) z<s z<s))}
    {pB = ((∀ⁱ
      ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
       (idˣ (here refl) z<s z<s))) ↦
      (idˣ (here refl) z<s z<s))}
    refl
    refl
    refl
    refl
    endpointMlb-coherence-captured-outer-body-targetᵢ

endpointMlb-sound-bad-glb-certified-targetᵢ :
  EndpointMlbSoundᵢ 0 BadGlbLeftTy BadGlbRightTy
endpointMlb-sound-bad-glb-certified-targetᵢ =
  endpoint-common-lower-sound-targetᵢ endpointMlb-bad-glb-commonᵢ

endpointMlb-comparable-bad-glb-targetᵢ :
  EndpointMlbComparableᵢ 0 BadGlbLeftTy BadGlbRightTy
endpointMlb-comparable-bad-glb-targetᵢ =
  endpoint-choice-id-selector-comparableᵢ
    (sel-∀νᵢ refl bad-glb-endpoint-body-routeᵢ bad-glb-top-∀ν-supportᵢ)
    refl

endpointMlb-sound-bad-glb-selector-targetᵢ :
  EndpointMlbSoundᵢ 0 BadGlbLeftTy BadGlbRightTy
endpointMlb-sound-bad-glb-selector-targetᵢ =
  endpoint-comparable-sound-targetᵢ endpointMlb-comparable-bad-glb-targetᵢ

endpointMlb-maximal-bad-glb-targetᵢ :
  EndpointMlbMaximalᵢ 0 BadGlbLeftTy BadGlbRightTy
endpointMlb-maximal-bad-glb-targetᵢ =
  endpoint-comparable-maximal-targetᵢ endpointMlb-comparable-bad-glb-targetᵢ

endpointMlb-sound-bad-glb-reversed-certified-targetᵢ :
  EndpointMlbSoundᵢ 0 BadGlbRightTy BadGlbLeftTy
endpointMlb-sound-bad-glb-reversed-certified-targetᵢ =
  endpoint-common-lower-sound-targetᵢ endpointMlb-bad-glb-reversed-commonᵢ

endpointMlb-comparable-bad-glb-reversed-targetᵢ :
  EndpointMlbComparableᵢ 0 BadGlbRightTy BadGlbLeftTy
endpointMlb-comparable-bad-glb-reversed-targetᵢ =
  endpoint-choice-id-selector-comparableᵢ
    (sel-ν∀ᵢ
      refl
      bad-glb-reversed-endpoint-body-routeᵢ
      bad-glb-reversed-top-ν∀-supportᵢ)
    refl

endpointMlb-sound-bad-glb-reversed-selector-targetᵢ :
  EndpointMlbSoundᵢ 0 BadGlbRightTy BadGlbLeftTy
endpointMlb-sound-bad-glb-reversed-selector-targetᵢ =
  endpoint-comparable-sound-targetᵢ
    endpointMlb-comparable-bad-glb-reversed-targetᵢ

endpointMlb-maximal-bad-glb-reversed-targetᵢ :
  EndpointMlbMaximalᵢ 0 BadGlbRightTy BadGlbLeftTy
endpointMlb-maximal-bad-glb-reversed-targetᵢ =
  endpoint-comparable-maximal-targetᵢ
    endpointMlb-comparable-bad-glb-reversed-targetᵢ

endpointMlb-coherence-bad-glb-self-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = BadGlbLeftTy}
    {A′ = BadGlbLeftTy}
    {B = BadGlbRightTy}
    {B′ = BadGlbRightTy}
    glb-bad-A⊑A
    glb-bad-B⊑B
endpointMlb-coherence-bad-glb-self-targetᵢ =
  endpoint-common-lower-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = BadGlbLeftTy}
    {A′ = BadGlbLeftTy}
    {B = BadGlbRightTy}
    {B′ = BadGlbRightTy}
    {pA = glb-bad-A⊑A}
    {pB = glb-bad-B⊑B}
    endpointMlb-bad-glb-commonᵢ
    endpointMlb-bad-glb-commonᵢ
    bad-glb-lower⊑selfᵢ

endpointMlb-coherence-bad-glb-reversed-self-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = BadGlbRightTy}
    {A′ = BadGlbRightTy}
    {B = BadGlbLeftTy}
    {B′ = BadGlbLeftTy}
    glb-bad-B⊑B
    glb-bad-A⊑A
endpointMlb-coherence-bad-glb-reversed-self-targetᵢ =
  endpoint-common-lower-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = BadGlbRightTy}
    {A′ = BadGlbRightTy}
    {B = BadGlbLeftTy}
    {B′ = BadGlbLeftTy}
    {pA = glb-bad-B⊑B}
    {pB = glb-bad-A⊑A}
    endpointMlb-bad-glb-reversed-commonᵢ
    endpointMlb-bad-glb-reversed-commonᵢ
    bad-glb-lower⊑selfᵢ

endpointMlb-coherence-bad-glb-to-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = BadGlbLeftTy}
    {A′ = ★}
    {B = BadGlbRightTy}
    {B′ = ★}
    bad-glb-left⊑starᵢ
    bad-glb-right⊑starᵢ
endpointMlb-coherence-bad-glb-to-star-star-targetᵢ =
  endpoint-common-lower-to-star-star-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = BadGlbLeftTy}
    {B = BadGlbRightTy}
    {pA = bad-glb-left⊑starᵢ}
    {pB = bad-glb-right⊑starᵢ}
    endpointMlb-bad-glb-commonᵢ
    bad-glb-lower⊑starᵢ

endpointMlb-coherence-bad-glb-reversed-to-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = BadGlbRightTy}
    {A′ = ★}
    {B = BadGlbLeftTy}
    {B′ = ★}
    bad-glb-right⊑starᵢ
    bad-glb-left⊑starᵢ
endpointMlb-coherence-bad-glb-reversed-to-star-star-targetᵢ =
  endpoint-common-lower-to-star-star-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = BadGlbRightTy}
    {B = BadGlbLeftTy}
    {pA = bad-glb-right⊑starᵢ}
    {pB = bad-glb-left⊑starᵢ}
    endpointMlb-bad-glb-reversed-commonᵢ
    bad-glb-lower⊑starᵢ

endpointMlb-sound-repeated-one-sided-certified-targetᵢ :
  EndpointMlbSoundᵢ 0 RepeatedOneSidedTy ★
endpointMlb-sound-repeated-one-sided-certified-targetᵢ =
  endpoint-common-lower-sound-targetᵢ
    endpointMlb-repeated-one-sided-commonᵢ

endpointMlb-sound-repeated-one-sided-targetᵢ :
  EndpointMlbSoundᵢ 0 RepeatedOneSidedTy ★
endpointMlb-sound-repeated-one-sided-targetᵢ =
  endpoint-choice-id-selector-sound-targetᵢ
    endpoint-forall-var-arrow-var-star-routeᵢ
    refl

endpointMlb-maximal-repeated-one-sided-targetᵢ :
  EndpointMlbMaximalᵢ 0 RepeatedOneSidedTy ★
endpointMlb-maximal-repeated-one-sided-targetᵢ =
  endpoint-choice-id-selector-maximal-targetᵢ
    endpoint-forall-var-arrow-var-star-routeᵢ
    refl

endpointMlb-sound-repeated-one-sided-right-targetᵢ :
  EndpointMlbSoundᵢ 0 ★ RepeatedOneSidedTy
endpointMlb-sound-repeated-one-sided-right-targetᵢ =
  endpoint-choice-id-selector-sound-targetᵢ
    endpoint-star-forall-var-arrow-var-routeᵢ
    refl

endpointMlb-maximal-repeated-one-sided-right-targetᵢ :
  EndpointMlbMaximalᵢ 0 ★ RepeatedOneSidedTy
endpointMlb-maximal-repeated-one-sided-right-targetᵢ =
  endpoint-choice-id-selector-maximal-targetᵢ
    endpoint-star-forall-var-arrow-var-routeᵢ
    refl

endpointMlb-sound-used-var-left-targetᵢ :
  EndpointMlbSoundᵢ 0 (`∀ (＇ 0)) ★
endpointMlb-sound-used-var-left-targetᵢ =
  endpoint-choice-id-selector-sound-targetᵢ
    endpoint-forall-var-star-routeᵢ
    refl

endpointMlb-maximal-used-var-left-targetᵢ :
  EndpointMlbMaximalᵢ 0 (`∀ (＇ 0)) ★
endpointMlb-maximal-used-var-left-targetᵢ =
  endpoint-choice-id-selector-maximal-targetᵢ
    endpoint-forall-var-star-routeᵢ
    refl

endpointMlb-sound-used-var-right-targetᵢ :
  EndpointMlbSoundᵢ 0 ★ (`∀ (＇ 0))
endpointMlb-sound-used-var-right-targetᵢ =
  endpoint-choice-id-selector-sound-targetᵢ
    endpoint-star-forall-var-routeᵢ
    refl

endpointMlb-maximal-used-var-right-targetᵢ :
  EndpointMlbMaximalᵢ 0 ★ (`∀ (＇ 0))
endpointMlb-maximal-used-var-right-targetᵢ =
  endpoint-choice-id-selector-maximal-targetᵢ
    endpoint-star-forall-var-routeᵢ
    refl

endpointMlb-sound-used-var-base-left-targetᵢ :
  EndpointMlbSoundᵢ 0 UsedVarBaseTy ★
endpointMlb-sound-used-var-base-left-targetᵢ =
  endpoint-choice-id-selector-sound-targetᵢ
    endpoint-forall-var-arrow-base-star-routeᵢ
    refl

endpointMlb-maximal-used-var-base-left-targetᵢ :
  EndpointMlbMaximalᵢ 0 UsedVarBaseTy ★
endpointMlb-maximal-used-var-base-left-targetᵢ =
  endpoint-choice-id-selector-maximal-targetᵢ
    endpoint-forall-var-arrow-base-star-routeᵢ
    refl

endpointMlb-sound-used-var-base-right-targetᵢ :
  EndpointMlbSoundᵢ 0 ★ UsedVarBaseTy
endpointMlb-sound-used-var-base-right-targetᵢ =
  endpoint-choice-id-selector-sound-targetᵢ
    endpoint-star-forall-var-arrow-base-routeᵢ
    refl

endpointMlb-maximal-used-var-base-right-targetᵢ :
  EndpointMlbMaximalᵢ 0 ★ UsedVarBaseTy
endpointMlb-maximal-used-var-base-right-targetᵢ =
  endpoint-choice-id-selector-maximal-targetᵢ
    endpoint-star-forall-var-arrow-base-routeᵢ
    refl

endpointMlb-sound-used-var-star-left-targetᵢ :
  EndpointMlbSoundᵢ 0 UsedVarStarTy ★
endpointMlb-sound-used-var-star-left-targetᵢ =
  endpoint-choice-id-selector-sound-targetᵢ
    endpoint-forall-var-arrow-star-star-routeᵢ
    refl

endpointMlb-maximal-used-var-star-left-targetᵢ :
  EndpointMlbMaximalᵢ 0 UsedVarStarTy ★
endpointMlb-maximal-used-var-star-left-targetᵢ =
  endpoint-choice-id-selector-maximal-targetᵢ
    endpoint-forall-var-arrow-star-star-routeᵢ
    refl

endpointMlb-sound-used-var-star-right-targetᵢ :
  EndpointMlbSoundᵢ 0 ★ UsedVarStarTy
endpointMlb-sound-used-var-star-right-targetᵢ =
  endpoint-choice-id-selector-sound-targetᵢ
    endpoint-star-forall-var-arrow-star-routeᵢ
    refl

endpointMlb-maximal-used-var-star-right-targetᵢ :
  EndpointMlbMaximalᵢ 0 ★ UsedVarStarTy
endpointMlb-maximal-used-var-star-right-targetᵢ =
  endpoint-choice-id-selector-maximal-targetᵢ
    endpoint-star-forall-var-arrow-star-routeᵢ
    refl

endpointMlb-sound-forall-star-star-targetᵢ :
  EndpointMlbSoundᵢ 0 (`∀ ★) (`∀ ★)
endpointMlb-sound-forall-star-star-targetᵢ =
  endpoint-canonical-forall-forall-sound-targetᵢ can-star-star refl

endpointMlb-sound-forall-star-star-under∀-targetᵢ :
  EndpointMlbSoundᵢ 1 (`∀ ★) (`∀ ★)
endpointMlb-sound-forall-star-star-under∀-targetᵢ =
  endpoint-canonical-forall-forall-sound-targetᵢ can-star-star refl

endpointMlb-sound-unused-binders-pair-twice-targetᵢ :
  EndpointMlbSoundᵢ 0 (`∀ (`∀ ★)) (`∀ (`∀ ★))
endpointMlb-sound-unused-binders-pair-twice-targetᵢ =
  endpoint-forall-forall-sound-targetᵢ
    endpointMlb-sound-forall-star-star-under∀-targetᵢ
    refl
    refl

endpointMlb-comparable-forall-star-star-under∀-targetᵢ :
  EndpointMlbComparableᵢ 1 (`∀ ★) (`∀ ★)
endpointMlb-comparable-forall-star-star-under∀-targetᵢ =
  endpoint-comparable-forall-forall-from-supportᵢ
    endpoint-comparable-star-starᵢ
    (canonical-first-order-∀∀-supportᵢ can-star-star)
    refl

endpointMlb-maximal-unused-binders-pair-twice-targetᵢ :
  EndpointMlbMaximalᵢ 0 (`∀ (`∀ ★)) (`∀ (`∀ ★))
endpointMlb-maximal-unused-binders-pair-twice-targetᵢ =
  endpoint-forall-forall-supported-maximal-targetᵢ
    endpointMlb-comparable-forall-star-star-under∀-targetᵢ
    left-endpoint-∀∀-supportᵢ
    refl

endpointMlb-maximal-forall-star-star-targetᵢ :
  EndpointMlbMaximalᵢ 0 (`∀ ★) (`∀ ★)
endpointMlb-maximal-forall-star-star-targetᵢ =
  endpoint-canonical-forall-forall-maximal-targetᵢ can-star-star refl

endpointMlb-sound-forall-base-base-targetᵢ :
  EndpointMlbSoundᵢ 0 (`∀ NatTy) (`∀ NatTy)
endpointMlb-sound-forall-base-base-targetᵢ =
  endpoint-canonical-forall-forall-sound-targetᵢ can-base-base refl

endpointMlb-sound-forall-base-base-structural-targetᵢ :
  EndpointMlbSoundᵢ 0 (`∀ NatTy) (`∀ NatTy)
endpointMlb-sound-forall-base-base-structural-targetᵢ =
  endpoint-forall-forall-sound-targetᵢ
    endpointMlb-sound-base-base-under∀-targetᵢ
    refl
    refl

endpointMlb-sound-forall-base-base-supported-targetᵢ :
  EndpointMlbSoundᵢ 0 (`∀ NatTy) (`∀ NatTy)
endpointMlb-sound-forall-base-base-supported-targetᵢ =
  endpoint-forall-forall-supported-sound-targetᵢ
    endpoint-comparable-base-baseᵢ
    (canonical-first-order-∀∀-supportᵢ can-base-base)
    refl

endpointMlb-maximal-forall-base-base-targetᵢ :
  EndpointMlbMaximalᵢ 0 (`∀ NatTy) (`∀ NatTy)
endpointMlb-maximal-forall-base-base-targetᵢ =
  endpoint-canonical-forall-forall-maximal-targetᵢ can-base-base refl

endpointMlb-maximal-forall-base-base-supported-targetᵢ :
  EndpointMlbMaximalᵢ 0 (`∀ NatTy) (`∀ NatTy)
endpointMlb-maximal-forall-base-base-supported-targetᵢ =
  endpoint-forall-forall-supported-maximal-targetᵢ
    endpoint-comparable-base-baseᵢ
    (canonical-first-order-∀∀-supportᵢ can-base-base)
    refl

endpointMlb-sound-forall-var-var-targetᵢ :
  EndpointMlbSoundᵢ 0 (`∀ (＇ 0)) (`∀ (＇ 0))
endpointMlb-sound-forall-var-var-targetᵢ =
  endpoint-canonical-forall-forall-sound-targetᵢ (can-var-var z<s) refl

endpointMlb-maximal-forall-var-var-targetᵢ :
  EndpointMlbMaximalᵢ 0 (`∀ (＇ 0)) (`∀ (＇ 0))
endpointMlb-maximal-forall-var-var-targetᵢ =
  endpoint-canonical-forall-forall-maximal-targetᵢ (can-var-var z<s) refl

endpointMlb-sound-nested-forall-blocks-targetᵢ :
  EndpointMlbSoundᵢ
    0
    ((`∀ (＇ 0)) ⇒ (`∀ ★))
    ((`∀ (＇ 0)) ⇒ (`∀ ★))
endpointMlb-sound-nested-forall-blocks-targetᵢ =
  endpoint-arrow-arrow-sound-targetᵢ
    endpointMlb-sound-forall-var-var-targetᵢ
    endpointMlb-sound-forall-star-star-targetᵢ
    refl
    refl
    refl

endpointMlb-maximal-nested-forall-blocks-targetᵢ :
  EndpointMlbMaximalᵢ
    0
    ((`∀ (＇ 0)) ⇒ (`∀ ★))
    ((`∀ (＇ 0)) ⇒ (`∀ ★))
endpointMlb-maximal-nested-forall-blocks-targetᵢ =
  endpoint-arrow-arrow-maximal-targetᵢ
    endpointMlb-maximal-forall-var-var-targetᵢ
    endpointMlb-maximal-forall-star-star-targetᵢ
    refl
    refl
    refl

endpointMlb-sound-first-use-exposure-targetᵢ :
  EndpointMlbSoundᵢ 0 ★ FirstUseExposureTy
endpointMlb-sound-first-use-exposure-targetᵢ =
  endpoint-common-lower-sound-targetᵢ endpointMlb-first-use-exposure-commonᵢ

endpointMlb-maximal-first-use-exposure-targetᵢ :
  EndpointMlbMaximalᵢ 0 ★ FirstUseExposureTy
endpointMlb-maximal-first-use-exposure-targetᵢ =
  endpoint-comparable-maximal-targetᵢ
    endpoint-comparable-star-first-use-exposureᵢ

endpointMlb-coherence-first-use-exposure-self-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {A′ = ★}
    {B = FirstUseExposureTy}
    {B′ = FirstUseExposureTy}
    id★
    first-use-exposure⊑selfᵢ
endpointMlb-coherence-first-use-exposure-self-targetᵢ =
  endpoint-choice-id-selector-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {A′ = ★}
    {B = FirstUseExposureTy}
    {B′ = FirstUseExposureTy}
    {pA = id★}
    {pB = first-use-exposure⊑selfᵢ}
    endpoint-star-first-use-exposure-routeᵢ
    endpoint-star-first-use-exposure-routeᵢ
    refl
    refl
    first-use-exposure⊑selfᵢ

endpointMlb-coherence-first-use-exposure-to-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {A′ = ★}
    {B = FirstUseExposureTy}
    {B′ = ★}
    id★
    first-use-exposure⊑starᵢ
endpointMlb-coherence-first-use-exposure-to-star-star-targetᵢ =
  endpoint-comparable-to-star-star-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {B = FirstUseExposureTy}
    {pA = id★}
    {pB = first-use-exposure⊑starᵢ}
    endpoint-comparable-star-first-use-exposureᵢ
    first-use-exposure⊑starᵢ

endpointMlb-sound-first-use-exposure-reversed-targetᵢ :
  EndpointMlbSoundᵢ 0 FirstUseExposureTy ★
endpointMlb-sound-first-use-exposure-reversed-targetᵢ =
  endpoint-common-lower-sound-targetᵢ
    endpointMlb-first-use-exposure-reversed-commonᵢ

endpointMlb-maximal-first-use-exposure-reversed-targetᵢ :
  EndpointMlbMaximalᵢ 0 FirstUseExposureTy ★
endpointMlb-maximal-first-use-exposure-reversed-targetᵢ =
  endpoint-comparable-maximal-targetᵢ
    endpoint-comparable-first-use-exposure-starᵢ

endpointMlb-coherence-first-use-exposure-reversed-self-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = FirstUseExposureTy}
    {A′ = FirstUseExposureTy}
    {B = ★}
    {B′ = ★}
    first-use-exposure⊑selfᵢ
    id★
endpointMlb-coherence-first-use-exposure-reversed-self-targetᵢ =
  endpoint-choice-id-selector-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = FirstUseExposureTy}
    {A′ = FirstUseExposureTy}
    {B = ★}
    {B′ = ★}
    {pA = first-use-exposure⊑selfᵢ}
    {pB = id★}
    endpoint-first-use-exposure-star-routeᵢ
    endpoint-first-use-exposure-star-routeᵢ
    refl
    refl
    first-use-exposure⊑selfᵢ

endpointMlb-coherence-first-use-exposure-reversed-to-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = FirstUseExposureTy}
    {A′ = ★}
    {B = ★}
    {B′ = ★}
    first-use-exposure⊑starᵢ
    id★
endpointMlb-coherence-first-use-exposure-reversed-to-star-star-targetᵢ =
  endpoint-comparable-to-star-star-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = FirstUseExposureTy}
    {B = ★}
    {pA = first-use-exposure⊑starᵢ}
    {pB = id★}
    endpoint-comparable-first-use-exposure-starᵢ
    first-use-exposure⊑starᵢ

endpointMlb-coherence-base-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy}
    {A′ = ★}
    {B = ★}
    {B′ = ★}
    (tag `ℕ)
    id★
endpointMlb-coherence-base-star-star-targetᵢ =
  endpoint-canonical-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy}
    {A′ = ★}
    {B = ★}
    {B′ = ★}
    can-base-star
    can-star-star
    refl
    refl
    (tag `ℕ)
    id★

endpointMlb-coherence-base-base-to-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy}
    {A′ = ★}
    {B = NatTy}
    {B′ = ★}
    (tag `ℕ)
    (tag `ℕ)
endpointMlb-coherence-base-base-to-star-star-targetᵢ =
  endpoint-canonical-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy}
    {A′ = ★}
    {B = NatTy}
    {B′ = ★}
    can-base-base
    can-star-star
    refl
    refl
    (tag `ℕ)
    (tag `ℕ)

endpointMlb-coherence-base-base-to-star-star-under∀-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A = NatTy}
    {A′ = ★}
    {B = NatTy}
    {B′ = ★}
    (tag `ℕ)
    (tag `ℕ)
endpointMlb-coherence-base-base-to-star-star-under∀-targetᵢ =
  endpoint-canonical-coherence-targetᵢ
    {Φ = (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0)}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A = NatTy}
    {A′ = ★}
    {B = NatTy}
    {B′ = ★}
    can-base-base
    can-star-star
    refl
    refl
    (tag `ℕ)
    (tag `ℕ)

endpointMlb-coherence-star-base-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {A′ = ★}
    {B = NatTy}
    {B′ = ★}
    id★
    (tag `ℕ)
endpointMlb-coherence-star-base-star-targetᵢ =
  endpoint-canonical-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {A′ = ★}
    {B = NatTy}
    {B′ = ★}
    can-star-base
    can-star-star
    refl
    refl
    id★
    (tag `ℕ)

endpointMlb-coherence-arrow-base-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy ⇒ NatTy}
    {A′ = ★ ⇒ ★}
    {B = ★ ⇒ ★}
    {B′ = ★ ⇒ ★}
    ((tag `ℕ) ↦ (tag `ℕ))
    (id★ ↦ id★)
endpointMlb-coherence-arrow-base-star-star-targetᵢ =
  endpoint-arrow-arrow-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A₁ = NatTy}
    {A₁′ = ★}
    {A₂ = NatTy}
    {A₂′ = ★}
    {B₁ = ★}
    {B₁′ = ★}
    {B₂ = ★}
    {B₂′ = ★}
    {C₁ = NatTy}
    {C₁′ = ★}
    {C₂ = NatTy}
    {C₂′ = ★}
    {pA₁ = tag `ℕ}
    {pA₂ = tag `ℕ}
    {pB₁ = id★}
    {pB₂ = id★}
    refl
    refl
    refl
    refl
    refl
    refl
    endpointMlb-coherence-base-star-star-targetᵢ
    endpointMlb-coherence-base-star-star-targetᵢ

endpointMlb-coherence-arrow-base-base-to-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy ⇒ NatTy}
    {A′ = ★ ⇒ ★}
    {B = NatTy ⇒ NatTy}
    {B′ = ★ ⇒ ★}
    ((tag `ℕ) ↦ (tag `ℕ))
    ((tag `ℕ) ↦ (tag `ℕ))
endpointMlb-coherence-arrow-base-base-to-star-star-targetᵢ =
  endpoint-arrow-arrow-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A₁ = NatTy}
    {A₁′ = ★}
    {A₂ = NatTy}
    {A₂′ = ★}
    {B₁ = NatTy}
    {B₁′ = ★}
    {B₂ = NatTy}
    {B₂′ = ★}
    {C₁ = NatTy}
    {C₁′ = ★}
    {C₂ = NatTy}
    {C₂′ = ★}
    {pA₁ = tag `ℕ}
    {pA₂ = tag `ℕ}
    {pB₁ = tag `ℕ}
    {pB₂ = tag `ℕ}
    refl
    refl
    refl
    refl
    refl
    refl
    endpointMlb-coherence-base-base-to-star-star-targetᵢ
    endpointMlb-coherence-base-base-to-star-star-targetᵢ

endpointMlb-coherence-arrow-base-base-to-star-star-under∀-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A = NatTy ⇒ NatTy}
    {A′ = ★ ⇒ ★}
    {B = NatTy ⇒ NatTy}
    {B′ = ★ ⇒ ★}
    ((tag `ℕ) ↦ (tag `ℕ))
    ((tag `ℕ) ↦ (tag `ℕ))
endpointMlb-coherence-arrow-base-base-to-star-star-under∀-targetᵢ =
  endpoint-arrow-arrow-coherence-targetᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A₁ = NatTy}
    {A₁′ = ★}
    {A₂ = NatTy}
    {A₂′ = ★}
    {B₁ = NatTy}
    {B₁′ = ★}
    {B₂ = NatTy}
    {B₂′ = ★}
    {C₁ = NatTy}
    {C₁′ = ★}
    {C₂ = NatTy}
    {C₂′ = ★}
    {pA₁ = tag `ℕ}
    {pA₂ = tag `ℕ}
    {pB₁ = tag `ℕ}
    {pB₂ = tag `ℕ}
    refl
    refl
    refl
    refl
    refl
    refl
    endpointMlb-coherence-base-base-to-star-star-under∀-targetᵢ
    endpointMlb-coherence-base-base-to-star-star-under∀-targetᵢ

endpointMlb-coherence-forall-arrow-star-structural-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ (NatTy ⇒ NatTy)}
    {A′ = `∀ (★ ⇒ ★)}
    {B = `∀ (NatTy ⇒ NatTy)}
    {B′ = `∀ (★ ⇒ ★)}
    (∀ⁱ ((tag `ℕ) ↦ (tag `ℕ)))
    (∀ⁱ ((tag `ℕ) ↦ (tag `ℕ)))
endpointMlb-coherence-forall-arrow-star-structural-targetᵢ =
  endpoint-forall-forall-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy ⇒ NatTy}
    {A′ = ★ ⇒ ★}
    {B = NatTy ⇒ NatTy}
    {B′ = ★ ⇒ ★}
    {pA = (tag `ℕ) ↦ (tag `ℕ)}
    {pB = (tag `ℕ) ↦ (tag `ℕ)}
    refl
    refl
    refl
    refl
    endpointMlb-coherence-arrow-base-base-to-star-star-under∀-targetᵢ

endpointMlb-coherence-arrow-star-base-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy ⇒ NatTy}
    {A′ = ★ ⇒ ★}
    {B = ★}
    {B′ = ★}
    ((tag `ℕ) ↦ (tag `ℕ))
    id★
endpointMlb-coherence-arrow-star-base-star-targetᵢ =
  endpoint-arrow-star-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A₁ = NatTy}
    {A₁′ = ★}
    {A₂ = NatTy}
    {A₂′ = ★}
    {C₁ = NatTy}
    {C₁′ = ★}
    {C₂ = NatTy}
    {C₂′ = ★}
    {pA₁ = tag `ℕ}
    {pA₂ = tag `ℕ}
    refl
    refl
    refl
    refl
    refl
    refl
    endpointMlb-coherence-base-star-star-targetᵢ
    endpointMlb-coherence-base-star-star-targetᵢ

endpointMlb-coherence-arrow-star-to-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy ⇒ NatTy}
    {A′ = ★}
    {B = ★}
    {B′ = ★}
    (tag (tag `ℕ) ⇛ tag `ℕ)
    id★
endpointMlb-coherence-arrow-star-to-star-star-targetᵢ =
  endpoint-arrow-star-to-star-star-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A₁ = NatTy}
    {A₂ = NatTy}
    {C₁ = NatTy}
    {C₂ = NatTy}
    {pA₁ = tag `ℕ}
    {pA₂ = tag `ℕ}
    refl
    refl
    refl
    refl
    refl
    refl
    endpointMlb-coherence-base-star-star-targetᵢ
    endpointMlb-coherence-base-star-star-targetᵢ

endpointMlb-coherence-star-arrow-base-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {A′ = ★}
    {B = NatTy ⇒ NatTy}
    {B′ = ★ ⇒ ★}
    id★
    ((tag `ℕ) ↦ (tag `ℕ))
endpointMlb-coherence-star-arrow-base-star-targetᵢ =
  endpoint-star-arrow-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {B₁ = NatTy}
    {B₁′ = ★}
    {B₂ = NatTy}
    {B₂′ = ★}
    {C₁ = NatTy}
    {C₁′ = ★}
    {C₂ = NatTy}
    {C₂′ = ★}
    {pB₁ = tag `ℕ}
    {pB₂ = tag `ℕ}
    refl
    refl
    refl
    refl
    refl
    refl
    endpointMlb-coherence-star-base-star-targetᵢ
    endpointMlb-coherence-star-base-star-targetᵢ

endpointMlb-coherence-star-arrow-to-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {A′ = ★}
    {B = NatTy ⇒ NatTy}
    {B′ = ★}
    id★
    (tag (tag `ℕ) ⇛ tag `ℕ)
endpointMlb-coherence-star-arrow-to-star-star-targetᵢ =
  endpoint-star-arrow-to-star-star-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {B₁ = NatTy}
    {B₂ = NatTy}
    {C₁ = NatTy}
    {C₂ = NatTy}
    {pB₁ = tag `ℕ}
    {pB₂ = tag `ℕ}
    refl
    refl
    refl
    refl
    refl
    refl
    endpointMlb-coherence-star-base-star-targetᵢ
    endpointMlb-coherence-star-base-star-targetᵢ

endpointMlb-coherence-forall-base-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ NatTy}
    {A′ = `∀ ★}
    {B = `∀ NatTy}
    {B′ = `∀ ★}
    (∀ⁱ (tag `ℕ))
    (∀ⁱ (tag `ℕ))
endpointMlb-coherence-forall-base-star-targetᵢ =
  endpoint-canonical-forall-forall-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy}
    {A′ = ★}
    {B = NatTy}
    {B′ = ★}
    {pA = tag `ℕ}
    {pB = tag `ℕ}
    can-base-base
    can-star-star
    refl
    refl

endpointMlb-coherence-forall-base-star-structural-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ NatTy}
    {A′ = `∀ ★}
    {B = `∀ NatTy}
    {B′ = `∀ ★}
    (∀ⁱ (tag `ℕ))
    (∀ⁱ (tag `ℕ))
endpointMlb-coherence-forall-base-star-structural-targetᵢ =
  endpoint-forall-forall-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy}
    {A′ = ★}
    {B = NatTy}
    {B′ = ★}
    {pA = tag `ℕ}
    {pB = tag `ℕ}
    refl
    refl
    refl
    refl
    endpointMlb-coherence-base-base-to-star-star-under∀-targetᵢ

endpointMlb-coherence-forall-base-star-supported-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ NatTy}
    {A′ = `∀ ★}
    {B = `∀ NatTy}
    {B′ = `∀ ★}
    (∀ⁱ (tag `ℕ))
    (∀ⁱ (tag `ℕ))
endpointMlb-coherence-forall-base-star-supported-targetᵢ =
  endpoint-forall-forall-supported-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy}
    {A′ = ★}
    {B = NatTy}
    {B′ = ★}
    {pA = tag `ℕ}
    {pB = tag `ℕ}
    endpoint-comparable-base-baseᵢ
    endpoint-comparable-star-starᵢ
    (canonical-first-order-∀∀-supportᵢ can-base-base)
    (canonical-first-order-∀∀-supportᵢ can-star-star)
    refl
    refl
    (canonical-forall-forall-maximal-coherenceᵢ
      {Φ = idᵢ 0}
      {Δᴸ = 0}
      {Δᴿ = 0}
      {A = NatTy}
      {A′ = ★}
      {B = NatTy}
      {B′ = ★}
      {C = NatTy}
      {C′ = ★}
      {pA = tag `ℕ}
      {pB = tag `ℕ}
      can-base-base
      can-star-star)

endpointMlb-coherence-forall-arrow-star-supported-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ (NatTy ⇒ NatTy)}
    {A′ = `∀ (★ ⇒ ★)}
    {B = `∀ (NatTy ⇒ NatTy)}
    {B′ = `∀ (★ ⇒ ★)}
    (∀ⁱ ((tag `ℕ) ↦ (tag `ℕ)))
    (∀ⁱ ((tag `ℕ) ↦ (tag `ℕ)))
endpointMlb-coherence-forall-arrow-star-supported-targetᵢ =
  endpoint-forall-forall-supported-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = NatTy ⇒ NatTy}
    {A′ = ★ ⇒ ★}
    {B = NatTy ⇒ NatTy}
    {B′ = ★ ⇒ ★}
    {pA = (tag `ℕ) ↦ (tag `ℕ)}
    {pB = (tag `ℕ) ↦ (tag `ℕ)}
    (endpoint-comparable-arrow-arrowᵢ
      endpoint-comparable-base-baseᵢ
      endpoint-comparable-base-baseᵢ
      refl)
    (endpoint-comparable-arrow-arrowᵢ
      endpoint-comparable-star-starᵢ
      endpoint-comparable-star-starᵢ
      refl)
    (canonical-first-order-∀∀-supportᵢ
      (can-arrow-arrow can-base-base can-base-base))
    (canonical-first-order-∀∀-supportᵢ
      (can-arrow-arrow can-star-star can-star-star))
    refl
    refl
    (canonical-forall-forall-maximal-coherenceᵢ
      {Φ = idᵢ 0}
      {Δᴸ = 0}
      {Δᴿ = 0}
      {A = NatTy ⇒ NatTy}
      {A′ = ★ ⇒ ★}
      {B = NatTy ⇒ NatTy}
      {B′ = ★ ⇒ ★}
      {C = NatTy ⇒ NatTy}
      {C′ = ★ ⇒ ★}
      {pA = (tag `ℕ) ↦ (tag `ℕ)}
      {pB = (tag `ℕ) ↦ (tag `ℕ)}
      (can-arrow-arrow can-base-base can-base-base)
      (can-arrow-arrow can-star-star can-star-star))

endpointMlb-coherence-forall-var-var-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ (＇ 0)}
    {A′ = `∀ (＇ 0)}
    {B = `∀ (＇ 0)}
    {B′ = `∀ (＇ 0)}
    (∀ⁱ (idˣ (here refl) z<s z<s))
    (∀ⁱ (idˣ (here refl) z<s z<s))
endpointMlb-coherence-forall-var-var-targetᵢ =
  endpoint-canonical-forall-forall-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ＇ 0}
    {A′ = ＇ 0}
    {B = ＇ 0}
    {B′ = ＇ 0}
    {pA = idˣ (here refl) z<s z<s}
    {pB = idˣ (here refl) z<s z<s}
    (can-var-var z<s)
    (can-var-var z<s)
    refl
    refl

endpointMlb-coherence-forall-var-var-route-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ (＇ 0)}
    {A′ = `∀ (＇ 0)}
    {B = `∀ (＇ 0)}
    {B′ = `∀ (＇ 0)}
    (∀ⁱ (idˣ (here refl) z<s z<s))
    (∀ⁱ (idˣ (here refl) z<s z<s))
endpointMlb-coherence-forall-var-var-route-targetᵢ =
  endpoint-mlb-type-from-lower-∀∀-first-order-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ＇ 0}
    {A′ = ＇ 0}
    {B = ＇ 0}
    {B′ = ＇ 0}
    {C = ＇ 0}
    {C′ = ＇ 0}
    {pA = idˣ (here refl) z<s z<s}
    {pB = idˣ (here refl) z<s z<s}
    {p = idˣ (here refl) z<s z<s}
    {q = idˣ (here refl) z<s z<s}
    {p′ = idˣ (here refl) z<s z<s}
    {q′ = idˣ (here refl) z<s z<s}
    fo-var-var-atᵢ
    fo-var-var-atᵢ
    refl
    refl

endpointMlb-coherence-forall-var-var-to-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ (＇ 0)}
    {A′ = ★}
    {B = `∀ (＇ 0)}
    {B′ = ★}
    endpoint-forall-var-starᵢ
    endpoint-forall-var-starᵢ
endpointMlb-coherence-forall-var-var-to-star-star-targetᵢ =
  endpoint-canonical-forall-forall-to-first-order-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ＇ 0}
    {A′ = ★}
    {B = ＇ 0}
    {B′ = ★}
    {C = ＇ 0}
    {C′ = ★}
    {pA = tagˣ (here refl) z<s}
    {pB = tagˣ (here refl) z<s}
    (can-var-var z<s)
    can-star-star
    refl
    refl
    refl
    refl

endpointMlb-coherence-forall-var-var-route-to-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ (＇ 0)}
    {A′ = ★}
    {B = `∀ (＇ 0)}
    {B′ = ★}
    endpoint-forall-var-starᵢ
    endpoint-forall-var-starᵢ
endpointMlb-coherence-forall-var-var-route-to-star-targetᵢ =
  endpoint-mlb-type-from-lower-∀∀-first-order-target-coherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ＇ 0}
    {A′ = ★}
    {B = ＇ 0}
    {B′ = ★}
    {C = ＇ 0}
    {C′ = ★}
    {pA = tagˣ (here refl) z<s}
    {pB = tagˣ (here refl) z<s}
    {p = idˣ (here refl) z<s z<s}
    {q = idˣ (here refl) z<s z<s}
    {p′ = id★}
    {q′ = id★}
    refl
    refl
    fo-var-var-atᵢ
    fo-star-star-atᵢ
    refl
    refl

endpointMlb-coherence-forall-var-arrow-base-to-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = UsedVarBaseTy}
    {A′ = ★}
    {B = UsedVarBaseTy}
    {B′ = ★}
    endpoint-forall-var-arrow-base-starᵢ
    endpoint-forall-var-arrow-base-starᵢ
endpointMlb-coherence-forall-var-arrow-base-to-star-targetᵢ =
  endpoint-canonical-forall-forall-to-first-order-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = (＇ 0) ⇒ NatTy}
    {A′ = ★}
    {B = (＇ 0) ⇒ NatTy}
    {B′ = ★}
    {C = (＇ 0) ⇒ NatTy}
    {C′ = ★}
    {pA = tag tagˣ (here refl) z<s ⇛ tag `ℕ}
    {pB = tag tagˣ (here refl) z<s ⇛ tag `ℕ}
    (can-arrow-arrow (can-var-var z<s) can-base-base)
    can-star-star
    refl
    refl
    refl
    refl

endpointMlb-coherence-forall-star-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ ★}
    {A′ = `∀ ★}
    {B = `∀ ★}
    {B′ = `∀ ★}
    (∀ⁱ id★)
    (∀ⁱ id★)
endpointMlb-coherence-forall-star-star-targetᵢ =
  endpoint-canonical-forall-forall-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {A′ = ★}
    {B = ★}
    {B′ = ★}
    {pA = id★}
    {pB = id★}
    can-star-star
    can-star-star
    refl
    refl

endpointMlb-coherence-forall-star-star-under∀-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A = `∀ ★}
    {A′ = `∀ ★}
    {B = `∀ ★}
    {B′ = `∀ ★}
    (∀ⁱ id★)
    (∀ⁱ id★)
endpointMlb-coherence-forall-star-star-under∀-targetᵢ =
  endpoint-canonical-forall-forall-coherence-targetᵢ
    {Φ = ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ (idᵢ 0))}
    {Δᴸ = 1}
    {Δᴿ = 1}
    {A = ★}
    {A′ = ★}
    {B = ★}
    {B′ = ★}
    {pA = id★}
    {pB = id★}
    can-star-star
    can-star-star
    refl
    refl

endpointMlb-coherence-unused-binders-pair-twice-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ (`∀ ★)}
    {A′ = `∀ (`∀ ★)}
    {B = `∀ (`∀ ★)}
    {B′ = `∀ (`∀ ★)}
    (∀ⁱ (∀ⁱ id★))
    (∀ⁱ (∀ⁱ id★))
endpointMlb-coherence-unused-binders-pair-twice-targetᵢ =
  endpoint-forall-forall-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = `∀ ★}
    {A′ = `∀ ★}
    {B = `∀ ★}
    {B′ = `∀ ★}
    {C = `∀ ★}
    {C′ = `∀ ★}
    {pA = ∀ⁱ id★}
    {pB = ∀ⁱ id★}
    refl
    refl
    refl
    refl
    endpointMlb-coherence-forall-star-star-under∀-targetᵢ

endpointMlb-coherence-nested-forall-blocks-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = (`∀ (＇ 0)) ⇒ (`∀ ★)}
    {A′ = (`∀ (＇ 0)) ⇒ (`∀ ★)}
    {B = (`∀ (＇ 0)) ⇒ (`∀ ★)}
    {B′ = (`∀ (＇ 0)) ⇒ (`∀ ★)}
    ((∀ⁱ (idˣ (here refl) z<s z<s)) ↦ (∀ⁱ id★))
    ((∀ⁱ (idˣ (here refl) z<s z<s)) ↦ (∀ⁱ id★))
endpointMlb-coherence-nested-forall-blocks-targetᵢ =
  endpoint-arrow-arrow-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A₁ = `∀ (＇ 0)}
    {A₁′ = `∀ (＇ 0)}
    {A₂ = `∀ ★}
    {A₂′ = `∀ ★}
    {B₁ = `∀ (＇ 0)}
    {B₁′ = `∀ (＇ 0)}
    {B₂ = `∀ ★}
    {B₂′ = `∀ ★}
    {C₁ = `∀ (＇ 0)}
    {C₁′ = `∀ (＇ 0)}
    {C₂ = `∀ ★}
    {C₂′ = `∀ ★}
    {pA₁ = ∀ⁱ (idˣ (here refl) z<s z<s)}
    {pA₂ = ∀ⁱ id★}
    {pB₁ = ∀ⁱ (idˣ (here refl) z<s z<s)}
    {pB₂ = ∀ⁱ id★}
    refl
    refl
    refl
    refl
    refl
    refl
    endpointMlb-coherence-forall-var-var-targetᵢ
    endpointMlb-coherence-forall-star-star-targetᵢ

endpointMlb-coherence-used-var-base-to-star-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = UsedVarBaseTy}
    {A′ = UsedVarStarTy}
    {B = ★}
    {B′ = ★}
    endpoint-forall-var-arrow-base-to-starᵢ
    id★
endpointMlb-coherence-used-var-base-to-star-targetᵢ =
  endpoint-choice-id-selector-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = UsedVarBaseTy}
    {A′ = UsedVarStarTy}
    {B = ★}
    {B′ = ★}
    {pA = endpoint-forall-var-arrow-base-to-starᵢ}
    {pB = id★}
    endpoint-forall-var-arrow-base-star-routeᵢ
    endpoint-forall-var-arrow-star-star-routeᵢ
    refl
    refl
    endpoint-forall-var-arrow-base-to-starᵢ

endpointMlb-coherence-used-var-base-to-star-right-targetᵢ :
  EndpointMlbCoherenceᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {A′ = ★}
    {B = UsedVarBaseTy}
    {B′ = UsedVarStarTy}
    id★
    endpoint-forall-var-arrow-base-to-starᵢ
endpointMlb-coherence-used-var-base-to-star-right-targetᵢ =
  endpoint-choice-id-selector-coherence-targetᵢ
    {Φ = idᵢ 0}
    {Δᴸ = 0}
    {Δᴿ = 0}
    {A = ★}
    {A′ = ★}
    {B = UsedVarBaseTy}
    {B′ = UsedVarStarTy}
    {pA = id★}
    {pB = endpoint-forall-var-arrow-base-to-starᵢ}
    endpoint-star-forall-var-arrow-base-routeᵢ
    endpoint-star-forall-var-arrow-star-routeᵢ
    refl
    refl
    endpoint-forall-var-arrow-base-to-starᵢ
