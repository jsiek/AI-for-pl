module
  proof.Quotient.NuImprecisionMutualQuotientEliminationExperiment
  where

-- File Charter:
--   * Tests the live mutually recursive quotient narrowing-elimination and
--     widening-compatibility invariant at a higher-order function domain.
--   * Forces function widening to expose contravariant narrowing elimination
--     and covariant widening compatibility recursively.
--   * Lifts the existing two-function-cast fixture by one arrow, so the outer
--     function domain must use the existing function narrowing evidence.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using (Coercion)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import ForallPermutation using
  ( _∣_⊢_⊑ᵖ_⊣_
  ; quotientᵖ
  ; ≈∀-refl
  ; ≈∀-⇒
  ; ⊑ᵖ-arrow-components
  )
open import Imprecision using (idᵢ)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _↦ˢ_)
import ImprecisionWf as IWF
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; _↦_)
open import QuotientImprecisionCompatibility using
  ( ReductionClosedQuotientWideningCompatible
  ; compatible-quotient-functionᴿ
  )
open import Types using
  (Ty; TyCtx; _⇒_)
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientExamples
  using
  ( down-D
  ; down-E
  ; up-D
  ; up-E
  ; inner-D
  ; inner-E
  ; outer-D
  ; outer-E
  ; inner-function-elimination-compatible
  ; outer-function-compatible
  ; identity-function-quotient
  ; identity-A-function⊑identity-A-function
  ; identity-D-function⊑identity-D-function
  )
open import proof.Core.Permutation.ForallPermutationTest using
  ( glb-lower-XY≈YX
  ; glb-lower-XY⊑ᵖYX
  )
open import proof.EndpointMLB.Core.MLBGlbExample using
  ( glb-bad-A
  ; glb-bad-A⊑A
  ; glb-lower-XY
  ; glb-lower-XY⊑A
  ; glb-lower-YX
  ; glb-lower-YX⊑A
  )

------------------------------------------------------------------------
-- Higher-order function-domain fixture
------------------------------------------------------------------------

higher-D : Coercion
higher-D = inner-D C.↦ outer-D

higher-E : Coercion
higher-E = inner-E C.↦ outer-E

higher-ordinary :
  idᵢ zero IWF.∣ zero
    ⊢ (glb-bad-A ⇒ glb-bad-A) ⇒
        (glb-bad-A ⇒ glb-bad-A)
      ⊑
      (glb-bad-A ⇒ glb-bad-A) ⇒
        (glb-bad-A ⇒ glb-bad-A)
    ⊣ zero
higher-ordinary =
  identity-A-function⊑identity-A-function ↦
  identity-A-function⊑identity-A-function

higher-left-ordinary :
  idᵢ zero IWF.∣ zero
    ⊢ (glb-lower-XY ⇒ glb-lower-XY) ⇒
        (glb-lower-XY ⇒ glb-lower-XY)
      ⊑
      (glb-lower-XY ⇒ glb-lower-XY) ⇒
        (glb-lower-XY ⇒ glb-lower-XY)
    ⊣ zero
higher-left-ordinary =
  identity-D-function⊑identity-D-function ↦
  identity-D-function⊑identity-D-function

higher-quotient =
  quotientᵖ
    ≈∀-refl
    higher-left-ordinary
    (≈∀-⇒
      (≈∀-⇒ glb-lower-XY≈YX glb-lower-XY≈YX)
      (≈∀-⇒ glb-lower-XY≈YX glb-lower-XY≈YX))

higher-function-domain-widening-mutual :
  ReductionClosedQuotientWideningCompatible (idᵢ zero) zero zero
    higher-D higher-E higher-quotient higher-ordinary
    ((⌊ glb-lower-XY⊑A ⌋ ↦ˢ ⌊ glb-lower-XY⊑A ⌋) ↦ˢ
      (⌊ glb-lower-XY⊑A ⌋ ↦ˢ ⌊ glb-lower-XY⊑A ⌋))
    ((⌊ glb-lower-YX⊑A ⌋ ↦ˢ ⌊ glb-lower-YX⊑A ⌋) ↦ˢ
      (⌊ glb-lower-YX⊑A ⌋ ↦ˢ ⌊ glb-lower-YX⊑A ⌋))
higher-function-domain-widening-mutual =
  compatible-quotient-functionᴿ
    refl
    inner-function-elimination-compatible
    outer-function-compatible
