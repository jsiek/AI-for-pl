module
  proof.Quotient.NuImprecisionReductionClosedQuotientExamples
  where

-- File Charter:
--   * Tests the smaller quotient relation on two successive function casts.
--   * Uses the incomparable `∀`-permuted lower bounds from the endpoint-MLB
--     examples, so the quotient index is genuinely non-ordinary.
--   * Reduces through an identity lambda, forcing the quotient argument to be
--     substituted before the final smaller-relation derivation.
--   * Uses no quotient-indexed application or fused down/application/up rule.
--   * Does not change the live term-imprecision relation.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥)

import CastImprecisionShape as CastShape
import Coercions as C
import ImprecisionWf as IWF
import NarrowWiden as NW
import Types
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import ForallPermutation using
  (quotientᵖ; ≈∀-refl; ≈∀-⇒)
open import Imprecision using (idᵢ)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _↦ˢ_
  ; _；⌊_⌋≋ᵖ_；_
  ; source-perm-refl
  ; source-perm-↦
  ; source-swap-∀ν
  ; quotient-boundary-square
  ; comp-↦-↦
  ; comp-∀-∀
  ; comp-∀-ν
  ; comp-idˣ-idˣ
  ; comp-idˣ-tagˣ
  ; comp-ν
  ; comp-tagˣ-id★
  )
open import NuReduction using
  ( keep
  ; pure-step
  ; ξ-⟨⟩
  ; β
  ; β-↦
  ; ↠-step
  ; ↠-refl
  ; _—↠[_]_
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( ctx-imp
  )
open import NuTerms using
  ( Term
  ; Value
  ; No•
  ; no•-⟨⟩
  ; `_
  ; ƛ_
  ; _·_
  ; _⟨_⟩
  ; _[_]
  )
open import QuotientedTermImprecision using
  ( ƛ⊑ƛᵀ
  ; x⊑xᵀ
  ; ·⊑·ᵀ
  ; paired-downᵀ
  ; closeᵀ
  ; quotient-id-widening
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using
  ( Ty
  ; _⇒_
  )
open import proof.Compilation.CompileCoercions using
  (coerce-downⁿ-shape-idᵢ; coerce-upʷ-shape-idᵢ)
open import proof.Core.Permutation.ForallPermutationTest using
  ( glb-lower-XY≈YX
  ; glb-lower-XY⊑XY
  ; glb-lower-YX⊑YX
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
open import QuotientImprecisionCompatibility
  using
  ( id-only↓
  ; compatible-functionᴿ
  ; compatible-target-activeᴿ
  ; ReductionClosedQuotientWideningCompatible
  ; compatible-through-representativesᴿ
  )
open import
  proof.Quotient.NuImprecisionQuotientNarrowingEliminationCompatibility
  using
  ( QuotientNarrowingEliminationCompatible
  ; function-elimination
  ; non-function-elimination
  ; non-function-universal
  ; source-non-function
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientSingleSubstitutionExperiment
  using (smaller-single-term-substitutionᴿ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-idᵢ)
open import
  proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionLemma
  using (quotiented-parallel-term-substitution-lemmaᵀ)
open import
  proof.Substitution.Term.NuImprecisionSingleSubstitutionEnvironmentLemma
  using (quotiented-single-substitution-environment-lemmaᵀ)
open import
  proof.Substitution.Term.NuImprecisionTermSubstitutionProof
  using (quotiented-term-substitution-proofᵀ)

------------------------------------------------------------------------
-- One nontrivial down/up round trip
------------------------------------------------------------------------

down-D-result =
  coerce-downⁿ-shape-idᵢ 81 glb-lower-XY⊑A

down-E-result =
  coerce-downⁿ-shape-idᵢ 81 glb-lower-YX⊑A

down-D : C.Coercion
down-D = proj₁ down-D-result

down-E : C.Coercion
down-E = proj₁ down-E-result

up-D-result =
  coerce-upʷ-shape-idᵢ 82 glb-lower-XY⊑A

up-E-result =
  coerce-upʷ-shape-idᵢ 82 glb-lower-YX⊑A

up-D : C.Coercion
up-D = proj₁ up-D-result

up-E : C.Coercion
up-E = proj₁ up-E-result

down-D-inert : C.Inert down-D
down-D-inert = C.`∀ _

down-E-inert : C.Inert down-E
down-E-inert = C.gen _ _

up-D-inert : C.Inert up-D
up-D-inert = C.`∀ _

up-E-not-inert : C.Inert up-E → ⊥
up-E-not-inert ()

route-quotient-square :
  ⌊ glb-lower-XY⊑A ⌋ ；⌊ glb-bad-A⊑A ⌋≋ᵖ
    glb-lower-XY⊑ᵖYX ； ⌊ glb-lower-YX⊑A ⌋
route-quotient-square =
  quotient-boundary-square
    source-perm-refl
    (comp-∀-∀
      (comp-ν
        (comp-↦-↦ comp-idˣ-idˣ comp-tagˣ-id★)))
    source-swap-∀ν
    (comp-∀-∀
      (comp-∀-ν
        (comp-↦-↦ comp-idˣ-idˣ comp-idˣ-tagˣ)))

route-widening-compatible :
  ReductionClosedQuotientWideningCompatible (idᵢ zero) zero zero
    up-D up-E glb-lower-XY⊑ᵖYX glb-bad-A⊑A
    ⌊ glb-lower-XY⊑A ⌋ ⌊ glb-lower-YX⊑A ⌋
route-widening-compatible =
  compatible-through-representativesᴿ
    source-perm-refl source-swap-∀ν
    (compatible-target-activeᴿ up-D-inert up-E-not-inert)

down-routeᴿ :
  ∀ {M M′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ M ⊑ M′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿᵖ M ⟨ down-D ⟩ ⊑ M′ ⟨ down-E ⟩
    ⦂ glb-lower-XY ⊑ᵖ glb-lower-YX
    ∶ glb-lower-XY⊑ᵖYX
down-routeᴿ relation =
  paired-downᴿ relation
    id-only↓
    (proj₁ (proj₂ down-D-result))
    (proj₂ (proj₂ down-D-result))
    id-only↓
    (proj₁ (proj₂ down-E-result))
    (proj₂ (proj₂ down-E-result))
    route-quotient-square

close-routeᴿ :
  ∀ {M M′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿᵖ M ⊑ M′
    ⦂ glb-lower-XY ⊑ᵖ glb-lower-YX
    ∶ glb-lower-XY⊑ᵖYX →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ M ⟨ up-D ⟩ ⊑ M′ ⟨ up-E ⟩
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
close-routeᴿ relation =
  closeᴿ relation
    (quotient-id-wideningᴿ
      (proj₁ (proj₂ up-D-result))
      (proj₁ (proj₂ up-E-result)))
    (proj₂ (proj₂ up-D-result))
    (proj₂ (proj₂ up-E-result))
    route-quotient-square
    route-widening-compatible

round-tripᴿ :
  ∀ {M M′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ M ⊑ M′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ (M ⟨ down-D ⟩) ⟨ up-D ⟩
      ⊑ (M′ ⟨ down-E ⟩) ⟨ up-E ⟩
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
round-tripᴿ relation = close-routeᴿ (down-routeᴿ relation)

------------------------------------------------------------------------
-- The same round trip returns to the existing ordinary QTI relation
------------------------------------------------------------------------

down-routeᵀ :
  ∀ {M M′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ M ⊑ M′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᵖ M ⟨ down-D ⟩ ⊑ M′ ⟨ down-E ⟩
    ⦂ glb-lower-XY ⊑ᵖ glb-lower-YX
    ∶ glb-lower-XY⊑ᵖYX
down-routeᵀ relation =
  paired-downᵀ relation
    id-only↓
    (proj₁ (proj₂ down-D-result))
    (proj₂ (proj₂ down-D-result))
    id-only↓
    (proj₁ (proj₂ down-E-result))
    (proj₂ (proj₂ down-E-result))
    route-quotient-square

close-routeᵀ :
  ∀ {M M′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᵖ M ⊑ M′
    ⦂ glb-lower-XY ⊑ᵖ glb-lower-YX
    ∶ glb-lower-XY⊑ᵖYX →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ M ⟨ up-D ⟩ ⊑ M′ ⟨ up-E ⟩
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
close-routeᵀ relation =
  closeᵀ relation
    (quotient-id-widening
      (proj₁ (proj₂ up-D-result))
      (proj₁ (proj₂ up-E-result)))
    glb-bad-A⊑A
    (proj₂ (proj₂ up-D-result))
    (proj₂ (proj₂ up-E-result))
    route-quotient-square
    route-widening-compatible

round-tripᵀ :
  ∀ {M M′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ M ⊑ M′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ (M ⟨ down-D ⟩) ⟨ up-D ⟩
      ⊑ (M′ ⟨ down-E ⟩) ⟨ up-E ⟩
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
round-tripᵀ relation = close-routeᵀ (down-routeᵀ relation)

------------------------------------------------------------------------
-- The paired inner narrowing and outer widening function casts
------------------------------------------------------------------------

lower-identity-D⊑A :
  idᵢ zero IWF.∣ zero
    ⊢ glb-lower-XY ⇒ glb-lower-XY
      ⊑ glb-bad-A ⇒ glb-bad-A
    ⊣ zero
lower-identity-D⊑A =
  glb-lower-XY⊑A IWF.↦ glb-lower-XY⊑A

lower-identity-E⊑A :
  idᵢ zero IWF.∣ zero
    ⊢ glb-lower-YX ⇒ glb-lower-YX
      ⊑ glb-bad-A ⇒ glb-bad-A
    ⊣ zero
lower-identity-E⊑A =
  glb-lower-YX⊑A IWF.↦ glb-lower-YX⊑A

identity-A-function⊑identity-A-function :
  idᵢ zero IWF.∣ zero
    ⊢ glb-bad-A ⇒ glb-bad-A
      ⊑ glb-bad-A ⇒ glb-bad-A
    ⊣ zero
identity-A-function⊑identity-A-function =
  glb-bad-A⊑A IWF.↦ glb-bad-A⊑A

identity-D-function⊑identity-D-function :
  idᵢ zero IWF.∣ zero
    ⊢ glb-lower-XY ⇒ glb-lower-XY
      ⊑ glb-lower-XY ⇒ glb-lower-XY
    ⊣ zero
identity-D-function⊑identity-D-function =
  glb-lower-XY⊑XY IWF.↦ glb-lower-XY⊑XY

identity-function-quotient =
  quotientᵖ ≈∀-refl
    identity-D-function⊑identity-D-function
    (≈∀-⇒ glb-lower-XY≈YX glb-lower-XY≈YX)

inner-D : C.Coercion
inner-D = up-D C.↦ down-D

inner-E : C.Coercion
inner-E = up-E C.↦ down-E

outer-D : C.Coercion
outer-D = down-D C.↦ up-D

outer-E : C.Coercion
outer-E = down-E C.↦ up-E

inner-D-inert : C.Inert inner-D
inner-D-inert = up-D C.↦ down-D

inner-E-inert : C.Inert inner-E
inner-E-inert = up-E C.↦ down-E

outer-D-inert : C.Inert outer-D
outer-D-inert = down-D C.↦ up-D

outer-E-inert : C.Inert outer-E
outer-E-inert = down-E C.↦ up-E

inner-D-typing :
  C.id-onlyᵈ ∣ zero ∣ []
    ⊢ inner-D
      ∶ glb-bad-A ⇒ glb-bad-A
      ⊒ glb-lower-XY ⇒ glb-lower-XY
inner-D-typing =
  C.cast-fun
    (proj₁ (proj₁ (proj₂ up-D-result)))
    (proj₁ (proj₁ (proj₂ down-D-result))) ,
  NW.cross
    (proj₂ (proj₁ (proj₂ up-D-result))
      NW.↦ proj₂ (proj₁ (proj₂ down-D-result)))

inner-E-typing :
  C.id-onlyᵈ ∣ zero ∣ []
    ⊢ inner-E
      ∶ glb-bad-A ⇒ glb-bad-A
      ⊒ glb-lower-YX ⇒ glb-lower-YX
inner-E-typing =
  C.cast-fun
    (proj₁ (proj₁ (proj₂ up-E-result)))
    (proj₁ (proj₁ (proj₂ down-E-result))) ,
  NW.cross
    (proj₂ (proj₁ (proj₂ up-E-result))
      NW.↦ proj₂ (proj₁ (proj₂ down-E-result)))

outer-D-typing :
  C.id-onlyᵈ ∣ zero ∣ []
    ⊢ outer-D
      ∶ glb-lower-XY ⇒ glb-lower-XY
      ⊑ glb-bad-A ⇒ glb-bad-A
outer-D-typing =
  C.cast-fun
    (proj₁ (proj₁ (proj₂ down-D-result)))
    (proj₁ (proj₁ (proj₂ up-D-result))) ,
  NW.cross
    (proj₂ (proj₁ (proj₂ down-D-result))
      NW.↦ proj₂ (proj₁ (proj₂ up-D-result)))

outer-E-typing :
  C.id-onlyᵈ ∣ zero ∣ []
    ⊢ outer-E
      ∶ glb-lower-YX ⇒ glb-lower-YX
      ⊑ glb-bad-A ⇒ glb-bad-A
outer-E-typing =
  C.cast-fun
    (proj₁ (proj₁ (proj₂ down-E-result)))
    (proj₁ (proj₁ (proj₂ up-E-result))) ,
  NW.cross
    (proj₂ (proj₁ (proj₂ down-E-result))
      NW.↦ proj₂ (proj₁ (proj₂ up-E-result)))

identity-function-quotient-square :
  (⌊ glb-lower-XY⊑A ⌋ ↦ˢ ⌊ glb-lower-XY⊑A ⌋)
    ；⌊ identity-A-function⊑identity-A-function ⌋≋ᵖ
      identity-function-quotient ；
    (⌊ glb-lower-YX⊑A ⌋ ↦ˢ ⌊ glb-lower-YX⊑A ⌋)
identity-function-quotient-square =
  quotient-boundary-square
    source-perm-refl
    (comp-↦-↦
      (comp-∀-∀
        (comp-ν
          (comp-↦-↦ comp-idˣ-idˣ comp-tagˣ-id★)))
      (comp-∀-∀
        (comp-ν
          (comp-↦-↦ comp-idˣ-idˣ comp-tagˣ-id★))))
    (source-perm-↦ source-swap-∀ν source-swap-∀ν)
    (comp-↦-↦
      (comp-∀-∀
        (comp-∀-ν
          (comp-↦-↦ comp-idˣ-idˣ comp-idˣ-tagˣ)))
      (comp-∀-∀
        (comp-∀-ν
          (comp-↦-↦ comp-idˣ-idˣ comp-idˣ-tagˣ))))

outer-function-compatible :
  ReductionClosedQuotientWideningCompatible (idᵢ zero) zero zero
    outer-D outer-E identity-function-quotient
    identity-A-function⊑identity-A-function
    (⌊ glb-lower-XY⊑A ⌋ ↦ˢ ⌊ glb-lower-XY⊑A ⌋)
    (⌊ glb-lower-YX⊑A ⌋ ↦ˢ ⌊ glb-lower-YX⊑A ⌋)
outer-function-compatible =
  compatible-through-representativesᴿ
    source-perm-refl
    (source-perm-↦ source-swap-∀ν source-swap-∀ν)
    (compatible-functionᴿ
      (compatible-target-activeᴿ up-D-inert up-E-not-inert))

inner-function-elimination-compatible :
  QuotientNarrowingEliminationCompatible (idᵢ zero) zero zero
    inner-D inner-E
    identity-A-function⊑identity-A-function
    identity-function-quotient
    (⌊ glb-lower-XY⊑A ⌋ ↦ˢ ⌊ glb-lower-XY⊑A ⌋)
    (⌊ glb-lower-YX⊑A ⌋ ↦ˢ ⌊ glb-lower-YX⊑A ⌋)
inner-function-elimination-compatible =
  function-elimination
    refl
    route-widening-compatible
    (non-function-elimination
      (source-non-function non-function-universal))

identity-A⊑identity-A :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ ƛ (` zero) ⊑ ƛ (` zero)
    ⦂ glb-bad-A ⇒ glb-bad-A
    ⊑ glb-bad-A ⇒ glb-bad-A
    ∶ identity-A-function⊑identity-A-function
identity-A⊑identity-A =
  ƛ⊑ƛᵀ
    (IWF.⊑-src-wf glb-bad-A⊑A)
    (IWF.⊑-tgt-wf glb-bad-A⊑A)
    (x⊑xᵀ Types.Z)

identity-A⊑identity-Aᴿ :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ ƛ (` zero) ⊑ ƛ (` zero)
    ⦂ glb-bad-A ⇒ glb-bad-A
    ⊑ glb-bad-A ⇒ glb-bad-A
    ∶ identity-A-function⊑identity-A-function
identity-A⊑identity-Aᴿ =
  ƛ⊑ƛᴿ
    (IWF.⊑-src-wf glb-bad-A⊑A)
    (IWF.⊑-tgt-wf glb-bad-A⊑A)
    (x⊑xᴿ Types.Z)

closed-identity-functionsᴿ :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ ((ƛ (` zero)) ⟨ inner-D ⟩) ⟨ outer-D ⟩
      ⊑ ((ƛ (` zero)) ⟨ inner-E ⟩) ⟨ outer-E ⟩
    ⦂ glb-bad-A ⇒ glb-bad-A
    ⊑ glb-bad-A ⇒ glb-bad-A
    ∶ identity-A-function⊑identity-A-function
closed-identity-functionsᴿ =
  closeᴿ
    (paired-downᴿ
      identity-A⊑identity-Aᴿ
      id-only↓
      inner-D-typing
      (CastShape.shape-fun
        (proj₂ (proj₂ up-D-result))
        (proj₂ (proj₂ down-D-result)))
      id-only↓
      inner-E-typing
      (CastShape.shape-fun
        (proj₂ (proj₂ up-E-result))
        (proj₂ (proj₂ down-E-result)))
      identity-function-quotient-square)
    (quotient-id-wideningᴿ outer-D-typing outer-E-typing)
    (CastShape.shape-fun
      (proj₂ (proj₂ down-D-result))
      (proj₂ (proj₂ up-D-result)))
    (CastShape.shape-fun
      (proj₂ (proj₂ down-E-result))
      (proj₂ (proj₂ up-E-result)))
    identity-function-quotient-square
    outer-function-compatible

closed-identity-functionsᵀ :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ ((ƛ (` zero)) ⟨ inner-D ⟩) ⟨ outer-D ⟩
      ⊑ ((ƛ (` zero)) ⟨ inner-E ⟩) ⟨ outer-E ⟩
    ⦂ glb-bad-A ⇒ glb-bad-A
    ⊑ glb-bad-A ⇒ glb-bad-A
    ∶ identity-A-function⊑identity-A-function
closed-identity-functionsᵀ =
  closeᵀ
    (paired-downᵀ
      identity-A⊑identity-A
      id-only↓
      inner-D-typing
      (CastShape.shape-fun
        (proj₂ (proj₂ up-D-result))
        (proj₂ (proj₂ down-D-result)))
      id-only↓
      inner-E-typing
      (CastShape.shape-fun
        (proj₂ (proj₂ up-E-result))
        (proj₂ (proj₂ down-E-result)))
      identity-function-quotient-square)
    (quotient-id-widening outer-D-typing outer-E-typing)
    identity-A-function⊑identity-A-function
    (CastShape.shape-fun
      (proj₂ (proj₂ down-D-result))
      (proj₂ (proj₂ up-D-result)))
    (CastShape.shape-fun
      (proj₂ (proj₂ down-E-result))
      (proj₂ (proj₂ up-E-result)))
    identity-function-quotient-square
    outer-function-compatible

related-two-function-cast-applicationsᴿ :
  ∀ {W W′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ W ⊑ W′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ
      (((ƛ (` zero)) ⟨ inner-D ⟩) ⟨ outer-D ⟩) · W
      ⊑
      (((ƛ (` zero)) ⟨ inner-E ⟩) ⟨ outer-E ⟩) · W′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
related-two-function-cast-applicationsᴿ W⊑W′ =
  closed-identity-functionsᴿ ·ᴿ W⊑W′

related-two-function-cast-applicationsᵀ :
  ∀ {W W′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ W ⊑ W′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ
      (((ƛ (` zero)) ⟨ inner-D ⟩) ⟨ outer-D ⟩) · W
      ⊑
      (((ƛ (` zero)) ⟨ inner-E ⟩) ⟨ outer-E ⟩) · W′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
related-two-function-cast-applicationsᵀ W⊑W′ =
  ·⊑·ᵀ closed-identity-functionsᵀ W⊑W′

------------------------------------------------------------------------
-- Reducing both successive function casts and the identity beta-redex
------------------------------------------------------------------------

two-function-casts-two-beta-reduction :
  ∀ {W c₁ d₁ c₂ d₂} →
  Value W →
  C.Inert c₂ →
  ((((ƛ (` zero)) ⟨ c₁ C.↦ d₁ ⟩)
      ⟨ c₂ C.↦ d₂ ⟩) · W)
    —↠[ keep ∷ keep ∷ [] ]
  (((ƛ (` zero)) · ((W ⟨ c₂ ⟩) ⟨ c₁ ⟩)) ⟨ d₁ ⟩)
    ⟨ d₂ ⟩
two-function-casts-two-beta-reduction
    {W} {c₁} {d₁} {c₂} {d₂} vW inert-c₂ =
  ↠-step
    (pure-step
      (β-↦
        ((ƛ (` zero)) ⟨ c₁ C.↦ d₁ ⟩)
        vW))
    (↠-step
      (ξ-⟨⟩
        (pure-step
          (β-↦
            (ƛ (` zero))
            (vW ⟨ inert-c₂ ⟩))))
      ↠-refl)


two-function-casts-identity-reduction :
  ∀ {W c₁ d₁ c₂ d₂} →
  Value W →
  C.Inert c₁ →
  C.Inert c₂ →
  ((((ƛ (` zero)) ⟨ c₁ C.↦ d₁ ⟩)
      ⟨ c₂ C.↦ d₂ ⟩) · W)
    —↠[ keep ∷ keep ∷ keep ∷ [] ]
  ((((W ⟨ c₂ ⟩) ⟨ c₁ ⟩) ⟨ d₁ ⟩) ⟨ d₂ ⟩)
two-function-casts-identity-reduction
    {W} {c₁} {d₁} {c₂} {d₂} vW inert-c₁ inert-c₂ =
  ↠-step
    (pure-step
      (β-↦
        ((ƛ (` zero)) ⟨ c₁ C.↦ d₁ ⟩)
        vW))
    (↠-step
      (ξ-⟨⟩
        (pure-step
          (β-↦
            (ƛ (` zero))
            (vW ⟨ inert-c₂ ⟩))))
      (↠-step
        (ξ-⟨⟩
          (ξ-⟨⟩
            (pure-step
              (β ((vW ⟨ inert-c₂ ⟩) ⟨ inert-c₁ ⟩)))))
        ↠-refl))

-- Relation-level endpoint after both round trips
------------------------------------------------------------------------

two-round-tripsᴿ :
  ∀ {W W′ : Term} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ W ⊑ W′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ
      ((((W ⟨ down-D ⟩) ⟨ up-D ⟩) ⟨ down-D ⟩)
        ⟨ up-D ⟩)
      ⊑
      ((((W′ ⟨ down-E ⟩) ⟨ up-E ⟩) ⟨ down-E ⟩)
        ⟨ up-E ⟩)
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
two-round-tripsᴿ W⊑W′ =
  round-tripᴿ (round-tripᴿ W⊑W′)

two-round-tripsᵀ :
  ∀ {W W′ : Term} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ W ⊑ W′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ
      ((((W ⟨ down-D ⟩) ⟨ up-D ⟩) ⟨ down-D ⟩)
        ⟨ up-D ⟩)
      ⊑
      ((((W′ ⟨ down-E ⟩) ⟨ up-E ⟩) ⟨ down-E ⟩)
        ⟨ up-E ⟩)
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
two-round-tripsᵀ W⊑W′ =
  round-tripᵀ (round-tripᵀ W⊑W′)

------------------------------------------------------------------------
-- Arbitrary lambda bodies accept the closed quotient argument
------------------------------------------------------------------------

two-round-trips-substitutionᵀ :
  ∀ {N N′ W W′ B B′ pB} →
  No• N →
  No• N′ →
  No• W →
  No• W′ →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣
      ctx-imp glb-bad-A glb-bad-A glb-bad-A⊑A ∷ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ W ⊑ W′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ
      N [
        ((((W ⟨ down-D ⟩) ⟨ up-D ⟩) ⟨ down-D ⟩)
          ⟨ up-D ⟩)
      ]
      ⊑
      N′ [
        ((((W′ ⟨ down-E ⟩) ⟨ up-E ⟩) ⟨ down-E ⟩)
          ⟨ up-E ⟩)
      ]
    ⦂ B ⊑ B′ ∶ pB
two-round-trips-substitutionᵀ
    noN noN′ noW noW′ body W⊑W′ =
  quotiented-term-substitution-proofᵀ
    quotiented-parallel-term-substitution-lemmaᵀ
    quotiented-single-substitution-environment-lemmaᵀ
    (assumption-membership-unique-idᵢ zero)
    noN noN′
    (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ noW))))
    (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ noW′))))
    body
    (two-round-tripsᵀ W⊑W′)

two-round-trips-substitutionᴿ :
  ∀ {N N′ W W′ B B′ pB} →
  No• N →
  No• N′ →
  No• W →
  No• W′ →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣
      ctx-imp glb-bad-A glb-bad-A glb-bad-A⊑A ∷ []
    ⊢ᴿ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ W ⊑ W′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ
      N [
        ((((W ⟨ down-D ⟩) ⟨ up-D ⟩) ⟨ down-D ⟩)
          ⟨ up-D ⟩)
      ]
      ⊑
      N′ [
        ((((W′ ⟨ down-E ⟩) ⟨ up-E ⟩) ⟨ down-E ⟩)
          ⟨ up-E ⟩)
      ]
    ⦂ B ⊑ B′ ∶ pB
two-round-trips-substitutionᴿ
    noN noN′ noW noW′ body W⊑W′ =
  smaller-single-term-substitutionᴿ
    (assumption-membership-unique-idᵢ zero)
    noN noN′
    (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ noW))))
    (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ noW′))))
    body
    (two-round-tripsᴿ W⊑W′)

------------------------------------------------------------------------
-- The inert route takes the expected three beta steps
------------------------------------------------------------------------

source-two-function-casts-identity-reduction :
  ∀ {W} →
  Value W →
  ((((ƛ (` zero)) ⟨ inner-D ⟩) ⟨ outer-D ⟩) · W)
    —↠[ keep ∷ keep ∷ keep ∷ [] ]
  ((((W ⟨ down-D ⟩) ⟨ up-D ⟩) ⟨ down-D ⟩)
    ⟨ up-D ⟩)
source-two-function-casts-identity-reduction vW =
  two-function-casts-identity-reduction
    vW up-D-inert down-D-inert

------------------------------------------------------------------------
-- The permuted route must allocate before the second function beta
------------------------------------------------------------------------

target-first-function-cast-reduction :
  ∀ {W′} →
  Value W′ →
  ((((ƛ (` zero)) ⟨ inner-E ⟩) ⟨ outer-E ⟩) · W′)
    —↠[ keep ∷ [] ]
  (((ƛ (` zero)) ⟨ inner-E ⟩) · (W′ ⟨ down-E ⟩))
    ⟨ up-E ⟩
target-first-function-cast-reduction vW′ =
  ↠-step
    (pure-step
      (β-↦
        ((ƛ (` zero)) ⟨ inner-E-inert ⟩)
        vW′))
    ↠-refl

target-round-trip-argument-not-value :
  ∀ {W′} →
  Value ((W′ ⟨ down-E ⟩) ⟨ up-E ⟩) →
  ⊥
target-round-trip-argument-not-value
    ((vW′ ⟨ down-inert ⟩) ⟨ up-inert ⟩) =
  up-E-not-inert up-inert

------------------------------------------------------------------------
-- The bilateral square stops after the quotient argument has closed
------------------------------------------------------------------------

two-function-casts-two-beta-joinᴿ :
  ∀ {W W′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ W ⊑ W′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ
      (((ƛ (` zero)) · ((W ⟨ down-D ⟩) ⟨ up-D ⟩))
        ⟨ down-D ⟩) ⟨ up-D ⟩
      ⊑
      (((ƛ (` zero)) · ((W′ ⟨ down-E ⟩) ⟨ up-E ⟩))
        ⟨ down-E ⟩) ⟨ up-E ⟩
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
two-function-casts-two-beta-joinᴿ W⊑W′ =
  round-tripᴿ
    (identity-A⊑identity-Aᴿ ·ᴿ round-tripᴿ W⊑W′)


two-function-casts-squareᴿ :
  ∀ {W W′} →
  Value W →
  Value W′ →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ W ⊑ W′
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A →
  idᵢ zero ∣ zero ∣ zero ∣ []
    ⊢ᴿ↠
      ((((ƛ (` zero)) ⟨ inner-D ⟩) ⟨ outer-D ⟩) · W)
      ⊑
      ((((ƛ (` zero)) ⟨ inner-E ⟩) ⟨ outer-E ⟩) · W′)
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
two-function-casts-squareᴿ {W} {W′} vW vW′ W⊑W′ =
  record
    { sourceChanges = keep ∷ keep ∷ []
    ; targetChanges = keep ∷ keep ∷ []
    ; sourceResult =
        (((ƛ (` zero)) · ((W ⟨ down-D ⟩) ⟨ up-D ⟩))
          ⟨ down-D ⟩) ⟨ up-D ⟩
    ; targetResult =
        (((ƛ (` zero)) · ((W′ ⟨ down-E ⟩) ⟨ up-E ⟩))
          ⟨ down-E ⟩) ⟨ up-E ⟩
    ; resultCtx = idᵢ zero
    ; resultLeftCtx = zero
    ; resultRightCtx = zero
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = []
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; resultSourceType = glb-bad-A
    ; resultTargetType = glb-bad-A
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = λ relation → relation
    ; sourceReduction =
        two-function-casts-two-beta-reduction vW down-D-inert
    ; targetReduction =
        two-function-casts-two-beta-reduction vW′ down-E-inert
    ; resultImprecision =
        two-function-casts-two-beta-joinᴿ W⊑W′
    }
