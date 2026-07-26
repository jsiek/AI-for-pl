module
  proof.Quotient.NuImprecisionSingleNarrowingBoundaryExamples
  where

-- File Charter:
--   * Tests whether bilateral reduction makes one paired narrowing boundary
--     sufficient for quotient term imprecision.
--   * Uses two same-polarity function widenings whose beta reductions expose
--     two genuinely quotient-producing narrowing casts around the argument.
--   * Checks that a finite narrowing spine relates the exposed prefix and that
--     the one-boundary prototype cannot relate that same prefix.
--   * Proves the first prefix is quotient-related but not ordinarily related,
--     so the doubly cast top terms are outside the live relation.
--   * Records the corresponding four-cast reduction endpoint as an
--     expressiveness diagnostic, not as a simulation counterexample.
--   * Does not change or re-export the live term-imprecision relation.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import Coercions as C
import ImprecisionWf as IWF
import CastImprecisionShape as CastShape

open import ForallPermutation using
  (quotientᵖ; ≈∀-refl; ≈∀-⇒)
open import Imprecision using (idᵢ; _ˣ⊑ˣ_)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _↦ˢ_
  ; _；_≋_
  ; _；⌊_⌋≋ᵖ_；_
  ; comp-id★
  ; comp-idˣ-idˣ
  ; comp-idˣ-tagˣ
  ; comp-↦-↦
  ; comp-∀-∀
  ; comp-∀-ν
  ; comp-tagˣ-id★
  ; comp-ν
  ; source-perm-refl
  ; source-perm-↦
  ; source-swap-∀ν
  ; quotient-boundary-square
  )
open import NuReduction using (keep; _—↠[_]_)
open import NuTerms using (Term; Value; `_; ƛ_; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; _⇒_)
open import proof.Compilation.CompileCoercions using
  (coerce-downⁿ-shape-idᵢ; coerce-upʷ-shape-idᵢ)
open import proof.Core.Properties.CoercionProperties using
  (coercion-src-tgtᵐ)
open import proof.Core.Permutation.ForallPermutationTest using
  ( glb-lower-XY≈YX
  ; glb-lower-XY⊑XY
  ; glb-lower-YX⊑YX
  )
open import proof.EndpointMLB.Core.MLBGlbExample using
  ( glb-bad-A
  ; glb-bad-A⊑A
  ; glb-lower-XY
  ; glb-lower-XY⊑A
  ; glb-lower-YX
  ; glb-lower-YX⊑A
  )
open import
  proof.Quotient.NuImprecisionCompositionalQuotientDef
  using
  ( cast-spine
  ; id-only↓
  ; single↓
  ; extend↓
  ; _∣_∣_∣_∣_⊢ᴺᶜ[_]_⊑_⦂_⊑ᵖ_∶_
  ; paired-spinesᶜ
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( _∣_∣_∣_∣_⊢ᴿᵖ_⊑_⦂_⊑ᵖ_∶_
  ; ordinaryᴿ
  ; paired-downᴿ
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientExamples
  using
  ( identity-A-function⊑identity-A-function
  ; identity-function-quotient
  ; identity-function-quotient-square
  ; two-function-casts-identity-reduction
  )

------------------------------------------------------------------------
-- Two proper narrowing stages between a common type and the quotient
------------------------------------------------------------------------

first-source-domain : Ty
first-source-domain = glb-lower-XY ⇒ glb-bad-A

first-target-domain : Ty
first-target-domain = glb-lower-YX ⇒ glb-bad-A

final-source-domain : Ty
final-source-domain = glb-lower-XY ⇒ glb-lower-XY

final-target-domain : Ty
final-target-domain = glb-lower-YX ⇒ glb-lower-YX

first-source-below-common :
  idᵢ zero IWF.∣ zero ⊢ first-source-domain
    ⊑ glb-bad-A ⇒ glb-bad-A ⊣ zero
first-source-below-common =
  glb-lower-XY⊑A IWF.↦ glb-bad-A⊑A

first-target-below-common :
  idᵢ zero IWF.∣ zero ⊢ first-target-domain
    ⊑ glb-bad-A ⇒ glb-bad-A ⊣ zero
first-target-below-common =
  glb-lower-YX⊑A IWF.↦ glb-bad-A⊑A

final-source-below-first :
  idᵢ zero IWF.∣ zero ⊢ final-source-domain
    ⊑ first-source-domain ⊣ zero
final-source-below-first =
  glb-lower-XY⊑XY IWF.↦ glb-lower-XY⊑A

final-target-below-first :
  idᵢ zero IWF.∣ zero ⊢ final-target-domain
    ⊑ first-target-domain ⊣ zero
final-target-below-first =
  glb-lower-YX⊑YX IWF.↦ glb-lower-YX⊑A

first-source-reflexive :
  idᵢ zero IWF.∣ zero ⊢ first-source-domain
    ⊑ first-source-domain ⊣ zero
first-source-reflexive =
  glb-lower-XY⊑XY IWF.↦ glb-bad-A⊑A

first-domain-quotient =
  quotientᵖ ≈∀-refl first-source-reflexive
    (≈∀-⇒ glb-lower-XY≈YX ≈∀-refl)

first-source-down-result =
  coerce-downⁿ-shape-idᵢ 83 first-source-below-common

first-target-down-result =
  coerce-downⁿ-shape-idᵢ 83 first-target-below-common

second-source-down-result =
  coerce-downⁿ-shape-idᵢ 84 final-source-below-first

second-target-down-result =
  coerce-downⁿ-shape-idᵢ 84 final-target-below-first

first-source-down : C.Coercion
first-source-down = proj₁ first-source-down-result

first-target-down : C.Coercion
first-target-down = proj₁ first-target-down-result

second-source-down : C.Coercion
second-source-down = proj₁ second-source-down-result

second-target-down : C.Coercion
second-target-down = proj₁ second-target-down-result

source-self-then-lower :
  ⌊ glb-lower-XY⊑XY ⌋
    ； ⌊ glb-lower-XY⊑A ⌋
    ≋ ⌊ glb-lower-XY⊑A ⌋
source-self-then-lower =
  comp-∀-∀
    (comp-∀-ν
      (comp-↦-↦ comp-idˣ-idˣ comp-idˣ-tagˣ))

target-self-then-lower :
  ⌊ glb-lower-YX⊑YX ⌋
    ； ⌊ glb-lower-YX⊑A ⌋
    ≋ ⌊ glb-lower-YX⊑A ⌋
target-self-then-lower =
  comp-∀-ν
    (comp-∀-∀
      (comp-↦-↦ comp-idˣ-idˣ comp-idˣ-tagˣ))

source-lower-then-common-self :
  ⌊ glb-lower-XY⊑A ⌋
    ； ⌊ glb-bad-A⊑A ⌋
    ≋ ⌊ glb-lower-XY⊑A ⌋
source-lower-then-common-self =
  comp-∀-∀
    (comp-ν
      (comp-↦-↦ comp-idˣ-idˣ comp-tagˣ-id★))

target-lower-then-common-self :
  ⌊ glb-lower-YX⊑A ⌋
    ； ⌊ glb-bad-A⊑A ⌋
    ≋ ⌊ glb-lower-YX⊑A ⌋
target-lower-then-common-self =
  comp-ν
    (comp-∀-∀
      (comp-↦-↦ comp-idˣ-idˣ comp-tagˣ-id★))

common-self-compose :
  ⌊ glb-bad-A⊑A ⌋ ； ⌊ glb-bad-A⊑A ⌋
    ≋ ⌊ glb-bad-A⊑A ⌋
common-self-compose =
  comp-∀-∀
    (comp-↦-↦ comp-idˣ-idˣ comp-id★)

first-domain-quotient-square :
  ⌊ first-source-below-common ⌋
    ；⌊ identity-A-function⊑identity-A-function ⌋≋ᵖ
    first-domain-quotient ； ⌊ first-target-below-common ⌋
first-domain-quotient-square =
  quotient-boundary-square
    source-perm-refl
    (comp-↦-↦ source-lower-then-common-self
      common-self-compose)
    (source-perm-↦ source-swap-∀ν source-perm-refl)
    (comp-↦-↦ source-self-then-lower
      common-self-compose)

source-two-down-shapes :
  ⌊ final-source-below-first ⌋
    ； ⌊ first-source-below-common ⌋
    ≋ ⌊
      glb-lower-XY⊑A IWF.↦ glb-lower-XY⊑A
    ⌋
source-two-down-shapes =
  comp-↦-↦ source-self-then-lower
    source-lower-then-common-self

target-two-down-shapes :
  ⌊ final-target-below-first ⌋
    ； ⌊ first-target-below-common ⌋
    ≋ ⌊
      glb-lower-YX⊑A IWF.↦ glb-lower-YX⊑A
    ⌋
target-two-down-shapes =
  comp-↦-↦ target-self-then-lower
    target-lower-then-common-self

first-genuine-downᴿ :
  ∀ {W W′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ W ⊑ W′
    ⦂ glb-bad-A ⇒ glb-bad-A
    ⊑ glb-bad-A ⇒ glb-bad-A
    ∶ identity-A-function⊑identity-A-function →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿᵖ W ⟨ first-source-down ⟩
      ⊑ W′ ⟨ first-target-down ⟩
    ⦂ first-source-domain ⊑ᵖ first-target-domain
    ∶ first-domain-quotient
first-genuine-downᴿ relation =
  paired-downᴿ (ordinaryᴿ relation)
    id-only↓
    (proj₁ (proj₂ first-source-down-result))
    (proj₂ (proj₂ first-source-down-result))
    id-only↓
    (proj₁ (proj₂ first-target-down-result))
    (proj₂ (proj₂ first-target-down-result))
    first-domain-quotient-square

------------------------------------------------------------------------
-- The finite spine succeeds
------------------------------------------------------------------------

two-genuine-downsᶜ :
  ∀ {W W′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ W ⊑ W′
    ⦂ glb-bad-A ⇒ glb-bad-A
    ⊑ glb-bad-A ⇒ glb-bad-A
    ∶ identity-A-function⊑identity-A-function →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ[ cast-spine ]
      (W ⟨ first-source-down ⟩) ⟨ second-source-down ⟩
      ⊑
      (W′ ⟨ first-target-down ⟩) ⟨ second-target-down ⟩
    ⦂ final-source-domain ⊑ᵖ final-target-domain
    ∶ identity-function-quotient
two-genuine-downsᶜ relation =
  paired-spinesᶜ relation
    (extend↓
      (single↓ id-only↓
        (proj₁ (proj₂ first-source-down-result))
        (proj₂ (proj₂ first-source-down-result)))
      id-only↓
      (proj₁ (proj₂ second-source-down-result))
      (proj₂ (proj₂ second-source-down-result))
      source-two-down-shapes)
    (extend↓
      (single↓ id-only↓
        (proj₁ (proj₂ first-target-down-result))
        (proj₂ (proj₂ first-target-down-result)))
      id-only↓
      (proj₁ (proj₂ second-target-down-result))
      (proj₂ (proj₂ second-target-down-result))
      target-two-down-shapes)
    identity-function-quotient-square

------------------------------------------------------------------------
-- One paired narrowing cannot consume the already-quotient prefix
------------------------------------------------------------------------

lower-permuted-types-not-ordinary :
  idᵢ zero IWF.∣ zero
    ⊢ glb-lower-XY ⊑ glb-lower-YX ⊣ zero →
  ⊥

one-not-below-zero :
  (suc zero ˣ⊑ˣ zero) ∈
    ((zero ˣ⊑ˣ zero) ∷ (suc zero ˣ⊑ˣ suc zero) ∷ []) →
  ⊥
one-not-below-zero (here ())
one-not-below-zero (there (here ()))
one-not-below-zero (there (there ()))

lower-permuted-types-not-ordinary
    (IWF.∀ⁱ
      (IWF.∀ⁱ
        (IWF.idˣ assumption _ _ IWF.↦ codomain))) =
  one-not-below-zero assumption
lower-permuted-types-not-ordinary
    (IWF.ν safe occurs (IWF.∀ⁱ ()))
lower-permuted-types-not-ordinary
    (IWF.ν safe occurs (IWF.ν safe′ occurs′ ()))

first-domains-not-ordinary :
  idᵢ zero IWF.∣ zero
    ⊢ first-source-domain ⊑ first-target-domain ⊣ zero →
  ⊥
first-domains-not-ordinary
    (domain IWF.↦ codomain) =
  lower-permuted-types-not-ordinary domain

two-genuine-downs-not-single :
  ∀ {W W′} →
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿᵖ
      (W ⟨ first-source-down ⟩) ⟨ second-source-down ⟩
      ⊑
      (W′ ⟨ first-target-down ⟩) ⟨ second-target-down ⟩
    ⦂ final-source-domain ⊑ᵖ final-target-domain
    ∶ identity-function-quotient →
  ⊥
two-genuine-downs-not-single
    (paired-downᴿ {p = p} relation
      source-mode source-down source-shape
      target-mode target-down target-shape square)
    with coercion-src-tgtᵐ (proj₁ source-down)
       | coercion-src-tgtᵐ
          (proj₁ (proj₁ (proj₂ second-source-down-result)))
       | coercion-src-tgtᵐ (proj₁ target-down)
       | coercion-src-tgtᵐ
          (proj₁ (proj₁ (proj₂ second-target-down-result)))
... | source-src , source-tgt
    | known-source-src , known-source-tgt
    | target-src , target-tgt
    | known-target-src , known-target-tgt
    with trans (sym source-src) known-source-src
       | trans (sym target-src) known-target-src
... | refl | refl =
  first-domains-not-ordinary p

------------------------------------------------------------------------
-- Unrelated same-polarity tops expose the adversarial prefix
------------------------------------------------------------------------

-- These reductions are individually valid. Their top terms are not related
-- by the live relation because the innermost lambdas would already require
-- ordinary imprecision between the permuted domains.

first-source-up-result =
  coerce-upʷ-shape-idᵢ 85 first-source-below-common

first-target-up-result =
  coerce-upʷ-shape-idᵢ 85 first-target-below-common

second-source-up-result =
  coerce-upʷ-shape-idᵢ 86 final-source-below-first

second-target-up-result =
  coerce-upʷ-shape-idᵢ 86 final-target-below-first

first-source-up : C.Coercion
first-source-up = proj₁ first-source-up-result

first-target-up : C.Coercion
first-target-up = proj₁ first-target-up-result

second-source-up : C.Coercion
second-source-up = proj₁ second-source-up-result

second-target-up : C.Coercion
second-target-up = proj₁ second-target-up-result

first-source-down-inert : C.Inert first-source-down
first-source-down-inert
    with proj₂ (proj₂ first-source-down-result)
... | CastShape.shape-fun {c = c} {d = d} domain codomain =
  c C.↦ d

first-target-down-inert : C.Inert first-target-down
first-target-down-inert
    with proj₂ (proj₂ first-target-down-result)
... | CastShape.shape-fun {c = c} {d = d} domain codomain =
  c C.↦ d

second-source-down-inert : C.Inert second-source-down
second-source-down-inert
    with proj₂ (proj₂ second-source-down-result)
... | CastShape.shape-fun {c = c} {d = d} domain codomain =
  c C.↦ d

second-target-down-inert : C.Inert second-target-down
second-target-down-inert
    with proj₂ (proj₂ second-target-down-result)
... | CastShape.shape-fun {c = c} {d = d} domain codomain =
  c C.↦ d

source-same-polarity-reduction :
  ∀ {W} →
  Value W →
  ((((ƛ (` zero))
      ⟨ second-source-down C.↦ second-source-up ⟩)
      ⟨ first-source-down C.↦ first-source-up ⟩) · W)
    —↠[ keep ∷ keep ∷ keep ∷ [] ]
  (((((W ⟨ first-source-down ⟩) ⟨ second-source-down ⟩)
      ⟨ second-source-up ⟩) ⟨ first-source-up ⟩))
source-same-polarity-reduction vW =
  two-function-casts-identity-reduction
    vW second-source-down-inert first-source-down-inert

target-same-polarity-reduction :
  ∀ {W′} →
  Value W′ →
  ((((ƛ (` zero))
      ⟨ second-target-down C.↦ second-target-up ⟩)
      ⟨ first-target-down C.↦ first-target-up ⟩) · W′)
    —↠[ keep ∷ keep ∷ keep ∷ [] ]
  (((((W′ ⟨ first-target-down ⟩) ⟨ second-target-down ⟩)
      ⟨ second-target-up ⟩) ⟨ first-target-up ⟩))
target-same-polarity-reduction vW′ =
  two-function-casts-identity-reduction
    vW′ second-target-down-inert first-target-down-inert
