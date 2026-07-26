module proof.Quotient.NuImprecisionCompositionalQuotientExamples where

-- File Charter:
--   * Stress-tests the compositional quotient prototype before it is used by
--     the dynamic gradual guarantee proof.
--   * Covers exact embedding, quotient-derived function and argument
--     positions, left- and right-nested applications, and two paired casts.
--   * Reuses the incomparable `∀`-permuted lower bounds from the bad-GLB
--     example for a concrete non-ordinary quotient witness.
--   * Contains examples only; it does not change the live term relation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)

import Coercions as C
open import CastImprecisionShape using
  (narrowing; widening; _⊢ᶜ_⦂_)
open import Coercions using (Coercion)
open import ForallPermutation using
  ( quotientᵖ
  ; ≈∀-refl
  ; ≈∀-⇒
  ; ⊑ᵖ-arrow-components
  )
open import Imprecision using (idᵢ)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _；_≋_
  ; _；⌊_⌋≋ᵖ_；_
  ; source-perm-refl
  ; source-perm-sym
  ; source-perm-↦
  ; source-swap-∀ν
  ; source-swap-ν∀
  ; quotient-boundary-square
  ; comp-id★
  ; comp-idˣ-idˣ
  ; comp-idˣ-tagˣ
  ; comp-↦-↦
  ; comp-∀-∀
  ; comp-∀-ν
  ; comp-tagˣ-id★
  ; comp-ν
  )
import ImprecisionWf as IWF
open import NuTerms using (blame; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( blame⊑ᵀ
  ; PairedCast
  ; QuotientWideningPair
  ; quotient-id-widening
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import PairedWideningCompatibility using
  ( compatible-source-inert
  ; compatible-target-inert-bridge
  )
open import TermTyping using (⊢blame)
open import Types
open import proof.Compilation.CompileCoercions using
  ( coerce-downⁿ-shape-idᵢ
  ; coerce-upʷ-shape-idᵢ
  )
open import proof.Core.Permutation.ForallPermutationTest using
  ( glb-lower-XY≈YX
  ; glb-lower-XY⊑XY
  ; glb-lower-YX⊑YX
  ; glb-lower-XY⊑ᵖYX
  ; glb-lower-YX⊑ᵖXY
  )
open import proof.EndpointMLB.Core.MLBGlbExample using
  ( glb-bad-A
  ; glb-bad-A⊑A
  ; glb-lower-XY
  ; glb-lower-XY⊑A
  ; glb-lower-XY⊑B
  ; glb-lower-YX
  ; glb-lower-YX⊑A
  ; glb-lower-YX⊑B
  ; glb-bad-B
  ; glb-bad-B⊑B
  )
open import proof.Quotient.NuImprecisionCompositionalQuotientDef

------------------------------------------------------------------------
-- Exact embedding and application closure
------------------------------------------------------------------------

blame-star⊑blame-star :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ blame ⊑ blame ⦂ ★ ⊑ ★ ∶ IWF.id★
blame-star⊑blame-star = blame⊑ᵀ (⊢blame wf★)


exact-embedding :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ[ cast-spine ] blame ⊑ blame
    ⦂ ★ ⊑ᵖ ★ ∶ quotientᵖ ≈∀-refl IWF.id★ ≈∀-refl
exact-embedding = ordinaryᶜ blame-star⊑blame-star


blame-function⊑blame-function :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ blame ⊑ blame
    ⦂ ★ ⇒ ★ ⊑ ★ ⇒ ★ ∶ IWF.id★ IWF.↦ IWF.id★
blame-function⊑blame-function =
  blame⊑ᵀ (⊢blame (wf⇒ wf★ wf★))


blame-curried⊑blame-curried :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ blame ⊑ blame
    ⦂ ★ ⇒ ★ ⇒ ★ ⊑ ★ ⇒ ★ ⇒ ★
    ∶ IWF.id★ IWF.↦ (IWF.id★ IWF.↦ IWF.id★)
blame-curried⊑blame-curried =
  blame⊑ᵀ (⊢blame (wf⇒ wf★ (wf⇒ wf★ wf★)))


left-nested-application :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ[ application ] (blame · blame) · blame
      ⊑ (blame · blame) · blame
    ⦂ ★ ⊑ᵖ ★ ∶ quotientᵖ ≈∀-refl IWF.id★ ≈∀-refl
left-nested-application =
  (ordinaryᶜ blame-curried⊑blame-curried
    ·ᶜ[ refl ] ordinaryᶜ blame-star⊑blame-star)
  ·ᶜ[ refl ] ordinaryᶜ blame-star⊑blame-star


right-nested-application :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ[ application ] blame · (blame · blame)
      ⊑ blame · (blame · blame)
    ⦂ ★ ⊑ᵖ ★ ∶ quotientᵖ ≈∀-refl IWF.id★ ≈∀-refl
right-nested-application =
  ordinaryᶜ blame-function⊑blame-function
  ·ᶜ[ refl ]
  (ordinaryᶜ blame-function⊑blame-function
    ·ᶜ[ refl ] ordinaryᶜ blame-star⊑blame-star)

------------------------------------------------------------------------
-- Closing an application-derived quotient term
------------------------------------------------------------------------

star⊑star :
  idᵢ zero IWF.∣ zero ⊢ ★ ⊑ ★ ⊣ zero
star⊑star = IWF.id★


up-star-result =
  coerce-upʷ-shape-idᵢ 80 star⊑star


up-star : Coercion
up-star = proj₁ up-star-result


star-quotient-square :
  ⌊ star⊑star ⌋ ；⌊ star⊑star ⌋≋ᵖ
    quotientᵖ ≈∀-refl star⊑star ≈∀-refl ； ⌊ star⊑star ⌋
star-quotient-square =
  quotient-boundary-square
    source-perm-refl comp-id★ source-perm-refl comp-id★


star-quotient-widening-compatible :
  QuotientWideningCompatible (idᵢ zero) zero zero
    up-star up-star
    (quotientᵖ ≈∀-refl star⊑star ≈∀-refl)
    star⊑star ⌊ star⊑star ⌋ ⌊ star⊑star ⌋
star-quotient-widening-compatible =
  exact-widening-compatible
    (compatible-target-inert-bridge λ ())


closed-right-nested-application :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ (blame · (blame · blame)) ⟨ up-star ⟩
      ⊑ (blame · (blame · blame)) ⟨ up-star ⟩
    ⦂ ★ ⊑ ★ ∶ star⊑star
closed-right-nested-application =
  closeᶜ right-nested-application
    (quotient-id-widening
      (proj₁ (proj₂ up-star-result))
      (proj₁ (proj₂ up-star-result)))
    (proj₂ (proj₂ up-star-result))
    (proj₂ (proj₂ up-star-result))
    star-quotient-square
    star-quotient-widening-compatible

------------------------------------------------------------------------
-- A concrete non-ordinary quotient and a two-cast narrowing spine
------------------------------------------------------------------------

example-label : Label
example-label = 81


down-D-result =
  coerce-downⁿ-shape-idᵢ example-label glb-lower-XY⊑A

down-E-result =
  coerce-downⁿ-shape-idᵢ example-label glb-lower-YX⊑A

identity-D-result =
  coerce-downⁿ-shape-idᵢ example-label glb-lower-XY⊑XY

identity-E-result =
  coerce-downⁿ-shape-idᵢ example-label glb-lower-YX⊑YX


down-D : Coercion
down-D = proj₁ down-D-result

down-E : Coercion
down-E = proj₁ down-E-result

identity-D : Coercion
identity-D = proj₁ identity-D-result

identity-E : Coercion
identity-E = proj₁ identity-E-result


blame-A⊑blame-A :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ blame ⊑ blame
    ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
blame-A⊑blame-A =
  blame⊑ᵀ (⊢blame (IWF.⊑-tgt-wf glb-bad-A⊑A))


single-D-spine :
  NarrowingSpine zero [] blame glb-bad-A
    (blame ⟨ down-D ⟩) glb-lower-XY ⌊ glb-lower-XY⊑A ⌋
single-D-spine =
  single↓ id-only↓ (proj₁ (proj₂ down-D-result))
    (proj₂ (proj₂ down-D-result))


single-E-spine :
  NarrowingSpine zero [] blame glb-bad-A
    (blame ⟨ down-E ⟩) glb-lower-YX ⌊ glb-lower-YX⊑A ⌋
single-E-spine =
  single↓ id-only↓ (proj₁ (proj₂ down-E-result))
    (proj₂ (proj₂ down-E-result))


identity-D-then-down-D :
  ⌊ glb-lower-XY⊑XY ⌋ ； ⌊ glb-lower-XY⊑A ⌋
    ≋ ⌊ glb-lower-XY⊑A ⌋
identity-D-then-down-D =
  comp-∀-∀
    (comp-∀-ν
      (comp-↦-↦ comp-idˣ-idˣ comp-idˣ-tagˣ))


identity-E-then-down-E :
  ⌊ glb-lower-YX⊑YX ⌋ ； ⌊ glb-lower-YX⊑A ⌋
    ≋ ⌊ glb-lower-YX⊑A ⌋
identity-E-then-down-E =
  comp-∀-ν
    (comp-∀-∀
      (comp-↦-↦ comp-idˣ-idˣ comp-idˣ-tagˣ))


double-D-spine :
  NarrowingSpine zero [] blame glb-bad-A
    ((blame ⟨ down-D ⟩) ⟨ identity-D ⟩)
    glb-lower-XY ⌊ glb-lower-XY⊑A ⌋
double-D-spine =
  extend↓ single-D-spine id-only↓
    (proj₁ (proj₂ identity-D-result))
    (proj₂ (proj₂ identity-D-result))
    identity-D-then-down-D


double-E-spine :
  NarrowingSpine zero [] blame glb-bad-A
    ((blame ⟨ down-E ⟩) ⟨ identity-E ⟩)
    glb-lower-YX ⌊ glb-lower-YX⊑A ⌋
double-E-spine =
  extend↓ single-E-spine id-only↓
    (proj₁ (proj₂ identity-E-result))
    (proj₂ (proj₂ identity-E-result))
    identity-E-then-down-E


double-D-length :
  narrowing-spine-length double-D-spine ≡ suc (suc zero)
double-D-length = refl


double-E-length :
  narrowing-spine-length double-E-spine ≡ suc (suc zero)
double-E-length = refl


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


single-route-quotient :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ[ cast-spine ] blame ⟨ down-D ⟩
      ⊑ blame ⟨ down-E ⟩
    ⦂ glb-lower-XY ⊑ᵖ glb-lower-YX
    ∶ glb-lower-XY⊑ᵖYX
single-route-quotient =
  paired-spinesᶜ blame-A⊑blame-A
    single-D-spine single-E-spine route-quotient-square


double-route-quotient :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ[ cast-spine ]
      ((blame ⟨ down-D ⟩) ⟨ identity-D ⟩)
      ⊑ ((blame ⟨ down-E ⟩) ⟨ identity-E ⟩)
    ⦂ glb-lower-XY ⊑ᵖ glb-lower-YX
    ∶ glb-lower-XY⊑ᵖYX
double-route-quotient =
  paired-spinesᶜ blame-A⊑blame-A
    double-D-spine double-E-spine route-quotient-square

------------------------------------------------------------------------
-- A quotient-related function consumes the two-cast quotient argument
------------------------------------------------------------------------

lower-function-D⊑A :
  idᵢ zero IWF.∣ zero ⊢ (glb-lower-XY ⇒ ★)
    ⊑ (glb-bad-A ⇒ ★) ⊣ zero
lower-function-D⊑A =
  IWF._↦_ glb-lower-XY⊑A IWF.id★


lower-function-E⊑A :
  idᵢ zero IWF.∣ zero ⊢ (glb-lower-YX ⇒ ★)
    ⊑ (glb-bad-A ⇒ ★) ⊣ zero
lower-function-E⊑A =
  IWF._↦_ glb-lower-YX⊑A IWF.id★


source-function⊑source-function :
  idᵢ zero IWF.∣ zero ⊢ (glb-bad-A ⇒ ★)
    ⊑ (glb-bad-A ⇒ ★) ⊣ zero
source-function⊑source-function =
  IWF._↦_ glb-bad-A⊑A IWF.id★


lower-function-D⊑D :
  idᵢ zero IWF.∣ zero ⊢ (glb-lower-XY ⇒ ★)
    ⊑ (glb-lower-XY ⇒ ★) ⊣ zero
lower-function-D⊑D =
  IWF._↦_ glb-lower-XY⊑XY IWF.id★


down-function-D-result =
  coerce-downⁿ-shape-idᵢ example-label
    lower-function-D⊑A

down-function-E-result =
  coerce-downⁿ-shape-idᵢ example-label
    lower-function-E⊑A


down-function-D : Coercion
down-function-D = proj₁ down-function-D-result

down-function-E : Coercion
down-function-E = proj₁ down-function-E-result


blame-A-function⊑blame-A-function :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ blame ⊑ blame
    ⦂ (glb-bad-A ⇒ ★) ⊑ (glb-bad-A ⇒ ★)
    ∶ source-function⊑source-function
blame-A-function⊑blame-A-function =
  blame⊑ᵀ
    (⊢blame
      (wf⇒ (IWF.⊑-tgt-wf glb-bad-A⊑A) wf★))


single-function-D-spine :
  NarrowingSpine zero [] blame (glb-bad-A ⇒ ★)
    (blame ⟨ down-function-D ⟩)
    (glb-lower-XY ⇒ ★)
    ⌊ lower-function-D⊑A ⌋
single-function-D-spine =
  single↓ id-only↓
    (proj₁ (proj₂ down-function-D-result))
    (proj₂ (proj₂ down-function-D-result))


single-function-E-spine :
  NarrowingSpine zero [] blame (glb-bad-A ⇒ ★)
    (blame ⟨ down-function-E ⟩)
    (glb-lower-YX ⇒ ★)
    ⌊ lower-function-E⊑A ⌋
single-function-E-spine =
  single↓ id-only↓
    (proj₁ (proj₂ down-function-E-result))
    (proj₂ (proj₂ down-function-E-result))


function-route-quotient-square :
  ⌊ lower-function-D⊑A ⌋
    ；⌊ source-function⊑source-function ⌋≋ᵖ
    quotientᵖ ≈∀-refl
      lower-function-D⊑D
      (≈∀-⇒ glb-lower-XY≈YX ≈∀-refl)
    ； ⌊ lower-function-E⊑A ⌋
function-route-quotient-square =
  quotient-boundary-square
    source-perm-refl
    (comp-↦-↦
      (comp-∀-∀
        (comp-ν
          (comp-↦-↦ comp-idˣ-idˣ comp-tagˣ-id★)))
      comp-id★)
    (source-perm-↦ source-swap-∀ν source-perm-refl)
    (comp-↦-↦
      (comp-∀-∀
        (comp-∀-ν
          (comp-↦-↦ comp-idˣ-idˣ comp-idˣ-tagˣ)))
      comp-id★)


function-route-quotient :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ[ cast-spine ] blame ⟨ down-function-D ⟩
      ⊑ blame ⟨ down-function-E ⟩
    ⦂ (glb-lower-XY ⇒ ★) ⊑ᵖ (glb-lower-YX ⇒ ★)
    ∶ quotientᵖ ≈∀-refl
        lower-function-D⊑D
        (≈∀-⇒ glb-lower-XY≈YX ≈∀-refl)
function-route-quotient =
  paired-spinesᶜ blame-A-function⊑blame-A-function
    single-function-D-spine single-function-E-spine
    function-route-quotient-square


quotient-function-and-two-cast-argument :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ[ application ]
      (blame ⟨ down-function-D ⟩)
        · ((blame ⟨ down-D ⟩) ⟨ identity-D ⟩)
      ⊑
      (blame ⟨ down-function-E ⟩)
        · ((blame ⟨ down-E ⟩) ⟨ identity-E ⟩)
    ⦂ ★ ⊑ᵖ ★ ∶ quotientᵖ ≈∀-refl IWF.id★ ≈∀-refl
quotient-function-and-two-cast-argument =
  function-route-quotient ·ᶜ[ refl ] double-route-quotient

------------------------------------------------------------------------
-- Closing a genuinely permuted quotient through its representatives
------------------------------------------------------------------------

reverse-route-quotient-square :
  ⌊ glb-lower-YX⊑A ⌋ ；⌊ glb-bad-A⊑A ⌋≋ᵖ
    glb-lower-YX⊑ᵖXY ； ⌊ glb-lower-XY⊑A ⌋
reverse-route-quotient-square =
  quotient-boundary-square
    source-perm-refl
    (comp-ν
      (comp-∀-∀
        (comp-↦-↦ comp-idˣ-idˣ comp-tagˣ-id★)))
    (source-perm-sym source-swap-∀ν)
    (comp-∀-ν
      (comp-∀-∀
        (comp-↦-↦ comp-idˣ-idˣ comp-idˣ-tagˣ)))


single-reverse-route-quotient :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ[ cast-spine ] blame ⟨ down-E ⟩
      ⊑ blame ⟨ down-D ⟩
    ⦂ glb-lower-YX ⊑ᵖ glb-lower-XY
    ∶ glb-lower-YX⊑ᵖXY
single-reverse-route-quotient =
  paired-spinesᶜ blame-A⊑blame-A
    single-E-spine single-D-spine reverse-route-quotient-square


up-E-result =
  coerce-upʷ-shape-idᵢ example-label glb-lower-YX⊑B

up-D-result =
  coerce-upʷ-shape-idᵢ example-label glb-lower-XY⊑B


up-E : Coercion
up-E = proj₁ up-E-result

up-D : Coercion
up-D = proj₁ up-D-result


up-E-inert : C.Inert up-E
up-E-inert = C.`∀ _


reverse-route-closing-square :
  ⌊ glb-lower-YX⊑B ⌋ ；⌊ glb-bad-B⊑B ⌋≋ᵖ
    glb-lower-YX⊑ᵖXY ； ⌊ glb-lower-XY⊑B ⌋
reverse-route-closing-square =
  quotient-boundary-square
    source-perm-refl
    (comp-∀-∀
      (comp-ν
        (comp-↦-↦ comp-tagˣ-id★ comp-idˣ-idˣ)))
    (source-perm-sym source-swap-ν∀)
    (comp-∀-∀
      (comp-∀-ν
        (comp-↦-↦ comp-idˣ-tagˣ comp-idˣ-idˣ)))


reverse-route-widening-compatible :
  QuotientWideningCompatible (idᵢ zero) zero zero
    up-E up-D glb-lower-YX⊑ᵖXY glb-bad-B⊑B
    ⌊ glb-lower-YX⊑B ⌋ ⌊ glb-lower-XY⊑B ⌋
reverse-route-widening-compatible =
  compatible-through-representatives
    source-perm-refl
    (source-perm-sym source-swap-ν∀)
    (compatible-source-inert up-E-inert)


closed-reverse-route-quotient :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺᶜ (blame ⟨ down-E ⟩) ⟨ up-E ⟩
      ⊑ (blame ⟨ down-D ⟩) ⟨ up-D ⟩
    ⦂ glb-bad-B ⊑ glb-bad-B ∶ glb-bad-B⊑B
closed-reverse-route-quotient =
  closeᶜ single-reverse-route-quotient
    (quotient-id-widening
      (proj₁ (proj₂ up-E-result))
      (proj₁ (proj₂ up-D-result)))
    (proj₂ (proj₂ up-E-result))
    (proj₂ (proj₂ up-D-result))
    reverse-route-closing-square
    reverse-route-widening-compatible

------------------------------------------------------------------------
-- The residual after two successive function-cast reductions
------------------------------------------------------------------------

two-function-cast-residual :
  ∀ {Φ Δᴸ Δᴿ ρ γ L L′ M M′
      C C′ B B′ E E′ F F′
      pE pF qF qC qB f g
      d₂ d₂′ d₁ d₁′ u₁ u₁′ u₂ u₂′ s s′} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺᶜ[ f ] L ⊑ L′
    ⦂ (C ⇒ B) ⊑ᵖ (C′ ⇒ B′) ∶ qF →
  ⊑ᵖ-arrow-components qF ≡ (qC , qB) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺᶜ[ g ] ((M ⟨ d₂ ⟩) ⟨ d₁ ⟩)
      ⊑ ((M′ ⟨ d₂′ ⟩) ⟨ d₁′ ⟩)
    ⦂ C ⊑ᵖ C′ ∶ qC →
  QuotientWideningPair Δᴸ Δᴿ ρ u₁ u₁′ B B′ E E′ →
  widening ⊢ᶜ u₁ ⦂ s →
  widening ⊢ᶜ u₁′ ⦂ s′ →
  s ；⌊ pE ⌋≋ᵖ qB ； s′ →
  QuotientWideningCompatible Φ Δᴸ Δᴿ
    u₁ u₁′ qB pE s s′ →
  PairedCast Φ Δᴸ Δᴿ ρ u₂ u₂′ pE pF →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺᶜ
      (((L · ((M ⟨ d₂ ⟩) ⟨ d₁ ⟩)) ⟨ u₁ ⟩) ⟨ u₂ ⟩)
      ⊑
      ((L′ · ((M′ ⟨ d₂′ ⟩) ⟨ d₁′ ⟩)) ⟨ u₁′ ⟩)
        ⟨ u₂′ ⟩
    ⦂ F ⊑ F′ ∶ pF
two-function-cast-residual
    function components argument widening-pair
    source-shape target-shape square compatible outer-cast =
  paired-castᶜ outer-cast
    (closeᶜ
      (function ·ᶜ[ components ] argument)
      widening-pair source-shape target-shape square compatible)
