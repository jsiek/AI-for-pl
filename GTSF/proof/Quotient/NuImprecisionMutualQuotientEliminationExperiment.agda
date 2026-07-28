module
  proof.Quotient.NuImprecisionMutualQuotientEliminationExperiment
  where

-- File Charter:
--   * Tests a mutually recursive quotient narrowing/elimination and
--     widening-compatibility invariant without changing the live relations.
--   * Forces function widening to expose contravariant narrowing elimination
--     and covariant widening compatibility recursively.
--   * Permits the old reduction-closed widening compatibility only when at
--     least one paired coercion is syntactically non-function.
--   * Checks the existing two-function-cast fixture and one higher-order
--     fixture whose outer function domain needs narrowing evidence.

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
  (ReductionClosedQuotientWideningCompatible)
open import Types using
  (Ty; TyCtx; _⇒_)
open import
  proof.Quotient.NuImprecisionQuotientNarrowingEliminationCompatibility
  using
  ( NonPairedFunctionCoercions
  ; source-non-function
  ; non-function-universal
  )
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
  ; route-widening-compatible
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


mutual
  data ExperimentalQuotientNarrowingElimination
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
      (d d′ : Coercion) → {A A′ D D′ : Ty} →
      (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
      (q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
      (d-shape d′-shape : ImprecisionShape) → Set where

    narrowing-non-function :
      ∀ {d d′ A A′ D D′ p q d-shape d′-shape} →
      NonPairedFunctionCoercions d d′ →
      ExperimentalQuotientNarrowingElimination
        Φ Δᴸ Δᴿ d d′
        {A} {A′} {D} {D′} p q d-shape d′-shape

    narrowing-function :
      ∀ {a b a′ b′ A₁ A₁′ A₂ A₂′ D₁ D₁′ D₂ D₂′
        p₁ p₂ q₁ q₂ qF
        a-shape b-shape a′-shape b′-shape} →
      ⊑ᵖ-arrow-components qF ≡ (q₁ , q₂) →
      ExperimentalQuotientWideningCompatibility
        Φ Δᴸ Δᴿ a a′ q₁ p₁ a-shape a′-shape →
      ExperimentalQuotientNarrowingElimination
        Φ Δᴸ Δᴿ b b′ p₂ q₂ b-shape b′-shape →
      ExperimentalQuotientNarrowingElimination
        Φ Δᴸ Δᴿ
        (a C.↦ b) (a′ C.↦ b′)
        {A₁ ⇒ A₂} {A₁′ ⇒ A₂′}
        {D₁ ⇒ D₂} {D₁′ ⇒ D₂′}
        (p₁ ↦ p₂) qF
        (a-shape ↦ˢ b-shape) (a′-shape ↦ˢ b′-shape)

  data ExperimentalQuotientWideningCompatibility
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
      (u u′ : Coercion) → {D D′ A A′ : Ty} →
      (q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
      (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
      (u-shape u′-shape : ImprecisionShape) → Set where

    widening-non-function :
      ∀ {u u′ D D′ A A′ q p u-shape u′-shape} →
      NonPairedFunctionCoercions u u′ →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ u u′
        {D} {D′} {A} {A′} q p u-shape u′-shape →
      ExperimentalQuotientWideningCompatibility
        Φ Δᴸ Δᴿ u u′ q p u-shape u′-shape

    widening-function :
      ∀ {d u d′ u′ D₁ D₁′ D₂ D₂′ A₁ A₁′ A₂ A₂′
        q₁ q₂ p₁ p₂ qF
        d-shape u-shape d′-shape u′-shape} →
      ⊑ᵖ-arrow-components qF ≡ (q₁ , q₂) →
      ExperimentalQuotientNarrowingElimination
        Φ Δᴸ Δᴿ d d′ p₁ q₁ d-shape d′-shape →
      ExperimentalQuotientWideningCompatibility
        Φ Δᴸ Δᴿ u u′ q₂ p₂ u-shape u′-shape →
      ExperimentalQuotientWideningCompatibility
        Φ Δᴸ Δᴿ
        (d C.↦ u) (d′ C.↦ u′)
        {D₁ ⇒ D₂} {D₁′ ⇒ D₂′}
        {A₁ ⇒ A₂} {A₁′ ⇒ A₂′}
        qF (p₁ ↦ p₂)
        (d-shape ↦ˢ u-shape) (d′-shape ↦ˢ u′-shape)


------------------------------------------------------------------------
-- Existing first-order two-function-cast fixture
------------------------------------------------------------------------

route-widening-mutual :
  ExperimentalQuotientWideningCompatibility (idᵢ zero) zero zero
    up-D up-E
    glb-lower-XY⊑ᵖYX
    glb-bad-A⊑A
    ⌊ glb-lower-XY⊑A ⌋ ⌊ glb-lower-YX⊑A ⌋
route-widening-mutual =
  widening-non-function
    (source-non-function non-function-universal)
    route-widening-compatible

route-narrowing-mutual :
  ExperimentalQuotientNarrowingElimination (idᵢ zero) zero zero
    down-D down-E glb-bad-A⊑A
    glb-lower-XY⊑ᵖYX
    ⌊ glb-lower-XY⊑A ⌋ ⌊ glb-lower-YX⊑A ⌋
route-narrowing-mutual =
  narrowing-non-function
    (source-non-function non-function-universal)

inner-function-elimination-mutual :
  ExperimentalQuotientNarrowingElimination (idᵢ zero) zero zero
    inner-D inner-E
    identity-A-function⊑identity-A-function
    identity-function-quotient
    (⌊ glb-lower-XY⊑A ⌋ ↦ˢ ⌊ glb-lower-XY⊑A ⌋)
    (⌊ glb-lower-YX⊑A ⌋ ↦ˢ ⌊ glb-lower-YX⊑A ⌋)
inner-function-elimination-mutual =
  narrowing-function
    refl
    route-widening-mutual
    route-narrowing-mutual

outer-function-widening-mutual :
  ExperimentalQuotientWideningCompatibility (idᵢ zero) zero zero
    outer-D outer-E identity-function-quotient
    identity-A-function⊑identity-A-function
    (⌊ glb-lower-XY⊑A ⌋ ↦ˢ ⌊ glb-lower-XY⊑A ⌋)
    (⌊ glb-lower-YX⊑A ⌋ ↦ˢ ⌊ glb-lower-YX⊑A ⌋)
outer-function-widening-mutual =
  widening-function
    refl
    route-narrowing-mutual
    route-widening-mutual


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
  ExperimentalQuotientWideningCompatibility (idᵢ zero) zero zero
    higher-D higher-E higher-quotient higher-ordinary
    ((⌊ glb-lower-XY⊑A ⌋ ↦ˢ ⌊ glb-lower-XY⊑A ⌋) ↦ˢ
      (⌊ glb-lower-XY⊑A ⌋ ↦ˢ ⌊ glb-lower-XY⊑A ⌋))
    ((⌊ glb-lower-YX⊑A ⌋ ↦ˢ ⌊ glb-lower-YX⊑A ⌋) ↦ˢ
      (⌊ glb-lower-YX⊑A ⌋ ↦ˢ ⌊ glb-lower-YX⊑A ⌋))
higher-function-domain-widening-mutual =
  widening-function
    refl
    inner-function-elimination-mutual
    outer-function-widening-mutual
