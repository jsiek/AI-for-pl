module proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleQuotient where

-- File Charter:
--   * Proves cross-context monotonicity of the simple endpoint MLB after
--     quotienting adjacent `∀` permutations.
--   * Factors source lower bounds through target raw-enumeration routes.
--   * Retains both exact endpoint quotient-boundary shape squares.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst)

open import Types
open import ForallPermutation using
  ( _∣_⊢_⊑ᵖ_⊣_
  ; ≈∀-refl
  ; quotientᵖ
  )
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _；_≋_
  ; _；⌊_⌋≋ᵖ_；_
  ; quotient-boundary-square
  ; source-perm-refl
  )
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using
  (MLB; fuelFor)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePermutation using
  ( aligned-routes-≈∀
  ; generated-routes-aligned
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleFactorization using
  ( indexed-factor-root
  ; route-factor-worker
  )
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleFactorizationShape
  using
  ( aligned-routes-left-leg-shape
  ; aligned-routes-right-leg-shape
  ; pair-lower-left-shape
  ; pair-lower-right-shape
  ; route-factor-worker-shapes
  )
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePairedSpan
  using
  ( pair-lower
  ; paired-lower-left
  ; paired-lower-right
  )
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleCompleteness
  using (sourceFuelFor)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleRoutes using
  ( MLB-result-route-sound
  ; MLB-result→route
  ; enum-route-sound
  )
open import proof.Core.Properties.ImprecisionCompositionProperties using
  (shape-trans-left-idᵢ)
open import proof.Core.Properties.ImprecisionProperties using
  (WfImpCtx-to²; idᵢ-wf)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-trans-left-idᵢ)

MLB-monotoneᵖ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′} →
  (A⊑A′ : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (B⊑B′ : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (C-selected : MLB Δᴸ A B ≡ just C) →
  (C′-selected : MLB Δᴿ A′ B′ ≡ just C′) →
  let C-lower = MLB-result-route-sound C-selected
      C′-lower = MLB-result-route-sound C′-selected
  in
  Σ[ q ∈ Φ ∣ Δᴸ ⊢ C ⊑ᵖ C′ ⊣ Δᴿ ]
    (⌊ proj₁ C-lower ⌋ ；⌊ A⊑A′ ⌋≋ᵖ q ；
      ⌊ proj₁ C′-lower ⌋) ×
    (⌊ proj₂ C-lower ⌋ ；⌊ B⊑B′ ⌋≋ᵖ q ；
      ⌊ proj₂ C′-lower ⌋)
MLB-monotoneᵖ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′}
    A⊑A′ B⊑B′ C-selected C′-selected
    with
      route-factor-worker (fuelFor A′ B′) _ sourceFuelFor
        indexed-factor-root
        (pair-lower
          (⊑-trans-left-idᵢ
            (proj₁ (MLB-result-route-sound
              {Δ = Δᴸ} {A = A} {B = B} {C = C} C-selected))
            A⊑A′)
          (⊑-trans-left-idᵢ
            (proj₂ (MLB-result-route-sound
              {Δ = Δᴸ} {A = A} {B = B} {C = C} C-selected))
            B⊑B′))
        (MLB-result→route
          {Δ = Δᴿ} {A = A′} {B = B′} {C = C′} C′-selected)
       | route-factor-worker-shapes
           (fuelFor A′ B′) _ sourceFuelFor
           indexed-factor-root
           (pair-lower
             (⊑-trans-left-idᵢ
               (proj₁ (MLB-result-route-sound
                 {Δ = Δᴸ} {A = A} {B = B} {C = C} C-selected))
               A⊑A′)
             (⊑-trans-left-idᵢ
               (proj₂ (MLB-result-route-sound
                 {Δ = Δᴸ} {A = A} {B = B} {C = C} C-selected))
               B⊑B′))
           (MLB-result→route
             {Δ = Δᴿ} {A = A′} {B = B′} {C = C′} C′-selected)
MLB-monotoneᵖ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′}
    A⊑A′ B⊑B′ C-selected C′-selected
    | D , generated-route , factor
    | factor-left , factor-right =
  quotientᵖ ≈∀-refl factor (aligned-routes-≈∀ aligned) ,
  quotient-boundary-square
    source-perm-refl source-left-composition
    (aligned-routes-left-leg-shape target-wf target-wf aligned)
    factor-left′ ,
  quotient-boundary-square
    source-perm-refl source-right-composition
    (aligned-routes-right-leg-shape target-wf target-wf aligned)
    factor-right′
  where
    source-lower =
      MLB-result-route-sound
        {Δ = Δᴸ} {A = A} {B = B} C-selected

    source-left =
      ⊑-trans-left-idᵢ (proj₁ source-lower) A⊑A′

    source-right =
      ⊑-trans-left-idᵢ (proj₂ source-lower) B⊑B′

    target-wf = WfImpCtx-to² (idᵢ-wf Δᴿ)

    aligned =
      generated-routes-aligned
        {modes = []} {Δ = Δᴿ} generated-route
        (MLB-result→route
          {Δ = Δᴿ} {A = A′} {B = B′} {C = C′} C′-selected)

    source-left-composition =
      shape-trans-left-idᵢ (proj₁ source-lower) A⊑A′

    source-right-composition =
      shape-trans-left-idᵢ (proj₂ source-lower) B⊑B′

    generated-lower =
      enum-route-sound target-wf target-wf generated-route

    factor-left′ =
      subst
        (λ s →
          ⌊ factor ⌋ ； ⌊ proj₁ generated-lower ⌋ ≋ s)
        (pair-lower-left-shape source-left source-right)
        factor-left

    factor-right′ =
      subst
        (λ s →
          ⌊ factor ⌋ ； ⌊ proj₂ generated-lower ⌋ ≋ s)
        (pair-lower-right-shape source-left source-right)
        factor-right
