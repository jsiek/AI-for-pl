module proof.EndpointCanonicalMLBSimpleQuotient where

-- File Charter:
--   * Proves cross-context monotonicity of the simple endpoint MLB after
--     quotienting adjacent `∀` permutations.
--   * Factors source lower bounds through target raw-enumeration routes.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)

open import Types
open import ForallPermutation using
  (_∣_⊢_⊑ᵖ_⊣_; ≈∀-refl; quotientᵖ)
open import Imprecision using (idᵢ)
open import ImprecisionWf as IWF using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import proof.EndpointCanonicalMLBSimple using
  (MLB; rawEndpointMlbsAt)
open import proof.EndpointCanonicalMLBSimpleCompleteness using
  (rawEndpointMlbsAt-complete)
open import proof.EndpointCanonicalMLBSimplePermutation using
  (rawEndpointMlbsAt-≈∀)
open import proof.EndpointCanonicalMLBSimpleFactorization using
  (rawEndpointMlbsAt-factor)
open import proof.EndpointCanonicalMLBSimpleRoutes using
  (MLB-result→route; raw-endpoint-route→membership)
open import proof.EndpointCanonicalMLBSimpleSoundness using (MLB-sound)
open import proof.MaximalLowerBoundsWf using
  (⊑-trans-idᵢ; ⊑-trans-left-idᵢ)

MLB-monotoneᵖ-from-factor :
  (∀ {Φ Δᴸ Δᴿ A B C C′} →
    Φ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴿ →
    C′ ∈ rawEndpointMlbsAt Δᴿ A B →
    ∃[ D ]
      (D ∈ rawEndpointMlbsAt Δᴿ A B ×
       Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ)) →
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′} →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  MLB Δᴸ A B ≡ just C →
  MLB Δᴿ A′ B′ ≡ just C′ →
  Φ ∣ Δᴸ ⊢ C ⊑ᵖ C′ ⊣ Δᴿ
MLB-monotoneᵖ-from-factor factor
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    A⊑A′ B⊑B′ C-selected C′-selected =
  quotientᵖ ≈∀-refl C⊑D D≈C′
  where
    C-lower =
      MLB-sound {Δ = Δᴸ} {A = A} {B = B} C-selected

    C⊑A′ = ⊑-trans-left-idᵢ (proj₁ C-lower) A⊑A′
    C⊑B′ = ⊑-trans-left-idᵢ (proj₂ C-lower) B⊑B′

    C′∈raw =
      raw-endpoint-route→membership
        {Δ = Δᴿ} {A = A′} {B = B′}
        (MLB-result→route
          {Δ = Δᴿ} {A = A′} {B = B′} C′-selected)

    factored =
      factor
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {A = A′} {B = B′} {C = C} {C′ = C′}
        C⊑A′ C⊑B′ C′∈raw

    D = proj₁ factored
    D∈raw = proj₁ (proj₂ factored)
    C⊑D = proj₂ (proj₂ factored)

    D≈C′ =
      rawEndpointMlbsAt-≈∀
        {Δ = Δᴿ} {A = A′} {B = B′} D∈raw C′∈raw

MLB-monotoneᵖ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′} →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  MLB Δᴸ A B ≡ just C →
  MLB Δᴿ A′ B′ ≡ just C′ →
  Φ ∣ Δᴸ ⊢ C ⊑ᵖ C′ ⊣ Δᴿ
MLB-monotoneᵖ =
  MLB-monotoneᵖ-from-factor rawEndpointMlbsAt-factor

MLB-monotone-idᵖ :
  ∀ {Δ A A′ B B′ C C′} →
  idᵢ Δ ∣ Δ ⊢ A ⊑ A′ ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ B ⊑ B′ ⊣ Δ →
  MLB Δ A B ≡ just C →
  MLB Δ A′ B′ ≡ just C′ →
  idᵢ Δ ∣ Δ ⊢ C ⊑ᵖ C′ ⊣ Δ
MLB-monotone-idᵖ
    {Δ = Δ} {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′} A⊑A′ B⊑B′ C-selected C′-selected =
  quotientᵖ ≈∀-refl C⊑D D≈C′
  where
    C-lower = MLB-sound {Δ = Δ} {A = A} {B = B} C-selected

    C⊑A′ = ⊑-trans-idᵢ (proj₁ C-lower) A⊑A′
    C⊑B′ = ⊑-trans-idᵢ (proj₂ C-lower) B⊑B′

    factored =
      rawEndpointMlbsAt-complete
        {Δ = Δ} {A = A′} {B = B′} {D = C}
        (IWF.⊑-tgt-wf C⊑A′) (IWF.⊑-tgt-wf C⊑B′)
        (C⊑A′ , C⊑B′)

    D = proj₁ factored
    D∈raw = proj₁ (proj₂ factored)
    C⊑D = proj₂ (proj₂ factored)

    C′∈raw =
      raw-endpoint-route→membership
        {Δ = Δ} {A = A′} {B = B′}
        (MLB-result→route
          {Δ = Δ} {A = A′} {B = B′} C′-selected)

    D≈C′ =
      rawEndpointMlbsAt-≈∀
        {Δ = Δ} {A = A′} {B = B′} D∈raw C′∈raw

-- The fixed-endpoint half is discharged by `rawEndpointMlbsAt-≈∀`.
-- General `Φ` uses route-guided factorization because an arbitrary
-- imprecision context need not be functional.  The factor proof retains the
-- source-only `∀` alternative even when the target also starts in `∀`;
-- eagerly pairing those binders makes the recursive certificate incomplete.
