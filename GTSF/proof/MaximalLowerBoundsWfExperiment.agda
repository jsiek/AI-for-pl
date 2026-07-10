module proof.MaximalLowerBoundsWfExperiment where

-- WARNING:
--   This is an obsolete experiment, not the current MLB coherence plan.
--   The route-coherence postulate below is refuted by
--   `proof.MLBGlbCounterexample.bad-selector-coherence-counterexampleᵢ`
--   when paired with route completeness for arbitrary lower-bound evidence.
--   Keep this file only as a record of the failed evidence-directed proof
--   shape.  New work should use the endpoint-canonical algorithm described
--   in `GTSF/proof/EndpointCanonicalMLBDesign.md`.

-- File Charter:
--   * Historical postulate-fit experiment for a now-rejected indexed MLB
--     coherence theorem shape.
--   * Keeps speculative assumptions out of `MaximalLowerBoundsWf.agda`.
--   * Shows that route completeness plus route coherence would compose to the
--     cast-facing theorem, but those assumptions are too broad.

open import Data.Product using (proj₁)

open import Imprecision using (idᵢ)
open import ImprecisionWf
open import proof.MaximalLowerBoundsWf

------------------------------------------------------------------------
-- Obsolete experimental assumptions
------------------------------------------------------------------------

-- Missing piece 1: complete construction of canonical selector routes for
-- identity-context lower-bound evidence.  This packages the remaining
-- polymorphic support internalization and mixed package assembly work.
-- This assumption is not the current target because arbitrary lower-bound
-- evidence is not endpoint-canonical.

postulate
  mlb-type-from-lower-selector-route-assumptionᵢ :
    ∀ {Δ C A B} →
    (p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ) →
    (q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ) →
    MlbTypeSelectorᵢ
      {Γ = choice-idᵢ Δ}
      (leftChoice-id-proofᵢ p)
      (rightChoice-id-proofᵢ q)

-- Missing piece 2: coherence for canonical selector routes constructed from
-- related endpoint pairs.  This is still selector-specific: it does not assert
-- that arbitrary maximal lower bounds are coherent.
-- This postulate is false when used with the route-completeness postulate
-- above.  The flipped `forall` counterexample gives two route-complete
-- selected lowers that are incomparable.

postulate
  mlb-type-from-lower-selector-coherence-assumptionᵢ :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {p : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ}
      {q : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ}
      {p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
      {q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
    (route :
      MlbTypeSelectorᵢ
        {Γ = choice-idᵢ Δᴸ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)) →
    (route′ :
      MlbTypeSelectorᵢ
        {Γ = choice-idᵢ Δᴿ}
        (leftChoice-id-proofᵢ p′)
        (rightChoice-id-proofᵢ q′)) →
    MlbTypeSelectorCoherenceᵢ Φ route route′

------------------------------------------------------------------------
-- Historical experiment result
------------------------------------------------------------------------

-- This theorem is kept only to document how the obsolete assumptions composed
-- to the cast-facing statement.  Do not use it as the current proof target.

mlb-type-from-lower-maximal-coherence-experimentᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (p : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ) →
  (q : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ) →
  (p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ) →
  (q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ) →
  MaximalLowerBoundCoherenceᵢ
    (proj₁
      (choice-id-maximal-selectorᵢ
        (mlb-type-from-lower-selector-route-assumptionᵢ p q)))
    (proj₁
      (choice-id-maximal-selectorᵢ
        (mlb-type-from-lower-selector-route-assumptionᵢ p′ q′)))
    pA
    pB
mlb-type-from-lower-maximal-coherence-experimentᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} p q p′ q′ =
  choice-id-maximal-selector-coherenceᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = A}
    {A′ = A′}
    {B = B}
    {B′ = B′}
    {C = C}
    {C′ = C′}
    {pA = pA}
    {pB = pB}
    {p = p}
    {q = q}
    {p′ = p′}
    {q′ = q′}
    (mlb-type-from-lower-selector-route-assumptionᵢ p q)
    (mlb-type-from-lower-selector-route-assumptionᵢ p′ q′)
    (mlb-type-from-lower-selector-coherence-assumptionᵢ
      {Φ = Φ}
      {Δᴸ = Δᴸ}
      {Δᴿ = Δᴿ}
      {A = A}
      {A′ = A′}
      {B = B}
      {B′ = B′}
      {C = C}
      {C′ = C′}
      {pA = pA}
      {pB = pB}
      {p = p}
      {q = q}
      {p′ = p′}
      {q′ = q′}
      (mlb-type-from-lower-selector-route-assumptionᵢ p q)
      (mlb-type-from-lower-selector-route-assumptionᵢ p′ q′))
