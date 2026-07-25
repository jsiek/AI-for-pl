module
  proof.Core.Properties.ImprecisionCompositionUniversalInversion
  where

-- File Charter:
--   * Inverts hereditary imprecision composition at a target-only universal
--     instantiation boundary.
--   * Recovers the exact body composition when paired universal imprecision
--     is followed by source-only universal imprecision.
--   * Proves that composing any incoming shape with a source-only `ν` shape
--     cannot produce a paired `∀` shape.
--   * Contains no cast typing, term relation, store invariant, or simulation.

open import Data.Empty using (⊥)

open import ImprecisionComposition using
  ( ImprecisionShape
  ; ∀ˢ_
  ; νˢ_
  ; comp-∀-ν
  ; _；_≋_
  )


compose-right-ν-cannot-result-∀ :
  ∀ {p q r : ImprecisionShape} →
  p ； νˢ q ≋ ∀ˢ r →
  ⊥
compose-right-ν-cannot-result-∀ ()


compose-∀-ν-body :
  ∀ {p q r : ImprecisionShape} →
  ∀ˢ p ； νˢ q ≋ νˢ r →
  p ； q ≋ r
compose-∀-ν-body (comp-∀-ν composition) = composition
