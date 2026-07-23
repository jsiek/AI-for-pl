module BigStepProperties where

-- File Charter:
--   * States the adequacy boundary between structural big-step evaluation and
--     the existing store-changing small-step semantics.
--   * Packages soundness and completeness as proof obligations; it does not
--     assume them or add postulates.
--   * Intended as the first metatheory target before proving the big-step DGG
--     directly or transporting the existing small-step formulation.

open import BigStep
open import NuReduction using (_—↠[_]_)

record BigStepAdequacy : Set₁ where
  field
    sound :
      ∀ {M χs R} →
      M ⇓[ χs ] R →
      M —↠[ χs ] R

    complete :
      ∀ {M χs R} →
      M —↠[ χs ] R →
      Final R →
      M ⇓[ χs ] R
