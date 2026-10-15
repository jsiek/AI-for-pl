{-# OPTIONS --safe #-}

module proof.DGG.Catchup.MorePreciseSourceLambdaClosingProof where

-- File Charter:
--   * Proves source-only type-abstraction closing after target catch-up.
--   * Reconstructs the abstraction once target-only evolution has been
--     normalized out of the protected left type scope.
--   * Is parameterized only by that separate center-swap induction.

open import Data.Product using (_,_)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecisionTyping using (target-typing)
open import proof.DGG.Catchup.MorePreciseSourceLambdaClosingDef using
  (MorePreciseSourceLambdaClosingᵀ)
open import proof.DGG.Catchup.UnliftLeftTargetEvolutionDef using
  (UnliftLeftTargetEvolutionᵀ)
open import proof.DGG.WorldEvolutionSequence using (multi-⊑ᵀ)


module _
    (unlift-left-target-evolution : UnliftLeftTargetEvolutionᵀ)
  where

  more-precise-source-lambda-closing :
    MorePreciseSourceLambdaClosingᵀ
  more-precise-source-lambda-closing no-rebase nonvar occurs source-value
      evolution related q
      with unlift-left-target-evolution no-rebase evolution related
  more-precise-source-lambda-closing no-rebase nonvar occurs source-value
      evolution related q
    | γ′ , r , outer-evolution , body-related =
      γ′ , multi-⊑ᵀ outer-evolution q , outer-evolution ,
        CTI.Λ⊑² nonvar occurs source-value
          (target-typing body-related) body-related
          (multi-⊑ᵀ outer-evolution q)
