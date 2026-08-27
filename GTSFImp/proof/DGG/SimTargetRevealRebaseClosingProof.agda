{-# OPTIONS --safe #-}

module proof.DGG.SimTargetRevealRebaseClosingProof where

-- File Charter:
--   * Closes a target reveal after one source step beneath an open
--     source-rebase scope.
--   * Lifts the target-body trace through the reveal, transports the reveal
--     typing and outer result type, and rebuilds the balanced rebase CTI node.
--   * Builds a one-frame balanced stack and is parameterized only by the
--     genuine open source-rebase stack simulation induction.

open import Data.Product using (_,_)

open import CastTerms using (_↑_)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimSourceRebaseStackDef using
  (SimSourceRebaseStackᵀ)
open import proof.DGG.SourceRebaseStackDef using
  ( source-rebase-stack
  ; stack-root-evolution
  ; transport-source-rebase-stack-evolution
  )
open import proof.DGG.SimTargetRevealRebaseClosingDef using
  (SimTargetRevealRebaseClosingᵀ)
open import proof.DGG.WorldEvolutionSequence using
  (multi-⊑ᵀ; multi-target-reveal)
open import proof.Reduction using (applyReveals; reveal-↠)


module _ (sim-source-rebase-stack : SimSourceRebaseStackᵀ) where

  sim-target-reveal-rebase-closing : SimTargetRevealRebaseClosingᵀ
  sim-target-reveal-rebase-closing {M′ = M′} {c′ = c′}
      no-rebase c′⊢ rebase related q source-step
      with sim-source-rebase-stack
        {stack = source-rebase-stack no-rebase rebase}
        related source-step
  sim-target-reveal-rebase-closing {M′ = M′} {c′ = c′}
      no-rebase c′⊢ rebase related q source-step
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-body , γ′ , γᵖ′ , stack′ , r ,
      target-steps , stack-evolution , related′ =
      Δᴿ′ , Σᴿ′ , χsᴿ , target-body ↑ applyReveals χsᴿ c′ , γ′ ,
      multi-⊑ᵀ (stack-root-evolution stack-evolution) q ,
      reveal-↠ c′ target-steps ,
      stack-root-evolution stack-evolution ,
      CTI.⊑reveal-rebase²
        (multi-target-reveal (stack-root-evolution stack-evolution) c′⊢)
        (transport-source-rebase-stack-evolution rebase stack-evolution)
        related′
        (multi-⊑ᵀ (stack-root-evolution stack-evolution) q)
