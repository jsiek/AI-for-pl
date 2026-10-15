{-# OPTIONS --safe #-}

module proof.DGG.SimPairedCastValuesProof where

-- File Charter:
--   * Proves paired ordinary-cast value simulation by factoring the source
--     cast step through source-only cast simulation.
--   * Uses the related-value consistency-square diagonal to expose the
--     source-only cast judgment, then reattaches the unchanged target cast.
--   * Is parameterized only by those two genuine lower semantic inductions;
--     it contains no reduction classifier or residual-family interface.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_)

open import CastTerms using (_⟨_⟩)
open import Reduction
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.RelatedValueCastSquareDef using
  (RelatedValueCastSquareᵀ)
open import proof.DGG.SimPairedCastValuesDef using
  (SimPairedCastValuesᵀ)
open import proof.DGG.SimSourceCastValuesDef using
  (SimSourceCastValuesᵀ)
open import proof.DGG.WorldEvolutionSequence using
  (multi-⊑ᵀ)
open import proof.Reduction.ValueIrreducibleProof using
  (value-no-step)


module _
    (related-value-cast-square : RelatedValueCastSquareᵀ)
    (sim-source-cast-values : SimSourceCastValuesᵀ)
  where

  private
    close-root : SimPairedCastValuesᵀ
    close-root {V′ = V′} {c = c} {c′ = c′}
        no-rebase related q source-value target-value source-step
        with related-value-cast-square {c = c} {c′ = c′}
          related source-value target-value q
    close-root {V′ = V′} {c′ = c′}
        no-rebase related q source-value target-value source-step
      | diagonal
        with sim-source-cast-values
          no-rebase related diagonal source-value target-value source-step
    close-root {V′ = V′} {c′ = c′}
        no-rebase related q source-value target-value source-step
      | diagonal
      | γ′ , r , evolution , final =
        _ , _ , [] , V′ ⟨ c′ ⟩ , γ′ , multi-⊑ᵀ evolution q ,
        (V′ ⟨ c′ ⟩ ∎[]) , evolution ,
        CTI.⊑cast² c′ final (multi-⊑ᵀ evolution q)

  sim-paired-cast-values : SimPairedCastValuesᵀ
  sim-paired-cast-values no-rebase related q source-value target-value
      root@(pure-step (β-id value)) =
    close-root no-rebase related q source-value target-value root

  sim-paired-cast-values no-rebase related q source-value target-value
      root@(pure-step (ground value not-equal)) =
    close-root no-rebase related q source-value target-value root

  sim-paired-cast-values no-rebase related q source-value target-value
      root@(pure-step (expand value not-equal)) =
    close-root no-rebase related q source-value target-value root

  sim-paired-cast-values no-rebase related q source-value target-value
      root@(pure-step (tag-untag value)) =
    close-root no-rebase related q source-value target-value root

  sim-paired-cast-values no-rebase related q source-value target-value
      root@(pure-step (tag-untag-bad value not-equal)) =
    close-root no-rebase related q source-value target-value root

  sim-paired-cast-values no-rebase related q source-value target-value
      root@(pure-step (blame-bot-intro value)) =
    close-root no-rebase related q source-value target-value root

  sim-paired-cast-values no-rebase related q () target-value
      (pure-step blame-⟨⟩)

  sim-paired-cast-values no-rebase related q source-value target-value
      root@(β-inst value not-star) =
    close-root no-rebase related q source-value target-value root

  sim-paired-cast-values no-rebase related q source-value target-value
      (ξ-⟨⟩ source-step renamed) =
    ⊥-elim (value-no-step source-value source-step)
