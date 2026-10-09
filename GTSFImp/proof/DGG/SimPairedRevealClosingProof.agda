{-# OPTIONS --safe #-}

module proof.DGG.SimPairedRevealClosingProof where

-- File Charter:
--   * Proves paired reveal closing after catching the target reveal body up
--     to a related value.
--   * Transports generator positions, pivot alignment, representation types,
--     and the target conversion across that catch-up evolution.
--   * Is parameterized only by target catch-up and the genuine value/value
--     paired-reveal induction; it has no classifier or residual family.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (refl; subst; sym; trans)

open import CastTerms using (_↑_)
open import Reduction
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.CatchupToMorePreciseDef using
  (CatchupToMorePrecise)
open import proof.DGG.SimPairedRevealClosingDef using
  (SimPairedRevealClosingᵀ)
open import proof.DGG.SimPairedRevealValuesDef using
  (SimPairedRevealValuesᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using
  ( composeMultiWorldEvolution
  ; multi-no-open-frames
  ; multi-⊑ᵀ
  ; multi-aligned
  ; multi-target-reveal
  ; multi-target-reveal-position
  )
open import proof.Reduction using
  ( _++χ_
  ; _—↠+[_]⟨_⟩_
  ; applyTys-++
  ; applyReveals
  ; reveal-↠
  )
open import proof.Reduction.ValueIrreducibleProof using
  (value-no-step)


module _
    (catchup-to-more-precise : CatchupToMorePrecise)
    (sim-paired-reveal-values : SimPairedRevealValuesᵀ)
  where

  private
    close-root : SimPairedRevealClosingᵀ
    close-root {c′ = c′} no-rebase c⊢ c′⊢ positions aligned
        represented related q source-value source-step
        with catchup-to-more-precise no-rebase related source-value
    close-root {c = c} {c′ = c′} no-rebase c⊢ c′⊢ positions aligned
        represented related q source-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-value , γ₁ , type-rel₁ ,
        target-steps , target-is-value , evolution₁ , related₁
        with sim-paired-reveal-values
          (multi-no-open-frames evolution₁ no-rebase)
          c⊢ (multi-target-reveal evolution₁ c′⊢)
          (trans positions
            (sym (multi-target-reveal-position evolution₁ c′⊢)))
          (multi-aligned evolution₁ aligned)
          (multi-⊑ᵀ evolution₁ represented)
          related₁ (multi-⊑ᵀ evolution₁ q)
          source-value target-is-value source-step
    close-root {M′ = M′} {c′ = c′}
        no-rebase c⊢ c′⊢ positions aligned represented related q
        source-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-value , γ₁ , type-rel₁ ,
        target-steps , target-is-value , evolution₁ , related₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , result , γ₂ , result-rel ,
        root-steps , root-evolution , result-related
        with subst
          (λ T →
            Σ[ r ∈ _ ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ ⊢² _ ⊑ result ∶ r)
          (applyTys-++ χsᴿ₁ χsᴿ₂ _)
          (result-rel , result-related)
    close-root {M′ = M′} {c′ = c′}
        no-rebase c⊢ c′⊢ positions aligned represented related q
        source-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-value , γ₁ , type-rel₁ ,
        target-steps , target-is-value , evolution₁ , related₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , result , γ₂ , result-rel ,
        root-steps , root-evolution , result-related
      | result-rel′ , result-related′ =
        Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ , result , γ₂ ,
        result-rel′ ,
        (M′ ↑ c′
          —↠+[ χsᴿ₁ ]⟨ reveal-↠ c′ target-steps ⟩
         target-value ↑ applyReveals χsᴿ₁ c′
          —↠[ χsᴿ₂ ]⟨ root-steps ⟩
         result ∎[]) ,
        composeMultiWorldEvolution evolution₁ root-evolution ,
        result-related′

  sim-paired-reveal-closing : SimPairedRevealClosingᵀ
  sim-paired-reveal-closing no-rebase c⊢ c′⊢ positions aligned
      represented related q source-value
      root@(pure-step (id-reveal value)) =
    close-root no-rebase c⊢ c′⊢ positions aligned represented
      related q source-value root

  sim-paired-reveal-closing no-rebase c⊢ c′⊢ positions aligned
      represented related q source-value
      root@(pure-step (conceal-reveal value)) =
    close-root no-rebase c⊢ c′⊢ positions aligned represented
      related q source-value root

  sim-paired-reveal-closing no-rebase c⊢ c′⊢ positions aligned
      represented related q () (pure-step blame-reveal)

  sim-paired-reveal-closing no-rebase c⊢ c′⊢ positions aligned
      represented related q source-value
      (ξ-reveal source-step renamed) =
    ⊥-elim (value-no-step source-value source-step)
