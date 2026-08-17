module proof.DGG.SimPairedRevealValuesProof where

-- File Charter:
--   * Provides a checked residualized skeleton for paired reveal value
--     simulation.
--   * Names the paired conceal/reveal keep row separately from the paired
--     id-reveal target-replay row.
--   * Refutes source frame steps from value irreducibility.

open import Data.Empty using (⊥-elim)

open import Reduction using
  ( pure-step
  ; id-reveal
  ; conceal-reveal
  ; blame-reveal
  ; ξ-reveal
  )
open import proof.DGG.SimPairedRevealValuesDef
  using (SimPairedRevealValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


record SimPairedRevealValuesResiduals : Set₁ where
  field
    paired-id-reveal-row : SimPairedRevealValuesᵀ
    paired-conceal-reveal-row : SimPairedRevealValuesᵀ


sim-paired-reveal-values-with :
  SimPairedRevealValuesResiduals → SimPairedRevealValuesᵀ
sim-paired-reveal-values-with residuals parked mono rebase c⊢ c′⊢
    rel q vV step@(pure-step (id-reveal _)) caught =
  SimPairedRevealValuesResiduals.paired-id-reveal-row residuals
    parked mono rebase c⊢ c′⊢ rel q vV step caught
sim-paired-reveal-values-with residuals parked mono rebase c⊢ c′⊢
    rel q vV step@(pure-step (conceal-reveal _)) caught =
  SimPairedRevealValuesResiduals.paired-conceal-reveal-row residuals
    parked mono rebase c⊢ c′⊢ rel q vV step caught
sim-paired-reveal-values-with residuals _ _ _ _ _ _ _ ()
    (pure-step blame-reveal) _
sim-paired-reveal-values-with residuals _ _ _ _ _ _ _ vV
    (ξ-reveal step _) _ =
  ⊥-elim (value-no-step vV step)
