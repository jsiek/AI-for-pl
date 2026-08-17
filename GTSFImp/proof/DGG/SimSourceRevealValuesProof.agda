module proof.DGG.SimSourceRevealValuesProof where

-- File Charter:
--   * Implements the source-only reveal value simulation rows that are
--     already supported by the current catchup package.
--   * Leaves the conceal/reveal keep row as a named residual, to be supplied
--     by the two-sided/source-opened peel plumbing.
--   * Refutes source frame steps from value irreducibility.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)

open import Reduction using
  ( pure-step
  ; id-reveal
  ; conceal-reveal
  ; blame-reveal
  ; ξ-reveal
  )
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.CatchupToMorePreciseDef
  using (boundary-source-reveal)
open import proof.DGG.Parked.ParkedWorldDef
  using (evolve-keepᴸ)
open import proof.DGG.SimSourceRevealValuesDef
  using (SimSourceRevealValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


record SimSourceRevealValuesResiduals : Set₁ where
  field
    source-conceal-reveal-row : SimSourceRevealValuesᵀ


sim-source-reveal-values-with :
  SimSourceRevealValuesResiduals → SimSourceRevealValuesᵀ
sim-source-reveal-values-with residuals _ _ CTI2.rebase-idᴸ
    CTI2.⊢↑-idˣ _ _ vV (pure-step (id-reveal _))
    (Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , .W′ , _ ,
      boundary-source-reveal _ CTI2.tag-rebase-idᴸ , q′ ,
      _ , M′↠V′ , _ , evol , _ , _ , rel′) =
  Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , q′ ,
  M′↠V′ , evolve-keepᴸ evol , rel′
sim-source-reveal-values-with residuals parked mono rebase c⊢
    rel q vV step@(pure-step (conceal-reveal _)) caught =
  SimSourceRevealValuesResiduals.source-conceal-reveal-row residuals
    parked mono rebase c⊢ rel q vV step caught
sim-source-reveal-values-with residuals _ _ _ _ _ _ () (pure-step blame-reveal) _
sim-source-reveal-values-with residuals _ _ _ _ _ _ vV (ξ-reveal step _) _ =
  ⊥-elim (value-no-step vV step)
