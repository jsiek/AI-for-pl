module
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingCastsAccProof
  where

-- File Charter:
--   * Proves the terminal inert branch of quotient-down target pending
--     administration and delegates only non-inert active casts.
--   * Closes the current proof-relevant quotient boundary with `closeᵀ`, then
--     invokes the canonical ordinary pending-cast worker on the outer tail.
--   * Preserves accessibility, context action, and right-only store lineage.
--   * Contains no new relation constructor, postulate, hole, permissive
--     option, catch-all case, or termination bypass.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (n<1+n)
open import Induction.WellFounded using (acc)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary using (no; yes)

open import NuTerms using
  (no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using (closeᵀ)
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureProof
  using (inert-rank-decreases)
open import
  proof.Core.Properties.CoercionProperties
  using (inert-dec)
open import
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingCastsAccDef
  using (WorldCoherentRightTargetQuotientDownPendingCastsAccᵀ)
open import
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingCastsResidualAccDef
  using (WorldCoherentRightTargetQuotientDownPendingCastsResidualAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsAccDef
  using (WorldCoherentRightTargetPendingCastsAccᵀ)


private
  successor-rank-decrease :
    ∀ {inner outer} →
    outer ≡ suc inner →
    inner < outer
  successor-rank-decrease {inner} equality =
    subst (inner <_) (sym equality) (n<1+n inner)


world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ :
  WorldCoherentRightTargetPendingCastsAccᵀ →
  WorldCoherentRightTargetQuotientDownPendingCastsResidualAccᵀ →
  WorldCoherentRightTargetQuotientDownPendingCastsAccᵀ
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary residual {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
    with inert-dec _
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary residual {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
    | yes inert-s =
  ordinary
    (vW ⟨ inert-s ⟩)
    (smaller
      (successor-rank-decrease
        (inert-rank-decreases vW inert-s cs)))
    tail coherent exclusive unique wfR runtime
    source-value source-no-bullet (no•-⟨⟩ noW)
    (closeᵀ relation widening _ u-shape s-shape square compatible)
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary residual {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
    | no not-inert =
  residual not-inert
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
