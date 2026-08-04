module
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingCastsAccProof
  where

-- File Charter:
--   * Proves the terminal inert branch of quotient-down target pending
--     administration, delegates identity/sequence/unseal, and invokes the
--     separate checked instantiation cell.
--   * Closes the current proof-relevant quotient boundary with `closeᵀ`, then
--     invokes the canonical ordinary pending-cast worker on the outer tail.
--   * Preserves accessibility, context action, and right-only store lineage.
--   * Contains no new relation constructor, postulate, hole, permissive
--     option, catch-all case, or termination bypass.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (cast-inst)
open import Data.Product using (_,_)
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (n<1+n)
open import Induction.WellFounded using (acc)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary using (no; yes)

open import NuTerms using
  (no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using
  ( closeᵀ
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureProof
  using (inert-rank-decreases)
open import
  proof.Core.Properties.CoercionProperties
  using (inert-dec)
open import
  proof.Core.Properties.ActiveWideningShapeProperties
  using
  ( active-id-base
  ; active-id-star
  ; active-id-var
  ; active-inst
  ; active-sequence
  ; active-unseal
  ; active-widening-shape
  ; non-inst-id-base
  ; non-inst-id-star
  ; non-inst-id-var
  ; non-inst-sequence
  ; non-inst-unseal
  )
open import
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingCastsAccDef
  using (WorldCoherentRightTargetQuotientDownPendingCastsAccᵀ)
open import
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingNonInstantiationAccDef
  using
  (WorldCoherentRightTargetQuotientDownPendingNonInstantiationAccᵀ)
open import
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingInstAccDef
  using (WorldCoherentRightTargetQuotientDownPendingInstAccᵀ)
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
  WorldCoherentRightTargetQuotientDownPendingNonInstantiationAccᵀ →
  WorldCoherentRightTargetQuotientDownPendingInstAccᵀ →
  WorldCoherentRightTargetQuotientDownPendingCastsAccᵀ
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary non-inst inst-cell {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
    with inert-dec _
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary non-inst inst-cell {cs = cs}
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
    ordinary non-inst inst-cell {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
    | no not-inert
    with active-widening-shape s-shape not-inert
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary non-inst inst-cell {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
    | no not-inert
    | active-id-var =
  non-inst non-inst-id-var
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary non-inst inst-cell {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
    | no not-inert
    | active-id-base =
  non-inst non-inst-id-base
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary non-inst inst-cell {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
    | no not-inert
    | active-id-star =
  non-inst non-inst-id-star
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary non-inst inst-cell {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
    | no not-inert
    | active-sequence c-shape d-shape composition =
  non-inst
    (non-inst-sequence c-shape d-shape composition)
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary non-inst inst-cell {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
    | no not-inert
    | active-unseal =
  non-inst non-inst-unseal
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary non-inst inst-cell {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening@(quotient-id-widening source-widening
      (cast-inst hB occ c⊢ , target-widening))
    u-shape s-shape square compatible tail
    | no not-inert
    | active-inst c-shape =
  inst-cell
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
world-coherent-right-target-quotient-down-pending-casts-acc-proofᵀ
    ordinary non-inst inst-cell {cs = cs}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening@(quotient-cast-widening
      source-mode source-seal source-widening
      target-mode target-seal
      (cast-inst hB occ c⊢ , target-widening))
    u-shape s-shape square compatible tail
    | no not-inert
    | active-inst c-shape =
  inst-cell
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape s-shape square compatible tail
