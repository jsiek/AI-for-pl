module
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingInstAccProof
  where

-- File Charter:
--   * Proves the active target-`inst` cell of quotient-down pending
--     administration.
--   * Normalizes the proof-relevant quotient permutations, delegates the
--     post-`β-inst` allocation to the direct path leaf, and prepends the
--     target type-beta step beneath the ordinary outer cast tail.
--   * Derives the strictly smaller post-beta administration rank explicitly.
--   * Contains no ordinary pre-inst edge, new relation constructor, postulate,
--     hole, permissive option, or termination bypass.

open import Agda.Builtin.Equality using (refl)
open import Coercions using (Coercion; inst)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (<-trans; n<1+n)
open import Data.Product using (_,_)
open import ForallPermutation using (quotientᵖ)
open import Induction.WellFounded using (acc)
open import NuReduction using (pure-step; β-inst)
open import NuTerms using
  (RuntimeOK; Value; ok-no; ok-ν; ok-⟨⟩)
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureDef
  using (pendingAdministrationRank)
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureProof
  using (inst-rank-decreases; nu-rank-decreases)
open import proof.Core.Permutation.ForallPermutationPath using
  (normalize-forall-permutation)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (applyTargetPendingCasts)
open import
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingInstAccDef
  using (WorldCoherentRightTargetQuotientDownPendingInstAccᵀ)
open import
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingNuAllocationPathAccDef
  using
  (WorldCoherentRightTargetQuotientDownPendingNuAllocationPathAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextDef
  using (WorldCoherentRightTargetPendingCastPrependContextᵀ)


private
  apply-pending-runtime :
    ∀ (cs : List Coercion) {M} →
    RuntimeOK M →
    RuntimeOK (applyTargetPendingCasts M cs)
  apply-pending-runtime [] runtime = runtime
  apply-pending-runtime (c ∷ cs) runtime =
    apply-pending-runtime cs (ok-⟨⟩ runtime)

  inst-body-rank-decrease :
    ∀ {V} (vV : Value V) B c cs →
    pendingAdministrationRank vV (c ∷ cs)
      < pendingAdministrationRank vV (inst B c ∷ cs)
  inst-body-rank-decrease vV B c cs
      rewrite inst-rank-decreases vV B c cs
            | nu-rank-decreases vV c cs =
    <-trans
      (n<1+n _)
      (<-trans
        (n<1+n _)
        (<-trans (n<1+n _) (n<1+n _)))


world-coherent-right-target-quotient-down-pending-inst-acc-proofᵀ :
  WorldCoherentRightTargetQuotientDownPendingNuAllocationPathAccᵀ →
  WorldCoherentRightTargetPendingCastPrependContextᵀ →
  WorldCoherentRightTargetQuotientDownPendingInstAccᵀ
world-coherent-right-target-quotient-down-pending-inst-acc-proofᵀ
    allocation prepend
    {B = B} {s = s} {cs = cs}
    {qD =
      quotientᵖ
        source-permutation
        representative
        target-permutation}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape inst-shape square compatible tail
    with allocation
      (normalize-forall-permutation source-permutation)
      (normalize-forall-permutation target-permutation)
      refl refl
      source-value source-no-bullet vW noW
      (smaller (inst-body-rank-decrease vW B s cs))
      coherent exclusive unique wfR
      (apply-pending-runtime cs (ok-ν (ok-no noW)))
      relation widening u-shape inst-shape square compatible tail
world-coherent-right-target-quotient-down-pending-inst-acc-proofᵀ
    allocation prepend
    {B = B} {s = s} {cs = cs}
    {qD =
      quotientᵖ
        source-permutation
        representative
        target-permutation}
    source-value source-no-bullet vW noW (acc smaller)
    coherent exclusive unique wfR runtime relation
    widening u-shape inst-shape square compatible tail
    | caught , context-eq , right-prefix =
  prepend
    {cs = cs}
    (pure-step (β-inst vW))
    caught context-eq right-prefix
