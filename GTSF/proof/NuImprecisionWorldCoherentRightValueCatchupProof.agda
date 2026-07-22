module proof.NuImprecisionWorldCoherentRightValueCatchupProof where

-- File Charter:
--   * Projects the recursive ambient-prefix right-value catch-up result to
--     the compact terminal package consumed by forward DGG trace induction.
--   * Instantiates the recursive worker at the reflexive store prefix.
--   * Erases transport, lineage, and final preservation evidence only at this
--     terminal boundary.
--   * Contains no recursive catch-up implementation, postulate, or hole.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)

open import QuotientedTermImprecision using (prefix-reflⁱ)
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceUnchanged
  ; rightCatchupTargetValue
  )
open import proof.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; resultCtx
  ; resultStore
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  )
open import proof.NuImprecisionWorldCoherentRightValueCatchupDef using
  (WorldCoherentRightValueCatchupᵀ)
open import proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef using
  (WorldCoherentRightValueCatchupPrefixᵀ)


world-coherent-right-value-catchup-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentRightValueCatchupᵀ
world-coherent-right-value-catchup-proofᵀ
    prefix-catchup {p = p} coherent exclusive unique wfR
    okM′ vV noV V⊑M′
    with prefix-catchup prefix-reflⁱ coherent exclusive unique wfR okM′
      vV noV V⊑M′
world-coherent-right-value-catchup-proofᵀ
    prefix-catchup {p = p} coherent exclusive unique wfR
    okM′ vV noV V⊑M′
    | world-result
    with sourceCtxResult result
       | targetCtxResult result
       | rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
  where
  catchup = worldRightCatchupResult world-result
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
world-coherent-right-value-catchup-proofᵀ
    prefix-catchup {p = p} coherent exclusive unique wfR
    okM′ vV noV V⊑M′
    | world-result | refl | refl | refl | refl =
      targetResult result ,
      targetTailChanges result ,
      resultCtx result ,
      resultStore result ,
      transportType result p ,
      targetTail result ,
      rightCatchupTargetValue catchup ,
      sourceStoreResult result ,
      targetStoreResult result ,
      canonicalIndexedResults indexed
  where
  catchup = worldRightCatchupResult world-result
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
