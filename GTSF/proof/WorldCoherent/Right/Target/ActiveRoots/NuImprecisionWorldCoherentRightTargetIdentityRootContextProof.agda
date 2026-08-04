module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetIdentityRootContextProof
  where

-- File Charter:
--   * Proves the shared contextual target identity root by framing the inner
--     catch-up, taking the post-catch-up `β-id` step, and resuming through a
--     contextual zero-step terminal continuation.
--   * Reuses the existing contextual target-step resumption theorem and
--     introduces no identity-specific result carrier.
--   * Contains no postulate, hole, permissive option, termination bypass, or
--     broad DGG import.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
import Coercions as C
open import NuReduction using
  ( applyTy
  ; applyTys
  ; bind
  ; keep
  ; pure-step
  ; β-id
  ; _—→[_]_
  )
open import NuTerms using (No•; Value; _⟨_⟩)
open import QuotientedTermImprecision using (prefix-reflⁱ)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Types using (Atom; Ty; ⇑ᵗ; ＇_; ‵_; ★)
open import proof.OneStep.NuImprecisionAtomicTargetReindex using
  (atomic-target-value-reindexᵀ)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; resultStore
  ; sourceResult
  ; targetResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( world-coherent-right-value-indexed-catchup
  ; worldRightCatchupResult
  )
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextDef
  using (WorldCoherentRightValueTerminalContextᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetIdentityRootContextDef
  using (WorldCoherentRightTargetIdentityRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextDef
  using (WorldCoherentRightTargetStepResumeContextᵀ)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)


private
  applyTy-preserves-Atom :
    ∀ χ {A} →
    Atom A →
    Atom (applyTy χ A)
  applyTy-preserves-Atom keep atom = atom
  applyTy-preserves-Atom (bind A) (＇ X) = ＇ (suc X)
  applyTy-preserves-Atom (bind A) (‵ ι) = ‵ ι
  applyTy-preserves-Atom (bind A) ★ = ★

  applyTys-preserves-Atom :
    ∀ χs {A} →
    Atom A →
    Atom (applyTys χs A)
  applyTys-preserves-Atom [] atom = atom
  applyTys-preserves-Atom (χ ∷ χs) atom =
    applyTys-preserves-Atom χs (applyTy-preserves-Atom χ atom)

  post-catchup-β-id :
    ∀ χs {V A} →
    Value V →
    V ⟨ applyCoercions χs (C.id A) ⟩ —→[ keep ] V
  post-catchup-β-id [] vV = pure-step (β-id vV)
  post-catchup-β-id (keep ∷ χs) vV =
    post-catchup-β-id χs vV
  post-catchup-β-id (bind A ∷ χs) {A = B} vV =
    post-catchup-β-id χs {A = ⇑ᵗ B} vV


world-coherent-right-target-identity-root-context-proofᵀ :
  WorldCoherentRightValueTerminalContextᵀ →
  WorldCoherentRightTargetStepResumeContextᵀ →
  WorldCoherentRightTargetIdentityRootContextᵀ
world-coherent-right-target-identity-root-context-proofᵀ
    terminal resume
    {B = B} {q = q} atom
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    with terminal
      {ρ₀ = resultStore
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      {ρ⁺ = resultStore
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      {V = sourceResult
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      {V′ = targetResult
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      prefix-reflⁱ final-world final-exclusive final-unique final-wfR
      (subst Value
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceValue catchup))
      (subst No•
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceNoBullet catchup))
      (rightCatchupTargetValue catchup)
      (rightCatchupTargetNoBullet catchup)
      (atomic-target-value-reindexᵀ
        (applyTys-preserves-Atom
          (targetTailChanges
            (weakIndexedResult
              (rightCatchupIndexedResult catchup)))
          atom)
        (rightCatchupTargetValue catchup)
        (canonicalIndexedResults
          (rightCatchupIndexedResult catchup))
        (transportType
          (weakIndexedResult
            (rightCatchupIndexedResult catchup))
          q))
world-coherent-right-target-identity-root-context-proofᵀ
    terminal resume
    {B = B} {q = q} atom
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | continued , continued-context , continued-prefix =
  resume
    inner context-eq right-prefix framed
    (post-catchup-β-id
      (targetTailChanges result)
      (rightCatchupTargetValue catchup))
    continued continued-context continued-prefix
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
