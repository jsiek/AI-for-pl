module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowUntagRootContextProof
  where

-- File Charter:
--   * Proves the contextual ordinary target-narrowing untag root from target
--     tag cancellation, contextual value terminalization, and contextual
--     target-step resumption.
--   * Cancels the final ground tag, takes the post-catch-up `tag-untag-ok`
--     step, and preserves the target context action and right-only lineage.
--   * Contains no postulate, hole, permissive option, termination bypass, or
--     broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( applyTy
  ; applyTys
  ; bind
  ; keep
  ; pure-step
  ; tag-untag-ok
  ; _—→[_]_
  )
open import NuTerms using
  (No•; Value; no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using
  ( nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  )
open import TermTyping using (forget; _∣_∣_⊢_⦂_)
open import Types using
  (Ground; Ty; ★; ★⇒★; ＇_; ‵_; ⇑ᵗ)
open import proof.DGG.Core.NuProgress using
  (StarView; canonical-★; sv-tag)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (nu-term-imprecision-transport-typesᵀ)
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
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowUntagRootContextDef
  using (WorldCoherentRightTargetNarrowUntagRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextDef
  using (WorldCoherentRightTargetStepResumeContextᵀ)
open import
  proof.Target.SealTag.NuImprecisionTargetTagCancellationDef
  using (TargetTagCancellationᵀ)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)


private
  applyTy-preserves-Ground :
    ∀ χ {G} →
    Ground G →
    Ground (applyTy χ G)
  applyTy-preserves-Ground keep gG = gG
  applyTy-preserves-Ground (bind A) (＇ α) = ＇ (suc α)
  applyTy-preserves-Ground (bind A) (‵ ι) = ‵ ι
  applyTy-preserves-Ground (bind A) ★⇒★ = ★⇒★

  applyTys-preserves-Ground :
    ∀ χs {G} →
    Ground G →
    Ground (applyTys χs G)
  applyTys-preserves-Ground [] gG = gG
  applyTys-preserves-Ground (χ ∷ χs) gG =
    applyTys-preserves-Ground χs (applyTy-preserves-Ground χ gG)

  applyTys-star :
    ∀ χs →
    applyTys χs ★ ≡ ★
  applyTys-star [] = refl
  applyTys-star (keep ∷ χs) = applyTys-star χs
  applyTys-star (bind A ∷ χs) = applyTys-star χs

  applyCoercions-untag :
    ∀ χs H →
    applyCoercions χs (H C.？) ≡ applyTys χs H C.？
  applyCoercions-untag [] H = refl
  applyCoercions-untag (keep ∷ χs) H =
    applyCoercions-untag χs H
  applyCoercions-untag (bind A ∷ χs) H =
    applyCoercions-untag χs (⇑ᵗ H)

  canonical-applied-target-star :
    ∀ {Δ Σ V A} →
    A ≡ ★ →
    Value V →
    Δ ∣ Σ ∣ [] ⊢ V ⦂ A →
    StarView V
  canonical-applied-target-star refl vV V⊢ =
    canonical-★ vV (forget V⊢)

  tag-no•⁻¹ :
    ∀ {V G} →
    No• (V ⟨ G C.! ⟩) →
    No• V
  tag-no•⁻¹ (no•-⟨⟩ noV) = noV

  post-catchup-tag-untag :
    ∀ χs {V G H} →
    Value V →
    G ≡ applyTys χs H →
    V ⟨ G C.! ⟩
      ⟨ applyCoercions χs (H C.？) ⟩ —→[ keep ] V
  post-catchup-tag-untag χs {H = H} vV refl
      rewrite applyCoercions-untag χs H =
    pure-step (tag-untag-ok vV)


world-coherent-right-target-narrow-untag-root-context-proofᵀ :
  TargetTagCancellationᵀ →
  WorldCoherentRightValueTerminalContextᵀ →
  WorldCoherentRightTargetStepResumeContextᵀ →
  WorldCoherentRightTargetNarrowUntagRootContextᵀ
world-coherent-right-target-narrow-untag-root-context-proofᵀ
    cancel terminal resume
    {H = H} {q = q} gH
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    with canonical-applied-target-star
      (applyTys-star
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult catchup))))
      (rightCatchupTargetValue catchup)
      (nu-term-imprecision-target-typing
        (canonicalIndexedResults
          (rightCatchupIndexedResult catchup)))
world-coherent-right-target-narrow-untag-root-context-proofᵀ
    cancel terminal resume
    {H = H} {q = q} gH
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | sv-tag {W = W} {G = G} vW refl
    with cancel final-exclusive final-unique
      (applyTys-preserves-Ground
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult catchup)))
        gH)
      (subst Value
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceValue catchup))
      (subst No•
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceNoBullet catchup))
      vW
      (nu-term-imprecision-transport-typesᵀ
        refl
        (applyTys-star
          (targetTailChanges
            (weakIndexedResult
              (rightCatchupIndexedResult catchup))))
        refl
        (canonicalIndexedResults
          (rightCatchupIndexedResult catchup)))
      (transportType
        (weakIndexedResult
          (rightCatchupIndexedResult catchup))
        q)
world-coherent-right-target-narrow-untag-root-context-proofᵀ
    cancel terminal resume
    {H = H} {q = q} gH
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | sv-tag {W = W} {G = G} vW refl
    | tag-eq , canceled
    with terminal
      {ρ₀ = resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult catchup))}
      {ρ⁺ = resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult catchup))}
      {V = sourceResult
        (weakIndexedResult
          (rightCatchupIndexedResult catchup))}
      {V′ = W}
      prefix-reflⁱ final-world final-exclusive final-unique final-wfR
      (subst Value
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceValue catchup))
      (subst No•
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceNoBullet catchup))
      vW
      (tag-no•⁻¹ (rightCatchupTargetNoBullet catchup))
      canceled
world-coherent-right-target-narrow-untag-root-context-proofᵀ
    cancel terminal resume
    {H = H} {q = q} gH
    inner@(world-coherent-right-value-indexed-catchup
      catchup lineage bullet final-world final-exclusive final-unique
      final-wfR)
    context-eq right-prefix framed
    | sv-tag {W = W} {G = G} vW refl
    | tag-eq , canceled
    | continued , continued-context , continued-prefix =
  resume inner context-eq right-prefix framed
    (post-catchup-tag-untag
      (targetTailChanges result) vW tag-eq)
    continued continued-context continued-prefix
  where
  indexed = rightCatchupIndexedResult catchup
  result = weakIndexedResult indexed
