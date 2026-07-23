module
  proof.NuImprecisionWorldCoherentRightTargetInertFramingProof
  where

-- File Charter:
--   * Proves right-target inert-cast framing for completed strong right-value
--     catch-up results.
--   * Dispatches the statement's reveal, conceal, narrowing, widening, and
--     identity-mode widening alternatives directly to the focused target-frame
--     infrastructure.
--   * Preserves source silence, transport, type coherence, store lineage,
--     world coherence, source-name exclusivity, and target-store
--     well-formedness.
--   * Contains no result type, outcome type, alias, postulate, hole,
--     incomplete match, permissive option, or compatibility wrapper.

open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Coercions using (id-onlyᵈ)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using (applyTyCtxs; applyTys; keep)
open import NuTermImprecision using (rightStoreⁱ)
open import NuTerms using (no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using
  ( ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import TermTyping using (SealModeStore★)
open import proof.CoercionProperties using (modeRename-id-only)
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( right-value-indexed-catchup
  ; rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.NuImprecisionSimulation using
  ( weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  ; weak-one-step-target-cast-frameᵀ
  )
open import proof.NuImprecisionSimulationCore using
  ( apply-conceal-conversions
  ; apply-narrows-typing
  ; apply-reveal-conversions
  ; seal★-id-only
  )
open import proof.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; relatedResults
  ; resultRightCtx
  ; resultStore
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import
  proof.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( world-coherent-right-value-indexed-catchup
  )
open import
  proof.NuImprecisionWorldCoherentRightTargetInertFramingDef
  using (WorldCoherentRightTargetInertFramingᵀ)
open import proof.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.ReductionProperties using
  (applyCoercions; applyCoercions-preserves-Inert)
open import proof.TypePreservation using (seal★-weaken)


world-coherent-right-target-inert-framing-proofᵀ :
  WorldCoherentRightTargetInertFramingᵀ
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c} {q = q}
    prefix inert (inj₁ (_ , _ , _ , c↑))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    with apply-reveal-conversions
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↑)
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c} {q = q}
    prefix inert (inj₁ (_ , _ , _ , c↑))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    | μ″ , β″ , X″ , c″↑ =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed
      (rightCatchupSourceChangesEmpty catchup)
      (rightCatchupSourceUnchanged catchup)
      (rightCatchupSourceValue catchup)
      (rightCatchupSourceNoBullet catchup)
      (rightCatchupTargetValue catchup ⟨ inert⁺ ⟩)
      (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent exclusive unique wfR
  where
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  inert⁺ =
    applyCoercions-preserves-Inert (targetTailChanges inner) inert

  final-conversion :
    RevealConversion μ″ (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner)) β″ X″
      (applyCoercions (targetTailChanges inner) c)
      (applyTys (targetTailChanges inner) A′)
      (applyTys (targetTailChanges inner) B′)
  final-conversion =
    subst
      (λ Δ → RevealConversion μ″ Δ
        (rightStoreⁱ (resultStore inner)) β″ X″
        (applyCoercions (targetTailChanges inner) c)
        (applyTys (targetTailChanges inner) A′)
        (applyTys (targetTailChanges inner) B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ″
          (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ β″ X″
          (applyCoercions (targetTailChanges inner) c)
          (applyTys (targetTailChanges inner) A′)
          (applyTys (targetTailChanges inner) B′))
        (sym (targetStoreResult inner)) c″↑)

  final-relation =
    ⊑conv↑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  first =
    weak-one-step-target-cast-frameᵀ inner final-relation

  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed =
    weak-indexed-result first (relatedResults first)
      framed-transport framed-coherence
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c} {q = q}
    prefix inert (inj₂ (inj₁ (_ , _ , _ , c↓)))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    with apply-conceal-conversions
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↓)
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c} {q = q}
    prefix inert (inj₂ (inj₁ (_ , _ , _ , c↓)))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    | μ″ , β″ , X″ , c″↓ =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed
      (rightCatchupSourceChangesEmpty catchup)
      (rightCatchupSourceUnchanged catchup)
      (rightCatchupSourceValue catchup)
      (rightCatchupSourceNoBullet catchup)
      (rightCatchupTargetValue catchup ⟨ inert⁺ ⟩)
      (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent exclusive unique wfR
  where
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  inert⁺ =
    applyCoercions-preserves-Inert (targetTailChanges inner) inert

  final-conversion :
    ConcealConversion μ″ (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner)) β″ X″
      (applyCoercions (targetTailChanges inner) c)
      (applyTys (targetTailChanges inner) A′)
      (applyTys (targetTailChanges inner) B′)
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ″ Δ
        (rightStoreⁱ (resultStore inner)) β″ X″
        (applyCoercions (targetTailChanges inner) c)
        (applyTys (targetTailChanges inner) A′)
        (applyTys (targetTailChanges inner) B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ″
          (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ β″ X″
          (applyCoercions (targetTailChanges inner) c)
          (applyTys (targetTailChanges inner) A′)
          (applyTys (targetTailChanges inner) B′))
        (sym (targetStoreResult inner)) c″↓)

  final-relation =
    ⊑conv↓ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  first =
    weak-one-step-target-cast-frameᵀ inner final-relation

  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed =
    weak-indexed-result first (relatedResults first)
      framed-transport framed-coherence
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c} {q = q}
    prefix inert (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊒))))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    with apply-narrows-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊒)
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c} {q = q}
    prefix inert (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊒))))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    | μ″ , mode″ , seal★″ , c″⊒ =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed
      (rightCatchupSourceChangesEmpty catchup)
      (rightCatchupSourceUnchanged catchup)
      (rightCatchupSourceValue catchup)
      (rightCatchupSourceNoBullet catchup)
      (rightCatchupTargetValue catchup ⟨ inert⁺ ⟩)
      (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent exclusive unique wfR
  where
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  inert⁺ =
    applyCoercions-preserves-Inert (targetTailChanges inner) inert

  final-seal :
    SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ″)
      (sym (targetStoreResult inner)) seal★″

  final-cast :
    μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) c
        ∶ applyTys (targetTailChanges inner) A′
          ⊒ applyTys (targetTailChanges inner) B′
  final-cast =
    subst
      (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) c
          ∶ applyTys (targetTailChanges inner) A′
            ⊒ applyTys (targetTailChanges inner) B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μ″ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner) c
            ∶ applyTys (targetTailChanges inner) A′
              ⊒ applyTys (targetTailChanges inner) B′)
        (sym (targetStoreResult inner)) c″⊒)

  final-relation =
    ⊑cast⊒ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)

  first =
    weak-one-step-target-cast-frameᵀ inner final-relation

  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed =
    weak-indexed-result first (relatedResults first)
      framed-transport framed-coherence
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c} {q = q}
    prefix inert
    (inj₂ (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊑)))))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    with apply-widens-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (rightCatchupIndexedResult catchup))}
      mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊑)
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c} {q = q}
    prefix inert
    (inj₂ (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊑)))))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR)
    | μ″ , mode″ , seal★″ , c″⊑ =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed
      (rightCatchupSourceChangesEmpty catchup)
      (rightCatchupSourceUnchanged catchup)
      (rightCatchupSourceValue catchup)
      (rightCatchupSourceNoBullet catchup)
      (rightCatchupTargetValue catchup ⟨ inert⁺ ⟩)
      (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent exclusive unique wfR
  where
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  inert⁺ =
    applyCoercions-preserves-Inert (targetTailChanges inner) inert

  final-seal :
    SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ″)
      (sym (targetStoreResult inner)) seal★″

  final-cast :
    μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) c
        ∶ applyTys (targetTailChanges inner) A′
          ⊑ applyTys (targetTailChanges inner) B′
  final-cast =
    subst
      (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) c
          ∶ applyTys (targetTailChanges inner) A′
            ⊑ applyTys (targetTailChanges inner) B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μ″ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner) c
            ∶ applyTys (targetTailChanges inner) A′
              ⊑ applyTys (targetTailChanges inner) B′)
        (sym (targetStoreResult inner)) c″⊑)

  final-relation =
    ⊑cast⊑ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)

  first =
    weak-one-step-target-cast-frameᵀ inner final-relation

  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed =
    weak-indexed-result first (relatedResults first)
      framed-transport framed-coherence
world-coherent-right-target-inert-framing-proofᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c = c} {q = q}
    prefix inert (inj₂ (inj₂ (inj₂ (inj₂ (seal★ , c⊑)))))
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent exclusive unique wfR) =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed
      (rightCatchupSourceChangesEmpty catchup)
      (rightCatchupSourceUnchanged catchup)
      (rightCatchupSourceValue catchup)
      (rightCatchupSourceNoBullet catchup)
      (rightCatchupTargetValue catchup ⟨ inert⁺ ⟩)
      (no•-⟨⟩ (rightCatchupTargetNoBullet catchup)))
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent exclusive unique wfR
  where
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  inert⁺ =
    applyCoercions-preserves-Inert (targetTailChanges inner) inert

  c″⊑ =
    apply-fixed-widens-typing
      {χs = keep ∷ targetTailChanges inner}
      (modeRename-id-only suc)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊑)

  final-seal :
    SealModeStore★ id-onlyᵈ (rightStoreⁱ (resultStore inner))
  final-seal = seal★-id-only

  final-cast :
    id-onlyᵈ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) c
        ∶ applyTys (targetTailChanges inner) A′
          ⊑ applyTys (targetTailChanges inner) B′
  final-cast =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) c
          ∶ applyTys (targetTailChanges inner) A′
            ⊑ applyTys (targetTailChanges inner) B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ
          ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner) c
            ∶ applyTys (targetTailChanges inner) A′
              ⊑ applyTys (targetTailChanges inner) B′)
        (sym (targetStoreResult inner)) c″⊑)

  final-relation =
    ⊑cast⊑idᵀ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)

  first =
    weak-one-step-target-cast-frameᵀ inner final-relation

  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (rightCatchupIndexedResult catchup))

  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup))

  framed =
    weak-indexed-result first (relatedResults first)
      framed-transport framed-coherence
