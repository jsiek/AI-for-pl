module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesProof
  where

-- File Charter:
--   * Implements target cast/conversion framing for completed source steps.
--   * Prefix-weakens the supplied target evidence to the completed relational
--     store, then frames only the target ξ-⟨⟩ tail.
--   * Preserves the exact source change/result and all final world invariants.
--   * Contains no active target-root normalization, hole, or permissive option.

open import Coercions using (Coercion; id-onlyᵈ)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( StoreChange
  ; applyTyCtxs
  ; applyTys
  ; keep
  )
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.Core.Properties.CoercionProperties using (modeRename-id-only)
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  ; weak-one-step-target-cast-frameᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( apply-conceal-conversions
  ; apply-narrows-typing
  ; apply-reveal-conversions
  ; seal★-id-only
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
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
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( WorldCoherentSourceOneStepIndexedResult
  ; sourceStepChangesExact
  ; sourceStepIndexedResult
  ; sourceStepResultExact
  ; sourceStepSourceNameExclusive
  ; sourceStepAssumptionMembershipUnique
  ; sourceStepStoreLineage
  ; sourceStepWorldCoherent
  ; world-coherent-source-one-step-indexed
  )
open import proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using
  ( WorldCoherentSourceOneStepTargetCastFrames
  ; sourceStepTargetConcealFrame
  ; sourceStepTargetIdWidenFrame
  ; sourceStepTargetNarrowFrame
  ; sourceStepTargetRevealFrame
  ; sourceStepTargetWidenFrame
  )
open import proof.Core.Properties.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using (applyCoercions)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


source-step-target-narrow-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A A′ B′ : Ty}
    {c′ : Coercion} {μ′} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊒ B′ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-target-narrow-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {q = q}
    prefix mode seal★ c′⊒ complete
    with apply-narrows-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c′⊒)
source-step-target-narrow-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {q = q}
    prefix mode seal★ c′⊒ complete
    | μ″ , mode″ , seal★″ , c″⊒ =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    (sourceStepResultExact complete)
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  final-seal :
    SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ″)
      (sym (targetStoreResult inner)) seal★″

  final-cast :
    μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) c′
        ∶ applyTys (targetTailChanges inner) A′
          ⊒ applyTys (targetTailChanges inner) B′
  final-cast =
    subst
      (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) c′
          ∶ applyTys (targetTailChanges inner) A′
            ⊒ applyTys (targetTailChanges inner) B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μ″ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner) c′
            ∶ applyTys (targetTailChanges inner) A′
              ⊒ applyTys (targetTailChanges inner) B′)
        (sym (targetStoreResult inner)) c″⊒)

  final-relation =
    ⊑cast⊒ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed₀) (transportType inner q)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (sourceStepIndexedResult complete))


source-step-target-widen-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A A′ B′ : Ty}
    {c′ : Coercion} {μ′} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊑ B′ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-target-widen-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {q = q}
    prefix mode seal★ c′⊑ complete
    with apply-widens-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c′⊑)
source-step-target-widen-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {q = q}
    prefix mode seal★ c′⊑ complete
    | μ″ , mode″ , seal★″ , c″⊑ =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    (sourceStepResultExact complete)
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  final-seal :
    SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ″)
      (sym (targetStoreResult inner)) seal★″

  final-cast :
    μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) c′
        ∶ applyTys (targetTailChanges inner) A′
          ⊑ applyTys (targetTailChanges inner) B′
  final-cast =
    subst
      (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) c′
          ∶ applyTys (targetTailChanges inner) A′
            ⊑ applyTys (targetTailChanges inner) B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μ″ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner) c′
            ∶ applyTys (targetTailChanges inner) A′
              ⊑ applyTys (targetTailChanges inner) B′)
        (sym (targetStoreResult inner)) c″⊑)

  final-relation =
    ⊑cast⊑ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed₀) (transportType inner q)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (sourceStepIndexedResult complete))


source-step-target-id-widen-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A A′ B′ : Ty}
    {c′ : Coercion} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊑ B′ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-target-id-widen-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {q = q}
    prefix seal★ c′⊑ complete =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    (sourceStepResultExact complete)
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  c″⊑ =
    apply-fixed-widens-typing
      {χs = keep ∷ targetTailChanges inner}
      (modeRename-id-only suc)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c′⊑)

  final-seal :
    SealModeStore★ id-onlyᵈ (rightStoreⁱ (resultStore inner))
  final-seal = seal★-id-only

  final-cast :
    id-onlyᵈ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) c′
        ∶ applyTys (targetTailChanges inner) A′
          ⊑ applyTys (targetTailChanges inner) B′
  final-cast =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) c′
          ∶ applyTys (targetTailChanges inner) A′
            ⊑ applyTys (targetTailChanges inner) B′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ
          ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner) c′
            ∶ applyTys (targetTailChanges inner) A′
              ⊑ applyTys (targetTailChanges inner) B′)
        (sym (targetStoreResult inner)) c″⊑)

  final-relation =
    ⊑cast⊑idᵀ final-seal final-cast
      (canonicalIndexedResults indexed₀) (transportType inner q)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (sourceStepIndexedResult complete))


source-step-target-reveal-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A A′ B′ : Ty}
    {c′ : Coercion} {μ′ β X′} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ₀) β X′ c′ A′ B′ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-target-reveal-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {q = q}
    prefix c′↑ complete
    with apply-reveal-conversions
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c′↑)
source-step-target-reveal-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {q = q}
    prefix c′↑ complete
    | μ″ , β″ , X″ , c″↑ =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    (sourceStepResultExact complete)
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  final-conversion :
    RevealConversion μ″ (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner)) β″ X″
      (applyCoercions (targetTailChanges inner) c′)
      (applyTys (targetTailChanges inner) A′)
      (applyTys (targetTailChanges inner) B′)
  final-conversion =
    subst
      (λ Δ → RevealConversion μ″ Δ
        (rightStoreⁱ (resultStore inner)) β″ X″
        (applyCoercions (targetTailChanges inner) c′)
        (applyTys (targetTailChanges inner) A′)
        (applyTys (targetTailChanges inner) B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ″
          (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ β″ X″
          (applyCoercions (targetTailChanges inner) c′)
          (applyTys (targetTailChanges inner) A′)
          (applyTys (targetTailChanges inner) B′))
        (sym (targetStoreResult inner)) c″↑)

  final-relation =
    ⊑conv↑ᵀ final-conversion
      (canonicalIndexedResults indexed₀) (transportType inner q)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (sourceStepIndexedResult complete))


source-step-target-conceal-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A A′ B′ : Ty}
    {c′ : Coercion} {μ′ β X′} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ₀) β X′ c′ A′ B′ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-target-conceal-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {q = q}
    prefix c′↓ complete
    with apply-conceal-conversions
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c′↓)
source-step-target-conceal-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {q = q}
    prefix c′↓ complete
    | μ″ , β″ , X″ , c″↓ =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    (sourceStepResultExact complete)
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  final-conversion :
    ConcealConversion μ″ (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner)) β″ X″
      (applyCoercions (targetTailChanges inner) c′)
      (applyTys (targetTailChanges inner) A′)
      (applyTys (targetTailChanges inner) B′)
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ″ Δ
        (rightStoreⁱ (resultStore inner)) β″ X″
        (applyCoercions (targetTailChanges inner) c′)
        (applyTys (targetTailChanges inner) A′)
        (applyTys (targetTailChanges inner) B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ″
          (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ β″ X″
          (applyCoercions (targetTailChanges inner) c′)
          (applyTys (targetTailChanges inner) A′)
          (applyTys (targetTailChanges inner) B′))
        (sym (targetStoreResult inner)) c″↓)

  final-relation =
    ⊑conv↓ᵀ final-conversion
      (canonicalIndexedResults indexed₀) (transportType inner q)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence (sourceStepIndexedResult complete))


world-coherent-source-one-step-target-cast-frames-proofᵀ :
  WorldCoherentSourceOneStepTargetCastFrames
world-coherent-source-one-step-target-cast-frames-proofᵀ = record
  { sourceStepTargetNarrowFrame = source-step-target-narrow-frameᵀ
  ; sourceStepTargetWidenFrame = source-step-target-widen-frameᵀ
  ; sourceStepTargetIdWidenFrame = source-step-target-id-widen-frameᵀ
  ; sourceStepTargetRevealFrame = source-step-target-reveal-frameᵀ
  ; sourceStepTargetConcealFrame = source-step-target-conceal-frameᵀ
  }
