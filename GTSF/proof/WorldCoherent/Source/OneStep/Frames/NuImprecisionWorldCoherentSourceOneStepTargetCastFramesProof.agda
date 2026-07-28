module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesProof
  where

-- File Charter:
--   * Implements target cast/conversion framing for completed source steps.
--   * Prefix-weakens the supplied target evidence to the completed relational
--     store, then frames only the target ξ-⟨⟩ tail.
--   * Preserves the exact source change/result and all final world invariants.
--   * Contains no active target-root normalization, hole, or permissive option.

import CastImprecisionShape as CastShape
open import Coercions using
  (Coercion; id-onlyᵈ; id-only≤tag-or-idᵈ)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import Data.List using (_∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using
  ( narrow-weaken
  ; widen-mode-relax
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
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ; seal★-tag-or-id)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)
open import TermTyping using
  (CastMode; SealModeStore★; cast-tag-or-id)
open import Types using (Ty; TyCtx)
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  ; weak-one-step-target-cast-frameᵀ
  )
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-narrows-typing)
open import proof.Core.Properties.NuConversionTransport
  using
  ( apply-conceal-conversions-exact
  ; apply-reveal-conversions-exact
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; relatedResults
  ; resultRightCtx
  ; resultStore
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
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
  (apply-widens-typing)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyTyVars)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


source-step-target-narrow-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A A′ B′ : Ty}
    {c′ : Coercion} {μ′} {χ : StoreChange}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊒ B′ →
  CastShape.narrowing CastShape.⊢ᶜ c′ ⦂ s →
  ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-target-narrow-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′}
    {p = p} {q = q}
    prefix mode seal★ c′⊒ c-shape comp complete
    with apply-narrows-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c′⊒)
source-step-target-narrow-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′}
    {p = p} {q = q}
    prefix mode seal★ c′⊒ c-shape comp complete
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
      (cast-shape-applyCoercions (targetTailChanges inner)
        c-shape)
      (imprecision-composition-shape-transport
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed₀) q)
        refl
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed₀) p)
        comp)

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
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊑ B′ →
  CastShape.widening CastShape.⊢ᶜ c′ ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-target-widen-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′}
    {p = p} {q = q}
    prefix mode seal★ c′⊑ c-shape comp complete
    with apply-widens-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c′⊑)
source-step-target-widen-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′}
    {p = p} {q = q}
    prefix mode seal★ c′⊑ c-shape comp complete
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
      (cast-shape-applyCoercions (targetTailChanges inner)
        c-shape)
      (imprecision-composition-shape-transport
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed₀) p)
        refl
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed₀) q)
        comp)

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
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊑ B′ →
  CastShape.widening CastShape.⊢ᶜ c′ ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-target-id-widen-frameᵀ
    prefix seal★ c′⊑ c-shape comp complete =
  source-step-target-widen-frameᵀ
    prefix cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ c′⊑)
    c-shape comp complete


source-step-target-reveal-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A A′ B′ : Ty}
    {c′ : Coercion} {μ′ β X′} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ₀) β X′ c′ A′ B′ →
  p [ β ↦ X′ ]ᴿ q →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-target-reveal-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′}
    {β = β} {X′ = X′} {q = q}
    prefix c′↑ replace complete
    with apply-reveal-conversions-exact
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c′↑)
source-step-target-reveal-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′}
    {β = β} {X′ = X′} {q = q}
    prefix c′↑ replace complete
    | μ″ , c″↑ =
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
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X′)
      (applyCoercions (targetTailChanges inner) c′)
      (applyTys (targetTailChanges inner) A′)
      (applyTys (targetTailChanges inner) B′)
  final-conversion =
    subst
      (λ Δ → RevealConversion μ″ Δ
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X′)
        (applyCoercions (targetTailChanges inner) c′)
        (applyTys (targetTailChanges inner) A′)
        (applyTys (targetTailChanges inner) B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ″
          (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
          (applyTyVars (targetTailChanges inner) β)
          (applyTys (targetTailChanges inner) X′)
          (applyCoercions (targetTailChanges inner) c′)
          (applyTys (targetTailChanges inner) A′)
          (applyTys (targetTailChanges inner) B′))
        (sym (targetStoreResult inner)) c″↑)

  final-relation =
    ⊑conv↑ᵀ final-conversion
      (canonicalIndexedResults indexed₀) (transportType inner q)
      (transportRightReplacementCoherent
        (weakIndexedTypeCoherence indexed₀) replace)

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
  q [ β ↦ X′ ]ᴿ p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-target-conceal-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′}
    {β = β} {X′ = X′} {q = q}
    prefix c′↓ replace complete
    with apply-conceal-conversions-exact
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c′↓)
source-step-target-conceal-frameᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′}
    {β = β} {X′ = X′} {q = q}
    prefix c′↓ replace complete
    | μ″ , c″↓ =
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
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X′)
      (applyCoercions (targetTailChanges inner) c′)
      (applyTys (targetTailChanges inner) A′)
      (applyTys (targetTailChanges inner) B′)
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ″ Δ
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X′)
        (applyCoercions (targetTailChanges inner) c′)
        (applyTys (targetTailChanges inner) A′)
        (applyTys (targetTailChanges inner) B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ″
          (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
          (applyTyVars (targetTailChanges inner) β)
          (applyTys (targetTailChanges inner) X′)
          (applyCoercions (targetTailChanges inner) c′)
          (applyTys (targetTailChanges inner) A′)
          (applyTys (targetTailChanges inner) B′))
        (sym (targetStoreResult inner)) c″↓)

  final-relation =
    ⊑conv↓ᵀ final-conversion
      (canonicalIndexedResults indexed₀) (transportType inner q)
      (transportRightReplacementCoherent
        (weakIndexedTypeCoherence indexed₀) replace)

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
