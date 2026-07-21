module proof.NuImprecisionWorldCoherentRightSourceFramesProof where

-- File Charter:
--   * Implements the four source-frame fields for world-coherent right-value
--     catch-up.
--   * Frames an already-completed inner right-value result through one inert
--     source narrowing, widening, reveal, or conceal cast.
--   * Preserves the inner target terminal value, source silence, transport,
--     type coherence, store lineage, world coherence, exclusivity, and target
--     store well-formedness.
--   * Contains no recursive dispatcher, axiom, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Coercions using (Coercion; Inert)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( right-value-indexed-catchup
  ; rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceUnchanged
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  ; rightCatchupTransport
  ; rightCatchupTypeCoherence
  )
open import proof.NuImprecisionSimulation using
  ( weak-one-step-source-cast-frame-coherenceᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frameᵀ
  ; weak-one-step-source-narrow-cast-indexed-frameᵀ
  ; weak-one-step-source-widen-cast-indexed-frameᵀ
  )
open import proof.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; relatedResults
  ; resultLeftCtx
  ; resultStore
  ; sourceCtxResult
  ; sourceStoreResult
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportNo•Terms
  ; transportType
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  )
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; world-coherent-right-value-indexed-catchup
  )
open import
  proof.NuImprecisionWorldCoherentRightSourceFramesDef using
  (WorldCoherentRightSourceFrames)
open import proof.TypePreservation using (seal★-weaken)


right-source-narrow-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B B′ : Ty} {c : Coercion} {μ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M′ →
  Value M →
  No• M →
  Inert c →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊒ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M ⟨ c ⟩} {M′ = M′} {ρ = ρ⁺} q
right-source-narrow-frameᵀ
    prefix coherent exclusive wfR okM′ vM noM inert mode seal★ c⊒
    M⊑M′
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent′ exclusive′ wfR′)
    with rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
right-source-narrow-frameᵀ
    prefix coherent exclusive wfR okM′ vM noM inert mode seal★ c⊒
    M⊑M′
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent′ exclusive′ wfR′)
    | refl | refl =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed refl refl
      (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
      (rightCatchupTargetValue catchup)
      (rightCatchupTargetNoBullet catchup)
      framed-transport framed-coherence)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent′ exclusive′ wfR′
  where
  seal★⁺ =
    seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★

  c⊒⁺ =
    narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) c⊒

  framed =
    weak-one-step-source-narrow-cast-indexed-frameᵀ
      mode seal★⁺ c⊒⁺ (rightCatchupIndexedResult catchup)

  framed-transport =
    weak-step-transport
      (transportNo•Terms (rightCatchupTransport catchup))

  framed-coherence =
    weak-step-type-coherence
      (transportArrowCoherent (rightCatchupTypeCoherence catchup))
      (transportAllCoherent (rightCatchupTypeCoherence catchup))


right-source-widen-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B B′ : Ty} {c : Coercion} {μ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M′ →
  Value M →
  No• M →
  Inert c →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M ⟨ c ⟩} {M′ = M′} {ρ = ρ⁺} q
right-source-widen-frameᵀ
    prefix coherent exclusive wfR okM′ vM noM inert mode seal★ c⊑
    M⊑M′
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent′ exclusive′ wfR′)
    with rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
right-source-widen-frameᵀ
    prefix coherent exclusive wfR okM′ vM noM inert mode seal★ c⊑
    M⊑M′
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent′ exclusive′ wfR′)
    | refl | refl =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed refl refl
      (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
      (rightCatchupTargetValue catchup)
      (rightCatchupTargetNoBullet catchup)
      framed-transport framed-coherence)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent′ exclusive′ wfR′
  where
  seal★⁺ =
    seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★

  c⊑⁺ =
    widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) c⊑

  framed =
    weak-one-step-source-widen-cast-indexed-frameᵀ
      mode seal★⁺ c⊑⁺ (rightCatchupIndexedResult catchup)

  framed-transport =
    weak-step-transport
      (transportNo•Terms (rightCatchupTransport catchup))

  framed-coherence =
    weak-step-type-coherence
      (transportArrowCoherent (rightCatchupTypeCoherence catchup))
      (transportAllCoherent (rightCatchupTypeCoherence catchup))


right-source-reveal-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B B′ : Ty} {c : Coercion} {μ α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M′ →
  Value M →
  No• M →
  Inert c →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M ⟨ c ⟩} {M′ = M′} {ρ = ρ⁺} q
right-source-reveal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c}
    prefix coherent exclusive wfR okM′ vM noM inert c↑ M⊑M′
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent′ exclusive′ wfR′)
    with rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
right-source-reveal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c}
    prefix coherent exclusive wfR okM′ vM noM inert c↑ M⊑M′
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent′ exclusive′ wfR′)
    | refl | refl =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed refl refl
      (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
      (rightCatchupTargetValue catchup)
      (rightCatchupTargetNoBullet catchup)
      framed-transport framed-coherence)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent′ exclusive′ wfR′
  where
  inner = weakIndexedResult (rightCatchupIndexedResult catchup)

  c↑⁺ =
    weaken-reveal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↑

  final-conversion =
    subst
      (λ Δ → RevealConversion _ Δ
        (leftStoreⁱ (resultStore inner)) _ _ c A B)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → RevealConversion _ Δᴸ Σ _ _ c A B)
        (sym (sourceStoreResult inner)) c↑⁺)

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults (rightCatchupIndexedResult catchup))
      (transportType inner _)

  first =
    weak-one-step-source-cast-frameᵀ inner final-relation

  framed =
    weak-indexed-result first (relatedResults first)

  framed-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (rightCatchupTransport catchup)

  framed-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (rightCatchupTypeCoherence catchup)


right-source-conceal-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B B′ : Ty} {c : Coercion} {μ α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M′ →
  Value M →
  No• M →
  Inert c →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M ⟨ c ⟩} {M′ = M′} {ρ = ρ⁺} q
right-source-conceal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c}
    prefix coherent exclusive wfR okM′ vM noM inert c↓ M⊑M′
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent′ exclusive′ wfR′)
    with rightCatchupSourceChangesEmpty catchup
       | rightCatchupSourceUnchanged catchup
right-source-conceal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c}
    prefix coherent exclusive wfR okM′ vM noM inert c↓ M⊑M′
    (world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet-transport coherent′ exclusive′ wfR′)
    | refl | refl =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup framed refl refl
      (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
      (rightCatchupTargetValue catchup)
      (rightCatchupTargetNoBullet catchup)
      framed-transport framed-coherence)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    source-bullet-transport coherent′ exclusive′ wfR′
  where
  inner = weakIndexedResult (rightCatchupIndexedResult catchup)

  c↓⁺ =
    weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↓

  final-conversion =
    subst
      (λ Δ → ConcealConversion _ Δ
        (leftStoreⁱ (resultStore inner)) _ _ c A B)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → ConcealConversion _ Δᴸ Σ _ _ c A B)
        (sym (sourceStoreResult inner)) c↓⁺)

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults (rightCatchupIndexedResult catchup))
      (transportType inner _)

  first =
    weak-one-step-source-cast-frameᵀ inner final-relation

  framed =
    weak-indexed-result first (relatedResults first)

  framed-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (rightCatchupTransport catchup)

  framed-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (rightCatchupTypeCoherence catchup)


world-coherent-right-source-frames-proof :
  WorldCoherentRightSourceFrames
world-coherent-right-source-frames-proof = record
  { rightSourceNarrowFrame = right-source-narrow-frameᵀ
  ; rightSourceWidenFrame = right-source-widen-frameᵀ
  ; rightSourceRevealFrame = right-source-reveal-frameᵀ
  ; rightSourceConcealFrame = right-source-conceal-frameᵀ
  }
