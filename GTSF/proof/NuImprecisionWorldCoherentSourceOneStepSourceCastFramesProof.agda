module
  proof.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesProof
  where

-- File Charter:
--   * Implements source cast/conversion framing for completed source steps.
--   * Prefix-weakens source evidence to the completed relational store, then
--     frames the source trace and final quotient relation.
--   * Preserves transport, type coherence, store lineage, exact source
--     change/result, world coherence, and source-name exclusivity.
--   * Contains no recursive source worker, hole, postulate, or permissive
--     option.

open import Coercions using (Coercion)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
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
  ; applyCoercion
  ; applyTyCtxs
  ; applyTys
  )
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  )
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; subst; sym)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionSimulation using
  ( weak-one-step-source-cast-frame-coherenceᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frameᵀ
  )
open import proof.NuImprecisionSimulationCore using
  ( apply-conceal-conversions
  ; apply-narrows-typing
  ; apply-reveal-conversions
  )
open import proof.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; relatedResults
  ; resultLeftCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; transportType
  ; weak-indexed-result
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
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( WorldCoherentSourceOneStepIndexedResult
  ; sourceStepChangesExact
  ; sourceStepIndexedResult
  ; sourceStepResultExact
  ; sourceStepSourceNameExclusive
  ; sourceStepStoreLineage
  ; sourceStepTransport
  ; sourceStepTypeCoherence
  ; sourceStepWorldCoherent
  ; world-coherent-source-one-step-indexed
  )
open import proof.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesDef
  using
  ( WorldCoherentSourceOneStepSourceCastFrames
  ; sourceStepSourceConcealFrame
  ; sourceStepSourceNarrowFrame
  ; sourceStepSourceRevealFrame
  ; sourceStepSourceWidenFrame
  )
open import proof.NuWideningTransport using (apply-widens-typing)
open import proof.ReductionProperties using (applyCoercions)
open import proof.TypePreservation using (seal★-weaken)


source-step-source-narrow-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B B′ : Ty}
    {c : Coercion} {μ} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊒ B →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M ⟨ c ⟩} {M′ = M′}
    {L = L ⟨ applyCoercion χ c ⟩}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-source-narrow-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix mode seal★ c⊒ complete
    with apply-narrows-typing
      {χs = sourceChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊒)
source-step-source-narrow-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix mode seal★ c⊒ complete
    | μ′ , mode′ , seal★′ , c′⊒ =
  world-coherent-source-one-step-indexed
    framed-indexed
    framed-transport
    framed-coherence
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) A
          ⊒ applyTys (sourceChanges inner) B
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) A
            ⊒ applyTys (sourceChanges inner) B)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) A
              ⊒ applyTys (sourceChanges inner) B)
        (sym (sourceStoreResult inner)) c′⊒)

  final-relation =
    cast⊒⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed₀) (transportType inner q)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
  framed-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (sourceStepTransport complete)
  framed-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (sourceStepTypeCoherence complete)

  cast-exact :
    applyCoercions (sourceChanges inner) c ≡ applyCoercion χ c
  cast-exact =
    cong (λ χs → applyCoercions χs c)
      (sourceStepChangesExact complete)

  framed-result-exact =
    cong₂ _⟨_⟩
      (sourceStepResultExact complete) cast-exact


source-step-source-widen-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B B′ : Ty}
    {c : Coercion} {μ} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M ⟨ c ⟩} {M′ = M′}
    {L = L ⟨ applyCoercion χ c ⟩}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-source-widen-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix mode seal★ c⊑ complete
    with apply-widens-typing
      {χs = sourceChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊑)
source-step-source-widen-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix mode seal★ c⊑ complete
    | μ′ , mode′ , seal★′ , c′⊑ =
  world-coherent-source-one-step-indexed
    framed-indexed
    framed-transport
    framed-coherence
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) A
          ⊑ applyTys (sourceChanges inner) B
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) A
            ⊑ applyTys (sourceChanges inner) B)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) A
              ⊑ applyTys (sourceChanges inner) B)
        (sym (sourceStoreResult inner)) c′⊑)

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed₀) (transportType inner q)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
  framed-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (sourceStepTransport complete)
  framed-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (sourceStepTypeCoherence complete)

  cast-exact :
    applyCoercions (sourceChanges inner) c ≡ applyCoercion χ c
  cast-exact =
    cong (λ χs → applyCoercions χs c)
      (sourceStepChangesExact complete)

  framed-result-exact =
    cong₂ _⟨_⟩
      (sourceStepResultExact complete) cast-exact


source-step-source-reveal-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B B′ : Ty}
    {c : Coercion} {μ α X} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M ⟨ c ⟩} {M′ = M′}
    {L = L ⟨ applyCoercion χ c ⟩}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-source-reveal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix c↑ complete
    with apply-reveal-conversions
      {χs = sourceChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) c↑)
source-step-source-reveal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix c↑ complete
    | μ′ , α′ , X′ , c′↑ =
  world-coherent-source-one-step-indexed
    framed-indexed
    framed-transport
    framed-coherence
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  final-conversion :
    RevealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner)) α′ X′
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final-conversion =
    subst
      (λ Δ → RevealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner)) α′ X′
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ α′ X′
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) c′↑)

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed₀) (transportType inner q)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
  framed-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (sourceStepTransport complete)
  framed-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (sourceStepTypeCoherence complete)

  cast-exact :
    applyCoercions (sourceChanges inner) c ≡ applyCoercion χ c
  cast-exact =
    cong (λ χs → applyCoercions χs c)
      (sourceStepChangesExact complete)

  framed-result-exact =
    cong₂ _⟨_⟩
      (sourceStepResultExact complete) cast-exact


source-step-source-conceal-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B B′ : Ty}
    {c : Coercion} {μ α X} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M ⟨ c ⟩} {M′ = M′}
    {L = L ⟨ applyCoercion χ c ⟩}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-source-conceal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix c↓ complete
    with apply-conceal-conversions
      {χs = sourceChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      (weaken-conceal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) c↓)
source-step-source-conceal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix c↓ complete
    | μ′ , α′ , X′ , c′↓ =
  world-coherent-source-one-step-indexed
    framed-indexed
    framed-transport
    framed-coherence
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepChangesExact complete)
    framed-result-exact
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  final-conversion :
    ConcealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner)) α′ X′
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner)) α′ X′
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ α′ X′
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) c′↓)

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed₀) (transportType inner q)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
  framed-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (sourceStepTransport complete)
  framed-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (sourceStepTypeCoherence complete)

  cast-exact :
    applyCoercions (sourceChanges inner) c ≡ applyCoercion χ c
  cast-exact =
    cong (λ χs → applyCoercions χs c)
      (sourceStepChangesExact complete)

  framed-result-exact =
    cong₂ _⟨_⟩
      (sourceStepResultExact complete) cast-exact


world-coherent-source-one-step-source-cast-frames-proofᵀ :
  WorldCoherentSourceOneStepSourceCastFrames
world-coherent-source-one-step-source-cast-frames-proofᵀ = record
  { sourceStepSourceNarrowFrame = source-step-source-narrow-frameᵀ
  ; sourceStepSourceWidenFrame = source-step-source-widen-frameᵀ
  ; sourceStepSourceRevealFrame = source-step-source-reveal-frameᵀ
  ; sourceStepSourceConcealFrame = source-step-source-conceal-frameᵀ
  }
