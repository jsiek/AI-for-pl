module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesProof
  where

-- File Charter:
--   * Implements source cast/conversion framing for completed source steps.
--   * Prefix-weakens source evidence to the completed relational store, then
--     frames the source trace and final quotient relation.
--   * Transports exact cast shapes, composition triangles, and conversion
--     replacements through the completed inner step.
--   * Preserves transport, type coherence, store lineage, the distinguished
--     source change and arbitrary tail, and final world invariants.
--   * Contains no recursive source worker, hole, postulate, or permissive
--     option.

open import Coercions using (Coercion)
open import CastImprecisionShape using
  (narrowing; widening; _⊢ᶜ_⦂_)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ConversionIndexCompatibility using (_[_↦_]ᴸ_)
open import Data.List using (_∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( StoreChange
  ; StoreChanges
  ; _—↠[_]_
  ; applyCoercion
  ; applyTyCtxs
  ; applyTys
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  )
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; sym)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.OneStep.NuImprecisionWeakOneStepSourceCastFrame using
  ( weak-one-step-source-cast-frame-coherenceᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frameᵀ
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
  ; resultLeftCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  ; transportLeftReplacementCoherent
  ; transportShapeCoherent
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( WorldCoherentSourceOneStepIndexedResult
  ; sourceStepChanges
  ; sourceStepIndexedResult
  ; sourceStepSourceNameExclusive
  ; sourceStepAssumptionMembershipUnique
  ; sourceStepStoreLineage
  ; sourceStepTail
  ; sourceStepTailChanges
  ; sourceStepWorldCoherent
  ; world-coherent-source-one-step-indexed
  )
open import proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesDef
  using
  ( WorldCoherentSourceOneStepSourceCastFrames
  ; sourceStepSourceConcealFrame
  ; sourceStepSourceNarrowFrame
  ; sourceStepSourceRevealFrame
  ; sourceStepSourceWidenFrame
  )
open import proof.Core.Properties.NuWideningTransport using (apply-widens-typing)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyTyVars; cast-↠)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


private
  cast-source-step-tail :
    ∀ {L N : Term} {c : Coercion} {χ : StoreChange}
      {χs χs⁺ : StoreChanges} →
    χs⁺ ≡ χ ∷ χs →
    L —↠[ χs ] N →
    L ⟨ applyCoercion χ c ⟩
      —↠[ χs ] N ⟨ applyCoercions χs⁺ c ⟩
  cast-source-step-tail
      {L = L} {N = N} {c = c} {χ = χ} {χs = χs} changes L↠N =
    subst
      (λ d → L ⟨ applyCoercion χ c ⟩ —↠[ χs ] N ⟨ d ⟩)
      (sym (cong (λ χs → applyCoercions χs c) changes))
      (cast-↠ {c = applyCoercion χ c} L↠N)


source-step-source-narrow-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B B′ : Ty}
    {c : Coercion} {μ} {χ : StoreChange}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊒ B →
  narrowing ⊢ᶜ c ⦂ s →
  s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M ⟨ c ⟩} {M′ = M′}
    {L = L ⟨ applyCoercion χ c ⟩}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-source-narrow-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix mode seal★ c⊒ c-shape comp complete
    with apply-narrows-typing
      {χs = sourceChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊒)
source-step-source-narrow-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix mode seal★ c⊒ c-shape comp complete
    | μ′ , mode′ , seal★′ , c′⊒ =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepTailChanges complete)
    (sourceStepChanges complete)
    (cast-source-step-tail
      (sourceStepChanges complete) (sourceStepTail complete))
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
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
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (imprecision-composition-shape-transport
        refl
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed₀) _)
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed₀) q)
        comp)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed₀))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed₀))


source-step-source-widen-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B B′ : Ty}
    {c : Coercion} {μ} {χ : StoreChange}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M ⟨ c ⟩} {M′ = M′}
    {L = L ⟨ applyCoercion χ c ⟩}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-source-widen-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix mode seal★ c⊑ c-shape comp complete
    with apply-widens-typing
      {χs = sourceChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊑)
source-step-source-widen-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {χ = χ} {q = q}
    prefix mode seal★ c⊑ c-shape comp complete
    | μ′ , mode′ , seal★′ , c′⊑ =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepTailChanges complete)
    (sourceStepChanges complete)
    (cast-source-step-tail
      (sourceStepChanges complete) (sourceStepTail complete))
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
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
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (imprecision-composition-shape-transport
        refl
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed₀) q)
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed₀) _)
        comp)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed₀))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed₀))


source-step-source-reveal-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B B′ : Ty}
    {c : Coercion} {μ α X} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  p [ α ↦ X ]ᴸ q →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M ⟨ c ⟩} {M′ = M′}
    {L = L ⟨ applyCoercion χ c ⟩}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-source-reveal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c}
    {α = α} {X = X} {χ = χ} {q = q}
    prefix c↑ replace complete
    with apply-reveal-conversions-exact
      {χs = sourceChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) c↑)
source-step-source-reveal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c}
    {α = α} {X = X} {χ = χ} {q = q}
    prefix c↑ replace complete
    | μ′ , c′↑ =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepTailChanges complete)
    (sourceStepChanges complete)
    (cast-source-step-tail
      (sourceStepChanges complete) (sourceStepTail complete))
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  final-conversion :
    RevealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner))
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final-conversion =
    subst
      (λ Δ → RevealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner))
        (applyTyVars (sourceChanges inner) α)
        (applyTys (sourceChanges inner) X)
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ
          (applyTyVars (sourceChanges inner) α)
          (applyTys (sourceChanges inner) X)
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) c′↑)

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed₀) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed₀) replace)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed₀))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed₀))


source-step-source-conceal-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B B′ : Ty}
    {c : Coercion} {μ α X} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  q [ α ↦ X ]ᴸ p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M ⟨ c ⟩} {M′ = M′}
    {L = L ⟨ applyCoercion χ c ⟩}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q
source-step-source-conceal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c}
    {α = α} {X = X} {χ = χ} {q = q}
    prefix c↓ replace complete
    with apply-conceal-conversions-exact
      {χs = sourceChanges
        (weakIndexedResult (sourceStepIndexedResult complete))}
      (weaken-conceal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) c↓)
source-step-source-conceal-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c}
    {α = α} {X = X} {χ = χ} {q = q}
    prefix c↓ replace complete
    | μ′ , c′↓ =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepTailChanges complete)
    (sourceStepChanges complete)
    (cast-source-step-tail
      (sourceStepChanges complete) (sourceStepTail complete))
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  final-conversion :
    ConcealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner))
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner))
        (applyTyVars (sourceChanges inner) α)
        (applyTys (sourceChanges inner) X)
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ
          (applyTyVars (sourceChanges inner) α)
          (applyTys (sourceChanges inner) X)
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) c′↓)

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed₀) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed₀) replace)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed₀))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed₀))


world-coherent-source-one-step-source-cast-frames-proofᵀ :
  WorldCoherentSourceOneStepSourceCastFrames
world-coherent-source-one-step-source-cast-frames-proofᵀ = record
  { sourceStepSourceNarrowFrame = source-step-source-narrow-frameᵀ
  ; sourceStepSourceWidenFrame = source-step-source-widen-frameᵀ
  ; sourceStepSourceRevealFrame = source-step-source-reveal-frameᵀ
  ; sourceStepSourceConcealFrame = source-step-source-conceal-frameᵀ
  }
