module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesProof
  where

-- File Charter:
--   * Implements ordinary and casted target-ν framing for completed source
--     steps.
--   * Prefix-weakens target ν evidence to the completed relational store, then
--     delegates the weak one-step result to the target ν frame helpers.
--   * Preserves the exact source change/result, lineage, world coherence, and
--     source-name exclusivity fields.
--   * Contains no outcome wrapper, result alias, hole, postulate, or
--     permissive option.

open import Coercions using (Coercion; instᵈ)
open import Conversion using (RevealConversion; weaken-reveal-conversion)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; ⇑ᴿᵢ)
open import NarrowWiden using (widen-weaken; _∣_∣_⊢_∶_⊑_)
open import NuReduction using (StoreChange)
open import NuStore using (StoreIncl-cons)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; ν)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; WfTy; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( weak-one-step-target-ν-frameᵀ
  ; weak-one-step-target-ν-frame-preserves-transportᵀ
  ; weak-one-step-target-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-target-νcast-frameᵀ
  ; weak-one-step-target-νcast-frame-preserves-transportᵀ
  ; weak-one-step-target-νcast-frame-preserves-type-coherenceᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( relatedResults
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
open import proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
  using
  ( WorldCoherentSourceOneStepTargetNuFrames
  ; sourceStepTargetNuCastFrame
  ; sourceStepTargetNuFrame
  )
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


source-step-target-ν-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B B′ C′ : Ty}
    {s : Coercion} {μ} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WfTy Δᴿ A →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
  (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = B} {B = `∀ C′} {χ = χ} {ρ = ρ⁺} q →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = ν A M′ s} {L = L}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} p
source-step-target-ν-frameᵀ {p = p}
    prefix hA s↑ r complete =
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

  target-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix))

  s↑⁺ = weaken-reveal-conversion target-store-incl s↑

  framed = weak-one-step-target-ν-frameᵀ hA s↑⁺ p r inner
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-target-ν-frame-preserves-transportᵀ
      hA s↑⁺ p r inner (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-target-ν-frame-preserves-type-coherenceᵀ
      hA s↑⁺ p r inner (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-target-ν-frame-preserves-transportᵀ
      hA s↑⁺ p r inner (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-target-ν-frame-preserves-type-coherenceᵀ
      hA s↑⁺ p r inner (weakIndexedTypeCoherence (sourceStepIndexedResult complete))


source-step-target-νcast-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {B B′ C′ : Ty}
    {s : Coercion} {μ} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀)) →
  instᵈ μ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
  (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = B} {B = `∀ C′} {χ = χ} {ρ = ρ⁺} q →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = ν ★ M′ s} {L = L}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} p
source-step-target-νcast-frameᵀ {p = p}
    prefix mode seal★ s⊑ r complete =
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

  target-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix))

  seal★⁺ = seal★-weaken target-store-incl seal★

  s⊑⁺ = widen-weaken ≤-refl target-store-incl s⊑

  framed =
    weak-one-step-target-νcast-frameᵀ
      mode seal★⁺ s⊑⁺ p r inner
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-target-νcast-frame-preserves-transportᵀ
      mode seal★⁺ s⊑⁺ p r inner (weakIndexedTransport (sourceStepIndexedResult complete)))
    (weak-one-step-target-νcast-frame-preserves-type-coherenceᵀ
      mode seal★⁺ s⊑⁺ p r inner (weakIndexedTypeCoherence (sourceStepIndexedResult complete)))
  framed-transport =
    weak-one-step-target-νcast-frame-preserves-transportᵀ
      mode seal★⁺ s⊑⁺ p r inner (weakIndexedTransport (sourceStepIndexedResult complete))
  framed-coherence =
    weak-one-step-target-νcast-frame-preserves-type-coherenceᵀ
      mode seal★⁺ s⊑⁺ p r inner (weakIndexedTypeCoherence (sourceStepIndexedResult complete))


world-coherent-source-one-step-target-nu-frames-proofᵀ :
  WorldCoherentSourceOneStepTargetNuFrames
world-coherent-source-one-step-target-nu-frames-proofᵀ = record
  { sourceStepTargetNuFrame = source-step-target-ν-frameᵀ
  ; sourceStepTargetNuCastFrame = source-step-target-νcast-frameᵀ
  }
