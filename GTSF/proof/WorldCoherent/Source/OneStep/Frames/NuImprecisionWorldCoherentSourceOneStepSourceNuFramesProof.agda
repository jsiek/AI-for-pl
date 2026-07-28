module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepSourceNuFramesProof
  where

-- File Charter:
--   * Implements matched and source-only ordinary/casted source-ν framing for
--     completed source steps.
--   * Prefix-weakens reveal, seal, and widening evidence to the completed
--     relational store, then delegates to the weak source-ν frame helpers.
--   * Preserves store lineage, the arbitrary administrative source tail,
--     final world coherence, and source-name exclusivity.
--   * Contains no outcome wrapper, result alias, compatibility shim, hole,
--     postulate, permissive option, or incomplete match.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (Coercion; instᵈ)
open import Conversion using (RevealConversion; weaken-reveal-conversion)
import CastImprecisionShape as CastShape
open import ConversionIndexCompatibility using
  (_[_↦_]ᴸ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  )
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using (widen-weaken; _∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( StoreChange
  ; applyCoercionUnderTyBinder
  ; applyTy
  ; keep
  )
open import NuStore using (StoreIncl-cons)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; ν)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; WfTy; occurs; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( weak-indexed-all-resultᵀ
  ; weak-one-step-matched-ν-frameᵀ
  ; weak-one-step-matched-ν-frame-preserves-transportᵀ
  ; weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-source-ν-frameᵀ
  ; weak-one-step-source-ν-frame-preserves-transportᵀ
  ; weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepAllResult
  ; WeakOneStepResult
  ; relatedResults
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
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
  ; sourceStepTail
  ; sourceStepTailChanges
  ; sourceStepSourceNameExclusive
  ; sourceStepAssumptionMembershipUnique
  ; sourceStepStoreLineage
  ; sourceStepWorldCoherent
  ; world-coherent-source-one-step-indexed
  )
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepSourceNuFramesDef
  using
  ( WorldCoherentSourceOneStepSourceNuFrames
  ; sourceStepMatchedNuFrame
  ; sourceStepSourceNuFrame
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyTy-★
  ; ν-↠
  )
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ)


source-step-matched-ν-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N N′ L : Term} {A A′ B B′ C C′ : Ty}
    {s s′ : Coercion} {μ μ′} {χ : StoreChange}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB →
  WorldCoherentSourceOneStepIndexedResult
    {M = N} {M′ = N′} {L = L}
    {A = `∀ C} {B = `∀ C′} {χ = χ} {ρ = ρ⁺} (∀ⁱ q) →
  WorldCoherentSourceOneStepIndexedResult
    {M = ν A N s} {M′ = ν A′ N′ s′}
    {L = ν (applyTy χ A) L (applyCoercionUnderTyBinder χ s)}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB
source-step-matched-ν-frameᵀ
    {ρ⁺ = ρ⁺} {N = N} {N′ = N′} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {C = C} {C′ = C′} {s = s}
    {s′ = s′} {χ = χ} {q = q}
    {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    prefix s↑ s′↑ replacement complete
    with sourceStepChanges complete
source-step-matched-ν-frameᵀ
    {ρ⁺ = ρ⁺} {N = N} {N′ = N′} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {C = C} {C′ = C′} {s = s}
    {s′ = s′} {χ = χ} {q = q}
    {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    prefix s↑ s′↑ replacement complete
    | refl =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepTailChanges complete)
    refl
    (ν-↠ (sourceStepTail complete))
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  all : WeakOneStepAllResult
    {N = N} {N₁′ = N′} {C = C} {C′ = C′}
    {χ = keep} {ρ = ρ⁺} q
  all =
    weak-indexed-all-resultᵀ {q = q} indexed₀

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  target-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix))

  s↑⁺ = weaken-reveal-conversion source-store-incl s↑
  s′↑⁺ = weaken-reveal-conversion target-store-incl s′↑
  coherence₀ = weakIndexedTypeCoherence indexed₀

  framed : WeakOneStepResult ρ⁺
    (ν A N s)
    (ν (applyTy keep A′) N′ (applyCoercionUnderTyBinder keep s′))
    B B′ keep
  framed =
    weak-one-step-matched-ν-frameᵀ {χ = keep} {q = q}
      s↑⁺ s′↑⁺ pA A⇑⊑A′⇑ pB replacement all coherence₀
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-matched-ν-frame-preserves-transportᵀ
      {χ = keep} {q = q}
      s↑⁺ s′↑⁺ pA A⇑⊑A′⇑ pB replacement all coherence₀
      (weakIndexedTransport indexed₀))
    (weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
      {χ = keep} {q = q}
      s↑⁺ s′↑⁺ pA A⇑⊑A′⇑ pB replacement all coherence₀)
  framed-transport =
    weak-one-step-matched-ν-frame-preserves-transportᵀ
      {χ = keep} {q = q}
      s↑⁺ s′↑⁺ pA A⇑⊑A′⇑ pB replacement all coherence₀
      (weakIndexedTransport indexed₀)
  framed-coherence =
    weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
      {χ = keep} {q = q}
      s↑⁺ s′↑⁺ pA A⇑⊑A′⇑ pB replacement all coherence₀

source-step-source-ν-frameᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N N′ L : Term} {A B B′ C : Ty}
    {s : Coercion} {μ} {χ : StoreChange}
    {occ : occurs zero C ≡ true}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  {{safe : NonVar C}} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WfTy Δᴸ A →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
  WorldCoherentSourceOneStepIndexedResult
    {M = N} {M′ = N′} {L = L}
    {A = `∀ C} {B = B′} {χ = χ} {ρ = ρ⁺}
    (ν safe occ q) →
  WorldCoherentSourceOneStepIndexedResult
    {M = ν A N s} {M′ = N′}
    {L = ν (applyTy χ A) L (applyCoercionUnderTyBinder χ s)}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} pB
source-step-source-ν-frameᵀ {A = A} {s = s} {χ = χ} {pB = pB}
    prefix hA s↑ replacement complete
    with sourceStepChanges complete
source-step-source-ν-frameᵀ {A = A} {s = s} {χ = χ} {pB = pB}
    prefix hA s↑ replacement complete
    | refl =
  world-coherent-source-one-step-indexed
    framed-indexed
    (weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete)))
    (sourceStepTailChanges complete)
    refl
    (ν-↠ (sourceStepTail complete))
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  indexed₀ = sourceStepIndexedResult complete
  inner = weakIndexedResult indexed₀

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  s↑⁺ = weaken-reveal-conversion source-store-incl s↑

  framed =
    weak-one-step-source-ν-frameᵀ hA s↑⁺ pB replacement indexed₀
  framed-indexed = weak-indexed-result framed (relatedResults framed)
    (weak-one-step-source-ν-frame-preserves-transportᵀ
      hA s↑⁺ pB replacement indexed₀
      (weakIndexedTransport indexed₀))
    (weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
      hA s↑⁺ pB replacement indexed₀
      (weakIndexedTypeCoherence indexed₀))
  framed-transport =
    weak-one-step-source-ν-frame-preserves-transportᵀ
      hA s↑⁺ pB replacement indexed₀
      (weakIndexedTransport indexed₀)
  framed-coherence =
    weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
      hA s↑⁺ pB replacement indexed₀
      (weakIndexedTypeCoherence indexed₀)

world-coherent-source-one-step-source-nu-frames-proofᵀ :
  WorldCoherentSourceOneStepSourceNuFrames
world-coherent-source-one-step-source-nu-frames-proofᵀ = record
  { sourceStepMatchedNuFrame =
      λ {Φ} {Δᴸ} {Δᴿ} {ρ₀} {ρ⁺}
        {N} {N′} {L} {A} {A′} {B} {B′} {C} {C′}
        {s} {s′} {μ} {μ′} {χ} {q} {pA} {A⇑⊑A′⇑} {pB}
        prefix s↑ s′↑ replacement complete →
        source-step-matched-ν-frameᵀ
          {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
          {ρ₀ = ρ₀} {ρ⁺ = ρ⁺}
          {N = N} {N′ = N′} {L = L}
          {A = A} {A′ = A′} {B = B} {B′ = B′}
          {C = C} {C′ = C′}
          {s = s} {s′ = s′} {μ = μ} {μ′ = μ′}
          {χ = χ} {q = q} {pA = pA}
          {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
          prefix s↑ s′↑ replacement complete
  ; sourceStepSourceNuFrame = source-step-source-ν-frameᵀ
  }
