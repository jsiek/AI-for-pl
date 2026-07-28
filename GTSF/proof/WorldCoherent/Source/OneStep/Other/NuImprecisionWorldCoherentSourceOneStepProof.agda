module proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepProof where

-- File Charter:
--   * Specializes the ambient-prefix recursive source one-step worker to the
--     current store and projects its outcome to the DGG-facing contract.
--   * Erases generic transport and store lineage on the related branch only
--     after checking the exact distinguished source change and result term.
--   * Contains no recursive simulation implementation, postulate, or hole.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( leftCtxⁱ
  ; rightCtxⁱ
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; prefix-reflⁱ
  )

open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; resultCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepDef using
  (WorldCoherentSourceOneStepSimulationᵀ)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef using
  ( source-step-outcome-related
  ; source-step-outcome-source-blame
  )
open import proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( sourceStepAssumptionMembershipUnique
  ; sourceStepChanges
  ; sourceStepIndexedResult
  ; sourceStepSourceNameExclusive
  ; sourceStepTail
  ; sourceStepTailChanges
  ; sourceStepWorldCoherent
  )
open import TermTyping using (_∣_∣_⊢_⦂_)


normalize-source-one-step-empty-runtime-context :
  ∀ {Δ Σ Γ M A} →
  Γ ≡ [] →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A
normalize-source-one-step-empty-runtime-context refl M⊢ = M⊢


source-one-step-empty-context-source-typing :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A
source-one-step-empty-context-source-typing
    {Φ} {Δᴸ} {Δᴿ} {M} {M′} {A} {B} {ρ} {p} M⊑M′ =
  normalize-source-one-step-empty-runtime-context
    {Γ = leftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} []} refl
    (nu-term-imprecision-source-typing
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γ = []}
      {M = M} {M′ = M′} {A = A} {B = B} {p = p} M⊑M′)


source-one-step-empty-context-target-typing :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ B
source-one-step-empty-context-target-typing
    {Φ} {Δᴸ} {Δᴿ} {M} {M′} {A} {B} {ρ} {p} M⊑M′ =
  normalize-source-one-step-empty-runtime-context
    {Γ = rightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} []} refl
    (nu-term-imprecision-target-typing
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γ = []}
      {M = M} {M′ = M′} {A = A} {B = B} {p = p} M⊑M′)


world-coherent-source-one-step-proofᵀ :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentSourceOneStepSimulationᵀ
world-coherent-source-one-step-proofᵀ
    prefix-step {p = p} coherent exclusive unique wfL wfR
    okM okM′ M⊑M′ source-step
    with prefix-step prefix-reflⁱ coherent exclusive unique wfL wfR okM okM′
      (source-one-step-empty-context-source-typing M⊑M′)
      (source-one-step-empty-context-target-typing M⊑M′)
      M⊑M′ source-step
world-coherent-source-one-step-proofᵀ
    prefix-step {p = p} coherent exclusive unique wfL wfR
    okM okM′ M⊑M′ source-step
    | source-step-outcome-source-blame source↠blame =
      inj₂ (_ , source↠blame)
world-coherent-source-one-step-proofᵀ
    prefix-step {p = p} coherent exclusive unique wfL wfR
    okM okM′ M⊑M′ source-step
    | source-step-outcome-related complete
    with sourceStepChanges complete
       | sourceCtxResult result
       | targetCtxResult result
  where
  indexed = sourceStepIndexedResult complete
  result = weakIndexedResult indexed
world-coherent-source-one-step-proofᵀ
    prefix-step {p = p} coherent exclusive unique wfL wfR
    okM okM′ M⊑M′ source-step
    | source-step-outcome-related complete
    | refl | refl | refl =
    inj₁
      (sourceResult result ,
      targetResult result ,
      sourceStepTailChanges complete ,
      targetTailChanges result ,
      resultCtx result ,
      resultStore result ,
      transportType result p ,
      sourceStepTail complete ,
      targetTail result ,
      sourceStepWorldCoherent complete ,
      sourceStepSourceNameExclusive complete ,
      sourceStepAssumptionMembershipUnique complete ,
      sourceStoreResult result ,
      targetStoreResult result ,
      canonicalIndexedResults indexed)
  where
  indexed = sourceStepIndexedResult complete
  result = weakIndexedResult indexed
