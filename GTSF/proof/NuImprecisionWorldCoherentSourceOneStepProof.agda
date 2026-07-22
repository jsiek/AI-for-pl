module proof.NuImprecisionWorldCoherentSourceOneStepProof where

-- File Charter:
--   * Specializes the ambient-prefix recursive source one-step worker to the
--     current store and projects its outcome to the DGG-facing contract.
--   * Erases generic transport and store lineage on the related branch only
--     after checking the exact distinguished source change and result term.
--   * Contains no recursive simulation implementation, postulate, or hole.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  ( StoreImp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  )

open import proof.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; resultCtx
  ; resultStore
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import proof.NuImprecisionWorldCoherentSourceOneStepDef using
  (WorldCoherentSourceOneStepSimulationᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepOutcomeDef using
  ( source-step-outcome-related
  ; source-step-outcome-source-blame
  )
open import proof.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( sourceStepAssumptionMembershipUnique
  ; sourceStepChangesExact
  ; sourceStepIndexedResult
  ; sourceStepResultExact
  ; sourceStepSourceNameExclusive
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
    | source-step-outcome-related exact-result
    with sourceCtxResult result
       | targetCtxResult result
       | sourceStepChangesExact exact-result
       | sourceStepResultExact exact-result
  where
  indexed = sourceStepIndexedResult exact-result
  result = weakIndexedResult indexed
world-coherent-source-one-step-proofᵀ
    prefix-step {p = p} coherent exclusive unique wfL wfR
    okM okM′ M⊑M′ source-step
    | source-step-outcome-related exact-result
    | refl | refl | refl | refl =
    inj₁
      (targetResult result ,
      targetTailChanges result ,
      resultCtx result ,
      resultStore result ,
      transportType result p ,
      targetTail result ,
      sourceStepWorldCoherent exact-result ,
      sourceStepSourceNameExclusive exact-result ,
      sourceStepAssumptionMembershipUnique exact-result ,
      sourceStoreResult result ,
      targetStoreResult result ,
      canonicalIndexedResults indexed)
  where
  indexed = sourceStepIndexedResult exact-result
  result = weakIndexedResult indexed
