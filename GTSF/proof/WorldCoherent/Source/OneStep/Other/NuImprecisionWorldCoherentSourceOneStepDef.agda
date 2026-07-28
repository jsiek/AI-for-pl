module proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepDef where

-- File Charter:
--   * Defines the source-oriented one-step simulation contract used by
--     forward terminal DGG trace induction.
--   * Requires and returns world coherence, source-name exclusivity, and
--     assumption-membership uniqueness on the continuing related branch.
--   * Lets both sides reduce after the distinguished source step before the
--     next ordinary term-imprecision edge.
--   * Returns either that continuing related result or a source trace to
--     blame.
--   * Contains no implementation and imports only statement-level support.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChange
  ; StoreChanges
  ; applyStore
  ; applyStores
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


WorldCoherentSourceOneStepSimulationᵀ : Set₁
WorldCoherentSourceOneStepSimulationᵀ =
  ∀ {Φ Δᴸ Δᴿ M M′ L A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  M —→[ χ ] L →
  (∃[ K ] (∃[ L′ ] (Σ[ ψs ∈ StoreChanges ]
    (Σ[ θs ∈ StoreChanges ]
    (∃[ Ψ ] (Σ[ ρ′ ∈
        StoreImp Ψ
          (applyTyCtxs ψs (applyTyCtx χ Δᴸ))
          (applyTyCtxs θs Δᴿ) ]
    (Σ[ q ∈
        (Ψ ∣ applyTyCtxs ψs (applyTyCtx χ Δᴸ)
          ⊢ applyTys ψs (applyTy χ A) ⊑ applyTys θs B
          ⊣ applyTyCtxs θs Δᴿ) ]
      ((L —↠[ ψs ] K) ×
       (M′ —↠[ θs ] L′) ×
       WorldCoherent ρ′ ×
       SourceNameExclusive Ψ ×
       AssumptionMembershipUnique Ψ ×
       (leftStoreⁱ ρ′
         ≡ applyStores ψs (applyStore χ (leftStoreⁱ ρ))) ×
       (rightStoreⁱ ρ′ ≡ applyStores θs (rightStoreⁱ ρ)) ×
       Ψ ∣ applyTyCtxs ψs (applyTyCtx χ Δᴸ)
         ∣ applyTyCtxs θs Δᴿ ∣ ρ′ ∣ []
         ⊢ᴺ K ⊑ L′
         ⦂ applyTys ψs (applyTy χ A)
           ⊑ applyTys θs B ∶ q))))))))
  ⊎ (∃[ χs ] (M —↠[ χs ] blame))
