module proof.NuImprecisionWorldCoherentSourceOneStepDef where

-- File Charter:
--   * Defines the source-oriented one-step simulation contract used by
--     forward terminal DGG trace induction.
--   * Requires and returns world coherence and source-name exclusivity on the
--     continuing related branch.
--   * Returns either a continuing related result after the distinguished
--     source step or a source trace to blame.
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
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


WorldCoherentSourceOneStepSimulationᵀ : Set₁
WorldCoherentSourceOneStepSimulationᵀ =
  ∀ {Φ Δᴸ Δᴿ M M′ L A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  M —→[ χ ] L →
  (∃[ L′ ] (Σ[ θs ∈ StoreChanges ]
    (∃[ Ψ ] (Σ[ ρ′ ∈
        StoreImp Ψ
          (applyTyCtx χ Δᴸ) (applyTyCtxs θs Δᴿ) ]
    (Σ[ q ∈
        (Ψ ∣ applyTyCtx χ Δᴸ
          ⊢ applyTy χ A ⊑ applyTys θs B
          ⊣ applyTyCtxs θs Δᴿ) ]
      ((M′ —↠[ θs ] L′) ×
       WorldCoherent ρ′ ×
       SourceNameExclusive Ψ ×
       (leftStoreⁱ ρ′ ≡ applyStore χ (leftStoreⁱ ρ)) ×
       (rightStoreⁱ ρ′ ≡ applyStores θs (rightStoreⁱ ρ)) ×
       Ψ ∣ applyTyCtx χ Δᴸ
         ∣ applyTyCtxs θs Δᴿ ∣ ρ′ ∣ []
         ⊢ᴺ L ⊑ L′
         ⦂ applyTy χ A ⊑ applyTys θs B ∶ q))))))
  ⊎ (∃[ χs ] (M —↠[ χs ] blame))
