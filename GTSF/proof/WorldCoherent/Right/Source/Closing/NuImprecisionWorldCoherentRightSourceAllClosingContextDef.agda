module
  proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingContextDef
  where

-- File Charter:
--   * Defines source-universal closing with the target-only context and store
--     lineage exposed in its conclusion.
--   * Reuses the existing complete catch-up carrier and adds only flat
--     equality and prefix witnesses.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; Σ-syntax)

open import Imprecision using (NonVar)
open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _∣_⊢_⊑_⊣_; ⇑ᴸᵢ)
import ImprecisionWf as IW
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( LiftLeftCtxⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; Λ_)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; occurs)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  (resultCtx; resultStore; targetTailChanges; weakIndexedResult)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (lineageStore)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightSourceAllClosingContextᵀ : Set₁
WorldCoherentRightSourceAllClosingContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {V N′ : Term} {A B : Ty}
    {{safe : NonVar A}}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {occ : occurs zero A ≡ true} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK N′ →
  Value V →
  No• V →
  LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
  LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
  Σ[ closed ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = Λ V} {M′ = N′} {ρ = ρ⁺}
      (IW.ν safe occ p) ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult closed)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult closed))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage closed))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult closed))))
