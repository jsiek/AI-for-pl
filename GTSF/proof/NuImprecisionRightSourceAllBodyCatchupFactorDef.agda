module
  proof.NuImprecisionRightSourceAllBodyCatchupFactorDef
  where

-- File Charter:
--   * Defines source-universal body catch-up with both final context shape
--     and final relational-store left-lift factorization exposed.
--   * Uses heterogeneous equality at the single dependent-store boundary,
--     while keeping the existing catch-up carrier and all base-world
--     invariants explicit.
--   * Contains no implementation, recursion, result/view/outcome hierarchy,
--     postulate, hole, permissive option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; ∃-syntax; Σ-syntax)
import Relation.Binary.HeterogeneousEquality as HE

open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _∣_⊢_⊑_⊣_; ⇑ᴸᵢ)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using (No•; RuntimeOK; Term; Value)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.NuImprecisionRelStoreEmbeddingDef using
  (RelStoreEmbeddingⁱ)
open import proof.NuImprecisionSimulationResultDef using
  ( resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; targetTailChanges
  ; weakIndexedResult
  )
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  )
open import proof.ReductionProperties using (applyTyVars)


WorldCoherentRightSourceAllBodyCatchupFactorᵀ : Set₁
WorldCoherentRightSourceAllBodyCatchupFactorᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {V N′ : Term} {A B : Ty}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK N′ →
  Value V →
  No• V →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
  ∃[ ρ⁺ᴸ ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ⁺ ρ⁺ᴸ ×
    StoreImpPrefix ρᴸ ρ⁺ᴸ ×
    Σ[ caught ∈
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = N′} {ρ = ρ⁺ᴸ} p ]
      let result =
            weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))
          Φ⁺ =
            applyRightImpCtxChanges
              (targetTailChanges result) Φ
      in
      resultCtx result
        ≡ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ⁺
      ×
      resultLeftCtx result ≡ suc Δᴸ
      ×
      Σ[ Δᴿ⁺ ∈ TyCtx ]
      Σ[ ρlineage ∈ StoreImp Φ⁺ Δᴸ Δᴿ⁺ ]
      Σ[ ρbase ∈ StoreImp Φ⁺ Δᴸ Δᴿ⁺ ]
      Σ[ ρlift ∈
        StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ⁺)
          (suc Δᴸ) Δᴿ⁺ ]
        resultRightCtx result ≡ Δᴿ⁺
        ×
        HE._≅_ (resultStore result) ρlift
        ×
        RelStoreEmbeddingⁱ
          (applyTyVars [])
          (applyTyVars (targetTailChanges result))
          ρ⁺ ρlineage
        ×
        RightOnlyStoreImpPrefix ρlineage ρbase
        ×
        LiftLeftStoreⁱ
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ⁺) ρbase ρlift
        ×
        WorldCoherent ρbase
        ×
        SourceNameExclusive Φ⁺
        ×
        AssumptionMembershipUnique Φ⁺
        ×
        StoreWf Δᴿ⁺ (rightStoreⁱ ρbase)
