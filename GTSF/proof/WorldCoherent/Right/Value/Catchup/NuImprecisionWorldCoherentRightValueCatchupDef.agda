module proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupDef where

-- File Charter:
--   * Defines target catch-up from a related source value for forward terminal
--     DGG trace induction.
--   * Keeps the source context, type, and physical store fixed while exposing
--     every target store change and the final related target value.
--   * Requires the world and store invariants used by target administrative
--     reduction but returns only the terminal package consumed by DGG.
--   * Contains no implementation and imports only statement-level support.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; _—↠[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (No•; RuntimeOK; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


WorldCoherentRightValueCatchupᵀ : Set₁
WorldCoherentRightValueCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ V M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M′ →
  Value V →
  No• V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
  ∃[ V′ ] (Σ[ θs ∈ StoreChanges ]
  (∃[ Ψ ] (Σ[ ρ′ ∈
      StoreImp Ψ Δᴸ (applyTyCtxs θs Δᴿ) ]
  (Σ[ q ∈
      (Ψ ∣ Δᴸ
        ⊢ A ⊑ applyTys θs B
        ⊣ applyTyCtxs θs Δᴿ) ]
    ((M′ —↠[ θs ] V′) ×
     Value V′ ×
     (leftStoreⁱ ρ′ ≡ leftStoreⁱ ρ) ×
     (rightStoreⁱ ρ′ ≡ applyStores θs (rightStoreⁱ ρ)) ×
     Ψ ∣ Δᴸ ∣ applyTyCtxs θs Δᴿ ∣ ρ′ ∣ []
       ⊢ᴺ V ⊑ V′ ⦂ A ⊑ applyTys θs B ∶ q)))))
