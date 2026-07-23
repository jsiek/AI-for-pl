module proof.Right.Target.NuImprecisionRightTargetWidenInstPostBetaDef where

-- File Charter:
--   * Defines the semantic continuation after an active target
--     instantiation has taken its `β-inst` step to runtime `ν ★`.
--   * Isolates the index-sensitive binder work shared by all four
--     incoming/final paired/source-only matrix cells.
--   * Returns the existing complete right-value catch-up carrier and adds no
--     result, view, outcome, postulate, hole, option, or compatibility layer.

open import Coercions using (Coercion; ModeEnv; instᵈ)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; ν)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; ★; `∀; ⟰ᵗ; ⇑ᵗ)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightTargetWidenInstPostBetaᵀ : Set₁
WorldCoherentRightTargetWidenInstPostBetaᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {A B C : Ty} {s : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (ν ★ V′ s) →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ
    ∣ ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ `∀ C ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = ν ★ V′ s} {ρ = ρ} q
