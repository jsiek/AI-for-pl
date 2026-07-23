module proof.NuImprecisionRightTargetWidenInstPostBetaMatrixDef where

-- File Charter:
--   * Defines the four incoming/final paired/source-only semantic cells after
--     target instantiation has stepped to runtime `ν ★`.
--   * Retains two flat row boundaries and the existing generic post-beta
--     theorem so exhaustive index dispatch can be checked independently.
--   * Adds no result, view, outcome, record, postulate, hole, option,
--     compatibility layer, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; ModeEnv; instᵈ)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Imprecision using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  )
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; ∀ⁱ_; ν)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; ν)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; ★; occurs; `∀; ⟰ᵗ; ⇑ᵗ)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightTargetWidenInstPostBetaSourceOnlyFromPairedᵀ :
  Set₁
WorldCoherentRightTargetWidenInstPostBetaSourceOnlyFromPairedᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {safe : NonVar D}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ B ⊣ Δᴿ}
    {occ : occurs zero D ≡ true} →
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
    ⊢ᴺ V ⊑ V′ ⦂ `∀ D ⊑ `∀ C ∶ ∀ⁱ r →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = ν ★ V′ s} {ρ = ρ}
    (ν safe occ q)


WorldCoherentRightTargetWidenInstPostBetaSourceOnlyFromSourceOnlyᵀ :
  Set₁
WorldCoherentRightTargetWidenInstPostBetaSourceOnlyFromSourceOnlyᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {safeₚ safeq : NonVar D}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ `∀ C ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ B ⊣ Δᴿ}
    {occₚ occq : occurs zero D ≡ true} →
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
    ⊢ᴺ V ⊑ V′ ⦂ `∀ D ⊑ `∀ C ∶ ν safeₚ occₚ r →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = ν ★ V′ s} {ρ = ρ}
    (ν safeq occq q)


WorldCoherentRightTargetWidenInstPostBetaSourceOnlyᵀ : Set₁
WorldCoherentRightTargetWidenInstPostBetaSourceOnlyᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {{safe : NonVar D}}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ B ⊣ Δᴿ}
    {occ : occurs zero D ≡ true} →
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
    ⊢ᴺ V ⊑ V′ ⦂ `∀ D ⊑ `∀ C ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = ν ★ V′ s} {ρ = ρ}
    (ν safe occ q)


WorldCoherentRightTargetWidenInstPostBetaPairedFromPairedᵀ : Set₁
WorldCoherentRightTargetWidenInstPostBetaPairedFromPairedᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {C D E : Ty} {s : Coercion} {μ : ModeEnv}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ E ⊣ suc Δᴿ} →
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
    ⊢ s ∶ C ⊑ ⇑ᵗ (`∀ E) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ D ⊑ `∀ C ∶ ∀ⁱ r →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = ν ★ V′ s} {ρ = ρ}
    (∀ⁱ q)


WorldCoherentRightTargetWidenInstPostBetaPairedFromSourceOnlyᵀ :
  Set₁
WorldCoherentRightTargetWidenInstPostBetaPairedFromSourceOnlyᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {C D E : Ty} {s : Coercion} {μ : ModeEnv}
    {safe : NonVar D}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ `∀ C ⊣ Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ E ⊣ suc Δᴿ}
    {occ : occurs zero D ≡ true} →
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
    ⊢ s ∶ C ⊑ ⇑ᵗ (`∀ E) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ D ⊑ `∀ C ∶ ν safe occ r →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = ν ★ V′ s} {ρ = ρ}
    (∀ⁱ q)


WorldCoherentRightTargetWidenInstPostBetaPairedᵀ : Set₁
WorldCoherentRightTargetWidenInstPostBetaPairedᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {C D E : Ty} {s : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C ⊣ Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ E ⊣ suc Δᴿ} →
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
    ⊢ s ∶ C ⊑ ⇑ᵗ (`∀ E) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ D ⊑ `∀ C ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = ν ★ V′ s} {ρ = ρ}
    (∀ⁱ q)
