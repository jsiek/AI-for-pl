module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationRootDef
  where

-- File Charter:
--   * Defines the flat target-instantiation root and the two reachable
--     incoming/source-only-final universal type-index cases.
--   * Retains the outer cast shape and composition triangle through both
--     reachable cells, so a paired final index can be rejected by structural
--     inversion and the source-only body square remains available.
--   * Returns the existing complete right-value catch-up carrier and adds no
--     result, view, outcome, postulate, hole, option, or bypass.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)

open import CastImprecisionShape using (widening; _⊢ᶜ_⦂_)
open import Coercions using (Coercion; ModeEnv; inst)
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
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; occurs; `∀)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (WorldCoherentRightTargetAllocationFrames)


WorldCoherentRightTargetWidenInstantiationSourceOnlyFromPairedRootᵀ :
  Set₁
WorldCoherentRightTargetWidenInstantiationSourceOnlyFromPairedRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {shape : ImprecisionShape}
    {safe : NonVar D}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ B ⊣ Δᴿ}
    {occ : occurs zero D ≡ true} →
  WorldCoherentRightTargetAllocationFrames →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ inst B s ⟩) →
  Value V →
  No• V →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst B s ∶ `∀ C ⊑ B →
  widening ⊢ᶜ inst B s ⦂ shape →
  ⌊ ∀ⁱ r ⌋ ； shape ≋ ⌊ ν safe occ q ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ `∀ D ⊑ `∀ C ∶ ∀ⁱ r →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} (∀ⁱ r) →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ inst B s ⟩} {ρ = ρ⁺}
    (ν safe occ q)


WorldCoherentRightTargetWidenInstantiationSourceOnlyFromSourceOnlyRootᵀ :
  Set₁
WorldCoherentRightTargetWidenInstantiationSourceOnlyFromSourceOnlyRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {shape : ImprecisionShape}
    {safeₚ safeq : NonVar D}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ `∀ C ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ B ⊣ Δᴿ}
    {occₚ occq : occurs zero D ≡ true} →
  WorldCoherentRightTargetAllocationFrames →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ inst B s ⟩) →
  Value V →
  No• V →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst B s ∶ `∀ C ⊑ B →
  widening ⊢ᶜ inst B s ⦂ shape →
  ⌊ ν safeₚ occₚ r ⌋ ； shape ≋ ⌊ ν safeq occq q ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ `∀ D ⊑ `∀ C ∶ ν safeₚ occₚ r →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} (ν safeₚ occₚ r) →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ inst B s ⟩} {ρ = ρ⁺}
    (ν safeq occq q)


WorldCoherentRightTargetWidenInstantiationSourceOnlyRootᵀ : Set₁
WorldCoherentRightTargetWidenInstantiationSourceOnlyRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {shape : ImprecisionShape}
    {{safe : NonVar D}}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ B ⊣ Δᴿ}
    {occ : occurs zero D ≡ true} →
  WorldCoherentRightTargetAllocationFrames →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ inst B s ⟩) →
  Value V →
  No• V →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst B s ∶ `∀ C ⊑ B →
  widening ⊢ᶜ inst B s ⦂ shape →
  ⌊ p ⌋ ； shape ≋ ⌊ ν safe occ q ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ `∀ D ⊑ `∀ C ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ inst B s ⟩} {ρ = ρ⁺}
    (ν safe occ q)


WorldCoherentRightTargetWidenInstantiationRootᵀ : Set₁
WorldCoherentRightTargetWidenInstantiationRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B C : Ty} {s : Coercion} {μ : ModeEnv}
    {shape : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherentRightTargetAllocationFrames →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ inst B s ⟩) →
  Value V →
  No• V →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst B s ∶ `∀ C ⊑ B →
  widening ⊢ᶜ inst B s ⦂ shape →
  ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ `∀ C ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ inst B s ⟩} {ρ = ρ⁺} q
