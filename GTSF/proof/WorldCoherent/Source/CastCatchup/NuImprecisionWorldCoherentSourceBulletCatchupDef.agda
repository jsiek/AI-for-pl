module proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceBulletCatchupDef where

-- File Charter:
--   * Defines coherent catch-up for the source-only post-allocation bullet.
--   * Isolates reconstruction of the allocated relation from the recursive
--     target-value dispatcher and the enclosing `ν` handlers.
--   * Contains no implementation or permissive proof dependency.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( NonVar
  ; ImpCtx
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImpEntry
  ; LiftLeftCtxⁱ
  ; leftCtxⁱ
  ; rightCtxⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; ⇑ᵗᵐ; _•)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  (Ty; TyCtx; WfTy; `∀; ⇑ᵗ; occurs)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentSourceBulletCatchupᵀ : Set₁
WorldCoherentSourceBulletCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ ρ⁺ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {L V′ : Term} {A B′ C : Ty}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {{safe : NonVar C}}
    {occ : occurs zero C ≡ true} →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  StoreImpPrefix
    (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′) ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
  AssumptionMembershipUnique ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
  StoreWf (suc Δᴸ) (leftStoreⁱ ρ⁺) →
  RuntimeOK ((⇑ᵗᵐ L) •) →
  Value V′ →
  No• V′ →
  Value L →
  No• L →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
    ([] {A = CtxImpEntry
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ V′ ⦂ `∀ C ⊑ B′ ∶ ν safe occ p →
  suc Δᴸ
    ∣ leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
    ∣ leftCtxⁱ ([] {A = CtxImpEntry
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ})
    ⊢ (⇑ᵗᵐ L) • ⦂ C →
  Δᴿ
    ∣ rightStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
    ∣ rightCtxⁱ ([] {A = CtxImpEntry
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ})
    ⊢ V′ ⦂ B′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = (⇑ᵗᵐ L) •} {V′ = V′} {ρ = ρ⁺} p
