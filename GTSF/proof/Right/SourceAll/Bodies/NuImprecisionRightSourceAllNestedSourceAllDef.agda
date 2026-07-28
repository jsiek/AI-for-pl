module
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllNestedSourceAllDef
  where

-- File Charter:
--   * Defines nested source-only universal closing beneath an outer
--     source-universal right-value closing boundary.
--   * Contains no implementation, dispatcher, result/view/outcome type,
--     postulate, hole, permissive option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
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
  ( CtxImp
  ; LiftLeftCtxⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; Λ_)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx; occurs; `∀)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightSourceAllNestedSourceAllᵀ : Set₁
WorldCoherentRightSourceAllNestedSourceAllᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρᴸᴸ : StoreImp
      ((zero ˣ⊑★) ∷
        ⇑ᴸᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      (suc (suc Δᴸ)) Δᴿ}
    {γᴸᴸ : CtxImp
      ((zero ˣ⊑★) ∷
        ⇑ᴸᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      (suc (suc Δᴸ)) Δᴿ}
    {U N′ : Term} {C B : Ty}
    {{innerSafe : NonVar C}}
    {{outerSafe : NonVar (`∀ C)}}
    {p : ((zero ˣ⊑★) ∷
        ⇑ᴸᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      ∣ suc (suc Δᴸ) ⊢ C ⊑ B ⊣ Δᴿ}
    {innerOcc : occurs zero C ≡ true}
    {outerOcc : occurs zero (`∀ C) ≡ true} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK N′ →
  Value U →
  No• U →
  LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
  LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
  LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷
      ⇑ᴸᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
    ρᴸ ρᴸᴸ →
  LiftLeftCtxⁱ
    {Φ = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ}
    {Δᴸ = suc Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑★) ∷
      ⇑ᴸᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
    [] γᴸᴸ →
  ((zero ˣ⊑★) ∷
      ⇑ᴸᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
    ∣ suc (suc Δᴸ) ∣ Δᴿ ∣ ρᴸᴸ ∣ γᴸᴸ
    ⊢ᴺ U ⊑ N′ ⦂ C ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = Λ (Λ U)} {M′ = N′} {ρ = ρ⁺}
    (IW.ν outerSafe outerOcc
      (IW.ν innerSafe innerOcc p))
