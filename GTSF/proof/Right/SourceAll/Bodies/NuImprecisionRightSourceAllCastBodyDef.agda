module
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllCastBodyDef
  where

-- File Charter:
--   * Defines source-universal right-value closing when the body source is an
--     inert cast of a value.
--   * Keeps the lifted source-only world and exact body QTI relation explicit.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, compatibility re-export, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; Inert)
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
  ( LiftLeftCtxⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; Λ_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx; occurs)
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


WorldCoherentRightSourceAllCastBodyᵀ : Set₁
WorldCoherentRightSourceAllCastBodyᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {M N′ : Term} {A B : Ty} {c : Coercion}
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
  Value M →
  No• M →
  Inert c →
  LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
  LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
    ⊢ᴺ M ⟨ c ⟩ ⊑ N′ ⦂ A ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = Λ (M ⟨ c ⟩)} {M′ = N′} {ρ = ρ⁺}
    (IW.ν safe occ p)
