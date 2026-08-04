module
  proof.Right.SourceAll.Frames.NuImprecisionRightSourceAllPairedConcealDef
  where

-- File Charter:
--   * Defines the direct paired-conceal semantic case beneath
--     source-universal right-value closing.
--   * States the live QTI constructor premises directly, without a
--     compatibility wrapper or retired paired-cast carrier.
--   * Contains no implementation, dispatcher, result/view/outcome type,
--     postulate, hole, permissive option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; Inert)
open import Conversion using (ConcealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
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
  ; StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
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


WorldCoherentRightSourceAllPairedConcealᵀ : Set₁
WorldCoherentRightSourceAllPairedConcealᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {M M′ : Term} {A A′ B B′ X X′ : Ty}
    {c c′ : Coercion} {α β pX μ μ′}
    {{safe : NonVar B}}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {occ : occurs zero B ≡ true} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ c′ ⟩) →
  Value M →
  No• M →
  Inert c →
  LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
  LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
  StoreCorresponds ρᴸ α X β X′ pX →
  ConcealConversion μ (suc Δᴸ) (leftStoreⁱ ρᴸ)
    α X c A B →
  ConcealConversion μ′ Δᴿ (rightStoreⁱ ρᴸ)
    β X′ c′ A′ B′ →
  q [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ p →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = Λ (M ⟨ c ⟩)} {M′ = M′ ⟨ c′ ⟩}
    {ρ = ρ⁺} (IW.ν safe occ q)
