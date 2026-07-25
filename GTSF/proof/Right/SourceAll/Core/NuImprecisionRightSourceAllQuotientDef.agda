module
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllQuotientDef
  where

-- File Charter:
--   * Defines the quotient down/up semantic case beneath source-universal
--     right-value closing.
--   * Contains no implementation, dispatcher, result/view/outcome type,
--     postulate, hole, permissive option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Imprecision using (NonVar)
open import ImprecisionComposition using
  (ImprecisionShape; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _∣_⊢_⊑_⊣_; ⇑ᴸᵢ)
import ImprecisionWf as IW
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; Λ_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
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


WorldCoherentRightSourceAllQuotientᵀ : Set₁
WorldCoherentRightSourceAllQuotientᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {N N′ : Term} {D D′ A A′ : Ty}
    {u u′ : Coercion}
    {sU sU′ : ImprecisionShape}
    {{safe : NonVar A}}
    {qD : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {occ : occurs zero A ≡ true} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (N′ ⟨ u′ ⟩) →
  Value (N ⟨ u ⟩) →
  No• (N ⟨ u ⟩) →
  LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
  LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
    ⊢ᴺᵖ N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair
    (suc Δᴸ) Δᴿ ρᴸ u u′ D D′ A A′ →
  widening ⊢ᶜ u ⦂ sU →
  widening ⊢ᶜ u′ ⦂ sU′ →
  sU ；⌊ pA ⌋≋ᵖ qD ； sU′ →
  WorldCoherentRightValueCatchupIndexedResult
    {V = Λ (N ⟨ u ⟩)} {M′ = N′ ⟨ u′ ⟩}
    {ρ = ρ⁺} (IW.ν safe occ pA)
