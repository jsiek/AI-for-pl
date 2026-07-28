module
  proof.Right.SourceAll.Frames.NuImprecisionRightSourceAllPairedWideningDef
  where

-- File Charter:
--   * Defines the direct paired-widening semantic case beneath
--     source-universal right-value closing.
--   * Exposes the reduction-closed compatibility invariant introduced by
--     the live QTI constructor.
--   * Contains no implementation, dispatcher, result/view/outcome type,
--     postulate, hole, permissive option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion; Inert; ModeEnv)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Imprecision using (NonVar)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _∣_⊢_⊑_⊣_; ⇑ᴸᵢ)
import ImprecisionWf as IW
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; Λ_; _⟨_⟩)
open import QuotientImprecisionCompatibility using
  (ReductionClosedPairedWideningCompatible)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
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


WorldCoherentRightSourceAllPairedWideningᵀ : Set₁
WorldCoherentRightSourceAllPairedWideningᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {M M′ : Term} {A A′ B B′ : Ty}
    {c c′ : Coercion} {μ μ′ : ModeEnv}
    {s s′ r : ImprecisionShape}
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
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρᴸ) →
  μ ∣ suc Δᴸ ∣ leftStoreⁱ ρᴸ ⊢ c ∶ A ⊑ B →
  widening ⊢ᶜ c ⦂ s →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρᴸ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᴸ ⊢ c′ ∶ A′ ⊑ B′ →
  widening ⊢ᶜ c′ ⦂ s′ →
  s ； ⌊ q ⌋ ≋ r →
  ⌊ p ⌋ ； s′ ≋ r →
  ReductionClosedPairedWideningCompatible
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ
    c c′ p q s s′ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = Λ (M ⟨ c ⟩)} {M′ = M′ ⟨ c′ ⟩}
    {ρ = ρ⁺} (IW.ν safe occ q)
