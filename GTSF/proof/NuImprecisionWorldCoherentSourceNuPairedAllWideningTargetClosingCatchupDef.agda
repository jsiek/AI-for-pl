module
  proof.NuImprecisionWorldCoherentSourceNuPairedAllWideningTargetClosingCatchupDef
  where

-- File Charter:
--   * Defines coherent post-allocation target closing for paired universal
--     widening on source-`ν` `av-∀`/`av-∀` values.
--   * Retains both endpoint typings and paired-widening compatibility because
--     no intermediate one-sided type relation exists in general.
--   * Contains no implementation, dispatcher, or permissive option.

open import Coercions using (Coercion; ModeEnv; `∀)
open import Conversion using (RevealConversion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; WfTy; `∀; ⇑ᵗ)
open import proof.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentSourceNuPairedAllWideningTargetClosingCatchupᵀ : Set₁
WorldCoherentSourceNuPairedAllWideningTargetClosingCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {V V′ : Term} {A B C C′ D D′ : Ty}
    {c c′ s : Coercion} {μ η η′ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ D′ ⊣ suc Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  WfTy Δᴸ A →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴸ)
    (leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρν))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  CastMode η →
  SealModeStore★ η (leftStoreⁱ ρ) →
  η ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ D ⊑ `∀ C →
  CastMode η′ →
  SealModeStore★ η′ (rightStoreⁱ ρ) →
  η′ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ D′ ⊑ `∀ C′ →
  PairedWideningCompatible Φ Δᴸ Δᴿ
    (`∀ c) (`∀ c′) (`∀ C) (`∀ D′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ D ⊑ `∀ D′ ∶ ∀ⁱ r →
  WorldCoherentLeftCatchupIndexedResult
    {N = ((⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •) ⟨ s ⟩}
    {V′ = V′ ⟨ `∀ c′ ⟩}
    {ρ = store-left zero (⇑ᵗ A) h⇑A ∷ ρν}
    (⊑-source-liftνᵢ p)
