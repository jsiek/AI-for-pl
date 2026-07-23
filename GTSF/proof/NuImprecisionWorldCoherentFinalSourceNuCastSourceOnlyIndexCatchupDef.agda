module
  proof.NuImprecisionWorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupDef
  where

-- File Charter:
--   * Defines exact-final source-`ν ★` catch-up for the source-only inner
--     universal precision index.
--   * Keeps the runtime allocation cast and complete world premises visible.
--   * Contains no implementation, recursive dispatcher, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; ModeEnv; instᵈ)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ) renaming (ν to νⁱ)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; Term; Value; ν)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; ★; `∀; ⇑ᵗ; ⟰ᵗ; occurs)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupᵀ : Set₁
WorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L V′ : Term} {B B′ C : Ty} {s : Coercion}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {{safe : NonVar C}}
    {occ : occurs zero C ≡ true} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  Value L →
  No• L →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ V′ ⦂ `∀ C ⊑ B′ ∶ νⁱ safe occ r →
  WorldCoherentLeftCatchupIndexedResult
    {N = ν ★ L s} {V′ = V′} {ρ = ρ} p
