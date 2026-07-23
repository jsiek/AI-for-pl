module
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastPairedIndexViewCatchupDef
  where

-- File Charter:
--   * Defines the paired-index source-`ν ★` worker after both polymorphic
--     endpoints have been classified by canonical forms.
--   * Isolates the unresolved one-sided-allocation `AllView` cross-product.
--   * Contains no implementation, recursive dispatcher, or permissive option.

open import Coercions using (Coercion; ModeEnv; instᵈ)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; Term; Value; ν)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)
open import proof.DGG.Core.NuProgress using (AllView)


WorldCoherentFinalSourceNuCastPairedIndexViewCatchupᵀ : Set₁
WorldCoherentFinalSourceNuCastPairedIndexViewCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L V′ : Term} {B C C′ : Ty} {s : Coercion}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
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
  AllView L →
  AllView V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ r →
  WorldCoherentLeftCatchupIndexedResult
    {N = ν ★ L s} {V′ = V′} {ρ = ρ} p
