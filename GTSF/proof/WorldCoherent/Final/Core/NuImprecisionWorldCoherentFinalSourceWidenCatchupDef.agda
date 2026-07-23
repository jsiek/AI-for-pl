module
  proof.WorldCoherent.Final.Core.NuImprecisionWorldCoherentFinalSourceWidenCatchupDef
  where

-- File Charter:
--   * Defines exact-world terminal catch-up for one source widening cast.
--   * Makes active instantiation an explicit semantic boundary rather than
--     hiding it in accumulated-change framing or a permissive dispatcher.
--   * Contains no implementation or permissive proof dependency.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; ModeEnv)
open import Data.List using ([])
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ)
open import NuTerms using
  (No•; Term; Value; blame; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentFinalSourceWidenCatchupᵀ : Set₁
WorldCoherentFinalSourceWidenCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W V′ : Term} {A B B′ : Ty} {c : Coercion}
    {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  ((Value W × No• W) ⊎ (W ≡ blame)) →
  Value V′ →
  No• V′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ A ⊑ B′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
    {N = W ⟨ c ⟩} {V′ = V′} {ρ = ρ} q
