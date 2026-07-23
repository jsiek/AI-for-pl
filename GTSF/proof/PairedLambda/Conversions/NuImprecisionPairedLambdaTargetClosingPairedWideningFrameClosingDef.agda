module
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameClosingDef
  where

-- File Charter:
--   * Defines fused target closing through one outer paired-widening frame.
--   * Retains the recursively closed inner result expanded inline, the exact
--     proof-relevant frame view, both cast/seal modes, both widening typings,
--     paired-widening compatibility, the external paired conversion, both
--     allocation lifts, and the final structural reveal interaction.
--   * Exposes no one-sided coercion-order intermediate.
--   * Contains no handler import, implementation, postulate, hole,
--     permissive option, recursive frame-closing dependency, or broad
--     simulation import.

import Coercions as C
open import Coercions using (Coercion; Inert; ModeEnv)
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
open import NuTerms using (Term; ⇑ᵗᵐ; _•; _⟨_⟩)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  ( PairedConversion
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; extᵗ
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


PairedLambdaTargetClosingPairedWideningFrameClosingᵀ : Set₁
PairedLambdaTargetClosingPairedWideningFrameClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ C′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
    {d d′ : Coercion} {μ μ′ : ModeEnv} →
  (∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
      {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {A C₀′ D E : Ty} {c c′ t : Coercion} {ν : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C₀′ ⊣ Δᴿ}
      {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ `∀ E ⊑ C₀′ ⊣ suc Δᴿ} →
    StoreImpPrefix ρ₀ ρ →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
    RevealConversion (C.extᵈ ν) (suc (suc Δᴸ))
      (⟰ᵗ (leftStoreⁱ
        (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
      (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
      (renameᵗ (extᵗ suc) D) →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
    PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
      {`∀ B} {B′} {`∀ (`∀ E)} {`∀ C₀′} q (∀ⁱ s) →
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣
        store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
      ⊢ᴺ (((⇑ᵗᵐ W) •) ⟨ c ⟩) ⟨ C.`∀ t ⟩
        ⊑ W′ ⟨ c′ ⟩
        ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C₀′ ∶ ⊑-source-liftνᵢ p) →
  PairedLambdaTargetClosingFrameView ρ₀
    W W′ (`∀ B) B′ q →
  Inert d′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ C.`∀ d ∶ `∀ B ⊑ `∀ C →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ d′ ∶ B′ ⊑ C′ →
  PairedWideningCompatible Φ Δᴸ Δᴿ
    (C.`∀ d) d′ (`∀ C) B′ →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {A C₀′ D E : Ty} {c c′ t : Coercion} {ν : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C₀′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C₀′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion (C.extᵈ ν) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ C} {C′} {`∀ (`∀ E)} {`∀ C₀′} r (∀ⁱ s) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ
      (((⇑ᵗᵐ (W ⟨ C.`∀ d ⟩)) •) ⟨ c ⟩)
        ⟨ C.`∀ t ⟩
      ⊑ (W′ ⟨ d′ ⟩) ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C₀′ ∶ ⊑-source-liftνᵢ p
