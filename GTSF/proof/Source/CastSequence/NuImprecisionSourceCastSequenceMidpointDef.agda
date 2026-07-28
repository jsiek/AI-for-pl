module proof.Source.CastSequence.NuImprecisionSourceCastSequenceMidpointDef where

-- File Charter:
--   * Defines source-side midpoint recovery for narrowing and widening
--     coercion sequences.
--   * Exposes the exact ambient-prefix world invariants available to the
--     source-runtime catch-up handlers.
--   * Contains no implementation or recursive catch-up dependency.

open import Coercions using
  ( Coercion
  ; ModeEnv
  ; _︔_
  ; _∣_∣_⊢_∶_=⇒_
  )
open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Data.Product using (_×_; Σ-syntax)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using
  ( Narrowing
  ; Widening
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  )
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


record SourceCastSequenceMidpointᵀ : Set₁ where
  field
    narrowing-midpoint :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {A C B B′ : Ty} {s t : Coercion} {μ : ModeEnv} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ s ∶ A =⇒ C →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ t ∶ C =⇒ B →
      Narrowing (s ︔ t) →
      Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ →
      Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
      Φ ∣ Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ

    widening-midpoint :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {A C B B′ : Ty} {s t : Coercion} {μ : ModeEnv}
        {s-shape t-shape sequence-shape : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ s ∶ A =⇒ C →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ t ∶ C =⇒ B →
      Widening (s ︔ t) →
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      widening ⊢ᶜ s ⦂ s-shape →
      widening ⊢ᶜ t ⦂ t-shape →
      s-shape ； t-shape ≋ sequence-shape →
      sequence-shape ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
      Σ[ middle ∈ (Φ ∣ Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ) ]
        (s-shape ； ⌊ middle ⌋ ≋ ⌊ p ⌋) ×
        (t-shape ； ⌊ q ⌋ ≋ ⌊ middle ⌋)

open SourceCastSequenceMidpointᵀ public
