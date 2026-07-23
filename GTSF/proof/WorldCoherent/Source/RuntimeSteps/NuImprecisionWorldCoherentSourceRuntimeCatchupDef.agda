module proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceRuntimeCatchupDef where

-- File Charter:
--   * Defines the eight source-runtime branches required by the
--     world-coherent target-value catch-up recursion.
--   * Keeps the exceptional runtime-bullet branch explicit and factors the
--     other source forms as coherent catch-up frames.
--   * Contains no implementation and imports only statement-level support.

open import Agda.Builtin.Equality using (_≡_)
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  ( CtxImpEntry
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuStore using (StoreWf)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  ; ν
  )
open import QuotientedTermImprecision using
  ( PairedCast
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; TyVar
  ; WfTy
  ; ★
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  ; occurs
  )
open import Coercions using (Coercion; Inert; ModeEnv; instᵈ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)
open import proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceNarrowCatchupDef using
  (WorldCoherentSourceNarrowCatchupᵀ)
open import proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupDef using
  (WorldCoherentSourceWidenCatchupᵀ)
open import proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceBulletCatchupDef using
  (WorldCoherentSourceBulletCatchupᵀ)
open import proof.WorldCoherent.Source.NuCatchup.NuImprecisionWorldCoherentSourceNuCatchupDef using
  (WorldCoherentSourceNuCatchupᵀ)
open import proof.WorldCoherent.Source.NuCatchup.NuImprecisionWorldCoherentSourceNuCastCatchupDef using
  (WorldCoherentSourceNuCastCatchupᵀ)


record WorldCoherentSourceRuntimeCatchupᵀ : Set₁ where
  field
    source-bullet : WorldCoherentSourceBulletCatchupᵀ

    source-ν : WorldCoherentSourceNuCatchupᵀ

    source-νcast : WorldCoherentSourceNuCastCatchupᵀ

    source-narrow : WorldCoherentSourceNarrowCatchupᵀ

    source-widen : WorldCoherentSourceWidenCatchupᵀ

    source-paired-cast :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ : Term} {A A′ B B′ : Ty} {c c′ : Coercion}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      PairedCast Φ Δᴸ Δᴿ ρ₀
        c c′ {A} {A′} {B} {B′} p q →
      Value V′ →
      No• V′ →
      Inert c′ →
      WorldCoherentLeftCatchupIndexedResult
        {N = N} {V′ = V′} {ρ = ρ⁺} p →
      WorldCoherentLeftCatchupIndexedResult
        {N = N ⟨ c ⟩} {V′ = V′ ⟨ c′ ⟩} {ρ = ρ⁺} q

    source-reveal :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ : Term} {A B B′ X : Ty} {c : Coercion}
        {μ : ModeEnv} {α : TyVar}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      Value V′ →
      No• V′ →
      WorldCoherentLeftCatchupIndexedResult
        {N = N} {V′ = V′} {ρ = ρ⁺} p →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      WorldCoherentLeftCatchupIndexedResult
        {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q

    source-conceal :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ : Term} {A B B′ X : Ty} {c : Coercion}
        {μ : ModeEnv} {α : TyVar}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      Value V′ →
      No• V′ →
      WorldCoherentLeftCatchupIndexedResult
        {N = N} {V′ = V′} {ρ = ρ⁺} p →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      WorldCoherentLeftCatchupIndexedResult
        {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q

open WorldCoherentSourceRuntimeCatchupᵀ public
