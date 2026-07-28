module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupDef
  where

-- File Charter:
--   * Defines exactly the proven admissible source-widen catch-up cases:
--     inert, atomic identity, sequence, and source-only `ν` instantiation.
--   * Exposes a case capability record instead of treating arbitrary-index
--     source widening as one indivisible leaf.
--   * Contains no implementation, compatibility alias, postulate, or hole.

open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion; Inert; ModeEnv; _︔_)
import Coercions as C
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
open import NarrowWiden using
  ( Widening
  ; _∣_∣_⊢_∶_⊑_
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using
  ( Atom
  ; Ty
  ; TyCtx
  ; occurs
  ; `∀
  )
open import
  proof.Source.CastSequence.NuImprecisionSourceCastSequenceMidpointDef
  using (SourceCastSequenceMidpointᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentLeftCatchupIndexedResult)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef
  using (WorldCoherentLeftValueCatchupPrefixᵀ)


WorldCoherentSourceInertWidenCatchupᵀ : Set₁
WorldCoherentSourceInertWidenCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ : Term} {A B B′ : Ty} {c : Coercion}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {s : ImprecisionShape} →
  Inert c →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q


WorldCoherentSourceIdentityWidenCatchupᵀ : Set₁
WorldCoherentSourceIdentityWidenCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ : Term} {A B′ : Ty}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {s : ImprecisionShape} →
  Atom A →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ C.id A ∶ A ⊑ A →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ C.id A ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ C.id A ⟩} {V′ = V′} {ρ = ρ⁺} q


WorldCoherentSourceSequenceWidenCatchupᵀ : Set₁
WorldCoherentSourceSequenceWidenCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ : Term} {A C B B′ : Ty} {s t : Coercion}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {sequence-shape : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ s ∶ A ⊑ C →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ t ∶ C ⊑ B →
  Widening (s ︔ t) →
  Value V′ →
  No• V′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ s ︔ t ⦂ sequence-shape →
  sequence-shape ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ s ︔ t ⟩} {V′ = V′} {ρ = ρ⁺} q


WorldCoherentSourceNuIndexedInstantiationWidenCatchupᵀ : Set₁
WorldCoherentSourceNuIndexedInstantiationWidenCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ : Term} {A B B′ : Ty} {c : Coercion}
    {μ : ModeEnv} {s : ImprecisionShape}
    {index-occ : occurs zero A ≡ true}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  {{safe : NonVar A}} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ C.inst B c ∶ `∀ A ⊑ B →
  Value V′ →
  No• V′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺}
    (ν safe index-occ r) →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ C.inst B c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ ν safe index-occ r ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ C.inst B c ⟩} {V′ = V′} {ρ = ρ⁺} q


record WorldCoherentSourceWidenCatchupCasesᵀ : Set₁ where
  field
    inert-widen : WorldCoherentSourceInertWidenCatchupᵀ
    identity-widen : WorldCoherentSourceIdentityWidenCatchupᵀ
    sequence-widen :
      SourceCastSequenceMidpointᵀ →
      WorldCoherentLeftValueCatchupPrefixᵀ →
      WorldCoherentSourceSequenceWidenCatchupᵀ
    ν-inst-widen :
      WorldCoherentLeftValueCatchupPrefixᵀ →
      WorldCoherentSourceNuIndexedInstantiationWidenCatchupᵀ


open WorldCoherentSourceWidenCatchupCasesᵀ public
