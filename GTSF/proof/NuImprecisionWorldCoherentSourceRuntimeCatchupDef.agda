module proof.NuImprecisionWorldCoherentSourceRuntimeCatchupDef where

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
open import Coercions using (Coercion; ModeEnv; instᵈ)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


record WorldCoherentSourceRuntimeCatchupᵀ : Set₁ where
  field
    source-bullet :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ ρ⁺ : StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {L V′ : Term} {A B′ C : Ty}
        {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
        {occ : occurs zero C ≡ true} →
      (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
      StoreImpPrefix
        (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′) ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
      StoreWf (suc Δᴸ) (leftStoreⁱ ρ⁺) →
      RuntimeOK ((⇑ᵗᵐ L) •) →
      Value V′ →
      No• V′ →
      Value L →
      No• L →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
        ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ L ⊑ V′ ⦂ `∀ C ⊑ B′ ∶ ν occ p →
      suc Δᴸ
        ∣ leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
        ∣ leftCtxⁱ ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ})
        ⊢ (⇑ᵗᵐ L) • ⦂ C →
      Δᴿ
        ∣ rightStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
        ∣ rightCtxⁱ ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ})
        ⊢ V′ ⦂ B′ →
      WorldCoherentLeftCatchupIndexedResult
        {N = (⇑ᵗᵐ L) •} {V′ = V′} {ρ = ρ⁺} p

    source-ν :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {N V′ : Term} {A B B′ C : Ty} {s : Coercion}
        {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WfTy Δᴸ A →
      WfTy (suc Δᴸ) (⇑ᵗ A) →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ′ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
        ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
      Value V′ →
      No• V′ →
      WorldCoherentLeftCatchupIndexedResult
        {N = N} {V′ = V′} {ρ = ρ⁺} q →
      WorldCoherentLeftCatchupIndexedResult
        {N = ν A N s} {V′ = V′} {ρ = ρ⁺} p

    source-νcast :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {N V′ : Term} {B B′ C : Ty} {s : Coercion}
        {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)) →
      instᵈ μ ∣ suc Δᴸ
        ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)
        ⊢ s ∶ C ⊑ ⇑ᵗ B →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ′ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
        ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
      Value V′ →
      No• V′ →
      WorldCoherentLeftCatchupIndexedResult
        {N = N} {V′ = V′} {ρ = ρ⁺} q →
      WorldCoherentLeftCatchupIndexedResult
        {N = ν ★ N s} {V′ = V′} {ρ = ρ⁺} p

    source-narrow :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ : Term} {A B B′ : Ty} {c : Coercion}
        {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊒ B →
      Value V′ →
      No• V′ →
      WorldCoherentLeftCatchupIndexedResult
        {N = N} {V′ = V′} {ρ = ρ⁺} p →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      WorldCoherentLeftCatchupIndexedResult
        {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q

    source-widen :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ : Term} {A B B′ : Ty} {c : Coercion}
        {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
      Value V′ →
      No• V′ →
      WorldCoherentLeftCatchupIndexedResult
        {N = N} {V′ = V′} {ρ = ρ⁺} p →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      WorldCoherentLeftCatchupIndexedResult
        {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q

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
