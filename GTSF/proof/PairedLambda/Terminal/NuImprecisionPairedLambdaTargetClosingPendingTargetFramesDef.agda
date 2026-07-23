module
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  where

-- File Charter:
--   * Defines the proof-relevant continuation of pending store prefixes and
--     target-only frames for paired-lambda target closing.
--   * Keeps the source term and source universal type fixed while recording
--     every target endpoint, precision index, and relational-store world.
--   * Defines the continuation-indexed closing motive; its reflexive
--     continuation recovers the existing public closing motive exactly.
--   * Contains no interpreter, semantic handler, implementation, postulate,
--     hole, permissive option, or broad simulation import.

open import Coercions using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; id-onlyᵈ
  )
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using (Ty; TyCtx; TyVar; `∀)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)


data PairedLambdaTargetClosingPendingTargetFrames
    { Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} :
    (ρ₀ : StoreImp Φ Δᴸ Δᴿ) →
    (W W′ : Term) → (F B′ : Ty) →
    (q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ) →
    (ρ⁺ : StoreImp Φ Δᴸ Δᴿ) →
    (W⁺ : Term) → (C′ : Ty) →
    (r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C′ ⊣ Δᴿ) → Set₁ where

  pending-refl :
    ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
      {W W′ : Term} {F B′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ} →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ W W′ F B′ q ρ W′ B′ q

  pending-prefix :
    ∀ {ρ₀ ρ₁ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {W W′ W⁺ : Term} {F B′ C′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C′ ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ₁ →
    Δᴸ ∣ leftStoreⁱ ρ₁ ∣ [] ⊢ W ⦂ `∀ F →
    Δᴿ ∣ rightStoreⁱ ρ₁ ∣ [] ⊢ W′ ⦂ B′ →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₁ W W′ F B′ q ρ⁺ W⁺ C′ r →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W W′ F B′ q ρ⁺ W⁺ C′ r

  pending-⊑cast⊒ :
    ∀ {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {W W′ W⁺ : Term} {F B′ C′ D′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C′ ⊣ Δᴿ}
      {s : Φ ∣ Δᴸ ⊢ `∀ F ⊑ D′ ⊣ Δᴿ}
      {c′ : Coercion} {μ′ : ModeEnv} →
    Inert c′ →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ B′ ⊒ C′ →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W (W′ ⟨ c′ ⟩) F C′ r ρ⁺ W⁺ D′ s →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W W′ F B′ q ρ⁺ W⁺ D′ s

  pending-⊑cast⊑ :
    ∀ {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {W W′ W⁺ : Term} {F B′ C′ D′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C′ ⊣ Δᴿ}
      {s : Φ ∣ Δᴸ ⊢ `∀ F ⊑ D′ ⊣ Δᴿ}
      {c′ : Coercion} {μ′ : ModeEnv} →
    Inert c′ →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ B′ ⊑ C′ →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W (W′ ⟨ c′ ⟩) F C′ r ρ⁺ W⁺ D′ s →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W W′ F B′ q ρ⁺ W⁺ D′ s

  pending-⊑cast⊑id :
    ∀ {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {W W′ W⁺ : Term} {F B′ C′ D′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C′ ⊣ Δᴿ}
      {s : Φ ∣ Δᴸ ⊢ `∀ F ⊑ D′ ⊣ Δᴿ}
      {c′ : Coercion} →
    Inert c′ →
    SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ B′ ⊑ C′ →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W (W′ ⟨ c′ ⟩) F C′ r ρ⁺ W⁺ D′ s →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W W′ F B′ q ρ⁺ W⁺ D′ s

  pending-⊑conv↑ :
    ∀ {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {W W′ W⁺ : Term} {F B′ C′ D′ X′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C′ ⊣ Δᴿ}
      {s : Φ ∣ Δᴸ ⊢ `∀ F ⊑ D′ ⊣ Δᴿ}
      {c′ : Coercion} {η′ : ModeEnv} {β : TyVar} →
    Inert c′ →
    RevealConversion η′ Δᴿ (rightStoreⁱ ρ₀)
      β X′ c′ B′ C′ →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W (W′ ⟨ c′ ⟩) F C′ r ρ⁺ W⁺ D′ s →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W W′ F B′ q ρ⁺ W⁺ D′ s

  pending-⊑conv↓ :
    ∀ {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {W W′ W⁺ : Term} {F B′ C′ D′ X′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C′ ⊣ Δᴿ}
      {s : Φ ∣ Δᴸ ⊢ `∀ F ⊑ D′ ⊣ Δᴿ}
      {c′ : Coercion} {η′ : ModeEnv} {β : TyVar} →
    Inert c′ →
    ConcealConversion η′ Δᴿ (rightStoreⁱ ρ₀)
      β X′ c′ B′ C′ →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W (W′ ⟨ c′ ⟩) F C′ r ρ⁺ W⁺ D′ s →
    PairedLambdaTargetClosingPendingTargetFrames
      ρ₀ W W′ F B′ q ρ⁺ W⁺ D′ s


PairedLambdaTargetClosingFrameClosingMotiveᴷ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} →
  (ρ₀ : StoreImp Φ Δᴸ Δᴿ) →
  (W W′ : Term) → (F B′ : Ty) →
  (q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ) → Set₁
PairedLambdaTargetClosingFrameClosingMotiveᴷ
    ρ₀ W W′ F B′ q =
  ∀ {ρ⁺ W⁺ C′ r} →
  PairedLambdaTargetClosingPendingTargetFrames
    ρ₀ W W′ F B′ q ρ⁺ W⁺ C′ r →
  PairedLambdaTargetClosingFrameClosingMotive
    ρ⁺ W W⁺ F C′ r


pending-refl-closing-motiveᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ
    ρ W W′ F B′ q →
  PairedLambdaTargetClosingFrameClosingMotive
    ρ W W′ F B′ q
pending-refl-closing-motiveᵀ closingᴷ = closingᴷ pending-refl
