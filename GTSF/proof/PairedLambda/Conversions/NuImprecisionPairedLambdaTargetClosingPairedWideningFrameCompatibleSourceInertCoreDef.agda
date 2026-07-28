module
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreDef
  where

-- File Charter:
--   * Defines the exact residual core of the compatible-source-inert paired
--     widening branch after inverting its forced source universal widening.
--   * Replaces the outer source `cast-all` typing and inert witness with the
--     body widening under the extended mode, context, and store; target inert
--     widening is reduced to tag, function, and universal views.
--   * Reduces the final paired conversion to its source-universal reveal or
--     conceal body while retaining the recursive result, exact frame view,
--     allocation lifts, and final reveal.
--   * Contains no implementation, postulate, hole, permissive option,
--     recursive frame-closing dependency, or broad simulation import.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; ModeEnv; tagTyAllowed)
open import Data.Bool using (true)
open import Conversion using (ConcealConversion; RevealConversion)
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
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; StoreCorresponds
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuTerms using (Term; ⇑ᵗᵐ; _•; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedConversion
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using
  ( Ty
  ; TyCtx
  ; TyVar
  ; Store
  ; Ground
  ; WfTy
  ; ★
  ; _⇒_
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


data PairedWideningTargetInertView
    (μ : ModeEnv) (Δ : TyCtx) (Σ : Store) :
    Coercion → Ty → Ty → Set where
  inert-tag : ∀ {G} →
    WfTy Δ G →
    Ground G →
    tagTyAllowed μ G ≡ true →
    PairedWideningTargetInertView μ Δ Σ (G C.!) G ★

  inert-fun : ∀ {s t A A′ B B′} →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A′ ⊒ A →
    μ ∣ Δ ∣ Σ ⊢ t ∶ B ⊑ B′ →
    PairedWideningTargetInertView μ Δ Σ
      (s C.↦ t) (A ⇒ B) (A′ ⇒ B′)

  inert-all : ∀ {d B C} →
    C.extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ d ∶ B ⊑ C →
    PairedWideningTargetInertView μ Δ Σ
      (C.`∀ d) (`∀ B) (`∀ C)


data PairedSourceAllConversionView
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) (ρ : StoreImp Φ Δᴸ Δᴿ)
    (c c′ : Coercion) {A A′ B B′ : Ty}
    (p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ A′ ⊣ Δᴿ)
    (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) : Set₁ where
  source-all-reveal :
    ∀ {α β : TyVar} {X X′ : Ty} {pX} {η η′ : ModeEnv} →
    StoreCorresponds ρ α X β X′ pX →
    RevealConversion (C.extᵈ η) (suc Δᴸ) (⟰ᵗ (leftStoreⁱ ρ))
      (suc α) (⇑ᵗ X) c A B →
    RevealConversion η′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
    PairedSourceAllConversionView Φ Δᴸ Δᴿ ρ c c′ p q

  source-all-conceal :
    ∀ {α β : TyVar} {X X′ : Ty} {pX} {η η′ : ModeEnv} →
    StoreCorresponds ρ α X β X′ pX →
    ConcealConversion (C.extᵈ η) (suc Δᴸ) (⟰ᵗ (leftStoreⁱ ρ))
      (suc α) (⇑ᵗ X) c A B →
    ConcealConversion η′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
    PairedSourceAllConversionView Φ Δᴸ Δᴿ ρ c c′ p q


PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ :
  Set₁
PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ =
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
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  C.extᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ₀)
    ⊢ d ∶ B ⊑ C →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
  PairedWideningTargetInertView μ′ Δᴿ
    (rightStoreⁱ ρ₀) d′ B′ C′ →
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
  PairedSourceAllConversionView Φ Δᴸ Δᴿ ρ c c′
    r (∀ⁱ s) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ
      (((⇑ᵗᵐ (W ⟨ C.`∀ d ⟩)) •) ⟨ c ⟩)
        ⟨ C.`∀ t ⟩
      ⊑ (W′ ⟨ d′ ⟩) ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C₀′ ∶ ⊑-source-liftνᵢ p
