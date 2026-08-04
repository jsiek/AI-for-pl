module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetRevealCoreDef
  where

-- File Charter:
--   * Defines the reduced fused core for target-only inert reveal-frame
--     closing under paired-lambda target closing.
--   * Jointly normalizes target reveal provenance, inertness, and both outer
--     type-imprecision indices after source-allocation result indices are
--     discharged by the separate fresh-path-cycle theorem.
--   * Only two source-universal/target-universal cases remain, distinguished
--     by a structural or source-allocation input index and a structural
--     result index.
--   * Normalizes the final paired all-to-all conversion to reveal/reveal or
--     conceal/conceal body evidence while retaining the recursively closed
--     result, exact frame view, allocation lifts, final reveal, and
--     target-framed conclusion.
--   * Contains no implementation, postulate, hole, permissive option,
--     recursive frame-closing dependency, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using (Coercion; ModeEnv)
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Bool using (true)
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
  ; ν
  )
open import Imprecision using (NonVar)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; StoreCorresponds
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuStore using (StoreWf)
open import NuTerms using (Term; ⇑ᵗᵐ; _•; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedConversion
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; TyVar
  ; WfTy
  ; `∀
  ; extᵗ
  ; occurs
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


data PairedLambdaTargetClosingTargetRevealView
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) (ρ : StoreImp Φ Δᴸ Δᴿ)
    (η : ModeEnv) (β : TyVar) (X : Ty) :
    (d : Coercion) (F B C : Ty) →
    (q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B ⊣ Δᴿ)
    (r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C ⊣ Δᴿ) → Set₁ where

  target-reveal-all-∀∀ :
    ∀ {F A B : Ty} {d : Coercion}
      {q-body : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ F ⊑ A ⊣ suc Δᴿ}
      {r-body : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ F ⊑ B ⊣ suc Δᴿ} →
    RevealConversion (C.extᵈ η) (suc Δᴿ)
      (⟰ᵗ (rightStoreⁱ ρ)) (suc β) (⇑ᵗ X) d A B →
    PairedLambdaTargetClosingTargetRevealView
      Φ Δᴸ Δᴿ ρ η β X (C.`∀ d) F (`∀ A) (`∀ B)
      (∀ⁱ q-body) (∀ⁱ r-body)

  target-reveal-all-ν∀ :
    ∀ {F A B : Ty} {d : Coercion}
      {{safe : NonVar F}}
      {occ-q : occurs zero F ≡ true}
      {q-body : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ F ⊑ `∀ A ⊣ Δᴿ}
      {r-body : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ F ⊑ B ⊣ suc Δᴿ} →
    RevealConversion (C.extᵈ η) (suc Δᴿ)
      (⟰ᵗ (rightStoreⁱ ρ)) (suc β) (⇑ᵗ X) d A B →
    PairedLambdaTargetClosingTargetRevealView
      Φ Δᴸ Δᴿ ρ η β X (C.`∀ d) F (`∀ A) (`∀ B)
      (ν safe occ-q q-body) (∀ⁱ r-body)


data PairedLambdaTargetClosingPairedAllConversionView
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) (ρ : StoreImp Φ Δᴸ Δᴿ) :
    (c c′ : Coercion) → {A A′ B B′ : Ty} →
    (p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ A′ ⊣ Δᴿ) →
    (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) → Set₁ where

  paired-all-reveal :
    ∀ {α β : TyVar} {X X′ : Ty} {pX}
      {η η′ : ModeEnv} {c c′ : Coercion}
      {A A′ B B′ : Ty}
      {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
      {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ} →
    StoreCorresponds ρ α X β X′ pX →
    RevealConversion (C.extᵈ η) (suc Δᴸ) (⟰ᵗ (leftStoreⁱ ρ))
      (suc α) (⇑ᵗ X) c A B →
    RevealConversion (C.extᵈ η′) (suc Δᴿ) (⟰ᵗ (rightStoreⁱ ρ))
      (suc β) (⇑ᵗ X′) c′ A′ B′ →
    PairedLambdaTargetClosingPairedAllConversionView
      Φ Δᴸ Δᴿ ρ c (C.`∀ c′) (∀ⁱ p) (∀ⁱ q)

  paired-all-conceal :
    ∀ {α β : TyVar} {X X′ : Ty} {pX}
      {η η′ : ModeEnv} {c c′ : Coercion}
      {A A′ B B′ : Ty}
      {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
      {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ} →
    StoreCorresponds ρ α X β X′ pX →
    ConcealConversion (C.extᵈ η) (suc Δᴸ) (⟰ᵗ (leftStoreⁱ ρ))
      (suc α) (⇑ᵗ X) c A B →
    ConcealConversion (C.extᵈ η′) (suc Δᴿ) (⟰ᵗ (rightStoreⁱ ρ))
      (suc β) (⇑ᵗ X′) c′ A′ B′ →
    PairedLambdaTargetClosingPairedAllConversionView
      Φ Δᴸ Δᴿ ρ c (C.`∀ c′) (∀ⁱ p) (∀ⁱ q)


PairedLambdaTargetClosingFrameClosingTargetRevealCoreᵀ : Set₁
PairedLambdaTargetClosingFrameClosingTargetRevealCoreᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ C′ : Ty} {d′ : Coercion}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ F ⊑ C′ ⊣ Δᴿ}
    {η′ : ModeEnv} {β : TyVar} {X′ : Ty} →
  (∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
      {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {A C₀′ D E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C₀′ ⊣ Δᴿ}
      {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ `∀ E ⊑ C₀′ ⊣ suc Δᴿ} →
    StoreImpPrefix ρ₀ ρ →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
    RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
      (⟰ᵗ (leftStoreⁱ
        (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
      (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
      (renameᵗ (extᵗ suc) D) →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
    PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
      {`∀ F} {B′} {`∀ (`∀ E)} {`∀ C₀′} q (∀ⁱ s) →
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣
        store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
      ⊢ᴺ (((⇑ᵗᵐ W) •) ⟨ c ⟩) ⟨ C.`∀ t ⟩
        ⊑ W′ ⟨ c′ ⟩
        ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C₀′ ∶ ⊑-source-liftνᵢ p) →
  PairedLambdaTargetClosingFrameView ρ₀ W W′ (`∀ F) B′ q →
  PairedLambdaTargetClosingTargetRevealView
    Φ Δᴸ Δᴿ ρ₀ η′ β X′ d′ F B′ C′ q r →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {A C₀′ D E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C₀′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C₀′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedLambdaTargetClosingPairedAllConversionView
    Φ Δᴸ Δᴿ ρ c c′ r (∀ⁱ s) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ (((⇑ᵗᵐ W) •) ⟨ c ⟩) ⟨ C.`∀ t ⟩
      ⊑ (W′ ⟨ d′ ⟩) ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C₀′ ∶ ⊑-source-liftνᵢ p
