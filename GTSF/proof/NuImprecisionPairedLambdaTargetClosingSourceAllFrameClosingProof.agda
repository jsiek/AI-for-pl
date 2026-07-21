module
  proof.NuImprecisionPairedLambdaTargetClosingSourceAllFrameClosingProof
  where

-- File Charter:
--   * Implements all four source-universal frame handlers from one fused
--     commutation theorem.
--   * Projects exact endpoint evidence from the proof-relevant inner view,
--     reconstructs the authoritative framed QTI relation, and delegates.
--   * Contains no handler assembly, broad simulation import, postulate, hole,
--     or permissive option.

import Coercions as C
open import Coercions using (Coercion; ModeEnv)
open import Conversion using (ConcealConversion; RevealConversion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_; _∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; TyVar; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewProperties
  using
  ( paired-lambda-target-closing-frame-view-relation
  ; paired-lambda-target-closing-frame-view-source-no-bullet
  ; paired-lambda-target-closing-frame-view-source-value
  ; paired-lambda-target-closing-frame-view-target-no-bullet
  ; paired-lambda-target-closing-frame-view-target-value
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceAllFrameCommutationDef
  using (PairedLambdaTargetClosingSourceAllFrameCommutationᵀ)


paired-lambda-target-closing-source-all-narrowing-frame-closing-proofᵀ :
  PairedLambdaTargetClosingSourceAllFrameCommutationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {c : Coercion} {μ : ModeEnv} →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ
    W W′ (`∀ B) B′ q →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ C.`∀ c ∶ `∀ B ⊒ `∀ C →
  (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (W ⟨ C.`∀ c ⟩) W′ C B′ r
paired-lambda-target-closing-source-all-narrowing-frame-closing-proofᵀ
    commutation inner view mode seal★ c⊒ r =
  commutation
    (paired-lambda-target-closing-frame-view-source-value view)
    (paired-lambda-target-closing-frame-view-source-no-bullet view)
    (paired-lambda-target-closing-frame-view-target-value view)
    (paired-lambda-target-closing-frame-view-target-no-bullet view)
    relation (cast⊒⊑ᵀ mode seal★ c⊒ relation r) inner
  where
  relation = paired-lambda-target-closing-frame-view-relation view


paired-lambda-target-closing-source-all-widening-frame-closing-proofᵀ :
  PairedLambdaTargetClosingSourceAllFrameCommutationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {c : Coercion} {μ : ModeEnv} →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ
    W W′ (`∀ B) B′ q →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ C.`∀ c ∶ `∀ B ⊑ `∀ C →
  (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (W ⟨ C.`∀ c ⟩) W′ C B′ r
paired-lambda-target-closing-source-all-widening-frame-closing-proofᵀ
    commutation inner view mode seal★ c⊑ r =
  commutation
    (paired-lambda-target-closing-frame-view-source-value view)
    (paired-lambda-target-closing-frame-view-source-no-bullet view)
    (paired-lambda-target-closing-frame-view-target-value view)
    (paired-lambda-target-closing-frame-view-target-no-bullet view)
    relation (cast⊑⊑ᵀ mode seal★ c⊑ relation r) inner
  where
  relation = paired-lambda-target-closing-frame-view-relation view


paired-lambda-target-closing-source-all-reveal-frame-closing-proofᵀ :
  PairedLambdaTargetClosingSourceAllFrameCommutationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ X : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {c : Coercion} {μ : ModeEnv} {α : TyVar} →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ
    W W′ (`∀ B) B′ q →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ)
    α X (C.`∀ c) (`∀ B) (`∀ C) →
  (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (W ⟨ C.`∀ c ⟩) W′ C B′ r
paired-lambda-target-closing-source-all-reveal-frame-closing-proofᵀ
    commutation inner view c↑ r =
  commutation
    (paired-lambda-target-closing-frame-view-source-value view)
    (paired-lambda-target-closing-frame-view-source-no-bullet view)
    (paired-lambda-target-closing-frame-view-target-value view)
    (paired-lambda-target-closing-frame-view-target-no-bullet view)
    relation (conv↑⊑ᵀ c↑ relation r) inner
  where
  relation = paired-lambda-target-closing-frame-view-relation view


paired-lambda-target-closing-source-all-conceal-frame-closing-proofᵀ :
  PairedLambdaTargetClosingSourceAllFrameCommutationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ X : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {c : Coercion} {μ : ModeEnv} {α : TyVar} →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ
    W W′ (`∀ B) B′ q →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ)
    α X (C.`∀ c) (`∀ B) (`∀ C) →
  (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (W ⟨ C.`∀ c ⟩) W′ C B′ r
paired-lambda-target-closing-source-all-conceal-frame-closing-proofᵀ
    commutation inner view c↓ r =
  commutation
    (paired-lambda-target-closing-frame-view-source-value view)
    (paired-lambda-target-closing-frame-view-source-no-bullet view)
    (paired-lambda-target-closing-frame-view-target-value view)
    (paired-lambda-target-closing-frame-view-target-no-bullet view)
    relation (conv↓⊑ᵀ c↓ relation r) inner
  where
  relation = paired-lambda-target-closing-frame-view-relation view
