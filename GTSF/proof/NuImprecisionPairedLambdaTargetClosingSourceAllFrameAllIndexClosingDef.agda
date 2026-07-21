module
  proof.NuImprecisionPairedLambdaTargetClosingSourceAllFrameAllIndexClosingDef
  where

-- File Charter:
--   * Defines the fused structural-all-index branch for one source universal
--     frame inside paired-lambda target closing.
--   * Retains the exact inner and framed QTI relations, endpoint evidence,
--     and recursive closing motive; the target binder is never opened into a
--     false source-only intermediate index.
--   * Is generic across narrowing, widening, reveal, and conceal source
--     frames because their exact evidence remains in the framed QTI premise.
--   * Contains no implementation, postulate, hole, or permissive option.

import Coercions as C
open import Coercions using (Coercion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)


PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ : Set₁
PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ : Ty} {d : Coercion}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ `∀ B′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ suc Δᴿ} →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ `∀ B ⊑ `∀ B′ ∶ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⟨ C.`∀ d ⟩ ⊑ W′
      ⦂ `∀ C ⊑ `∀ B′ ∶ ∀ⁱ r →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    W W′ B (`∀ B′) q →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (W ⟨ C.`∀ d ⟩) W′ C (`∀ B′) (∀ⁱ r)
