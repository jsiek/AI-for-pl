module
  proof.NuImprecisionPairedLambdaTargetClosingNuTerminalDef
  where

-- File Charter:
--   * Defines terminal paired-lambda closing when the final imprecision index
--     is source-only `ν`.
--   * Keeps the endpoint value and quotiented-relation evidence explicit so
--     the theorem has the same input shape as the all-index terminal theorem.
--   * Contains no implementation, postulate, hole, permissive option,
--     continuation interpreter, semantic handler, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; Term; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; `∀; occurs)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)


PairedLambdaTargetClosingNuTerminalᵀ : Set₁
PairedLambdaTargetClosingNuTerminalᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ : Ty}
    {occ : occurs zero F ≡ true}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ F ⊑ B′ ⊣ Δᴿ} →
  Value W → No• W →
  Value W′ → No• W′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ `∀ F ⊑ B′ ∶ ν occ r →
  PairedLambdaTargetClosingFrameClosingMotive
    ρ W W′ F B′ (ν occ r)
