module
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingAllTerminalDef
  where

-- File Charter:
--   * Defines the hard terminal paired-lambda closing theorem when the final
--     imprecision index is paired universal `∀ⁱ`.
--   * This is the direct semantic root: its implementation must decrease a
--     body/index measure and must not invoke the continuation interpreter.
--   * Contains no implementation, postulate, hole, permissive option,
--     semantic handler, recursive theorem parameter, or broad simulation
--     import.

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
open import NuTerms using (No•; Term; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)


PairedLambdaTargetClosingAllTerminalᵀ : Set₁
PairedLambdaTargetClosingAllTerminalᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ : Ty}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ F ⊑ B′ ⊣ suc Δᴿ} →
  Value W → No• W →
  Value W′ → No• W′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ `∀ F ⊑ `∀ B′ ∶ ∀ⁱ r →
  PairedLambdaTargetClosingFrameClosingMotive
    ρ W W′ F (`∀ B′) (∀ⁱ r)
