module
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationLambdaLambdaLeafDef
  where

-- File Charter:
--   * Defines the complete matched source/target `Λ` continuation leaf.
--   * Restates the terminal handler contract at its own dependency boundary.
--   * Contains no implementation, postulate, hole, permissive option, record
--     projection, or broad simulation import.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftStoreⁱ
  ; StoreImp
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; Λ_
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
  ; `∀
  )
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationLambdaLambdaLeafᵀ : Set₁
PairedLambdaTargetClosingContinuationLambdaLambdaLeafᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {γ′ : CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {V V′ : Term} {A B : Ty}
    {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ} →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] γ′ →
  Value V → No• V →
  Value V′ → No• V′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ p →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    (Λ V) (Λ V′) A (`∀ B) (∀ⁱ p)
