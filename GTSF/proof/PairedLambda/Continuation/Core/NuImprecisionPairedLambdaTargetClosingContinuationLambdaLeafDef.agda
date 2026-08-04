module
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationLambdaLeafDef
  where

-- File Charter:
--   * Defines the complete source-only `Λ` continuation leaf.
--   * Restates the terminal handler contract at its own dependency boundary.
--   * Contains no implementation, postulate, hole, permissive option, record
--     projection, or broad simulation import.

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
open import Imprecision using (NonVar)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; LiftLeftCtxⁱ
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
  ; occurs
  )
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationLambdaLeafᵀ : Set₁
PairedLambdaTargetClosingContinuationLambdaLeafᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {γ′ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {V N′ : Term} {A B : Ty}
    {{safe : NonVar A}}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (occ : occurs zero A ≡ true) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] γ′ →
  Value V → No• V →
  Value N′ → No• N′ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    (Λ V) N′ A B (ν safe occ p)
