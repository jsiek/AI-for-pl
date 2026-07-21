module
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafClosingProof
  where

-- File Charter:
--   * Adapts the exact fused matched-`Λ` closing theorem to the corresponding
--     target-closing frame handler field.
--   * Keeps the fused semantic theorem as an explicit higher-order
--     dependency because the pre-reveal rotation is false.
--   * Contains no postulate, hole, permissive option, broad simulation
--     import, or dependency on the recursive frame-closing theorem.

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
open import NuTerms using (No•; Term; Value; Λ_)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafClosingDef
  using (PairedLambdaTargetClosingLambdaLambdaLeafClosingᵀ)


paired-lambda-target-closing-lambda-lambda-leaf-handler-proofᵀ :
  PairedLambdaTargetClosingLambdaLambdaLeafClosingᵀ →
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
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (Λ V) (Λ V′) A (`∀ B) (∀ⁱ p)
paired-lambda-target-closing-lambda-lambda-leaf-handler-proofᵀ
    closing liftρ liftγ vV noV vV′ noV′ V⊑V′ =
  closing liftρ liftγ vV noV vV′ noV′ V⊑V′
