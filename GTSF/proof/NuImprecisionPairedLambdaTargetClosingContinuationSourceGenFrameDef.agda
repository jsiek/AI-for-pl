module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationSourceGenFrameDef
  where

-- File Charter:
--   * Defines the source generic-cast continuation frame obligation for
--     paired-lambda target closing.
--   * States the recursive continuation premise and its exact inner frame
--     view explicitly.
--   * Contains no proof, postulate, hole, permissive option, or broad handler
--     import.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; genᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
import NarrowWiden as NW
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( Term
  ; _⟨_⟩
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; occurs
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationSourceGenFrameᵀ : Set₁
PairedLambdaTargetClosingContinuationSourceGenFrameᵀ =
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {V N′ : Term} {F B B′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ `∀ B′ ⊣ Δᴿ}
      {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ}
      {c : Coercion} {μ : ModeEnv} →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    V N′ F (`∀ B′) q →
  PairedLambdaTargetClosingFrameView ρ
    V N′ (`∀ F) (`∀ B′) q →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (hA : WfTy Δᴸ (`∀ F)) →
  (occ : occurs zero B ≡ true) →
  genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ c ∶ ⇑ᵗ (`∀ F) =⇒ B →
  NW.Narrowing c →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    (V ⟨ C.gen (`∀ F) c ⟩) N′ B (`∀ B′) (∀ⁱ r)
