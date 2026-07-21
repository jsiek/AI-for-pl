module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationGenNuLeafDef
  where

-- File Charter:
--   * Defines the complete source generic-cast/target-`ν` continuation leaf.
--   * Restates the terminal handler contract at its own dependency boundary.
--   * Contains no implementation, postulate, hole, permissive option, record
--     projection, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; genᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
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
import NarrowWiden as NW
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; occurs
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationGenNuLeafᵀ : Set₁
PairedLambdaTargetClosingContinuationGenNuLeafᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V N′ : Term} {A B B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {c : Coercion} {μ : ModeEnv} →
  Value V → No• V →
  Value N′ → No• N′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (hA : WfTy Δᴸ A) →
  (occ : occurs zero B ≡ true) →
  genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ c ∶ ⇑ᵗ A =⇒ B →
  NW.Narrowing c →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B′ ∶ q →
  (occ-r : occurs zero B ≡ true) →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    (V ⟨ C.gen A c ⟩) N′ B B′ (ν occ-r r)
