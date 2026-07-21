module
  proof.NuImprecisionPairedLambdaTargetClosingGenLeafAllIndexClosingDef
  where

-- File Charter:
--   * Defines the exact structural-all branch of the generic-narrowing
--     terminal in paired-lambda target closing.
--   * Retains the complete leaf and frame-closing telescopes so the boundary
--     can be checked independently of the handler record.
--   * Contains no implementation, postulate, hole, or permissive option.

import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; genᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using (RevealConversion)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Agda.Builtin.Equality using (_≡_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
import NarrowWiden as NW
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; store-left
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( PairedConversion
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
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
  ; extᵗ
  ; occurs
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)


PairedLambdaTargetClosingGenLeafAllIndexClosingᵀ : Set₁
PairedLambdaTargetClosingGenLeafAllIndexClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {V N′ : Term} {A B B′ : Ty}
    {q₀ : Φ ∣ Δᴸ ⊢ A ⊑ `∀ B′ ⊣ Δᴿ}
    {g : Coercion} {μ₀ : ModeEnv} →
  Value V → No• V →
  Value N′ → No• N′ →
  CastMode μ₀ →
  SealModeStore★ μ₀ (leftStoreⁱ ρ₀) →
  (hA : WfTy Δᴸ A) →
  (occ : occurs zero B ≡ true) →
  genᵈ μ₀ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ₀)
    ⊢ g ∶ ⇑ᵗ A =⇒ B →
  NW.Narrowing g →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ `∀ B′ ∶ q₀ →
  (r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ) →
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {Aν C′ D E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ Aν) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ Aν)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ B} {`∀ B′} {`∀ (`∀ E)} {`∀ C′}
    (∀ⁱ r) (∀ⁱ s) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ Aν) h⇑A ∷ ρν ∣ []
    ⊢ᴺ (((⇑ᵗᵐ (V ⟨ C.gen A g ⟩)) •) ⟨ c ⟩) ⟨ C.`∀ t ⟩
      ⊑ N′ ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C′ ∶ ⊑-source-liftνᵢ p
