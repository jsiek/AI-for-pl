module
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingGenLeafNuConversionRotationDef
  where

-- File Charter:
--   * Defines the generic-narrowing `ν`-index paired-conversion rotation
--     required by source-only allocation with a closed target binder.
--   * Retains the complete generic leaf inputs and moves the source body
--     coercion below the runtime bullet while keeping the target coercion
--     whole.
--   * Stops before the final source reveal and exposes its intermediate
--     source-only index existentially.
--   * Contains no implementation, postulate, hole, or permissive option.

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
open import Data.Product using (∃-syntax)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  )
open import Imprecision using (NonVar)
import NarrowWiden as NW
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
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
  ; occurs
  ; ⇑ᵗ
  ; ⟰ᵗ
  )


PairedLambdaTargetClosingGenLeafNuConversionRotationᵀ : Set₁
PairedLambdaTargetClosingGenLeafNuConversionRotationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {V N′ : Term} {A B B′ Aν E C′ : Ty}
    {{safe : NonVar B}}
    {q₀ : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {g c c′ : Coercion} {μ₀ : ModeEnv}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  Value V → No• V →
  Value N′ → No• N′ →
  CastMode μ₀ →
  SealModeStore★ μ₀ (leftStoreⁱ ρ₀) →
  (hA : WfTy Δᴸ A) →
  (occ-g : occurs zero B ≡ true) →
  genᵈ μ₀ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ₀)
    ⊢ g ∶ ⇑ᵗ A =⇒ B →
  NW.GenSafe g →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B′ ∶ q₀ →
  (occ-r : occurs zero B ≡ true) →
  (r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (h⇑Aν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ B} {B′} {`∀ (`∀ E)} {`∀ C′}
    (ν safe occ-r r) (∀ⁱ s) →
  ∃[ u ]
    (((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣
        store-left zero (⇑ᵗ Aν) h⇑Aν ∷ ρν ∣ []
      ⊢ᴺ ((⇑ᵗᵐ (V ⟨ C.gen A g ⟩)) •) ⟨ c ⟩
        ⊑ N′ ⟨ c′ ⟩
        ⦂ `∀ E ⊑ `∀ C′ ∶ u)
