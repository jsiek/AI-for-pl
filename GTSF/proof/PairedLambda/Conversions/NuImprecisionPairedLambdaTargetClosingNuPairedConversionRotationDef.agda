module
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  where

-- File Charter:
--   * Defines the exact semantic rotation of a paired universal conversion
--     through one source-only allocation.
--   * Opens the source universal coercion below the fresh runtime bullet while
--     keeping the target coercion whole and exposing the resulting index.
--   * Contains no generic-leaf administration, implementation, postulate,
--     hole, permissive option, or broad simulation import.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion)
open import Data.Bool using (true)
open import Data.List using (_∷_)
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
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; store-left
  )
open import QuotientedTermImprecision using (PairedConversion)
open import Types using (Ty; TyCtx; WfTy; `∀; occurs; ⇑ᵗ)


PairedLambdaTargetClosingNuPairedConversionRotationᵀ : Set₁
PairedLambdaTargetClosingNuPairedConversionRotationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {Aν B B′ E C′ : Ty} {c c′ : Coercion}
    {{safe : NonVar B}}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  (h⇑Aν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  (occ-r : occurs zero B ≡ true) →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ B} {B′} {`∀ (`∀ E)} {`∀ C′}
    (ν safe occ-r r) (∀ⁱ s) →
  ∃[ u ]
    PairedConversion
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ
      (store-left zero (⇑ᵗ Aν) h⇑Aν ∷ ρν)
      c c′ {B} {B′} {`∀ E} {`∀ C′} r u
