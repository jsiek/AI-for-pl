module proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathCycleDef where

-- File Charter:
--   * Defines the fresh-binder path-cycle impossibility for a paired
--     universal conversion whose input index is source-only and whose output
--     index is paired.
--   * Exposes only the occurrence witness, the two body indices, and the
--     paired conversion; store allocation and term-level closing are outside
--     this boundary.
--   * Contains no implementation, postulate, hole, permissive option, handler
--     import, or broad simulation import.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion)
open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
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
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using (PairedConversion)
open import Types using (Ty; TyCtx; `∀; occurs)


PairedUniversalConversionFreshPathCycleᵀ : Set₁
PairedUniversalConversionFreshPathCycleᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {B B′ E C′ : Ty} {c c′ : Coercion}
    {{safe : NonVar B}}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  (occ-r : occurs zero B ≡ true) →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ B} {B′} {`∀ (`∀ E)} {`∀ C′}
    (ν safe occ-r r) (∀ⁱ s) →
  ⊥
