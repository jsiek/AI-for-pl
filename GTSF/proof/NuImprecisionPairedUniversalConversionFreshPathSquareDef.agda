module
  proof.NuImprecisionPairedUniversalConversionFreshPathSquareDef
  where

-- File Charter:
--   * Defines joint fresh-path transport around a source-only-to-paired
--     universal-conversion square.
--   * States that every path to the fresh source name in the source-only
--     body is reproduced below one additional universal constructor.
--   * Contains no implementation, postulate, hole, permissive option,
--     rotation theorem, handler import, or broad simulation import.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion)
open import Data.Bool using (true)
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
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using (PairedConversion)
open import Types using (Ty; TyCtx; `∀; occurs)
open import proof.NuImprecisionFreshTypePath using (VarAtPath; body)


PairedUniversalConversionFreshPathSquareᵀ : Set₁
PairedUniversalConversionFreshPathSquareᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {B B′ E C′ : Ty} {c c′ : Coercion}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {s : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ}
    {p} →
  VarAtPath zero p B →
  (occ-r : occurs zero B ≡ true) →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ B} {B′} {`∀ (`∀ E)} {`∀ C′}
    (ν _ occ-r r) (∀ⁱ s) →
  VarAtPath zero (body p) B
