module
  proof.NuImprecisionPairedUniversalConversionFreshPathCycleProof
  where

-- File Charter:
--   * Reduces the fresh-path-cycle impossibility to one joint path transport
--     around the imprecision/paired-conversion square.
--   * Converts boolean occurrence to a proof-relevant path and closes the
--     cycle with the finite self-extension contradiction.
--   * Keeps the missing joint transport as an inline theorem parameter;
--     contains no postulate, hole, permissive option, or broad simulation
--     import.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
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
open import proof.NuImprecisionFreshTypePath using
  ( VarAtPath
  ; body
  ; occurs-to-var-at-path
  ; var-at-path-not-below-itself
  )
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathCycleDef
  using (PairedUniversalConversionFreshPathCycleᵀ)


paired-universal-conversion-fresh-path-cycle-proofᵀ :
  (∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
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
      (ν occ-r r) (∀ⁱ s) →
    VarAtPath zero (body p) B) →
  PairedUniversalConversionFreshPathCycleᵀ
paired-universal-conversion-fresh-path-cycle-proofᵀ
    transport occ-r conversion
    with occurs-to-var-at-path occ-r
paired-universal-conversion-fresh-path-cycle-proofᵀ
    transport occ-r conversion | p , x-at =
  var-at-path-not-below-itself x-at
    (transport x-at occ-r conversion)
