module
  proof.NuImprecisionPairedUniversalConversionFreshPathSquareProof
  where

-- File Charter:
--   * Proves the full fresh-path square from its exact target/imprecision
--     reveal and conceal half-square dependencies.
--   * Uses exact-path preservation through the source conversion in the
--     forward direction before the dependency and backward afterward.
--   * Contains no target half-square implementation, postulate, hole,
--     permissive option, handler import, or broad simulation import.

open import Conversion using (conceal-all; reveal-all)
open import QuotientedTermImprecision using
  ( paired-conceal
  ; paired-reveal
  )
open import proof.NuImprecisionFreshTypePathTransport using
  ( conceal-fresh-path-backward
  ; conceal-fresh-path-forward
  ; reveal-fresh-path-backward
  ; reveal-fresh-path-forward
  )
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathSquareDef
  using (PairedUniversalConversionFreshPathSquareᵀ)
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathTargetHalfSquareDef
  using
  ( PairedUniversalConversionFreshPathTargetConcealHalfSquareᵀ
  ; PairedUniversalConversionFreshPathTargetRevealHalfSquareᵀ
  )


paired-universal-conversion-fresh-path-square-proofᵀ :
  PairedUniversalConversionFreshPathTargetRevealHalfSquareᵀ →
  PairedUniversalConversionFreshPathTargetConcealHalfSquareᵀ →
  PairedUniversalConversionFreshPathSquareᵀ
paired-universal-conversion-fresh-path-square-proofᵀ
    reveal-half conceal-half {B = B} {r = r} {s = s} x-at occ-r
    (paired-reveal corr (reveal-all source-reveal) target-reveal) =
  reveal-fresh-path-backward source-reveal
    (reveal-half {B = B} {r = r} {s = s}
      corr target-reveal occ-r x-at
      (reveal-fresh-path-forward source-reveal x-at))
paired-universal-conversion-fresh-path-square-proofᵀ
    reveal-half conceal-half {B = B} {r = r} {s = s} x-at occ-r
    (paired-conceal corr (conceal-all source-conceal) target-conceal) =
  conceal-fresh-path-backward source-conceal
    (conceal-half {B = B} {r = r} {s = s}
      corr target-conceal occ-r x-at
      (conceal-fresh-path-forward source-conceal x-at))
