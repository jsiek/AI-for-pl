module proof.NuImprecisionLeftSilentPairedCastTransportProof where

-- File Charter:
--   * Derives full left-silent paired-cast transport exhaustively from the
--     paired-conversion and paired-widening constructor-family capabilities.
--   * Keeps the easy widening implementation independent of the hard final
--     StoreCorresponds reconstruction required by paired conversions.
--   * Contains no constructor-specific transport implementation.

open import QuotientedTermImprecision using
  ( paired-conversion
  ; paired-widening
  )
open import proof.NuImprecisionLeftSilentPairedCastTransportDef using
  (LeftSilentPairedCastTransportᵀ)
open import
  proof.NuImprecisionLeftSilentPairedConversionTransportDef using
  (LeftSilentPairedConversionTransportᵀ)
open import
  proof.NuImprecisionLeftSilentPairedWideningTransportDef using
  (LeftSilentPairedWideningTransportᵀ)


left-silent-paired-cast-transport-proofᵀ :
  LeftSilentPairedConversionTransportᵀ →
  LeftSilentPairedWideningTransportᵀ →
  LeftSilentPairedCastTransportᵀ
left-silent-paired-cast-transport-proofᵀ
    conversion-transport widening-transport
    prefix inner silent lineage coherent
    (paired-conversion conversion) =
  paired-conversion
    (conversion-transport
      prefix inner silent lineage coherent conversion)
left-silent-paired-cast-transport-proofᵀ
    conversion-transport widening-transport
    prefix inner silent lineage coherent
    (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑ compat) =
  widening-transport prefix inner silent
    mode seal★ c⊑ mode′ seal★′ c′⊑ compat
