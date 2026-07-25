module proof.Left.SilentTransport.NuImprecisionLeftSilentPairedCastTransportProof where

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
open import proof.Left.SilentTransport.NuImprecisionLeftSilentPairedCastTransportDef using
  (LeftSilentPairedCastTransportᵀ)
open import
  proof.Left.SilentTransport.NuImprecisionLeftSilentPairedConversionTransportDef using
  (LeftSilentPairedConversionTransportᵀ)
open import
  proof.Left.SilentTransport.NuImprecisionLeftSilentPairedWideningTransportDef using
  (LeftSilentPairedWideningTransportᵀ)


left-silent-paired-cast-transport-proofᵀ :
  LeftSilentPairedConversionTransportᵀ →
  LeftSilentPairedWideningTransportᵀ →
  LeftSilentPairedCastTransportᵀ
left-silent-paired-cast-transport-proofᵀ
    conversion-transport widening-transport
    prefix inner silent type-coherence lineage coherent
    (paired-conversion conversion) =
  paired-conversion
    (conversion-transport
      prefix inner silent type-coherence lineage coherent conversion)
left-silent-paired-cast-transport-proofᵀ
    conversion-transport widening-transport
    prefix inner silent type-coherence lineage coherent
    (paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      left-square right-square compat) =
  widening-transport prefix inner silent type-coherence
    mode seal★ c⊑ c-shape
    mode′ seal★′ c′⊑ c′-shape
    left-square right-square compat
