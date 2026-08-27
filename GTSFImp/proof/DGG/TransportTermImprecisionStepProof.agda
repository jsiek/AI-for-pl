{-# OPTIONS --safe #-}

module proof.DGG.TransportTermImprecisionStepProof where

-- File Charter:
--   * Proves one-step cast-term-imprecision transport by cases on canonical
--     world evolution.
--   * Handles the identity evolution directly and delegates the five
--     allocation cases to their genuine structural CTI inductions.
--   * Contains no compatibility world, result wrapper, or proof hole.

open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionStepᵀ)
open import proof.DGG.TransportTermImprecisionStepDef
open import proof.DGG.WorldEvolution using
  ( evolution-keep
  ; evolution-bind-left
  ; evolution-bind-left-aligned
  ; evolution-bind-right
  ; evolution-bind-both
  ; evolution-bind-both-star
  )


module _
    (transport-source-bind : TransportSourceBindᵀ)
    (transport-aligned-source-bind : TransportAlignedSourceBindᵀ)
    (transport-target-bind : TransportTargetBindᵀ)
    (transport-paired-bind : TransportPairedBindᵀ)
    (transport-paired-star-bind : TransportPairedStarBindᵀ)
    where

  transport-term-imprecision-step : TransportTermImprecisionStepᵀ
  transport-term-imprecision-step no-rebase evolution-keep related = related

  transport-term-imprecision-step
      no-rebase (evolution-bind-left eqᴸ) related =
    transport-source-bind no-rebase eqᴸ related

  transport-term-imprecision-step no-open
      (evolution-bind-left-aligned
        eqᴸ update boundary represented) related =
    transport-aligned-source-bind no-open
      eqᴸ update boundary represented related

  transport-term-imprecision-step
      no-rebase (evolution-bind-right fresh eqᴿ) related =
    transport-target-bind fresh eqᴿ related

  transport-term-imprecision-step
      no-rebase (evolution-bind-both represented eqᴸ eqᴿ) related =
    transport-paired-bind represented eqᴸ eqᴿ related

  transport-term-imprecision-step
      no-rebase
      (evolution-bind-both-star represented C≠★ eqᴸ eqᴿ) related =
    transport-paired-star-bind represented C≠★ eqᴸ eqᴿ related
