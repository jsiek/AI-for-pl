{-# OPTIONS --safe #-}

module proof.DGG.Catchup.MorePrecisePairedTargetGroundCastSquareLemma where

-- File Charter:
--   * Exposes the four closed paired target all/gen ground-cast squares.
--   * Instantiates the constructor-specific derivation with the completed
--     GenSafe consistency/imprecision induction.
--   * Contains no proof parameter, wrapper record, or cast classifier.

open import
  proof.DGG.Catchup.MorePrecisePairedTargetGroundCastSquareDef
  using
    ( MorePrecisePairedTargetAllInjectionGroundSquareᵀ
    ; MorePrecisePairedTargetGenInjectionGroundSquareᵀ
    ; MorePrecisePairedTargetAllProjectionGroundSquareᵀ
    ; MorePrecisePairedTargetGenProjectionGroundSquareᵀ
    )
open import
  proof.DGG.Catchup.MorePreciseGenSafeTargetGroundCastSquareLemma
  using (more-precise-gen-safe-target-ground-cast-square)
import proof.DGG.Catchup.MorePrecisePairedTargetGroundCastSquareProof as Proof


more-precise-paired-target-all-injection-ground-square :
  MorePrecisePairedTargetAllInjectionGroundSquareᵀ
more-precise-paired-target-all-injection-ground-square
    {γ = γ} cᴸ Gᵍ Bns cᴿ pC qA =
  Proof.more-precise-paired-target-all-injection-ground-square
    more-precise-gen-safe-target-ground-cast-square
    {γ = γ} cᴸ Gᵍ Bns cᴿ pC qA


more-precise-paired-target-gen-injection-ground-square :
  MorePrecisePairedTargetGenInjectionGroundSquareᵀ
more-precise-paired-target-gen-injection-ground-square
    {γ = γ} safe Gᵍ Bns cᴿ pC qA =
  Proof.more-precise-paired-target-gen-injection-ground-square
    more-precise-gen-safe-target-ground-cast-square
    {γ = γ} safe Gᵍ Bns cᴿ pC qA


more-precise-paired-target-all-projection-ground-square :
  MorePrecisePairedTargetAllProjectionGroundSquareᵀ
more-precise-paired-target-all-projection-ground-square
    {γ = γ} cᴸ Gᵍ Bns cᴿ pC qA =
  Proof.more-precise-paired-target-all-projection-ground-square
    more-precise-gen-safe-target-ground-cast-square
    {γ = γ} cᴸ Gᵍ Bns cᴿ pC qA


more-precise-paired-target-gen-projection-ground-square :
  MorePrecisePairedTargetGenProjectionGroundSquareᵀ
more-precise-paired-target-gen-projection-ground-square
    {γ = γ} safe Gᵍ Bns cᴿ pC qA =
  Proof.more-precise-paired-target-gen-projection-ground-square
    more-precise-gen-safe-target-ground-cast-square
    {γ = γ} safe Gᵍ Bns cᴿ pC qA
