{-# OPTIONS --safe #-}

module proof.DGG.notes.CTIGammaCarriedFramePacket where

-- File Charter:
--   * Generates the fully normalized named terms and Imp Ladder used by the
--     gamma-carried reveal/conceal frame permission packet.
--   * Focuses on TargetIdentityReveal checkpoint 2 to checkpoint 3, where the
--     source allocation turns the alpha boundary from target-only to paired.
--   * Also renders checkpoint 6 to checkpoint 7, where the paired alpha
--     arrow reveal distributes and exposes the nested alpha/beta scopes.
--   * Reuses the live trusted reductions and CTI derivations without changing
--     CastTermImprecision.

open import Data.Nat using (zero)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import proof.DGG.ImpLadder using
  (defaultTermName; impLadderDefault; showTerm)
import proof.DGG.WorldSnapshot as Snapshot
import proof.DGG.Examples.TargetIdentityReveal as TIR


checkpoint₂-source-term : String
checkpoint₂-source-term =
  showTerm zero zero Snapshot.defaultName defaultTermName
    TIR.more-checkpoint₂

checkpoint₂-target-term : String
checkpoint₂-target-term =
  showTerm zero zero Snapshot.defaultNameᵗ defaultTermName
    TIR.less-checkpoint₂

checkpoint₃-source-term : String
checkpoint₃-source-term =
  showTerm zero zero Snapshot.defaultName defaultTermName
    TIR.more-checkpoint₃

checkpoint₃-target-term : String
checkpoint₃-target-term =
  showTerm zero zero Snapshot.defaultNameᵗ defaultTermName
    TIR.less-checkpoint₃

checkpoint₃-ladder : String
checkpoint₃-ladder = impLadderDefault TIR.checkpoint₃-imprecision

checkpoint₃-target-unchanged :
  checkpoint₃-target-term ≡ checkpoint₂-target-term
checkpoint₃-target-unchanged = refl

checkpoint₃-ladder-is-trusted :
  checkpoint₃-ladder ≡ TIR.checkpoint₃-ladder
checkpoint₃-ladder-is-trusted = refl


------------------------------------------------------------------------
-- The anchored-crossing replacement gate: checkpoint 6 to checkpoint 7
------------------------------------------------------------------------

checkpoint₆-source-term : String
checkpoint₆-source-term =
  showTerm zero zero Snapshot.defaultName defaultTermName
    TIR.more-checkpoint₆

checkpoint₆-target-term : String
checkpoint₆-target-term =
  showTerm zero zero Snapshot.defaultNameᵗ defaultTermName
    TIR.less-checkpoint₆

checkpoint₇-source-term : String
checkpoint₇-source-term =
  showTerm zero zero Snapshot.defaultName defaultTermName
    TIR.more-checkpoint₇

checkpoint₇-target-term : String
checkpoint₇-target-term =
  showTerm zero zero Snapshot.defaultNameᵗ defaultTermName
    TIR.less-checkpoint₇

checkpoint₃-ambient-world-snapshot : String
checkpoint₃-ambient-world-snapshot =
  Snapshot.worldSnapshotDefault TIR.checkpoint₃-allocation-world

checkpoint₃-live-rebased-world-snapshot : String
checkpoint₃-live-rebased-world-snapshot =
  Snapshot.worldSnapshotDefault TIR.checkpoint₃-world

checkpoint₃-live-alpha-beta-world-snapshot : String
checkpoint₃-live-alpha-beta-world-snapshot =
  Snapshot.worldSnapshotDefault TIR.checkpoint₃-beta-current

checkpoint₆-ladder : String
checkpoint₆-ladder = impLadderDefault TIR.checkpoint₆-imprecision

checkpoint₇-ladder : String
checkpoint₇-ladder = impLadderDefault TIR.checkpoint₇-imprecision

checkpoint₆-ladder-is-trusted :
  checkpoint₆-ladder ≡ TIR.checkpoint₆-ladder
checkpoint₆-ladder-is-trusted = refl

checkpoint₇-ladder-is-trusted :
  checkpoint₇-ladder ≡ TIR.checkpoint₇-ladder
checkpoint₇-ladder-is-trusted = refl
