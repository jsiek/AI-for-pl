module NuMetaTheory where

-- File Charter:
--   * Public metatheory statements for the Nu variant of GTSF.
--   * Exposes progress and preservation at the top level while keeping proof
--     scripts and helper infrastructure under `proof/`.
--   * The theorem statements are restated here explicitly over `Telescope`;
--     this module is not a compatibility re-export of the proof modules.

open import Types
open import NuTerms
open import NuReduction
open import proof.NuTermProperties using (weakenTy)

import proof.NuProgress as ProgressProof
import proof.NuPreservation as PreservationProof

progress :
  ∀ {Γ M A} →
  RuntimeTelescope Γ →
  Γ ⊢ M ⦂ A →
  ProgressProof.Progress {Γ = Γ} M
progress = ProgressProof.progress

preservation :
  ∀ {Γ Γ′ M N A} →
  Γ ⊢ M ⦂ A →
  (red : Γ ∣ M —→ Γ′ ∣ N) →
  Γ′ ⊢ N ⦂ weakenTy (stepExt red) A
preservation = PreservationProof.preservation
