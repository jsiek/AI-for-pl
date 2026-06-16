module NuMetaTheory where

-- File Charter:
--   * Public metatheory statements for the Nu variant of GTSF.
--   * Exposes progress and preservation at the top level while keeping proof
--     scripts and helper infrastructure under `proof/`.
--   * The theorem statements are restated here explicitly; this module is not
--     a compatibility re-export of the proof modules.

open import Data.List using ([])
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Ctx
open import NuStore using (StoreIncl; StoreWf)
open import NuTerms
open import NuReduction

import proof.NuProgress as ProgressProof
import proof.NuPreservation as PreservationProof

progress :
  ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{A : Ty} →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  ProgressProof.Progress {Σ = Σ} M
progress = ProgressProof.progress

preservation :
  ∀ {Δ : TyCtx}{Σ Σ′ : Store}{Γ : Ctx}{M N : Term}{A : Ty} →
  StoreWf Δ Σ →
  CtxWf Δ Γ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Σ ∣ M —→ Σ′ ∣ N →
  ∃[ Δ′ ] StoreWf Δ′ Σ′ × Δ ≤ Δ′ × StoreIncl Σ Σ′ ×
           CtxWf Δ′ Γ × Δ′ ∣ Σ′ ∣ Γ ⊢ N ⦂ A
preservation wfΣ hΓ M⊢ red
    with PreservationProof.preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ M⊢ red
    | PreservationProof.preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ N⊢ =
  Δ′ , wfΣ′ , Δ≤Δ′ , incl , hΓ′ , N⊢
