module TypeSafety where

-- File Charter:
--   * Public type-safety statements for the current PolyConvert slice.
--   * Exposes progress and preservation at the top level while keeping proof
--     details under `proof/`.

open import Data.List using ([])
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Store
open import Terms
open import Reduction

import proof.Progress as ProgressProof
import proof.Preservation as PreservationProof

progress :
  ∀ {Ψ}{Σ : Store}{M : Term}{A : Ty} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A →
  ProgressProof.Progress {Σ = Σ} M
progress = ProgressProof.progress

preservation :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Γ : Ctx}{M M′ : Term}{A : Ty} →
  StoreWf Δ Ψ Σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Σ ∣ M —→ Σ′ ∣ M′ →
  ∃[ Ψ′ ]
    (StoreWf Δ Ψ′ Σ′ ×
     (Δ ∣ Ψ′ ∣ Σ′ ∣ Γ ⊢ M′ ⦂ A))
preservation wfΣ M⊢ red
    with PreservationProof.preservation-step wfΣ M⊢ red
preservation wfΣ M⊢ red | Ψ′ , eqΨ , M′⊢ =
  Ψ′ ,
  PreservationProof.exact-storeWf
    {shape = PreservationProof.step-ctx-shape red}
    eqΨ
    (PreservationProof.step-storeWf wfΣ M⊢ red) ,
  M′⊢
