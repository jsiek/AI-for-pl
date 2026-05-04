module MetaTheory where

-- File Charter:
--   * Public metatheory statements for the current PolyConvert slice.
--   * Exposes theorem statements at the top level while keeping proof details
--     under `proof/`.
--   * Currently exports progress for closed terms over the store-threaded
--     reduction relation.

open import Data.List using ([])
open import Data.Product as Product using (_×_; _,_)

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
  Product.Σ SealCtx
    (λ Ψ′ →
      StoreWf Δ Ψ′ Σ′ ×
      (Δ ∣ Ψ′ ∣ Σ′ ∣ Γ ⊢ M′ ⦂ A))
preservation wfΣ M⊢ red with PreservationProof.preservation-step wfΣ M⊢ red
preservation wfΣ M⊢ red | Ψ′ , eqΨ , M′⊢ =
  Ψ′ ,
  PreservationProof.exact-storeWf
    {shape = PreservationProof.step-ctx-shape red}
    eqΨ
    (PreservationProof.step-storeWf wfΣ M⊢ red) ,
  M′⊢
