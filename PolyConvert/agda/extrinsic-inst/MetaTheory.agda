module MetaTheory where

-- File Charter:
--   * Public metatheory statements for the current PolyConvert slice.
--   * Exposes theorem statements at the top level while keeping proof details
--     under `proof/`.
--   * Currently exports progress for closed terms over the store-threaded
--     reduction relation.

open import Data.List using ([])

open import Types
open import Terms

import proof.Progress as ProgressProof

progress :
  ∀ {Ψ}{Σ : Store}{M : Term}{A : Ty} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A →
  ProgressProof.Progress {Σ = Σ} M
progress = ProgressProof.progress
