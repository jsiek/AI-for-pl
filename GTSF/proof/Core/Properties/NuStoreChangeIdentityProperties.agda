module proof.Core.Properties.NuStoreChangeIdentityProperties where

-- File Charter:
--   * Proves neutral facts about accumulated store changes and identity casts.
--   * Preserves atomic types through type changes and exposes the resulting
--     identity-cast reduction on values.
--   * Contains no term-imprecision case analysis or world-coherent semantics.

import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import NuReduction using
  (applyTy; applyTys; bind; keep; pure-step; β-id; _—→[_]_)
open import NuTerms using (Value; _⟨_⟩)
open import Types using (Atom; ＇_; ‵_; ★; ⇑ᵗ)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)


applyTy-preserves-Atom :
  ∀ χ {A} →
  Atom A →
  Atom (applyTy χ A)
applyTy-preserves-Atom keep atom = atom
applyTy-preserves-Atom (bind A) (＇ X) = ＇ (suc X)
applyTy-preserves-Atom (bind A) (‵ ι) = ‵ ι
applyTy-preserves-Atom (bind A) ★ = ★


applyTys-preserves-Atom :
  ∀ χs {A} →
  Atom A →
  Atom (applyTys χs A)
applyTys-preserves-Atom [] atom = atom
applyTys-preserves-Atom (χ ∷ χs) atom =
  applyTys-preserves-Atom χs (applyTy-preserves-Atom χ atom)


post-catchup-β-id :
  ∀ χs {V A} →
  Value V →
  V ⟨ applyCoercions χs (C.id A) ⟩ —→[ keep ] V
post-catchup-β-id [] vV = pure-step (β-id vV)
post-catchup-β-id (keep ∷ χs) vV =
  post-catchup-β-id χs vV
post-catchup-β-id (bind A ∷ χs) {A = B} vV =
  post-catchup-β-id χs {A = ⇑ᵗ B} vV
