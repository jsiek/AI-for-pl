module D16WideMarkIndependenceProbe where

-- File Charter:
--   * Checks that stores and center alignment do not determine impEnv marks,
--     even after all four landed D16 WorldInvariants fields are required.
--   * Uses two one-cell worlds with identical embeddings and stores and with
--     different marks as the minimal counterexample to mark reconstruction.
--   * Changes no live definition and depends only on the landed D16 layer.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using (TyStore; store-empty; store-bind)
open import Consistency using (id↪ᵗ; toRenameᵗ)
open import Imprecision using (ImpEnv; X⊑X; X⊑★)
import proof.DGG.CtxImp as CTX
import proof.DGG.WorldInvariants as WI


------------------------------------------------------------------------
-- Same layout, two valid mark choices
------------------------------------------------------------------------

nat-store : TyStore 1
nat-store = store-bind store-empty (‵ `ℕ)

precise-env : ImpEnv 1
precise-env Fin.zero = X⊑X

dynamic-env : ImpEnv 1
dynamic-env Fin.zero = X⊑★

precise-world : CTX.World 1 1 1
precise-world = CTX.world id↪ᵗ id↪ᵗ precise-env nat-store nat-store

dynamic-world : CTX.World 1 1 1
dynamic-world = CTX.world id↪ᵗ id↪ᵗ dynamic-env nat-store nat-store

precise-world-invariants : WI.WorldInvariants precise-world
precise-world-invariants =
  WI.identityWorld-invariants precise-env nat-store no-dynamic-star
  where
  no-dynamic-star : ∀ X
    → precise-env (toRenameᵗ id↪ᵗ X) ≡ X⊑★
    → TyStore.lookupStore nat-store X ≡ ★
    → ∀ Y
    → toRenameᵗ id↪ᵗ Y ≢ toRenameᵗ id↪ᵗ X
  no-dynamic-star Fin.zero () entry Y aligned

dynamic-world-invariants : WI.WorldInvariants dynamic-world
dynamic-world-invariants =
  WI.identityWorld-invariants dynamic-env nat-store no-dynamic-star
  where
  no-dynamic-star : ∀ X
    → dynamic-env (toRenameᵗ id↪ᵗ X) ≡ X⊑★
    → TyStore.lookupStore nat-store X ≡ ★
    → ∀ Y
    → toRenameᵗ id↪ᵗ Y ≢ toRenameᵗ id↪ᵗ X
  no-dynamic-star Fin.zero mark () Y aligned


------------------------------------------------------------------------
-- Refutation of reconstruction from valid layouts
------------------------------------------------------------------------

ValidLayoutsDetermineMarks : Set
ValidLayoutsDetermineMarks =
  ∀ {W W′ : CTX.World 1 1 1}
  → WI.WorldInvariants W
  → WI.WorldInvariants W′
  → CTX.ηᴸʷ W ≡ CTX.ηᴸʷ W′
  → CTX.ηᴿʷ W ≡ CTX.ηᴿʷ W′
  → CTX.sourceStoreʷ W ≡ CTX.sourceStoreʷ W′
  → CTX.targetStoreʷ W ≡ CTX.targetStoreʷ W′
  → ∀ Z
  → CTX.impEnvʷ W Z ≡ CTX.impEnvʷ W′ Z

valid-layouts-do-not-determine-marks :
  ValidLayoutsDetermineMarks → ⊥
valid-layouts-do-not-determine-marks determines
    with determines precise-world-invariants dynamic-world-invariants
      refl refl refl refl Fin.zero
valid-layouts-do-not-determine-marks determines | ()
