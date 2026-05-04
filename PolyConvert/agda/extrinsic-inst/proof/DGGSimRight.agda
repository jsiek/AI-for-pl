module proof.DGGSimRight where

-- File Charter:
--   * Right-to-left simulation interface for the PolyConvert DGG proof.
--   * Owns `sim-right` and its multi-step closure.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([])
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)

open import Types
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.DGGCommon

postulate
  sim-right :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σʳ′ M M′ N′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ M M′ A B →
    Σʳ ∣ M′ —→ Σʳ′ ∣ N′ →
    (∃[ Ψˡ′ ] ∃[ Σˡ′ ] ∃[ N ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       (Σˡ ∣ M —↠ Σˡ′ ∣ N) ×
       TermRel Ψˡ′ Σˡ′ N N′ A B))
    ⊎ Blames Σˡ M

  sim-right* :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σʳ′ M M′ N′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ M M′ A B →
    Σʳ ∣ M′ —↠ Σʳ′ ∣ N′ →
    (∃[ Ψˡ′ ] ∃[ Σˡ′ ] ∃[ N ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       (Σˡ ∣ M —↠ Σˡ′ ∣ N) ×
       TermRel Ψˡ′ Σˡ′ N N′ A B))
    ⊎ Blames Σˡ M
