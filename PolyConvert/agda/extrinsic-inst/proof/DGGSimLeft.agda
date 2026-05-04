module proof.DGGSimLeft where

-- File Charter:
--   * Left-to-right simulation interface for the PolyConvert DGG proof.
--   * Owns `sim-left` and its multi-step closure.
--   * Delegates application, type-application, catchup, and term-imprecision
--     helper obligations to separate files.

open import Data.List using ([])
open import Data.Product using (_×_; ∃-syntax)

open import Types
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.DGGCommon
open import proof.DGGSimLeftApp
open import proof.DGGSimLeftTypeApp

postulate
  sim-left :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ M M′ A B →
    Σˡ ∣ M —→ Σˡ′ ∣ N →
    ∃[ Ψˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Σʳ′ ] ∃[ N′ ]
         ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ′ Σˡ′ N N′ A B))

  sim-left* :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ M M′ A B →
    Σˡ ∣ M —↠ Σˡ′ ∣ N →
    ∃[ Ψˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Σʳ′ ] ∃[ N′ ]
         ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ′ Σˡ′ N N′ A B))
