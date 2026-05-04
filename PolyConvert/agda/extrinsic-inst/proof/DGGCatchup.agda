module proof.DGGCatchup where

-- File Charter:
--   * Value catchup and convergence lemmas for the PolyConvert DGG proof.
--   * Owns the mutual terminal/value reasoning used by both simulations.
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
  left-value-right-catchup :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V N′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ V N′ A B →
    ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
      (StoreWf 0 Ψʳ′ Σʳ′ ×
       ∃[ V′ ]
         (Value V′ ×
          (Σʳ ∣ N′ —↠ Σʳ′ ∣ V′) ×
          TermRel Ψˡ Σˡ V V′ A B))

  right-value-left-catchup-or-blame :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ N V′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V′ →
    TermRel Ψˡ Σˡ N V′ A B →
    (∃[ Ψˡ′ ] ∃[ Σˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ V ]
         (Value V ×
          (Σˡ ∣ N —↠ Σˡ′ ∣ V) ×
          TermRel Ψˡ′ Σˡ′ V V′ A B)))
    ⊎ Blames Σˡ N

  right-converges-implies-left-converges :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ M M′ A B →
    Converges Σʳ M′ →
    Converges Σˡ M

  right-diverges-implies-left-blame-or-step :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ M M′ A B →
    Diverges Σʳ M′ →
    Σˡ ∣ M —↠ Σˡ′ ∣ N →
    Blame N ⊎ (∃[ Σ″ ] ∃[ N″ ] (Σˡ′ ∣ N —→ Σ″ ∣ N″))
