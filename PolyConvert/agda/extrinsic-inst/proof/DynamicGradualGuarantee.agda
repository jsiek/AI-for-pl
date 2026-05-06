module proof.DynamicGradualGuarantee where

-- File Charter:
--   * Assembly point for the PolyConvert dynamic gradual guarantee.
--   * The final theorem is built from simulation and catchup obligations.
--   * This file should remain thin; substantial proof scripts belong in the
--     specialized DGG modules.

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
  dynamic-gradual-guarantee :
    ∀ {Ψ Σ M M′ A B} →
    StoreWf 0 Ψ Σ →
    ⟪ 0 , Ψ , Σ , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B →
    (∀ {Σˡ′ V} →
       Value V →
       Σ ∣ M —↠ Σˡ′ ∣ V →
       ∃[ Ψˡ′ ]
         (StoreWf 0 Ψˡ′ Σˡ′ ×
          ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
            (StoreWf 0 Ψʳ′ Σʳ′ ×
             ∃[ V′ ]
               (Value V′ ×
                (Σ ∣ M′ —↠ Σʳ′ ∣ V′) ×
                (⟪ 0 , Ψˡ′ , Σˡ′ , Ψʳ′ , Σʳ′ , [] ⟫
                  ⊢ V ⊑ V′ ⦂ A ⊑ B)))))
    ×
    (Diverges Σ M → Diverges Σ M′)
    ×
    (∀ {Σʳ′ V′} →
       Value V′ →
       Σ ∣ M′ —↠ Σʳ′ ∣ V′ →
       (∃[ Ψʳ′ ]
         (StoreWf 0 Ψʳ′ Σʳ′ ×
          ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
            (StoreWf 0 Ψˡ′ Σˡ′ ×
             ∃[ V ]
               (Value V ×
                (Σ ∣ M —↠ Σˡ′ ∣ V) ×
                (⟪ 0 , Ψˡ′ , Σˡ′ , Ψʳ′ , Σʳ′ , [] ⟫
                  ⊢ V ⊑ V′ ⦂ A ⊑ B)))))
       ⊎ Blames Σ M)
    ×
    (Diverges Σ M′ → DivergeOrBlame Σ M)
