module proof.DGGSimLeftApp where

-- File Charter:
--   * Function-application helper interfaces for the left-to-right simulation.
--   * Owns operator/operand congruence and term-level beta-family obligations.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([])
open import Data.Product using (_×_; ∃-syntax)

open import Types
open import Imprecision
open import Conversion
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.DGGCommon

postulate
  sim-left-app₁ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ L L′ M M′ N A A′ B B′} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ L L′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ M M′ A A′ →
    Σˡ ∣ L —→ Σˡ′ ∣ N →
    ∃[ Ψˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Σʳ′ ] ∃[ N′ ]
         ((Σʳ ∣ (L′ · M′) —↠ Σʳ′ ∣ (N′ · M′)) ×
          TermRel Ψˡ′ Σˡ′ (N · M) (N′ · M′) B B′))

  sim-left-app₂ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ V L′ M M′ N A A′ B B′} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ V L′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ M M′ A A′ →
    Σˡ ∣ M —→ Σˡ′ ∣ N →
    ∃[ Ψˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Σʳ′ ] ∃[ N′ ]
         ((Σʳ ∣ (L′ · M′) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ′ Σˡ′ (V · N) N′ B B′))

  sim-left-beta-app :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ A A′ B B′ C N W L′ W′} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value W →
    TermRel Ψˡ Σˡ (ƛ C ⇒ N) L′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ W W′ A A′ →
    ∃[ Σʳ′ ] ∃[ N′ ]
      ((Σʳ ∣ (L′ · W′) —↠ Σʳ′ ∣ N′) ×
       TermRel Ψˡ Σˡ (N [ W ]) N′ B B′)

  sim-left-beta-up-app :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V W V′ W′ A A′ B B′ p q} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value W →
    TermRel Ψˡ Σˡ (V ⇑ A⇒B⊑A′⇒B′ p q) V′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ W W′ A A′ →
    ∃[ Σʳ′ ] ∃[ N′ ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       TermRel Ψˡ Σˡ ((V · (W ⇓ p)) ⇑ q) N′ B B′)

  sim-left-beta-down-app :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V W V′ W′ A A′ B B′ p q} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value W →
    TermRel Ψˡ Σˡ (V ⇓ A⇒B⊑A′⇒B′ p q) V′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ W W′ A A′ →
    ∃[ Σʳ′ ] ∃[ N′ ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       TermRel Ψˡ Σˡ ((V · (W ⇑ p)) ⇓ q) N′ B B′)

  sim-left-beta-reveal-app :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V W V′ W′ A A′ B B′ p q} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value W →
    TermRel Ψˡ Σˡ (V ↑ ↑-⇒ p q) V′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ W W′ A A′ →
    ∃[ Σʳ′ ] ∃[ N′ ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       TermRel Ψˡ Σˡ ((V · (W ↓ p)) ↑ q) N′ B B′)

  sim-left-beta-conceal-app :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V W V′ W′ A A′ B B′ p q} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value W →
    TermRel Ψˡ Σˡ (V ↓ ↓-⇒ p q) V′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ W W′ A A′ →
    ∃[ Σʳ′ ] ∃[ N′ ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       TermRel Ψˡ Σˡ ((V · (W ↑ p)) ↓ q) N′ B B′)
