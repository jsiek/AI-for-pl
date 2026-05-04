module proof.DGGSimLeftApp where

-- File Charter:
--   * Function-application helper interfaces for the left-to-right simulation.
--   * Owns operator/operand congruence and term-level beta-family obligations.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([])
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Imprecision
open import Conversion
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.DGGCommon
open import proof.DGGMultistep using (appL-↠; appR-↠; multi-trans)
open import proof.DGGCatchup using (left-value-right-catchup)
open import proof.DGGTermImprecision using (wk-left-world-⊑)
open import proof.Preservation using (store-growth)

SimLeftStepᵃ : Set
SimLeftStepᵃ =
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  ∃[ Ψˡ′ ]
    (Ψˡ ≤ Ψˡ′ ×
     StoreWf 0 Ψˡ′ Σˡ′ ×
     ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
       (StoreWf 0 Ψʳ′ Σʳ′ ×
        ∃[ N′ ]
          ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
           TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′ N N′ A B)))

sim-left-app₁ :
  SimLeftStepᵃ →
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ L L′ M M′ N A A′ B B′} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ L L′ (A ⇒ B) (A′ ⇒ B′) →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A A′ →
  Σˡ ∣ L —→ Σˡ′ ∣ N →
  ∃[ Ψˡ′ ]
    (Ψˡ ≤ Ψˡ′ ×
     StoreWf 0 Ψˡ′ Σˡ′ ×
     ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
       (StoreWf 0 Ψʳ′ Σʳ′ ×
        ∃[ N′ ]
          ((Σʳ ∣ (L′ · M′) —↠ Σʳ′ ∣ (N′ · M′)) ×
           TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′ (N · M) (N′ · M′) B B′)))
sim-left-app₁ sim-left-step {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ relL relM redL
    with sim-left-step wfΣˡ wfΣʳ relL redL
sim-left-app₁ sim-left-step {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ relL relM redL
  | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
    L′↠N′ , N⊑N′ =
  Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
  appL-↠ L′↠N′ ,
  ⊑· N⊑N′
    (wk-left-world-⊑
      {Ψʳ = Ψʳ} {Ψʳ′ = Ψʳ′} {Σʳ = Σʳ} {Σʳ′ = Σʳ′}
      wfΣˡ′ wfΣʳ′ Ψ≤Ψ′ (store-growth redL) relM)

sim-left-app₂ :
  SimLeftStepᵃ →
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ V L′ M M′ N A A′ B B′} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  TermRel Ψˡ Σˡ Ψʳ Σʳ V L′ (A ⇒ B) (A′ ⇒ B′) →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A A′ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  ∃[ Ψˡ′ ]
    (Ψˡ ≤ Ψˡ′ ×
     StoreWf 0 Ψˡ′ Σˡ′ ×
     ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
       (StoreWf 0 Ψʳ′ Σʳ′ ×
        ∃[ N′ ]
          ((Σʳ ∣ (L′ · M′) —↠ Σʳ′ ∣ N′) ×
           TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′ (V · N) N′ B B′)))
sim-left-app₂ sim-left-step wfΣˡ wfΣʳ vV relL relM redM
    with left-value-right-catchup wfΣˡ wfΣʳ vV relL
sim-left-app₂ sim-left-step wfΣˡ wfΣʳ vV relL relM redM
  | Ψʳᵥ , Σʳᵥ , wfΣʳᵥ , V′ , vV′ , L′↠V′ , V⊑V′
    with sim-left-step wfΣˡ wfΣʳᵥ relM redM
sim-left-app₂ sim-left-step wfΣˡ wfΣʳ vV relL relM redM
  | Ψʳᵥ , Σʳᵥ , wfΣʳᵥ , V′ , vV′ , L′↠V′ , V⊑V′
  | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
    M′↠N′ , N⊑N′ =
  Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ · N′ ,
  multi-trans (appL-↠ L′↠V′) (appR-↠ vV′ M′↠N′) ,
  ⊑·
    (wk-left-world-⊑
      {Ψʳ = Ψʳᵥ} {Ψʳ′ = Ψʳ′} {Σʳ = Σʳᵥ} {Σʳ′ = Σʳ′}
      wfΣˡ′ wfΣʳ′ Ψ≤Ψ′ (store-growth redM) V⊑V′)
    N⊑N′

postulate
  sim-left-beta-app :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ A A′ B B′ C N W L′ W′} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value W →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (ƛ C ⇒ N) L′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ Ψʳ Σʳ W W′ A A′ →
    ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
      (StoreWf 0 Ψʳ′ Σʳ′ ×
       ∃[ N′ ]
         ((Σʳ ∣ (L′ · W′) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ Σˡ Ψʳ′ Σʳ′ (N [ W ]) N′ B B′))

  sim-left-beta-up-app :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V W V′ W′ A A′ B B′ p q} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value W →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (V ⇑ A⇒B⊑A′⇒B′ p q) V′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ Ψʳ Σʳ W W′ A A′ →
    ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
      (StoreWf 0 Ψʳ′ Σʳ′ ×
       ∃[ N′ ]
         ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ Σˡ Ψʳ′ Σʳ′ ((V · (W ⇓ p)) ⇑ q) N′ B B′))

  sim-left-beta-down-app :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V W V′ W′ A A′ B B′ p q} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value W →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (V ⇓ A⇒B⊑A′⇒B′ p q) V′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ Ψʳ Σʳ W W′ A A′ →
    ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
      (StoreWf 0 Ψʳ′ Σʳ′ ×
       ∃[ N′ ]
         ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ Σˡ Ψʳ′ Σʳ′ ((V · (W ⇑ p)) ⇓ q) N′ B B′))

  sim-left-beta-reveal-app :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V W V′ W′ A A′ B B′ p q} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value W →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (V ↑ ↑-⇒ p q) V′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ Ψʳ Σʳ W W′ A A′ →
    ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
      (StoreWf 0 Ψʳ′ Σʳ′ ×
       ∃[ N′ ]
         ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ Σˡ Ψʳ′ Σʳ′ ((V · (W ↓ p)) ↑ q) N′ B B′))

  sim-left-beta-conceal-app :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V W V′ W′ A A′ B B′ p q} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value W →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (V ↓ ↓-⇒ p q) V′ (A ⇒ B) (A′ ⇒ B′) →
    TermRel Ψˡ Σˡ Ψʳ Σʳ W W′ A A′ →
    ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
      (StoreWf 0 Ψʳ′ Σʳ′ ×
       ∃[ N′ ]
         ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ Σˡ Ψʳ′ Σʳ′ ((V · (W ↑ p)) ↓ q) N′ B B′))
