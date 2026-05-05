module proof.DGGSimLeftApp where

-- File Charter:
--   * Function-application helper interfaces for the left-to-right simulation.
--   * Owns operator/operand congruence and term-level beta-family obligations.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([]; _∷_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Imprecision
open import Conversion
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.DGGCommon
open import proof.DGGMultistep
  using (appL-↠; appR-↠; down-↠; multi-trans; up-↠)
open import proof.DGGCatchup using (left-value-right-catchup)
open import proof.DGGTermImprecision using (subst-⊑; wk-left-world-⊑)
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

private
  beta-subst-⊑ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ W W′ A A′ B B′} →
    (p : Imp) →
    (p⊢ : Ψˡ ∣ plains 0 [] ⊢ p ⦂ A ⊑ A′) →
    TermRel Ψˡ Σˡ Ψʳ Σʳ W W′ A A′ →
    ⟪ 0 , Ψˡ , Σˡ , (A , A′ , p , p⊢) ∷ [] ⟫
      ⊢ M ⊑ M′ ⦂ B ⊑ B′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (M [ W ]) (M′ [ W′ ]) B B′
  beta-subst-⊑ p p⊢ W⊑W′ rel = subst-⊑ W⊑W′ rel

  postulate
    sim-left-beta-app-rest :
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
sim-left-beta-app
  wfΣˡ wfΣʳ vW
  (⊑ƛ {A′ = A′} {M′ = N′} {pA = pA} {pA⊢ = pA⊢}
       hA hA′ relN) relW
    with left-value-right-catchup wfΣˡ wfΣʳ vW relW
sim-left-beta-app
  wfΣˡ wfΣʳ vW
  (⊑ƛ {A′ = A′} {M′ = N′} {pA = pA} {pA⊢ = pA⊢}
       hA hA′ relN) relW
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , W′↠V′ , W⊑V′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ [ V′ ] ,
  multi-trans (appR-↠ (ƛ A′ ⇒ N′) W′↠V′)
    (((ƛ A′ ⇒ N′) · V′) —→⟨ pure-step (β vV′) ⟩
      (N′ [ V′ ]) ∎) ,
  beta-subst-⊑ {Ψʳ = Ψʳ′} {Σʳ = Σʳ′} pA pA⊢ W⊑V′ relN
sim-left-beta-app
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {W′ = W′}
  wfΣˡ wfΣʳ vW
  (⊑⇑R rel (⊑-⇒ pDom′⊢ pCod′⊢) (⊑-⇒ pDomB⊢ pCodB⊢)) relW
    with left-value-right-catchup wfΣˡ wfΣʳ (ƛ _ ⇒ _) rel
sim-left-beta-app
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {W′ = W′}
  wfΣˡ wfΣʳ vW
  (⊑⇑R rel (⊑-⇒ pDom′⊢ pCod′⊢) (⊑-⇒ pDomB⊢ pCodB⊢)) relW
  | Ψʳᶠ , Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , L⊑V′
    with ⊑-type-imprecision L⊑V′
sim-left-beta-app
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {W′ = W′}
  wfΣˡ wfΣʳ vW
  (⊑⇑R rel (⊑-⇒ pDom′⊢ pCod′⊢) (⊑-⇒ pDomB⊢ pCodB⊢)) relW
  | Ψʳᶠ , Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , L⊑V′
  | A⇒B⊑A′⇒B′ pDom pCod , ⊑-⇒ pDom⊢ pCod⊢
    with left-value-right-catchup wfΣˡ wfΣʳᶠ vW
      (wk-left-world-⊑
        {Ψʳ = Ψʳ} {Ψʳ′ = Ψʳᶠ} {Σʳ = Σʳ} {Σʳ′ = Σʳᶠ}
        wfΣˡ wfΣʳᶠ ≤-refl ⊆ˢ-refl relW)
sim-left-beta-app
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {W′ = W′}
  wfΣˡ wfΣʳ vW
  (⊑⇑R rel (⊑-⇒ pDom′⊢ pCod′⊢) (⊑-⇒ pDomB⊢ pCodB⊢)) relW
  | Ψʳᶠ , Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , L⊑V′
  | A⇒B⊑A′⇒B′ pDom pCod , ⊑-⇒ pDom⊢ pCod⊢
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-app-rest
      wfΣˡ wfΣʳᵃ vW
      (wk-left-world-⊑
        {Ψʳ = Ψʳᶠ} {Ψʳ′ = Ψʳᵃ} {Σʳ = Σʳᶠ} {Σʳ′ = Σʳᵃ}
        wfΣˡ wfΣʳᵃ ≤-refl ⊆ˢ-refl L⊑V′)
      (⊑⇓R W⊑W′ᵥ pDom′⊢ pDom⊢)
sim-left-beta-app
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {W′ = W′}
  wfΣˡ wfΣʳ vW
  (⊑⇑R rel (⊑-⇒ pDom′⊢ pCod′⊢) (⊑-⇒ pDomB⊢ pCodB⊢)) relW
  | Ψʳᶠ , Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , L⊑V′
  | A⇒B⊑A′⇒B′ pDom pCod , ⊑-⇒ pDom⊢ pCod⊢
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , N′ ⇑ _ ,
  multi-trans (appL-↠ (up-↠ L′↠V′))
    (multi-trans (appR-↠ (vV′ ⇑ _↦_) W′↠W′ᵥ)
      (((V′ ⇑ _) · W′ᵥ) —→⟨ pure-step (β-up-↦ vV′ vW′ᵥ) ⟩
        up-↠ V′W′↠N′)) ,
  ⊑⇑R N⊑N′ pCod′⊢ pCodB⊢
sim-left-beta-app wfΣˡ wfΣʳ vW (⊑⇑R rel p′⊢ pB⊢) relW =
  sim-left-beta-app-rest wfΣˡ wfΣʳ vW (⊑⇑R rel p′⊢ pB⊢) relW
sim-left-beta-app
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {W′ = W′}
  wfΣˡ wfΣʳ vW
  (⊑⇓R rel (⊑-⇒ pDom′⊢ pCod′⊢) (⊑-⇒ pDomB⊢ pCodB⊢)) relW
    with left-value-right-catchup wfΣˡ wfΣʳ (ƛ _ ⇒ _) rel
sim-left-beta-app
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {W′ = W′}
  wfΣˡ wfΣʳ vW
  (⊑⇓R rel (⊑-⇒ pDom′⊢ pCod′⊢) (⊑-⇒ pDomB⊢ pCodB⊢)) relW
  | Ψʳᶠ , Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , L⊑V′
    with ⊑-type-imprecision L⊑V′
sim-left-beta-app
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {W′ = W′}
  wfΣˡ wfΣʳ vW
  (⊑⇓R rel (⊑-⇒ pDom′⊢ pCod′⊢) (⊑-⇒ pDomB⊢ pCodB⊢)) relW
  | Ψʳᶠ , Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , L⊑V′
  | A⇒B⊑A′⇒B′ pDom pCod , ⊑-⇒ pDom⊢ pCod⊢
    with left-value-right-catchup wfΣˡ wfΣʳᶠ vW
      (wk-left-world-⊑
        {Ψʳ = Ψʳ} {Ψʳ′ = Ψʳᶠ} {Σʳ = Σʳ} {Σʳ′ = Σʳᶠ}
        wfΣˡ wfΣʳᶠ ≤-refl ⊆ˢ-refl relW)
sim-left-beta-app
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {W′ = W′}
  wfΣˡ wfΣʳ vW
  (⊑⇓R rel (⊑-⇒ pDom′⊢ pCod′⊢) (⊑-⇒ pDomB⊢ pCodB⊢)) relW
  | Ψʳᶠ , Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , L⊑V′
  | A⇒B⊑A′⇒B′ pDom pCod , ⊑-⇒ pDom⊢ pCod⊢
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-app-rest
      wfΣˡ wfΣʳᵃ vW
      (wk-left-world-⊑
        {Ψʳ = Ψʳᶠ} {Ψʳ′ = Ψʳᵃ} {Σʳ = Σʳᶠ} {Σʳ′ = Σʳᵃ}
        wfΣˡ wfΣʳᵃ ≤-refl ⊆ˢ-refl L⊑V′)
      (⊑⇑R W⊑W′ᵥ pDom′⊢ pDom⊢)
sim-left-beta-app
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {W′ = W′}
  wfΣˡ wfΣʳ vW
  (⊑⇓R rel (⊑-⇒ pDom′⊢ pCod′⊢) (⊑-⇒ pDomB⊢ pCodB⊢)) relW
  | Ψʳᶠ , Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , L⊑V′
  | A⇒B⊑A′⇒B′ pDom pCod , ⊑-⇒ pDom⊢ pCod⊢
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , N′ ⇓ _ ,
  multi-trans (appL-↠ (down-↠ L′↠V′))
    (multi-trans (appR-↠ (vV′ ⇓ _↦_) W′↠W′ᵥ)
      (((V′ ⇓ _) · W′ᵥ) —→⟨ pure-step (β-down-↦ vV′ vW′ᵥ) ⟩
        down-↠ V′W′↠N′)) ,
  ⊑⇓R N⊑N′ pCod′⊢ pCodB⊢
sim-left-beta-app wfΣˡ wfΣʳ vW (⊑⇓R rel p′⊢ pB⊢) relW =
  sim-left-beta-app-rest wfΣˡ wfΣʳ vW (⊑⇓R rel p′⊢ pB⊢) relW

postulate
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
