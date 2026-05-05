module proof.DGGSimLeft where

-- File Charter:
--   * Left-to-right simulation interface for the PolyConvert DGG proof.
--   * Owns `sim-left` and its multi-step closure.
--   * Delegates application, type-application, catchup, and term-imprecision
--     helper obligations to separate files.

open import Data.List using ([])
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
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
open import proof.Preservation using (store-growth)
open import proof.PreservationWkConv using (wk-conv↑; wk-conv↓)
open import proof.PreservationWkImp using (wk-⊑; wk-⊒)
open import proof.DGGSimLeftApp
open import proof.DGGSimLeftTypeApp

SimLeftResult :
  SealCtx → Store → Term → Store → Store → Term → Ty → Ty → Set
SimLeftResult Ψˡ Σˡ M′ Σʳ Σˡ′ N A B =
  ∃[ Ψˡ′ ]
    (Ψˡ ≤ Ψˡ′ ×
     StoreWf 0 Ψˡ′ Σˡ′ ×
     ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
       (StoreWf 0 Ψʳ′ Σʳ′ ×
        ∃[ N′ ]
          ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
           TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′ N N′ A B)))

postulate
  sim-left-with-≤ : SimLeftStepˢ

  sim-left-rest :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
    Σˡ ∣ M —→ Σˡ′ ∣ N →
    SimLeftResult Ψˡ Σˡ M′ Σʳ Σˡ′ N A B

sim-left-reveal-cong :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A A′ B B′ c c′ pB} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A A′ →
  0 ∣ Ψˡ ∣ Σˡ ⊢ c ⦂ A ↑ˢ B →
  0 ∣ Ψˡ ∣ Σˡ ⊢ c′ ⦂ A′ ↑ˢ B′ →
  Ψˡ ∣ plains 0 [] ⊢ pB ⦂ B ⊑ B′ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  SimLeftResult Ψˡ Σˡ (M′ ↑ c′) Σʳ Σˡ′ (N ↑ c) B B′
sim-left-reveal-cong wfΣˡ wfΣʳ rel c⊢ c′⊢ pB⊢ redM
    with sim-left-with-≤ wfΣˡ wfΣʳ rel redM
... | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
      M′↠N′ , rel′ =
  Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ ,
  (N′ ↑ _) , reveal-↠ M′↠N′ ,
  ⊑↑ rel′
    (wk-conv↑ Ψ≤Ψ′ (store-growth redM) c⊢)
    (wk-conv↑ Ψ≤Ψ′ (store-growth redM) c′⊢)
    (wk-⊑ Ψ≤Ψ′ pB⊢)

sim-left-revealL-cong :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A A′ B c pB} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A A′ →
  0 ∣ Ψˡ ∣ Σˡ ⊢ c ⦂ A ↑ˢ B →
  Ψˡ ∣ plains 0 [] ⊢ pB ⦂ B ⊑ A′ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  SimLeftResult Ψˡ Σˡ M′ Σʳ Σˡ′ (N ↑ c) B A′
sim-left-revealL-cong wfΣˡ wfΣʳ rel c⊢ pB⊢ redM
    with sim-left-with-≤ wfΣˡ wfΣʳ rel redM
... | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
      M′↠N′ , rel′ =
  Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ ,
  N′ , M′↠N′ ,
  ⊑↑L rel′
    (wk-conv↑ Ψ≤Ψ′ (store-growth redM) c⊢)
    (wk-⊑ Ψ≤Ψ′ pB⊢)

sim-left-conceal-cong :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A A′ B B′ c c′ pB} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A A′ →
  0 ∣ Ψˡ ∣ Σˡ ⊢ c ⦂ A ↓ˢ B →
  0 ∣ Ψˡ ∣ Σˡ ⊢ c′ ⦂ A′ ↓ˢ B′ →
  Ψˡ ∣ plains 0 [] ⊢ pB ⦂ B ⊑ B′ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  SimLeftResult Ψˡ Σˡ (M′ ↓ c′) Σʳ Σˡ′ (N ↓ c) B B′
sim-left-conceal-cong wfΣˡ wfΣʳ rel c⊢ c′⊢ pB⊢ redM
    with sim-left-with-≤ wfΣˡ wfΣʳ rel redM
... | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
      M′↠N′ , rel′ =
  Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ ,
  (N′ ↓ _) , conceal-↠ M′↠N′ ,
  ⊑↓ rel′
    (wk-conv↓ Ψ≤Ψ′ (store-growth redM) c⊢)
    (wk-conv↓ Ψ≤Ψ′ (store-growth redM) c′⊢)
    (wk-⊑ Ψ≤Ψ′ pB⊢)

sim-left :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  SimLeftResult Ψˡ Σˡ M′ Σʳ Σˡ′ N A B
sim-left wfΣˡ wfΣʳ (⊑· relL relM) (ξ-·₁ redL)
    with sim-left-app₁ sim-left-with-≤ wfΣˡ wfΣʳ relL relM redL
... | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
      L′M′↠N′M′ , rel′ =
  Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , (N′ · _) ,
  L′M′↠N′M′ , rel′
sim-left wfΣˡ wfΣʳ rel (ξ-·₁ redL) =
  sim-left-rest wfΣˡ wfΣʳ rel (ξ-·₁ redL)
sim-left wfΣˡ wfΣʳ (⊑· relL relM) (ξ-·₂ vV redM) =
  sim-left-app₂ sim-left-with-≤ wfΣˡ wfΣʳ vV relL relM redM
sim-left wfΣˡ wfΣʳ (⊑⦂∀ rel wfA wfB wfT pT⊢) (ξ-·α redM) =
  sim-left-tyapp sim-left-with-≤ wfΣˡ wfΣʳ rel wfA wfB wfT pT⊢ redM
sim-left wfΣˡ wfΣʳ (⊑· relL relM) (pure-step (β vW)) =
  _ , ≤-refl , wfΣˡ , sim-left-beta-app wfΣˡ wfΣʳ vW relL relM
sim-left wfΣˡ wfΣʳ (⊑· relL relM) (pure-step (β-up-↦ vV vW)) =
  _ , ≤-refl , wfΣˡ , sim-left-beta-up-app wfΣˡ wfΣʳ vV vW relL relM
sim-left wfΣˡ wfΣʳ (⊑· relL relM) (pure-step (β-down-↦ vV vW)) =
  _ , ≤-refl , wfΣˡ ,
  sim-left-beta-down-app wfΣˡ wfΣʳ vV vW relL relM
sim-left wfΣˡ wfΣʳ (⊑· relL relM) (pure-step (β-reveal-↦ vV vW)) =
  _ , ≤-refl , wfΣˡ ,
  sim-left-beta-reveal-app wfΣˡ wfΣʳ vV vW relL relM
sim-left wfΣˡ wfΣʳ (⊑· relL relM) (pure-step (β-conceal-↦ vV vW)) =
  _ , ≤-refl , wfΣˡ ,
  sim-left-beta-conceal-app wfΣˡ wfΣʳ vV vW relL relM
sim-left wfΣˡ wfΣʳ
    rel@((⊑⦂∀ (⊑Λ vV vM′ relBody) wfA wfB wfT pT⊢)) β-Λ =
  sim-left-rest wfΣˡ wfΣʳ rel β-Λ
sim-left wfΣˡ wfΣʳ (⊑⦂∀ rel wfA wfB wfT pT⊢) (pure-step (β-up-∀ vV)) =
  _ , ≤-refl , wfΣˡ , sim-left-beta-up-∀ wfΣˡ wfΣʳ vV rel
sim-left wfΣˡ wfΣʳ rel@(⊑⦂∀ relM wfA wfB wfT pT⊢) (β-down-∀ vV) =
  sim-left-rest wfΣˡ wfΣʳ rel (β-down-∀ vV)
sim-left wfΣˡ wfΣʳ rel@(⊑⦂∀-ν relM wfA wfT pT⊢) (β-down-ν vV) =
  sim-left-rest wfΣˡ wfΣʳ rel (β-down-ν vV)
sim-left wfΣˡ wfΣʳ rel (β-up-ν vV) =
  sim-left-rest wfΣˡ wfΣʳ rel (β-up-ν vV)
sim-left wfΣˡ wfΣʳ (⊑⦂∀ rel wfA wfB wfT pT⊢) (β-reveal-∀ vV) =
  _ , ≤-refl , wfΣˡ , sim-left-beta-reveal-∀ wfΣˡ wfΣʳ vV rel
sim-left wfΣˡ wfΣʳ (⊑⦂∀ rel wfA wfB wfT pT⊢) (β-conceal-∀ vV) =
  _ , ≤-refl , wfΣˡ , sim-left-beta-conceal-∀ wfΣˡ wfΣʳ vV rel
sim-left {M′ = M′} wfΣˡ wfΣʳ rel (pure-step blame-·₁)
    with ⊑-type-imprecision rel
... | p , p⊢ =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , M′ , (M′ ∎) ,
  ⊑blameR (⊑-right-typed rel) p⊢
sim-left {M′ = M′} wfΣˡ wfΣʳ rel (pure-step (blame-·₂ vV))
    with ⊑-type-imprecision rel
... | p , p⊢ =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , M′ , (M′ ∎) ,
  ⊑blameR (⊑-right-typed rel) p⊢
sim-left {M′ = M′} wfΣˡ wfΣʳ rel (pure-step blame-·α)
    with ⊑-type-imprecision rel
... | p , p⊢ =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , M′ , (M′ ∎) ,
  ⊑blameR (⊑-right-typed rel) p⊢
sim-left {M′ = M′} wfΣˡ wfΣʳ rel (pure-step blame-up)
    with ⊑-type-imprecision rel
... | p , p⊢ =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , M′ , (M′ ∎) ,
  ⊑blameR (⊑-right-typed rel) p⊢
sim-left {M′ = M′} wfΣˡ wfΣʳ rel (pure-step blame-down)
    with ⊑-type-imprecision rel
... | p , p⊢ =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , M′ , (M′ ∎) ,
  ⊑blameR (⊑-right-typed rel) p⊢
sim-left {M′ = M′} wfΣˡ wfΣʳ rel (pure-step blame-reveal)
    with ⊑-type-imprecision rel
... | p , p⊢ =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , M′ , (M′ ∎) ,
  ⊑blameR (⊑-right-typed rel) p⊢
sim-left {M′ = M′} wfΣˡ wfΣʳ rel (pure-step blame-conceal)
    with ⊑-type-imprecision rel
... | p , p⊢ =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , M′ , (M′ ∎) ,
  ⊑blameR (⊑-right-typed rel) p⊢
sim-left {M′ = M′} wfΣˡ wfΣʳ rel (pure-step blame-⊕₁)
    with ⊑-type-imprecision rel
... | p , p⊢ =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , M′ , (M′ ∎) ,
  ⊑blameR (⊑-right-typed rel) p⊢
sim-left {M′ = M′} wfΣˡ wfΣʳ rel (pure-step (blame-⊕₂ vV))
    with ⊑-type-imprecision rel
... | p , p⊢ =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , M′ , (M′ ∎) ,
  ⊑blameR (⊑-right-typed rel) p⊢
sim-left wfΣˡ wfΣʳ (⊑⊕ ⊑$ ⊑$) (pure-step δ-⊕) =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , _ ,
  ((_ ⊕[ addℕ ] _) —→⟨ pure-step δ-⊕ ⟩ (_ ∎)) ,
  ⊑$
sim-left wfΣˡ wfΣʳ (⊑⇑ rel p⊢ p′⊢ pB⊢) (ξ-⇑ redM)
    with sim-left-with-≤ wfΣˡ wfΣʳ rel redM
... | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
      M′↠N′ , rel′ =
  Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , (N′ ⇑ _) ,
  up-↠ M′↠N′ ,
  ⊑⇑ rel′ (wk-⊑ Ψ≤Ψ′ p⊢) (wk-⊑ Ψ≤Ψ′ p′⊢)
    (wk-⊑ Ψ≤Ψ′ pB⊢)
sim-left wfΣˡ wfΣʳ (⊑⇑L rel p⊢ pB⊢) (ξ-⇑ redM)
    with sim-left-with-≤ wfΣˡ wfΣʳ rel redM
... | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
      M′↠N′ , rel′ =
  Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ , M′↠N′ ,
  ⊑⇑L rel′ (wk-⊑ Ψ≤Ψ′ p⊢) (wk-⊑ Ψ≤Ψ′ pB⊢)
sim-left wfΣˡ wfΣʳ (⊑⇓ rel p⊢ p′⊢ pB⊢) (ξ-⇓ redM)
    with sim-left-with-≤ wfΣˡ wfΣʳ rel redM
... | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
      M′↠N′ , rel′ =
  Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , (N′ ⇓ _) ,
  down-↠ M′↠N′ ,
  ⊑⇓ rel′ (wk-⊒ Ψ≤Ψ′ p⊢) (wk-⊒ Ψ≤Ψ′ p′⊢)
    (wk-⊑ Ψ≤Ψ′ pB⊢)
sim-left wfΣˡ wfΣʳ (⊑⇓L rel p⊢ pB⊢) (ξ-⇓ redM)
    with sim-left-with-≤ wfΣˡ wfΣʳ rel redM
... | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
      M′↠N′ , rel′ =
  Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ , M′↠N′ ,
  ⊑⇓L rel′ (wk-⊒ Ψ≤Ψ′ p⊢) (wk-⊑ Ψ≤Ψ′ pB⊢)
sim-left wfΣˡ wfΣʳ (⊑↑ rel c⊢ c′⊢ pB⊢) (ξ-↑ redM) =
  sim-left-reveal-cong wfΣˡ wfΣʳ rel c⊢ c′⊢ pB⊢ redM
sim-left wfΣˡ wfΣʳ (⊑↑L rel c⊢ pB⊢) (ξ-↑ redM) =
  sim-left-revealL-cong wfΣˡ wfΣʳ rel c⊢ pB⊢ redM
sim-left wfΣˡ wfΣʳ (⊑↓ rel c⊢ c′⊢ pB⊢) (ξ-↓ redM) =
  sim-left-conceal-cong wfΣˡ wfΣʳ rel c⊢ c′⊢ pB⊢ redM
sim-left wfΣˡ wfΣʳ rel red = sim-left-rest wfΣˡ wfΣʳ rel red

sim-left* :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
  Σˡ ∣ M —↠ Σˡ′ ∣ N →
  SimLeftResult Ψˡ Σˡ M′ Σʳ Σˡ′ N A B
sim-left* {M′ = M′} wfΣˡ wfΣʳ rel (M ∎) =
  _ , ≤-refl , wfΣˡ , _ , _ , wfΣʳ , _ , (M′ ∎) , rel
sim-left* wfΣˡ wfΣʳ rel (M —→⟨ M→N ⟩ N↠K)
    with sim-left wfΣˡ wfΣʳ rel M→N
... | Ψˡ₁ , Ψ≤Ψ₁ , wfΣˡ₁ , Ψʳ₁ , Σʳ₁ , wfΣʳ₁ , N′ , M′↠N′ , rel₁
    with sim-left* wfΣˡ₁ wfΣʳ₁ rel₁ N↠K
... | Ψˡ₂ , Ψ₁≤Ψ₂ , wfΣˡ₂ , Ψʳ₂ , Σʳ₂ , wfΣʳ₂ , K′ , N′↠K′ , rel₂ =
  Ψˡ₂ , ≤-trans Ψ≤Ψ₁ Ψ₁≤Ψ₂ , wfΣˡ₂ , Ψʳ₂ , Σʳ₂ ,
  wfΣʳ₂ , K′ ,
  multi-trans M′↠N′ N′↠K′ , rel₂
