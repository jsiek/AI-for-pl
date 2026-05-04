module proof.DGGSimLeftTypeApp where

-- File Charter:
--   * Type-application helper interfaces for the left-to-right simulation.
--   * Owns polymorphic beta-family obligations and fresh-seal synchronization
--     points for type application.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([]; _∷_; length)
open import Data.Nat using (_≤_; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Imprecision
open import Conversion
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.DGGCommon
open import proof.DGGMultistep using (tyapp-↠)
open import proof.PreservationBetaRevealConceal using (openConv↑)
open import proof.PreservationWkImp using (wk-⊑)
open import proof.TypeProperties using (WfTy-weakenˢ)

SimLeftStepˢ : Set
SimLeftStepˢ =
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

sim-left-tyapp :
  SimLeftStepˢ →
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B T pT} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ (`∀ A) (`∀ B) →
  WfTy 1 Ψˡ A →
  WfTy 1 Ψˡ B →
  WfTy 0 Ψˡ T →
  Ψˡ ∣ plains 0 [] ⊢ pT ⦂ A [ T ]ᵗ ⊑ B [ T ]ᵗ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  ∃[ Ψˡ′ ]
    (Ψˡ ≤ Ψˡ′ ×
     StoreWf 0 Ψˡ′ Σˡ′ ×
     ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
       (StoreWf 0 Ψʳ′ Σʳ′ ×
        ∃[ N′ ]
          ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
           TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′ (N ⦂∀ A [ T ]) N′
             (A [ T ]ᵗ) (B [ T ]ᵗ))))
sim-left-tyapp sim-left wfΣˡ wfΣʳ rel wfA wfB wfT pT⊢ M→N
  with sim-left wfΣˡ wfΣʳ rel M→N
sim-left-tyapp sim-left wfΣˡ wfΣʳ rel wfA wfB wfT pT⊢ M→N
  | Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
    M′↠N′ , relN =
    Ψˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ ,
    (N′ ⦂∀ _ [ _ ]) ,
    tyapp-↠ M′↠N′ ,
    ⊑⦂∀ relN
      (WfTy-weakenˢ wfA Ψ≤Ψ′)
      (WfTy-weakenˢ wfB Ψ≤Ψ′)
      (WfTy-weakenˢ wfT Ψ≤Ψ′)
      (wk-⊑ Ψ≤Ψ′ pT⊢)

sim-left-beta-reveal-∀-matched :
  ∀ {Ψ Σ V V′ T c c′ pSrcT pTgtT} →
  StoreWf 0 Ψ Σ →
  Value V′ →
  TermRel Ψ Σ Ψ Σ V V′
    (`∀ (src↑ (⟰ᵗ Σ) c)) (`∀ (src↑ (⟰ᵗ Σ) c′)) →
  WfTy 0 Ψ T →
  1 ∣ Ψ ∣ ⟰ᵗ Σ ⊢ c ⦂
    src↑ (⟰ᵗ Σ) c ↑ˢ tgt↑ (⟰ᵗ Σ) c →
  1 ∣ Ψ ∣ ⟰ᵗ Σ ⊢ c′ ⦂
    src↑ (⟰ᵗ Σ) c′ ↑ˢ tgt↑ (⟰ᵗ Σ) c′ →
  Ψ ∣ plains 0 [] ⊢ pSrcT ⦂
    src↑ (⟰ᵗ Σ) c [ T ]ᵗ ⊑ src↑ (⟰ᵗ Σ) c′ [ T ]ᵗ →
  Ψ ∣ plains 0 [] ⊢ pTgtT ⦂
    tgt↑ (⟰ᵗ Σ) c [ T ]ᵗ ⊑ tgt↑ (⟰ᵗ Σ) c′ [ T ]ᵗ →
  ∃[ Σ′ ] ∃[ N′ ]
    ((Σ ∣ ((V′ ↑ ↑-∀ c′) ⦂∀ tgt↑ (⟰ᵗ Σ) c′ [ T ])
      —↠ Σ′ ∣ N′) ×
     TermRel Ψ Σ Ψ Σ
       ((V ⦂∀ src↑ (⟰ᵗ Σ) c [ T ]) ↑ subst↑ (singleTyEnv T) c)
       N′
       (tgt↑ (⟰ᵗ Σ) c [ T ]ᵗ)
       (tgt↑ (⟰ᵗ Σ) c′ [ T ]ᵗ))
sim-left-beta-reveal-∀-matched wfΣ vV′ relV wfT c⊢ c′⊢ pSrcT⊢ pTgtT⊢ =
  _ ,
  (( _ ⦂∀ _ [ _ ]) ↑ subst↑ (singleTyEnv _) _) ,
  (((_ ↑ ↑-∀ _) ⦂∀ _ [ _ ]) —→⟨ β-reveal-∀ vV′ ⟩
    (((_ ⦂∀ _ [ _ ]) ↑ subst↑ (singleTyEnv _) _) ∎)) ,
  ⊑↑
    (⊑⦂∀ relV
      (src↑-wf (storeWf-⟰ᵗ wfΣ) c⊢)
      (src↑-wf (storeWf-⟰ᵗ wfΣ) c′⊢)
      wfT
      pSrcT⊢)
    (openConv↑ c⊢ wfT)
    (openConv↑ c′⊢ wfT)
    pTgtT⊢

-- This is the store-allocation bridge isolated by the first β-Λ pass.
-- After the right side catches up to a type abstraction, both sides allocate
-- a fresh seal.  The DGG relation then needs a synchronized left-world store
-- in which the opened bodies, whose fresh seals may be named by different
-- store lengths, are related after the generated reveals.
postulate
  fresh-seal-sync-Λ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A B T pT} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    length Σˡ ≡ length Σʳ →
    Value V →
    Value V′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (Λ V) (Λ V′) (`∀ A) (`∀ B) →
    WfTy 1 Ψˡ A →
    WfTy 1 Ψˡ B →
    WfTy 0 Ψˡ T →
    Ψˡ ∣ plains 0 [] ⊢ pT ⦂ A [ T ]ᵗ ⊑ B [ T ]ᵗ →
    TermRel (suc Ψˡ) ((length Σˡ , T) ∷ Σˡ)
      (suc Ψʳ) ((length Σʳ , T) ∷ Σʳ)
      ((V [ ｀ (length Σˡ) ]ᵀ) ↑ convert↑ A (length Σˡ))
      ((V′ [ ｀ (length Σʳ) ]ᵀ) ↑ convert↑ B (length Σʳ))
      (A [ T ]ᵗ) (B [ T ]ᵗ)

postulate
  sim-left-beta-Λ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B T pT} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (Λ V) M′ (`∀ A) (`∀ B) →
    WfTy 1 Ψˡ A →
    WfTy 1 Ψˡ B →
    WfTy 0 Ψˡ T →
    Ψˡ ∣ plains 0 [] ⊢ pT ⦂ A [ T ]ᵗ ⊑ B [ T ]ᵗ →
    ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
         (StoreWf 0 Ψʳ′ Σʳ′ ×
          ∃[ N′ ]
            ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
             TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′
               ((V [ ｀ (length Σˡ) ]ᵀ) ↑ convert↑ A (length Σˡ))
               N′ (A [ T ]ᵗ) (B [ T ]ᵗ))))

  sim-left-beta-up-∀ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B T p C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (V ⇑ (`∀A⊑∀B p)) M′ (`∀ A) (`∀ B) →
    ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
      (StoreWf 0 Ψʳ′ Σʳ′ ×
       ∃[ N′ ]
         ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ Σˡ Ψʳ′ Σʳ′
            ((V ⦂∀ src⊑ p [ T ]) ⇑ p [ T ]⊑) N′ C D))

  sim-left-beta-down-∀ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B T p C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (V ⇓ (`∀A⊑∀B p)) M′ (`∀ A) (`∀ B) →
    ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
         (StoreWf 0 Ψʳ′ Σʳ′ ×
          ∃[ N′ ]
            ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
             TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′
               (((V ⦂∀ tgt⊑ p [ ｀ (length Σˡ) ]) ⇓
                 p [ ｀ (length Σˡ) ]⊑) ↑
                 convert↑ (src⊑ p) (length Σˡ))
               N′ C D)))

  sim-left-beta-down-ν :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B C T p D E} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (V ⇓ (`∀A⊑B B p)) M′ (`∀ A) C →
    ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
         (StoreWf 0 Ψʳ′ Σʳ′ ×
          ∃[ N′ ]
            ((Σʳ ∣ (M′ ⦂∀ C [ T ]) —↠ Σʳ′ ∣ N′) ×
             TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′
               ((V ⇓ p [ ｀ (length Σˡ) ]⊑) ↑
                 convert↑ (src⊑ p) (length Σˡ))
               N′ D E)))

  sim-left-beta-up-ν :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B p C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (V ⇑ (`∀A⊑B B p)) M′ A B →
    ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
         (StoreWf 0 Ψʳ′ Σʳ′ ×
          ∃[ N′ ]
            ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
             TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′
               ((V ⦂∀ src⊑ p [ ｀ (length Σˡ) ]) ⇑
                 p [ ｀ (length Σˡ) ]⊑)
               N′ C D)))

  sim-left-beta-reveal-∀ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B T c C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (V ↑ ↑-∀ c) M′ (`∀ A) (`∀ B) →
    ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
      (StoreWf 0 Ψʳ′ Σʳ′ ×
       ∃[ N′ ]
         ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ Σˡ Ψʳ′ Σʳ′
            ((V ⦂∀ src↑ (⟰ᵗ Σˡ) c [ T ]) ↑ subst↑ (singleTyEnv T) c)
            N′ C D))

  sim-left-beta-conceal-∀ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B T c C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (V ↓ ↓-∀ c) M′ (`∀ A) (`∀ B) →
    ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
      (StoreWf 0 Ψʳ′ Σʳ′ ×
       ∃[ N′ ]
         ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ Σˡ Ψʳ′ Σʳ′
            ((V ⦂∀ src↓ (⟰ᵗ Σˡ) c [ T ]) ↓ subst↓ (singleTyEnv T) c)
            N′ C D))
