module proof.DGGSimLeftTypeApp where

-- File Charter:
--   * Type-application helper interfaces for the left-to-right simulation.
--   * Owns polymorphic beta-family obligations and fresh-seal synchronization
--     points for type application.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([]; _∷_; length)
open import Data.Nat using (_≤_; suc)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; subst; sym; trans)

open import Types
open import Imprecision
open import Conversion
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.DGGCommon
open import proof.DGGTermImprecision using (tysubst-body-⊑; wk-rel-⊑; wkᴾ-map)
open import proof.DGGMultistep using (multi-trans; tyapp-↠; up-↠)
open import proof.Preservation using (len<suc-StoreWf; storeWf-fresh-ext)
open import proof.PreservationBetaDownForall using (convert↑-fresh-wt)
open import proof.PreservationBetaRevealConceal using (openConv↑)
open import proof.PreservationImpSubst using ([]⊑ᵗ-wt)
open import proof.PreservationWkImp using (wk-⊑)
open import proof.TypeProperties using (WfTy-weakenˢ)

cong-⊢⊑ :
  ∀ {Ψ Γ p A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ p ⦂ A′ ⊑ B′
cong-⊢⊑ refl refl p⊢ = p⊢

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
fresh-seal-sync-Λ {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {V = V} {V′ = V′} {A = A} {B = B} {T = T}
    wfΣˡ wfΣʳ lenEq vV vV′ (⊑Λ vV₀ vV′₀ relBody)
    wfA wfB wfT pT⊢
    rewrite sym lenEq =
  ⊑↑ opened cA⊢ cB⊢ (wk-⊑ (n≤1+n Ψˡ) pT⊢)
  where
    α = length Σˡ

    wfα : WfTy 0 (suc Ψˡ) (｀ α)
    wfα = wfSeal (len<suc-StoreWf wfΣˡ)

    relBody↑ :
      ⟪ 1 , suc Ψˡ , ⟰ᵗ ((α , T) ∷ Σˡ) , [] ⟫
        ⊢ V ⊑ V′ ⦂ A ⊑ B
    relBody↑ =
      wk-rel-⊑ {E = ⟪ 1 , Ψˡ , ⟰ᵗ Σˡ , [] ⟫}
        {Ψ′ = suc Ψˡ} {Σ′ = ⟰ᵗ ((α , T) ∷ Σˡ)}
        (n≤1+n Ψˡ) (drop ⊆ˢ-refl) (wkᴾ-map (n≤1+n Ψˡ))
        relBody

    opened :
      TermRel (suc Ψˡ) ((α , T) ∷ Σˡ) (suc Ψˡ) ((α , T) ∷ Σˡ)
        (V [ ｀ α ]ᵀ) (V′ [ ｀ α ]ᵀ)
        (A [ ｀ α ]ᵗ) (B [ ｀ α ]ᵗ)
    opened = tysubst-body-⊑ wfα relBody↑

    cA⊢ :
      0 ∣ suc Ψˡ ∣ ((α , T) ∷ Σˡ) ⊢
        convert↑ A α ⦂ A [ ｀ α ]ᵗ ↑ˢ A [ T ]ᵗ
    cA⊢ = convert↑-fresh-wt wfΣˡ wfA wfT

    cB⊢ :
      0 ∣ suc Ψˡ ∣ ((α , T) ∷ Σˡ) ⊢
        convert↑ B α ⦂ B [ ｀ α ]ᵗ ↑ˢ B [ T ]ᵗ
    cB⊢ = convert↑-fresh-wt wfΣˡ wfB wfT

sealCtx-sync :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  length Σˡ ≡ length Σʳ →
  Ψˡ ≡ Ψʳ
sealCtx-sync wfΣˡ wfΣʳ lenEq =
  trans (sym (storeWf-length wfΣˡ))
    (trans lenEq (storeWf-length wfΣʳ))

postulate
  left-value-right-catchup-Λ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ Ψʳ Σʳ (Λ V) M′ (`∀ A) (`∀ B) →
    ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
      (StoreWf 0 Ψʳ′ Σʳ′ ×
       ∃[ V′ ]
         (Value V′ ×
          (Σʳ ∣ M′ —↠ Σʳ′ ∣ V′) ×
          TermRel Ψˡ Σˡ Ψʳ′ Σʳ′ (Λ V) V′ (`∀ A) (`∀ B)))

sim-left-beta-Λ-matched :
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
  ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
    (StoreWf 0 Ψˡ′ Σˡ′ ×
     ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
       (StoreWf 0 Ψʳ′ Σʳ′ ×
        ∃[ N′ ]
          ((Σʳ ∣ ((Λ V′) ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
           TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′
             ((V [ ｀ (length Σˡ) ]ᵀ) ↑ convert↑ A (length Σˡ))
             N′ (A [ T ]ᵗ) (B [ T ]ᵗ))))
sim-left-beta-Λ-matched
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {V = V} {V′ = V′} {A = A} {B = B} {T = T}
    wfΣˡ wfΣʳ lenEq vV vV′ rel wfA wfB wfT pT⊢ =
  suc Ψˡ ,
  ((length Σˡ , T) ∷ Σˡ) ,
  storeWf-fresh-ext wfT wfΣˡ ,
  suc Ψʳ ,
  ((length Σʳ , T) ∷ Σʳ) ,
  storeWf-fresh-ext wfTʳ wfΣʳ ,
  ((V′ [ ｀ (length Σʳ) ]ᵀ) ↑ convert↑ B (length Σʳ)) ,
  (((Λ V′) ⦂∀ B [ T ]) —→⟨ β-Λ ⟩
    (((V′ [ ｀ (length Σʳ) ]ᵀ) ↑ convert↑ B (length Σʳ)) ∎)) ,
  fresh-seal-sync-Λ wfΣˡ wfΣʳ lenEq vV vV′ rel wfA wfB wfT pT⊢
  where
    wfTʳ : WfTy 0 Ψʳ T
    wfTʳ = subst (λ Ψ → WfTy 0 Ψ T)
      (sealCtx-sync wfΣˡ wfΣʳ lenEq) wfT

postulate
  sim-left-beta-Λ-rest :
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
      (Ψˡ ≤ Ψˡ′ ×
       StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
         (StoreWf 0 Ψʳ′ Σʳ′ ×
          ∃[ N′ ]
            ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
             TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′
               ((V [ ｀ (length Σˡ) ]ᵀ) ↑ convert↑ A (length Σˡ))
               N′ (A [ T ]ᵗ) (B [ T ]ᵗ))))

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
sim-left-beta-Λ {Σʳ = Σʳ} {V = V} {M′ = M′} {A = A}
    {B = B} {T = T}
    wfΣˡ wfΣʳ vV (⊑⇑R rel (⊑-∀ {p = pR} pR⊢) pB⊢)
    wfA wfB wfT pT⊢
    with left-value-right-catchup-Λ wfΣˡ wfΣʳ vV rel
sim-left-beta-Λ {Σʳ = Σʳ} {V = V} {M′ = M′} {A = A}
    {B = B} {T = T}
    wfΣˡ wfΣʳ vV (⊑⇑R rel (⊑-∀ {p = pR} pR⊢) pB⊢)
    wfA wfB wfT pT⊢
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , ΛV⊑V′
    with ⊑-index-cast refl (sym (cong `∀ (src⊑-correct pR⊢))) ΛV⊑V′
sim-left-beta-Λ {Σʳ = Σʳ} {V = V} {M′ = M′} {A = A}
    {B = B} {T = T}
    wfΣˡ wfΣʳ vV (⊑⇑R rel (⊑-∀ {p = pR} pR⊢) pB⊢)
    wfA wfB wfT pT⊢
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , ΛV⊑V′
  | ΛV⊑V′R
    with ⊑-type-imprecision ΛV⊑V′R
sim-left-beta-Λ {Σʳ = Σʳ} {V = V} {M′ = M′} {A = A}
    {B = B} {T = T}
    wfΣˡ wfΣʳ vV (⊑⇑R rel (⊑-∀ {p = pR} pR⊢) pB⊢)
    wfA wfB wfT pT⊢
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , ΛV⊑V′
  | ΛV⊑V′R
  | `∀A⊑B Bν pν , ⊑-ν wfBν occ pν⊢
    with sim-left-beta-Λ-rest wfΣˡ wfΣʳ vV
      (⊑⇑R rel (⊑-∀ {p = pR} pR⊢) pB⊢) wfA wfB wfT pT⊢
... | Ψˡ′ , Σˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ″ , Σʳ″ , wfΣʳ″ , N′ ,
      M′⦂∀↠N′ , relN =
  Ψˡ′ , Σˡ′ , wfΣˡ′ , Ψʳ″ , Σʳ″ , wfΣʳ″ , N′ , M′⦂∀↠N′ , relN
sim-left-beta-Λ {Σʳ = Σʳ} {V = V} {M′ = M′} {A = A}
    {B = B} {T = T}
    wfΣˡ wfΣʳ vV (⊑⇑R rel (⊑-∀ {p = pR} pR⊢) pB⊢)
    wfA wfB wfT pT⊢
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , ΛV⊑V′
  | ΛV⊑V′R
  | `∀A⊑∀B pI , ⊑-∀ pI⊢
    with sim-left-beta-Λ-rest wfΣˡ wfΣʳ′ vV ΛV⊑V′R
      wfA
      (subst (WfTy 1 _) (sym (src⊑-correct pR⊢)) (⊑-src-wf pR⊢))
      wfT
      (cong-⊢⊑
        (cong (λ C → C [ T ]ᵗ) (src⊑-correct pI⊢))
        (cong (λ C → C [ T ]ᵗ) (tgt⊑-correct pI⊢))
        ([]⊑ᵗ-wt pI⊢ wfT))
sim-left-beta-Λ {Σʳ = Σʳ} {V = V} {M′ = M′} {A = A}
    {B = B} {T = T}
    wfΣˡ wfΣʳ vV (⊑⇑R rel (⊑-∀ {p = pR} pR⊢) pB⊢)
    wfA wfB wfT pT⊢
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , ΛV⊑V′
  | ΛV⊑V′R
  | `∀A⊑∀B pI , ⊑-∀ pI⊢
  | Ψˡ′ , Σˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ″ , Σʳ″ , wfΣʳ″ , N′ ,
    V′⦂∀↠N′ , relN =
  Ψˡ′ , Σˡ′ , wfΣˡ′ , Ψʳ″ , Σʳ″ , wfΣʳ″ ,
  (N′ ⇑ pR [ T ]⊑) ,
  multi-trans (tyapp-↠ (up-↠ M′↠V′))
    (((V′ ⇑ `∀A⊑∀B pR) ⦂∀ B [ T ])
      —→⟨ pure-step (β-up-∀ vV′) ⟩ up-↠ V′⦂∀↠N′) ,
  ⊑⇑R relN
    (cong-⊢⊑ refl
      (cong (λ C → C [ T ]ᵗ) (tgt⊑-correct pR⊢))
      ([]⊑ᵗ-wt (wk-⊑ Ψ≤Ψ′ pR⊢) (WfTy-weakenˢ wfT Ψ≤Ψ′)))
    (wk-⊑ Ψ≤Ψ′ pT⊢)
sim-left-beta-Λ wfΣˡ wfΣʳ vV rel wfA wfB wfT pT⊢
    with sim-left-beta-Λ-rest wfΣˡ wfΣʳ vV rel wfA wfB wfT pT⊢
... | Ψˡ′ , Σˡ′ , Ψ≤Ψ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ ,
      M′⦂∀↠N′ , relN =
  Ψˡ′ , Σˡ′ , wfΣˡ′ , Ψʳ′ , Σʳ′ , wfΣʳ′ , N′ , M′⦂∀↠N′ , relN

postulate

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
