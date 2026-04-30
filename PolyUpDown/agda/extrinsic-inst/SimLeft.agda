{-# OPTIONS --allow-unsolved-metas #-}

module SimLeft where

-- File Charter:
--   * Defines the left-to-right one-step simulation obligation used by
--     `DGGSim.agda` for the dynamic gradual guarantee.
--   * Keeps the case analysis for left reduction separate from the public
--     closed-program theorem statements.
--   * Depends on `SimLeftLemmas.agda` for catchup and beta-family helper
--     lemmas, and on `PreservationFresh.agda` for store/cast weakening facts.

open import Data.List using ([]; _++_; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; trans)
open import Relation.Nullary using (¬_)

open import Types
open import UpDown using (Up; Down; wt-↦)
open import Store using (StoreWf)
open import ImprecisionIndexed
open import Terms
  using
    ( Term
    ; blame
    ; ƛ_⇒_
    ; _·_
    ; _⦂∀_[_]
    ; _up_
    ; _down_
    ; substᵗᵐ
    ; wk⊒
    ; `_
    ; _∣_∣_∣_⊢_⦂_
    )
open import TermProperties using (substˣ-term; _[_])
open import TermImprecisionIndexed
open import ReductionFresh
open import SimLeftLemmas

open import PreservationFresh
  using
    ( step-preserves-store-wf
    ; wkΨ-cast-tag-⊑-≤
    ; wkΨ-cast-tag-⊒-≤
    )
    
sim-left :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  (Σ[ Ψˡ″ ∈ SealCtx ]
    Σ[ Ψˡ≤Ψˡ″ ∈ Ψˡ ≤ Ψˡ″ ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ″ , Σˡ′ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
sim-left M⊑M′ wfΣˡ wfΣʳ red with red

-- Congruence: application operator.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡᵣ lenΦ (Terms.wk⊑ (store-growth redL) hu′)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , huᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ up _ , up-↠ M′↠M′ᵣ ,
  ⊑upR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ huᵣ

sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊒-≤ Ψˡ≤Ψˡᵣ lenΦ (wk⊒ (store-growth redL) hd′)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , hdᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ down _ , down-↠ M′↠M′ᵣ ,
  ⊑downR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ hdᵣ

sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑· L⊑L′ Arg⊑Arg′
    with sim-left L⊑L′ wfΣˡ wfΣʳ redL
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑· L⊑L′ Arg⊑Arg′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , (M′ᵣ · _) , appL-↠ M′↠M′ᵣ ,
  ⊑· Nᵣ⊑M′ᵣ (wkΨΣ-⊑ Ψˡ≤Ψˡᵣ (store-growth redL) Arg⊑Arg′)

-- Congruence: application operand.
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
    with M⊑M′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₂ vV redM)
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  let Φᵣ , lenΦᵣ , huᵣ =
        wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡᵣ lenΦ
          (Terms.wk⊑ (store-growth redM) hu′)
  in
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ up _ , up-↠ M′↠M′ᵣ ,
  ⊑upR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ huᵣ
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₂ vV redM)
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊒-≤ Ψˡ≤Ψˡᵣ lenΦ (wk⊒ (store-growth redM) hd′)
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , hdᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ down _ , down-↠ M′↠M′ᵣ ,
  ⊑downR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ hdᵣ
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑· L⊑L′ Arg⊑Arg′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vV L⊑L′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑· L⊑L′ Arg⊑Arg′
  | Σʳᵥ , wfΣʳᵥ , V′ , vV′ , L′↠V′ , V⊑V′
    with sim-left Arg⊑Arg′ wfΣˡ wfΣʳᵥ redM
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑· L⊑L′ Arg⊑Arg′
  | Σʳᵥ , wfΣʳᵥ , V′ , vV′ , L′↠V′ , V⊑V′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , (V′ · M′ᵣ) ,
  multi-trans (appL-↠ {M = _} L′↠V′) (appR-↠ vV′ M′↠M′ᵣ) ,
  ⊑· (wkΨΣ-⊑ Ψˡ≤Ψˡᵣ (store-growth redM) V⊑V′) Nᵣ⊑M′ᵣ

-- Congruence: type application.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·α redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·α redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊒-≤ Ψˡ≤Ψˡᵣ lenΦ
           (wk⊒ (store-growth (ξ-·α redM)) hd′)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , hdᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ down _ , down-↠ M′↠M′ᵣ ,
  ⊑downR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ hdᵣ
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑⦂∀ rel wfA wfB hT
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑⦂∀ rel wfA wfB hT
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ ⦂∀ _ [ _ ] ,
  sim-left-w09-tyapp-↠ M′↠M′ᵣ ,
  ⊑⦂∀ Nᵣ⊑M′ᵣ
    (UpDown.WfTy-weakenˢ wfA Ψˡ≤Ψˡᵣ)
    (UpDown.WfTy-weakenˢ wfB Ψˡ≤Ψˡᵣ)
    (UpDown.WfTy-weakenˢ hT Ψˡ≤Ψˡᵣ)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑⦂∀-ν A B p rel wfA hT inst =
  {!!}

-- Congruence: up casts.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-up redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡᵣ lenΦ (Terms.wk⊑ (store-growth redM) hu′)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , huᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ up _ , up-↠ M′↠M′ᵣ ,
  ⊑upR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ huᵣ
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-up redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑up Φ lenΦ rel hu hu′
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑up Φ lenΦ rel hu hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upL Φ lenΦ rel hu
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upL Φ lenΦ rel hu
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  let Φᵣ , lenΦᵣ , huᵣ =
        wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡᵣ lenΦ (Terms.wk⊑ (store-growth redM) hu)
  in
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ ,
  ⊑upL Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ huᵣ

-- Congruence: down casts.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-down redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡᵣ lenΦ (Terms.wk⊑ (store-growth redM) hu′)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , huᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ up _ , up-↠ M′↠M′ᵣ ,
  ⊑upR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ huᵣ
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-down redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑down Φ lenΦ rel hd hd′
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑down Φ lenΦ rel hd hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downL Φ lenΦ rel hd
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downL Φ lenΦ rel hd
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- Congruence: primitive operator left operand.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡᵣ lenΦ (Terms.wk⊑ (store-growth redL) hu′)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , huᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ up _ , up-↠ M′↠M′ᵣ ,
  ⊑upR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ huᵣ
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑⊕ L⊑L′ Arg⊑Arg′
    with sim-left L⊑L′ wfΣˡ wfΣʳ redL
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑⊕ L⊑L′ Arg⊑Arg′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- Congruence: primitive operator right operand.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₂ vV redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₂ vV redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑⊕ L⊑L′ Arg⊑Arg′
    with sim-left Arg⊑Arg′ wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑⊕ L⊑L′ Arg⊑Arg′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- β reduction
-- β reduction, ⊑upR
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
    with M⊑M′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡᵣ lenΦ hu′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , huᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ up _ , up-↠ M′↠M′ᵣ ,
  ⊑upR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ huᵣ

-- β reduction, ⊑downR
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- β reduction, ⊑·
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑· L⊑L′ W⊑W′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} (ƛ A ⇒ N) L⊑L′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , ƛN⊑V′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳᶠ} vW W⊑W′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , ƛN⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta {Σʳ = Σʳᵃ} ƛN⊑V′ vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , ƛN⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N[W]⊑N′ =
  Ψˡ , ≤-refl , Σʳᵝ , N′ ,
  multi-trans
    (appL-↠ {M = _} L′↠V′)
    (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′) ,
  N[W]⊑N′

-- β-up-∀
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-∀ vV) =
  {!!}

-- β-up-↦
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
    with M⊑M′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β-up-↦ vV vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β-up-↦ vV vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} (vV up _↦_) L⊑L′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vup⊑V′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳᶠ} vW W⊑W′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vup⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-up {Σʳ = Σʳᵃ} Vup⊑V′ vV vV′
           W⊑W′ᵥ vW vW′ᵥ
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vup⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Ψˡ , ≤-refl , Σʳᵝ , N′ ,
  multi-trans
    (appL-↠ {M = _} L′↠V′)
    (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′) ,
  N⊑N′
  
-- β-down-↦
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
    with M⊑M′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β-down-↦ vV vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡᵣ lenΦ hu′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , huᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ up _ , up-↠ M′↠M′ᵣ ,
  ⊑upR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ huᵣ
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β-down-↦ vV vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} (vV down _↦_) L⊑L′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vdown⊑V′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳᶠ} vW W⊑W′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vdown⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-down {Σʳ = Σʳᵃ} Vdown⊑V′ vV vV′
           W⊑W′ᵥ vW vW′ᵥ
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vdown⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Ψˡ , ≤-refl , Σʳᵝ , N′ ,
  multi-trans
    (appL-↠ {M = _} L′↠V′)
    (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′) ,
  N⊑N′
  
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (id-up vV) =
  {!!}
sim-left {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (id-down {V = V} {A = C} vV)
    with sim-left-w03-id-down {Σʳ = Σʳ} {V = V} {C = C} M⊑M′
sim-left {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (id-down {V = V} {A = C} vV)
  | N′ , M′↠N′ , V⊑N′ =
  Ψˡ , ≤-refl , Σʳ , N′ , M′↠N′ , V⊑N′
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (seal-unseal vV) =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (tag-untag-ok vV) =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (tag-untag-bad vV G≢H) =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step δ-⊕ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step blame-·₁ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (blame-·₂ vV) =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step blame-·α =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step blame-up =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step blame-down =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step blame-⊕₁ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (blame-⊕₂ vV) =
  {!!}

-- PolyUpDown-specific store-allocation/poly-instantiation cases.
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-Λ = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-down-∀ vV = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-down-ν vV = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-up-ν vV = {!!}
