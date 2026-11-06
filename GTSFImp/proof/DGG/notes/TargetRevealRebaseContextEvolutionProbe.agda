{-# OPTIONS --safe #-}

module proof.DGG.notes.TargetRevealRebaseContextEvolutionProbe where

-- File Charter:
--   * Strict-probes the live constructor-indexed target evolution of the CTI
--     zipper used by target-reveal/rebase closing.
--   * Pins application-right and primitive-right after prerequisite target
--     sibling catch-up.
--   * Confirms that the synchronized path derives target readiness and source
--     reconstruction transport.  It does not change CTI.

open import TermCtx using (TermCtx)
open import Types using (Ty; TyCtx; _⇒_)
open import TyStore using (TyStore)
open import Imprecision using (⇒⊑⇒)
open import Primitives using (Prim; primArgTy; primResultTy)
open import CastTerms using (Term; Value; ⟨_,_,_⟩)
open import Relation.Binary.PropositionalEquality using (refl)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.World


------------------------------------------------------------------------
-- Application-right: first catch up the target function, then the argument
------------------------------------------------------------------------

application-right-evolves : ∀ {Δᴸ Δᴿ Δᴿ′}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Σᴿ′ : TyStore Δᴿ′}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴿ′ : TermCtx Δᴿ′}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ′ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ′ , Σᴿ′ , Γᴿ′ ⟩}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {L″ M″ : Term Δᴿ′}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {A″ B″ : Ty Δᴿ′}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    {pA′ : A ⊑ᵀ⟨ γ′ ⟩ A″} {pB′ : B ⊑ᵀ⟨ γ′ ⟩ B″}
    {function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB}
    {argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA}
    {function-rel′ : γ′ CTI.⊢² L ⊑ L″ ∶ ⇒⊑⇒ pA′ pB′}
    {argument-rel′ : γ′ CTI.⊢² M ⊑ M″ ∶ pA′}
    {source-value : Value L}
  → Value L″
  → TargetEdgeEvolution
      (focus-·₂ function-rel argument-rel source-value)
      (focus-·₂ function-rel′ argument-rel′ source-value)
application-right-evolves target-value = evolve-edge refl target-value

application-right-target-value : ∀ {Δᴸ Δᴿ Δᴿ′}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Σᴿ′ : TyStore Δᴿ′}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴿ′ : TermCtx Δᴿ′}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ′ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ′ , Σᴿ′ , Γᴿ′ ⟩}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {L″ M″ : Term Δᴿ′}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {A″ B″ : Ty Δᴿ′}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    {pA′ : A ⊑ᵀ⟨ γ′ ⟩ A″} {pB′ : B ⊑ᵀ⟨ γ′ ⟩ B″}
    {function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB}
    {argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA}
    {function-rel′ : γ′ CTI.⊢² L ⊑ L″ ∶ ⇒⊑⇒ pA′ pB′}
    {argument-rel′ : γ′ CTI.⊢² M ⊑ M″ ∶ pA′}
    {source-value : Value L}
  → TargetEdgeEvolution
      (focus-·₂ function-rel argument-rel source-value)
      (focus-·₂ function-rel′ argument-rel′ source-value)
  → Value L″
application-right-target-value evolution =
  TargetEdgeEvolution.target-edge-ready evolution


------------------------------------------------------------------------
-- Primitive-right: the same prerequisite is necessary and sufficient
------------------------------------------------------------------------

primitive-right-evolves : ∀ {Δᴸ Δᴿ Δᴿ′}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Σᴿ′ : TyStore Δᴿ′}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴿ′ : TermCtx Δᴿ′}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ′ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ′ , Σᴿ′ , Γᴿ′ ⟩}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {L″ M″ : Term Δᴿ′} {op : Prim}
    {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
    {p′ q′ : primArgTy op ⊑ᵀ⟨ γ′ ⟩ primArgTy op}
    {r : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op}
    {r′ : primResultTy op ⊑ᵀ⟨ γ′ ⟩ primResultTy op}
    {left-rel : γ CTI.⊢² L ⊑ L′ ∶ p}
    {right-rel : γ CTI.⊢² M ⊑ M′ ∶ q}
    {left-rel′ : γ′ CTI.⊢² L ⊑ L″ ∶ p′}
    {right-rel′ : γ′ CTI.⊢² M ⊑ M″ ∶ q′}
    {source-value : Value L}
  → Value L″
  → TargetEdgeEvolution
      (focus-⊕₂ left-rel right-rel r source-value)
      (focus-⊕₂ left-rel′ right-rel′ r′ source-value)
primitive-right-evolves target-value = evolve-edge refl target-value

primitive-right-target-value : ∀ {Δᴸ Δᴿ Δᴿ′}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Σᴿ′ : TyStore Δᴿ′}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴿ′ : TermCtx Δᴿ′}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ′ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ′ , Σᴿ′ , Γᴿ′ ⟩}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {L″ M″ : Term Δᴿ′} {op : Prim}
    {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
    {p′ q′ : primArgTy op ⊑ᵀ⟨ γ′ ⟩ primArgTy op}
    {r : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op}
    {r′ : primResultTy op ⊑ᵀ⟨ γ′ ⟩ primResultTy op}
    {left-rel : γ CTI.⊢² L ⊑ L′ ∶ p}
    {right-rel : γ CTI.⊢² M ⊑ M′ ∶ q}
    {left-rel′ : γ′ CTI.⊢² L ⊑ L″ ∶ p′}
    {right-rel′ : γ′ CTI.⊢² M ⊑ M″ ∶ q′}
    {source-value : Value L}
  → TargetEdgeEvolution
      (focus-⊕₂ left-rel right-rel r source-value)
      (focus-⊕₂ left-rel′ right-rel′ r′ source-value)
  → Value L″
primitive-right-target-value evolution =
  TargetEdgeEvolution.target-edge-ready evolution
