module proof.DGG.Catchup.InstCatchupRightDef where

-- File Charter:
--   * States checked auxiliary surfaces for the right-instantiation
--     catch-up milestone.
--   * Keeps the concrete right-only bind extensions and per-view allocation
--     redexes separate from the full relational driver.
--   * Depends on the stage-1 ExtraCastRight2 interface, core reduction,
--     and the shared target value-spine view.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; extᵐ; instᵐ; genᵐ; ∀ᶜ_; inst_; gen_;
   ↑ᶜ_; close-instᶜ; _[_]ᶜ)
open import Conversion using
  (Conv↑; Conv↓; `∀↑_; `∀↓_; 〖_,_↑_〗)
open import CastTerms using
  (Term; Value; GenSafe; _⟨_⟩; _⦂∀_[_]; _↑_; _↓_; Λ_; ⇑ᵗᵐ)
open import Reduction using
  (StoreChanges; _—↠[_]_; []; _∷_; bind; keep; applyBody)

import proof.DGG.CtxImp as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open CTI2 using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)


RightBindWorldExtendᴿᵀ : Set
RightBindWorldExtendᴿᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ECR.WorldExtendᴿ (bind B ∷ []) W (CTI2.rightOnlyWorld W B)


RightBindKeepWorldExtendᴿᵀ : Set
RightBindKeepWorldExtendᴿᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ECR.WorldExtendᴿ
      (bind B ∷ keep ∷ []) W (CTI2.rightOnlyWorld W B)


RightBindRightBindWorldExtendᴿᵀ : Set
RightBindRightBindWorldExtendᴿᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {B : Ty Δᴿ} {C : Ty (suc Δᴿ)}
  → ECR.WorldExtendᴿ (bind B ∷ bind C ∷ []) W
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W B) C)


RightBindTransport⊑ᵂᵀ : Set
RightBindTransport⊑ᵂᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ CTI2.rightOnlyWorld W B′ ⟩ ⇑ᵗ B


RightBindMapCtxᴿᵀ : Set
RightBindMapCtxᴿᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → CtxImp W
  → CtxImp (CTI2.rightOnlyWorld W B)


InstCastAllocPrefixᵀ : Set
InstCastAllocPrefixᵀ =
  ∀ {Δ} {V : Term Δ} {ν : Env∼ Δ}
    {A : Ty (suc Δ)} {B : Ty Δ}
    {c : instᵐ ν ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
  → Value V
  → (B≢★ : B ≢ ★)
  → V ⟨ (inst c) B≢★ ⟩ —↠[ bind ★ ∷ [] ]
      (⇑ᵗᵐ V ⦂∀ applyBody (bind ★) A [ ＇ Fin.zero ] ↑
        〖 Fin.zero , ★ ↑ A 〗 ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩)


TypeAppΛStepᵀ : Set
TypeAppΛStepᵀ =
  ∀ {Δ} {A : Ty Δ} {B : Ty (suc Δ)} {V : Term (suc Δ)}
  → Value V
  → (Λ V) ⦂∀ B [ A ] —↠[ bind A ∷ [] ]
      (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)


TypeApp∀Stepᵀ : Set
TypeApp∀Stepᵀ =
  ∀ {Δ} {D : Ty Δ} {A B : Ty (suc Δ)}
    {V : Term Δ} {ν : Env∼ Δ} {c : extᵐ ν ⊢ A ∼ B}
  → Value V
  → (V ⟨ ∀ᶜ c ⟩) ⦂∀ B [ D ] —↠[ keep ∷ [] ]
      ((V ⦂∀ A [ D ]) ⟨ c [ D ]ᶜ ⟩)


TypeAppGenStepᵀ : Set
TypeAppGenStepᵀ =
  ∀ {Δ} {A C : Ty Δ} {B : Ty (suc Δ)}
    {V : Term Δ} {ν : Env∼ Δ}
    {c : genᵐ ν ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
  → Value V
  → (A≢★ : A ≢ ★)
  → GenSafe c
  → (V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —↠[ bind C ∷ [] ]
      (⇑ᵗᵐ V ⟨ c ⟩ ↑ 〖 Fin.zero , ⇑ᵗ C ↑ B 〗)


TypeAppRevealStepᵀ : Set
TypeAppRevealStepᵀ =
  ∀ {Δ} {A : Ty Δ} {B C : Ty (suc Δ)}
    {V : Term Δ} {c : Conv↑ (suc Δ) C B}
  → Value V
  → (V ↑ `∀↑ c) ⦂∀ B [ A ] —↠[ bind A ∷ [] ]
      (((⇑ᵗᵐ V ⦂∀ applyBody (bind A) C [ ＇ Fin.zero ]) ↑ c)
        ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)


TypeAppConcealStepᵀ : Set
TypeAppConcealStepᵀ =
  ∀ {Δ} {A : Ty Δ} {B C : Ty (suc Δ)}
    {V : Term Δ} {c : Conv↓ (suc Δ) C B}
  → Value V
  → (V ↓ `∀↓ c) ⦂∀ B [ A ] —↠[ bind A ∷ [] ]
      ((⇑ᵗᵐ V ⦂∀ applyBody (bind A) C [ ＇ Fin.zero ] ↓ c)
        ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)


AllValueViewStepCatalogᵀ : Set
AllValueViewStepCatalogᵀ =
  TypeAppΛStepᵀ × TypeApp∀Stepᵀ × TypeAppGenStepᵀ ×
  TypeAppRevealStepᵀ × TypeAppConcealStepᵀ
