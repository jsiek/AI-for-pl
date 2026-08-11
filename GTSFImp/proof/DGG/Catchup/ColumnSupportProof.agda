module proof.DGG.Catchup.ColumnSupportProof where

-- File Charter:
--   * Proves the non-blocked M6 cast-column support lemmas stated in
--     ValueCatchupRightDef.
--   * Keeps the support proofs independent of the higher-order M4/M5 proof
--     implementations.
--   * Depends on core consistency/reduction, the value-catch-up Def surface,
--     and stage-1 DGG world-extension interfaces.

import Data.Fin as Fin
import Data.List as List
open import Data.Nat.Properties using (n<1+n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)
  renaming (subst to subst≡)

open import Types
open import CastTerms using (Term)
open import Reduction using
  (StoreChange; StoreChanges; _—→[_]_; _—↠[_]_; keep; bind;
   []; _∷_; ↠-refl; ↠-step; ξ-⟨⟩; applyConsistency;
   applyStore; applyTy; applyStores; applyTys)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_)
open import proof.DGG.Catchup.ValueCatchupRightDef
  using
    ( castSize; CastColumn; []ᶜ; _▻ᶜ_; columnSize; applyColumn
    ; mapColumn₁; mapColumn; _++χ_
    ; ground-other-decreaseᵀ; project-expand-decreaseᵀ
    ; composeWorldExtendᴿᵀ; mapCtxᴿ-composeᵀ
    ; composeReductionᵀ; liftReductionThroughColumnᵀ
    )

------------------------------------------------------------------------
-- Strict-decrease one-step obligations that do not allocate
------------------------------------------------------------------------

ground-other-decrease : ground-other-decreaseᵀ
ground-other-decrease c = n<1+n (castSize c)

project-expand-decrease : project-expand-decreaseᵀ
project-expand-decrease c = n<1+n (castSize c)

------------------------------------------------------------------------
-- Store-change append algebra
------------------------------------------------------------------------

applyStores-++ : ∀ {Δ₀ Δ₁ Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → ∀ Σ
  → applyStores ψs (applyStores χs Σ) ≡ applyStores (χs ++χ ψs) Σ
applyStores-++ [] ψs Σ = refl
applyStores-++ (χ ∷ χs) ψs Σ =
  applyStores-++ χs ψs (applyStore χ Σ)

applyTys-++ : ∀ {Δ₀ Δ₁ Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → ∀ A
  → applyTys ψs (applyTys χs A) ≡ applyTys (χs ++χ ψs) A
applyTys-++ [] ψs A = refl
applyTys-++ (χ ∷ χs) ψs A = applyTys-++ χs ψs (applyTy χ A)

composeWorldExtendᴿ : composeWorldExtendᴿᵀ
composeWorldExtendᴿ {χs = χs} {ψs = ψs} {W₀ = W₀} {W₂ = W₂}
    ext₁ ext₂ =
  record
    { sourceStore-kept =
        trans (ECR.sourceStore-kept ext₂) (ECR.sourceStore-kept ext₁)
    ; targetStore-follows =
        trans (ECR.targetStore-follows ext₂)
          (trans
            (cong (applyStores ψs) (ECR.targetStore-follows ext₁))
            (applyStores-++ χs ψs (CTI2.targetStoreʷ W₀)))
    ; transport⊑ᵂ = λ {A = A} {C = C} p →
        subst≡ (λ C′ → A ⊑ᵂ⟨ W₂ ⟩ C′)
          (applyTys-++ χs ψs C)
          (ECR.transport⊑ᵂ ext₂ (ECR.transport⊑ᵂ ext₁ p))
    }

ctx-imp-transportᴿ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → (eq : B ≡ B′)
  → (p : A ⊑ᵂ⟨ W ⟩ B)
  → CTI2.ctx-imp {W = W} A B p ≡
    CTI2.ctx-imp {W = W} A B′
      (subst≡ (λ C → A ⊑ᵂ⟨ W ⟩ C) eq p)
ctx-imp-transportᴿ refl p = refl

mapCtxᴿ-compose : mapCtxᴿ-composeᵀ composeWorldExtendᴿ
mapCtxᴿ-compose ext₁ ext₂ List.[] = refl
mapCtxᴿ-compose {χs = χs} {ψs = ψs} {W₂ = W₂} ext₁ ext₂
    (CTI2.ctx-imp A B p List.∷ γ) =
  cong₂ List._∷_
    (ctx-imp-transportᴿ {W = W₂} (applyTys-++ χs ψs B)
      (ECR.transport⊑ᵂ ext₂ (ECR.transport⊑ᵂ ext₁ p)))
    (mapCtxᴿ-compose ext₁ ext₂ γ)

------------------------------------------------------------------------
-- Store-changing trace composition and column lifting
------------------------------------------------------------------------

composeReduction : composeReductionᵀ
composeReduction ↠-refl N↠P = N↠P
composeReduction (↠-step M→N N↠P) P↠Q =
  ↠-step M→N (composeReduction N↠P P↠Q)

liftStepThroughColumn : ∀ {Δ Δ′} {A B : Ty Δ}
    {χ : StoreChange Δ Δ′} {M : Term Δ} {N : Term Δ′}
  → (κ : CastColumn A B)
  → M —→[ χ ] N
  → applyColumn M κ —→[ χ ] applyColumn N (mapColumn₁ χ κ)
liftStepThroughColumn []ᶜ M→N = M→N
liftStepThroughColumn (c ▻ᶜ κ) M→N =
  liftStepThroughColumn κ (ξ-⟨⟩ M→N refl)

liftReductionThroughColumn : liftReductionThroughColumnᵀ
liftReductionThroughColumn κ ↠-refl = ↠-refl
liftReductionThroughColumn κ (↠-step M→N N↠P) =
  ↠-step (liftStepThroughColumn κ M→N)
    (liftReductionThroughColumn (mapColumn₁ _ κ) N↠P)
