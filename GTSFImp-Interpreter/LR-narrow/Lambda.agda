module LR-narrow.Lambda where

-- File Charter:
--   * Exposes lambda compatibility from a semantic body premise.
--   * Retains the lower-level function-elimination formulation.
--   * Exposes construction of the related function-body substitution.
--   * Keeps the compiled-term theorem statement at the public LR boundary.
--   * Delegates endpoint and step-index proof scripts to the proof namespace.

open import Data.List using (_∷_)
open import Data.Nat using (ℕ; suc; _≤_)

open import Types
open import CastTerms
import Imprecision as I
import proof.DGG.CtxImp as CTI
open import LR-narrow.World
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation
import proof.LR-narrow.Lambda as Proof

related-function-body-substitution : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁ : TyCtx}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂ : TyCtx}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {k j : ℕ} {Γ : ContextImprecision W₀} {Aᴾ Aᴵ}
    (W₀≼W₁ : Future W₀ W₁) (p : Aᴾ ⊑ᵂ⟨ core W₀ ⟩ Aᴵ)
  → RelatedClosingSubstitutions W₁ k
      (liftContextImprecision W₀≼W₁ Γ)
  → (W₁≼W₂ : Future W₁ W₂)
  → {Uᴵ : Term Δᴵ₂} {Uᴾ : Term Δᴾ₂}
  → suc j ≤ k
  → ValueImprecision W₂
      (liftCenterImprecision W₁≼W₂
        (liftCenterImprecision W₀≼W₁ p)) (suc j) Uᴵ Uᴾ
  → RelatedClosingSubstitutions W₂ j
      (liftContextImprecision (future-trans W₀≼W₁ W₁≼W₂)
        (context-imp Aᴾ Aᴵ p ∷ Γ))
related-function-body-substitution =
  Proof.related-function-body-substitution

functions-related-from-body : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ} {Nᴾ : Term Δᴾ} {Nᴵ : Term Δᴵ}
  → (∀ i → i ≤ k → CompiledTermRelation {W = W} q i
      (CTI.ctx-imp Aᴾ Aᴵ p ∷ Γ) Nᴾ Nᴵ)
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′ (compiledContext W Γ)))
      (j : ℕ)
  → j ≤ k
  → FunctionsRelated W′ (liftCenterImprecision W≼W′ p)
      (liftCenterImprecision W≼W′ q) j
      (close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ (ƛ Nᴵ)))
      (close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ (ƛ Nᴾ)))
functions-related-from-body = Proof.functions-related-from-body

lambda-compatible : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ} {Nᴾ : Term Δᴾ} {Nᴵ : Term Δᴵ}
  → ⟨ Δᴾ , preciseStore (core W) , CTI.srcCtxʷ Γ ⟩
      ⊢ ƛ Nᴾ ⦂ Aᴾ ⇒ Bᴾ
  → ⟨ Δᴵ , impreciseStore (core W) , CTI.tgtCtxʷ Γ ⟩
      ⊢ ƛ Nᴵ ⦂ Aᴵ ⇒ Bᴵ
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′ (compiledContext W Γ)))
      (j : ℕ)
    → j ≤ k
    → FunctionsRelated W′ (liftCenterImprecision W≼W′ p)
        (liftCenterImprecision W≼W′ q) j
        (close (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W≼W′ (ƛ Nᴵ)))
        (close (preciseClosingSubstitution γ)
          (liftPreciseTerm W≼W′ (ƛ Nᴾ))))
  → CompiledTermRelation {W = W} (I.⇒⊑⇒ p q) k Γ
      (ƛ Nᴾ) (ƛ Nᴵ)
lambda-compatible = Proof.lambda-compatible

lambda-compatible-from-body : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ} {Nᴾ : Term Δᴾ} {Nᴵ : Term Δᴵ}
  → ⟨ Δᴾ , preciseStore (core W) , CTI.srcCtxʷ Γ ⟩
      ⊢ ƛ Nᴾ ⦂ Aᴾ ⇒ Bᴾ
  → ⟨ Δᴵ , impreciseStore (core W) , CTI.tgtCtxʷ Γ ⟩
      ⊢ ƛ Nᴵ ⦂ Aᴵ ⇒ Bᴵ
  → (∀ i → i ≤ k → CompiledTermRelation {W = W} q i
      (CTI.ctx-imp Aᴾ Aᴵ p ∷ Γ) Nᴾ Nᴵ)
  → CompiledTermRelation {W = W} (I.⇒⊑⇒ p q) k Γ
      (ƛ Nᴾ) (ƛ Nᴵ)
lambda-compatible-from-body = Proof.lambda-compatible-from-body
