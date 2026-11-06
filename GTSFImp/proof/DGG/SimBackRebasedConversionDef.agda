{-# OPTIONS --safe #-}

module proof.DGG.SimBackRebasedConversionDef where

-- File Charter:
--   * States backward simulation for paired reveal roots and the target
--     reveal-rebase root, function-value, and frame cases.
--   * Exposes the exact canonical CTI evidence and repeats the complete
--     SimBack conclusion without an action, classifier, or result wrapper.
--   * Is separated because its recursive relation lives one source-rebase
--     change beneath the enclosing no-rebase world.
--   * Contains no target reveal-rebase simulation proof.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; ＇_; _⇒_)
open import TyStore using (TyStore; lookupStore)
open import Consistency using (toRenameᵗ)
open import Conversion using (Conv↑; Conv↓; _↦↑_; _⊢↑[_⦂_]_)
import Conversion as Conv
open import CastTerms using
  (Term; Value; blame; ⟨_,_,_⟩; _·_; _↑_; _↓_)
open import Imprecision using (⇒⊑⇒)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyStore
  ; applyTy
  ; applyTys
  ; applyVar
  ; keep
  ; _—→_
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition)
open import proof.DGG.World
open import proof.DGG.SourceRebase
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


SimBackPairedRevealClosingᵀ : Set
SimBackPairedRevealClosingᵀ =
  ∀ {Deltaᴸ Deltaᴿ : TyCtx}
    {Σᴸ : TyStore Deltaᴸ} {Σᴿ : TyStore Deltaᴿ}
    {γ : ⟨ Deltaᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Deltaᴿ , Σᴿ , [] ⟩}
    {M : Term Deltaᴸ} {M′ N′ : Term Deltaᴿ}
    {A B : Ty Deltaᴸ} {A′ B′ : Ty Deltaᴿ}
    {Xᴸ : Fin.Fin Deltaᴸ} {Xᴿ : Fin.Fin Deltaᴿ}
    {Rᴸ : Ty Deltaᴸ} {Rᴿ : Ty Deltaᴿ}
    {c : Conv↑ Deltaᴸ A B} {c′ : Conv↑ Deltaᴿ A′ B′}
  → openFramesᶜ γ ≡ []
  → (c⊢ : Σᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
  → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡ toRenameⁱ (ηᴿᶜ γ) Xᴿ
  → Rᴸ ⊑ᵀ⟨ γ ⟩ Rᴿ
  → {p : A ⊑ᵀ⟨ γ ⟩ A′}
  → γ ⊢² M ⊑ M′ ∶ p
  → (q : B ⊑ᵀ⟨ γ ⟩ B′)
  → M′ ↑ c′ —→ N′
  → ( Σ[ Deltaᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Deltaᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Deltaᴸ Deltaᴸ′ ]
      Σ[ N ∈ Term Deltaᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Deltaᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Deltaᴿ , applyStore keep Σᴿ , [] ⟩ ]
      Σ[ r ∈ applyTys χsᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTy keep B′ ]
        (M ↑ c —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (keep ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ N′ ∶ r))
    ⊎ (∃[ Deltaᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Deltaᴸ Deltaᴸ′ ]
        (M ↑ c —↠[ χsᴸ ] blame))


SimBackTargetRevealRebaseClosingᵀ : Set
SimBackTargetRevealRebaseClosingᵀ =
  ∀ {Deltaᴸ Deltaᴿ : TyCtx}
    {Σᴸ : TyStore Deltaᴸ} {Σᴿ : TyStore Deltaᴿ}
    {γ : ⟨ Deltaᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Deltaᴿ , Σᴿ , [] ⟩}
    {γᵖ : ⟨ Deltaᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Deltaᴿ , Σᴿ , [] ⟩}
    {M : Term Deltaᴸ} {M′ N′ : Term Deltaᴿ}
    {A : Ty Deltaᴸ} {B B′ Rᴿ : Ty Deltaᴿ}
    {Xᴸ : Fin.Fin Deltaᴸ} {Xᴿ : Fin.Fin Deltaᴿ}
    {c′ : Conv↑ Deltaᴿ B B′}
  → openFramesᶜ γ ≡ []
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
  → γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → M′ ↑ c′ —→ N′
  → ( Σ[ Deltaᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Deltaᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Deltaᴸ Deltaᴸ′ ]
      Σ[ N ∈ Term Deltaᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Deltaᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Deltaᴿ , applyStore keep Σᴿ , [] ⟩ ]
      Σ[ r ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTy keep B′ ]
        (M —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (keep ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ N′ ∶ r))
    ⊎ (∃[ Deltaᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Deltaᴸ Deltaᴸ′ ]
        (M —↠[ χsᴸ ] blame))


SimBackTargetRevealRebaseFunValuesᵀ : Set
SimBackTargetRevealRebaseFunValuesᵀ =
  ∀ {Deltaᴸ Deltaᴿ : TyCtx}
    {Σᴸ : TyStore Deltaᴸ} {Σᴿ : TyStore Deltaᴿ}
    {γ : ⟨ Deltaᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Deltaᴿ , Σᴿ , [] ⟩}
    {γᵖ : ⟨ Deltaᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Deltaᴿ , Σᴿ , [] ⟩}
    {V W : Term Deltaᴸ} {V′ W′ : Term Deltaᴿ}
    {A B : Ty Deltaᴸ} {A₀ B₀ A′ B′ Rᴿ : Ty Deltaᴿ}
    {Xᴸ : Fin.Fin Deltaᴸ} {Xᴿ : Fin.Fin Deltaᴿ}
    {c : Conv↓ Deltaᴿ A′ A₀} {d : Conv↑ Deltaᴿ B₀ B′}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
  → openFramesᶜ γ ≡ []
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] (c ↦↑ d))
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → (pAᵖ : A ⊑ᵀ⟨ γᵖ ⟩ A₀)
  → (pBᵖ : B ⊑ᵀ⟨ γᵖ ⟩ B₀)
  → γᵖ ⊢² V ⊑ V′ ∶ ⇒⊑⇒ pAᵖ pBᵖ
  → γ ⊢² W ⊑ W′ ∶ pA
  → Value V
  → Value W
  → Value V′
  → Value W′
  → ( Σ[ Deltaᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Deltaᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Deltaᴸ Deltaᴸ′ ]
      Σ[ N ∈ Term Deltaᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Deltaᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Deltaᴿ , applyStore keep Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTy keep B′ ]
        (V · W —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (keep ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑ (V′ · (W′ ↓ c)) ↑ d ∶ q))
    ⊎ (∃[ Deltaᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Deltaᴸ Deltaᴸ′ ]
        (V · W —↠[ χsᴸ ] blame))


SimBackTargetRevealRebaseFrameᵀ : Set
SimBackTargetRevealRebaseFrameᵀ =
  ∀ {Deltaᴸ Deltaᴿ Deltaᴿ′ : TyCtx}
    {Σᴸ : TyStore Deltaᴸ} {Σᴿ : TyStore Deltaᴿ}
    {γ : ⟨ Deltaᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Deltaᴿ , Σᴿ , [] ⟩}
    {γᵖ : ⟨ Deltaᴸ , Σᴸ , [] ⟩ ⊑ᶜ
      ⟨ Deltaᴿ , Σᴿ , [] ⟩}
    {M : Term Deltaᴸ} {M′ : Term Deltaᴿ} {N′ : Term Deltaᴿ′}
    {A : Ty Deltaᴸ} {B B′ Rᴿ : Ty Deltaᴿ}
    {Xᴸ : Fin.Fin Deltaᴸ} {Xᴿ : Fin.Fin Deltaᴿ}
    {c′ : Conv↑ Deltaᴿ B B′} {χᴿ : StoreChange Deltaᴿ Deltaᴿ′}
  → openFramesᶜ γ ≡ []
  → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
  → γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → M′ —→[ χᴿ ] N′
  → ( Σ[ Deltaᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Deltaᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Deltaᴸ Deltaᴸ′ ]
      Σ[ N ∈ Term Deltaᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Deltaᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Deltaᴿ′ , applyStore χᴿ Σᴿ , [] ⟩ ]
      Σ[ r ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTy χᴿ B′ ]
        (M —↠[ χsᴸ ] N)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} χsᴸ (χᴿ ∷ˢ []ˢ)
        × (γ′ ⊢² N ⊑
          N′ ↑ Conv.rename↑ (applyVar χᴿ) c′ ∶ r))
    ⊎ (∃[ Deltaᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Deltaᴸ Deltaᴸ′ ]
        (M —↠[ χsᴸ ] blame))
