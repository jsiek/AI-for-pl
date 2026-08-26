{-# OPTIONS --safe #-}

module proof.DGG.SimBackTargetRevealRebaseFunValuesProof where

-- File Charter:
--   * Develops backward simulation for application of a target arrow reveal
--     whose payload relation lives beneath one source-rebase change.
--   * Is parameterized alongside the enclosing backward-simulation proof.
--   * Rebuilds the distributed domain conceal and result reveal directly
--     beneath the same source rebase.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl)

open import Types using (Ty; TyCtx; ＇_; _⇒_)
open import TyStore using (TyStore; lookupStore)
open import Consistency using (toRenameᵗ)
open import Conversion using (Conv↑; Conv↓; _↦↑_; _⊢↑[_⦂_]_)
import Conversion as Conv
open import CastTerms using
  (Term; Value; blame; ⟨_,_,_⟩; _·_; _↑_; _↓_)
open import Reduction using
  ( StoreChanges; applyStore; applyTy; applyTys; keep; _—↠[_]_
  ; _∎[]
  )
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Imprecision using (⇒⊑⇒)
open import proof.DGG.CastTermImprecision
open import proof.DGG.CatchupToLessPreciseDef using
  (CatchupToLessPrecise)
open import proof.DGG.SimBackRebasedConversionDef using
  (SimBackTargetRevealRebaseFunValuesᵀ)
open import proof.DGG.TermImprecisionSubstitutionDef using
  (TermImprecisionSubstitutionᵀ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution
  ; evolutions-refl
  ; evolutions-step-right
  )

module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-to-less-precise : CatchupToLessPrecise)
    (term-imprecision-substitution : TermImprecisionSubstitutionᵀ)
  where

  private
    worker : ∀ {Deltaᴸ Deltaᴿ : TyCtx}
        {Σᴸ : TyStore Deltaᴸ} {Σᴿ : TyStore Deltaᴿ}
        {γ : ⟨ Deltaᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Deltaᴿ , Σᴿ , [] ⟩}
        {γᵖ : ⟨ Deltaᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Deltaᴿ , Σᴿ , [] ⟩}
        {V W : Term Deltaᴸ} {V′ W′ : Term Deltaᴿ}
        {A B : Ty Deltaᴸ} {A₀ B₀ A′ B′ Rᴿ : Ty Deltaᴿ}
        {Xᴸ : Fin.Fin Deltaᴸ} {Xᴿ : Fin.Fin Deltaᴿ}
        {c : Conv↓ Deltaᴿ A′ A₀} {d : Conv↑ Deltaᴿ B₀ B′}
        {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
        {pAᵖ : A ⊑ᵀ⟨ γᵖ ⟩ A₀} {pBᵖ : B ⊑ᵀ⟨ γᵖ ⟩ B₀}
      → sourceRebaseCountᶜ γ ≡ 0
      → (conversion : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] (c ↦↑ d))
      → (ok : CanRebaseSourceᵗ
          (ηᴸᶜ γ) Xᴸ (toRenameᵗ (ηᴿᶜ γ) Xᴿ))
      → (represented :
          (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Xᴿ)
      → γᵖ ≡
          γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented
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
    worker {Σᴸ = Σᴸ} {γ = γ} {V = V} {W = W} {pB = pB}
        no-rebase
        (Conv.⊢↑-⇒ target-domain⊢ target-result⊢)
        ok represented refl body-rel arg-rel
        source-fun-value source-arg-value target-fun-value
        target-arg-value =
      inj₁
        (_ , Σᴸ , []ˢ , V · W , γ , pB ,
          (V · W ∎[]) ,
          evolutions-step-right refl evolution-keep evolutions-refl ,
          ⊑reveal-rebase² target-result⊢ ok represented
            (·⊑·² body-rel
              (⊑conceal-rebase² target-domain⊢ ok represented arg-rel _))
            pB)

  sim-back-target-reveal-rebase-fun-values :
    SimBackTargetRevealRebaseFunValuesᵀ
  sim-back-target-reveal-rebase-fun-values {pB = pB} no-rebase
      conversion ok represented premise-argument-rel
      premise-result-rel body-rel arg-rel
      source-fun-value source-arg-value target-fun-value
      target-arg-value =
    worker {pB = pB} {pAᵖ = premise-argument-rel}
      {pBᵖ = premise-result-rel}
      no-rebase conversion ok represented refl body-rel arg-rel
      source-fun-value source-arg-value target-fun-value target-arg-value
