{-# OPTIONS --safe #-}

module proof.DGG.SimPairedFunClosingProof where

-- File Charter:
--   * Proves forward simulation for paired function roots after separately
--     catching up the target function and argument to related values.
--   * Is parameterized by CTI transport, target value catch-up, and the
--     value-level paired-function simulation induction.
--   * Contains no root classifier or residual-family interface.

open import Data.List using ([])
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; subst; trans)

open import Types using (Ty; TyCtx; _⇒_)
open import TyStore using (TyStore)
open import CastTerms using
  (Term; Value; _·_; ⟨_,_,_⟩; ƛ_; _《_》; _↑_; _↓_; fun)
open import Reduction
open import Imprecision using (⇒⊑⇒)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.CatchupToMorePreciseDef using
  (CatchupToMorePrecise)
open import proof.DGG.SimPairedFunClosingDef using
  (SimPairedFunClosingᵀ)
open import proof.DGG.SimPairedFunValuesDef using
  (SimPairedFunValuesᵀ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence
open import proof.Reduction
import proof.Imprecision as PI


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-to-more-precise : CatchupToMorePrecise)
    (sim-paired-fun-values : SimPairedFunValuesᵀ)
  where

  private
    close-root : ∀ {Δᴸ Δᴿ : TyCtx}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
        {L M N : Term Δᴸ} {L′ M′ : Term Δᴿ}
        {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
        {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
      → openFramesᶜ γ ≡ []
      → γ ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB
      → γ ⊢² M ⊑ M′ ∶ pA
      → Value L
      → Value M
      → L · M —→ N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ]
        Σ[ γ′ ∈
          ⟨ Δᴸ , applyStore keep Σᴸ , [] ⟩ ⊑ᶜ
          ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
        Σ[ q ∈ applyTy keep B ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
          (L′ · M′ —↠[ χsᴿ ] N′)
          × MultiWorldEvolution
              {W = γ} {W′ = γ′} (keep ∷ []) χsᴿ
          × (γ′ ⊢² N ⊑ N′ ∶ q)
    close-root {L = L} {M = M} {N = N} {L′ = L′} {M′ = M′}
        {A = A} {B = B} {A′ = A′} {B′ = B′}
        no-rebase fun-rel arg-rel source-fun-value source-arg-value source-step
        with catchup-to-more-precise no-rebase fun-rel source-fun-value
    close-root {L = L} {M = M} {N = N} {L′ = L′} {M′ = M′}
        {A = A} {B = B} {A′ = A′} {B′ = B′}
        no-rebase fun-rel arg-rel source-fun-value source-arg-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-fun , γ₁ , type-rel₁ ,
        fun-steps , target-fun-value , evolution₁ , fun-rel₁
        with catchup-to-more-precise
          (multi-no-open-frames evolution₁ no-rebase)
          (transport-CTI evolution₁ arg-rel) source-arg-value
    close-root {L = L} {M = M} {N = N} {L′ = L′} {M′ = M′}
        {A = A} {B = B} {A′ = A′} {B′ = B′}
        no-rebase fun-rel arg-rel source-fun-value source-arg-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-fun , γ₁ , type-rel₁ ,
        fun-steps , target-fun-value , evolution₁ , fun-rel₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-arg , γ₂ , type-rel₂ ,
        arg-steps , target-arg-value , evolution₂ , arg-rel₂
        with subst
          (λ T →
            Σ[ q ∈ (A ⇒ B) ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ ⊢² L ⊑ applyTerms χsᴿ₂ target-fun ∶ q)
          (trans (cong (applyTys χsᴿ₂) (applyTys-⇒ χsᴿ₁ A′ B′))
            (applyTys-⇒ χsᴿ₂ (applyTys χsᴿ₁ A′)
              (applyTys χsᴿ₁ B′)))
          (multi-⊑ᵀ evolution₂ type-rel₁ ,
            transport-CTI evolution₂ fun-rel₁)
    close-root {L = L} {M = M} {N = N} {L′ = L′} {M′ = M′}
        {A = A} {B = B} {A′ = A′} {B′ = B′}
        no-rebase fun-rel arg-rel source-fun-value source-arg-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-fun , γ₁ , type-rel₁ ,
        fun-steps , target-fun-value , evolution₁ , fun-rel₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-arg , γ₂ , type-rel₂ ,
        arg-steps , target-arg-value , evolution₂ , arg-rel₂
      | (⇒⊑⇒ argument-rel result-rel) , fun-rel₂
        with sim-paired-fun-values
          {pA = argument-rel} {pB = result-rel}
          (multi-no-open-frames evolution₂
            (multi-no-open-frames evolution₁ no-rebase))
          fun-rel₂
          (subst (λ q → γ₂ ⊢² M ⊑ target-arg ∶ q)
            (PI.⊑-unique type-rel₂ argument-rel) arg-rel₂)
          source-fun-value source-arg-value
          (applyTerms-preserves-Value χsᴿ₂ target-fun-value)
          target-arg-value source-step
    close-root {L = L} {M = M} {N = N} {L′ = L′} {M′ = M′}
        {B = B} {B′ = B′}
        no-rebase fun-rel arg-rel source-fun-value source-arg-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-fun , γ₁ , type-rel₁ ,
        fun-steps , target-fun-value , evolution₁ , fun-rel₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-arg , γ₂ , type-rel₂ ,
        arg-steps , target-arg-value , evolution₂ , arg-rel₂
      | (⇒⊑⇒ argument-rel result-rel) , fun-rel₂
      | Δᴿ₃ , Σᴿ₃ , χsᴿ₃ , result , γ₃ , root-result-rel ,
        root-steps , root-evolution , result-related
        with subst
          (λ T →
            Σ[ q ∈ applyTy keep B ⊑ᵀ⟨ γ₃ ⟩ T ]
              γ₃ ⊢² N ⊑ result ∶ q)
          (trans
            (applyTys-++ χsᴿ₂ χsᴿ₃ (applyTys χsᴿ₁ B′))
            (applyTys-++ χsᴿ₁ (χsᴿ₂ ++χ χsᴿ₃) B′))
          (root-result-rel , result-related)
    close-root {L = L} {M = M} {L′ = L′} {M′ = M′}
        no-rebase fun-rel arg-rel source-fun-value source-arg-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-fun , γ₁ , type-rel₁ ,
        fun-steps , target-fun-value , evolution₁ , fun-rel₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-arg , γ₂ , type-rel₂ ,
        arg-steps , target-arg-value , evolution₂ , arg-rel₂
      | (⇒⊑⇒ argument-rel result-rel) , fun-rel₂
      | Δᴿ₃ , Σᴿ₃ , χsᴿ₃ , result , γ₃ , root-result-rel ,
        root-steps , root-evolution , result-related
      | result-rel′ , result-related′ =
        Δᴿ₃ , Σᴿ₃ , χsᴿ₁ ++χ (χsᴿ₂ ++χ χsᴿ₃) ,
        result , γ₃ , result-rel′ ,
        (L′ · M′
          —↠+[ χsᴿ₁ ]⟨ appL-↠ fun-steps ⟩
         target-fun · applyTerms χsᴿ₁ M′
          —↠+[ χsᴿ₂ ]⟨ appR-↠ target-fun-value arg-steps ⟩
         applyTerms χsᴿ₂ target-fun · target-arg
          —↠[ χsᴿ₃ ]⟨ root-steps ⟩
         result ∎[]) ,
        composeMultiWorldEvolution evolution₁
          (composeMultiWorldEvolution evolution₂ root-evolution) ,
        result-related′

  sim-paired-fun-closing : SimPairedFunClosingᵀ
  sim-paired-fun-closing no-rebase fun-rel arg-rel
      source-fun-value source-arg-value (β root-arg-value) =
    close-root no-rebase fun-rel arg-rel
      source-fun-value source-arg-value (β root-arg-value)

  sim-paired-fun-closing no-rebase fun-rel arg-rel
      source-fun-value source-arg-value
      (β-⇒ root-fun-value root-arg-value) =
    close-root no-rebase fun-rel arg-rel source-fun-value source-arg-value
      (β-⇒ root-fun-value root-arg-value)

  sim-paired-fun-closing no-rebase fun-rel arg-rel
      source-fun-value source-arg-value
      (β-reveal-⇒ root-fun-value root-arg-value) =
    close-root no-rebase fun-rel arg-rel source-fun-value source-arg-value
      (β-reveal-⇒ root-fun-value root-arg-value)

  sim-paired-fun-closing no-rebase fun-rel arg-rel
      source-fun-value source-arg-value
      (β-conceal-⇒ root-fun-value root-arg-value) =
    close-root no-rebase fun-rel arg-rel source-fun-value source-arg-value
      (β-conceal-⇒ root-fun-value root-arg-value)
