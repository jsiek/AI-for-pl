{-# OPTIONS --safe #-}

module proof.DGG.SimBackPairedFunClosingProof where

-- File Charter:
--   * Proves backward simulation for paired function roots after separately
--     catching up the source function and argument to related values.
--   * Is parameterized by CTI transport, source value catch-up, and the
--     value-level paired-function inversion induction.
--   * Contains no root classifier or residual-family interface.

open import Data.List using ([])
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; trans)

open import Types using (Ty; TyCtx; _⇒_)
open import TyStore using (TyStore)
open import CastTerms using
  (Term; Value; blame; _·_; ⟨_,_,_⟩; ƛ_; _《_》; _↑_; _↓_; fun)
open import Reduction
open import Imprecision using (⇒⊑⇒)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.CatchupToLessPreciseDef using
  (CatchupToLessPrecise)
open import proof.DGG.SimBackPairedFunClosingDef using
  (SimBackPairedFunClosingᵀ)
open import proof.DGG.SimBackPairedFunValuesDef using
  (SimBackPairedFunValuesᵀ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence
open import proof.Reduction
import proof.Imprecision as PI


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-to-less-precise : CatchupToLessPrecise)
    (sim-back-paired-fun-values : SimBackPairedFunValuesᵀ)
  where

  private
    close-root : ∀ {Δᴸ Δᴿ : TyCtx}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
        {L M : Term Δᴸ} {L′ M′ N′ : Term Δᴿ}
        {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
        {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
      → sourceRebaseCountᶜ γ ≡ 0
      → γ ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB
      → γ ⊢² M ⊑ M′ ∶ pA
      → Value L′
      → Value M′
      → L′ · M′ —→ N′
      → (Σ[ Δᴸ′ ∈ TyCtx ]
          Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
          Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
          Σ[ N ∈ Term Δᴸ′ ]
          Σ[ γ′ ∈
            ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
            ⟨ Δᴿ , applyStore keep Σᴿ , [] ⟩ ]
          Σ[ q ∈ applyTys χsᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTy keep B′ ]
            (L · M —↠[ χsᴸ ] N)
            × MultiWorldEvolution
                {W = γ} {W′ = γ′} χsᴸ (keep ∷ [])
            × (γ′ ⊢² N ⊑ N′ ∶ q))
        ⊎ (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
            (L · M —↠[ χsᴸ ] blame))
    close-root {L = L} {M = M} {L′ = L′} {M′ = M′} {N′ = N′}
        {A = A} {B = B} {A′ = A′} {B′ = B′}
        no-rebase fun-rel arg-rel target-fun-value target-arg-value target-step
        with catchup-to-less-precise no-rebase fun-rel target-fun-value
    close-root {L = L} {M = M} {L′ = L′} {M′ = M′} {N′ = N′}
        {A = A} {B = B} {A′ = A′} {B′ = B′}
        no-rebase fun-rel arg-rel target-fun-value target-arg-value target-step
      | inj₂
          (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , source-blame , evolution) =
        inj₂
          (Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
            (L · M
              —↠+[ χsᴸ ]⟨ appL-↠ source-blame ⟩
             blame · applyTerms χsᴸ M
              —→[ keep ]⟨ pure-step blame-·₁ ⟩
             blame ∎[]))
    close-root {L = L} {M = M} {L′ = L′} {M′ = M′} {N′ = N′}
        {A = A} {B = B} {A′ = A′} {B′ = B′}
        no-rebase fun-rel arg-rel target-fun-value target-arg-value target-step
      | inj₁
          (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-fun , γ₁ , type-rel₁ ,
            fun-steps , source-fun-value , evolution₁ , fun-rel₁)
        with catchup-to-less-precise
          (multi-no-source-rebase evolution₁ no-rebase)
          (transport-CTI no-rebase evolution₁ arg-rel) target-arg-value
    close-root {L = L} {M = M} {L′ = L′} {M′ = M′} {N′ = N′}
        {A = A} {B = B} {A′ = A′} {B′ = B′}
        no-rebase fun-rel arg-rel target-fun-value target-arg-value target-step
      | inj₁
          (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-fun , γ₁ , type-rel₁ ,
            fun-steps , source-fun-value , evolution₁ , fun-rel₁)
      | inj₂
          (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , γ₂ , argument-blame , evolution₂) =
        inj₂
          (Δᴸ₂ , χsᴸ₁ ++χ (χsᴸ₂ ++χ (keep ∷ [])) ,
            (L · M
              —↠+[ χsᴸ₁ ]⟨ appL-↠ fun-steps ⟩
             source-fun · applyTerms χsᴸ₁ M
              —↠+[ χsᴸ₂ ]⟨ appR-↠ source-fun-value argument-blame ⟩
             applyTerms χsᴸ₂ source-fun · blame
              —→[ keep ]⟨ pure-step
                (blame-·₂
                  (applyTerms-preserves-Value χsᴸ₂ source-fun-value)) ⟩
             blame ∎[]))
    close-root {L = L} {M = M} {L′ = L′} {M′ = M′} {N′ = N′}
        {A = A} {B = B}
        {A′ = A′} {B′ = B′} no-rebase fun-rel arg-rel
        target-fun-value target-arg-value target-step
      | inj₁
          (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-fun , γ₁ , type-rel₁ ,
            fun-steps , source-fun-value , evolution₁ , fun-rel₁)
      | inj₁
          (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , source-arg , γ₂ , type-rel₂ ,
            arg-steps , source-arg-value , evolution₂ , arg-rel₂)
        with subst
          (λ S →
            Σ[ q ∈ S ⊑ᵀ⟨ γ₂ ⟩ (A′ ⇒ B′) ]
              γ₂ ⊢² applyTerms χsᴸ₂ source-fun ⊑ L′ ∶ q)
          (trans (cong (applyTys χsᴸ₂) (applyTys-⇒ χsᴸ₁ A B))
            (applyTys-⇒ χsᴸ₂ (applyTys χsᴸ₁ A)
              (applyTys χsᴸ₁ B)))
          (multi-⊑ᵀ evolution₂ type-rel₁ ,
            transport-CTI
              (multi-no-source-rebase evolution₁ no-rebase)
              evolution₂ fun-rel₁)
    close-root {L = L} {M = M} {L′ = L′} {M′ = M′} {N′ = N′}
        {A = A} {B = B}
        {A′ = A′} {B′ = B′} no-rebase fun-rel arg-rel
        target-fun-value target-arg-value target-step
      | inj₁
          (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-fun , γ₁ , type-rel₁ ,
            fun-steps , source-fun-value , evolution₁ , fun-rel₁)
      | inj₁
          (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , source-arg , γ₂ , type-rel₂ ,
            arg-steps , source-arg-value , evolution₂ , arg-rel₂)
      | (⇒⊑⇒ argument-rel result-rel) , fun-rel₂
        with sim-back-paired-fun-values
          (multi-no-source-rebase evolution₂
            (multi-no-source-rebase evolution₁ no-rebase))
          fun-rel₂
          (subst (λ q → γ₂ ⊢² source-arg ⊑ M′ ∶ q)
            (PI.⊑-unique type-rel₂ argument-rel) arg-rel₂)
          (applyTerms-preserves-Value χsᴸ₂ source-fun-value)
          source-arg-value target-fun-value target-arg-value target-step
    close-root {L = L} {M = M} {L′ = L′} {M′ = M′} {N′ = N′}
        {A = A} {B = B}
        {A′ = A′} {B′ = B′} no-rebase fun-rel arg-rel
        target-fun-value target-arg-value target-step
      | inj₁
          (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-fun , γ₁ , type-rel₁ ,
            fun-steps , source-fun-value , evolution₁ , fun-rel₁)
      | inj₁
          (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , source-arg , γ₂ , type-rel₂ ,
            arg-steps , source-arg-value , evolution₂ , arg-rel₂)
      | (⇒⊑⇒ argument-rel result-rel) , fun-rel₂
      | inj₂ (Δᴸ₃ , χsᴸ₃ , root-blame) =
        inj₂
          (Δᴸ₃ , χsᴸ₁ ++χ (χsᴸ₂ ++χ χsᴸ₃) ,
            (L · M
              —↠+[ χsᴸ₁ ]⟨ appL-↠ fun-steps ⟩
             source-fun · applyTerms χsᴸ₁ M
              —↠+[ χsᴸ₂ ]⟨ appR-↠ source-fun-value arg-steps ⟩
             applyTerms χsᴸ₂ source-fun · source-arg
              —↠[ χsᴸ₃ ]⟨ root-blame ⟩
             blame ∎[]))

    close-root {L = L} {M = M} {L′ = L′} {M′ = M′} {N′ = N′}
        {A = A} {B = B}
        {A′ = A′} {B′ = B′} no-rebase fun-rel arg-rel
        target-fun-value target-arg-value target-step
      | inj₁
          (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-fun , γ₁ , type-rel₁ ,
            fun-steps , source-fun-value , evolution₁ , fun-rel₁)
      | inj₁
          (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , source-arg , γ₂ , type-rel₂ ,
            arg-steps , source-arg-value , evolution₂ , arg-rel₂)
      | (⇒⊑⇒ argument-rel result-rel) , fun-rel₂
      | inj₁
          (Δᴸ₃ , Σᴸ₃ , χsᴸ₃ , result , γ₃ , root-result-rel ,
            root-steps , root-evolution , result-related)
        with subst
          (λ S →
            Σ[ q ∈ S ⊑ᵀ⟨ γ₃ ⟩ B′ ] γ₃ ⊢² result ⊑ N′ ∶ q)
          (trans
            (applyTys-++ χsᴸ₂ χsᴸ₃ (applyTys χsᴸ₁ B))
            (applyTys-++ χsᴸ₁ (χsᴸ₂ ++χ χsᴸ₃) B))
          (root-result-rel , result-related)
    close-root {L = L} {M = M} {L′ = L′} {M′ = M′} {N′ = N′}
        no-rebase fun-rel arg-rel
        target-fun-value target-arg-value target-step
      | inj₁
          (Δᴸ₁ , Σᴸ₁ , χsᴸ₁ , source-fun , γ₁ , type-rel₁ ,
            fun-steps , source-fun-value , evolution₁ , fun-rel₁)
      | inj₁
          (Δᴸ₂ , Σᴸ₂ , χsᴸ₂ , source-arg , γ₂ , type-rel₂ ,
            arg-steps , source-arg-value , evolution₂ , arg-rel₂)
      | (⇒⊑⇒ argument-rel result-rel) , fun-rel₂
      | inj₁
          (Δᴸ₃ , Σᴸ₃ , χsᴸ₃ , result , γ₃ , root-result-rel ,
            root-steps , root-evolution , result-related)
      | result-rel′ , result-related′ =
        inj₁
          (Δᴸ₃ , Σᴸ₃ , χsᴸ₁ ++χ (χsᴸ₂ ++χ χsᴸ₃) ,
            result , γ₃ , result-rel′ ,
            (L · M
              —↠+[ χsᴸ₁ ]⟨ appL-↠ fun-steps ⟩
             source-fun · applyTerms χsᴸ₁ M
              —↠+[ χsᴸ₂ ]⟨ appR-↠ source-fun-value arg-steps ⟩
             applyTerms χsᴸ₂ source-fun · source-arg
              —↠[ χsᴸ₃ ]⟨ root-steps ⟩
             result ∎[]) ,
            composeMultiWorldEvolution evolution₁
              (composeMultiWorldEvolution evolution₂ root-evolution) ,
            result-related′)

  sim-back-paired-fun-closing : SimBackPairedFunClosingᵀ
  sim-back-paired-fun-closing no-rebase fun-rel arg-rel
      target-fun-value target-arg-value (β root-arg-value) =
    close-root no-rebase fun-rel arg-rel
      target-fun-value target-arg-value (β root-arg-value)

  sim-back-paired-fun-closing no-rebase fun-rel arg-rel
      target-value target-arg-value
      (β-⇒ root-fun-value root-arg-value) =
    close-root no-rebase fun-rel arg-rel
      target-value target-arg-value
      (β-⇒ root-fun-value root-arg-value)

  sim-back-paired-fun-closing no-rebase fun-rel arg-rel
      target-value target-arg-value
      (β-reveal-⇒ root-fun-value root-arg-value) =
    close-root no-rebase fun-rel arg-rel
      target-value target-arg-value
      (β-reveal-⇒ root-fun-value root-arg-value)

  sim-back-paired-fun-closing no-rebase fun-rel arg-rel
      target-value target-arg-value
      (β-conceal-⇒ root-fun-value root-arg-value) =
    close-root no-rebase fun-rel arg-rel
      target-value target-arg-value
      (β-conceal-⇒ root-fun-value root-arg-value)
