{-# OPTIONS --safe #-}

module proof.DGG.SimSourceAllClosingProof where

-- File Charter:
--   * Proves forward simulation for source-only type-application roots after
--     catching the target term up to a related value.
--   * Is parameterized by CTI transport, target value catch-up, and the
--     genuine value-spine source-universal simulation induction.
--   * Contains no root classifier or residual-family interface.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst)

open import Types using (Ty; TyCtx; ★; `∀; _[_]ᵗ)
open import TyStore using (TyStore)
open import CastTerms using
  ( Term
  ; Value
  ; ⟨_,_,_⟩
  ; _⦂∀_[_]
  )
open import Reduction
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.CatchupToMorePreciseDef using
  (CatchupToMorePrecise)
open import proof.DGG.SimSourceAllClosingDef using
  (SimSourceAllClosingᵀ)
open import proof.DGG.SimSourceAllValuesDef using
  (SimSourceAllValuesᵀ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence
open import proof.Reduction
open import proof.Reduction.ValueIrreducibleProof using
  (value-no-step)


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-to-more-precise : CatchupToMorePrecise)
    (sim-source-all-values : SimSourceAllValuesᵀ)
  where

  private
    close-root : SimSourceAllClosingᵀ
    close-root no-rebase related q r source-value source-step
        with catchup-to-more-precise no-rebase related source-value
    close-root {C = C} {A = A} {B = B}
        no-rebase related q r source-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-value , γ₁ , type-rel₁ ,
        target-steps , target-is-value , evolution₁ , related₁
        with sim-source-all-values
          (multi-no-open-frames evolution₁ no-rebase)
          related₁
          (subst (λ T → A ⊑ᵀ⟨ γ₁ ⟩ T)
            (applyTys-★ χsᴿ₁) (multi-⊑ᵀ evolution₁ q))
          (multi-⊑ᵀ evolution₁ r)
          source-value target-is-value source-step
    close-root {M′ = M′} {B = B}
        no-rebase related q r source-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-value , γ₁ , type-rel₁ ,
        target-steps , target-is-value , evolution₁ , related₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , result , γ₂ , result-rel ,
        root-steps , root-evolution , result-related
        with subst
          (λ T →
            Σ[ s ∈ _ ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ ⊢² _ ⊑ result ∶ s)
          (applyTys-++ χsᴿ₁ χsᴿ₂ B)
          (result-rel , result-related)
    close-root {M′ = M′} {B = B}
        no-rebase related q r source-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-value , γ₁ , type-rel₁ ,
        target-steps , target-is-value , evolution₁ , related₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , result , γ₂ , result-rel ,
        root-steps , root-evolution , result-related
      | result-rel′ , result-related′ =
        Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ , result , γ₂ ,
        result-rel′ ,
        (M′
          —↠+[ χsᴿ₁ ]⟨ target-steps ⟩
         target-value
          —↠[ χsᴿ₂ ]⟨ root-steps ⟩
         result ∎[]) ,
        composeMultiWorldEvolution evolution₁ root-evolution ,
        result-related′

  sim-source-all-closing : SimSourceAllClosingᵀ
  sim-source-all-closing no-rebase related q r source-value
      root@(pure-step (β-∀ value instantiated)) =
    close-root no-rebase related q r source-value root

  sim-source-all-closing no-rebase related q r source-value
      root@(β-Λ value) =
    close-root no-rebase related q r source-value root

  sim-source-all-closing no-rebase related q r source-value
      root@(β-gen value not-star safe) =
    close-root no-rebase related q r source-value root

  sim-source-all-closing no-rebase related q r source-value
      root@(β-reveal-∀ value) =
    close-root no-rebase related q r source-value root

  sim-source-all-closing no-rebase related q r source-value
      root@(β-conceal-∀ value) =
    close-root no-rebase related q r source-value root

  sim-source-all-closing no-rebase related q r ()
      (pure-step blame-•)

  sim-source-all-closing no-rebase related q r source-value
      (ξ-• source-step refl refl) =
    ⊥-elim (value-no-step source-value source-step)
