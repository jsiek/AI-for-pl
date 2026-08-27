{-# OPTIONS --safe #-}

module proof.DGG.SimPairedAllClosingProof where

-- File Charter:
--   * Proves forward simulation for paired type-application roots after
--     catching the target head up to a related universal value.
--   * Is parameterized by CTI transport, target value catch-up, and the
--     genuine value-spine paired-universal simulation induction.
--   * Contains no root classifier or residual-family interface.

open import Data.List using ([])
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst; sym; trans)

open import Types using (Ty; TyCtx; `∀; _[_]ᵗ)
open import TyStore using (TyStore)
open import CastTerms using
  ( Term
  ; Value
  ; ⟨_,_,_⟩
  ; _⦂∀_[_]
  ; Λ_
  ; _《_》
  ; _↑_
  ; _↓_
  ; all
  ; genᵥ
  )
open import Reduction
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.CatchupToMorePreciseDef using
  (CatchupToMorePrecise)
open import proof.DGG.SimPairedAllClosingDef using
  (SimPairedAllClosingᵀ)
open import proof.DGG.SimPairedAllValuesDef using
  (SimPairedAllValuesᵀ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence
open import proof.Reduction
open import proof.Reduction.ValueIrreducibleProof using
  (blame-not-value; value-no-step)


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-to-more-precise : CatchupToMorePrecise)
    (sim-paired-all-values : SimPairedAllValuesᵀ)
  where

  private
    close-root : SimPairedAllClosingᵀ
    close-root {C′ = C′} {A′ = A′}
        no-rebase related q r source-value source-step
        with catchup-to-more-precise no-rebase related source-value
    close-root {C = C} {A = A} {C′ = C′} {A′ = A′}
        no-rebase related q r source-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-value , γ₁ , type-rel₁ ,
        target-steps , target-is-value , evolution₁ , related₁
        with subst
          (λ T →
            Σ[ p ∈ `∀ C ⊑ᵀ⟨ γ₁ ⟩ T ]
              γ₁ ⊢² _ ⊑ target-value ∶ p)
          (applyTys-∀ χsᴿ₁ C′)
          (type-rel₁ , related₁)
    close-root {C = C} {A = A} {C′ = C′} {A′ = A′}
        no-rebase related q r source-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-value , γ₁ , type-rel₁ ,
        target-steps , target-is-value , evolution₁ , related₁
      | type-rel₁′ , related₁′
        with sim-paired-all-values
          (multi-no-source-rebase evolution₁ no-rebase)
          related₁′
          (multi-⊑ᵀ evolution₁ q)
          (subst (λ T → C [ A ]ᵗ ⊑ᵀ⟨ γ₁ ⟩ T)
            (applyTys-open χsᴿ₁ C′ A′)
            (multi-⊑ᵀ evolution₁ r))
          source-value target-is-value source-step
    close-root {M′ = M′} {C′ = C′} {A′ = A′}
        no-rebase related q r source-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-value , γ₁ , type-rel₁ ,
        target-steps , target-is-value , evolution₁ , related₁
      | type-rel₁′ , related₁′
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , result , γ₂ , result-rel ,
        root-steps , root-evolution , result-related
        with subst
          (λ T →
            Σ[ s ∈ _ ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ ⊢² _ ⊑ result ∶ s)
          (trans
            (cong (applyTys χsᴿ₂)
              (sym (applyTys-open χsᴿ₁ C′ A′)))
            (applyTys-++ χsᴿ₁ χsᴿ₂ (C′ [ A′ ]ᵗ)))
          (result-rel , result-related)
    close-root {M′ = M′} {C′ = C′} {A′ = A′}
        no-rebase related q r source-value source-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-value , γ₁ , type-rel₁ ,
        target-steps , target-is-value , evolution₁ , related₁
      | type-rel₁′ , related₁′
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , result , γ₂ , result-rel ,
        root-steps , root-evolution , result-related
      | result-rel′ , result-related′ =
        Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ , result , γ₂ ,
        result-rel′ ,
        (M′ ⦂∀ C′ [ A′ ]
          —↠+[ χsᴿ₁ ]⟨ typeApp-↠ target-steps ⟩
         target-value ⦂∀
            applyBodies χsᴿ₁ C′ [ applyTys χsᴿ₁ A′ ]
          —↠[ χsᴿ₂ ]⟨ root-steps ⟩
         result ∎[]) ,
        composeMultiWorldEvolution evolution₁ root-evolution ,
        result-related′

  sim-paired-all-closing : SimPairedAllClosingᵀ
  sim-paired-all-closing no-rebase related q r source-value
      root@(pure-step (β-∀ value instantiated)) =
    close-root no-rebase related q r source-value root

  sim-paired-all-closing no-rebase related q r source-value
      root@(β-Λ value) =
    close-root no-rebase related q r source-value root

  sim-paired-all-closing no-rebase related q r source-value
      root@(β-gen value not-star safe) =
    close-root no-rebase related q r source-value root

  sim-paired-all-closing no-rebase related q r source-value
      root@(β-reveal-∀ value) =
    close-root no-rebase related q r source-value root

  sim-paired-all-closing no-rebase related q r source-value
      root@(β-conceal-∀ value) =
    close-root no-rebase related q r source-value root

  sim-paired-all-closing no-rebase related q r ()
      (pure-step blame-•)

  sim-paired-all-closing no-rebase related q r source-value
      (ξ-• source-step refl refl) =
    ⊥-elim (value-no-step source-value source-step)
