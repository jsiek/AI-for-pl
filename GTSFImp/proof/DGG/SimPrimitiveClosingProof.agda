{-# OPTIONS --safe #-}

module proof.DGG.SimPrimitiveClosingProof where

-- File Charter:
--   * Proves primitive delta closing by catching both target operands up to
--     related values in left-to-right evaluation order.
--   * Transports the untouched operand and the first caught-up value through
--     the intervening target evolutions, then uses the closed primitive-value
--     lemma.
--   * Splits exhaustively on delta evidence and contains no classifier or
--     residual-family surface.

open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Primitives using (primArgTy; primResultTy; δ-add; δ-and)
open import CastTerms using ($; _⊕[_]_)
open import Reduction
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.CatchupToMorePreciseDef using
  (CatchupToMorePrecise)
open import proof.DGG.SimPrimitiveClosingDef using
  (SimPrimitiveClosingᵀ)
open import proof.DGG.SimPrimitiveValuesLemma using
  (sim-primitive-values)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World using (_⊑ᵀ⟨_⟩_)
open import proof.DGG.WorldEvolutionSequence using
  ( composeMultiWorldEvolution
  ; multi-no-open-frames
  ; multi-⊑ᵀ
  )
open import proof.Reduction using
  ( _++χ_
  ; _—↠+[_]⟨_⟩_
  ; applyTys-++
  ; applyTys-primArgTy
  ; applyTys-primResultTy
  ; applyTerms-preserves-Value
  ; primL-↠
  ; primR-↠
  )


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-to-more-precise : CatchupToMorePrecise)
  where

  private
    close-root : SimPrimitiveClosingᵀ
    close-root {op = op} {κ = κ} {κ′ = κ′}
        no-rebase left-related right-related r primitive-step
        with catchup-to-more-precise no-rebase left-related ($ κ)
    close-root {op = op} {κ = κ} {κ′ = κ′}
        no-rebase left-related right-related r primitive-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , left-type₁ ,
        left-steps , target-left-value , evolution₁ , left-related₁
        with catchup-to-more-precise
          (multi-no-open-frames evolution₁ no-rebase)
          (transport-CTI no-rebase evolution₁ right-related) ($ κ′)
    close-root {op = op} {κ = κ} {κ′ = κ′}
        no-rebase left-related right-related r primitive-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , left-type₁ ,
        left-steps , target-left-value , evolution₁ , left-related₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-right , γ₂ , right-type₂ ,
        right-steps , target-right-value , evolution₂ , right-related₂
        with subst
          (λ T →
            Σ[ s ∈ primArgTy op ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ ⊢² $ κ ⊑ applyTerms χsᴿ₂ target-left ∶ s)
          (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primArgTy op))
            (applyTys-primArgTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (multi-⊑ᵀ evolution₂ left-type₁ ,
            transport-CTI
              (multi-no-open-frames evolution₁ no-rebase)
              evolution₂ left-related₁)
    close-root {op = op} {κ = κ} {κ′ = κ′}
        no-rebase left-related right-related r primitive-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , left-type₁ ,
        left-steps , target-left-value , evolution₁ , left-related₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-right , γ₂ , right-type₂ ,
        right-steps , target-right-value , evolution₂ , right-related₂
      | left-type₂ , left-related₂
        with subst
          (λ T →
            Σ[ s ∈ primArgTy op ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ ⊢² $ κ′ ⊑ target-right ∶ s)
          (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primArgTy op))
            (applyTys-primArgTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (right-type₂ , right-related₂)
    close-root {op = op} {κ = κ} {κ′ = κ′}
        no-rebase left-related right-related r primitive-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , left-type₁ ,
        left-steps , target-left-value , evolution₁ , left-related₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-right , γ₂ , right-type₂ ,
        right-steps , target-right-value , evolution₂ , right-related₂
      | left-type₂ , left-related₂
      | right-type₂′ , right-related₂′
        with subst
          (λ T → primResultTy op ⊑ᵀ⟨ γ₂ ⟩ T)
          (trans (applyTys-++ χsᴿ₁ χsᴿ₂ (primResultTy op))
            (applyTys-primResultTy (χsᴿ₁ ++χ χsᴿ₂) op))
          (multi-⊑ᵀ evolution₂ (multi-⊑ᵀ evolution₁ r))
    close-root {op = op} {κ = κ} {κ′ = κ′}
        no-rebase left-related right-related r primitive-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , left-type₁ ,
        left-steps , target-left-value , evolution₁ , left-related₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-right , γ₂ , right-type₂ ,
        right-steps , target-right-value , evolution₂ , right-related₂
      | left-type₂ , left-related₂
      | right-type₂′ , right-related₂′
      | result-type₂
        with sim-primitive-values left-related₂ right-related₂′
          result-type₂
          (applyTerms-preserves-Value χsᴿ₂ target-left-value)
          target-right-value primitive-step
    close-root {L′ = L′} {M′ = M′}
        no-rebase left-related right-related r primitive-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , left-type₁ ,
        left-steps , target-left-value , evolution₁ , left-related₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-right , γ₂ , right-type₂ ,
        right-steps , target-right-value , evolution₂ , right-related₂
      | left-type₂ , left-related₂
      | right-type₂′ , right-related₂′
      | result-type₂
      | Δᴿ₃ , Σᴿ₃ , χsᴿ₃ , result , γ₃ , result-rel ,
        root-steps , root-evolution , result-related
        with subst
          (λ T →
            Σ[ s ∈ primResultTy _ ⊑ᵀ⟨ γ₃ ⟩ T ]
              γ₃ ⊢² $ _ ⊑ result ∶ s)
          (trans (applyTys-primResultTy χsᴿ₃ _)
            (sym (applyTys-primResultTy
              (χsᴿ₁ ++χ (χsᴿ₂ ++χ χsᴿ₃)) _)))
          (result-rel , result-related)
    close-root {L′ = L′} {M′ = M′}
        no-rebase left-related right-related r primitive-step
      | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , target-left , γ₁ , left-type₁ ,
        left-steps , target-left-value , evolution₁ , left-related₁
      | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , target-right , γ₂ , right-type₂ ,
        right-steps , target-right-value , evolution₂ , right-related₂
      | left-type₂ , left-related₂
      | right-type₂′ , right-related₂′
      | result-type₂
      | Δᴿ₃ , Σᴿ₃ , χsᴿ₃ , result , γ₃ , result-rel ,
        root-steps , root-evolution , result-related
      | result-rel′ , result-related′ =
        Δᴿ₃ , Σᴿ₃ ,
        χsᴿ₁ ++χ (χsᴿ₂ ++χ χsᴿ₃) , result , γ₃ ,
        result-rel′ ,
        (L′ ⊕[ _ ] M′
          —↠+[ χsᴿ₁ ]⟨ primL-↠ left-steps ⟩
         target-left ⊕[ _ ] applyTerms χsᴿ₁ M′
          —↠+[ χsᴿ₂ ]⟨
            primR-↠ target-left-value right-steps ⟩
         applyTerms χsᴿ₂ target-left ⊕[ _ ] target-right
          —↠[ χsᴿ₃ ]⟨ root-steps ⟩
         result ∎[]) ,
        composeMultiWorldEvolution evolution₁
          (composeMultiWorldEvolution evolution₂ root-evolution) ,
        result-related′

  sim-primitive-closing : SimPrimitiveClosingᵀ
  sim-primitive-closing no-rebase left-related right-related r
      δ-add =
    close-root no-rebase left-related right-related r δ-add

  sim-primitive-closing no-rebase left-related right-related r
      δ-and =
    close-root no-rebase left-related right-related r δ-and
