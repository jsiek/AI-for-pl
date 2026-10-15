{-# OPTIONS --safe #-}

module proof.DGG.SimSourceRevealClosingProof where

-- File Charter:
--   * Proves source-only reveal cancellation after target value catch-up.
--   * Uses source-seal inversion as the single genuine lower semantic
--     induction at the unmatched reveal boundary.
--   * Splits directly on every reveal root and contains no classifier or
--     residual-family surface.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl; subst)

open import CastTerms using (Value; seal; _↓_)
open import Reduction
import Conversion as Conv
open import proof.DGG.CatchupToMorePreciseDef using
  (CatchupToMorePrecise)
open import proof.DGG.Inversion.SourceSealInversion2Def using
  (SourceSealInversion²)
open import proof.DGG.SimSourceRevealClosingDef using
  (SimSourceRevealClosingᵀ)
open import proof.DGG.World using (_⊑ᵀ⟨_⟩_)
open import proof.DGG.WorldEvolutionSequence using
  ( append-left-keep
  ; multi-⊑ᵀ
  ; multi-source-mark
  ; multi-source-disaligned
  )
open import proof.Reduction using (applyTys-★)
open import proof.Reduction.ValueIrreducibleProof using
  (value-no-step)


module _
    (catchup-to-more-precise : CatchupToMorePrecise)
    (source-seal-inversion² : SourceSealInversion²)
  where

  sim-source-reveal-closing : SimSourceRevealClosingᵀ
  sim-source-reveal-closing no-rebase
      (Conv.⊢↑-id-var member not-equal) present mark free
      represented related q source-value (pure-step (id-reveal value)) =
    ⊥-elim (present refl)

  sim-source-reveal-closing no-rebase
      (Conv.⊢↑-id-base member) present mark free
      represented related q source-value (pure-step (id-reveal value)) =
    ⊥-elim (present refl)

  sim-source-reveal-closing no-rebase
      (Conv.⊢↑-id-star member) present mark free
      represented related q source-value (pure-step (id-reveal value)) =
    ⊥-elim (present refl)

  sim-source-reveal-closing no-rebase
      (Conv.⊢↑-unseal member) present mark free represented related q
      source-value (pure-step (conceal-reveal value))
      with catchup-to-more-precise no-rebase related (value ↓ seal)
  sim-source-reveal-closing {Rᴸ = Rᴸ} {B = B} no-rebase
      (Conv.⊢↑-unseal member) present mark free represented related q
      source-value (pure-step (conceal-reveal value))
    | Δᴿ′ , Σᴿ′ , χsᴿ , target-value , γ′ , type-related ,
      target-steps , target-is-value , evolution , final-related =
    Δᴿ′ , Σᴿ′ , χsᴿ , target-value , γ′ ,
    multi-⊑ᵀ evolution q , target-steps , append-left-keep evolution ,
    source-seal-inversion²
      (multi-source-mark evolution mark)
      (multi-source-disaligned evolution free)
      (subst (λ T → Rᴸ ⊑ᵀ⟨ γ′ ⟩ T)
        (applyTys-★ χsᴿ) (multi-⊑ᵀ evolution represented))
      member value target-is-value final-related (multi-⊑ᵀ evolution q)

  sim-source-reveal-closing no-rebase c⊢ present mark free represented
      related q () (pure-step blame-reveal)

  sim-source-reveal-closing no-rebase c⊢ present mark free represented
      related q source-value (ξ-reveal source-step renamed) =
    ⊥-elim (value-no-step source-value source-step)
