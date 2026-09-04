{-# OPTIONS --safe #-}

module proof.DGG.SimSourceCastValuesProof where

-- File Charter:
--   * Proves source-only ordinary-cast value simulation by an exhaustive split
--     on the source cast-root reduction.
--   * Delegates only the two left ground witnesses, generated-tag inversion,
--     and beta-instantiation value-spine induction.
--   * Contains no reduction classifier or residual-family interface and does
--     not depend on paired-cast simulation.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
  renaming (subst to subst≡)

open import Types
open import Consistency using
  ( idᵍ
  ; _!
  ; ？_
  )
open import CastTerms
open import Reduction
import proof.Imprecision as PI
import proof.DGG.CastTermImprecision as CTI
open CTI using (_⊢²_⊑_∶_)
open import proof.DGG.CastTermImprecisionTyping using (target-typing)
open import proof.DGG.Inversion.LeftInjInversion2Def using
  (LeftInjInversion²)
open import proof.DGG.Inversion.SpineValueDef using
  ( SpineValue
  ; sv-ƛ
  ; sv-Λ
  ; sv-$
  ; sv-cast
  ; sv-seal
  ; sv-reveal-fun
  ; sv-conceal-fun
  ; sv-reveal-all
  ; sv-conceal-all
  )
open import proof.DGG.SimSourceCastValuesDef using
  (SimSourceCastValuesᵀ)
open import proof.DGG.SimSourceInstantiationCastValuesDef using
  (SimSourceInstantiationCastValuesᵀ)
open import proof.DGG.SourceGroundCastWitnessDef using
  ( SourceGroundInjectionWitnessᵀ
  ; SourceGroundProjectionWitnessᵀ
  )
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence using
  (evolutions-refl; evolutions-step-left)
open import proof.Reduction.ValueIrreducibleProof using
  (value-no-step)


value→spine : ∀ {Δ} {V : Term Δ} → Value V → SpineValue V
value→spine (ƛ N) = sv-ƛ N
value→spine (Λ value) = sv-Λ (value→spine value)
value→spine ($ κ) = sv-$ κ
value→spine (value 《 inert 》) = sv-cast (value→spine value) inert
value→spine (value ↑ fun) = sv-reveal-fun (value→spine value)
value→spine (value ↑ all) = sv-reveal-all (value→spine value)
value→spine (value ↓ seal) = sv-seal (value→spine value)
value→spine (value ↓ fun) = sv-conceal-fun (value→spine value)
value→spine (value ↓ all) = sv-conceal-all (value→spine value)


module _
    (source-ground-injection-witness :
      SourceGroundInjectionWitnessᵀ)
    (source-ground-projection-witness :
      SourceGroundProjectionWitnessᵀ)
    (left-inj-inversion² : LeftInjInversion²)
    (sim-source-instantiation-cast-values :
      SimSourceInstantiationCastValuesᵀ)
  where

  sim-source-cast-values : SimSourceCastValuesᵀ
  sim-source-cast-values {γ = γ} {V = V} {V′ = V′} {p = p}
      no-rebase related q source-value target-value
      (pure-step (β-id value)) =
    γ , q ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    subst≡ (λ r → γ ⊢² V ⊑ V′ ∶ r) (PI.⊑-unique p q) related

  sim-source-cast-values {γ = γ} {c =
      _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄}
      no-rebase related q source-value target-value
      (pure-step (ground ⦃ Gns = Gns ⦄ value not-equal))
      with source-ground-injection-witness
        {c = c} {Gᵍ = Gᵍ} {Ans = Ans}
        related source-value target-value q
  sim-source-cast-values {γ = γ} {c =
      _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄}
      no-rebase related q source-value target-value
      (pure-step (ground ⦃ Gns = Gns ⦄ value not-equal))
      | ground-related =
    γ , q ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    CTI.cast⊑²
      (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ) ⦃ Gns ⦄)
      (CTI.cast⊑² c related ground-related) q

  sim-source-cast-values {γ = γ} {c =
      ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄}
      no-rebase related q source-value target-value
      (pure-step (expand ⦃ Gns = Gns ⦄ value not-equal))
      with source-ground-projection-witness
        {c = c} {Gᵍ = Gᵍ} {Bns = Bns}
        related source-value target-value q
  sim-source-cast-values {γ = γ} {c =
      ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄}
      no-rebase related q source-value target-value
      (pure-step (expand ⦃ Gns = Gns ⦄ value not-equal))
      | ground-related =
    γ , q ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    CTI.cast⊑² c
      (CTI.cast⊑²
        (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
          ⦃ Gns ⦄)
        related ground-related)
      q

  sim-source-cast-values {γ = γ} no-rebase related q
      source-value target-value (pure-step (tag-untag value)) =
    γ , q ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    left-inj-inversion² (value→spine value) target-value related q

  sim-source-cast-values {γ = γ} {c = c} no-rebase related q
      source-value target-value
      (pure-step (tag-untag-bad value not-equal)) =
    γ , q ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    CTI.blame⊑² (target-typing (CTI.cast⊑² c related q)) q

  sim-source-cast-values {γ = γ} {c = c} no-rebase related q
      source-value target-value (pure-step (blame-bot-intro value)) =
    γ , q ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    CTI.blame⊑² (target-typing (CTI.cast⊑² c related q)) q

  sim-source-cast-values no-rebase related q () target-value
      (pure-step blame-⟨⟩)

  sim-source-cast-values no-rebase related q source-value target-value
      root@(β-inst value not-star) =
    sim-source-instantiation-cast-values
      no-rebase related q source-value target-value root

  sim-source-cast-values no-rebase related q source-value target-value
      (ξ-⟨⟩ source-step renamed) =
    ⊥-elim (value-no-step source-value source-step)
