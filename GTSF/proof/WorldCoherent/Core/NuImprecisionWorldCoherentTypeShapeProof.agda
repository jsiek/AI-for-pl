module
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentTypeShapeProof
  where

-- File Charter:
--   * Proves the type-imprecision shape equations reused by world-coherent
--     one-step results.
--   * Connects source-side ν lifting to the proof-irrelevant imprecision shape.
--   * Contains no reduction, catch-up, or term-imprecision construction.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)
open import Data.Nat using (s<s)
open import Function using (id)
open import ImprecisionComposition using
  (⌊_⌋)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_)
open import NuReduction using (applyTy; applyTys)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( shape-rename
  ; shape-subst-source
  ; shape-subst-target
  )
open import proof.Core.Properties.ReductionProperties using
  (applyTys-++)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( rename-assm²-source-νᵢ
  ; rename-assm²-target-rightᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import proof.Core.Properties.TypeProperties using
  (renameᵗ-id)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (weak-one-step-compose-type)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; sourceResult
  ; sourceChanges
  ; targetResult
  ; targetTailChanges
  ; transportShapeCoherent
  ; transportType
  )
open import Relation.Binary.PropositionalEquality using
  (subst; sym; trans)
open import Types using (renameᵗ)


shape-source-liftνᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-source-liftνᵢ p ⌋ ≡ ⌊ p ⌋
shape-source-liftνᵢ {B = B} p =
  trans
    (shape-subst-target
      (renameᵗ-id B)
      (⊑-renameᵗ²ᵢ
        rename-assm²-source-νᵢ
        (λ X<Δ → s<s X<Δ)
        id
        p))
    (shape-rename
      rename-assm²-source-νᵢ
      (λ X<Δ → s<s X<Δ)
      id
      p)


shape-target-lift-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-target-lift-rightᵢ p ⌋ ≡ ⌊ p ⌋
shape-target-lift-rightᵢ {A = A} p =
  trans
    (shape-subst-source
      (renameᵗ-id A)
      (⊑-renameᵗ²ᵢ
        rename-assm²-target-rightᵢ
        id
        (λ Y<Δ → s<s Y<Δ)
        p))
    (shape-rename
      rename-assm²-target-rightᵢ
      id
      (λ Y<Δ → s<s Y<Δ)
      p)


weak-one-step-compose-type-preserves-shapeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (second : WeakOneStepResult
      (resultStore first) (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′) →
  WeakOneStepTypeCoherence first →
  WeakOneStepTypeCoherence second →
  ∀ {C D}
    (p : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
  ⌊ weak-one-step-compose-type first second p ⌋ ≡ ⌊ p ⌋
weak-one-step-compose-type-preserves-shapeᵀ
    {χ = χ} first {χ′ = χ′} second
    first-coherence second-coherence
    {C = C} {D = D} p =
  trans
    (shape-subst-target target-eq source-transport)
    (trans
      (shape-subst-source source-eq nested)
      (trans
        (transportShapeCoherent second-coherence
          (transportType first p))
        (transportShapeCoherent first-coherence p)))
  where
  nested = transportType second (transportType first p)
  source-eq = sym
    (applyTys-++ (sourceChanges first) (sourceChanges second) C)
  source-transport =
    subst
      (λ S → resultCtx second ∣ resultLeftCtx second
        ⊢ S ⊑ applyTys (targetTailChanges second)
            (applyTy χ′
              (applyTys (targetTailChanges first) (applyTy χ D)))
        ⊣ resultRightCtx second)
      source-eq nested
  target-eq = sym
    (applyTys-++ (targetTailChanges first)
      (χ′ ∷ targetTailChanges second) (applyTy χ D))
