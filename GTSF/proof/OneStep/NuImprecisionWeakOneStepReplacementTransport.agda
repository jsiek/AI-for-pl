module proof.OneStep.NuImprecisionWeakOneStepReplacementTransport where

-- File Charter:
--   * Transports paired hereditary replacement evidence through a weak
--     one-step result using its structural replacement coherence.
--   * Uses type-shape coherence only to reindex the transported stored
--     imprecision evidence to the caller's canonical witness.
--   * Transports quotient imprecision through the same weak one-step result.
--   * Provides the shared non-world-coherent helper used by left- and
--     right-silent paired conversion transport.
--   * Contains no simulation dispatcher, store lineage, postulate, hole,
--     permissive option, or compatibility shim.

open import Data.List using ([]; _∷_)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import ForallPermutation using
  ( _≈∀_
  ; _∣_⊢_⊑ᵖ_⊣_
  ; quotientᵖ
  )
open import ImprecisionComposition using
  ( _⊢_≈∀ˢ_
  ; ⌊_⌋
  ; _；⌊_⌋≋ᵖ_；_
  ; quotient-boundary-square
  )
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyTy; applyTys; bind; keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans)
open import Types using (Ty; TyCtx; TyVar)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; sourceChanges
  ; targetTailChanges
  ; transportShapeCoherent
  ; transportPairedReplacementCoherent
  ; transportType
  )
open import proof.Core.Properties.ReductionProperties using
  (applyTyVars)
open import
  proof.Core.Properties.ConversionIndexCompatibilityProperties
  using
  (replace-paired-evidence-shape)
open import proof.Core.Permutation.ForallPermutationProperties using
  (≈∀-renameᵗ)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (imprecision-composition-shape-transport)
open import
  proof.Core.Properties.NuImprecisionQuotientBoundaryProperties
  using (source-perm-shape-rename)


applyTy-preserves-≈∀ :
  ∀ {χ A B} →
  A ≈∀ B →
  applyTy χ A ≈∀ applyTy χ B
applyTy-preserves-≈∀ {χ = keep} A≈B = A≈B
applyTy-preserves-≈∀ {χ = bind C} A≈B = ≈∀-renameᵗ A≈B

applyTys-preserves-≈∀ :
  ∀ {χs A B} →
  A ≈∀ B →
  applyTys χs A ≈∀ applyTys χs B
applyTys-preserves-≈∀ {χs = []} A≈B = A≈B
applyTys-preserves-≈∀ {χs = χ ∷ χs} A≈B =
  applyTys-preserves-≈∀ {χs = χs}
    (applyTy-preserves-≈∀ {χ = χ} A≈B)


source-perm-shape-applyTy :
  ∀ {χ A B s s′} {equivalence : A ≈∀ B} →
  equivalence ⊢ s ≈∀ˢ s′ →
  applyTy-preserves-≈∀ {χ = χ} equivalence ⊢ s ≈∀ˢ s′
source-perm-shape-applyTy {χ = keep} shape = shape
source-perm-shape-applyTy {χ = bind C} shape =
  source-perm-shape-rename shape


source-perm-shape-applyTys :
  ∀ {χs A B s s′} {equivalence : A ≈∀ B} →
  equivalence ⊢ s ≈∀ˢ s′ →
  applyTys-preserves-≈∀ {χs = χs} equivalence ⊢ s ≈∀ˢ s′
source-perm-shape-applyTys {χs = []} shape = shape
source-perm-shape-applyTys {χs = χ ∷ χs} shape =
  source-perm-shape-applyTys {χs = χs}
    (source-perm-shape-applyTy {χ = χ} shape)


weak-one-step-transport-quotientᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ C D}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : WeakOneStepResult ρ M N′ A B χ) →
  Φ ∣ Δᴸ ⊢ C ⊑ᵖ D ⊣ Δᴿ →
  resultCtx result ∣ resultLeftCtx result
    ⊢ applyTys (sourceChanges result) C
      ⊑ᵖ applyTys (targetTailChanges result) (applyTy χ D)
    ⊣ resultRightCtx result
weak-one-step-transport-quotientᵀ {χ = χ} result
    (quotientᵖ C≈E E⊑F F≈D) =
  quotientᵖ
    (applyTys-preserves-≈∀
      {χs = sourceChanges result} C≈E)
    (transportType result E⊑F)
    (applyTys-preserves-≈∀
      {χs = targetTailChanges result}
      (applyTy-preserves-≈∀ {χ = χ} F≈D))


weak-one-step-transport-quotient-boundary-square :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ C C′ D D′ s s′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ) →
  WeakOneStepTypeCoherence result →
  s ；⌊ p ⌋≋ᵖ q ； s′ →
  s ；⌊ transportType result p ⌋≋ᵖ
    (weak-one-step-transport-quotientᵀ result q) ； s′
weak-one-step-transport-quotient-boundary-square
    {χ = χ} {p = p} result type-coherence
    (quotient-boundary-square
      {middle = middle}
      source-shape left-composition target-shape right-composition) =
  quotient-boundary-square
    (source-perm-shape-applyTys
      {χs = sourceChanges result} source-shape)
    (imprecision-composition-shape-transport
      refl (transportShapeCoherent type-coherence p) refl
      left-composition)
    (source-perm-shape-applyTys
      {χs = targetTailChanges result}
      (source-perm-shape-applyTy {χ = χ} target-shape))
    (imprecision-composition-shape-transport
      (transportShapeCoherent type-coherence middle)
      refl refl right-composition)


transport-paired-replacement :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ X X′ : Ty}
    {α β : TyVar}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    (inner : WeakOneStepResult ρ M M′ C C′ keep) →
  WeakOneStepTypeCoherence inner →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  (pX′ : resultCtx inner ∣ resultLeftCtx inner
    ⊢ applyTys (sourceChanges inner) X
      ⊑ applyTys (targetTailChanges inner) X′
      ⊣ resultRightCtx inner) →
  ⌊ pX′ ⌋ ≡ ⌊ pX ⌋ →
  transportType inner p
    [ applyTyVars (sourceChanges inner) α
    ↦ applyTys (sourceChanges inner) X
    ⊑⟨ pX′ ⟩
    applyTys (targetTailChanges inner) X′
    ↤ applyTyVars (targetTailChanges inner) β ]ᴾ
  transportType inner q
transport-paired-replacement inner type-coherence replacement
    pX′ pX-shape =
  replace-paired-evidence-shape
    (trans pX-shape
      (sym (transportShapeCoherent type-coherence _)))
    (transportPairedReplacementCoherent type-coherence replacement)
