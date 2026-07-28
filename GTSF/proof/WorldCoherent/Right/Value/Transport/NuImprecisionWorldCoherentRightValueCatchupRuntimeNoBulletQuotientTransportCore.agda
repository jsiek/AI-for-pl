module
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletQuotientTransportCore
  where

-- File Charter:
--   * Provides the nonrecursive quotient-index transport facts used by
--     runtime-source/no-bullet-target right-value catch-up.
--   * Separates stable type-index algebra from the constructor-sensitive QTI
--     recursion in the transport proof.
--   * Contains no term-imprecision case analysis, postulate, hole, or
--     termination bypass.

open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ForallPermutation using
  ( _≈∀_
  ; _∣_⊢_⊑ᵖ_⊣_
  ; ≈∀-refl
  ; quotientᵖ
  )
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _⊢_≈∀ˢ_
  ; _；⌊_⌋≋ᵖ_；_
  ; quotient-boundary-square
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( applyTy
  ; applyTys
  ; bind
  ; keep
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using (StoreImp)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; sourceChanges
  ; targetTailChanges
  ; transportShapeCoherent
  ; transportType
  )
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using (imprecision-composition-shape-transport)
open import
  proof.Core.Properties.NuImprecisionQuotientBoundaryProperties
  using (source-perm-shape-rename)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using
  ( applyTy-preserves-≈∀
  ; applyTys-preserves-≈∀
  ; weak-one-step-transport-quotientᵀ
  )
open import Types using (Ty)


private
  source-perm-shape-applyTy :
    ∀ {χ A B s s′} {equivalence : A ≈∀ B} →
    equivalence ⊢ s ≈∀ˢ s′ →
    applyTy-preserves-≈∀ {χ = χ} equivalence ⊢ s ≈∀ˢ s′
  source-perm-shape-applyTy {χ = keep} shape =
    shape
  source-perm-shape-applyTy {χ = bind A} shape =
    source-perm-shape-rename shape

  source-perm-shape-applyTys :
    ∀ {χs A B s s′} {equivalence : A ≈∀ B} →
    equivalence ⊢ s ≈∀ˢ s′ →
    applyTys-preserves-≈∀ {χs = χs} equivalence ⊢ s ≈∀ˢ s′
  source-perm-shape-applyTys {χs = []} shape =
    shape
  source-perm-shape-applyTys {χs = χ ∷ χs} shape =
    source-perm-shape-applyTys {χs = χs}
      (source-perm-shape-applyTy {χ = χ} shape)

  applyTy-preserves-≈∀-refl :
    ∀ {χ A} →
    applyTy-preserves-≈∀ {χ = χ} (≈∀-refl {A = A}) ≡ ≈∀-refl
  applyTy-preserves-≈∀-refl {χ = keep} =
    refl
  applyTy-preserves-≈∀-refl {χ = bind C} =
    refl

  applyTys-preserves-≈∀-refl :
    ∀ {χs A} →
    applyTys-preserves-≈∀ {χs = χs} (≈∀-refl {A = A}) ≡ ≈∀-refl
  applyTys-preserves-≈∀-refl {χs = []} =
    refl
  applyTys-preserves-≈∀-refl {χs = χ ∷ χs} {A = A}
      rewrite applyTy-preserves-≈∀-refl {χ = χ} {A = A}
            | applyTys-preserves-≈∀-refl
                {χs = χs} {A = applyTy χ A} =
    refl


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


weak-one-step-transport-reflexive-quotient :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ C C′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    (p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ) →
  weak-one-step-transport-quotientᵀ result
      (quotientᵖ ≈∀-refl p ≈∀-refl) ≡
    quotientᵖ ≈∀-refl (transportType result p) ≈∀-refl
weak-one-step-transport-reflexive-quotient
    {χ = χ} {C = C} {C′ = C′} result p
    rewrite applyTys-preserves-≈∀-refl
              {χs = sourceChanges result} {A = C}
          | applyTy-preserves-≈∀-refl {χ = χ} {A = C′}
          | applyTys-preserves-≈∀-refl
              {χs = targetTailChanges result}
              {A = applyTy χ C′} =
  refl
