module
  proof.Right.Core.NuImprecisionQuotientDownTransportProof
  where

-- File Charter:
--   * Transports an arbitrary paired quotient downcast through a completed
--     target-leading weak step.
--   * Applies the leading target store change before the target tail and
--     reconstructs the exact transported quotient boundary square.
--   * Transports general gradual cast modes existentially; identity-only mode
--     remains fixed.
--   * Contains no outer widening, frame assembly, dispatcher, postulate, hole,
--     permissive option, or compatibility wrapper.

open import Relation.Binary.PropositionalEquality using
  (subst; sym)

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing)
open import Coercions using (Coercion)
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( narrow-weaken
  ; _∣_∣_⊢_∶_⊒_
  )
open import NuReduction using
  ( StoreChange
  ; applyCoercion
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; paired-downᵀ
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import QuotientImprecisionCompatibility using
  (QuotientNarrowingEliminationCompatible; SpineCastMode)
open import Types using (Ty; TyCtx)
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-spine-narrows-typing)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; canonicalIndexedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceResult
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetStoreResult
  ; targetResult
  ; targetTailChanges
  ; weakIndexedResult
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (cast-shape-applyCoercions)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using
  ( weak-one-step-transport-quotientᵀ
  ; weak-one-step-transport-quotient-boundary-square
  )
open import
  proof.OneStep.NuImprecisionWeakOneStepQuotientCompatibilityTransport
  using
  ( weak-one-step-transport-quotient-narrowing-eliminationᵀ
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof
  using (spine-cast-mode-prefix-proofᵀ)


private
  source-spine-narrowingᵀ :
    ∀ {Φ Δᴸ Δᴿ M M′ C C′ D μ d}
      {χ : StoreChange}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ} →
    (prefix : StoreImpPrefix ρᵇ ρ) →
    (inner : WeakOneStepResult ρ M M′ C C′ χ) →
    SpineCastMode (leftStoreⁱ ρᵇ) μ →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ C ⊒ D →
    ∃[ μ′ ]
      (SpineCastMode (leftStoreⁱ (resultStore inner)) μ′ ×
      (μ′ ∣ resultLeftCtx inner ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) d
          ∶ applyTys (sourceChanges inner) C
          ⊒ applyTys (sourceChanges inner) D))
  source-spine-narrowingᵀ
      {Δᴸ = Δᴸ} prefix inner mode d⊒
      with apply-spine-narrows-typing
        {χs = sourceChanges inner}
        (spine-cast-mode-prefix-proofᵀ
          (leftStoreⁱ-prefix-inclusion prefix) mode)
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)
  source-spine-narrowingᵀ
      {Δᴸ = Δᴸ} prefix inner mode d⊒
      | μ′ , mode′ , d′⊒ =
    μ′ ,
    subst (λ Σ → SpineCastMode Σ μ′)
      (sym (sourceStoreResult inner)) mode′ ,
    subst
      (λ Δ → _ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) _
          ⊒ applyTys (sourceChanges inner) _)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → _
          ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) _
            ∶ applyTys (sourceChanges inner) _
            ⊒ applyTys (sourceChanges inner) _)
        (sym (sourceStoreResult inner)) d′⊒)

  target-spine-narrowingᵀ :
    ∀ {Φ Δᴸ Δᴿ M M′ C C′ D′ μ d′}
      {χ : StoreChange}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ} →
    (prefix : StoreImpPrefix ρᵇ ρ) →
    (inner : WeakOneStepResult ρ M M′ C C′ χ) →
    SpineCastMode (rightStoreⁱ ρᵇ) μ →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ C′ ⊒ D′ →
    ∃[ μ′ ]
      (SpineCastMode (rightStoreⁱ (resultStore inner)) μ′ ×
      (μ′ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner)
            (applyCoercion χ d′)
          ∶ applyTys (targetTailChanges inner) (applyTy χ C′)
          ⊒ applyTys (targetTailChanges inner) (applyTy χ D′)))
  target-spine-narrowingᵀ
      {Δᴿ = Δᴿ} {χ = χ}
      prefix inner mode d′⊒
      with apply-spine-narrows-typing
        {χs = χ ∷ targetTailChanges inner}
        (spine-cast-mode-prefix-proofᵀ
          (rightStoreⁱ-prefix-inclusion prefix) mode)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
  target-spine-narrowingᵀ
      {Δᴿ = Δᴿ} {χ = χ}
      prefix inner mode d′⊒
      | μ′ , mode′ , d″⊒ =
    μ′ ,
    subst (λ Σ → SpineCastMode Σ μ′)
      (sym (targetStoreResult inner)) mode′ ,
    subst
      (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner)
            (applyCoercion χ _)
          ∶ applyTys (targetTailChanges inner) (applyTy χ _)
          ⊒ applyTys (targetTailChanges inner) (applyTy χ _))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → _
          ∣ applyTyCtxs (targetTailChanges inner) (applyTyCtx χ Δᴿ)
          ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion χ _)
            ∶ applyTys (targetTailChanges inner) (applyTy χ _)
            ⊒ applyTys (targetTailChanges inner) (applyTy χ _))
        (sym (targetStoreResult inner)) d″⊒)


quotient-down-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ D D′ : Ty}
    {d d′ s s′ μ μ′} {χ : StoreChange}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρᵇ ρ) →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} pC) →
  SpineCastMode (leftStoreⁱ ρᵇ) μ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ C ⊒ D →
  narrowing ⊢ᶜ d ⦂ s →
  SpineCastMode (rightStoreⁱ ρᵇ) μ′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ C′ ⊒ D′ →
  narrowing ⊢ᶜ d′ ⦂ s′ →
  s ；⌊ pC ⌋≋ᵖ qD ； s′ →
  AssumptionMembershipUnique
    (resultCtx (weakIndexedResult indexed)) →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d d′ pC qD s s′ →
  let inner = weakIndexedResult indexed in
  resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺᵖ
      sourceResult inner ⟨
        applyCoercions (sourceChanges inner) d ⟩
      ⊑ targetResult inner ⟨
        applyCoercions (targetTailChanges inner)
          (applyCoercion χ d′) ⟩
      ⦂ applyTys (sourceChanges inner) D
        ⊑ᵖ applyTys (targetTailChanges inner) (applyTy χ D′)
      ∶ weak-one-step-transport-quotientᵀ inner qD
quotient-down-transportᵀ
    {χ = χ} prefix indexed
    mode d⊒ d-shape mode′ d′⊒ d′-shape square
    final-unique elimination
    with source-spine-narrowingᵀ
           prefix (weakIndexedResult indexed) mode d⊒
       | target-spine-narrowingᵀ
           prefix (weakIndexedResult indexed) mode′ d′⊒
quotient-down-transportᵀ
    {χ = χ} prefix indexed
    mode d⊒ d-shape mode′ d′⊒ d′-shape square
    final-unique elimination
    | μᴿ , modeᴿ , dᴿ⊒
    | μ′ᴿ , mode′ᴿ , d′ᴿ⊒ =
  paired-downᵀ
    (canonicalIndexedResults indexed)
    modeᴿ dᴿ⊒
    (cast-shape-applyCoercions
      (sourceChanges inner) d-shape)
    mode′ᴿ d′ᴿ⊒
    (cast-shape-applyCoercions
      (χ ∷ targetTailChanges inner) d′-shape)
    (weak-one-step-transport-quotient-boundary-square
      inner (weakIndexedTypeCoherence indexed) square)
    (weak-one-step-transport-quotient-narrowing-eliminationᵀ
      inner (weakIndexedTypeCoherence indexed)
      final-unique elimination)
  where
  inner = weakIndexedResult indexed
