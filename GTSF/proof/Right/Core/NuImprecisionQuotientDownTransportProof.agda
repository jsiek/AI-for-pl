module
  proof.Right.Core.NuImprecisionQuotientDownTransportProof
  where

-- File Charter:
--   * Transports the identity-mode and generated-mode quotient downcast
--     constructors through an arbitrary completed target-leading weak step.
--   * Applies the leading target store change before the target tail and
--     reconstructs the exact transported quotient boundary square.
--   * Contains no outer widening, frame assembly, dispatcher, postulate,
--     hole, permissive option, or compatibility wrapper.

open import Relation.Binary.PropositionalEquality using (subst; sym)

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing)
open import Coercions using
  (genᵈ; id-onlyᵈ; tag-or-idᵈ)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
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
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; down⊑downᵀ
  ; gen-down⊑gen-downᵀ
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.Core.Properties.CoercionProperties using
  (ModeRename; modeRename-id-only)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (apply-fixed-narrows-typing; modeRename-gen-tag-or-id)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
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


source-fixed-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D μ d}
    {χ : StoreChange}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ} →
  ModeRename suc μ μ →
  (prefix : StoreImpPrefix ρᵇ ρ) →
  (inner : WeakOneStepResult ρ M M′ C C′ χ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ C ⊒ D →
  μ ∣ resultLeftCtx inner ∣ leftStoreⁱ (resultStore inner)
    ⊢ applyCoercions (sourceChanges inner) d
      ∶ applyTys (sourceChanges inner) C
      ⊒ applyTys (sourceChanges inner) D
source-fixed-narrowingᵀ
    {Δᴸ = Δᴸ} mode-suc prefix inner d⊒ =
  subst
    (λ Δ → _ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) _
        ∶ applyTys (sourceChanges inner) _
        ⊒ applyTys (sourceChanges inner) _)
    (sym (sourceCtxResult inner))
    (subst
      (λ Σ → _ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
        ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) _
          ⊒ applyTys (sourceChanges inner) _)
      (sym (sourceStoreResult inner))
      (apply-fixed-narrows-typing
        {χs = sourceChanges inner} mode-suc
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)))


target-fixed-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D′ μ d′}
    {χ : StoreChange}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ} →
  ModeRename suc μ μ →
  (prefix : StoreImpPrefix ρᵇ ρ) →
  (inner : WeakOneStepResult ρ M M′ C C′ χ) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ C′ ⊒ D′ →
  μ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
    ⊢ applyCoercions (targetTailChanges inner)
        (applyCoercion χ d′)
      ∶ applyTys (targetTailChanges inner) (applyTy χ C′)
      ⊒ applyTys (targetTailChanges inner) (applyTy χ D′)
target-fixed-narrowingᵀ
    {Δᴿ = Δᴿ} {χ = χ} mode-suc prefix inner d′⊒ =
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
      (sym (targetStoreResult inner))
      (apply-fixed-narrows-typing
        {χs = χ ∷ targetTailChanges inner} mode-suc
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒)))


quotient-id-down-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ D D′ : Ty}
    {d d′ s s′} {χ : StoreChange}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρᵇ ρ) →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} pC) →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ C ⊒ D →
  narrowing ⊢ᶜ d ⦂ s →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ C′ ⊒ D′ →
  narrowing ⊢ᶜ d′ ⦂ s′ →
  s ；⌊ pC ⌋≋ᵖ qD ； s′ →
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
quotient-id-down-transportᵀ
    {χ = χ} prefix indexed d⊒ d-shape d′⊒ d′-shape square =
  down⊑downᵀ
    (source-fixed-narrowingᵀ
      (modeRename-id-only suc) prefix inner d⊒)
    (cast-shape-applyCoercions
      (sourceChanges inner) d-shape)
    (target-fixed-narrowingᵀ
      (modeRename-id-only suc) prefix inner d′⊒)
    (cast-shape-applyCoercions
      (χ ∷ targetTailChanges inner) d′-shape)
    (canonicalIndexedResults indexed)
    (weak-one-step-transport-quotientᵀ inner _)
    (weak-one-step-transport-quotient-boundary-square
      inner (weakIndexedTypeCoherence indexed) square)
  where
  inner = weakIndexedResult indexed


quotient-gen-down-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ D D′ : Ty}
    {d d′ s s′} {χ : StoreChange}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρᵇ ρ) →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} pC) →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ
    ⊢ d ∶ C ⊒ D →
  narrowing ⊢ᶜ d ⦂ s →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ
    ⊢ d′ ∶ C′ ⊒ D′ →
  narrowing ⊢ᶜ d′ ⦂ s′ →
  s ；⌊ pC ⌋≋ᵖ qD ； s′ →
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
quotient-gen-down-transportᵀ
    {χ = χ} prefix indexed d⊒ d-shape d′⊒ d′-shape square =
  gen-down⊑gen-downᵀ
    (source-fixed-narrowingᵀ
      (modeRename-gen-tag-or-id suc) prefix inner d⊒)
    (cast-shape-applyCoercions
      (sourceChanges inner) d-shape)
    (target-fixed-narrowingᵀ
      (modeRename-gen-tag-or-id suc) prefix inner d′⊒)
    (cast-shape-applyCoercions
      (χ ∷ targetTailChanges inner) d′-shape)
    (canonicalIndexedResults indexed)
    (weak-one-step-transport-quotientᵀ inner _)
    (weak-one-step-transport-quotient-boundary-square
      inner (weakIndexedTypeCoherence indexed) square)
  where
  inner = weakIndexedResult indexed
