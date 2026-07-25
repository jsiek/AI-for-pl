module
  proof.Right.Core.NuImprecisionQuotientWideningTransportProof
  where

-- File Charter:
--   * Transports a quotient widening pair through an arbitrary completed
--     target-leading weak one-step result.
--   * Applies the leading target store change before the target tail, while
--     preserving the complete source and target change lists.
--   * Contains no quotient downcast, frame assembly, dispatcher, postulate,
--     hole, permissive option, or compatibility wrapper.

open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Coercions using (Coercion; id-onlyᵈ)
open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import NarrowWiden using
  ( widen-weaken
  ; _∣_∣_⊢_∶_⊑_
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
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import TermTyping using (SealModeStore★)
open import Types using (Ty; TyCtx)
open import ImprecisionWf using (ImpCtx)
open import proof.Core.Properties.CoercionProperties using
  (modeRename-id-only)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Core.Properties.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


quotient-widening-pair-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {M M′ : Term} {C C′ D D′ A A′ : Ty}
    {u u′ : Coercion}
    {χ : StoreChange}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ} →
  (prefix : StoreImpPrefix ρᵇ ρ) →
  (inner : WeakOneStepResult ρ M M′ C C′ χ) →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
  QuotientWideningPair
    (resultLeftCtx inner) (resultRightCtx inner) (resultStore inner)
    (applyCoercions (sourceChanges inner) u)
    (applyCoercions (targetTailChanges inner) (applyCoercion χ u′))
    (applyTys (sourceChanges inner) D)
    (applyTys (targetTailChanges inner) (applyTy χ D′))
    (applyTys (sourceChanges inner) A)
    (applyTys (targetTailChanges inner) (applyTy χ A′))
quotient-widening-pair-transportᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    {u′ = u′} {χ = χ}
    prefix inner (quotient-id-widening u⊑ u′⊑) =
  quotient-id-widening source-u target-u
  where
  source-u⁺ = widen-weaken
    ≤-refl
    (leftStoreⁱ-prefix-inclusion prefix) u⊑

  source-u⁺⁺ = apply-fixed-widens-typing
    {χs = sourceChanges inner}
    (modeRename-id-only suc) source-u⁺

  source-u =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) D
          ⊑ applyTys (sourceChanges inner) A)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ ∣ applyTyCtxs (sourceChanges inner) Δᴸ
          ∣ Σ ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) D
          ⊑ applyTys (sourceChanges inner) A)
        (sym (sourceStoreResult inner)) source-u⁺⁺)

  target-u⁺ = widen-weaken
    ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) u′⊑

  target-u⁺⁺ = apply-fixed-widens-typing
    {χs = χ ∷ targetTailChanges inner}
    (modeRename-id-only suc) target-u⁺

  target-u =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner)
            (applyCoercion χ u′)
          ∶ applyTys (targetTailChanges inner) (applyTy χ D′)
          ⊑ applyTys (targetTailChanges inner) (applyTy χ A′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ
          ∣ applyTyCtxs (targetTailChanges inner) (applyTyCtx χ Δᴿ)
          ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion χ u′)
            ∶ applyTys (targetTailChanges inner) (applyTy χ D′)
            ⊑ applyTys (targetTailChanges inner) (applyTy χ A′))
        (sym (targetStoreResult inner)) target-u⁺⁺)
quotient-widening-pair-transportᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    {u′ = u′} {χ = χ}
    prefix inner
    (quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑)
    with apply-widens-typing
      {χs = sourceChanges inner}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) u⊑)
       | apply-widens-typing
      {χs = χ ∷ targetTailChanges inner}
      mode′
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) u′⊑)
quotient-widening-pair-transportᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    {u′ = u′} {χ = χ}
    prefix inner
    (quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑)
    | μˢ , modeˢ , seal★ˢ , uˢ⊑
    | μᵗ , modeᵗ , seal★ᵗ , uᵗ⊑ =
  quotient-cast-widening
    modeˢ source-seal★ source-u
    modeᵗ target-seal★ target-u
  where
  source-seal★ =
    subst (SealModeStore★ μˢ)
      (sym (sourceStoreResult inner)) seal★ˢ

  source-u =
    subst
      (λ Δ → μˢ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) D
          ⊑ applyTys (sourceChanges inner) A)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μˢ ∣ applyTyCtxs (sourceChanges inner) Δᴸ
          ∣ Σ ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) D
          ⊑ applyTys (sourceChanges inner) A)
        (sym (sourceStoreResult inner)) uˢ⊑)

  target-seal★ =
    subst (SealModeStore★ μᵗ)
      (sym (targetStoreResult inner)) seal★ᵗ

  target-u =
    subst
      (λ Δ → μᵗ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner)
            (applyCoercion χ u′)
          ∶ applyTys (targetTailChanges inner) (applyTy χ D′)
          ⊑ applyTys (targetTailChanges inner) (applyTy χ A′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μᵗ
          ∣ applyTyCtxs (targetTailChanges inner) (applyTyCtx χ Δᴿ)
          ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion χ u′)
            ∶ applyTys (targetTailChanges inner) (applyTy χ D′)
            ⊑ applyTys (targetTailChanges inner) (applyTy χ A′))
        (sym (targetStoreResult inner)) uᵗ⊑)
