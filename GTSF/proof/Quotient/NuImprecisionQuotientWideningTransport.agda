module proof.Quotient.NuImprecisionQuotientWideningTransport where

-- File Charter:
--   * Transports quotient widening pairs through a left-silent result.
--   * Preserves both id-only and general cast-mode widening evidence.
--   * Depends on stable result fields and focused widening transport only.
--   * Imports no simulation core, catch-up dispatcher, or recursive proof.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Coercions using (id-onlyᵈ)
open import NarrowWiden using
  ( widen-weaken
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  (applyTyCtxs; applyTys; keep)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import TermTyping using (SealModeStore★)
open import proof.Core.Properties.CoercionProperties using (modeRename-id-only)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftSilentInvariant
  ; WeakOneStepResult
  ; left-silent-invariant
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetStoreResult
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Core.Properties.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using (applyCoercions)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


weak-one-step-transport-quotient-widening-pairᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D D′ A A′ u u′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  QuotientWideningPair
    (resultLeftCtx inner) (resultRightCtx inner) (resultStore inner)
    (applyCoercions (sourceChanges inner) u) u′
    (applyTys (sourceChanges inner) D) D′
    (applyTys (sourceChanges inner) A) A′
weak-one-step-transport-quotient-widening-pairᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    prefix inner (left-silent-invariant refl refl)
    (quotient-id-widening u⊑ u′⊑) =
  quotient-id-widening source-u target-u
  where
  source-u⁺ = widen-weaken ≤-refl
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

  target-u⁺ = widen-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) u′⊑

  target-u =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ _ ∶ D′ ⊑ A′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ ∣ Δᴿ ∣ Σ ⊢ _ ∶ D′ ⊑ A′)
        (sym (targetStoreResult inner)) target-u⁺)
weak-one-step-transport-quotient-widening-pairᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    prefix inner (left-silent-invariant refl refl)
    (quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑)
    with apply-widens-typing
      { χs = sourceChanges inner }
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) u⊑)
weak-one-step-transport-quotient-widening-pairᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    prefix inner (left-silent-invariant refl refl)
    (quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑)
    | μˢ , modeˢ , seal★ˢ , uˢ⊑ =
  quotient-cast-widening
    modeˢ source-seal★ source-u
    mode′ target-seal★ target-u
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

  target-seal★⁺ = seal★-weaken
    (rightStoreⁱ-prefix-inclusion prefix) seal★′

  target-seal★ =
    subst (SealModeStore★ _)
      (sym (targetStoreResult inner)) target-seal★⁺

  target-u⁺ = widen-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) u′⊑

  target-u =
    subst
      (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ _ ∶ D′ ⊑ A′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → _ ∣ Δᴿ ∣ Σ ⊢ _ ∶ D′ ⊑ A′)
        (sym (targetStoreResult inner)) target-u⁺)
