module
  proof.NuImprecisionRightSilentQuotientWideningPairTransportProof
  where

-- File Charter:
--   * Implements right-silent transport for quotient widening pairs.
--   * Keeps the source side silent by rewriting with the explicit source
--     result equalities.
--   * Transports the accumulating target coercion and endpoint types through
--     the target tail changes.
--   * Exports only the frozen right-silent quotient-widening transport proof.

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
open import NuReduction using (applyTyCtxs; applyTys)
open import NuTermImprecision using (leftStoreⁱ; rightStoreⁱ)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import TermTyping using (SealModeStore★)
open import proof.CoercionProperties using (modeRename-id-only)
open import
  proof.NuImprecisionRightSilentQuotientWideningPairTransportDef using
  (RightSilentQuotientWideningPairTransportᵀ)
open import proof.NuImprecisionSimulationResultDef using
  ( resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  )
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.ReductionProperties using (applyCoercions)
open import proof.TypePreservation using (seal★-weaken)


right-silent-quotient-widening-pair-transport-proofᵀ :
  RightSilentQuotientWideningPairTransportᵀ
right-silent-quotient-widening-pair-transport-proofᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    prefix inner refl refl
    (quotient-id-widening u⊑ u′⊑) =
  quotient-id-widening source-u target-u
  where
  source-u⁺ = widen-weaken ≤-refl
    (leftStoreⁱ-prefix-inclusion prefix) u⊑

  source-u =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ _ ∶ D ⊑ A)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ ∣ Δᴸ ∣ Σ ⊢ _ ∶ D ⊑ A)
        (sym (sourceStoreResult inner)) source-u⁺)

  target-u⁺ = widen-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) u′⊑

  target-u⁺⁺ = apply-fixed-widens-typing
    {χs = targetTailChanges inner}
    (modeRename-id-only suc) target-u⁺

  target-u =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) _
          ∶ applyTys (targetTailChanges inner) D′
            ⊑ applyTys (targetTailChanges inner) A′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ
          ∣ Σ ⊢ applyCoercions (targetTailChanges inner) _
          ∶ applyTys (targetTailChanges inner) D′
            ⊑ applyTys (targetTailChanges inner) A′)
        (sym (targetStoreResult inner)) target-u⁺⁺)
right-silent-quotient-widening-pair-transport-proofᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    prefix inner refl refl
    (quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑)
    with apply-widens-typing
      {χs = targetTailChanges inner}
      mode′
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) u′⊑)
right-silent-quotient-widening-pair-transport-proofᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    prefix inner refl refl
    (quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑)
    | μ′ᵗ , mode′ᵗ , seal★′ᵗ , u′ᵗ⊑ =
  quotient-cast-widening
    mode source-seal★ source-u
    mode′ᵗ target-seal★ target-u
  where
  source-seal★⁺ = seal★-weaken
    (leftStoreⁱ-prefix-inclusion prefix) seal★

  source-seal★ =
    subst (SealModeStore★ _)
      (sym (sourceStoreResult inner)) source-seal★⁺

  source-u⁺ = widen-weaken ≤-refl
    (leftStoreⁱ-prefix-inclusion prefix) u⊑

  source-u =
    subst
      (λ Δ → _ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ _ ∶ D ⊑ A)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → _ ∣ Δᴸ ∣ Σ ⊢ _ ∶ D ⊑ A)
        (sym (sourceStoreResult inner)) source-u⁺)

  target-seal★ =
    subst (SealModeStore★ μ′ᵗ)
      (sym (targetStoreResult inner)) seal★′ᵗ

  target-u =
    subst
      (λ Δ → μ′ᵗ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) _
          ∶ applyTys (targetTailChanges inner) D′
            ⊑ applyTys (targetTailChanges inner) A′)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μ′ᵗ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ
          ∣ Σ ⊢ applyCoercions (targetTailChanges inner) _
          ∶ applyTys (targetTailChanges inner) D′
            ⊑ applyTys (targetTailChanges inner) A′)
        (sym (targetStoreResult inner)) u′ᵗ⊑)
