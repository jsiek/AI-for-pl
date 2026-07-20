module proof.NuDGGWeakResultPreservation where

-- File Charter:
--   * States the runtime and store invariants needed to recurse from a weak
--     one-step result during terminal trace simulation.
--   * Separates these mechanical preservation transports from the
--     well-founded terminal induction.
--   * Exports four checked result-level preservation facts for terminal
--     simulation.

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (subst₂; sym)

open import NuReduction using
  ( StoreChange
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; _∣_∣_⊢_⦂_)
open import proof.NuImprecisionSimulationCore using
  ( WeakOneStepResult
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceResult
  ; sourceCatchup
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetResult
  ; targetCtxResult
  ; targetStoreResult
  ; targetTail
  )
open import proof.NuDGGPreservation using (multi-store-preservation)
open import proof.NuPreservation using
  ( multi-runtime-preservation
  ; preservation
  ; runtime-preservation
  ; store-preservation
  )


weak-result-source-store-wf :
  ∀ {Φ Δᴸ Δᴿ M N′ A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : WeakOneStepResult ρ M N′ A B χ) →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK M →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A →
  StoreWf (resultLeftCtx result)
    (leftStoreⁱ (resultStore result))
weak-result-source-store-wf result wfΣ okM M⊢ =
  subst₂ StoreWf
    (sym (sourceCtxResult result))
    (sym (sourceStoreResult result))
    (multi-store-preservation wfΣ okM M⊢ (sourceCatchup result))

weak-result-source-runtime :
  ∀ {Φ Δᴸ Δᴿ M N′ A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : WeakOneStepResult ρ M N′ A B χ) →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK M →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A →
  RuntimeOK (sourceResult result)
weak-result-source-runtime result wfΣ okM M⊢ =
  multi-runtime-preservation wfΣ okM M⊢ (sourceCatchup result)

weak-result-target-store-wf :
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : WeakOneStepResult ρ M N′ A B χ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M′ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ B →
  M′ —→[ χ ] N′ →
  StoreWf (resultRightCtx result)
    (rightStoreⁱ (resultStore result))
weak-result-target-store-wf result wfΣ okM M⊢ red =
  subst₂ StoreWf
    (sym (targetCtxResult result))
    (sym (targetStoreResult result))
    (multi-store-preservation
      (store-preservation wfΣ M⊢ red)
      (runtime-preservation wfΣ okM M⊢ red)
      (preservation wfΣ okM M⊢ red)
      (targetTail result))

weak-result-target-runtime :
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : WeakOneStepResult ρ M N′ A B χ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M′ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ B →
  M′ —→[ χ ] N′ →
  RuntimeOK (targetResult result)
weak-result-target-runtime result wfΣ okM M⊢ red =
  multi-runtime-preservation
    (store-preservation wfΣ M⊢ red)
    (runtime-preservation wfΣ okM M⊢ red)
    (preservation wfΣ okM M⊢ red)
    (targetTail result)
