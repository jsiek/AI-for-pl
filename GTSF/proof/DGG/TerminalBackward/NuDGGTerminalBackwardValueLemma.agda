module proof.DGG.TerminalBackward.NuDGGTerminalBackwardValueLemma where

-- File Charter:
--   * Assembles the canonical backward target-value terminal lemma from the
--     generic proof and the live one-step/catch-up implementations.
--   * Keeps the expensive live dependency closure out of the Def and Proof
--     modules.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; _—↠[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; Value; blame)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; prefix-reflⁱ
  )
open import proof.DGG.Core.NuDGGClosedWorld using (empty-store-wf)
open import proof.DGG.TerminalBackward.NuDGGTerminalBackwardValueDef using
  (BackwardTargetValueOrSourceBlameᵀ)
open import proof.DGG.TerminalBackward.NuDGGTerminalBackwardValueProof using
  (backward-target-value-or-source-blame-proofᵀ)
open import proof.Catchup.Core.NuImprecisionCatchupScratch using
  ( left-catchup-indexed-prefixᵀ
  ; weak-one-step-indexed-simulationᵀ
  )


backward-target-value-or-source-blame-generalᵀ :
  BackwardTargetValueOrSourceBlameᵀ
backward-target-value-or-source-blame-generalᵀ =
  backward-target-value-or-source-blame-proofᵀ
    weak-one-step-indexed-simulationᵀ
    (λ okM vV′ noV′ M⊑V′ →
      left-catchup-indexed-prefixᵀ
        prefix-reflⁱ okM vV′ noV′ M⊑V′)


backward-target-value-or-source-blameᵀ :
  ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  RuntimeOK N →
  RuntimeOK N′ →
  [] ∣ 0 ∣ 0 ∣ [] ∣ [] ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  ∀ V′ χs′ →
  N′ —↠[ χs′ ] V′ →
  Value V′ →
    (∃[ V ] (Σ[ χs ∈ StoreChanges ]
    (∃[ Φ ] (Σ[ ρ ∈
        StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
    (Σ[ q ∈
        (Φ ∣ applyTyCtxs χs 0
          ⊢ applyTys χs A ⊑ applyTys χs′ B
          ⊣ applyTyCtxs χs′ 0) ]
      ((N —↠[ χs ] V) ×
       Value V ×
       (leftStoreⁱ ρ ≡ applyStores χs []) ×
       (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
       Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
         ⊢ᴺ V ⊑ V′
         ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))
    ⊎ (∃[ χs ] (N —↠[ χs ] blame)))
backward-target-value-or-source-blameᵀ okN okN′ N⊑N′ =
  backward-target-value-or-source-blame-generalᵀ
    empty-store-wf empty-store-wf okN okN′ N⊑N′
