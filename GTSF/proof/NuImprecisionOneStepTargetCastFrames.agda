module proof.NuImprecisionOneStepTargetCastFrames where

-- File Charter:
--   * Freezes the three outcome-level target-cast frames needed by the
--     indexed one-step dispatcher.
--   * Each wrapper consumes an already-computed inner indexed outcome and
--     frames only a target ξ-⟨⟩ step; root cast reductions are outside its
--     scope.
--   * The target coercion receives the inner step's store change, while the
--     source term, store imprecision, and store-change index stay unchanged.
--   * Contains exactly the three intended leaf-proof wrappers.

open import Coercions using (id-onlyᵈ)
open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( applyCoercion
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  )
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (_⟨_⟩)
open import QuotientedTermImprecision using
  ( ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  )
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import TermTyping using (CastMode; SealModeStore★)
open import proof.NuImprecisionSimulation using
  ( weak-one-step-target-cast-frameᵀ
  ; weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  )
open import proof.NuImprecisionSimulationCore using
  ( WeakOneStepIndexedOutcome
  ; apply-fixed-widens-typing
  ; apply-narrows-typing
  ; apply-widens-typing
  ; canonicalIndexedResults
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  ; modeRename-id-only
  ; relatedResults
  ; resultRightCtx
  ; resultStore
  ; seal★-id-only
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  )
open import proof.ReductionProperties using (applyCoercions)


weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ}
    mode seal★ c′⊒
    (indexed-outcome-related indexed transport coherence) q
    with apply-narrows-typing
      {χs = χ ∷ targetTailChanges (weakIndexedResult indexed)}
      mode seal★ c′⊒
weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ}
    mode seal★ c′⊒
    (indexed-outcome-related indexed transport coherence) q
    | μ″ , mode″ , seal★″ , c″⊒ =
  indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed))
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation transport)
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation coherence)
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ″)
      (sym (targetStoreResult inner)) seal★″

  final-cast :
    μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) (applyCoercion χ c′)
      ∶ applyTys (targetTailChanges inner) (applyTy χ A′)
        ⊒ applyTys (targetTailChanges inner) (applyTy χ B′)
  final-cast =
    subst
      (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) (applyCoercion χ c′)
        ∶ applyTys (targetTailChanges inner) (applyTy χ A′)
          ⊒ applyTys (targetTailChanges inner) (applyTy χ B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μ″
          ∣ applyTyCtxs (targetTailChanges inner) (applyTyCtx χ Δᴿ)
          ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion χ c′)
          ∶ applyTys (targetTailChanges inner) (applyTy χ A′)
            ⊒ applyTys (targetTailChanges inner) (applyTy χ B′))
        (sym (targetStoreResult inner)) c″⊒)

  final-relation =
    ⊑cast⊒ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ
    mode seal★ c′⊒
    (indexed-outcome-source-blame source↠) q =
  indexed-outcome-source-blame source↠


weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ}
    mode seal★ c′⊑
    (indexed-outcome-related indexed transport coherence) q
    with apply-widens-typing
      {χs = χ ∷ targetTailChanges (weakIndexedResult indexed)}
      mode seal★ c′⊑
weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ}
    mode seal★ c′⊑
    (indexed-outcome-related indexed transport coherence) q
    | μ″ , mode″ , seal★″ , c″⊑ =
  indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed))
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation transport)
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation coherence)
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ″)
      (sym (targetStoreResult inner)) seal★″

  final-cast :
    μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) (applyCoercion χ c′)
      ∶ applyTys (targetTailChanges inner) (applyTy χ A′)
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
  final-cast =
    subst
      (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) (applyCoercion χ c′)
        ∶ applyTys (targetTailChanges inner) (applyTy χ A′)
          ⊑ applyTys (targetTailChanges inner) (applyTy χ B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μ″
          ∣ applyTyCtxs (targetTailChanges inner) (applyTyCtx χ Δᴿ)
          ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion χ c′)
          ∶ applyTys (targetTailChanges inner) (applyTy χ A′)
            ⊑ applyTys (targetTailChanges inner) (applyTy χ B′))
        (sym (targetStoreResult inner)) c″⊑)

  final-relation =
    ⊑cast⊑ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ
    mode seal★ c′⊑
    (indexed-outcome-source-blame source↠) q =
  indexed-outcome-source-blame source↠


weak-one-step-target-widen-id-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-widen-id-cast-indexed-frame-outcomeᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ}
    seal★ c′⊑
    (indexed-outcome-related indexed transport coherence) q =
  indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed))
    (weak-one-step-target-cast-frame-transportᵀ
      inner final-relation transport)
    (weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation coherence)
  where
  inner = weakIndexedResult indexed

  c″⊑ =
    apply-fixed-widens-typing
      {χs = χ ∷ targetTailChanges inner}
      (modeRename-id-only suc) c′⊑

  final-cast :
    id-onlyᵈ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) (applyCoercion χ c′)
      ∶ applyTys (targetTailChanges inner) (applyTy χ A′)
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
  final-cast =
    subst
      (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) (applyCoercion χ c′)
        ∶ applyTys (targetTailChanges inner) (applyTy χ A′)
          ⊑ applyTys (targetTailChanges inner) (applyTy χ B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → id-onlyᵈ
          ∣ applyTyCtxs (targetTailChanges inner) (applyTyCtx χ Δᴿ)
          ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion χ c′)
          ∶ applyTys (targetTailChanges inner) (applyTy χ A′)
            ⊑ applyTys (targetTailChanges inner) (applyTy χ B′))
        (sym (targetStoreResult inner)) c″⊑)

  final-relation =
    ⊑cast⊑idᵀ seal★-id-only final-cast
      (canonicalIndexedResults indexed) (transportType inner q)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
weak-one-step-target-widen-id-cast-indexed-frame-outcomeᵀ
    seal★ c′⊑
    (indexed-outcome-source-blame source↠) q =
  indexed-outcome-source-blame source↠
