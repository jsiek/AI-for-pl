module proof.OneStep.NuImprecisionOneStepTargetCastFrames where

-- File Charter:
--   * Freezes the three target-cast frames needed by the indexed one-step
--     dispatcher, both as exact related-result builders and outcome wrappers.
--   * Each wrapper consumes an already-computed inner indexed outcome and
--     frames only a target ξ-⟨⟩ step; root cast reductions are outside its
--     scope.
--   * The target coercion receives the inner step's store change, while the
--     source term, store imprecision, and store-change index stay unchanged.
--   * Contains exactly the three intended target-cast frame cases.

open import CastImprecisionShape using (_⊢ᶜ_⦂_)
import CastImprecisionShape as CastShape using (narrowing; widening)
open import Coercions using
  (id-onlyᵈ; id-only≤tag-or-idᵈ)
open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( widen-mode-relax
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( applyCoercion
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; rightStoreⁱ
  )
open import proof.Core.Properties.SealModeProperties using
  (seal★-tag-or-id)
open import NuTerms using (_⟨_⟩)
open import QuotientedTermImprecision using
  ( ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  )
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)
open import TermTyping using
  (CastMode; SealModeStore★; cast-tag-or-id)
open import
  proof.Catchup.Simulation.NuImprecisionKeepCastFrameSupport
  using
  ( weak-one-step-target-cast-frameᵀ
  ; weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  )
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-narrows-typing)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedOutcome
  ; WeakOneStepIndexedResult
  ; canonicalIndexedResults
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  ; relatedResults
  ; resultRightCtx
  ; resultStore
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportShapeCoherent
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.Core.Properties.ReductionProperties using (applyCoercions)
open import proof.Core.Properties.NuWideningTransport using
  (apply-widens-typing)


weak-one-step-target-narrow-cast-indexed-frame-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ χ}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  WeakOneStepIndexedResult
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  CastShape.narrowing ⊢ᶜ c′ ⦂ s →
  ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
  WeakOneStepIndexedResult
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-narrow-cast-indexed-frame-relatedᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ}
    {p = p}
    mode seal★ c′⊒
    indexed q c-shape comp
    with apply-narrows-typing
      {χs = χ ∷ targetTailChanges (weakIndexedResult indexed)}
      mode seal★ c′⊒
weak-one-step-target-narrow-cast-indexed-frame-relatedᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ}
    {p = p}
    mode seal★ c′⊒
    indexed q c-shape comp
    | μ″ , mode″ , seal★″ , c″⊒ =
  weak-indexed-result framed (relatedResults framed)
    framed-transport framed-coherence
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
      (cast-shape-applyCoercions
        (χ ∷ targetTailChanges inner) c-shape)
      (imprecision-composition-shape-transport
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) q)
        refl
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) p)
        comp)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)
  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)
weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ χ}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  CastShape.narrowing ⊢ᶜ c′ ⦂ s →
  ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ
    mode seal★ c′⊒ (indexed-outcome-related indexed)
    q c-shape comp =
  indexed-outcome-related
    (weak-one-step-target-narrow-cast-indexed-frame-relatedᵀ
      mode seal★ c′⊒ indexed q c-shape comp)
weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ
    mode seal★ c′⊒
    (indexed-outcome-source-blame source↠) q c-shape comp =
  indexed-outcome-source-blame source↠


weak-one-step-target-widen-cast-indexed-frame-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ χ}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  WeakOneStepIndexedResult
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  CastShape.widening ⊢ᶜ c′ ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  WeakOneStepIndexedResult
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-widen-cast-indexed-frame-relatedᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ}
    {p = p}
    mode seal★ c′⊑
    indexed q c-shape comp
    with apply-widens-typing
      {χs = χ ∷ targetTailChanges (weakIndexedResult indexed)}
      mode seal★ c′⊑
weak-one-step-target-widen-cast-indexed-frame-relatedᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ}
    {p = p}
    mode seal★ c′⊑
    indexed q c-shape comp
    | μ″ , mode″ , seal★″ , c″⊑ =
  weak-indexed-result framed (relatedResults framed)
    framed-transport framed-coherence
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
      (cast-shape-applyCoercions
        (χ ∷ targetTailChanges inner) c-shape)
      (imprecision-composition-shape-transport
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) p)
        refl
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) q)
        comp)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)
  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)
weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ χ}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  CastShape.widening ⊢ᶜ c′ ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ
    mode seal★ c′⊑ (indexed-outcome-related indexed)
    q c-shape comp =
  indexed-outcome-related
    (weak-one-step-target-widen-cast-indexed-frame-relatedᵀ
      mode seal★ c′⊑ indexed q c-shape comp)
weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ
    mode seal★ c′⊑
    (indexed-outcome-source-blame source↠) q c-shape comp =
  indexed-outcome-source-blame source↠


weak-one-step-target-widen-id-cast-indexed-frame-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ χ}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  WeakOneStepIndexedResult
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  CastShape.widening ⊢ᶜ c′ ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  WeakOneStepIndexedResult
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-widen-id-cast-indexed-frame-relatedᵀ
    seal★ c′⊑ indexed q c-shape comp =
  weak-one-step-target-widen-cast-indexed-frame-relatedᵀ
    cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ c′⊑)
    indexed q c-shape comp
weak-one-step-target-widen-id-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ χ}
    {s : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  CastShape.widening ⊢ᶜ c′ ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-widen-id-cast-indexed-frame-outcomeᵀ
    seal★ c′⊑ (indexed-outcome-related indexed)
    q c-shape comp =
  indexed-outcome-related
    (weak-one-step-target-widen-id-cast-indexed-frame-relatedᵀ
      seal★ c′⊑ indexed q c-shape comp)
weak-one-step-target-widen-id-cast-indexed-frame-outcomeᵀ
    seal★ c′⊑
    (indexed-outcome-source-blame source↠) q c-shape comp =
  indexed-outcome-source-blame source↠
