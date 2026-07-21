module
  proof.NuImprecisionWorldCoherentRightTargetPendingSequenceContinuationDef
  where

-- File Charter:
--   * Defines the strictly smaller pending-sequence continuations consumed
--     by world-coherent right-target sequence resumption.
--   * Keeps only the reachable narrowing, widening, and identity-only
--     widening entries; reveal and conceal conversions contain no sequence.
--   * Takes hereditary subplans and the final canonical value relation, and
--     returns the existing complete right-value catch-up result directly.
--   * The explicit rank equation is discharged by
--     `target-sequence-rank-decreases` at recursive call sites.
--   * Contains no simulation result, view, outcome, implementation,
--     postulate, hole, permissive option, or termination bypass.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (proj₁)

open import Coercions using (Coercion; ModeEnv; id-onlyᵈ; _︔_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionTargetAdministrationMeasureDef using
  (targetPendingAdministrationRank)
open import proof.NuImprecisionTargetAdministrationPlanDef using
  (TargetAdministrationPlan)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.NuImprecisionWorldCoherentRightCatchupResultDef
  using (WorldCoherentRightValueCatchupIndexedResult)


record WorldCoherentRightTargetPendingSequenceContinuation : Set₁ where
  field
    rightTargetPendingNarrowSequence :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {V W : Term} {A B C D : Ty} {s t : Coercion} {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
      (vW : Value W) →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ) →
      (s⊒ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ B ⊒ C) →
      (t⊒ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C ⊒ D) →
      TargetAdministrationPlan ρ A (proj₁ s⊒) p r →
      TargetAdministrationPlan ρ A (proj₁ t⊒) r q →
      targetPendingAdministrationRank vW ((s ︔ t) ∷ []) ≡
        suc (targetPendingAdministrationRank vW (s ∷ t ∷ [])) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ W ⦂ A ⊑ B ∶ p →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK ((W ⟨ s ⟩) ⟨ t ⟩) →
      Value V →
      No• V →
      No• W →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = (W ⟨ s ⟩) ⟨ t ⟩} {ρ = ρ} q

    rightTargetPendingWidenSequence :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {V W : Term} {A B C D : Ty} {s t : Coercion} {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
      (vW : Value W) →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ) →
      (s⊑ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ B ⊑ C) →
      (t⊑ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C ⊑ D) →
      TargetAdministrationPlan ρ A (proj₁ s⊑) p r →
      TargetAdministrationPlan ρ A (proj₁ t⊑) r q →
      targetPendingAdministrationRank vW ((s ︔ t) ∷ []) ≡
        suc (targetPendingAdministrationRank vW (s ∷ t ∷ [])) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ W ⦂ A ⊑ B ∶ p →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK ((W ⟨ s ⟩) ⟨ t ⟩) →
      Value V →
      No• V →
      No• W →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = (W ⟨ s ⟩) ⟨ t ⟩} {ρ = ρ} q

    rightTargetPendingIdWidenSequence :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {V W : Term} {A B C D : Ty} {s t : Coercion}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
      (vW : Value W) →
      SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
      (s⊑ : id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ s ∶ B ⊑ C) →
      (t⊑ : id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ t ∶ C ⊑ D) →
      TargetAdministrationPlan ρ A (proj₁ s⊑) p r →
      TargetAdministrationPlan ρ A (proj₁ t⊑) r q →
      targetPendingAdministrationRank vW ((s ︔ t) ∷ []) ≡
        suc (targetPendingAdministrationRank vW (s ∷ t ∷ [])) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ W ⦂ A ⊑ B ∶ p →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK ((W ⟨ s ⟩) ⟨ t ⟩) →
      Value V →
      No• V →
      No• W →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = (W ⟨ s ⟩) ⟨ t ⟩} {ρ = ρ} q

open WorldCoherentRightTargetPendingSequenceContinuation public
