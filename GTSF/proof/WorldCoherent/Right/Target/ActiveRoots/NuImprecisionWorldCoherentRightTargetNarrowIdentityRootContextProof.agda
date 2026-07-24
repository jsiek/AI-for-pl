module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowIdentityRootContextProof
  where

-- File Charter:
--   * Proves all three contextual active target-narrowing identity roots.
--   * Builds the final framed relation by transporting the narrowing cast,
--     then delegates the shared `β-id` resumption to its higher-order
--     contextual contract.
--   * Contains no catch-all case, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Coercions as C
open import Coercions using (ModeEnv)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (narrow-weaken; _∣_∣_⊢_∶_⊒_)
import NarrowWiden as NW
open import NuReduction using
  (applyTyCtxs; applyTys; keep)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; ⊑cast⊒ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; ＇_; ‵_; ★)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (apply-narrows-typing)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; world-coherent-right-value-indexed-catchup
  ; worldRightCatchupResult
  )
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetIdentityRootContextDef
  using (WorldCoherentRightTargetIdentityRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowIdentityRootContextDef
  using (WorldCoherentRightTargetNarrowIdentityRootContextᵀ)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken)


private
  narrow-framed-relation :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty} {μ : ModeEnv}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ C.id B ∶ B ⊒ B →
    (inner-world :
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p) →
    (let catchup = worldRightCatchupResult inner-world
         indexed = rightCatchupIndexedResult catchup
         inner = weakIndexedResult indexed in
     resultCtx inner
       ∣ resultLeftCtx inner
       ∣ resultRightCtx inner
       ∣ resultStore inner ∣ []
       ⊢ᴺ sourceResult inner ⊑
         targetResult inner
           ⟨ applyCoercions (targetTailChanges inner) (C.id B) ⟩
       ⦂ applyTys (sourceChanges inner) A
         ⊑ applyTys (targetTailChanges inner) B
       ∶ transportType inner q)
  narrow-framed-relation {Δᴿ = Δᴿ} {B = B} {q = q}
      prefix mode seal★ c⊒
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      with apply-narrows-typing
        {χs = keep ∷ targetTailChanges
          (weakIndexedResult (rightCatchupIndexedResult catchup))}
        mode
        (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c⊒)
  narrow-framed-relation {Δᴿ = Δᴿ} {B = B} {q = q}
      prefix mode seal★ c⊒
      inner-world@(world-coherent-right-value-indexed-catchup
        catchup lineage source-bullet final-world final-exclusive final-unique
        final-wfR)
      | μ″ , mode″ , seal★″ , c″⊒ =
    ⊑cast⊒ᵀ mode″ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
    where
    indexed = rightCatchupIndexedResult catchup
    inner = weakIndexedResult indexed

    final-seal :
      SealModeStore★ μ″ (rightStoreⁱ (resultStore inner))
    final-seal =
      subst (SealModeStore★ μ″)
        (sym (targetStoreResult inner)) seal★″

    final-cast :
      μ″ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) (C.id B)
          ∶ applyTys (targetTailChanges inner) B
            ⊒ applyTys (targetTailChanges inner) B
    final-cast =
      subst
        (λ Δ → μ″ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
          ⊢ applyCoercions (targetTailChanges inner) (C.id B)
            ∶ applyTys (targetTailChanges inner) B
              ⊒ applyTys (targetTailChanges inner) B)
        (sym (targetCtxResult inner))
        (subst
          (λ Σ →
            μ″ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
              ⊢ applyCoercions (targetTailChanges inner) (C.id B)
                ∶ applyTys (targetTailChanges inner) B
                  ⊒ applyTys (targetTailChanges inner) B)
          (sym (targetStoreResult inner)) c″⊒)


world-coherent-right-target-narrow-identity-root-context-proofᵀ :
  WorldCoherentRightTargetIdentityRootContextᵀ →
  WorldCoherentRightTargetNarrowIdentityRootContextᵀ
world-coherent-right-target-narrow-identity-root-context-proofᵀ
    identity prefix coherent exclusive unique wfR runtime vV noV mode seal★
    c⊒@(C.cast-id _ _ , NW.cross (NW.id-＇ α))
    relation inner context-eq right-prefix =
  identity (＇ α) inner context-eq right-prefix
    (narrow-framed-relation prefix mode seal★ c⊒ inner)
world-coherent-right-target-narrow-identity-root-context-proofᵀ
    identity prefix coherent exclusive unique wfR runtime vV noV mode seal★
    c⊒@(C.cast-id _ _ , NW.cross (NW.id-‵ ι))
    relation inner context-eq right-prefix =
  identity (‵ ι) inner context-eq right-prefix
    (narrow-framed-relation prefix mode seal★ c⊒ inner)
world-coherent-right-target-narrow-identity-root-context-proofᵀ
    identity prefix coherent exclusive unique wfR runtime vV noV mode seal★
    c⊒@(C.cast-id _ _ , NW.id★)
    relation inner context-eq right-prefix =
  identity ★ inner context-eq right-prefix
    (narrow-framed-relation prefix mode seal★ c⊒ inner)
