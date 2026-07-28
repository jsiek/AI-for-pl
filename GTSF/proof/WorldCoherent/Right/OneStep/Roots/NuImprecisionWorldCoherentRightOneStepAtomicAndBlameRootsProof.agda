module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepAtomicAndBlameRootsProof
  where

-- File Charter:
--   * Implements the atomic-identity and target-blame leaves for
--     world-coherent target-oriented one-step simulation.
--   * Uses exact atomic target reindexing and completed target-blame catch-up.
--   * Contains no recursive dispatcher, postulate, hole, or permissive option.

open import Data.List using ([])
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( keep
  ; ↠-refl
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; Value
  ; blame
  )
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  ( Atom
  ; Ty
  ; TyCtx
  )
open import proof.OneStep.NuImprecisionAtomicTargetReindex using
  (atomic-target-value-reindexᵀ)
open import proof.OneStep.NuImprecisionOneStepRelated using
  (weak-one-step-indexed-relatedᵀ)
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (left-catchup-target-blameᵀ)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepAtomicAndBlameRootsDef
  using (WorldCoherentRightOneStepAtomicAndBlameRoots)


world-coherent-right-one-step-atomic-and-blame-roots-proofᵀ :
  WorldCoherentRightOneStepAtomicAndBlameRoots
world-coherent-right-one-step-atomic-and-blame-roots-proofᵀ =
  record
    { rightStepSourceBlameRoot =
        world-indexed-outcome-source-blame ↠-refl
    ; rightStepTargetAtomicIdentityRoot = atomic-identity
    ; rightStepTargetBlameRoot = target-blame
    }
  where
  atomic-identity :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V : Term} {A B : Ty}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    Atom B →
    Value V →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ V ⦂ A ⊑ B ∶ p →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = V} {χ = keep} {ρ = ρ} q
  atomic-identity {q = q} coherent exclusive unique atom vV M⊑V =
    world-indexed-outcome-related
      (weak-one-step-indexed-relatedᵀ
        (atomic-target-value-reindexᵀ atom vV M⊑V q))
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique

  target-blame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M : Term} {A B C : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    RuntimeOK M →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ blame ⦂ A ⊑ B ∶ p →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = blame} {χ = keep} {ρ = ρ} q
  target-blame okM M⊑blame
      with left-catchup-target-blameᵀ okM M⊑blame
  target-blame okM M⊑blame | χs , M↠blame =
    world-indexed-outcome-source-blame M↠blame
