module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationFromPairedLambdaAccProof
  where

-- File Charter:
--   * Proves the generic-root arbitrary-tail direct paired-lambda inert
--     target-allocation cell from the exact raw allocation prefix, the
--     strictly smaller pending-cast worker call, and source-silent
--     continuation.
--   * Uses the exact three-successor rank equation after shifting the pending
--     tail through the right allocation.
--   * Aligns the proof-relevant raw result index with the transported outer
--     index using final assumption-membership uniqueness.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     termination bypass, catch-all clause, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (⇑ᶜ)
open import Data.List using ([]; map; _∷_)
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (<-trans; n<1+n)
open import Data.Product using (_,_)
open import Induction.WellFounded using (acc)
open import Relation.Binary.PropositionalEquality using
  (subst; sym)

open import NuTerms using
  ( RuntimeOK
  ; no•-Λ
  ; no•-⟨⟩
  ; ok-no
  ; ok-⟨⟩
  ; Λ_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using (prefix-reflⁱ)
open import Types using (`∀)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( resultType
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureDef
  using
  (TargetPairedLambdaRightAllocationContinuationRankDecreaseᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (applyTargetPendingCasts)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingAllocationContinuationContextDef
  using
  (WorldCoherentRightTargetPendingAllocationContinuationContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsAccDef
  using (WorldCoherentRightTargetPendingCastsAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationAccCellsDef
  using
  (WorldCoherentRightTargetPendingNuAllocationFromPairedLambdaAccᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixᵀ)


private
  triple-successor-rank-decrease :
    ∀ {inner outer} →
    outer ≡ suc (suc (suc inner)) →
    inner < outer
  triple-successor-rank-decrease {inner} equality =
    subst
      (inner <_)
      (sym equality)
      (<-trans
        (n<1+n inner)
        (<-trans
          (n<1+n (suc inner))
          (n<1+n (suc (suc inner)))))

  apply-pending-runtime :
    ∀ cs {M} →
    RuntimeOK M →
    RuntimeOK (applyTargetPendingCasts M cs)
  apply-pending-runtime [] runtime = runtime
  apply-pending-runtime (c ∷ cs) runtime =
    apply-pending-runtime cs (ok-⟨⟩ runtime)


world-coherent-right-target-pending-nu-allocation-from-paired-lambda-acc-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixᵀ →
  WorldCoherentRightTargetPendingAllocationContinuationContextᵀ →
  WorldCoherentRightTargetPendingCastsAccᵀ →
  TargetPairedLambdaRightAllocationContinuationRankDecreaseᵀ →
  WorldCoherentRightTargetPendingNuAllocationFromPairedLambdaAccᵀ
world-coherent-right-target-pending-nu-allocation-from-paired-lambda-acc-proofᵀ
    prefix continuation pending-worker rank-decrease
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {W = W} {W′ = W′} {D = D} {F = F}
    {s = s} {cs = cs} {f = f} {q = q}
    vW′ (acc smaller) mode seal★ cast inert tail
    coherent exclusive unique wfR runtime
    vW noW noW′ liftρ liftγ body
    with prefix
      {f = f}
      prefix-reflⁱ coherent exclusive unique wfR runtime
      vW noW vW′ noW′ mode seal★ cast inert
      liftρ liftγ body tail
world-coherent-right-target-pending-nu-allocation-from-paired-lambda-acc-proofᵀ
    prefix continuation pending-worker rank-decrease
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {W = W} {W′ = W′} {D = D} {F = F}
    {s = s} {cs = cs} {f = f} {q = q}
    vW′ (acc smaller) mode seal★ cast inert tail
    coherent exclusive unique wfR runtime
    vW noW noW′ liftρ liftγ body
    | indexed ,
      refl , refl , refl , refl , refl , refl ,
      post-beta , allocated-tail ,
      lineage ,
      allocated-coherent ,
      allocated-exclusive ,
      allocated-unique ,
      allocated-wfR ,
      allocation-context ,
      allocation-prefix ,
      allocation-bullet
    with pending-worker
      (vW′ ⟨ inert ⟩)
      (smaller
        (triple-successor-rank-decrease
          (rank-decrease vW′ inert cs)))
      allocated-tail
      allocated-coherent
      allocated-exclusive
      allocated-unique
      allocated-wfR
      (apply-pending-runtime
        (map ⇑ᶜ cs)
        (ok-⟨⟩ (ok-no noW′)))
      (Λ vW)
      (no•-Λ noW)
      (no•-⟨⟩ noW′)
      post-beta
world-coherent-right-target-pending-nu-allocation-from-paired-lambda-acc-proofᵀ
    prefix continuation pending-worker rank-decrease
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {W = W} {W′ = W′} {D = D} {F = F}
    {s = s} {cs = cs} {f = f} {q = q}
    vW′ (acc smaller) mode seal★ cast inert tail
    coherent exclusive unique wfR runtime
    vW noW noW′ liftρ liftγ body
    | indexed ,
      refl , refl , refl , refl , refl , refl ,
      post-beta , allocated-tail ,
      lineage ,
      allocated-coherent ,
      allocated-exclusive ,
      allocated-unique ,
      allocated-wfR ,
      allocation-context ,
      allocation-prefix ,
      allocation-bullet
    | continued , continued-context , continued-prefix
    with assumption-membership-unique→precision-index-unique
      allocated-unique
      (resultType (weakIndexedResult indexed))
      (transportType (weakIndexedResult indexed) q)
world-coherent-right-target-pending-nu-allocation-from-paired-lambda-acc-proofᵀ
    prefix continuation pending-worker rank-decrease
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {W = W} {W′ = W′} {D = D} {F = F}
    {s = s} {cs = cs} {f = f} {q = q}
    vW′ (acc smaller) mode seal★ cast inert tail
    coherent exclusive unique wfR runtime
    vW noW noW′ liftρ liftγ body
    | indexed ,
      refl , refl , refl , refl , refl , refl ,
      post-beta , allocated-tail ,
      lineage ,
      allocated-coherent ,
      allocated-exclusive ,
      allocated-unique ,
      allocated-wfR ,
      allocation-context ,
      allocation-prefix ,
      allocation-bullet
    | continued , continued-context , continued-prefix
    | refl =
  continuation
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {W = W} {W′ = W′} {D = `∀ D} {F = F}
    {s = s} {cs = cs} {t = q}
    indexed refl refl refl
    lineage allocation-bullet
    allocation-context allocation-prefix
    continued continued-context continued-prefix
