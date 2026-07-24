module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixProof
  where

-- File Charter:
--   * Builds the exact source-silent paired-lambda target-allocation prefix
--     beneath an arbitrary hereditary pending-cast spine for an arbitrary
--     universal root.
--   * Uses the exact pending allocation trace, transports the spine through
--     the allocation, and folds the shifted spine over the post-beta QTI
--     relation to obtain the final indexed relation.
--   * Retains generic transport, type coherence, right-only lineage, final
--     world invariants, context action, and source-bullet transport for exact
--     source-silent composition with the smaller pending-cast result.
--   * Contains no recursive catch-up dispatcher, postulate, hole, permissive
--     option, termination bypass, catch-all clause, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions
open import Coercions using (inst)
import Data.List
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
import Data.Product
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Relation.Binary.HeterogeneousEquality as HE
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)

open import Imprecision using (⇑ᴿᵢ)
import NuReduction
open import NuReduction using
  (bind; keep; ↠-refl)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-right
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-right
  ; store-right
  )
open import NuStore using (StoreWf)
import NuTerms
open import NuTerms using
  ( no•-Λ
  ; no•-⟨⟩
  ; ok-⟨⟩
  ; Λ_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( Λ⊑Λᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import TermTyping using (_∣_∣_⊢_⦂_; ⊢⟨⟩⊑)
import Types
open import Types using (`∀; wf★; ⇑ᵗ; ★)
open import
  proof.Catchup.Simulation.NuImprecisionSimulation
  using
  ( right-lift-prefix-bodyᵀ
  ; ⊑-target-lift-right-all-coherentᵢ
  ; ⊑-target-lift-right-arrow-coherentᵢ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using
  ( ≡-to-≅
  ; transportAllType-to-raw≅
  ; transportArrowType-to-raw≅
  ; ⊑-target-lift-right-source-nuᵢ
  ; ⊑-target-lift-right-under-∀ᵢ
  ; ⊑-target-lift-under-rightᵢ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; transportAllType
  ; transportArrowType
  ; weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.Core.Properties.NuStoreProperties using
  (StoreWf-bind)
open import proof.Core.Properties.TypePreservation using
  (multi-preservation; term-weaken)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (⊑-target-lift-rightᵢ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-⇑ᴿᵢ)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityProof
  using (source-name-exclusive-⇑ᴿᵢ)
open import
  proof.Right.AllocationRuntime.NuImprecisionRightTargetAllocationSourceBulletTransportDef
  using (RightTargetAllocationSourceBulletTransportᵀ)
open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix
  using
  (right-only-prefix-refl; right-only-prefix-right)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import proof.Store.Core.NuImprecisionStoreLift using
  (lift-right-store-result)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (lift-right-store-embeddingⁱ)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationSpineRightAllocationDef
  using (TargetAdministrationSpineRightAllocationᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using
  ( TargetAdministrationSpine
  ; applyTargetPendingCasts
  ; pending-cons
  ; pending-empty
  )
open import
  proof.Target.Administration.NuImprecisionTargetPendingLambdaAllocationTraceDef
  using (TargetPendingLambdaAllocationTraceᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma
  using (world-coherent-right-allocation)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ)


private
  apply-target-administration-spine :
    ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
      {V W A B D p q cs} →
    TargetAdministrationSpine ρ A p q cs →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ W ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ applyTargetPendingCasts W cs
        ⦂ A ⊑ D ∶ q
  apply-target-administration-spine pending-empty relation =
    relation
  apply-target-administration-spine
      (pending-cons {r = r} plan
        (inj₁ (μ′ , β , X′ , reveal)) tail)
      relation =
    apply-target-administration-spine tail
      (⊑conv↑ᵀ reveal relation r)
  apply-target-administration-spine
      (pending-cons {r = r} plan
        (inj₂ (inj₁ (μ′ , β , X′ , conceal))) tail)
      relation =
    apply-target-administration-spine tail
      (⊑conv↓ᵀ conceal relation r)
  apply-target-administration-spine
      (pending-cons {r = r} plan
        (inj₂ (inj₂ (inj₁
          (μ′ , mode , seal★ , narrowing)))) tail)
      relation =
    apply-target-administration-spine tail
      (⊑cast⊒ᵀ mode seal★ narrowing relation r)
  apply-target-administration-spine
      (pending-cons {r = r} plan
        (inj₂ (inj₂ (inj₂ (inj₁
          (μ′ , mode , seal★ , widening))))) tail)
      relation =
    apply-target-administration-spine tail
      (⊑cast⊑ᵀ mode seal★ widening relation r)
  apply-target-administration-spine
      (pending-cons {r = r} plan
        (inj₂ (inj₂ (inj₂ (inj₂
          (seal★ , widening))))) tail)
      relation =
    apply-target-administration-spine tail
      (⊑cast⊑idᵀ seal★ widening relation r)


world-coherent-right-target-widen-instantiation-paired-lambda-pending-allocation-prefix-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ →
  RightTargetAllocationSourceBulletTransportᵀ →
  TargetAdministrationSpineRightAllocationᵀ →
  TargetPendingLambdaAllocationTraceᵀ →
  WorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixᵀ
world-coherent-right-target-widen-instantiation-paired-lambda-pending-allocation-prefix-proofᵀ
    post-beta bullet allocate-spine allocation-trace
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ⁺ = ρ⁺} {W = W} {W′ = W′}
    {B = B} {C = C} {D = D} {F = F}
    {s = s} {cs = cs}
    {f = f} {t = t}
    prefix coherent exclusive unique wfR runtime
    vW noW vW′ noW′ mode seal★ cast inert liftρ liftγ body tail =
  indexed ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  post-beta-related ,
  allocated-tail ,
  lineage ,
  final-coherent ,
  final-exclusive ,
  final-unique ,
  final-wf ,
  refl ,
  right-only-prefix-right right-only-prefix-refl ,
  source-bullet
  where
  outer = Λ⊑Λᵀ liftρ liftγ vW vW′ body

  source-typing⁺ :
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ Λ W ⦂ `∀ D
  source-typing⁺ =
    term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      (no•-Λ noW) (nu-term-imprecision-source-typing outer)

  initial-target-typing :
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ []
      ⊢ (Λ W′) ⟨ inst B s ⟩ ⦂ B
  initial-target-typing =
    term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      (no•-⟨⟩ (no•-Λ noW′))
      (⊢⟨⟩⊑ mode seal★ cast
        (nu-term-imprecision-target-typing outer))

  ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)
  ρᴿ⁺ = Data.Product.proj₁ (lift-right-store-result ρ⁺)

  liftρᴿ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ⁺ ρᴿ⁺
  liftρᴿ = Data.Product.proj₂ (lift-right-store-result ρ⁺)

  source-typing :
    Δᴸ ∣ leftStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
      ∣ [] ⊢ Λ W ⦂ `∀ D
  source-typing =
    subst
      (λ Σ → Δᴸ ∣ Σ ∣ [] ⊢ Λ W ⦂ `∀ D)
      (sym (leftStoreⁱ-lift-right liftρᴿ))
      source-typing⁺

  target-store-eq :
    rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
      ≡ (zero , ★) ∷ Types.⟰ᵗ (rightStoreⁱ ρ⁺)
  target-store-eq =
    cong ((zero , ★) ∷_) (rightStoreⁱ-lift-right liftρᴿ)

  full-target-trace :
    (Λ W′) ⟨ inst B s ⟩
      NuReduction.—↠[
        keep ∷ bind ★ ∷ keep ∷ [] ]
      W′ ⟨ s ⟩
  full-target-trace =
    NuReduction.↠-step
      (NuReduction.pure-step (NuReduction.β-inst (Λ vW′)))
      (allocation-trace
        {W′ = W′} {s = s} {cs = []} vW′ noW′)

  target-typing :
    suc Δᴿ ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
      ∣ [] ⊢ W′ ⟨ s ⟩ ⦂ ⇑ᵗ B
  target-typing =
    subst
      (λ Σ → suc Δᴿ ∣ Σ ∣ [] ⊢ W′ ⟨ s ⟩ ⦂ ⇑ᵗ B)
      (sym target-store-eq)
      (multi-preservation wfR
        (ok-⟨⟩ (NuTerms.ok-no (no•-Λ noW′)))
        initial-target-typing full-target-trace)

  post-beta-related =
    post-beta {f = f} prefix mode seal★ cast liftρ liftρᴿ
      vW noW vW′ noW′ inert body source-typing target-typing

  allocated-tail =
    allocate-spine liftρᴿ tail

  related =
    apply-target-administration-spine
      allocated-tail post-beta-related

  target-tail =
    allocation-trace
      {W′ = W′} {s = s} {cs = cs} vW′ noW′

  result :
    WeakOneStepResult ρ⁺ (Λ W)
      (applyTargetPendingCasts
        (NuTerms.ν ★ (Λ W′) s) cs)
      (`∀ D) F keep
  result =
    weak-step-result
      [] (bind ★ ∷ keep ∷ [])
      (Λ W)
      (applyTargetPendingCasts
        (W′ ⟨ s ⟩) (Data.List.map Coercions.⇑ᶜ cs))
      (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ) refl refl
      (store-right zero ★ wf★ ∷ ρᴿ⁺)
      (`∀ D) (⇑ᵗ F) refl refl
      ⊑-target-lift-rightᵢ
      ⊑-target-lift-right-under-∀ᵢ
      ⊑-target-lift-under-rightᵢ
      ⊑-target-lift-right-source-nuᵢ
      (⊑-target-lift-rightᵢ t)
      ↠-refl target-tail
      (leftStoreⁱ-lift-right liftρᴿ)
      target-store-eq
      related

  transport =
    weak-step-transport
      (right-lift-prefix-bodyᵀ
        liftρᴿ (prefix-∷ⁱ prefix-reflⁱ))

  type-coherence =
    weak-step-type-coherence
      (λ pD pE → HE.≅-to-≡
        (HE.trans
          (transportArrowType-to-raw≅ result pD pE)
          (≡-to-≅
            (⊑-target-lift-right-arrow-coherentᵢ pD pE))))
      (λ r → HE.≅-to-≡
        (HE.trans
          (transportAllType-to-raw≅ result r)
          (≡-to-≅
            (⊑-target-lift-right-all-coherentᵢ r))))

  indexed =
    weak-indexed-result result related transport type-coherence

  lineage =
    weak-step-store-lineage ρᴿ⁺
      (lift-right-store-embeddingⁱ liftρᴿ)
      (prefix-∷ⁱ prefix-reflⁱ)

  source-bullet :
    RightValueCatchupSourceBulletTransportᵀ result
  source-bullet prefix′ okL noM′ L⊢ L⊑M′ =
    bullet prefix′ liftρᴿ unique okL noM′ L⊢ L⊑M′

  final-coherent =
    world-coherent-right-allocation liftρᴿ coherent

  final-exclusive =
    source-name-exclusive-⇑ᴿᵢ exclusive

  final-unique =
    assumption-membership-unique-⇑ᴿᵢ unique

  final-wf :
    StoreWf (suc Δᴿ)
      (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺))
  final-wf =
    subst
      (λ Σ → StoreWf (suc Δᴿ) Σ)
      (sym target-store-eq)
      (StoreWf-bind wfR wf★)
