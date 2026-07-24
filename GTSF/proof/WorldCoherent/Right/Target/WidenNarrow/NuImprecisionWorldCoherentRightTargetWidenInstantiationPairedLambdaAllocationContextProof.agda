module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextProof
  where

-- File Charter:
--   * Assembles the inert paired-lambda target allocation and administrative
--     type-application step into the complete right-value catch-up result.
--   * Takes the independent source-bullet right-allocation transport theorem
--     as an explicit higher-order dependency.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (inst)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁; proj₂)
import Relation.Binary.HeterogeneousEquality as HE
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)

open import Imprecision using (⇑ᴿᵢ)
open import ImprecisionWf using (ν)
open import NuReduction using
  ( bind
  ; keep
  ; pure-step
  ; ν-step
  ; β-inst
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
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
  )
open import TermTyping using (_∣_∣_⊢_⦂_; ⊢⟨⟩⊑)
open import Types using (`∀; wf★; ⇑ᵗ; ★)
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( post-allocation-β-Λ•
  ; right-lift-prefix-bodyᵀ
  ; ⊑-target-lift-right-all-coherentᵢ
  ; ⊑-target-lift-right-arrow-coherentᵢ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
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
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (right-only-prefix-refl; right-only-prefix-right)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (right-value-indexed-catchup)
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
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma
  using (world-coherent-right-allocation)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (world-coherent-right-value-indexed-catchup)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ)


world-coherent-right-target-widen-instantiation-paired-lambda-allocation-context-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ →
  RightTargetAllocationSourceBulletTransportᵀ →
  WorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextᵀ
world-coherent-right-target-widen-instantiation-paired-lambda-allocation-context-proofᵀ
    post-beta bullet
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D} {s = s}
    {{safe = safe}} {q = q} {occ = occ}
    prefix coherent exclusive unique wfR runtime
    vW noW vW′ noW′ mode seal★ cast inert liftρ liftγ body =
  caught , refl , right-only-prefix-right right-only-prefix-refl
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

  full-target-trace :
    (Λ W′) ⟨ inst B s ⟩
      —↠[ keep ∷ bind ★ ∷ keep ∷ [] ] W′ ⟨ s ⟩
  full-target-trace =
    ↠-step (pure-step (β-inst (Λ vW′)))
      (↠-step (ν-step (Λ vW′) (no•-Λ noW′))
        (↠-step (post-allocation-β-Λ• vW′) ↠-refl))

  ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)
  ρᴿ⁺ = proj₁ (lift-right-store-result ρ⁺)

  liftρᴿ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ⁺ ρᴿ⁺
  liftρᴿ = proj₂ (lift-right-store-result ρ⁺)

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

  related :
    ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ
      ∣ store-right zero ★ wf★ ∷ ρᴿ⁺ ∣ []
      ⊢ᴺ Λ W ⊑ W′ ⟨ s ⟩
        ⦂ `∀ D ⊑ ⇑ᵗ B
        ∶ ⊑-target-lift-rightᵢ (ν safe occ q)
  related =
    post-beta {f = ν safe occ q} prefix mode seal★ cast liftρ liftρᴿ
      vW noW vW′ noW′ inert body source-typing target-typing

  target-tail :
    NuTerms.ν ★ (Λ W′) s
      —↠[ bind ★ ∷ keep ∷ [] ] W′ ⟨ s ⟩
  target-tail =
    ↠-step (ν-step (Λ vW′) (no•-Λ noW′))
      (↠-step (post-allocation-β-Λ• vW′) ↠-refl)

  result :
    WeakOneStepResult ρ⁺ (Λ W) (NuTerms.ν ★ (Λ W′) s)
      (`∀ D) B keep
  result =
    weak-step-result
      [] (bind ★ ∷ keep ∷ [])
      (Λ W) (W′ ⟨ s ⟩)
      (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ) refl refl
      (store-right zero ★ wf★ ∷ ρᴿ⁺)
      (`∀ D) (⇑ᵗ B) refl refl
      ⊑-target-lift-rightᵢ
      ⊑-target-lift-right-under-∀ᵢ
      ⊑-target-lift-under-rightᵢ
      ⊑-target-lift-right-source-nuᵢ
      (⊑-target-lift-rightᵢ (ν safe occ q))
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

  catchup =
    right-value-indexed-catchup indexed refl refl
      (Λ vW) (no•-Λ noW)
      (vW′ ⟨ inert ⟩) (no•-⟨⟩ noW′)

  lineage =
    weak-step-store-lineage ρᴿ⁺
      (lift-right-store-embeddingⁱ liftρᴿ)
      (prefix-∷ⁱ prefix-reflⁱ)

  source-bullet :
    RightValueCatchupSourceBulletTransportᵀ result
  source-bullet prefix′ okL noM′ L⊢ L⊑M′ =
    bullet prefix′ liftρᴿ unique okL noM′ L⊢ L⊑M′

  final-wf :
    StoreWf (suc Δᴿ)
      (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺))
  final-wf =
    subst
      (λ Σ → StoreWf (suc Δᴿ) Σ)
      (sym target-store-eq)
      (StoreWf-bind wfR wf★)

  caught =
    world-coherent-right-value-indexed-catchup
      catchup lineage source-bullet
      (world-coherent-right-allocation liftρᴿ coherent)
      (source-name-exclusive-⇑ᴿᵢ exclusive)
      (assumption-membership-unique-⇑ᴿᵢ unique)
      final-wf
