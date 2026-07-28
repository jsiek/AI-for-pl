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

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (_≡_; refl)
import CastImprecisionShape as CastShape
import Coercions
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; id-onlyᵈ
  ; id-only≤tag-or-idᵈ
  ; inst
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using
  (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
import Data.List
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
import Data.Product
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.HeterogeneousEquality as HE
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)

open import Imprecision using (ImpCtx; ⇑ᴿᵢ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import ImprecisionComposition using
  (⌊_⌋; _；_≋_)
open import NarrowWiden using
  (widen-mode-relax; _∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
import NuReduction
open import NuReduction using
  (bind; keep; ↠-refl)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-right
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-right
  ; store-right
  )
open import proof.Core.Properties.SealModeProperties using
  (seal★-tag-or-id)
open import NuStore using (StoreWf)
import NuTerms
open import NuTerms using
  ( Term
  ; no•-Λ
  ; no•-⟨⟩
  ; ok-⟨⟩
  ; Λ_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( Λ⊑Λᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-tag-or-id
  ; _∣_∣_⊢_⦂_
  ; ⊢⟨⟩⊑
  )
import Types
open import Types using (Ty; TyCtx; `∀; wf★; ⇑ᵗ; ★)
open import
  proof.Catchup.Simulation.NuImprecisionSimulation
  using
  ( replace-left-target-lift-right-source-nu-bodyᵢ
  ; replace-paired-target-lift-right-under-∀ᵢ
  ; replace-right-target-lift-under-rightᵢ
  ; shape-target-lift-right-under-∀ᵢ
  ; shape-target-lift-under-rightᵢ
  ; ⊑-target-lift-right-all-coherentᵢ
  ; ⊑-target-lift-right-arrow-coherentᵢ
  )
open import
  proof.Right.AllocationRuntime.NuImprecisionRightLiftPrefixBodyProof
  using (right-lift-prefix-body-proofᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( replace-left-target-lift-rightᵢ
  ; replace-paired-target-lift-rightᵢ
  ; replace-right-target-lift-rightᵢ
  ; ⊑-target-lift-right-source-nuᵢ
  ; ⊑-target-lift-right-under-∀ᵢ
  ; ⊑-target-lift-under-rightᵢ
  )
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( transportAllType-to-raw≅
  ; transportArrowType-to-raw≅
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
  proof.Core.Properties.NuImprecisionIndexedRenamingProperties
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
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (target-instantiation-creation)
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
  proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef
  using
  ( TargetAdministrationPlan
  ; plan-fun-untag-gen
  ; plan-id
  ; plan-id-widen-seq
  ; plan-inert
  ; plan-inst
  ; plan-inst-fun-tag
  ; plan-narrow-seq
  ; plan-unseal
  ; plan-untag
  ; plan-widen-seq
  )
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
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentTypeShapeProof
  using (shape-target-lift-rightᵢ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ)


private
  apply-target-frame-evidence :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {V W : Term} {A B C : Ty} {c : Coercion}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ c B C
        × p [ β ↦ X′ ]ᴿ q)
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ c B C
        × q [ β ↦ X′ ]ᴿ p)
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ c ∶ B ⊒ C)
        × (CastShape.narrowing CastShape.⊢ᶜ c ⦂ shape)
        × (⌊ q ⌋ ； shape ≋ ⌊ p ⌋))
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ c ∶ B ⊑ C)
        × (CastShape.widening CastShape.⊢ᶜ c ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))
     ⊎
     (∃[ shape ]
        SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ)
        × (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ c ∶ B ⊑ C)
        × (CastShape.widening CastShape.⊢ᶜ c ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ W ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ W ⟨ c ⟩ ⦂ A ⊑ C ∶ q
  apply-target-frame-evidence
      (inj₁ (μ′ , β , X′ , reveal , replacement))
      relation =
    ⊑conv↑ᵀ reveal relation _ replacement
  apply-target-frame-evidence
      (inj₂ (inj₁
        (μ′ , β , X′ , conceal , replacement)))
      relation =
    ⊑conv↓ᵀ conceal relation _ replacement
  apply-target-frame-evidence
      (inj₂ (inj₂ (inj₁
        (μ′ , shape , mode , seal★ , narrowing ,
         c-shape , composition))))
      relation =
    ⊑cast⊒ᵀ mode seal★ narrowing relation _
      c-shape composition
  apply-target-frame-evidence
      (inj₂ (inj₂ (inj₂ (inj₁
        (μ′ , shape , mode , seal★ , widening ,
         c-shape , composition)))))
      relation =
    ⊑cast⊑ᵀ mode seal★ widening relation _
      c-shape composition
  apply-target-frame-evidence
      (inj₂ (inj₂ (inj₂ (inj₂
        (shape , seal★ , widening ,
         c-shape , composition)))))
      relation =
    ⊑cast⊑ᵀ cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ widening) relation _
      c-shape composition

  apply-target-administration-plan :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {V W : Term} {A B C : Ty} {μ : ModeEnv}
      {c : Coercion}
      {c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    TargetAdministrationPlan ρ A c⊢ p q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ W ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ W ⟨ c ⟩ ⦂ A ⊑ C ∶ q
  apply-target-administration-plan
      (plan-inert inert evidence) relation =
    apply-target-frame-evidence evidence relation
  apply-target-administration-plan
      (plan-id evidence) relation =
    apply-target-frame-evidence evidence relation
  apply-target-administration-plan {q = q}
      (plan-untag mode seal★ narrowing c-shape composition)
      relation =
    ⊑cast⊒ᵀ mode seal★ narrowing relation q
      c-shape composition
  apply-target-administration-plan
      (plan-unseal evidence) relation =
    apply-target-frame-evidence evidence relation
  apply-target-administration-plan
      (plan-inst evidence) relation =
    apply-target-frame-evidence evidence relation
  apply-target-administration-plan
      (plan-fun-untag-gen evidence) relation =
    apply-target-frame-evidence evidence relation
  apply-target-administration-plan
      (plan-inst-fun-tag evidence) relation =
    apply-target-frame-evidence evidence relation
  apply-target-administration-plan {q = q}
      (plan-narrow-seq
        mode seal★ narrowing sequence-narrowing
        sequence-shape composition
        s-shape s-composition t-shape t-composition
        s-plan t-plan)
      relation =
    ⊑cast⊒ᵀ mode seal★ narrowing relation q
      sequence-shape composition
  apply-target-administration-plan {q = q}
      (plan-widen-seq
        mode seal★ widening sequence-widening
        sequence-shape composition
        s-shape s-composition t-shape t-composition
        s-plan t-plan)
      relation =
    ⊑cast⊑ᵀ mode seal★ widening relation q
      sequence-shape composition
  apply-target-administration-plan {q = q}
      (plan-id-widen-seq
        seal★ widening sequence-widening
        sequence-shape composition
        s-shape s-composition t-shape t-composition
        s-plan t-plan)
      relation =
    ⊑cast⊑ᵀ cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ widening) relation q
      sequence-shape composition

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
      (pending-cons plan tail)
      relation =
    apply-target-administration-spine tail
      (apply-target-administration-plan plan relation)


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
    vW noW vW′ noW′ mode seal★ cast inert liftρ liftγ body
    inst-shape creation-square tail =
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
    post-beta {f = f}
      (target-instantiation-creation
        prefix mode seal★ cast liftρ liftρᴿ
        vW noW vW′ noW′ inert body
        inst-shape creation-square source-typing target-typing)

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
      (right-lift-prefix-body-proofᵀ
        liftρᴿ (prefix-∷ⁱ prefix-reflⁱ))

  type-coherence =
    weak-step-type-coherence
      (λ pD pE → HE.≅-to-≡
        (HE.trans
          (transportArrowType-to-raw≅ result pD pE)
          (HE.≡-to-≅
            (⊑-target-lift-right-arrow-coherentᵢ pD pE))))
      (λ r → HE.≅-to-≡
        (HE.trans
          (transportAllType-to-raw≅ result r)
          (HE.≡-to-≅
            (⊑-target-lift-right-all-coherentᵢ r))))
      shape-target-lift-rightᵢ
      shape-target-lift-under-rightᵢ
      replace-left-target-lift-rightᵢ
      replace-right-target-lift-rightᵢ
      replace-paired-target-lift-rightᵢ
      replace-paired-target-lift-right-under-∀ᵢ
      replace-left-target-lift-right-source-nu-bodyᵢ
      replace-right-target-lift-under-rightᵢ

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
