module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsProof
  where

-- File Charter:
--   * Proves the four semantic target-allocation roots for world-coherent
--     target-oriented one-step simulation.
--   * Catches up the source before matched allocation, stops immediately on
--     source blame, and preserves relational-store lineage through allocation.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     or `blame-ν` root.

open import Agda.Builtin.Equality using (refl)
import CastImprecisionShape as CastShape
open import Coercions using (instᵈ)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
import Relation.Binary.HeterogeneousEquality as HE

open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ⇑ᵢ
  ; ⇑ᴿᵢ
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( bind
  ; blame-ν
  ; keep
  ; _—→[_]_
  ; ν-step
  ; ↠-refl
  ; ↠-step
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; blame
  ; no•-ν
  ; ok-no
  ; ok-ν
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; prefix-∷ⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; ★
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ; ⊑-target-lift-rightᵢ)
open import proof.Core.Properties.ReductionProperties using (ν-↠; ↠-trans)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (imprecision-composition-shape-transport; shape-target-lift-rightᵢ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( weak-indexed-all-resultᵀ
  ; weak-one-step-index-resultᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftCatchupIndexedResult
  ; WeakOneStepIndexedOutcome
  ; WeakOneStepIndexedResult
  ; catchupIndexedInvariant
  ; catchupIndexedResult
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  ; left-all-catchup
  ; left-catchup-invariant
  ; left-indexed-all-catchup
  ; left-indexed-catchup
  ; left-silent-invariant
  ; relatedResults
  ; resultStore
  ; sourceCatchup
  ; sourceIsValueOrBlame
  ; weakIndexedResult
  ; weakIndexedTypeCoherence
  )
open import proof.NuCore.Misc.NuImprecisionAllocationSimulation using
  ( weak-one-step-matched-ν↑-indexed-catchup-outcomeᵀ
  ; weak-one-step-matched-ν↑-value-catchupᵀ
  ; weak-one-step-matched-νcast-indexed-catchup-outcomeᵀ
  ; weak-one-step-matched-νcast-value-catchupᵀ
  ; weak-one-step-right-ν↑-type-coherenceᵀ
  ; weak-one-step-right-ν↑-transportᵀ
  ; weak-one-step-right-ν↑ᵀ
  ; weak-one-step-right-νcast-type-coherenceᵀ
  ; weak-one-step-right-νcast-transportᵀ
  ; weak-one-step-right-νcastᵀ
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-⇑ᴿᵢ
  )
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityProof
  using
  ( source-name-exclusive-matched-head
  ; source-name-exclusive-⇑ᴿᵢ
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof
  using (weak-one-step-prepend-left-silent-store-lineageᵀ)
open import proof.Store.Core.NuImprecisionStoreLift using
  (lift-store-result)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (lift-right-store-embeddingⁱ; lift-store-embeddingⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma
  using
  ( world-coherent-matched-allocation
  ; world-coherent-right-allocation
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; WorldCoherentLeftCatchupIndexedResult
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


ν-runtime : ∀ {A N s} → RuntimeOK (ν A N s) → RuntimeOK N
ν-runtime (ok-no (no•-ν no-N)) = ok-no no-N
ν-runtime (ok-ν ok-N) = ok-N


matched-nu-allocation :
  WorldCoherentLeftValueCatchupᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A A′ B B′ C C′ : Ty} {N V′ N′ : Term}
    {s s′} {μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (ν A N s) →
  RuntimeOK (ν A′ V′ s′) →
  WfTy Δᴸ A →
  WfTy Δᴿ A′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB →
  ν A′ V′ s′ —→[ bind A′ ] N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = ν A N s} {N′ = N′}
    {χ = bind A′} {ρ = ρ} pB
matched-nu-allocation
    catchup {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    coherent exclusive unique wfL wfR ok-source ok-target hA hA′
    s↑ s′↑ N⊑V′ replace (ν-step vV′ noV′)
    with catchup coherent exclusive unique wfL
      (ν-runtime ok-source) vV′ noV′ N⊑V′
matched-nu-allocation
    catchup {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    coherent exclusive unique wfL wfR ok-source ok-target hA hA′
    s↑ s′↑ N⊑V′ replace (ν-step vV′ noV′)
    | world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    with final
matched-nu-allocation
    catchup {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    coherent exclusive unique wfL wfR ok-source ok-target hA hA′
    s↑ s′↑ N⊑V′ replace (ν-step vV′ noV′)
    | world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₂ refl =
  world-indexed-outcome-source-blame
    (↠-trans
      (ν-↠ (sourceCatchup (weakIndexedResult indexed)))
      (↠-step blame-ν ↠-refl))
matched-nu-allocation
    catchup {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    coherent exclusive unique wfL wfR ok-source ok-target hA hA′
    s↑ s′↑ N⊑V′ replace (ν-step vV′ noV′)
    | world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₁ (vW , noW)
    with weak-one-step-matched-ν↑-indexed-catchup-outcomeᵀ
      wfR s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′
      (left-indexed-all-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) (inj₁ (vW , noW))))
matched-nu-allocation
    catchup {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    coherent exclusive unique wfL wfR ok-source ok-target hA hA′
    s↑ s′↑ N⊑V′ replace (ν-step vV′ noV′)
    | world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₁ (vW , noW)
    | indexed-outcome-related final-indexed =
  world-indexed-outcome-related
    final-indexed
    (world-coherent-matched-allocation liftρ⁺ final-coherent)
    (source-name-exclusive-matched-head final-exclusive)
    (assumption-membership-unique-matched final-unique)
  where
  raw =
    weak-one-step-matched-ν↑-value-catchupᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′
      (left-all-catchup
        (weak-indexed-all-resultᵀ indexed)
        (left-catchup-invariant
          (left-silent-invariant refl refl) (inj₁ (vW , noW))))
      vW noW (weakIndexedTypeCoherence indexed)

  liftρ⁺ = proj₂ (lift-store-result
    (resultStore (weakIndexedResult indexed)))

  combined-lineage : WeakOneStepStoreLineage raw
  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      _ _
      (weak-step-store-lineage
        (lineageStore caught-lineage)
        (lineageEmbedding caught-lineage)
        (lineagePrefix caught-lineage))
      (weak-step-store-lineage _
        (lift-store-embeddingⁱ liftρ⁺)
        (prefix-∷ⁱ prefix-reflⁱ))
matched-nu-allocation
    catchup {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    coherent exclusive unique wfL wfR ok-source ok-target hA hA′
    s↑ s′↑ N⊑V′ replace (ν-step vV′ noV′)
    | world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₁ (vW , noW)
    | indexed-outcome-source-blame source-blame =
  world-indexed-outcome-source-blame source-blame


target-nu-allocation :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {A B B′ C′ : Ty} {N V′ N′ : Term}
    {s} {μ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK N →
  RuntimeOK (ν A V′ s) →
  WfTy Δᴿ A →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ B ⊑ `∀ C′ ∶ q →
  pC [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ pB →
  ν A V′ s —→[ bind A ] N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = N} {N′ = N′} {χ = bind A} {ρ = ρ} pB
target-nu-allocation
    {pB = pB} coherent exclusive unique wfL wfR
    ok-source ok-target hA h⇑A s↑ liftρ pC N⊑V′ replace
    (ν-step vV′ noV′) =
  world-indexed-outcome-related
    indexed
    (world-coherent-right-allocation liftρ coherent)
    (source-name-exclusive-⇑ᴿᵢ exclusive)
    (assumption-membership-unique-⇑ᴿᵢ unique)
  where
  result = weak-one-step-right-ν↑ᵀ
    vV′ noV′ h⇑A s↑ pB pC replace liftρ N⊑V′

  indexed : WeakOneStepIndexedResult pB
  indexed =
    weak-one-step-index-resultᵀ result refl
      (weak-one-step-right-ν↑-transportᵀ
        vV′ noV′ h⇑A s↑ pB pC replace liftρ N⊑V′)
      (weak-one-step-right-ν↑-type-coherenceᵀ
        vV′ noV′ h⇑A s↑ pB pC replace liftρ N⊑V′)


target-nu-cast-allocation :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {B B′ C′ : Ty} {N V′ N′ : Term}
    {s} {μ} {s-shape : ImprecisionShape}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK N →
  RuntimeOK (ν ★ V′ s) →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ B ⊑ `∀ C′ ∶ q →
  CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
  ⌊ pC ⌋ ； s-shape ≋ ⌊ pB ⌋ →
  ν ★ V′ s —→[ bind ★ ] N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = N} {N′ = N′} {χ = bind ★} {ρ = ρ} pB
target-nu-cast-allocation
    {pB = pB} coherent exclusive unique wfL wfR
    ok-source ok-target mode seal★ s⊑ liftρ pC N⊑V′
    s-shape-proof comp (ν-step vV′ noV′) =
  world-indexed-outcome-related
    indexed
    (world-coherent-right-allocation liftρ coherent)
    (source-name-exclusive-⇑ᴿᵢ exclusive)
    (assumption-membership-unique-⇑ᴿᵢ unique)
  where
  comp′ =
    imprecision-composition-shape-transport
      refl refl (shape-target-lift-rightᵢ pB) comp

  result = weak-one-step-right-νcastᵀ
    vV′ noV′ mode seal★ s⊑ pB pC
    s-shape-proof comp′ liftρ N⊑V′

  indexed : WeakOneStepIndexedResult pB
  indexed =
    weak-one-step-index-resultᵀ result refl
      (weak-one-step-right-νcast-transportᵀ
        vV′ noV′ mode seal★ s⊑ pB pC
        s-shape-proof comp′ liftρ N⊑V′)
      (weak-one-step-right-νcast-type-coherenceᵀ
        vV′ noV′ mode seal★ s⊑ pB pC
        s-shape-proof comp′ liftρ N⊑V′)
