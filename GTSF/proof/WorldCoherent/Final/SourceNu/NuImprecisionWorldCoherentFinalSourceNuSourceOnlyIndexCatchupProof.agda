module
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuSourceOnlyIndexCatchupProof
  where

-- File Charter:
--   * Proves exact-final ordinary source-`ν` catch-up for the source-only
--     universal precision index.
--   * Allocates the coherent source world, delegates bullet and reveal
--     catch-up through whole theorem dependencies, and prepends the `ν` step.
--   * Records the source lift and fresh allocation as explicit store lineage.
--   * Contains no recursive dispatcher, postulates, or permissive holes.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym)

open import Conversion using (RevealConversion)
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_
  ; _↦_
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ∀ⁱ_
  ) renaming (ν to νⁱ)
open import NuReduction using
  (bind; keep; ν-step; ↠-refl; ↠-step)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-left
  ; rightStoreⁱ-lift-left
  ; store-left
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; ok-no
  ; ok-•
  ; ok-⟨⟩
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( conv↑⊑ᵀ
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; _⇒_
  ; `∀
  ; extᵗ
  ; renameᵗ
  ; ⇑ᵗ
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( rename-assm²-source-νᵢ
  ; rename-assm²-⇑ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  )
open import proof.NuCore.Relations.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-source-only-head)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-source)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (lift-left-store-embeddingⁱ)
open import proof.Left.Core.NuImprecisionLeftLiftPrefixBodyDef using
  (LeftLiftPrefixBodyᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( equality-proof-unique
  ; renameᵗ-ext-id
  ; transport-all-⊑ᵢ
  ; transport-arrow-⊑ᵢ
  ; ⊑-source-lift-source-nuᵢ
  ; ⊑-source-under-rightᵢ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftSilentIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepIndexedResult
  ; left-silent-indexed
  ; left-silent-invariant
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.Source.Core.NuImprecisionSourceBulletBase using
  (left-allocated-bulletᵀ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (weak-step-store-lineage)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma using
  (world-coherent-left-allocation)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentTypeShapeProof
  using (shape-source-liftνᵢ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupComposition using
  (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuSourceOnlyIndexCatchupDef
  using (WorldCoherentFinalSourceNuSourceOnlyIndexCatchupᵀ)
open import proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceBulletCatchupDef using
  (WorldCoherentSourceBulletCatchupᵀ)
open import proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceRevealCatchupDef using
  (WorldCoherentSourceRevealCatchupᵀ)
open import proof.Core.Properties.NuStoreProperties using (StoreWf-bind)
open import
  proof.Core.Properties.NuImprecisionSourceNuLiftProperties
  using
  ( replace-left-source-liftν-source-nu-bodyᵢ
  ; replace-left-source-liftνᵢ
  ; replace-paired-source-liftν-under-∀ᵢ
  ; replace-paired-source-liftνᵢ
  ; replace-right-source-liftν-under-rightᵢ
  ; replace-right-source-liftνᵢ
  ; source-liftν-right-body-shapeᵢ
  )
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-ext; TyRenameWf-suc; renameᵗ-id)


private
  source-lift-under-∀ᵢ :
    ∀ {Φ Δᴸ Δᴿ A B} →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
    ((zero ˣ⊑ˣ zero) ∷
      ⇑ᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      ∣ suc (suc Δᴸ)
      ⊢ renameᵗ (extᵗ suc) A ⊑ B
      ⊣ suc Δᴿ
  source-lift-under-∀ᵢ {B = B} p =
    subst
      (λ T → _ ∣ _ ⊢ renameᵗ (extᵗ suc) _ ⊑ T ⊣ _)
      (renameᵗ-ext-id B)
      (⊑-renameᵗ²ᵢ
        (rename-assm²-⇑ᵢ rename-assm²-source-νᵢ)
        (TyRenameWf-ext TyRenameWf-suc)
        (TyRenameWf-ext (λ X<Δ → X<Δ)) p)

  source-lift-arrowᵢ :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′}
      (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
      (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
    ⊑-source-liftνᵢ (pA ↦ pB) ≡
      ⊑-source-liftνᵢ pA ↦ ⊑-source-liftνᵢ pB
  source-lift-arrowᵢ {A′ = A′} {B′ = B′} pA pB
      rewrite equality-proof-unique
          (renameᵗ-id (A′ ⇒ B′))
          (cong₂ _⇒_ (renameᵗ-id A′) (renameᵗ-id B′)) =
    transport-arrow-⊑ᵢ
      refl (renameᵗ-id A′) refl (renameᵗ-id B′)

  source-lift-allᵢ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ) →
    ⊑-source-liftνᵢ (∀ⁱ p) ≡
      ∀ⁱ (source-lift-under-∀ᵢ p)
  source-lift-allᵢ {A = A} {B = B} p
      rewrite equality-proof-unique
          (renameᵗ-id (`∀ B))
          (cong `∀ (renameᵗ-ext-id B)) =
    transport-all-⊑ᵢ refl (renameᵗ-ext-id B)


world-coherent-final-source-ν-source-only-index-catchup-proofᵀ :
  LeftLiftPrefixBodyᵀ →
  WorldCoherentSourceBulletCatchupᵀ →
  WorldCoherentSourceRevealCatchupᵀ →
  WorldCoherentFinalSourceNuSourceOnlyIndexCatchupᵀ
world-coherent-final-source-ν-source-only-index-catchup-proofᵀ
    left-lift-prefix-body bullet-catchup reveal-catchup
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {ρ′ = ρ′} {L = L} {V′ = V′}
    {A = A} {B = B} {B′ = B′} {C = C} {s = s}
    {μ = μ} {p = p} {r = r} {{safe = safe}} {occ = occ}
    coherent exclusive unique wfL hA h⇑A s↑ liftρ liftγ
    vL noL vV′ noV′ L⊑V′ replacement =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    allocation-silent allocation-lineage cast-catchup
  where
  allocated :
    StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ
  allocated = store-left zero (⇑ᵗ A) h⇑A ∷ ρ′

  allocated-store-eq =
    cong ((zero , ⇑ᵗ A) ∷_) (leftStoreⁱ-lift-left liftρ)

  allocated-wf : StoreWf (suc Δᴸ) (leftStoreⁱ allocated)
  allocated-wf =
    subst (StoreWf (suc Δᴸ)) (sym allocated-store-eq)
      (StoreWf-bind wfL hA)

  allocated-reveal :
    RevealConversion μ (suc Δᴸ) (leftStoreⁱ allocated)
      zero (⇑ᵗ A) s C (⇑ᵗ B)
  allocated-reveal =
    subst
      (λ Σ → RevealConversion μ (suc Δᴸ) Σ
        zero (⇑ᵗ A) s C (⇑ᵗ B))
      (sym allocated-store-eq) s↑

  allocated-bullet =
    left-allocated-bulletᵀ {{safe = safe}} vL noL h⇑A liftρ L⊑V′

  bullet-result =
    bullet-catchup h⇑A prefix-reflⁱ
      (world-coherent-left-allocation liftρ coherent)
      (source-name-exclusive-source-only-head exclusive)
      (assumption-membership-unique-source unique)
      allocated-wf (ok-• vL noL) vV′ noV′ vL noL
      liftρ liftγ L⊑V′
      (nu-term-imprecision-source-typing allocated-bullet)
      (nu-term-imprecision-target-typing allocated-bullet)

  cast-catchup =
    reveal-catchup prefix-reflⁱ allocated-reveal
      vV′ noV′ bullet-result (⊑-source-liftνᵢ p) replacement

  allocation-result :
    WeakOneStepResult ρ (ν A L s) V′ B B′ keep
  allocation-result =
    record
      { sourceChanges = bind A ∷ []
      ; targetTailChanges = []
      ; sourceResult = ((⇑ᵗᵐ L) •) ⟨ s ⟩
      ; targetResult = V′
      ; resultCtx = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ
      ; resultLeftCtx = suc Δᴸ
      ; resultRightCtx = Δᴿ
      ; sourceCtxResult = refl
      ; targetCtxResult = refl
      ; resultStore = allocated
      ; resultSourceType = ⇑ᵗ B
      ; resultTargetType = B′
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = ⊑-source-liftνᵢ
      ; transportAllBody = source-lift-under-∀ᵢ
      ; transportRightBody = ⊑-source-under-rightᵢ
      ; transportSourceNu = ⊑-source-lift-source-nuᵢ
      ; resultType = ⊑-source-liftνᵢ p
      ; sourceCatchup = ↠-step (ν-step vL noL) ↠-refl
      ; targetTail = ↠-refl
      ; sourceStoreResult = allocated-store-eq
      ; targetStoreResult = rightStoreⁱ-lift-left liftρ
      ; relatedResults = conv↑⊑ᵀ allocated-reveal allocated-bullet
          (⊑-source-liftνᵢ p) replacement
      }

  allocation-indexed : WeakOneStepIndexedResult p
  allocation-indexed =
    weak-indexed-result allocation-result
      (conv↑⊑ᵀ allocated-reveal allocated-bullet
        (⊑-source-liftνᵢ p) replacement)
      (weak-step-transport
        (left-lift-prefix-body liftρ
          (prefix-∷ⁱ prefix-reflⁱ)))
      (weak-step-type-coherence source-lift-arrowᵢ source-lift-allᵢ
        shape-source-liftνᵢ source-liftν-right-body-shapeᵢ
        replace-left-source-liftνᵢ replace-right-source-liftνᵢ
        replace-paired-source-liftνᵢ
        replace-paired-source-liftν-under-∀ᵢ
        replace-left-source-liftν-source-nu-bodyᵢ
        replace-right-source-liftν-under-rightᵢ)

  allocation-silent : LeftSilentIndexedResult p
  allocation-silent =
    left-silent-indexed allocation-indexed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-• vL noL))

  allocation-lineage =
    weak-step-store-lineage ρ′
      (lift-left-store-embeddingⁱ liftρ)
      (prefix-∷ⁱ prefix-reflⁱ)
