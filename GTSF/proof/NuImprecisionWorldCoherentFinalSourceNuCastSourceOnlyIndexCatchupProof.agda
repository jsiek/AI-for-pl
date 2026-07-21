module
  proof.NuImprecisionWorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupProof
  where

-- File Charter:
--   * Proves exact-final source-`ν ★` catch-up for the source-only universal
--     precision index.
--   * Allocates the coherent source world, delegates the post-allocation
--     bullet and widening cast to whole theorem capabilities, and records
--     explicit source-store lineage.
--   * Contains no recursive dispatcher, postulates, or permissive holes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (instᵈ)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym)

open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_
  ; _↦_
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ∀ⁱ_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  (bind; keep; ν-step; ↠-refl; ↠-step)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-left
  ; lift-left-ctx-[]
  ; rightStoreⁱ-lift-left
  ; store-left
  )
open import NuTerms using
  ( ok-no
  ; ok-•
  ; ok-⟨⟩
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( cast⊑⊑ᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
open import TermTyping using
  (CastMode; SealModeStore★; cast-inst)
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  ; `∀
  ; extᵗ
  ; renameᵗ
  ; ★
  ; ⇑ᵗ
  ; wf★
  )
open import proof.MaximalLowerBoundsWf using
  ( rename-assm²-source-νᵢ
  ; rename-assm²-⇑ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  )
open import proof.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-source-only-head)
open import proof.NuImprecisionRelStoreEmbeddingAlgebra using
  (lift-left-store-embeddingⁱ)
open import proof.NuImprecisionLeftLiftPrefixBodyDef using
  (LeftLiftPrefixBodyᵀ)
open import proof.NuImprecisionSimulationCore using
  ( equality-proof-unique
  ; renameᵗ-ext-id
  ; transport-all-⊑ᵢ
  ; transport-arrow-⊑ᵢ
  ; ⊑-source-under-rightᵢ
  )
open import proof.NuImprecisionSimulationResultDef using
  ( LeftSilentIndexedResult
  ; WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; left-silent-indexed
  ; left-silent-invariant
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.NuImprecisionSourceBulletBase using
  (left-allocated-bulletᵀ)
open import proof.NuImprecisionStoreLift using
  (lift-left-store-result)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (weak-step-store-lineage)
open import proof.NuImprecisionWorldCoherenceLemma using
  (world-coherent-left-allocation)
open import proof.NuImprecisionWorldCoherentCatchupComposition using
  (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import
  proof.NuImprecisionWorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupDef
  using (WorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupᵀ)
open import proof.NuImprecisionWorldCoherentSourceBulletCatchupDef using
  (WorldCoherentSourceBulletCatchupᵀ)
open import proof.NuImprecisionWorldCoherentSourceWidenCatchupDef using
  (WorldCoherentSourceWidenCatchupᵀ)
open import proof.NuStoreProperties using (StoreWf-bind)
open import proof.TypeProperties using
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


world-coherent-final-source-νcast-source-only-index-catchup-proofᵀ :
  LeftLiftPrefixBodyᵀ →
  WorldCoherentSourceBulletCatchupᵀ →
  WorldCoherentSourceWidenCatchupᵀ →
  WorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupᵀ
world-coherent-final-source-νcast-source-only-index-catchup-proofᵀ
    left-lift-prefix-body bullet-catchup widen-catchup
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {L = L} {V′ = V′}
    {B = B} {B′ = B′} {C = C} {s = s}
    {μ = μ} {p = p} {r = r} {occ = occ}
    coherent exclusive wfL mode seal★ s⊑
    vL noL vV′ noV′ L⊑V′
    with lift-left-store-result ρ
world-coherent-final-source-νcast-source-only-index-catchup-proofᵀ
    left-lift-prefix-body bullet-catchup widen-catchup
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {L = L} {V′ = V′}
    {B = B} {B′ = B′} {C = C} {s = s}
    {μ = μ} {p = p} {r = r} {occ = occ}
    coherent exclusive wfL mode seal★ s⊑
    vL noL vV′ noV′ L⊑V′
    | ρ′ , liftρ =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    allocation-silent allocation-lineage cast-catchup
  where
  allocated :
    StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ
  allocated = store-left zero ★ wf★ ∷ ρ′

  allocated-store-eq =
    cong ((zero , ★) ∷_) (leftStoreⁱ-lift-left liftρ)

  allocated-wf : StoreWf (suc Δᴸ) (leftStoreⁱ allocated)
  allocated-wf =
    subst (StoreWf (suc Δᴸ)) (sym allocated-store-eq)
      (StoreWf-bind wfL wf★)

  allocated-seal :
    SealModeStore★ (instᵈ μ) (leftStoreⁱ allocated)
  allocated-seal =
    subst (SealModeStore★ (instᵈ μ))
      (sym allocated-store-eq) seal★

  allocated-cast =
    subst
      (λ Σ → instᵈ μ ∣ suc Δᴸ ∣ Σ ⊢ s ∶ C ⊑ ⇑ᵗ B)
      (sym allocated-store-eq) s⊑

  allocated-bullet =
    left-allocated-bulletᵀ vL noL wf★ liftρ L⊑V′

  bullet-result =
    bullet-catchup wf★ prefix-reflⁱ
      (world-coherent-left-allocation liftρ coherent)
      (source-name-exclusive-source-only-head exclusive)
      allocated-wf (ok-• vL noL) vV′ noV′ vL noL
      liftρ lift-left-ctx-[] L⊑V′
      (nu-term-imprecision-source-typing allocated-bullet)
      (nu-term-imprecision-target-typing allocated-bullet)

  cast-catchup =
    widen-catchup prefix-reflⁱ (cast-inst mode)
      allocated-seal allocated-cast vV′ noV′ bullet-result
      (⊑-source-liftνᵢ p)

  allocation-result :
    WeakOneStepResult ρ (ν ★ L s) V′ B B′ keep
  allocation-result =
    record
      { sourceChanges = bind ★ ∷ []
      ; targetTailChanges = []
      ; sourceResult = ((⇑ᵗᵐ L) •) ⟨ s ⟩
      ; targetResult = V′
      ; resultCtx = (zero ˣ⊑★) ∷ ⇑ᴸᵢ _
      ; resultLeftCtx = suc _
      ; resultRightCtx = _
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
      ; resultType = ⊑-source-liftνᵢ p
      ; sourceCatchup = ↠-step (ν-step vL noL) ↠-refl
      ; targetTail = ↠-refl
      ; sourceStoreResult = allocated-store-eq
      ; targetStoreResult = rightStoreⁱ-lift-left liftρ
      ; relatedResults =
          cast⊑⊑ᵀ (cast-inst mode) allocated-seal
            allocated-cast allocated-bullet (⊑-source-liftνᵢ p)
      }

  allocation-indexed : WeakOneStepIndexedResult p
  allocation-indexed =
    weak-indexed-result allocation-result
      (cast⊑⊑ᵀ (cast-inst mode) allocated-seal
        allocated-cast allocated-bullet (⊑-source-liftνᵢ p))

  allocation-silent : LeftSilentIndexedResult p
  allocation-silent =
    left-silent-indexed allocation-indexed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-• vL noL))
      (weak-step-transport
        (left-lift-prefix-body liftρ
          (prefix-∷ⁱ prefix-reflⁱ)))
      (weak-step-type-coherence source-lift-arrowᵢ source-lift-allᵢ)

  allocation-lineage =
    weak-step-store-lineage ρ′
      (lift-left-store-embeddingⁱ liftρ)
      (prefix-∷ⁱ prefix-reflⁱ)
