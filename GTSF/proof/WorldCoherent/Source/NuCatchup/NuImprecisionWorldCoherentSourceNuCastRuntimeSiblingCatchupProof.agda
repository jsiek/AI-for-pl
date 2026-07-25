module
  proof.WorldCoherent.Source.NuCatchup.NuImprecisionWorldCoherentSourceNuCastRuntimeSiblingCatchupProof
  where

-- File Charter:
--   * Implements source-`ν ★` cast catch-up while carrying one independent
--     source-no-bullet, target-runtime sibling.
--   * Uses the transported `SourceNuIndex` equality to retain the source-only
--     body schedule and constructs its allocation directly.
--   * Composes the inner frame and fresh allocation through the exact
--     silent-resumption sibling join.
--   * Contains no opaque allocation recovery, postulate, hole, permissive
--     option, or outcome alias.

open import Agda.Builtin.Equality using (_≡_; refl)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Coercions using
  (Coercion; ModeEnv; instᵈ)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionComposition using
  (ImprecisionShape; _；_≋_; ⌊_⌋)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym)

open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _↦_
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ∀ⁱ_
  ; _∣_⊢_⊑_⊣_
  )
  renaming (ν to νⁱ)
open import NarrowWiden using
  (widen-weaken; _∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; blame-ν
  ; keep
  ; ν-step
  ; ↠-refl
  ; ↠-step
  )
open import NuStore using
  (StoreIncl-cons; StoreWf)
open import NuTermImprecision using
  ( CtxImpEntry
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
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
  ; no•-blame
  ; ok-no
  ; ok-•
  ; ok-ν
  ; ok-⟨⟩
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊑⊑ᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
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
  ; ⟰ᵗ
  ; occurs
  )
open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import
  proof.Catchup.Core.NuImprecisionCatchupSourceAllocationTerminal
  using (left-silent-indexed-prefix-source-νcast-terminal-valueᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( apply-widen-inst-under-ty-binders
  ; equality-proof-unique
  ; left-ctx-rename-[]
  ; nu-term-imprecision-transport-typesᵀ
  ; rename-left-store-coherentⁱ
  ; rename-left-store-source-liftⁱ
  ; rename-left-storeⁱ
  ; renameᵗ-ext-id
  ; transport-all-⊑ᵢ
  ; transport-arrow-⊑ᵢ
  ; weak-one-step-source-νcast-frame-preserves-transportᵀ
  ; weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
  ; weak-one-step-source-νcast-frameᵀ
  ; ⊑-source-lift-source-nuᵢ
  ; ⊑-source-under-rightᵢ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftSilentIndexedResult
  ; WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; canonicalIndexedResults
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; sourceTypeResult
  ; sourceNuBody
  ; sourceNuIndexEquality
  ; sourceNuSafe
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTailChanges
  ; targetTypeResult
  ; transportShapeCoherent
  ; transportSourceNu
  ; transportType
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Core.Properties.NuStoreProperties using
  (StoreWf-bind)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercionUnderTyBinders
  ; imprecision-composition-shape-transport
  ; ⊑-rename-leftᵢ
  )
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-No•)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercionUnderTyBinders
  ; applyTerms-preserves-No•
  ; applyTerms-preserves-RuntimeOK
  ; applyTys-∀
  ; applyTysUnderTyBinders
  )
open import proof.Core.Properties.StoreProperties using
  (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken; term-weaken)
open import proof.Core.Properties.TypeProperties using
  ( TyRenameWf-ext
  ; TyRenameWf-suc
  ; renameᵗ-id
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( rename-assm²-source-νᵢ
  ; rename-assm²-⇑ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  )
open import
  proof.Left.AllocationRuntime.NuImprecisionLeftSourceAllocationRuntimeTransportDef
  using (left-source-allocation-runtimeᵀ)
open import
  proof.Left.AllocationRuntime.NuImprecisionLeftSourceAllocationRuntimeTransportLemma
  using (left-source-allocation-runtime-transport)
open import proof.Left.Core.NuImprecisionLeftLiftPrefixBodyProof using
  (left-lift-prefix-body-proofᵀ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-source)
open import proof.NuCore.Misc.NuImprecisionAllocationSimulation using
  ( replace-left-source-liftν-source-nu-bodyᵢ
  ; replace-left-source-liftνᵢ
  ; replace-paired-source-liftν-under-∀ᵢ
  ; replace-paired-source-liftνᵢ
  ; replace-right-source-liftν-under-rightᵢ
  ; replace-right-source-liftνᵢ
  ; source-liftν-right-body-shapeᵢ
  )
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityProof
  using (source-name-exclusive-source-only-head)
open import proof.Source.Core.NuImprecisionSourceBulletBase using
  (left-allocated-bulletᵀ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  ( lift-left-store-embeddingⁱ
  ; rel-store-embedding-reflⁱ
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupRuntimeSiblingComposition
  using
  (world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  )
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentTypeShapeProof
  using (shape-source-liftνᵢ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma using
  (world-coherent-left-allocation)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastIndexBodyViewProof
  using (transport-source-nu-body-shape)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupRuntimeSiblingPrefixDef
  using (WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ)


private
  source-lift-under-∀ᵢ :
    ∀ {Φ Δᴸ Δᴿ A B} →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
    ((zero ˣ⊑ˣ zero) ∷
      ⇑ᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      ∣ suc (suc Δᴸ)
      ⊢ renameᵗ (extᵗ suc) A ⊑ B ⊣ suc Δᴿ
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


world-coherent-source-νcast-runtime-sibling-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {N V′ R R′ : Term} {B B′ C E E′ : Ty}
    {s : Coercion} {s-shape : ImprecisionShape}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {occ : occurs zero C ≡ true}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ} →
  {{safe : NonVar C}} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  widening ⊢ᶜ s ⦂ s-shape →
  s-shape ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ′ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
    ([] {A = CtxImpEntry
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
  Value V′ →
  No• V′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ⁺} (νⁱ safe occ q)) →
  (let result =
         weakIndexedResult
           (catchupIndexedResult (worldCatchupResult inner))
   in
   resultCtx result
     ∣ resultLeftCtx result
     ∣ resultRightCtx result
     ∣ resultStore result ∣ []
     ⊢ᴺ applyTerms (sourceChanges result) R
       ⊑ applyTerms (targetTailChanges result) (applyTerm keep R′)
     ⦂ applyTys (sourceChanges result) E
       ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
     ∶ transportType result r) →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = ν ★ N s} {V′ = V′} {ρ = ρ⁺} p ]
    let result =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ applyTerms (sourceChanges result) R
        ⊑ applyTerms (targetTailChanges result) (applyTerm keep R′)
      ⦂ applyTys (sourceChanges result) E
        ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
      ∶ transportType result r
world-coherent-source-νcast-runtime-sibling-catchup-proofᵀ
    value-sibling
    {R = R} {R′ = R′} {B = B} {B′ = B′}
    {C = C} {E = E} {E′ = E′}
    {s = s} {p = p} {r = r} {occ = occ} {q = q}
    {{safe = safe}}
    prefix mode seal★ c⊑ s-shape comp liftρ liftγ
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      inner-lineage coherent exclusive unique wfL)
    inner-sibling
    with final
world-coherent-source-νcast-runtime-sibling-catchup-proofᵀ
    value-sibling
    {R = R} {R′ = R′} {B = B} {B′ = B′}
    {C = C} {E = E} {E′ = E′}
    {s = s} {p = p} {r = r} {occ = occ} {q = q}
    {{safe = safe}}
    prefix mode seal★ c⊑ s-shape comp liftρ liftγ
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      inner-lineage coherent exclusive unique wfL)
    inner-sibling
    | inj₁ (vW , noW)
    with apply-widen-inst-under-ty-binders
      {χs = sourceChanges (weakIndexedResult indexed)}
      mode
      (seal★-weaken
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion prefix)))
        seal★)
      (widen-weaken ≤-refl
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion prefix)))
        c⊑)
world-coherent-source-νcast-runtime-sibling-catchup-proofᵀ
    value-sibling
    {R = R} {R′ = R′} {B = B} {B′ = B′}
    {C = C} {E = E} {E′ = E′}
    {s = s} {p = p} {r = r} {occ = occ} {q = q}
    {{safe = safe}}
    prefix mode seal★ c⊑ s-shape comp liftρ liftγ
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      inner-lineage coherent exclusive unique wfL)
    inner-sibling
    | inj₁ (vW , noW)
    | μ′ , mode′ , final-seal₀ , final-cast₀ =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
      allocation-silent allocation-lineage recursive)
  where
  inner = weakIndexedResult indexed

  final-index = transportSourceNu inner safe occ q

  final-safe = sourceNuSafe final-index

  body-index = sourceNuBody final-index

  body-shape-eq =
    transport-source-nu-body-shape
      inner (weakIndexedTypeCoherence indexed) safe occ q

  first-silent =
    left-silent-indexed-prefix-source-νcast-terminal-valueᵀ
      prefix mode seal★ c⊑ s-shape comp catchup vW noW

  first-lineage =
    weak-step-store-lineage
      (lineageStore inner-lineage)
      (lineageEmbedding inner-lineage)
      (lineagePrefix inner-lineage)

  final-seal =
    subst
      (λ Σ → SealModeStore★ (instᵈ μ′)
        ((zero , ★) ∷ ⟰ᵗ Σ))
      (sym (sourceStoreResult inner)) final-seal₀

  final-cast =
    subst
      (λ Δ → instᵈ μ′ ∣ suc Δ
        ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ (resultStore inner))
        ⊢ applyCoercionUnderTyBinders (sourceChanges inner) s
          ∶ applyTysUnderTyBinders (sourceChanges inner) C
            ⊑ ⇑ᵗ (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → instᵈ μ′
          ∣ suc (applyTyCtxs (sourceChanges inner) _)
          ∣ (zero , ★) ∷ ⟰ᵗ Σ
          ⊢ applyCoercionUnderTyBinders (sourceChanges inner) s
            ∶ applyTysUnderTyBinders (sourceChanges inner) C
              ⊑ ⇑ᵗ (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) final-cast₀)

  final-relation₀ =
    nu-term-imprecision-transport-typesᵀ
      (applyTys-∀ (sourceChanges inner) C) refl refl
      (canonicalIndexedResults indexed)

  final-relation =
    subst
      (λ index →
        resultCtx inner
          ∣ resultLeftCtx inner
          ∣ resultRightCtx inner
          ∣ resultStore inner ∣ []
          ⊢ᴺ sourceResult inner ⊑ targetResult inner
          ⦂ `∀ (applyTysUnderTyBinders (sourceChanges inner) C)
            ⊑ applyTys (targetTailChanges inner) B′
          ∶ index)
      (sourceNuIndexEquality final-index)
      final-relation₀

  final-shape =
    cast-shape-applyCoercionUnderTyBinders
      (sourceChanges inner) s-shape

  final-comp =
    imprecision-composition-shape-transport
      refl
      (transportShapeCoherent (weakIndexedTypeCoherence indexed) p)
      body-shape-eq comp

  final-store =
    rename-left-storeⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc (resultStore inner)

  final-lift =
    rename-left-store-source-liftⁱ (resultStore inner)

  final-store-rename =
    rename-left-store-coherentⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc (resultStore inner)

  allocated =
    store-left zero ★ wf★ ∷ final-store

  allocated-store-eq =
    cong ((zero , ★) ∷_) (leftStoreⁱ-lift-left final-lift)

  allocated-wf : StoreWf (suc (resultLeftCtx inner))
    (leftStoreⁱ allocated)
  allocated-wf =
    subst (StoreWf (suc (resultLeftCtx inner)))
      (sym allocated-store-eq)
      (StoreWf-bind wfL wf★)

  allocated-seal :
    SealModeStore★ (instᵈ μ′) (leftStoreⁱ allocated)
  allocated-seal =
    subst (SealModeStore★ (instᵈ μ′))
      (sym allocated-store-eq) final-seal

  allocated-cast =
    subst
      (λ Σ → instᵈ μ′ ∣ suc (resultLeftCtx inner) ∣ Σ
        ⊢ applyCoercionUnderTyBinders (sourceChanges inner) s
          ∶ applyTysUnderTyBinders (sourceChanges inner) C
            ⊑ ⇑ᵗ (applyTys (sourceChanges inner) B))
      (sym allocated-store-eq) final-cast

  allocated-bullet =
    left-allocated-bulletᵀ {{safe = final-safe}}
      vW noW wf★ final-lift final-relation

  allocated-comp =
    imprecision-composition-shape-transport
      refl
      (shape-source-liftνᵢ (transportType inner p))
      refl final-comp

  allocation-relation =
    cast⊑⊑ᵀ (cast-inst mode′) allocated-seal allocated-cast
      allocated-bullet (⊑-source-liftνᵢ (transportType inner p))
      final-shape allocated-comp

  allocation-result :
    WeakOneStepResult (resultStore inner)
      (ν ★ (sourceResult inner)
        (applyCoercionUnderTyBinders (sourceChanges inner) s))
      (targetResult inner)
      (applyTys (sourceChanges inner) B)
      (applyTys (targetTailChanges inner) B′)
      keep
  allocation-result =
    record
      { sourceChanges = bind ★ ∷ []
      ; targetTailChanges = []
      ; sourceResult =
          ((⇑ᵗᵐ (sourceResult inner)) •)
            ⟨ applyCoercionUnderTyBinders (sourceChanges inner) s ⟩
      ; targetResult = targetResult inner
      ; resultCtx =
          (zero ˣ⊑★) ∷ ⇑ᴸᵢ (resultCtx inner)
      ; resultLeftCtx = suc (resultLeftCtx inner)
      ; resultRightCtx = resultRightCtx inner
      ; sourceCtxResult = refl
      ; targetCtxResult = refl
      ; resultStore = allocated
      ; resultSourceType =
          ⇑ᵗ (applyTys (sourceChanges inner) B)
      ; resultTargetType =
          applyTys (targetTailChanges inner) B′
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = ⊑-source-liftνᵢ
      ; transportAllBody = source-lift-under-∀ᵢ
      ; transportRightBody = ⊑-source-under-rightᵢ
      ; transportSourceNu = ⊑-source-lift-source-nuᵢ
      ; resultType =
          ⊑-source-liftνᵢ (transportType inner p)
      ; sourceCatchup = ↠-step (ν-step vW noW) ↠-refl
      ; targetTail = ↠-refl
      ; sourceStoreResult = allocated-store-eq
      ; targetStoreResult = rightStoreⁱ-lift-left final-lift
      ; relatedResults = allocation-relation
      }

  allocation-indexed :
    WeakOneStepIndexedResult (transportType inner p)
  allocation-indexed =
    weak-indexed-result allocation-result allocation-relation
      (weak-step-transport
        (left-lift-prefix-body-proofᵀ final-lift
          (prefix-∷ⁱ prefix-reflⁱ)))
      (weak-step-type-coherence
        source-lift-arrowᵢ
        source-lift-allᵢ
        shape-source-liftνᵢ
        source-liftν-right-body-shapeᵢ
        replace-left-source-liftνᵢ
        replace-right-source-liftνᵢ
        replace-paired-source-liftνᵢ
        replace-paired-source-liftν-under-∀ᵢ
        replace-left-source-liftν-source-nu-bodyᵢ
        replace-right-source-liftν-under-rightᵢ)

  allocation-silent :
    LeftSilentIndexedResult (transportType inner p)
  allocation-silent =
    left-silent-indexed allocation-indexed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-• vW noW))

  allocation-lineage =
    weak-step-store-lineage final-store
      (lift-left-store-embeddingⁱ final-lift)
      (prefix-∷ⁱ prefix-reflⁱ)

  inner-noR =
    applyTerms-preserves-No• (sourceChanges inner) noR

  inner-okR′ =
    applyTerms-preserves-RuntimeOK
      (targetTailChanges inner) okR′

  allocation-sibling-index-eq =
    assumption-membership-unique→precision-index-unique
      (assumption-membership-unique-source unique)
      (⊑-rename-leftᵢ suc rename-assm²-source-νᵢ
        TyRenameWf-suc (transportType inner r))
      (⊑-source-liftνᵢ (transportType inner r))

  allocation-sibling-raw =
    left-source-allocation-runtimeᵀ
      left-source-allocation-runtime-transport
      final-store-rename left-ctx-rename-[]
      inner-noR inner-okR′ inner-sibling

  allocation-sibling-tail =
    nu-term-imprecision-transport-typesᵀ
      refl refl allocation-sibling-index-eq
      allocation-sibling-raw

  allocation-store-prefix = prefix-∷ⁱ prefix-reflⁱ

  allocation-sibling =
    allocation-prefixᵀ allocation-store-prefix
      allocation-sibling-tail
      (term-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion allocation-store-prefix)
        (renameᵗᵐ-preserves-No• suc inner-noR)
        (nu-term-imprecision-source-typing
          allocation-sibling-tail))
      (nu-term-imprecision-target-typing
        allocation-sibling-tail)

  recursive =
    value-sibling
      {Φ = (zero ˣ⊑★) ∷ ⇑ᴸᵢ (resultCtx inner)}
      {Δᴸ = suc (resultLeftCtx inner)}
      {Δᴿ = resultRightCtx inner}
      {ρᵇ = allocated} {ρ = allocated}
      {R = ⇑ᵗᵐ (applyTerms (sourceChanges inner) R)}
      {R′ = applyTerms (targetTailChanges inner)
        (applyTerm keep R′)}
      {C = ⇑ᵗ (applyTys (sourceChanges inner) E)}
      {C′ = applyTys (targetTailChanges inner)
        (applyTy keep E′)}
      {q = ⊑-source-liftνᵢ (transportType inner r)}
      prefix-reflⁱ
      (world-coherent-left-allocation final-lift coherent)
      (source-name-exclusive-source-only-head exclusive)
      (assumption-membership-unique-source unique)
      allocated-wf
      (ok-⟨⟩ (ok-• vW noW)) vV′ noV′
      allocation-relation
      (renameᵗᵐ-preserves-No• suc inner-noR)
      (applyTerms-preserves-RuntimeOK [] inner-okR′)
      allocation-sibling
      (nu-term-imprecision-source-typing allocation-sibling)
      (nu-term-imprecision-target-typing allocation-sibling)
world-coherent-source-νcast-runtime-sibling-catchup-proofᵀ
    value-sibling
    {R = R} {R′ = R′} {B = B} {B′ = B′}
    {C = C} {E = E} {E′ = E′}
    {s = s} {p = p} {r = r} {occ = occ} {q = q}
    {{safe = safe}}
    prefix mode seal★ c⊑ s-shape comp liftρ liftγ
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      inner-lineage coherent exclusive unique wfL)
    inner-sibling
    | inj₂ refl =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (second-caught , inner-sibling)
  where
  inner = weakIndexedResult indexed

  first-lineage =
    weak-step-store-lineage
      (lineageStore inner-lineage)
      (lineageEmbedding inner-lineage)
      (lineagePrefix inner-lineage)

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc
        (leftStoreⁱ-prefix-inclusion prefix))

  seal★⁺ = seal★-weaken source-store-incl seal★

  c⊑⁺ = widen-weaken ≤-refl source-store-incl c⊑

  framed =
    weak-one-step-source-νcast-frameᵀ
      mode seal★⁺ c⊑⁺ p s-shape comp indexed

  first-silent =
    left-silent-indexed
      (weak-indexed-result framed (relatedResults framed)
        (weak-one-step-source-νcast-frame-preserves-transportᵀ
          mode seal★⁺ c⊑⁺ p s-shape comp indexed
          (weakIndexedTransport indexed))
        (weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
          mode seal★⁺ c⊑⁺ p s-shape comp indexed
          (weakIndexedTypeCoherence indexed)))
      (left-silent-invariant refl refl)
      (ok-ν (ok-no no•-blame))

  target⊒ =
    nu-term-imprecision-target-typing (relatedResults framed)

  second-relation = blame⊑ᵀ target⊒

  second =
    weak-one-step-keep-source-catchupᵀ
      blame-ν second-relation

  second-caught =
    world-coherent-left-indexed-catchup
      (left-indexed-catchup
        (weak-indexed-result second (relatedResults second)
          (weak-one-step-keep-source-catchup-transportᵀ
            blame-ν second-relation)
          (weak-one-step-keep-source-catchup-type-coherenceᵀ
            blame-ν second-relation))
        (left-catchup-invariant
          (left-silent-invariant refl refl) (inj₂ refl)))
      (weak-step-store-lineage
        (resultStore framed)
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
