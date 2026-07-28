module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenRuntimeSiblingCatchupProof
  where

-- File Charter:
--   * Carries one independent runtime sibling through source widening.
--   * Treats inert, atomic identity, sequence, source-only instantiation, and
--     standalone unseal according to the widening grammar.
--   * Uses the exact silent-resumption sibling join at every active reduction.
--   * Shares one chosen store lift between source-instantiation allocation
--     and independent runtime-sibling transport.
--   * Contains no postulate, hole, or permissive option.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (_≡_; refl)
open import CastImprecisionShape using
  ( _⊢ᶜ_⦂_
  ; widening
  ; shape-inst
  ; shape-sequence-widening
  ; shape-unseal
  )
import Coercions as C
open import Coercions using
  (Coercion; Inert; ModeEnv; _︔_)
import Conversion as Conv
open import ConversionIndexCompatibility using
  (replace-left-seal)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; _；_≋_
  ; comp-ν
  ; comp-tagˣ-id★
  ; ⌊_⌋
  ; νˢ-injective
  )
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; _∣_⊢_⊑_⊣_
  ; ⇑ᴸᵢ
  ; id★
  ; tagˣ
  ; ν
  )
import NarrowWiden as NW
open import NarrowWiden using
  ( Widening
  ; _∣_∣_⊢_∶_⊑_
  ; widen-weaken
  )
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; blame-⟨⟩
  ; bind
  ; keep
  ; pure-step
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; store-left
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-blame
  ; no•-⟨⟩
  ; ok-no
  ; ok-•
  ; ok-ν
  ; ok-⟨⟩
  ; renameᵗᵐ
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊑⊑ᵀ
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using
  (cong; subst; subst₂; sym; trans)
open import Store using (StoreIncl-cons)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Atom; Ty; TyCtx; TyVar; occurs; ★; `∀; wf★; ⇑ᵗ)
import Types as T
open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import proof.OneStep.NuImprecisionWeakOneStepSourceCastFrame using
  ( weak-one-step-source-cast-frame-coherenceᵀ
  ; weak-one-step-source-cast-frame-silentᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frameᵀ
  )
open import proof.Source.Core.NuImprecisionSourcePolymorphicValueBase using
  (post-catchup-β-inst)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( left-ctx-rename-[]
  ; nu-term-imprecision-transport-typesᵀ
  ; rename-left-store-coherentⁱ
  ; rename-left-store-source-liftⁱ
  ; rename-left-storeⁱ
  ; weak-one-step-reindexᵀ
  ; weak-result-source-widen-inst
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( canonicalIndexedResults
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
  ; sourceNuIndexEquality
  ; sourceNuSafe
  ; sourceResult
  ; sourceStoreResult
  ; targetResult
  ; targetTailChanges
  ; transportShapeCoherent
  ; transportType
  ; transportSourceNu
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercionUnderTyBinders
  ; cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  ; shape-source-liftνᵢ
  ; shape-subst-source
  ; ⊑-rename-leftᵢ
  )
open import proof.Core.Properties.NuStoreProperties using (StoreWf-bind)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-No•)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-preserves-Inert
  ; applyTerms-preserves-No•
  ; applyTerms-preserves-RuntimeOK
  ; applyTys-∀
  )
open import proof.Core.Properties.StoreProperties using
  (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using
  (seal★-inst; seal★-weaken; term-weaken)
open import proof.Core.Properties.TypeProperties using (TyRenameWf-suc)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( rename-assm²-source-νᵢ
  ; ⊑-source-liftνᵢ
  )
open import
  proof.Left.AllocationRuntime.NuImprecisionLeftSourceAllocationRuntimeTransportDef
  using (left-source-allocation-runtimeᵀ)
open import
  proof.Left.AllocationRuntime.NuImprecisionLeftSourceAllocationRuntimeTransportLemma
  using (left-source-allocation-runtime-transport)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.Source.CastSequence.NuImprecisionSourceCastSequenceMidpointDef
  using (widening-midpoint)
open import
  proof.Source.CastSequence.NuImprecisionSourceCastSequenceMidpointLemma
  using (source-cast-sequence-midpointᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.Prefix.NuImprecisionStorePrefix
  using (leftStoreⁱ-prefix-inclusion)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupRuntimeSiblingComposition
  using
  ( world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
  ; world-coherent-left-catchup-prepend-keep-step-runtime-sibling
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  )
open import
  proof.WorldCoherent.Source.Allocation.NuImprecisionWorldCoherentSourceAllocationStepProof
  using (world-coherent-source-inst-allocation-step-with-liftᵀ)
open import
  proof.Source.Allocation.NuImprecisionSourceNuAllocationRelationLemma
  using (source-inst-allocation-relationᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef
  using
  ( sourceStepAssumptionMembershipUnique
  ; sourceStepIndexedResult
  ; sourceStepSourceNameExclusive
  ; sourceStepStoreLineage
  ; sourceStepWorldCoherent
  )
open import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupTransportCore
  using
  ( applyCoercions-preserves-Widening
  ; applyCoercions-seq
  ; indexed-source-precision
  ; post-catchup-β-seq
  ; result-widening-typingᵀ
  ; result-widening-typing₂ᵀ
  ; transport-source-widening-composition
  )
open import proof.Core.Properties.NuStoreChangeIdentityProperties using
  (applyTys-preserves-Atom; post-catchup-β-id)
open import proof.OneStep.NuImprecisionAtomicSourceReindex using
  (atomic-source-value-reindexᵀ)
open import
  proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceRevealRuntimeSiblingCatchupProof
  using (world-coherent-source-reveal-runtime-sibling-catchup-proofᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupRuntimeSiblingPrefixDef
  using (WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ)


world-coherent-source-inert-widen-runtime-sibling-catchupᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ R R′ : Term} {A B B′ E E′ : Ty}
    {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {s : ImprecisionShape} →
  Inert c →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  Value V′ →
  No• V′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ⁺} p) →
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
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q ]
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
world-coherent-source-inert-widen-runtime-sibling-catchupᵀ
    inert prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    with result-widening-typingᵀ prefix mode seal★ c⊑ indexed
world-coherent-source-inert-widen-runtime-sibling-catchupᵀ
    inert prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    with final
world-coherent-source-inert-widen-runtime-sibling-catchupᵀ
    inert prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₁ (vW , noW) =
  caught , inner-sibling
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  inert′ =
    applyCoercions-preserves-Inert (sourceChanges inner) inert

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  caught =
    world-coherent-left-indexed-catchup
      (left-indexed-catchup framed
        (left-catchup-invariant first-silent
          (inj₁ (vW ⟨ inert′ ⟩ , no•-⟨⟩ noW))))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL
world-coherent-source-inert-widen-runtime-sibling-catchupᵀ
    inert prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₂ refl =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (second-caught , inner-sibling)
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-no no•-blame))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-first =
    weak-one-step-reindexᵀ first refl refl
      (canonicalIndexedResults framed)

  terminal-target⊢ =
    nu-term-imprecision-target-typing
      (relatedResults terminal-first)

  terminal-second-relation = blame⊑ᵀ terminal-target⊢

  terminal-second = weak-one-step-keep-source-catchupᵀ
    {p = resultType terminal-first}
    (pure-step blame-⟨⟩) terminal-second-relation

  terminal-second-indexed =
    weak-indexed-result
      terminal-second terminal-second-relation
      (weak-one-step-keep-source-catchup-transportᵀ
        (pure-step blame-⟨⟩) terminal-second-relation)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (pure-step blame-⟨⟩) terminal-second-relation)

  terminal-second-catchup =
    left-indexed-catchup terminal-second-indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl)
        (inj₂ refl))

  second-caught =
    world-coherent-left-indexed-catchup
      terminal-second-catchup
      (weak-step-store-lineage
        (resultStore terminal-first)
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL


world-coherent-source-id-widen-runtime-sibling-catchupᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ R R′ : Term} {A B′ E E′ : Ty}
    {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {s : ImprecisionShape} →
  Atom A →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ C.id A ∶ A ⊑ A →
  Value V′ →
  No• V′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ⁺} p) →
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
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ C.id A ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = N ⟨ C.id A ⟩} {V′ = V′} {ρ = ρ⁺} q ]
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
world-coherent-source-id-widen-runtime-sibling-catchupᵀ
    atom prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    with result-widening-typingᵀ prefix mode seal★ c⊑ indexed
world-coherent-source-id-widen-runtime-sibling-catchupᵀ
    atom prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    with final
world-coherent-source-id-widen-runtime-sibling-catchupᵀ
    atom prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₁ (vW , noW) =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (second-caught , inner-sibling)
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (weak-one-step-source-cast-frame-silentᵀ
        inner final-relation silent)
      (ok-⟨⟩ (ok-no noW))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  source-atom =
    applyTys-preserves-Atom (sourceChanges inner) atom

  second-relation =
    atomic-source-value-reindexᵀ source-atom vW
      (canonicalIndexedResults indexed) (transportType inner q)

  second = weak-one-step-keep-source-catchupᵀ
    (post-catchup-β-id (sourceChanges inner) vW)
    second-relation

  second-indexed =
    weak-indexed-result
      second second-relation
      (weak-one-step-keep-source-catchup-transportᵀ
        (post-catchup-β-id (sourceChanges inner) vW)
        second-relation)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (post-catchup-β-id (sourceChanges inner) vW)
        second-relation)

  second-catchup =
    left-indexed-catchup second-indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl)
        (inj₁ (vW , noW)))

  second-caught =
    world-coherent-left-indexed-catchup
      second-catchup
      (weak-step-store-lineage
        (resultStore first)
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL
world-coherent-source-id-widen-runtime-sibling-catchupᵀ
    atom prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₂ refl =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (second-caught , inner-sibling)
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-no no•-blame))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-first =
    weak-one-step-reindexᵀ first refl refl
      (canonicalIndexedResults framed)

  terminal-target⊢ =
    nu-term-imprecision-target-typing
      (relatedResults terminal-first)

  terminal-second-relation = blame⊑ᵀ terminal-target⊢

  terminal-second = weak-one-step-keep-source-catchupᵀ
    {p = resultType terminal-first}
    (pure-step blame-⟨⟩) terminal-second-relation

  terminal-second-indexed =
    weak-indexed-result
      terminal-second terminal-second-relation
      (weak-one-step-keep-source-catchup-transportᵀ
        (pure-step blame-⟨⟩) terminal-second-relation)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (pure-step blame-⟨⟩) terminal-second-relation)

  terminal-second-catchup =
    left-indexed-catchup terminal-second-indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl)
        (inj₂ refl))

  second-caught =
    world-coherent-left-indexed-catchup
      terminal-second-catchup
      (weak-step-store-lineage
        (resultStore terminal-first)
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL


world-coherent-source-seq-widen-runtime-sibling-catchupᵀ :
  WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ R R′ : Term} {A C B B′ E E′ : Ty}
    {s t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {sequence-shape : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ s ∶ A ⊑ C →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ t ∶ C ⊑ B →
  Widening (s ︔ t) →
  Value V′ →
  No• V′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ⁺} p) →
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
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ s ︔ t ⦂ sequence-shape →
  sequence-shape ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = N ⟨ s ︔ t ⟩} {V′ = V′} {ρ = ρ⁺} q ]
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
world-coherent-source-seq-widen-runtime-sibling-catchupᵀ
    value-sibling
    {R = R} {R′ = R′} {E = E} {E′ = E′} {r = r}
    prefix mode seal★ s⊑ t⊑ seqʷ
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q
    sequence-shape-proof@(
      shape-sequence-widening
        {c = s} {d = t} s-shape t-shape sequence-comp)
    outer-comp
    with result-widening-typingᵀ prefix mode seal★
      (C.cast-seq (proj₁ s⊑) (proj₁ t⊑) , seqʷ) indexed
       | result-widening-typing₂ᵀ
           prefix mode seal★ s⊑ t⊑ indexed
world-coherent-source-seq-widen-runtime-sibling-catchupᵀ
    value-sibling
    {R = R} {R′ = R′} {E = E} {E′ = E′} {r = r}
    prefix mode seal★ s⊑ t⊑ seqʷ
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q
    sequence-shape-proof@(
      shape-sequence-widening
        {c = s} {d = t} s-shape t-shape sequence-comp)
    outer-comp
    | μc , modec , final-seal-c , final-cast-c
    | μst , modest , final-seal-st , final-cast-s , final-cast-t
    with final
world-coherent-source-seq-widen-runtime-sibling-catchupᵀ
    value-sibling
    {R = R} {R′ = R′} {E = E} {E′ = E′} {r = r}
    prefix mode seal★ s⊑ t⊑ seqʷ
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q
    sequence-shape-proof@(
      shape-sequence-widening
        {c = s} {d = t} s-shape t-shape sequence-comp)
    outer-comp
    | μc , modec , final-seal-c , final-cast-c
    | μst , modest , final-seal-st , final-cast-s , final-cast-t
    | inj₁ (vW , noW) =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage beta-composed
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ modec final-seal-c final-cast-c
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions
        (sourceChanges inner) sequence-shape-proof)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) outer-comp)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (weak-one-step-source-cast-frame-silentᵀ
        inner final-relation silent)
      (ok-⟨⟩ (ok-no noW))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  source-p = indexed-source-precision indexed

  source-q = transportType inner q

  seqʷ′ =
    subst Widening (applyCoercions-seq (sourceChanges inner) s t)
      (applyCoercions-preserves-Widening
        (sourceChanges inner) seqʷ)

  midpoint-result =
    widening-midpoint source-cast-sequence-midpointᵀ
      prefix-reflⁱ coherent exclusive wfL
      modest final-seal-st (proj₁ final-cast-s)
      (proj₁ final-cast-t) seqʷ′ source-p source-q
      (cast-shape-applyCoercions
        (sourceChanges inner) s-shape)
      (cast-shape-applyCoercions
        (sourceChanges inner) t-shape)
      sequence-comp
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) outer-comp)

  source-mid = proj₁ midpoint-result

  s-triangle = proj₁ (proj₂ midpoint-result)

  t-triangle = proj₂ (proj₂ midpoint-result)

  s-relation =
    cast⊑⊑ᵀ modest final-seal-st final-cast-s
      (canonicalIndexedResults indexed) source-mid
      (cast-shape-applyCoercions
        (sourceChanges inner) s-shape)
      s-triangle

  second-relation =
    cast⊑⊑ᵀ modest final-seal-st final-cast-t
      s-relation source-q
      (cast-shape-applyCoercions
        (sourceChanges inner) t-shape)
      t-triangle

  second = weak-one-step-keep-source-catchupᵀ
    (post-catchup-β-seq (sourceChanges inner) vW)
    second-relation

  second-indexed =
    weak-indexed-result
      second second-relation
      (weak-one-step-keep-source-catchup-transportᵀ
        (post-catchup-β-seq (sourceChanges inner) vW)
        second-relation)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (post-catchup-β-seq (sourceChanges inner) vW)
        second-relation)

  runtime =
    ok-⟨⟩ (ok-⟨⟩ (ok-no noW))

  second-silent =
    left-silent-indexed second-indexed
      (left-silent-invariant refl refl) runtime

  second-lineage =
    weak-step-store-lineage
      (resultStore first)
      rel-store-embedding-reflⁱ prefix-reflⁱ

  recursive =
    value-sibling
      {Φ = resultCtx first}
      {Δᴸ = resultLeftCtx first}
      {Δᴿ = resultRightCtx first}
      {ρᵇ = resultStore first}
      {ρ = resultStore first}
      {R = applyTerms (sourceChanges first) R}
      {R′ = applyTerms (targetTailChanges first)
        (applyTerm keep R′)}
      {C = applyTys (sourceChanges first) E}
      {C′ = applyTys (targetTailChanges first)
        (applyTy keep E′)}
      {q = transportType first r}
      prefix-reflⁱ coherent exclusive unique wfL
      runtime vV′ noV′
      (canonicalIndexedResults second-indexed)
      (applyTerms-preserves-No• (sourceChanges first) noR)
      (applyTerms-preserves-RuntimeOK
        (targetTailChanges first) okR′)
      inner-sibling
      (nu-term-imprecision-source-typing inner-sibling)
      (nu-term-imprecision-target-typing inner-sibling)

  beta-composed =
    world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
      second-silent second-lineage recursive
world-coherent-source-seq-widen-runtime-sibling-catchupᵀ
    value-sibling
    prefix mode seal★ s⊑ t⊑ seqʷ
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q
    sequence-shape-proof@(
      shape-sequence-widening s-shape t-shape sequence-comp)
    outer-comp
    | μc , modec , final-seal-c , final-cast-c
    | μst , modest , final-seal-st , final-cast-s , final-cast-t
    | inj₂ refl =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (second-caught , inner-sibling)
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ modec final-seal-c final-cast-c
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions
        (sourceChanges inner) sequence-shape-proof)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) outer-comp)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-no no•-blame))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-first =
    weak-one-step-reindexᵀ first refl refl
      (canonicalIndexedResults framed)

  terminal-target⊢ =
    nu-term-imprecision-target-typing
      (relatedResults terminal-first)

  terminal-second-relation = blame⊑ᵀ terminal-target⊢

  terminal-second = weak-one-step-keep-source-catchupᵀ
    {p = resultType terminal-first}
    (pure-step blame-⟨⟩) terminal-second-relation

  terminal-second-indexed =
    weak-indexed-result
      terminal-second terminal-second-relation
      (weak-one-step-keep-source-catchup-transportᵀ
        (pure-step blame-⟨⟩) terminal-second-relation)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (pure-step blame-⟨⟩) terminal-second-relation)

  terminal-second-catchup =
    left-indexed-catchup terminal-second-indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl)
        (inj₂ refl))

  second-caught =
    world-coherent-left-indexed-catchup
      terminal-second-catchup
      (weak-step-store-lineage
        (resultStore terminal-first)
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL


world-coherent-source-inst-widen-runtime-sibling-catchupᵀ :
  WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ R R′ : Term} {A B B′ E E′ : Ty}
    {c : Coercion} {μ : ModeEnv}
    {index-occ : occurs zero A ≡ true}
    {source-index : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {sibling-index : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {s : ImprecisionShape} →
  {{safe : NonVar A}} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ C.inst B c ∶ `∀ A ⊑ B →
  Value V′ →
  No• V′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ⁺}
      (ν safe index-occ source-index)) →
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
     ∶ transportType result sibling-index) →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ C.inst B c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ ν safe index-occ source-index ⌋ →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = N ⟨ C.inst B c ⟩} {V′ = V′} {ρ = ρ⁺} q ]
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
      ∶ transportType result sibling-index
world-coherent-source-inst-widen-runtime-sibling-catchupᵀ
    value-sibling
    {R = R} {R′ = R′} {E = E} {E′ = E′}
    {index-occ = index-occ} {source-index = source-index}
    {sibling-index = sibling-index}
    {{safe = safe}}
    prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    with result-widening-typingᵀ prefix mode seal★ c⊑ indexed
world-coherent-source-inst-widen-runtime-sibling-catchupᵀ
    value-sibling
    {R = R} {R′ = R′} {E = E} {E′ = E′}
    {index-occ = index-occ} {source-index = source-index}
    {sibling-index = sibling-index}
    {{safe = safe}}
    prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    with final
world-coherent-source-inst-widen-runtime-sibling-catchupᵀ
    value-sibling
    {R = R} {R′ = R′} {E = E} {E′ = E′}
    {index-occ = index-occ} {source-index = source-index}
    {sibling-index = sibling-index}
    {{safe = safe}}
    prefix mode seal★
    c⊑@(C.cast-inst hB occ s⊢ , NW.inst sʷ)
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q
    c-shape@(shape-inst inner-shape)
    comp@(comp-ν inner-comp)
    | μ′ , mode′ , final-seal , final-cast
    | inj₁ (vW , noW) =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage beta-composed
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (weak-one-step-source-cast-frame-silentᵀ
        inner final-relation silent)
      (ok-⟨⟩ (ok-no noW))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  transported-index =
    transportSourceNu inner safe index-occ source-index

  normalized =
    nu-term-imprecision-transport-typesᵀ
      (applyTys-∀ (sourceChanges inner) _) refl refl
      (canonicalIndexedResults indexed)

  shaped =
    nu-term-imprecision-transport-typesᵀ
      refl refl (sourceNuIndexEquality transported-index) normalized

  transported-source-shape =
    νˢ-injective
      (trans
        (sym
          (cong ⌊_⌋ (sourceNuIndexEquality transported-index)))
        (trans
          (shape-subst-source
            (applyTys-∀ (sourceChanges inner) _)
            (transportType inner
              (ν safe index-occ source-index)))
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed)
            (ν safe index-occ source-index))))

  transported-comp =
    imprecision-composition-shape-transport
      refl
      (trans
        (shape-source-liftνᵢ (transportType inner q))
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) q))
      transported-source-shape
      inner-comp

  allocation-typing =
    weak-result-source-widen-inst inner mode
      (seal★-inst
        (seal★-weaken
          (leftStoreⁱ-prefix-inclusion prefix) seal★))
      (widen-weaken ≤-refl
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion prefix)))
        (s⊢ , NW.instSafe→widening sʷ))

  final-store =
    rename-left-storeⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc (resultStore inner)

  final-lift =
    rename-left-store-source-liftⁱ (resultStore inner)

  final-store-rename =
    rename-left-store-coherentⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc (resultStore inner)

  allocation-step =
    world-coherent-source-inst-allocation-step-with-liftᵀ
      source-inst-allocation-relationᵀ
      {{sourceNuSafe transported-index}}
      coherent exclusive unique final-lift vW noW
      (proj₁ (proj₂ allocation-typing))
      (proj₁ (proj₂ (proj₂ allocation-typing)))
      (proj₂ (proj₂ (proj₂ allocation-typing)))
      (transportType inner q)
      (cast-shape-applyCoercionUnderTyBinders
        (sourceChanges inner) inner-shape)
      transported-comp shaped

  allocation-indexed = sourceStepIndexedResult allocation-step

  allocation-result = weakIndexedResult allocation-indexed

  allocation-silent =
    left-silent-indexed allocation-indexed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-• vW noW))

  allocation-wf =
    subst₂ StoreWf
      (sym (sourceCtxResult allocation-result))
      (sym (sourceStoreResult allocation-result))
      (StoreWf-bind wfL wf★)

  inner-noR =
    applyTerms-preserves-No• (sourceChanges inner) noR

  inner-okR′ =
    applyTerms-preserves-RuntimeOK
      (targetTailChanges inner) okR′

  allocation-sibling-index-eq =
    assumption-membership-unique→precision-index-unique
      (sourceStepAssumptionMembershipUnique allocation-step)
      (⊑-rename-leftᵢ suc rename-assm²-source-νᵢ
        TyRenameWf-suc (transportType inner sibling-index))
      (transportType allocation-result
        (transportType inner sibling-index))

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
    allocation-prefixᵀ
      allocation-store-prefix allocation-sibling-tail
      (term-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion allocation-store-prefix)
        (renameᵗᵐ-preserves-No• suc inner-noR)
        (nu-term-imprecision-source-typing
          allocation-sibling-tail))
      (nu-term-imprecision-target-typing allocation-sibling-tail)

  recursive =
    value-sibling
      {Φ = resultCtx allocation-result}
      {Δᴸ = resultLeftCtx allocation-result}
      {Δᴿ = resultRightCtx allocation-result}
      {ρᵇ = resultStore allocation-result}
      {ρ = resultStore allocation-result}
      {R = renameᵗᵐ suc
        (applyTerms (sourceChanges inner) R)}
      {R′ = applyTerms (targetTailChanges inner)
        (applyTerm keep R′)}
      {C = ⇑ᵗ (applyTys (sourceChanges inner) E)}
      {C′ = applyTys (targetTailChanges inner)
        (applyTy keep E′)}
      {q = transportType allocation-result
        (transportType inner sibling-index)}
      prefix-reflⁱ
      (sourceStepWorldCoherent allocation-step)
      (sourceStepSourceNameExclusive allocation-step)
      (sourceStepAssumptionMembershipUnique allocation-step)
      allocation-wf
      (ok-⟨⟩ (ok-• vW noW)) vV′ noV′
      (canonicalIndexedResults allocation-indexed)
      (renameᵗᵐ-preserves-No• suc inner-noR)
      inner-okR′
      allocation-sibling
      (nu-term-imprecision-source-typing allocation-sibling)
      (nu-term-imprecision-target-typing allocation-sibling)

  allocation-composed =
    world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
      allocation-silent
      (sourceStepStoreLineage allocation-step)
      recursive

  beta-composed =
    world-coherent-left-catchup-prepend-keep-step-runtime-sibling
      (post-catchup-β-inst (sourceChanges inner) vW)
      allocation-composed
world-coherent-source-inst-widen-runtime-sibling-catchupᵀ
    value-sibling
    prefix mode seal★ c⊑
    vV′ noV′ noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    inner-sibling q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₂ refl =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (second-caught , inner-sibling)
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first-raw = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first-raw (relatedResults first-raw)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first = weakIndexedResult framed

  first-silent =
    left-silent-indexed framed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-no no•-blame))

  first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-first =
    weak-one-step-reindexᵀ first refl refl
      (canonicalIndexedResults framed)

  terminal-target⊢ =
    nu-term-imprecision-target-typing
      (relatedResults terminal-first)

  terminal-second-relation = blame⊑ᵀ terminal-target⊢

  terminal-second = weak-one-step-keep-source-catchupᵀ
    {p = resultType terminal-first}
    (pure-step blame-⟨⟩) terminal-second-relation

  terminal-second-indexed =
    weak-indexed-result
      terminal-second terminal-second-relation
      (weak-one-step-keep-source-catchup-transportᵀ
        (pure-step blame-⟨⟩) terminal-second-relation)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (pure-step blame-⟨⟩) terminal-second-relation)

  terminal-second-catchup =
    left-indexed-catchup terminal-second-indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl)
        (inj₂ refl))

  second-caught =
    world-coherent-left-indexed-catchup
      terminal-second-catchup
      (weak-step-store-lineage
        (resultStore terminal-first)
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL


world-coherent-source-widen-runtime-sibling-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ R R′ : Term} {A B B′ E E′ : Ty}
    {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
    {s : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  Value V′ →
  No• V′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ⁺} p) →
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
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q ]
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
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling prefix mode seal★
    (C.cast-id hA ok , NW.cross (NW.id-＇ α)) =
  world-coherent-source-id-widen-runtime-sibling-catchupᵀ
    (T.＇ α) prefix mode seal★
    (C.cast-id hA ok , NW.cross (NW.id-＇ α))
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling prefix mode seal★
    (C.cast-id hA ok , NW.cross (NW.id-‵ ι)) =
  world-coherent-source-id-widen-runtime-sibling-catchupᵀ
    (T.‵ ι) prefix mode seal★
    (C.cast-id hA ok , NW.cross (NW.id-‵ ι))
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling prefix mode seal★
    (C.cast-fun {s = s} {t = t} s⊢ t⊢ ,
      NW.cross (sⁿ NW.↦ tʷ)) =
  world-coherent-source-inert-widen-runtime-sibling-catchupᵀ
    (s C.↦ t) prefix mode seal★
    (C.cast-fun s⊢ t⊢ , NW.cross (sⁿ NW.↦ tʷ))
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling prefix mode seal★
    (C.cast-all {s = s} s⊢ , NW.cross (NW.`∀ sʷ)) =
  world-coherent-source-inert-widen-runtime-sibling-catchupᵀ
    (C.`∀ s) prefix mode seal★
    (C.cast-all s⊢ , NW.cross (NW.`∀ sʷ))
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling prefix mode seal★
    (C.cast-id hA ok , NW.id★) =
  world-coherent-source-id-widen-runtime-sibling-catchupᵀ
    T.★ prefix mode seal★ (C.cast-id hA ok , NW.id★)
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling {p = ν safe index-occ source-index}
    prefix mode seal★
    c⊑@(C.cast-inst hB occ s⊢ , NW.inst sʷ)
    vV′ noV′ noR okR′ inner inner-sibling q
    c-shape@(shape-inst inner-shape)
    comp@(comp-ν inner-comp) =
  world-coherent-source-inst-widen-runtime-sibling-catchupᵀ
    value-sibling {{safe}} prefix mode seal★ c⊑
    vV′ noV′ noR okR′ inner inner-sibling q c-shape comp
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling prefix mode seal★
    (C.cast-tag {G = G} hG gG ok , NW.tag gG′) =
  world-coherent-source-inert-widen-runtime-sibling-catchupᵀ
    (G C.!) prefix mode seal★
    (C.cast-tag hG gG ok , NW.tag gG′)
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling prefix mode seal★
    (C.cast-seq s⊢ t⊢ , sˢ NW.︔ gG !) =
  world-coherent-source-seq-widen-runtime-sibling-catchupᵀ
    value-sibling prefix mode seal★
    (s⊢ , NW.cross (NW.strictCrossʷ→cross sˢ))
    (t⊢ , NW.tag gG)
    (sˢ NW.︔ gG !)
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling prefix mode seal★
    (C.cast-seq s⊢ t⊢ , NW.inst-fun-tag safe) =
  world-coherent-source-seq-widen-runtime-sibling-catchupᵀ
    value-sibling prefix mode seal★
    (s⊢ , NW.inst safe)
    (t⊢ , NW.tag T.★⇒★)
    (NW.inst-fun-tag safe)
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling {p = tagˣ x∈ α<Δ}
    prefix mode seal★
    (C.cast-unseal {μ = μ} hA α∈Σ ok , NW.unsealʷ α A)
    vV′ noV′ noR okR′ inner inner-sibling id★
    shape-unseal comp-tagˣ-id★ =
  world-coherent-source-reveal-runtime-sibling-catchup-proofᵀ
    prefix (Conv.reveal-unseal {μ = μ} hA α∈Σ ok)
    vV′ noV′ noR okR′ inner inner-sibling id★
    (replace-left-seal id★)
world-coherent-source-widen-runtime-sibling-catchup-proofᵀ
    value-sibling prefix mode seal★
    (C.cast-seq
      s⊢@(C.cast-unseal {A = A} hA α∈Σ ok) t⊢ ,
      NW.unseal︔_ α sˢ) =
  world-coherent-source-seq-widen-runtime-sibling-catchupᵀ
    value-sibling prefix mode seal★
    (s⊢ , NW.unsealʷ α A)
    (t⊢ , NW.strictʷ→widen sˢ)
    (NW.unseal︔_ α sˢ)
