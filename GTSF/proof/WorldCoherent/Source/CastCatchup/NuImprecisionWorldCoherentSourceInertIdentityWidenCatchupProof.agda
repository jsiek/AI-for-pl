module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceInertIdentityWidenCatchupProof
  where

-- File Charter:
--   * Proves the inert and atomic-identity source-widen catch-up cases.
--   * Uses the shared transported widening-typing and composition support.
--   * Contains no arbitrary-index source-instantiation case, dispatcher,
--     postulate, hole, or termination bypass.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping using
  (nu-term-imprecision-target-typing)
open import Agda.Builtin.Equality using (refl)
import Coercions as C
open import Coercions using (Inert)
open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( blame-⟨⟩
  ; pure-step
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; blame⊑ᵀ
  ; cast⊑⊑ᵀ
  ; prefix-reflⁱ
  )
open import Relation.Binary.PropositionalEquality using (sym)
import Relation.Binary.HeterogeneousEquality as HE
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Atom
  ; Ty
  ; TyCtx
  )
open import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupTransportCore
  using
  ( result-widening-typingᵀ
  ; transport-source-widening-composition
  )
open import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupDef
  using
  ( WorldCoherentSourceIdentityWidenCatchupᵀ
  ; WorldCoherentSourceInertWidenCatchupᵀ
  )
open import
  proof.Catchup.Core.NuImprecisionCatchupComposition
  using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import
  proof.Catchup.Core.NuImprecisionCatchupSourceCastTerminal
  using (left-catchup-indexed-source-cast-blame-frameᵀ)
open import
  proof.OneStep.NuImprecisionWeakOneStepSourceCastFrame
  using
  ( weak-one-step-source-cast-frame-coherenceᵀ
  ; weak-one-step-source-cast-frame-silentᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frameᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using
  ( subst²-to-≅
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
  ; weak-one-step-prepend-left-silent-preserves-transportᵀ
  ; weak-one-step-prepend-left-silentᵀ
  ; weak-one-step-reindexᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( canonicalIndexedResults
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; resultType
  ; sourceChanges
  ; sourceTypeResult
  ; targetTypeResult
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof
  using (weak-one-step-prepend-left-silent-store-lineageᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; world-coherent-left-indexed-catchup
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.Core.Properties.NuStoreChangeIdentityProperties
  using
  ( applyTys-preserves-Atom
  ; post-catchup-β-id
  )
open import proof.OneStep.NuImprecisionAtomicSourceReindex using
  (atomic-source-value-reindexᵀ)
open import
  proof.Core.Properties.ReductionProperties
  using (applyCoercions-preserves-Inert)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using (cast-shape-applyCoercions)


world-coherent-source-inert-widen-castᵀ :
  WorldCoherentSourceInertWidenCatchupᵀ
world-coherent-source-inert-widen-castᵀ
    {N = N} {V′ = V′} {c = c}
    inert prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    with result-widening-typingᵀ prefix mode seal★ c⊑ indexed
world-coherent-source-inert-widen-castᵀ
    {N = N} {V′ = V′} {c = c}
    inert prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    with final
world-coherent-source-inert-widen-castᵀ
    {N = N} {V′ = V′} {c = c}
    inert prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₁ (vW , noW) =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup framed
      (left-catchup-invariant first-silent
        (inj₁ (vW ⟨ inert′ ⟩ , no•-⟨⟩ noW))))
    (weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix)
    coherent exclusive unique wfL
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
world-coherent-source-inert-widen-castᵀ
    {N = N} {V′ = V′} {c = c}
    inert prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-source-cast-blame-frameᵀ
      catchup framed refl first-silent
      first-transport first-coherence refl)
    terminal-combined-lineage
    coherent exclusive unique wfL
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

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

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

  terminal-first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-second-lineage =
    weak-step-store-lineage
      (resultStore terminal-first)
      rel-store-embedding-reflⁱ prefix-reflⁱ

  terminal-combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent terminal-first
        (left-silent-invariant refl refl))
      terminal-second
      terminal-first-lineage terminal-second-lineage


world-coherent-source-id-widen-castᵀ :
  WorldCoherentSourceIdentityWidenCatchupᵀ
world-coherent-source-id-widen-castᵀ atom prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    with result-widening-typingᵀ prefix mode seal★ c⊑ indexed
world-coherent-source-id-widen-castᵀ atom prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    with final
world-coherent-source-id-widen-castᵀ atom prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₁ (vW , noW) =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup
      (weak-one-step-index-resultᵀ combined type-eq
        combined-transport combined-coherence)
      (left-catchup-invariant
        (left-silent-invariant refl refl) (inj₁ (vW , noW))))
    combined-lineage
    coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  source-atom =
    applyTys-preserves-Atom (sourceChanges inner) atom

  second-relation =
    atomic-source-value-reindexᵀ source-atom vW
      (canonicalIndexedResults indexed) (transportType inner q)

  second = weak-one-step-keep-source-catchupᵀ
    (post-catchup-β-id (sourceChanges inner) vW)
    second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first first-silent) second

  second-lineage =
    weak-step-store-lineage
      (resultStore first) rel-store-embedding-reflⁱ prefix-reflⁱ

  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent first first-silent) second
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      second-lineage

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ T ⊣ resultRightCtx combined}
        (sourceTypeResult combined)
        (targetTypeResult combined)
        (resultType combined))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second q)))

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first first-silent) second
      first-transport
      (weak-one-step-keep-source-catchup-transportᵀ
        (post-catchup-β-id (sourceChanges inner) vW)
        second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first first-silent) second
      first-coherence
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (post-catchup-β-id (sourceChanges inner) vW)
        second-relation)
world-coherent-source-id-widen-castᵀ atom prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-source-cast-blame-frameᵀ
      catchup framed refl first-silent
      first-transport first-coherence refl)
    terminal-combined-lineage
    coherent exclusive unique wfL
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

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

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

  terminal-first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-second-lineage =
    weak-step-store-lineage
      (resultStore terminal-first)
      rel-store-embedding-reflⁱ prefix-reflⁱ

  terminal-combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent terminal-first
        (left-silent-invariant refl refl))
      terminal-second
      terminal-first-lineage terminal-second-lineage
