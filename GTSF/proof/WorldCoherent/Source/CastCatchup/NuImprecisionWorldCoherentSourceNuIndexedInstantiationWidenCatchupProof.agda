module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceNuIndexedInstantiationWidenCatchupProof
  where

-- File Charter:
--   * Proves source widening by instantiation only when the incoming
--     imprecision index is explicitly source-only `ν`.
--   * Performs source type beta and fresh-`★` allocation before resuming
--     world-coherent catch-up.
--   * Contains no paired-`∀ⁱ` or arbitrary-index instantiation contract,
--     postulate, hole, or termination bypass.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping using
  (nu-term-imprecision-target-typing)
open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import CastImprecisionShape using
  ( _⊢ᶜ_⦂_
  ; widening
  ; shape-inst
  )
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionWf using
  ( NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  ; comp-ν
  ; νˢ-injective
  )
import NarrowWiden as NW
open import NarrowWiden using
  ( widen-weaken
  ; _∣_∣_⊢_∶_⊑_
  )
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
  ; ok-•
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; blame⊑ᵀ
  ; cast⊑⊑ᵀ
  ; prefix-reflⁱ
  )
open import Relation.Binary.PropositionalEquality using
  (cong; subst₂; sym; trans)
open import Store using (StoreIncl-cons)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; occurs
  ; ★
  ; `∀
  ; wf★
  )
open import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupTransportCore
  using
  ( result-widening-typingᵀ
  ; transport-source-widening-composition
  )
open import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupDef
  using (WorldCoherentSourceNuIndexedInstantiationWidenCatchupᵀ)
open import
  proof.Catchup.Core.NuImprecisionCatchupComposition
  using (weak-one-step-keep-source-catchupᵀ)
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
  proof.Source.Core.NuImprecisionSourcePolymorphicValueBase
  using (post-catchup-β-inst)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using
  ( nu-term-imprecision-transport-typesᵀ
  ; weak-result-source-widen-inst
  ; weak-one-step-reindexᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( canonicalIndexedResults
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultStore
  ; resultType
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; sourceNuIndexEquality
  ; sourceNuSafe
  ; transportShapeCoherent
  ; transportSourceNu
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
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
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupComposition
  using (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftCatchupPrependKeepStep
  using (world-coherent-left-catchup-prepend-keep-step)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; world-coherent-left-indexed-catchup
  )
open import
  proof.WorldCoherent.Source.Allocation.NuImprecisionWorldCoherentSourceAllocationStepProof
  using (world-coherent-source-inst-allocation-stepᵀ)
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
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef
  using (WorldCoherentLeftValueCatchupPrefixᵀ)
open import
  proof.Core.Properties.ReductionProperties
  using (applyTys-∀)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( cast-shape-applyCoercionUnderTyBinders
  ; cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  ; shape-source-liftνᵢ
  ; shape-subst-source
  )
open import
  proof.Core.Properties.NuStoreProperties
  using (StoreWf-bind)
open import
  proof.Core.Properties.StoreProperties
  using (renameStoreᵗ-incl)
open import
  proof.Core.Properties.TypePreservation
  using
  ( seal★-inst
  ; seal★-weaken
  )


world-coherent-source-inst-widen-castᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentSourceNuIndexedInstantiationWidenCatchupᵀ
world-coherent-source-inst-widen-castᵀ
    value-prefix
    {index-occ = index-occ} {r = r} {{safe = safe}}
    prefix mode seal★ c⊑ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    with result-widening-typingᵀ prefix mode seal★ c⊑ indexed
world-coherent-source-inst-widen-castᵀ
    value-prefix
    {index-occ = index-occ} {r = r} {{safe = safe}}
    prefix mode seal★ c⊑ vV′ noV′
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
world-coherent-source-inst-widen-castᵀ
    value-prefix
    {index-occ = index-occ} {r = r} {{safe = safe}}
    prefix mode seal★
    c⊑@(C.cast-inst hB occ s⊢ , NW.inst sʷ)
    vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape@(shape-inst inner-shape)
      comp@(comp-ν inner-comp)
    | μ′ , mode′ , final-seal , final-cast
    | inj₁ (vW , noW) =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    framed-silent framed-lineage
    (world-coherent-left-catchup-prepend-keep-step
      (post-catchup-β-inst (sourceChanges inner) vW)
      allocated-catchup)
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed-indexed =
    weak-indexed-result first (relatedResults first)
      (weak-one-step-source-cast-frame-transportᵀ
        inner final-relation (weakIndexedTransport indexed))
      (weak-one-step-source-cast-frame-coherenceᵀ
        inner final-relation (weakIndexedTypeCoherence indexed))

  runtime = ok-⟨⟩ (ok-no noW)

  framed-silent =
    left-silent-indexed framed-indexed
      (left-silent-invariant refl refl) runtime

  framed-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  transported-index =
    transportSourceNu inner safe index-occ r

  normalized =
    nu-term-imprecision-transport-typesᵀ
      (applyTys-∀ (sourceChanges inner) _) refl refl
      (canonicalIndexedResults indexed)

  shaped =
    nu-term-imprecision-transport-typesᵀ
      refl refl (sourceNuIndexEquality transported-index) normalized

  transported-r-shape =
    νˢ-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality transported-index)))
        (trans
          (shape-subst-source
            (applyTys-∀ (sourceChanges inner) _)
            (transportType inner (ν safe index-occ r)))
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed)
            (ν safe index-occ r))))

  transported-comp =
    imprecision-composition-shape-transport
      refl
      (trans
        (shape-source-liftνᵢ (transportType inner q))
        (transportShapeCoherent
          (weakIndexedTypeCoherence indexed) q))
      transported-r-shape
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

  allocation-step =
    world-coherent-source-inst-allocation-stepᵀ
      source-inst-allocation-relationᵀ
      {{sourceNuSafe transported-index}}
      coherent exclusive unique vW noW
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

  post-allocation =
    value-prefix prefix-reflⁱ
      (sourceStepWorldCoherent allocation-step)
      (sourceStepSourceNameExclusive allocation-step)
      (sourceStepAssumptionMembershipUnique allocation-step)
      allocation-wf
      (ok-⟨⟩ (ok-• vW noW))
      vV′ noV′
      (canonicalIndexedResults allocation-indexed)

  allocated-catchup =
    world-coherent-left-catchup-indexed-resume-silentᵀ
      allocation-silent
      (sourceStepStoreLineage allocation-step)
      post-allocation
world-coherent-source-inst-widen-castᵀ
    value-prefix
    {index-occ = index-occ} {r = r} {{safe = safe}}
    prefix mode seal★ c⊑ vV′ noV′
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
