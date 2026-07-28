module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceSequenceWidenCatchupProof
  where

-- File Charter:
--   * Proves the admissible sequential source-widen catch-up case.
--   * Makes its midpoint and value-prefix capabilities explicit.
--   * Contains no arbitrary-index source-instantiation case, dispatcher,
--     postulate, hole, or termination bypass.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping using
  (nu-term-imprecision-target-typing)
open import Agda.Builtin.Equality using (refl)
import Coercions as C
open import Coercions using (_︔_)
open import CastImprecisionShape using
  ( _⊢ᶜ_⦂_
  ; widening
  ; shape-sequence-widening
  )
open import Data.List using ([])
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( Widening
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
  ; RuntimeOK
  ; Term
  ; Value
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; blame⊑ᵀ
  ; cast⊑⊑ᵀ
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using (subst)
import Relation.Binary.HeterogeneousEquality as HE
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using (Ty; TyCtx)
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
open import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupDef
  using (WorldCoherentSourceSequenceWidenCatchupᵀ)
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
  ( left-catchup-indexed-relatedᵀ
  ; subst²-to-≅
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
  ; left-silent-indexed
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
  proof.Source.CastSequence.NuImprecisionSourceCastSequenceMidpointDef
  using
  ( SourceCastSequenceMidpointᵀ
  ; widening-midpoint
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
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupComposition
  using (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; world-coherent-left-indexed-catchup
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef
  using (WorldCoherentLeftValueCatchupPrefixᵀ)
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
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using (cast-shape-applyCoercions)


private
  terminal-world-catchupᵀ :
    ∀ {Φ Δᴸ Δᴿ W V′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    Value W →
    No• W →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ W ⊑ V′ ⦂ A ⊑ B ∶ p →
    WorldCoherentLeftCatchupIndexedResult
      {N = W} {V′ = V′} {ρ = ρ} p
  terminal-world-catchupᵀ coherent exclusive unique wfL vW noW relation =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-relatedᵀ (inj₁ (vW , noW)) relation)
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique wfL


world-coherent-source-seq-widen-castᵀ :
  SourceCastSequenceMidpointᵀ →
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentSourceSequenceWidenCatchupᵀ
world-coherent-source-seq-widen-castᵀ
    midpoint value-prefix
    prefix mode seal★ s⊑ t⊑ seqʷ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q
    sequence-shape-proof@(
      shape-sequence-widening s-shape t-shape sequence-comp)
    outer-comp
    with result-widening-typingᵀ prefix mode seal★
      (C.cast-seq (proj₁ s⊑) (proj₁ t⊑) , seqʷ) indexed
       | result-widening-typing₂ᵀ
           prefix mode seal★ s⊑ t⊑ indexed
world-coherent-source-seq-widen-castᵀ
    midpoint value-prefix
    prefix mode seal★ s⊑ t⊑ seqʷ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q
    sequence-shape-proof@(
      shape-sequence-widening s-shape t-shape sequence-comp)
    outer-comp
    | μc , modec , final-seal-c , final-cast-c
    | μst , modest , final-seal-st , final-cast-s , final-cast-t
    with final
world-coherent-source-seq-widen-castᵀ
    midpoint value-prefix
    prefix mode seal★ s⊑ t⊑ seqʷ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q
    sequence-shape-proof@(
      shape-sequence-widening s-shape t-shape sequence-comp)
    outer-comp
    | μc , modec , final-seal-c , final-cast-c
    | μst , modest , final-seal-st , final-cast-s , final-cast-t
    | inj₁ (vW , noW) =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    first-silent-result
    combined-lineage
    (value-prefix prefix-reflⁱ coherent exclusive unique wfL runtime
      vV′ noV′ (canonicalIndexedResults first-indexed))
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ modec final-seal-c final-cast-c
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions
        (sourceChanges inner) sequence-shape-proof)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) outer-comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  source-p =
    indexed-source-precision indexed

  source-q =
    transportType inner q

  seqʷ′ =
    subst Widening (applyCoercions-seq (sourceChanges inner) _ _)
      (applyCoercions-preserves-Widening (sourceChanges inner) seqʷ)

  midpoint-result =
    widening-midpoint midpoint prefix-reflⁱ coherent exclusive wfL
      modest final-seal-st (proj₁ final-cast-s) (proj₁ final-cast-t)
      seqʷ′ source-p source-q
      (cast-shape-applyCoercions (sourceChanges inner) s-shape)
      (cast-shape-applyCoercions (sourceChanges inner) t-shape)
      sequence-comp
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) outer-comp)

  source-mid = proj₁ midpoint-result

  s-triangle = proj₁ (proj₂ midpoint-result)

  t-triangle = proj₂ (proj₂ midpoint-result)

  s-relation =
    cast⊑⊑ᵀ modest final-seal-st final-cast-s
      (canonicalIndexedResults indexed) source-mid
      (cast-shape-applyCoercions (sourceChanges inner) s-shape)
      s-triangle

  second-relation =
    cast⊑⊑ᵀ modest final-seal-st final-cast-t
      s-relation source-q
      (cast-shape-applyCoercions (sourceChanges inner) t-shape)
      t-triangle

  second = weak-one-step-keep-source-catchupᵀ
    (post-catchup-β-seq (sourceChanges inner) vW)
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

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first first-silent) second
      first-transport
      (weak-one-step-keep-source-catchup-transportᵀ
        (post-catchup-β-seq (sourceChanges inner) vW)
        second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first first-silent) second
      first-coherence
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (post-catchup-β-seq (sourceChanges inner) vW)
        second-relation)

  first-indexed = weak-one-step-index-resultᵀ combined type-eq
    combined-transport combined-coherence

  runtime =
    ok-⟨⟩ (ok-⟨⟩ (ok-no noW))

  first-silent-result =
    left-silent-indexed first-indexed
      (left-silent-invariant refl refl) runtime
world-coherent-source-seq-widen-castᵀ
    midpoint value-prefix
    prefix mode seal★ s⊑ t⊑ seqʷ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q
    sequence-shape-proof@(
      shape-sequence-widening s-shape t-shape sequence-comp)
    outer-comp
    | μc , modec , final-seal-c , final-cast-c
    | μst , modest , final-seal-st , final-cast-s , final-cast-t
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
    cast⊑⊑ᵀ modec final-seal-c final-cast-c
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions
        (sourceChanges inner) sequence-shape-proof)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) outer-comp)

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
