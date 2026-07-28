module
  proof.WorldCoherent.Quotient.InstFunTag.NuImprecisionWorldCoherentQuotientInstFunTagRuntimeSiblingCatchupProof
  where

-- File Charter:
--   * Reduces eager quotient-inst/function-tag runtime-sibling catch-up to
--     the plain quotient-inst sibling leaf.
--   * Frames the plain result with the inert function tag and prepends the
--     administrative sequence step through the exact sibling-aware join.
--   * Contains no allocation reconstruction, classifier duplication,
--     postulate, hole, or permissive option.

import Coercions as C
import NarrowWiden as NW
open import Agda.Builtin.Equality using (refl)
open import CastImprecisionShape using
  ( shape-inst
  ; shape-sequence-widening
  ; shape-tag-fun
  )
open import Coercions using
  (id-only≤tag-or-idᵈ; _!; _︔_)
open import Data.Product using (_,_; proj₁; proj₂)
open import ImprecisionComposition using
  (comp-id★; comp-tag-⇛-id★)
open import ImprecisionWf using
  (id★; tag_⇛_)
open import NuReduction using
  (pure-step; β-seq)
open import proof.Core.Properties.CastImprecision using
  ( seal★-tag-or-id
  )
open import NuTerms using
  (no•-⟨⟩; ok-no; ok-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; cast⊑⊑ᵀ
  ; prefix-reflⁱ
  ; quotient-cast-widening
  ; quotient-id-widening
  ; up⊑upᵀ
  )
open import TermTyping using
  (cast-tag-or-id)
open import Types using (★; _⇒_)
open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( canonicalIndexedResults
  ; catchupIndexedResult
  ; left-silent-indexed
  ; left-silent-invariant
  ; weak-indexed-result
  )
open import proof.Quotient.NuImprecisionQuotientValue using
  (quotient-boundary-factor-left-direct)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupRuntimeSiblingComposition
  using
  (world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (worldCatchupResult)
open import
  proof.WorldCoherent.Quotient.InstCatchup.NuImprecisionWorldCoherentQuotientInstRuntimeSiblingCatchupDef
  using (WorldCoherentQuotientInstRuntimeSiblingCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstFunTag.NuImprecisionWorldCoherentQuotientInstFunTagRuntimeSiblingCatchupDef
  using (WorldCoherentQuotientInstFunTagRuntimeSiblingCatchupᵀ)
open import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenRuntimeSiblingCatchupProof
  using (world-coherent-source-inert-widen-runtime-sibling-catchupᵀ)


world-coherent-quotient-inst-fun-tag-runtime-sibling-catchup-proofᵀ :
  WorldCoherentQuotientInstRuntimeSiblingCatchupᵀ →
  WorldCoherentQuotientInstFunTagRuntimeSiblingCatchupᵀ
world-coherent-quotient-inst-fun-tag-runtime-sibling-catchup-proofᵀ
    plain {pA = id★}
    coherent exclusive unique wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down
    (quotient-id-widening
      (C.cast-seq (C.cast-inst hB occ s⊢)
                  (C.cast-tag hG gG ok) ,
       NW.inst-fun-tag safe)
      u′⊑)
    (shape-sequence-widening
      (shape-inst s-shape) shape-tag-fun sequence-comp)
    u′-shape up-square noR okR′ sibling =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage framed-pair
  where
  fun⊑★ = tag_⇛_ id★ id★

  inst-pair =
    quotient-id-widening
      (C.cast-inst hB occ s⊢ , NW.inst safe) u′⊑

  tag-comp = comp-tag-⇛-id★ comp-id★ comp-id★

  inst-square =
    quotient-boundary-factor-left-direct
      fun⊑★ refl sequence-comp tag-comp up-square

  plain-pair =
    plain {pA = fun⊑★}
      coherent exclusive unique wfL
      (ok-⟨⟩ (ok-no noVd))
      vVd noVd vV′ noV′ inert-d′ inert-u′ down inst-pair
      (shape-inst s-shape) u′-shape inst-square
      noR okR′ sibling

  plain-caught = proj₁ plain-pair

  plain-sibling = proj₂ plain-pair

  tag⊑ =
    NW.widen-mode-relax {μ = C.id-onlyᵈ}
      C.id-only≤tag-or-idᵈ
      (C.cast-tag hG gG ok , NW.tag gG)

  framed-pair =
    world-coherent-source-inert-widen-runtime-sibling-catchupᵀ
      ((★ ⇒ ★) C.!) prefix-reflⁱ
      cast-tag-or-id seal★-tag-or-id tag⊑
      (vV′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noV′))
      noR okR′ plain-caught plain-sibling
      id★ shape-tag-fun tag-comp

  framed-caught = proj₁ framed-pair

  framed-indexed =
    catchupIndexedResult (worldCatchupResult framed-caught)

  inst-relation =
    up⊑upᵀ down inst-pair fun⊑★
      (shape-inst s-shape) u′-shape inst-square

  residual-relation =
    cast⊑⊑ᵀ cast-tag-or-id seal★-tag-or-id tag⊑
      inst-relation id★ shape-tag-fun tag-comp

  first-step = pure-step (β-seq vVd)

  first-raw =
    weak-one-step-keep-source-catchupᵀ
      first-step residual-relation

  first-indexed =
    weak-indexed-result first-raw residual-relation
      (weak-one-step-keep-source-catchup-transportᵀ
        first-step residual-relation)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        first-step residual-relation)

  first-silent =
    left-silent-indexed first-indexed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-⟨⟩ (ok-no noVd)))

  first-lineage =
    weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ
world-coherent-quotient-inst-fun-tag-runtime-sibling-catchup-proofᵀ
    plain {pA = id★}
    coherent exclusive unique wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down
    (quotient-cast-widening mode seal★
      (C.cast-seq (C.cast-inst hB occ s⊢)
                  (C.cast-tag hG gG ok) ,
       NW.inst-fun-tag safe)
      mode′ seal★′ u′⊑)
    (shape-sequence-widening
      (shape-inst s-shape) shape-tag-fun sequence-comp)
    u′-shape up-square noR okR′ sibling =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage framed-pair
  where
  fun⊑★ = tag_⇛_ id★ id★

  inst-pair =
    quotient-cast-widening mode seal★
      (C.cast-inst hB occ s⊢ , NW.inst safe)
      mode′ seal★′ u′⊑

  tag-comp = comp-tag-⇛-id★ comp-id★ comp-id★

  inst-square =
    quotient-boundary-factor-left-direct
      fun⊑★ refl sequence-comp tag-comp up-square

  plain-pair =
    plain {pA = fun⊑★}
      coherent exclusive unique wfL
      (ok-⟨⟩ (ok-no noVd))
      vVd noVd vV′ noV′ inert-d′ inert-u′ down inst-pair
      (shape-inst s-shape) u′-shape inst-square
      noR okR′ sibling

  plain-caught = proj₁ plain-pair

  plain-sibling = proj₂ plain-pair

  tag⊑ = C.cast-tag hG gG ok , NW.tag gG

  framed-pair =
    world-coherent-source-inert-widen-runtime-sibling-catchupᵀ
      ((★ ⇒ ★) C.!) prefix-reflⁱ
      mode seal★ tag⊑
      (vV′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noV′))
      noR okR′ plain-caught plain-sibling
      id★ shape-tag-fun tag-comp

  framed-caught = proj₁ framed-pair

  framed-indexed =
    catchupIndexedResult (worldCatchupResult framed-caught)

  inst-relation =
    up⊑upᵀ down inst-pair fun⊑★
      (shape-inst s-shape) u′-shape inst-square

  residual-relation =
    cast⊑⊑ᵀ mode seal★ tag⊑
      inst-relation id★ shape-tag-fun tag-comp

  first-step = pure-step (β-seq vVd)

  first-raw =
    weak-one-step-keep-source-catchupᵀ
      first-step residual-relation

  first-indexed =
    weak-indexed-result first-raw residual-relation
      (weak-one-step-keep-source-catchup-transportᵀ
        first-step residual-relation)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        first-step residual-relation)

  first-silent =
    left-silent-indexed first-indexed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (ok-⟨⟩ (ok-no noVd)))

  first-lineage =
    weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ
