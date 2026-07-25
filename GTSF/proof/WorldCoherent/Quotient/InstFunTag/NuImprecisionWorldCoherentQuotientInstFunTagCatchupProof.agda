module
  proof.WorldCoherent.Quotient.InstFunTag.NuImprecisionWorldCoherentQuotientInstFunTagCatchupProof
  where

-- File Charter:
--   * Reduces eager quotient-inst/function-tag catch-up to plain quotient-inst
--     catch-up.
--   * Frames the plain result with the inert function tag and prepends the
--     administrative sequence step.
--   * Treats the plain quotient-inst capability as its sole semantic
--     dependency.

import Coercions as C
open import Coercions using (id-only≤tag-or-idᵈ; _!; _︔_)
open import Agda.Builtin.Equality using (refl)
open import CastImprecisionShape using
  ( shape-inst
  ; shape-sequence-widening
  ; shape-tag-fun
  )
open import Data.Product using (_,_)
open import ImprecisionWf using (id★; tag_⇛_; _∣_⊢_⊑_⊣_)
open import ImprecisionComposition using
  ( comp-id★
  ; comp-tag-⇛-id★
  )
import NarrowWiden as NW
open import NuReduction using (pure-step; β-seq)
open import NuTermImprecision using (seal★-tag-or-id)
open import NuTerms using (ok-no; ok-⟨⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; prefix-reflⁱ
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import TermTyping using (cast-tag-or-id)
open import Types using (★; _⇒_)
open import proof.Quotient.NuImprecisionQuotientValue using
  (quotient-boundary-factor-left-direct)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftCatchupPrependKeepStep
  using (world-coherent-left-catchup-prepend-keep-step)
open import
  proof.WorldCoherent.Quotient.InstCatchup.NuImprecisionWorldCoherentQuotientInstCatchupDef
  using (WorldCoherentQuotientInstCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstFunTag.NuImprecisionWorldCoherentQuotientInstFunTagCatchupDef
  using (WorldCoherentQuotientInstFunTagCatchupᵀ)
open import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceInertWidenFrameDef
  using (WorldCoherentSourceInertWidenFrameᵀ)


world-coherent-quotient-inst-fun-tag-catchup-proofᵀ :
  WorldCoherentQuotientInstCatchupᵀ →
  WorldCoherentSourceInertWidenFrameᵀ →
  WorldCoherentQuotientInstFunTagCatchupᵀ
world-coherent-quotient-inst-fun-tag-catchup-proofᵀ
    plain frame {pA = id★}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down
    (quotient-id-widening
      (C.cast-seq (C.cast-inst hB occ s⊢)
                  (C.cast-tag hG gG ok) ,
       NW.inst-fun-tag safe)
      u′⊑)
    (shape-sequence-widening
      (shape-inst s-shape) shape-tag-fun sequence-comp)
    u′-shape up-square =
  world-coherent-left-catchup-prepend-keep-step
    (pure-step (β-seq vVd))
    (frame
      ((★ ⇒ ★) C.!) prefix-reflⁱ
      cast-tag-or-id seal★-tag-or-id tag⊑
      plain-catchup id★ shape-tag-fun tag-comp)
  where
  fun⊑★ = tag_⇛_ id★ id★

  inst-pair =
    quotient-id-widening
      (C.cast-inst hB occ s⊢ , NW.inst safe) u′⊑

  tag-comp = comp-tag-⇛-id★ comp-id★ comp-id★

  inst-square =
    quotient-boundary-factor-left-direct
      fun⊑★ refl sequence-comp tag-comp up-square

  plain-catchup =
    plain {pA = fun⊑★}
      coherent exclusive wfL (ok-⟨⟩ (ok-no noVd))
      vVd noVd vV′ noV′ inert-d′ inert-u′ down inst-pair
      (shape-inst s-shape) u′-shape inst-square

  tag⊑ =
    NW.widen-mode-relax { μ = C.id-onlyᵈ }
      C.id-only≤tag-or-idᵈ
      (C.cast-tag hG gG ok , NW.tag gG)
world-coherent-quotient-inst-fun-tag-catchup-proofᵀ
    plain frame {pA = id★}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down
    (quotient-cast-widening mode seal★
      (C.cast-seq (C.cast-inst hB occ s⊢)
                  (C.cast-tag hG gG ok) ,
       NW.inst-fun-tag safe)
      mode′ seal★′ u′⊑)
    (shape-sequence-widening
      (shape-inst s-shape) shape-tag-fun sequence-comp)
    u′-shape up-square =
  world-coherent-left-catchup-prepend-keep-step
    (pure-step (β-seq vVd))
    (frame
      ((★ ⇒ ★) C.!) prefix-reflⁱ mode seal★ tag⊑
      plain-catchup id★ shape-tag-fun tag-comp)
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

  plain-catchup =
    plain {pA = fun⊑★}
      coherent exclusive wfL (ok-⟨⟩ (ok-no noVd))
      vVd noVd vV′ noV′ inert-d′ inert-u′ down inst-pair
      (shape-inst s-shape) u′-shape inst-square

  tag⊑ = C.cast-tag hG gG ok , NW.tag gG
