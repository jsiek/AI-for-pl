module
  proof.NuImprecisionWorldCoherentQuotientInstFunTagCatchupProof
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
open import Data.Product using (_,_)
open import ImprecisionWf using (id★; tag_⇛_; _∣_⊢_⊑_⊣_)
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
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import TermTyping using (cast-tag-or-id)
open import Types using (★; _⇒_)
open import proof.NuImprecisionQuotientValue using
  (star-imprecision-target)
open import
  proof.NuImprecisionWorldCoherentLeftCatchupPrependKeepStep
  using (world-coherent-left-catchup-prepend-keep-step)
open import
  proof.NuImprecisionWorldCoherentQuotientInstCatchupDef
  using (WorldCoherentQuotientInstCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientInstFunTagCatchupDef
  using (WorldCoherentQuotientInstFunTagCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceInertWidenFrameDef
  using (WorldCoherentSourceInertWidenFrameᵀ)


world-coherent-quotient-inst-fun-tag-catchup-proofᵀ :
  WorldCoherentQuotientInstCatchupᵀ →
  WorldCoherentSourceInertWidenFrameᵀ →
  WorldCoherentQuotientInstFunTagCatchupᵀ
world-coherent-quotient-inst-fun-tag-catchup-proofᵀ
    plain frame {pA = pA}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down
    (quotient-id-widening
      (C.cast-seq (C.cast-inst hB occ s⊢)
                  (C.cast-tag hG gG ok) ,
       NW.inst-fun-tag safe)
      u′⊑) =
  world-coherent-left-catchup-prepend-keep-step
    (pure-step (β-seq vVd))
    (frame
      ((★ ⇒ ★) C.!) prefix-reflⁱ
      cast-tag-or-id seal★-tag-or-id tag⊑
      plain-catchup pA)
  where
  fun⊑★ = tag_⇛_ id★ id★

  fun⊑A′ =
    subst (λ X → _ ∣ _ ⊢ (★ ⇒ ★) ⊑ X ⊣ _)
      (sym (star-imprecision-target pA)) fun⊑★

  inst-pair =
    quotient-id-widening
      (C.cast-inst hB occ s⊢ , NW.inst safe) u′⊑

  plain-catchup =
    plain {pA = fun⊑A′}
      coherent exclusive wfL (ok-⟨⟩ (ok-no noVd))
      vVd noVd vV′ noV′ inert-d′ inert-u′ down inst-pair

  tag⊑ =
    NW.widen-mode-relax { μ = C.id-onlyᵈ }
      C.id-only≤tag-or-idᵈ
      (C.cast-tag hG gG ok , NW.tag gG)
world-coherent-quotient-inst-fun-tag-catchup-proofᵀ
    plain frame {pA = pA}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down
    (quotient-cast-widening mode seal★
      (C.cast-seq (C.cast-inst hB occ s⊢)
                  (C.cast-tag hG gG ok) ,
       NW.inst-fun-tag safe)
      mode′ seal★′ u′⊑) =
  world-coherent-left-catchup-prepend-keep-step
    (pure-step (β-seq vVd))
    (frame
      ((★ ⇒ ★) C.!) prefix-reflⁱ mode seal★ tag⊑
      plain-catchup pA)
  where
  fun⊑★ = tag_⇛_ id★ id★

  fun⊑A′ =
    subst (λ X → _ ∣ _ ⊢ (★ ⇒ ★) ⊑ X ⊣ _)
      (sym (star-imprecision-target pA)) fun⊑★

  inst-pair =
    quotient-cast-widening mode seal★
      (C.cast-inst hB occ s⊢ , NW.inst safe)
      mode′ seal★′ u′⊑

  plain-catchup =
    plain {pA = fun⊑A′}
      coherent exclusive wfL (ok-⟨⟩ (ok-no noVd))
      vVd noVd vV′ noV′ inert-d′ inert-u′ down inst-pair

  tag⊑ = C.cast-tag hG gG ok , NW.tag gG
