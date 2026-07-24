module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsAccProof
  where

-- File Charter:
--   * Proves the accessibility-indexed target pending-cast worker.
--   * Owns empty, inert, identity, untag, and sequence administration and
--     delegates exactly the four residual active plans.
--   * Recurses structurally through strict target-administration rank edges.
--   * Preserves the canonical target context action and right-only lineage.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using (_︔_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (<-trans; n<1+n)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import NuReduction using
  (β-id; β-seq; pure-step; tag-untag-ok)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Value
  ; no•-⟨⟩
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import TermTyping using (forget)
open import proof.DGG.Core.NuProgress using
  (canonical-★; sv-tag)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureDef
  using (targetPendingAdministrationRank)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureLemma
  using
  ( target-inert-value-administration-increaseᵀ
  ; target-pending-administration-tail-decreaseᵀ
  )
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureProof
  using
  (target-inert-rank-decreases; target-sequence-rank-decreases)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef
  using
  ( plan-fun-untag-gen
  ; plan-id
  ; plan-inert
  ; plan-inst
  ; plan-inst-fun-tag
  ; plan-seq
  ; plan-unseal
  ; plan-untag
  )
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using
  ( applyTargetPendingCasts
  ; pending-cons
  ; pending-empty
  ; residual-fun-untag-gen
  ; residual-inst
  ; residual-inst-fun-tag
  ; residual-unseal
  )
open import
  proof.Target.Administration.NuImprecisionTargetPendingSequenceExpansion
  using (target-administration-sequence-spine-expansionᵀ)
open import
  proof.Target.SealTag.NuImprecisionTargetTagCancellationLemma
  using (target-tag-cancellationᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextLemma
  using
  (world-coherent-right-target-pending-cast-prepend-contextᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsAccDef
  using (WorldCoherentRightTargetPendingCastsAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsResidualAccDef
  using (WorldCoherentRightTargetPendingCastsResidualAccᵀ)
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextLemma
  using (world-coherent-right-value-terminal-contextᵀ)


private
  successor-rank-decrease :
    ∀ {inner outer} →
    outer ≡ suc inner →
    inner < outer
  successor-rank-decrease {inner} equality =
    subst (inner <_) (sym equality) (n<1+n inner)

  apply-pending-runtime :
    ∀ cs {M} →
    RuntimeOK M →
    RuntimeOK (applyTargetPendingCasts M cs)
  apply-pending-runtime [] runtime = runtime
  apply-pending-runtime (c ∷ cs) runtime =
    apply-pending-runtime cs (ok-⟨⟩ runtime)

  tag-no-bullet :
    ∀ {V G} →
    No• (V ⟨ G C.! ⟩) →
    No• V
  tag-no-bullet (no•-⟨⟩ noV) = noV

  tag-value-evidence⁻¹ :
    ∀ {V G} →
    (vTag : Value (V ⟨ G C.! ⟩)) →
    Σ[ vV ∈ Value V ] vTag ≡ (vV ⟨ G C.! ⟩)
  tag-value-evidence⁻¹ (vV ⟨ G C.! ⟩) = vV , refl


world-coherent-right-target-pending-casts-acc-proofᵀ :
  WorldCoherentRightTargetPendingCastsResidualAccᵀ →
  WorldCoherentRightTargetPendingCastsAccᵀ
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    vW access pending-empty coherent exclusive unique wfR
    runtime vV noV noW relation =
  world-coherent-right-value-terminal-contextᵀ
    prefix-reflⁱ coherent exclusive unique wfR
    vV noV vW noW relation
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {r = r} (plan-inert inert-c)
      (inj₁ (μ′ , β , X′ , reveal)) tail)
    coherent exclusive unique wfR runtime vV noV noW relation =
  world-coherent-right-target-pending-casts-acc-proofᵀ residual
    (vW ⟨ inert-c ⟩)
    (smaller
      (successor-rank-decrease
        (target-inert-rank-decreases vW inert-c cs)))
    tail coherent exclusive unique wfR runtime
    vV noV (no•-⟨⟩ noW)
    (⊑conv↑ᵀ reveal relation r)
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {r = r} (plan-inert inert-c)
      (inj₂ (inj₁ (μ′ , β , X′ , conceal))) tail)
    coherent exclusive unique wfR runtime vV noV noW relation =
  world-coherent-right-target-pending-casts-acc-proofᵀ residual
    (vW ⟨ inert-c ⟩)
    (smaller
      (successor-rank-decrease
        (target-inert-rank-decreases vW inert-c cs)))
    tail coherent exclusive unique wfR runtime
    vV noV (no•-⟨⟩ noW)
    (⊑conv↓ᵀ conceal relation r)
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {r = r} (plan-inert inert-c)
      (inj₂ (inj₂ (inj₁
        (μ′ , mode , seal★ , narrowing)))) tail)
    coherent exclusive unique wfR runtime vV noV noW relation =
  world-coherent-right-target-pending-casts-acc-proofᵀ residual
    (vW ⟨ inert-c ⟩)
    (smaller
      (successor-rank-decrease
        (target-inert-rank-decreases vW inert-c cs)))
    tail coherent exclusive unique wfR runtime
    vV noV (no•-⟨⟩ noW)
    (⊑cast⊒ᵀ mode seal★ narrowing relation r)
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {r = r} (plan-inert inert-c)
      (inj₂ (inj₂ (inj₂ (inj₁
        (μ′ , mode , seal★ , widening))))) tail)
    coherent exclusive unique wfR runtime vV noV noW relation =
  world-coherent-right-target-pending-casts-acc-proofᵀ residual
    (vW ⟨ inert-c ⟩)
    (smaller
      (successor-rank-decrease
        (target-inert-rank-decreases vW inert-c cs)))
    tail coherent exclusive unique wfR runtime
    vV noV (no•-⟨⟩ noW)
    (⊑cast⊑ᵀ mode seal★ widening relation r)
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {r = r} (plan-inert inert-c)
      (inj₂ (inj₂ (inj₂ (inj₂
        (seal★ , widening))))) tail)
    coherent exclusive unique wfR runtime vV noV noW relation =
  world-coherent-right-target-pending-casts-acc-proofᵀ residual
    (vW ⟨ inert-c ⟩)
    (smaller
      (successor-rank-decrease
        (target-inert-rank-decreases vW inert-c cs)))
    tail coherent exclusive unique wfR runtime
    vV noV (no•-⟨⟩ noW)
    (⊑cast⊑idᵀ seal★ widening relation r)
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {p = p} {r = r} plan-id evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation
    with assumption-membership-unique→precision-index-unique unique p r
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {p = p} {r = .p} plan-id evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation
    | refl
    with world-coherent-right-target-pending-casts-acc-proofᵀ residual
      vW
      (smaller
        (target-pending-administration-tail-decreaseᵀ vW c cs))
      tail coherent exclusive unique wfR
      (apply-pending-runtime cs (ok-no noW))
      vV noV noW relation
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {p = p} {r = .p} plan-id evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation
    | refl
    | caught , context-eq , right-prefix =
  world-coherent-right-target-pending-cast-prepend-contextᵀ
    {cs = cs}
    (pure-step (β-id vW))
    caught context-eq right-prefix
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {r = r} (plan-untag {gH = gH})
      evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation
    with canonical-★ vW
      (forget (nu-term-imprecision-target-typing relation))
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {r = r} (plan-untag {gH = gH})
      evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation
    | sv-tag {W = U} {G = G} canonical-vU refl
    with tag-value-evidence⁻¹ vW
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {r = r} (plan-untag {gH = gH})
      evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation
    | sv-tag {W = U} {G = G} canonical-vU refl
    | vU , refl
    with target-tag-cancellationᵀ
      exclusive unique gH vV noV vU relation r
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {r = r} (plan-untag {gH = gH})
      evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation
    | sv-tag {W = U} {G = G} canonical-vU refl
    | vU , refl
    | refl , canceled
    with world-coherent-right-target-pending-casts-acc-proofᵀ residual
      vU
      (smaller
        (<-trans
          (target-inert-value-administration-increaseᵀ
            vU (G C.!) cs)
          (target-pending-administration-tail-decreaseᵀ vW c cs)))
      tail coherent exclusive unique wfR
      (apply-pending-runtime cs
        (ok-no (tag-no-bullet noW)))
      vV noV (tag-no-bullet noW) canceled
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW (acc smaller)
    (pending-cons {r = r} (plan-untag {gH = gH})
      evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation
    | sv-tag {W = U} {G = G} canonical-vU refl
    | vU , refl
    | refl , canceled
    | caught , context-eq , right-prefix =
  world-coherent-right-target-pending-cast-prepend-contextᵀ
    {cs = cs}
    (pure-step (tag-untag-ok vU))
    caught context-eq right-prefix
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW access@(acc smaller)
    (pending-cons plan@plan-unseal evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation =
  residual vW access plan residual-unseal evidence tail
    coherent exclusive unique wfR runtime vV noV noW relation
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW access@(acc smaller)
    (pending-cons plan@plan-inst evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation =
  residual vW access plan residual-inst evidence tail
    coherent exclusive unique wfR runtime vV noV noW relation
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW access@(acc smaller)
    (pending-cons plan@plan-fun-untag-gen evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation =
  residual vW access plan residual-fun-untag-gen evidence tail
    coherent exclusive unique wfR runtime vV noV noW relation
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = c ∷ cs}
    vW access@(acc smaller)
    (pending-cons plan@plan-inst-fun-tag evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation =
  residual vW access plan residual-inst-fun-tag evidence tail
    coherent exclusive unique wfR runtime vV noV noW relation
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = (s ︔ t) ∷ cs}
    vW (acc smaller)
    (pending-cons
      (plan-seq s-plan t-plan) evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation
    with world-coherent-right-target-pending-casts-acc-proofᵀ residual
      vW
      (smaller
        (successor-rank-decrease
          (target-sequence-rank-decreases vW s t cs)))
      (target-administration-sequence-spine-expansionᵀ
        s-plan t-plan evidence tail)
      coherent exclusive unique wfR
      (apply-pending-runtime (s ∷ t ∷ cs) (ok-no noW))
      vV noV noW relation
world-coherent-right-target-pending-casts-acc-proofᵀ residual
    {cs = (s ︔ t) ∷ cs}
    vW (acc smaller)
    (pending-cons
      (plan-seq s-plan t-plan) evidence tail)
    coherent exclusive unique wfR runtime vV noV noW relation
    | caught , context-eq , right-prefix =
  world-coherent-right-target-pending-cast-prepend-contextᵀ
    {cs = cs}
    (pure-step (β-seq vW))
    caught context-eq right-prefix
