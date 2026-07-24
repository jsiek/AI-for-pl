module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsInstResidualAccProof
  where

-- File Charter:
--   * Proves the mechanical plain-instantiation branch of the private
--     accessibility-indexed target pending-cast worker.
--   * Classifies framing provenance, descends first to the target-`ν` rank
--     and then to its exposed body-cast rank, and prepends `β-inst` beneath
--     the arbitrary pending tail.
--   * Leaves only the exact target-allocation semantic boundary as a
--     higher-order dependency and never constructs a post-beta QTI relation.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, catch-all, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (<-trans; n<1+n)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Induction.WellFounded using (acc)
import NarrowWiden as NW
open import NarrowWiden using (widen-mode-relax)
open import NuReduction using
  (β-inst; pure-step)
open import NuTermImprecision using
  (seal★-tag-or-id)
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; ok-no
  ; ok-⟨⟩
  ; ok-ν
  )
open import Relation.Binary.PropositionalEquality using
  (subst; sym)
open import TermTyping using
  (cast-tag-or-id)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureProof
  using
  (target-inst-rank-decreases; target-nu-rank-decreases)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (applyTargetPendingCasts)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextDef
  using (WorldCoherentRightTargetPendingCastPrependContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsInstResidualAccDef
  using (WorldCoherentRightTargetPendingCastsInstResidualAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationAccDef
  using (WorldCoherentRightTargetPendingNuAllocationAccᵀ)


private
  successor-rank-decrease :
    ∀ {inner outer} →
    outer ≡ suc inner →
    inner < outer
  successor-rank-decrease {inner} equality =
    subst (inner <_) (sym equality) (n<1+n inner)

  triple-successor-rank-decrease :
    ∀ {inner outer} →
    outer ≡ suc (suc (suc inner)) →
    inner < outer
  triple-successor-rank-decrease {inner} equality =
    subst
      (inner <_)
      (sym equality)
      (<-trans
        (n<1+n inner)
        (<-trans
          (n<1+n (suc inner))
          (n<1+n (suc (suc inner)))))

  apply-pending-runtime :
    ∀ cs {M : Term} →
    RuntimeOK M →
    RuntimeOK (applyTargetPendingCasts M cs)
  apply-pending-runtime [] runtime = runtime
  apply-pending-runtime (c ∷ cs) runtime =
    apply-pending-runtime cs (ok-⟨⟩ runtime)


world-coherent-right-target-pending-casts-inst-residual-acc-proofᵀ :
  WorldCoherentRightTargetPendingNuAllocationAccᵀ →
  WorldCoherentRightTargetPendingCastPrependContextᵀ →
  WorldCoherentRightTargetPendingCastsInstResidualAccᵀ
world-coherent-right-target-pending-casts-inst-residual-acc-proofᵀ
    allocation prepend
    vW access
    (inj₁ (μ′ , β , X′ , ()))
world-coherent-right-target-pending-casts-inst-residual-acc-proofᵀ
    allocation prepend
    vW access
    (inj₂ (inj₁ (μ′ , β , X′ , ())))
world-coherent-right-target-pending-casts-inst-residual-acc-proofᵀ
    allocation prepend
    vW access
    (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       C.cast-inst hB occ s⊢ , NW.cross ()))))
world-coherent-right-target-pending-casts-inst-residual-acc-proofᵀ
    allocation prepend
    {B = B} {s = s} {cs = cs}
    vW (acc smaller)
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ , widening)))))
    tail coherent exclusive unique wfR runtime
    vV noV noW relation
    with smaller
      (triple-successor-rank-decrease
        (target-inst-rank-decreases vW B s cs))
world-coherent-right-target-pending-casts-inst-residual-acc-proofᵀ
    allocation prepend
    {B = B} {s = s} {cs = cs}
    vW (acc smaller)
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ , widening)))))
    tail coherent exclusive unique wfR runtime
    vV noV noW relation
    | acc smaller-nu
    with allocation vW
      (smaller-nu
        (successor-rank-decrease
          (target-nu-rank-decreases vW s cs)))
      mode seal★ widening tail coherent exclusive unique wfR
      (apply-pending-runtime cs (ok-ν (ok-no noW)))
      vV noV noW relation
world-coherent-right-target-pending-casts-inst-residual-acc-proofᵀ
    allocation prepend
    {B = B} {s = s} {cs = cs}
    vW (acc smaller)
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ , widening)))))
    tail coherent exclusive unique wfR runtime
    vV noV noW relation
    | acc smaller-nu
    | caught , context-eq , right-prefix =
  prepend
    {cs = cs}
    (pure-step (β-inst vW))
    caught context-eq right-prefix
world-coherent-right-target-pending-casts-inst-residual-acc-proofᵀ
    allocation prepend
    {B = B} {s = s} {cs = cs}
    vW (acc smaller)
    (inj₂ (inj₂ (inj₂ (inj₂
      (seal★ , widening)))))
    tail coherent exclusive unique wfR runtime
    vV noV noW relation
    with smaller
      (triple-successor-rank-decrease
        (target-inst-rank-decreases vW B s cs))
world-coherent-right-target-pending-casts-inst-residual-acc-proofᵀ
    allocation prepend
    {B = B} {s = s} {cs = cs}
    vW (acc smaller)
    (inj₂ (inj₂ (inj₂ (inj₂
      (seal★ , widening)))))
    tail coherent exclusive unique wfR runtime
    vV noV noW relation
    | acc smaller-nu
    with allocation vW
      (smaller-nu
        (successor-rank-decrease
          (target-nu-rank-decreases vW s cs)))
      cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax C.id-only≤tag-or-idᵈ widening)
      tail coherent exclusive unique wfR
      (apply-pending-runtime cs (ok-ν (ok-no noW)))
      vV noV noW relation
world-coherent-right-target-pending-casts-inst-residual-acc-proofᵀ
    allocation prepend
    {B = B} {s = s} {cs = cs}
    vW (acc smaller)
    (inj₂ (inj₂ (inj₂ (inj₂
      (seal★ , widening)))))
    tail coherent exclusive unique wfR runtime
    vV noV noW relation
    | acc smaller-nu
    | caught , context-eq , right-prefix =
  prepend
    {cs = cs}
    (pure-step (β-inst vW))
    caught context-eq right-prefix
