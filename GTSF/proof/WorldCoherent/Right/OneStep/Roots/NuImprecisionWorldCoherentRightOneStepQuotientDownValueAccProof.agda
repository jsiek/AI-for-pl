module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownValueAccProof
  where

-- File Charter:
--   * Proves the accessibility-indexed two-cast quotient-down value entry by
--     exhaustive target-root analysis.
--   * Delegates identity, sequence, and successful untag residuals to the
--     generic keep-only residual worker at strictly smaller ranks.
--   * Delegates only failed untag to the terminal source-blame leaf and
--     eliminates the remaining impossible narrowing roots.
--   * Contains no residual implementation, bad-untag implementation, public
--     wrapper, postulate, hole, permissive option, additional semantic
--     parameter, or termination bypass.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using (_︔_)
open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (<-trans; n<1+n)
open import Data.Product using (_,_; Σ-syntax)
open import Induction.WellFounded using (acc)
import NarrowWiden as NW
open import NuReduction using
  ( β-id
  ; β-inst
  ; β-seq
  ; blame-⟨⟩
  ; pure-step
  ; seal-unseal
  ; tag-untag-bad
  ; tag-untag-ok
  ; ξ-⟨⟩
  ; ↠-refl
  ; ↠-step
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Value
  ; no•-⟨⟩
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureLemma
  using
  ( inert-value-administration-increaseᵀ
  ; pending-administration-tail-decreaseᵀ
  )
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureProof
  using (sequence-rank-decreases)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (world-indexed-outcome-source-blame)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownBadUntagRootDef
  using (WorldCoherentRightOneStepQuotientDownBadUntagRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownResidualAccDef
  using (WorldCoherentRightOneStepQuotientDownResidualAccᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownValueAccDef
  using (WorldCoherentRightOneStepQuotientDownValueAccᵀ)


private
  successor-rank-decrease :
    ∀ {inner outer} →
    outer ≡ suc inner →
    inner < outer
  successor-rank-decrease {inner} equality =
    subst (inner <_) (sym equality) (n<1+n inner)

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


world-coherent-right-one-step-quotient-down-value-acc-proofᵀ :
  WorldCoherentRightOneStepQuotientDownResidualAccᵀ →
  WorldCoherentRightOneStepQuotientDownBadUntagRootᵀ →
  WorldCoherentRightOneStepQuotientDownValueAccᵀ
world-coherent-right-one-step-quotient-down-value-acc-proofᵀ
    residual bad-untag {u′ = u′}
    down-mode vV noV vV′ noV′ (acc smaller)
    coherent exclusive unique wfL wfR ok-source ok-target
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible
    root@(β-id {A = I} vBody) =
  residual {cs = u′ ∷ []} {χs = []}
    down-mode vV noV vV′ noV′ vV′ noV′
    (smaller
      (pending-administration-tail-decreaseᵀ
        vV′ (C.id I) (u′ ∷ [])))
    coherent exclusive unique wfL wfR ok-source ok-target
    (ok-⟨⟩ (ok-no noV′))
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible
    (↠-step (ξ-⟨⟩ (pure-step root)) ↠-refl)
    All.[]
world-coherent-right-one-step-quotient-down-value-acc-proofᵀ
    residual bad-untag {u′ = u′}
    down-mode vV noV vV′ noV′ (acc smaller)
    coherent exclusive unique wfL wfR ok-source ok-target
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible
    root@(β-seq {p = s} {q = t} vBody) =
  residual {cs = s ∷ t ∷ u′ ∷ []} {χs = []}
    down-mode vV noV vV′ noV′ vV′ noV′
    (smaller
      (successor-rank-decrease
        (sequence-rank-decreases vV′ s t (u′ ∷ []))))
    coherent exclusive unique wfL wfR ok-source ok-target
    (ok-⟨⟩ (ok-⟨⟩ (ok-⟨⟩ (ok-no noV′))))
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible
    (↠-step (ξ-⟨⟩ (pure-step root)) ↠-refl)
    All.[]
world-coherent-right-one-step-quotient-down-value-acc-proofᵀ
    residual bad-untag {u′ = u′}
    down-mode vV noV vV′ noV′ access
    coherent exclusive unique wfL wfR ok-source ok-target
    d⊒ d-shape (d′⊢ , NW.cross ()) d′-shape V⊑V′
    down-square elimination
    widening u-shape u′-shape up-square compatible
    (β-inst vBody)
world-coherent-right-one-step-quotient-down-value-acc-proofᵀ
    residual bad-untag {u′ = u′}
    down-mode vV noV vV′ noV′ (acc smaller)
    coherent exclusive unique wfL wfR ok-source ok-target
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible
    root@(tag-untag-ok {V = W} {G = G} vBody)
    with tag-value-evidence⁻¹ vV′
world-coherent-right-one-step-quotient-down-value-acc-proofᵀ
    residual bad-untag {u′ = u′}
    down-mode vV noV
    .(vW ⟨ G C.! ⟩) noV′ (acc smaller)
    coherent exclusive unique wfL wfR ok-source ok-target
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible
    root@(tag-untag-ok {V = W} {G = G} vBody)
    | vW , refl =
  residual {cs = u′ ∷ []} {χs = []}
    down-mode vV noV (vW ⟨ G C.! ⟩) noV′
    vW (tag-no-bullet noV′)
    (smaller
      (<-trans
        (inert-value-administration-increaseᵀ
          vW (G C.!) (u′ ∷ []))
        (pending-administration-tail-decreaseᵀ
          (vW ⟨ G C.! ⟩) (G C.？) (u′ ∷ []))))
    coherent exclusive unique wfL wfR ok-source ok-target
    (ok-⟨⟩ (ok-no (tag-no-bullet noV′)))
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible
    (↠-step (ξ-⟨⟩ (pure-step root)) ↠-refl)
    All.[]
world-coherent-right-one-step-quotient-down-value-acc-proofᵀ
    residual bad-untag {u′ = u′}
    down-mode vV noV vV′ noV′ access
    coherent exclusive unique wfL wfR ok-source ok-target
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible
    root@(tag-untag-bad {V = W} {G = G} {H = H} vBody G≢H)
    with tag-value-evidence⁻¹ vV′
world-coherent-right-one-step-quotient-down-value-acc-proofᵀ
    residual bad-untag {u′ = u′}
    down-mode vV noV
    .(vW ⟨ G C.! ⟩) noV′ access
    coherent exclusive unique wfL wfR ok-source ok-target
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible
    root@(tag-untag-bad {V = W} {G = G} {H = H} vBody G≢H)
    | vW , refl
    with bad-untag down-mode vV noV vW (tag-no-bullet noV′)
      coherent exclusive unique wfL wfR ok-source ok-target
      d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
      widening u-shape u′-shape up-square compatible root
world-coherent-right-one-step-quotient-down-value-acc-proofᵀ
    residual bad-untag {u′ = u′}
    down-mode vV noV
    .(vW ⟨ G C.! ⟩) noV′ access
    coherent exclusive unique wfL wfR ok-source ok-target
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible
    root@(tag-untag-bad {V = W} {G = G} {H = H} vBody G≢H)
    | vW , refl
    | χs , source-blame =
  world-indexed-outcome-source-blame source-blame
world-coherent-right-one-step-quotient-down-value-acc-proofᵀ
    residual bad-untag {u′ = u′}
    down-mode vV noV vV′ noV′ access
    coherent exclusive unique wfL wfR ok-source ok-target
    d⊒ d-shape (d′⊢ , NW.cross ()) d′-shape V⊑V′
    down-square elimination
    widening u-shape u′-shape up-square compatible
    (seal-unseal vBody)
world-coherent-right-one-step-quotient-down-value-acc-proofᵀ
    residual bad-untag {u′ = u′}
    down-mode vV noV () noV′ access
    coherent exclusive unique wfL wfR ok-source ok-target
    d⊒ d-shape d′⊒ d′-shape V⊑V′ down-square elimination
    widening u-shape u′-shape up-square compatible blame-⟨⟩
