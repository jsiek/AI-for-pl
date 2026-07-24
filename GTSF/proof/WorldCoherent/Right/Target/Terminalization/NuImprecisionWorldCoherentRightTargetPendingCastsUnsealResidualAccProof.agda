module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsUnsealResidualAccProof
  where

-- File Charter:
--   * Proves the focused unseal branch of the private accessibility-indexed
--     target pending-cast worker.
--   * Cancels the terminal seal, recurses on the strictly smaller pending
--     tail, and prepends `seal-unseal` below every remaining cast frame.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using (unseal)
open import Data.List using ([]; _∷_)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (<-trans)
open import Data.Product using (_,_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import NuReduction using
  (pure-step; seal-unseal)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; ƛ_
  ; Λ_
  ; $
  ; no•-⟨⟩
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (nu-term-imprecision-target-typing)
open import TermTyping using (forget)
open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩)
open import proof.DGG.Core.NuProgress using
  (canonical-＇; sv-seal)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureDef
  using
  ( targetPendingAdministrationRank
  ; valueAdministrationWeight
  )
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureLemma
  using
  ( target-inert-value-administration-increaseᵀ
  ; target-pending-administration-tail-decreaseᵀ
  )
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (applyTargetPendingCasts)
open import
  proof.Target.SealTag.NuImprecisionTargetSealCancellationDef
  using (TargetSealCancellationᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextDef
  using (WorldCoherentRightTargetPendingCastPrependContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsAccDef
  using (WorldCoherentRightTargetPendingCastsAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsUnsealResidualAccDef
  using (WorldCoherentRightTargetPendingCastsUnsealResidualAccᵀ)


private
  value-administration-weight-proof-irrelevant :
    ∀ {V : Term} (vV vV′ : Value V) →
    valueAdministrationWeight vV ≡
      valueAdministrationWeight vV′
  value-administration-weight-proof-irrelevant
      (ƛ N) (ƛ .N) =
    refl
  value-administration-weight-proof-irrelevant
      (Λ vV) (Λ vV′)
      rewrite
        value-administration-weight-proof-irrelevant vV vV′ =
    refl
  value-administration-weight-proof-irrelevant
      ($ k) ($ .k) =
    refl
  value-administration-weight-proof-irrelevant
      (vV ⟨ inert-c ⟩) (vV′ ⟨ inert-c′ ⟩)
      rewrite
        value-administration-weight-proof-irrelevant vV vV′ =
    refl

  target-pending-rank-value-proof-irrelevant :
    ∀ {V : Term} (vV vV′ : Value V) cs →
    targetPendingAdministrationRank vV cs ≡
      targetPendingAdministrationRank vV′ cs
  target-pending-rank-value-proof-irrelevant vV vV′ cs
      rewrite
        value-administration-weight-proof-irrelevant vV vV′ =
    refl

  seal-no•⁻¹ :
    ∀ {V A α} →
    No• (V ⟨ C.seal A α ⟩) →
    No• V
  seal-no•⁻¹ (no•-⟨⟩ noV) = noV

  pending-casts-runtime⁻¹ :
    ∀ cs {M : Term} →
    RuntimeOK (applyTargetPendingCasts M cs) →
    RuntimeOK M
  pending-casts-runtime⁻¹ [] okM = okM
  pending-casts-runtime⁻¹ (c ∷ cs) okM =
    runtime-⟨⟩ (pending-casts-runtime⁻¹ cs okM)

  pending-casts-runtime :
    ∀ cs {M : Term} →
    RuntimeOK M →
    RuntimeOK (applyTargetPendingCasts M cs)
  pending-casts-runtime [] okM = okM
  pending-casts-runtime (c ∷ cs) okM =
    pending-casts-runtime cs (ok-⟨⟩ okM)


world-coherent-right-target-pending-casts-unseal-residual-acc-proofᵀ :
  TargetSealCancellationᵀ →
  WorldCoherentRightTargetPendingCastsAccᵀ →
  WorldCoherentRightTargetPendingCastPrependContextᵀ →
  WorldCoherentRightTargetPendingCastsUnsealResidualAccᵀ
world-coherent-right-target-pending-casts-unseal-residual-acc-proofᵀ
    cancel pending-worker prepend
    {B = B} {α = α} {cs = cs} {r = r}
    vW (acc recurse)
    αB∈Σ tail-spine coherent exclusive unique wfR ok-pending
    vV noV noW relation
    with canonical-＇ vW
      (forget (nu-term-imprecision-target-typing relation))
world-coherent-right-target-pending-casts-unseal-residual-acc-proofᵀ
    cancel pending-worker prepend
    {B = B} {α = α} {cs = cs} {r = r}
    vW (acc recurse)
    αB∈Σ tail-spine coherent exclusive unique wfR ok-pending
    vV noV noW relation
    | sv-seal {W = U} {A = Y} vU refl =
  prepend
    {cs = cs}
    (pure-step (seal-unseal vU))
    caught context-eq right-prefix
  where
  noU = seal-no•⁻¹ noW

  canceled =
    cancel coherent wfR vV noV vU αB∈Σ relation r

  smaller =
    <-trans
      (target-inert-value-administration-increaseᵀ
        vU (C.seal Y α) cs)
      (subst
        (λ n →
          n <
          targetPendingAdministrationRank
            vW (unseal α B ∷ cs))
        (sym
          (target-pending-rank-value-proof-irrelevant
            (vU ⟨ C.seal Y α ⟩) vW cs))
        (target-pending-administration-tail-decreaseᵀ
          vW (unseal α B) cs))

  ok-root =
    pending-casts-runtime⁻¹ cs ok-pending

  okU =
    runtime-⟨⟩ (runtime-⟨⟩ ok-root)

  continued =
    pending-worker vU (recurse smaller) tail-spine coherent
      exclusive unique wfR (pending-casts-runtime cs okU)
      vV noV noU canceled

  caught = continued .Data.Product.proj₁
  context-eq = continued .Data.Product.proj₂ .Data.Product.proj₁
  right-prefix = continued .Data.Product.proj₂ .Data.Product.proj₂
