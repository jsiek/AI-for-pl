module
  proof.Target.Administration.NuImprecisionTargetPendingLambdaAllocationTraceProof
  where

-- File Charter:
--   * Proves the exact pending-cast target trace for polymorphic-lambda
--     allocation.
--   * Frames the two-step reduction through every pending cast and identifies
--     the resulting coercion action with one type shift.
--   * Contains no simulation recursion, result/view/outcome type, postulate,
--     hole, permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (Coercion; ⇑ᶜ)
open import Data.List using
  (List; []; map; _∷_)
open import Data.Nat using (suc)
open import NuReduction using
  ( StoreChanges
  ; bind
  ; keep
  ; pure-step
  ; β-Λ•
  ; ν-step
  ; ξ-⟨⟩
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  ; _—→[_]_
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-Λ
  ; Λ_
  ; _•
  ; _⟨_⟩
  ; ν
  ; ⇑ᵗᵐ
  )
open import Relation.Binary.PropositionalEquality using
  (cong₂; subst)
open import Types using (extᵗ; ★)
open import proof.Core.Properties.NuTermProperties using
  (open0-ext-suc-cancelᵐ; renameᵗᵐ-preserves-Value)
open import proof.Core.Properties.ReductionProperties using
  ( all-[]
  ; all-keep
  ; applyCoercions
  ; applyCoercions-last-bind
  ; cast-↠
  )
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (applyTargetPendingCasts)
open import
  proof.Target.Administration.NuImprecisionTargetPendingLambdaAllocationTraceDef
  using (TargetPendingLambdaAllocationTraceᵀ)


private
  lift-reduction-through-pending-casts :
    ∀ (cs : List Coercion) {M N : Term} {χs : StoreChanges} →
    M —↠[ χs ] N →
    applyTargetPendingCasts M cs —↠[ χs ]
      applyTargetPendingCasts N (map (applyCoercions χs) cs)
  lift-reduction-through-pending-casts [] M↠N = M↠N
  lift-reduction-through-pending-casts (c ∷ cs) M↠N =
    lift-reduction-through-pending-casts cs (cast-↠ M↠N)

  allocation-pending-coercions :
    ∀ cs →
    map (applyCoercions (bind ★ ∷ keep ∷ [])) cs ≡ map ⇑ᶜ cs
  allocation-pending-coercions [] = refl
  allocation-pending-coercions (c ∷ cs) =
    cong₂ _∷_
      (applyCoercions-last-bind
        [] ★ (keep ∷ []) (all-keep all-[]) c)
      (allocation-pending-coercions cs)

  post-allocation-lambda-step :
    ∀ {W′ s} →
    Value W′ →
    ((⇑ᵗᵐ (Λ W′)) •) ⟨ s ⟩ —→[ keep ] W′ ⟨ s ⟩
  post-allocation-lambda-step {W′ = W′} vW′ =
    ξ-⟨⟩
      (subst
        (λ N → (⇑ᵗᵐ (Λ W′)) • —→[ keep ] N)
        (open0-ext-suc-cancelᵐ W′)
        (pure-step
          (β-Λ•
            (renameᵗᵐ-preserves-Value (extᵗ suc) vW′))))


target-pending-lambda-allocation-trace-proofᵀ :
  TargetPendingLambdaAllocationTraceᵀ
target-pending-lambda-allocation-trace-proofᵀ
    {W′ = W′} {s = s} {cs = cs} vW′ noW′ =
  subst
    (λ ds →
      applyTargetPendingCasts (ν ★ (Λ W′) s) cs
        —↠[ bind ★ ∷ keep ∷ [] ]
        applyTargetPendingCasts (W′ ⟨ s ⟩) ds)
    (allocation-pending-coercions cs)
    (lift-reduction-through-pending-casts cs
      (↠-step (ν-step (Λ vW′) (no•-Λ noW′))
        (↠-step (post-allocation-lambda-step vW′) ↠-refl)))
