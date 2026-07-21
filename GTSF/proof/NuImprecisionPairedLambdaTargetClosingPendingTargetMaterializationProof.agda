module
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetMaterializationProof
  where

-- File Charter:
--   * Implements materialization of a pending target-only frame continuation.
--   * Recurses structurally over pending prefixes, target casts, and target
--     conversions while preserving the final target value/no-bullet evidence.
--   * Depends only on the pending-frame definition, materialization statement,
--     target value/no-bullet constructors, and quotiented term-imprecision
--     frame constructors.

open import Data.Product using (_,_)
open import NuTerms using (Value; _⟨_⟩; no•-⟨⟩)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using
    ( PairedLambdaTargetClosingPendingTargetFrames
    ; pending-refl
    ; pending-prefix
    ; pending-⊑cast⊒
    ; pending-⊑cast⊑
    ; pending-⊑cast⊑id
    ; pending-⊑conv↑
    ; pending-⊑conv↓
    )
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetMaterializationDef
  using (PairedLambdaTargetClosingPendingTargetMaterializationᵀ)


paired-lambda-target-closing-pending-target-materialization-proofᵀ :
  PairedLambdaTargetClosingPendingTargetMaterializationᵀ
paired-lambda-target-closing-pending-target-materialization-proofᵀ
    vW′ noW′ W⊑W′ pending-refl =
  vW′ , noW′ , W⊑W′
paired-lambda-target-closing-pending-target-materialization-proofᵀ
    vW′ noW′ W⊑W′ (pending-prefix prefix W⊢ W′⊢ pending) =
  paired-lambda-target-closing-pending-target-materialization-proofᵀ
    vW′ noW′ (allocation-prefixᵀ prefix W⊑W′ W⊢ W′⊢) pending
paired-lambda-target-closing-pending-target-materialization-proofᵀ
    vW′ noW′ W⊑W′
    (pending-⊑cast⊒ {r = r} inert-c′ mode′ seal★′ c′⊒ pending) =
  paired-lambda-target-closing-pending-target-materialization-proofᵀ
    (vW′ ⟨ inert-c′ ⟩)
    (no•-⟨⟩ noW′)
    (⊑cast⊒ᵀ mode′ seal★′ c′⊒ W⊑W′ r)
    pending
paired-lambda-target-closing-pending-target-materialization-proofᵀ
    vW′ noW′ W⊑W′
    (pending-⊑cast⊑ {r = r} inert-c′ mode′ seal★′ c′⊑ pending) =
  paired-lambda-target-closing-pending-target-materialization-proofᵀ
    (vW′ ⟨ inert-c′ ⟩)
    (no•-⟨⟩ noW′)
    (⊑cast⊑ᵀ mode′ seal★′ c′⊑ W⊑W′ r)
    pending
paired-lambda-target-closing-pending-target-materialization-proofᵀ
    vW′ noW′ W⊑W′
    (pending-⊑cast⊑id {r = r} inert-c′ seal★′ c′⊑ pending) =
  paired-lambda-target-closing-pending-target-materialization-proofᵀ
    (vW′ ⟨ inert-c′ ⟩)
    (no•-⟨⟩ noW′)
    (⊑cast⊑idᵀ seal★′ c′⊑ W⊑W′ r)
    pending
paired-lambda-target-closing-pending-target-materialization-proofᵀ
    vW′ noW′ W⊑W′
    (pending-⊑conv↑ {r = r} inert-c′ c′↑ pending) =
  paired-lambda-target-closing-pending-target-materialization-proofᵀ
    (vW′ ⟨ inert-c′ ⟩)
    (no•-⟨⟩ noW′)
    (⊑conv↑ᵀ c′↑ W⊑W′ r)
    pending
paired-lambda-target-closing-pending-target-materialization-proofᵀ
    vW′ noW′ W⊑W′
    (pending-⊑conv↓ {r = r} inert-c′ c′↓ pending) =
  paired-lambda-target-closing-pending-target-materialization-proofᵀ
    (vW′ ⟨ inert-c′ ⟩)
    (no•-⟨⟩ noW′)
    (⊑conv↓ᵀ c′↓ W⊑W′ r)
    pending
