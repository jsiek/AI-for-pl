module
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationGenGroundLeafProof
  where

-- File Charter:
--   * Reduces the dedicated `gen⊑groundᵀ` continuation leaf to common
--     continuation-value terminal closing.
--   * Reconstructs the exact quotient constructor without inspecting or
--     replacing its proof-relevant final index.
--   * Contains no terminal implementation, postulate, hole, permissive
--     option, generic catch-all leaf, or broad simulation import.

import Coercions as C
open import NuTerms using (no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using (gen⊑groundᵀ)
open import
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationGenGroundLeafDef
  using (PairedLambdaTargetClosingContinuationGenGroundLeafᵀ)
open import
  proof.PairedLambda.Continuation.ValueTerminal.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalDef
  using (PairedLambdaTargetClosingContinuationValueTerminalᵀ)


paired-lambda-target-closing-continuation-gen-ground-leaf-proofᵀ :
  PairedLambdaTargetClosingContinuationValueTerminalᵀ →
  PairedLambdaTargetClosingContinuationGenGroundLeafᵀ
paired-lambda-target-closing-continuation-gen-ground-leaf-proofᵀ
    close {A = A} {c = c}
    mode seal★ c⊒ gH vV noV vW noW W⊢ V⊑Wtag q =
  close
    (vV ⟨ C.gen A c ⟩) (no•-⟨⟩ noV) vW noW
    (gen⊑groundᵀ mode seal★ c⊒ gH
      vV vW W⊢ V⊑Wtag q)
