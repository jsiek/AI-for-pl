module
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingGenGroundLeafClosingProof
  where

-- File Charter:
--   * Reduces the dedicated `gen⊑groundᵀ` terminal leaf to source-only
--     `ν` terminal closing.
--   * Splits all three ground shapes explicitly; each forces the final
--     universal-source imprecision index to be `ν`.
--   * Contains no terminal implementation, postulate, hole, permissive
--     option, generic catch-all leaf, or broad simulation import.

import Coercions as C
open import Coercions using (_!)
open import ImprecisionWf using (ν)
open import NuTerms using (no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using (gen⊑groundᵀ)
open import Types using (★⇒★; ＇_; ‵_)
open import
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingGenGroundLeafClosingDef
  using (PairedLambdaTargetClosingGenGroundLeafClosingᵀ)
open import
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingNuTerminalDef
  using (PairedLambdaTargetClosingNuTerminalᵀ)


paired-lambda-target-closing-gen-ground-leaf-closing-proofᵀ :
  PairedLambdaTargetClosingNuTerminalᵀ →
  PairedLambdaTargetClosingGenGroundLeafClosingᵀ
paired-lambda-target-closing-gen-ground-leaf-closing-proofᵀ
    close {A = A} {c = c}
    mode seal★ c⊒ (＇ α) vV noV vW noW W⊢ V⊑Wtag
    (ν safe occ r) =
  close {{safe = safe}}
    (vV ⟨ C.gen A c ⟩) (no•-⟨⟩ noV) vW noW
    (gen⊑groundᵀ mode seal★ c⊒ (＇ α)
      vV vW W⊢ V⊑Wtag (ν safe occ r))
paired-lambda-target-closing-gen-ground-leaf-closing-proofᵀ
    close {A = A} {c = c}
    mode seal★ c⊒ (‵ ι) vV noV vW noW W⊢ V⊑Wtag
    (ν safe occ r) =
  close {{safe = safe}}
    (vV ⟨ C.gen A c ⟩) (no•-⟨⟩ noV) vW noW
    (gen⊑groundᵀ mode seal★ c⊒ (‵ ι)
      vV vW W⊢ V⊑Wtag (ν safe occ r))
paired-lambda-target-closing-gen-ground-leaf-closing-proofᵀ
    close {A = A} {c = c}
    mode seal★ c⊒ ★⇒★ vV noV vW noW W⊢ V⊑Wtag
    (ν safe occ r) =
  close {{safe = safe}}
    (vV ⟨ C.gen A c ⟩) (no•-⟨⟩ noV) vW noW
    (gen⊑groundᵀ mode seal★ c⊒ ★⇒★
      vV vW W⊢ V⊑Wtag (ν safe occ r))
