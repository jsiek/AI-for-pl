module
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingProof
  where

-- File Charter:
--   * Reduces structural source-generic paired-reveal closing to the exact
--     generic narrowing constructor core.
--   * Uses the QTI source-typing projection and exhaustively eliminates all
--     refined typing alternatives incompatible with a generic cast.
--   * Contains no postulate, hole, permissive option, broad simulation
--     import, recursive frame closer, or source-only rotation.

import Coercions as C
open import Data.Product using (_,_)
import NarrowWiden as NW
open import QuotientedTermImprecision using
  (nu-term-imprecision-source-typing)
open import TermTyping using
  ( ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  )
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreDef
  using
    (PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingDef
  using (PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ)


paired-lambda-target-closing-source-gen-frame-structural-reveal-closing-proofᵀ
  :
  PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreᵀ →
  PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ
paired-lambda-target-closing-source-gen-frame-structural-reveal-closing-proofᵀ
    core {q = q} {r = r} {p = p} {pX = pX}
    vV noV vN′ noN′ relation framed
    inner prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    corresponds
    source-reveal target-reveal
    with nu-term-imprecision-source-typing framed
paired-lambda-target-closing-source-gen-frame-structural-reveal-closing-proofᵀ
    core {q = q} {r = r} {p = p} {pX = pX}
    vV noV vN′ noN′ relation framed
    inner prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    corresponds
    source-reveal target-reveal
    | ⊢⟨⟩↑ () V⊢
paired-lambda-target-closing-source-gen-frame-structural-reveal-closing-proofᵀ
    core {q = q} {r = r} {p = p} {pX = pX}
    vV noV vN′ noN′ relation framed
    inner prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    corresponds
    source-reveal target-reveal
    | ⊢⟨⟩↓ () V⊢
paired-lambda-target-closing-source-gen-frame-structural-reveal-closing-proofᵀ
    core {q = q} {r = r} {p = p} {pX = pX}
    vV noV vN′ noN′ relation framed
    inner prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    corresponds
    source-reveal target-reveal
    | ⊢⟨⟩⊒ mode seal★
        (C.cast-gen h∀F occ-B g⊢ , NW.gen gⁿ) V⊢ =
  core {q = q} {r = r} {p = p} {pX = pX}
    vV noV vN′ noN′ relation mode seal★ h∀F occ-B g⊢ gⁿ
    inner prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    corresponds
    source-reveal target-reveal
paired-lambda-target-closing-source-gen-frame-structural-reveal-closing-proofᵀ
    core {q = q} {r = r} {p = p} {pX = pX}
    vV noV vN′ noN′ relation framed
    inner prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    corresponds
    source-reveal target-reveal
    | ⊢⟨⟩⊑ mode seal★ (_ , NW.cross ()) V⊢
