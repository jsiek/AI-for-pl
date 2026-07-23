module
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationHandlersAssemblyProof
  where

-- File Charter:
--   * Assembles the thirteen independently stated continuation semantic
--     capabilities into the exact record consumed by the continuation
--     interpreter.
--   * Provides one strict fit check across all four leaves, five source
--     frames, and four paired or quotient frames.
--   * Contains no semantic implementation, postulate, hole, permissive
--     option, target-only frame capability, or canonical `Lemma` assembly.

open import
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationGenNuLeafDef
  using (PairedLambdaTargetClosingContinuationGenNuLeafᵀ)
open import
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationHandlersDef
  using
  ( PairedLambdaTargetClosingContinuationHandlers
  ; handle-frame-cast⊒⊑
  ; handle-frame-cast⊑⊑
  ; handle-frame-conv↑⊑
  ; handle-frame-conv↓⊑
  ; handle-frame-gen-all
  ; handle-frame-paired-conversion
  ; handle-frame-paired-widening
  ; handle-frame-up-gen-all
  ; handle-frame-up-id
  ; handle-leaf-gen-ν
  ; handle-leaf-up-gen
  ; handle-leaf-Λ
  ; handle-leaf-ΛΛ
  )
open import
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationLambdaLambdaLeafDef
  using (PairedLambdaTargetClosingContinuationLambdaLambdaLeafᵀ)
open import
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationLambdaLeafDef
  using (PairedLambdaTargetClosingContinuationLambdaLeafᵀ)
open import
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationPairedConversionFrameDef
  using (PairedLambdaTargetClosingContinuationPairedConversionFrameᵀ)
open import
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationPairedWideningFrameDef
  using (PairedLambdaTargetClosingContinuationPairedWideningFrameᵀ)
open import
  proof.PairedLambda.Continuation.SourceAll.NuImprecisionPairedLambdaTargetClosingContinuationSourceAllConcealFrameDef
  using (PairedLambdaTargetClosingContinuationSourceAllConcealFrameᵀ)
open import
  proof.PairedLambda.Continuation.SourceAll.NuImprecisionPairedLambdaTargetClosingContinuationSourceAllNarrowingFrameDef
  using (PairedLambdaTargetClosingContinuationSourceAllNarrowingFrameᵀ)
open import
  proof.PairedLambda.Continuation.SourceAll.NuImprecisionPairedLambdaTargetClosingContinuationSourceAllRevealFrameDef
  using (PairedLambdaTargetClosingContinuationSourceAllRevealFrameᵀ)
open import
  proof.PairedLambda.Continuation.SourceAll.NuImprecisionPairedLambdaTargetClosingContinuationSourceAllWideningFrameDef
  using (PairedLambdaTargetClosingContinuationSourceAllWideningFrameᵀ)
open import
  proof.PairedLambda.Continuation.Frames.NuImprecisionPairedLambdaTargetClosingContinuationSourceGenFrameDef
  using (PairedLambdaTargetClosingContinuationSourceGenFrameᵀ)
open import
  proof.PairedLambda.Continuation.Frames.NuImprecisionPairedLambdaTargetClosingContinuationUpGenAllFrameDef
  using (PairedLambdaTargetClosingContinuationUpGenAllFrameᵀ)
open import
  proof.PairedLambda.Continuation.Frames.NuImprecisionPairedLambdaTargetClosingContinuationUpGenLeafDef
  using (PairedLambdaTargetClosingContinuationUpGenLeafᵀ)
open import
  proof.PairedLambda.Continuation.Frames.NuImprecisionPairedLambdaTargetClosingContinuationUpIdFrameDef
  using (PairedLambdaTargetClosingContinuationUpIdFrameᵀ)


paired-lambda-target-closing-continuation-handlers-assembly-proofᵀ :
  PairedLambdaTargetClosingContinuationLambdaLambdaLeafᵀ →
  PairedLambdaTargetClosingContinuationLambdaLeafᵀ →
  PairedLambdaTargetClosingContinuationGenNuLeafᵀ →
  PairedLambdaTargetClosingContinuationUpGenLeafᵀ →
  PairedLambdaTargetClosingContinuationSourceGenFrameᵀ →
  PairedLambdaTargetClosingContinuationSourceAllNarrowingFrameᵀ →
  PairedLambdaTargetClosingContinuationSourceAllWideningFrameᵀ →
  PairedLambdaTargetClosingContinuationSourceAllRevealFrameᵀ →
  PairedLambdaTargetClosingContinuationSourceAllConcealFrameᵀ →
  PairedLambdaTargetClosingContinuationPairedConversionFrameᵀ →
  PairedLambdaTargetClosingContinuationPairedWideningFrameᵀ →
  PairedLambdaTargetClosingContinuationUpIdFrameᵀ →
  PairedLambdaTargetClosingContinuationUpGenAllFrameᵀ →
  PairedLambdaTargetClosingContinuationHandlers
paired-lambda-target-closing-continuation-handlers-assembly-proofᵀ
    lambda-lambda lambda gen-ν up-gen source-gen source-all-narrowing
    source-all-widening source-all-reveal source-all-conceal
    paired-conversion paired-widening up-id up-gen-all =
  record
    { handle-leaf-ΛΛ = lambda-lambda
    ; handle-leaf-Λ = lambda
    ; handle-leaf-gen-ν = gen-ν
    ; handle-leaf-up-gen = up-gen
    ; handle-frame-gen-all = source-gen
    ; handle-frame-cast⊒⊑ = source-all-narrowing
    ; handle-frame-cast⊑⊑ = source-all-widening
    ; handle-frame-conv↑⊑ = source-all-reveal
    ; handle-frame-conv↓⊑ = source-all-conceal
    ; handle-frame-paired-conversion = paired-conversion
    ; handle-frame-paired-widening = paired-widening
    ; handle-frame-up-id = up-id
    ; handle-frame-up-gen-all = up-gen-all
    }
