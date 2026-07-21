module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationHandlersAssemblyProof
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
  proof.NuImprecisionPairedLambdaTargetClosingContinuationGenNuLeafDef
  using (PairedLambdaTargetClosingContinuationGenNuLeafᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationHandlersDef
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
  proof.NuImprecisionPairedLambdaTargetClosingContinuationLambdaLambdaLeafDef
  using (PairedLambdaTargetClosingContinuationLambdaLambdaLeafᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationLambdaLeafDef
  using (PairedLambdaTargetClosingContinuationLambdaLeafᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationPairedConversionFrameDef
  using (PairedLambdaTargetClosingContinuationPairedConversionFrameᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationPairedWideningFrameDef
  using (PairedLambdaTargetClosingContinuationPairedWideningFrameᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationSourceAllConcealFrameDef
  using (PairedLambdaTargetClosingContinuationSourceAllConcealFrameᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationSourceAllNarrowingFrameDef
  using (PairedLambdaTargetClosingContinuationSourceAllNarrowingFrameᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationSourceAllRevealFrameDef
  using (PairedLambdaTargetClosingContinuationSourceAllRevealFrameᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationSourceAllWideningFrameDef
  using (PairedLambdaTargetClosingContinuationSourceAllWideningFrameᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationSourceGenFrameDef
  using (PairedLambdaTargetClosingContinuationSourceGenFrameᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationUpGenAllFrameDef
  using (PairedLambdaTargetClosingContinuationUpGenAllFrameᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationUpGenLeafDef
  using (PairedLambdaTargetClosingContinuationUpGenLeafᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationUpIdFrameDef
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
