module
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationHandlersAssemblyProof
  where

-- File Charter:
--   * Assembles the fifteen independently stated continuation semantic
--     capabilities into the exact record consumed by the continuation
--     interpreter.
--   * Provides one strict fit check across all six leaves, five source
--     frames, and four paired or quotient frames.
--   * Requires the fused instantiation-beta leaf as an explicit higher-order
--     capability, leaving its semantic proof to the next layer.
--   * Contains no semantic implementation, postulate, hole, permissive
--     option, target-only frame capability, or canonical `Lemma` assembly.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; inst
  )
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Imprecision using (⇑ᴿᵢ)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  ( Closedᵐ
  ; No•
  ; Term
  ; Value
  ; Λ_
  ; _⟨_⟩
  ; renameᵗᵐ
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Renameᵗ
  ; Ty
  ; TyCtx
  ; renameᵗ
  ; wf★
  ; ★
  ; `∀
  ; ⇑ᵗ
  )
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (rename-assm²ᵢ)
open import
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationGenGroundLeafDef
  using (PairedLambdaTargetClosingContinuationGenGroundLeafᵀ)
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
  ; handle-leaf-gen-ground
  ; handle-leaf-gen-ν
  ; handle-leaf-instβ
  ; handle-leaf-up-gen
  ; handle-leaf-Λ
  ; handle-leaf-ΛΛ
  )
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)
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
  (inst-beta :
      ∀ {Φ Φ₀ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
        {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          (suc Θᴸ) (suc Θᴿ)}
        {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
        {τ σ : Renameᵗ}
        {W W′ M M′ : Term}
        {A′ B C D F : Ty}
        {s : Coercion} {μ : ModeEnv} {r} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Θᴿ ∣ rightStoreⁱ ρ₀
      ⊢ inst B s ∶ `∀ C ⊑ B →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀) ρ₀ ρ∀ →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ₀) ρ⁺ ρᴿ⁺ →
    Value W →
    No• W →
    Value W′ →
    No• W′ →
    Inert s →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
      ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ∀ ∣ []
      ⊢ᴺ W ⊑ W′ ⦂ D ⊑ C ∶ r →
    (f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ) →
    (assm :
      ∀ {a} → a ∈ ⇑ᴿᵢ Φ₀ →
        rename-assm²ᵢ τ σ a ∈ Φ) →
    (hτ : TyRenameWf Θᴸ Δᴸ τ) →
    (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ) →
    RelStoreEmbeddingⁱ τ σ
      (store-right zero ★ wf★ ∷ ρᴿ⁺) ρ →
    renameᵗᵐ τ (Λ W) ≡ M →
    renameᵗᵐ σ (W′ ⟨ s ⟩) ≡ M′ →
    renameᵗ τ (`∀ D) ≡ `∀ F →
    renameᵗ σ (⇑ᵗ B) ≡ A′ →
    (p : Φ ∣ Δᴸ ⊢ `∀ F ⊑ A′ ⊣ Δᴿ) →
    Value M →
    No• M →
    Closedᵐ M →
    Value M′ →
    No• M′ →
    Closedᵐ M′ →
    Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ `∀ F →
    Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ A′ →
    PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
      M M′ F A′ p) →
  PairedLambdaTargetClosingContinuationLambdaLambdaLeafᵀ →
  PairedLambdaTargetClosingContinuationLambdaLeafᵀ →
  PairedLambdaTargetClosingContinuationGenNuLeafᵀ →
  PairedLambdaTargetClosingContinuationGenGroundLeafᵀ →
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
    inst-beta lambda-lambda lambda gen-ν gen-ground up-gen
    source-gen source-all-narrowing
    source-all-widening source-all-reveal source-all-conceal
    paired-conversion paired-widening up-id up-gen-all =
  record
    { handle-leaf-ΛΛ = lambda-lambda
    ; handle-leaf-Λ = lambda
    ; handle-leaf-instβ = inst-beta
    ; handle-leaf-gen-ν = gen-ν
    ; handle-leaf-gen-ground = gen-ground
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
