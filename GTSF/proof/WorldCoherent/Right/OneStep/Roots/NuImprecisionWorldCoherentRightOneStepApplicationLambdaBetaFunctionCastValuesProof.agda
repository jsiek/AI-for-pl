module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesProof
  where

-- File Charter:
--   * Proves the caught source-function-cast versus target-lambda beta cell
--     from the recursive smaller-function scheduler.
--   * Distributes the source function coercion, recursively handles the
--     target beta step, frames the codomain cast or conversion, and prepends
--     source `β-↦`.
--   * Removes proof-only allocation prefixes while retaining exact cast
--     shapes, composition triangles, replacements, and store lineage.
--   * Contains no recursive definition, postulate, hole, permissive option,
--     catch-all, or compatibility wrapper.

import Coercions as C
import Conversion as CV
import NarrowWiden as NW
open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using (shape-fun)
open import ConversionIndexCompatibility using (replace-left-function)
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionComposition using (comp-↦-↦)
open import ImprecisionWf using
  ( _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( β-↦
  ; keep
  ; pure-step
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-·
  ; no•-⟨⟩
  ; ok-no
  ; ƛ_
  ; _·_
  ; _⟨_⟩
  ; _[_]
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; prefix-reflⁱ
  ; ·⊑·ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.DGG.Core.NuPreservation using
  (value-runtime-No•)
open import proof.Core.Properties.NuRuntimeProperties using
  (runtime-·₁; runtime-·₂)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import
  proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof
  using (quotiented-store-prefix-no-bullet-proofᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentSourceKeepOutcomeComposition
  using (world-coherent-source-keep-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesDef
  using
  ( WorldCoherentRightOneStepSourceCastFrames
  ; rightStepSourceNarrowFrame
  ; rightStepSourceWidenFrame
  )
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesDef
  using
  ( WorldCoherentRightOneStepSourceConversionFrames
  ; rightStepSourceConcealFrame
  ; rightStepSourceRevealFrame
  )
open import
  proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef
  using (targetFunctionCastSpineRank)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRankedDef
  using
  ( WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesAtᵀ
  ; WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueAtᵀ
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV


world-coherent-right-one-step-application-lambda-beta-function-cast-values-at-proofᵀ :
  ∀ {n} →
  WorldCoherentRightOneStepSourceCastFrames →
  WorldCoherentRightOneStepSourceConversionFrames →
  WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueAtᵀ n →
  WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesAtᵀ n
world-coherent-right-one-step-application-lambda-beta-function-cast-values-at-proofᵀ
    {n}
    cast-frames conversion-frames recursive =
  at-prefix prefix-reflⁱ
  where
  at-prefix :
    ∀ {Φ} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {V W N′ V′ : Term} {c d : C.Coercion}
      {A A′ B B′ : Ty}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    StoreImpPrefix ρᵇ ρ →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
    RuntimeOK ((ƛ N′) · V′) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ V ⟨ c C.↦ d ⟩ ⊑ ƛ N′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ W ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
    (vV : Value V) →
    Value W →
    Value V′ →
    targetFunctionCastSpineRank vV ≡ n →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (V ⟨ c C.↦ d ⟩) · W} {N′ = N′ [ V′ ]}
      {χ = keep} {ρ = ρ} pB
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (cast⊒⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
        (C.cast-fun c⊢ d⊢ , NW.cross (cʷ NW.↦ dⁿ))
        inner .(pA ↦ pB)
        (shape-fun c-shape d-shape)
        (comp-↦-↦ c-comp d-comp))
      argument-related vV vW vV′ rank =
    world-coherent-source-keep-then-outcomeᵀ
      final-runtime final-related
      (pure-step (β-↦ vV vW))
      (rightStepSourceNarrowFrame cast-frames
        mode seal★⁺ d⊒⁺ d-shape d-comp recursive-outcome)
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ = seal★-weaken left-incl seal★
    c⊑⁺ = NW.widen-weaken ≤-refl left-incl (c⊢ , cʷ)
    d⊒⁺ = NW.narrow-weaken ≤-refl left-incl (d⊢ , dⁿ)
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    source-W-no =
      value-runtime-No• vW (runtime-·₂ (vV ⟨ _ C.↦ _ ⟩) okM)
    target-function-no =
      value-runtime-No• (ƛ _) (runtime-·₁ okM′)
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-function-no inner
    argument-cast =
      cast⊑⊑ᵀ mode seal★⁺ c⊑⁺ argument-related pA₀
        c-shape c-comp
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      cast⊒⊑ᵀ mode seal★⁺ d⊒⁺ application-related pB
        d-shape d-comp
    inner-runtime =
      ok-no (no•-· source-V-no (no•-⟨⟩ source-W-no))
    final-runtime =
      ok-no (no•-⟨⟩ (no•-· source-V-no (no•-⟨⟩ source-W-no)))
    recursive-outcome =
      recursive
        coherent exclusive unique wfL inner-runtime okM′
        inner⁺ argument-cast vV vV′ rank
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (cast⊑⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
        (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
        inner .(pA ↦ pB)
        (shape-fun c-shape d-shape)
        (comp-↦-↦ c-comp d-comp))
      argument-related vV vW vV′ rank =
    world-coherent-source-keep-then-outcomeᵀ
      final-runtime final-related
      (pure-step (β-↦ vV vW))
      (rightStepSourceWidenFrame cast-frames
        mode seal★⁺ d⊑⁺ d-shape d-comp recursive-outcome)
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ = seal★-weaken left-incl seal★
    c⊒⁺ = NW.narrow-weaken ≤-refl left-incl (c⊢ , cⁿ)
    d⊑⁺ = NW.widen-weaken ≤-refl left-incl (d⊢ , dʷ)
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    source-W-no =
      value-runtime-No• vW (runtime-·₂ (vV ⟨ _ C.↦ _ ⟩) okM)
    target-function-no =
      value-runtime-No• (ƛ _) (runtime-·₁ okM′)
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-function-no inner
    argument-cast =
      cast⊒⊑ᵀ mode seal★⁺ c⊒⁺ argument-related pA₀
        c-shape c-comp
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      cast⊑⊑ᵀ mode seal★⁺ d⊑⁺ application-related pB
        d-shape d-comp
    inner-runtime =
      ok-no (no•-· source-V-no (no•-⟨⟩ source-W-no))
    final-runtime =
      ok-no (no•-⟨⟩ (no•-· source-V-no (no•-⟨⟩ source-W-no)))
    recursive-outcome =
      recursive
        coherent exclusive unique wfL inner-runtime okM′
        inner⁺ argument-cast vV vV′ rank
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (conv↑⊑ᵀ {p = pA₀ ↦ pB₀}
        (CV.reveal-fun c↓ d↑) inner .(pA ↦ pB)
        (replace-left-function c-replace d-replace))
      argument-related vV vW vV′ rank =
    world-coherent-source-keep-then-outcomeᵀ
      final-runtime final-related
      (pure-step (β-↦ vV vW))
      (rightStepSourceRevealFrame conversion-frames
        d↑⁺ d-replace recursive-outcome)
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    c↓⁺ = CV.weaken-conceal-conversion left-incl c↓
    d↑⁺ = CV.weaken-reveal-conversion left-incl d↑
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    source-W-no =
      value-runtime-No• vW (runtime-·₂ (vV ⟨ _ C.↦ _ ⟩) okM)
    target-function-no =
      value-runtime-No• (ƛ _) (runtime-·₁ okM′)
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-function-no inner
    argument-cast =
      conv↓⊑ᵀ c↓⁺ argument-related pA₀ c-replace
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      conv↑⊑ᵀ d↑⁺ application-related pB d-replace
    inner-runtime =
      ok-no (no•-· source-V-no (no•-⟨⟩ source-W-no))
    final-runtime =
      ok-no (no•-⟨⟩ (no•-· source-V-no (no•-⟨⟩ source-W-no)))
    recursive-outcome =
      recursive
        coherent exclusive unique wfL inner-runtime okM′
        inner⁺ argument-cast vV vV′ rank
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (conv↓⊑ᵀ {p = pA₀ ↦ pB₀}
        (CV.conceal-fun c↑ d↓) inner .(pA ↦ pB)
        (replace-left-function c-replace d-replace))
      argument-related vV vW vV′ rank =
    world-coherent-source-keep-then-outcomeᵀ
      final-runtime final-related
      (pure-step (β-↦ vV vW))
      (rightStepSourceConcealFrame conversion-frames
        d↓⁺ d-replace recursive-outcome)
    where
    left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
    c↑⁺ = CV.weaken-reveal-conversion left-incl c↑
    d↓⁺ = CV.weaken-conceal-conversion left-incl d↓
    source-function-no =
      value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
    source-V-no = cast-value-body-No• source-function-no
    source-W-no =
      value-runtime-No• vW (runtime-·₂ (vV ⟨ _ C.↦ _ ⟩) okM)
    target-function-no =
      value-runtime-No• (ƛ _) (runtime-·₁ okM′)
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-V-no target-function-no inner
    argument-cast =
      conv↑⊑ᵀ c↑⁺ argument-related pA₀ c-replace
    application-related = ·⊑·ᵀ inner⁺ argument-cast
    final-related =
      conv↓⊑ᵀ d↓⁺ application-related pB d-replace
    inner-runtime =
      ok-no (no•-· source-V-no (no•-⟨⟩ source-W-no))
    final-runtime =
      ok-no (no•-⟨⟩ (no•-· source-V-no (no•-⟨⟩ source-W-no)))
    recursive-outcome =
      recursive
        coherent exclusive unique wfL inner-runtime okM′
        inner⁺ argument-cast vV vV′ rank
