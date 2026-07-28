module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesProof
  where

-- File Charter:
--   * Proves target function-cast beta when the caught source function is an
--     ordinary lambda and both arguments are values.
--   * Distributes each reachable target-only function cast with zero source
--     steps after removing proof-only allocation prefixes.
--   * Contains no recursion, postulate, hole, permissive option, catch-all,
--     or compatibility wrapper.

import Coercions as C
import Conversion as CV
import NarrowWiden as NW
open import CastImprecisionShape using (shape-fun)
open import ConversionIndexCompatibility using (replace-right-function)
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionComposition using (comp-↦-↦)
open import ImprecisionWf using
  ( ImpCtx
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; Value
  ; ƛ_
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ·⊑·ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.DGG.Core.NuPreservation using
  (value-runtime-No•)
open import proof.Core.Properties.NuRuntimeProperties using
  (runtime-·₁; runtime-⟨⟩)
open import proof.OneStep.NuImprecisionOneStepRelated using
  (weak-one-step-indexed-relatedᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.Prefix.NuImprecisionStorePrefix
  using
  ( rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import
  proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof
  using (quotiented-store-prefix-no-bullet-proofᵀ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaDef
  using
  (WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ)
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  )


private
  related-outcome :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = M′} {χ = keep} {ρ = ρ} p
  related-outcome coherent exclusive unique relation =
    world-indexed-outcome-related
      (weak-one-step-indexed-relatedᵀ relation)
      (weak-step-store-lineage
        _ rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent exclusive unique


world-coherent-right-one-step-application-function-cast-beta-lambda-values-proofᵀ :
  WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ
world-coherent-right-one-step-application-function-cast-beta-lambda-values-proofᵀ =
  at-prefix prefix-reflⁱ
  where
  at-prefix :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {N M V′ W′ : Term} {e f : C.Coercion}
      {A A′ B B′ : Ty}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    StoreImpPrefix ρᵇ ρ →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    RuntimeOK ((ƛ N) · M) →
    RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ ƛ N ⊑ V′ ⟨ e C.↦ f ⟩
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ W′ ⦂ A ⊑ A′ ∶ pA →
    Value M →
    Value V′ →
    Value W′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (ƛ N) · M}
      {N′ = (V′ · (W′ ⟨ e ⟩)) ⟨ f ⟩}
      {χ = keep} {ρ = ρ} pB
  at-prefix relation-prefix coherent exclusive unique wfL okM okM′
      (allocation-prefixᵀ prefix₀ inner source⊢ target⊢)
      argument-related vM vV′ vW′ =
    at-prefix
      (store-imp-prefix-transⁱ prefix₀ relation-prefix)
      coherent exclusive unique wfL okM okM′
      inner argument-related vM vV′ vW′
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (⊑cast⊒ᵀ {p = pA₀ ↦ pB₀} mode seal★
        (C.cast-fun e⊢ f⊢ , NW.cross (eʷ NW.↦ fⁿ))
        inner .(pA ↦ pB)
        (shape-fun e-shape f-shape)
        (comp-↦-↦ e-comp f-comp))
      argument-related vM vV′ vW′ =
    related-outcome coherent exclusive unique final-related
    where
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ = seal★-weaken right-incl seal★
    e⊑⁺ = NW.widen-weaken ≤-refl right-incl (e⊢ , eʷ)
    f⊒⁺ = NW.narrow-weaken ≤-refl right-incl (f⊢ , fⁿ)
    source-function-no =
      value-runtime-No• (ƛ _) (runtime-·₁ okM)
    target-V-no =
      value-runtime-No• vV′ (runtime-⟨⟩ (runtime-·₁ okM′))
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-function-no target-V-no inner
    argument-cast =
      ⊑cast⊑ᵀ mode seal★⁺ e⊑⁺ argument-related pA₀
        e-shape e-comp
    final-related =
      ⊑cast⊒ᵀ mode seal★⁺ f⊒⁺
        (·⊑·ᵀ inner⁺ argument-cast) pB f-shape f-comp
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (⊑cast⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
        (C.cast-fun e⊢ f⊢ , NW.cross (eⁿ NW.↦ fʷ))
        inner .(pA ↦ pB)
        (shape-fun e-shape f-shape)
        (comp-↦-↦ e-comp f-comp))
      argument-related vM vV′ vW′ =
    related-outcome coherent exclusive unique final-related
    where
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    seal★⁺ = seal★-weaken right-incl seal★
    e⊒⁺ = NW.narrow-weaken ≤-refl right-incl (e⊢ , eⁿ)
    f⊑⁺ = NW.widen-weaken ≤-refl right-incl (f⊢ , fʷ)
    source-function-no =
      value-runtime-No• (ƛ _) (runtime-·₁ okM)
    target-V-no =
      value-runtime-No• vV′ (runtime-⟨⟩ (runtime-·₁ okM′))
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-function-no target-V-no inner
    argument-cast =
      ⊑cast⊒ᵀ mode seal★⁺ e⊒⁺ argument-related pA₀
        e-shape e-comp
    final-related =
      ⊑cast⊑ᵀ mode seal★⁺ f⊑⁺
        (·⊑·ᵀ inner⁺ argument-cast) pB f-shape f-comp
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (⊑conv↑ᵀ {p = pA₀ ↦ pB₀}
        (CV.reveal-fun e↓ f↑) inner .(pA ↦ pB)
        (replace-right-function e-replace f-replace))
      argument-related vM vV′ vW′ =
    related-outcome coherent exclusive unique final-related
    where
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    e↓⁺ = CV.weaken-conceal-conversion right-incl e↓
    f↑⁺ = CV.weaken-reveal-conversion right-incl f↑
    source-function-no =
      value-runtime-No• (ƛ _) (runtime-·₁ okM)
    target-V-no =
      value-runtime-No• vV′ (runtime-⟨⟩ (runtime-·₁ okM′))
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-function-no target-V-no inner
    argument-cast =
      ⊑conv↓ᵀ e↓⁺ argument-related pA₀ e-replace
    final-related =
      ⊑conv↑ᵀ f↑⁺
        (·⊑·ᵀ inner⁺ argument-cast) pB f-replace
  at-prefix
      {pA = pA} {pB = pB}
      relation-prefix coherent exclusive unique wfL okM okM′
      (⊑conv↓ᵀ {p = pA₀ ↦ pB₀}
        (CV.conceal-fun e↑ f↓) inner .(pA ↦ pB)
        (replace-right-function e-replace f-replace))
      argument-related vM vV′ vW′ =
    related-outcome coherent exclusive unique final-related
    where
    right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
    e↑⁺ = CV.weaken-reveal-conversion right-incl e↑
    f↓⁺ = CV.weaken-conceal-conversion right-incl f↓
    source-function-no =
      value-runtime-No• (ƛ _) (runtime-·₁ okM)
    target-V-no =
      value-runtime-No• vV′ (runtime-⟨⟩ (runtime-·₁ okM′))
    inner⁺ =
      quotiented-store-prefix-no-bullet-proofᵀ
        relation-prefix source-function-no target-V-no inner
    argument-cast =
      ⊑conv↑ᵀ e↑⁺ argument-related pA₀ e-replace
    final-related =
      ⊑conv↓ᵀ f↓⁺
        (·⊑·ᵀ inner⁺ argument-cast) pB f-replace
