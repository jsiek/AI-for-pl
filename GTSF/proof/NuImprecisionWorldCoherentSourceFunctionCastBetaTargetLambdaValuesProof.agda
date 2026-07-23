module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetLambdaValuesProof
  where

-- File Charter:
--   * Proves the target-lambda value/value terminal by structurally removing
--     proof-only function-relation prefixes and then distributing the
--     one-sided source function coercion.
--   * Accumulates the relation-store prefix explicitly and weakens only the
--     leaf coercion evidence and inner relation.
--   * Contains no target reduction, catch-all, postulate, hole, or permissive
--     option.

import Coercions as C
import Conversion as CV
import NarrowWiden as NW
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)

open import ImprecisionWf using
  (_↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using (β-↦; keep; pure-step)
open import NuTermImprecision using
  (StoreImp)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-⟨⟩
  ; ƛ_
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; prefix-reflⁱ
  ; ·⊑·ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; _⇒_)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; store-imp-prefix-transⁱ)
open import proof.NuImprecisionStorePrefixNoBulletProof using
  (quotiented-store-prefix-no-bullet-proofᵀ)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetLambdaValuesDef
  using (WorldCoherentSourceFunctionCastBetaTargetLambdaValuesᵀ)
open import proof.NuImprecisionWorldCoherentSourceKeepRelationLemma using
  (world-coherent-source-keep-relationᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import proof.NuPreservation using
  (runtime-·₁; runtime-·₂; value-runtime-No•)
open import proof.TypePreservation using
  (seal★-weaken)


private
  cast-value-body-No• :
    ∀ {V c} →
    No• (V ⟨ c ⟩) →
    No• V
  cast-value-body-No• (no•-⟨⟩ noV) = noV


target-lambda-values-at-prefixᵀ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W N′ R′ : Term} {c d : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK ((ƛ N′) · R′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ V ⟨ c C.↦ d ⟩ ⊑ ƛ N′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value W →
  Value R′ →
  WorldCoherentSourceOneStepIndexedResult
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = (ƛ N′) · R′}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {A = B} {B = B′} {χ = keep} {ρ = ρ} pB
target-lambda-values-at-prefixᵀ
    relation-prefix coherent exclusive unique okM okM′
    (allocation-prefixᵀ prefix₀ inner source⊢ target⊢)
    argument-related vV vW vR′ =
  target-lambda-values-at-prefixᵀ
    (store-imp-prefix-transⁱ prefix₀ relation-prefix)
    coherent exclusive unique okM okM′ inner
    argument-related vV vW vR′
target-lambda-values-at-prefixᵀ
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique okM okM′
    (cast⊒⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cʷ NW.↦ dⁿ))
      inner .(pA ↦ pB))
    argument-related vV vW vR′ =
  world-coherent-source-keep-relationᵀ
    coherent exclusive unique final-related
    (pure-step (β-↦ vV vW))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ = seal★-weaken left-incl seal★
  c⊑⁺ = NW.widen-weaken ≤-refl left-incl (c⊢ , cʷ)
  d⊒⁺ = NW.narrow-weaken ≤-refl left-incl (d⊢ , dⁿ)
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-no =
    value-runtime-No• (ƛ _) (runtime-·₁ okM′)
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-function-no inner
  argument-cast =
    cast⊑⊑ᵀ mode seal★⁺ c⊑⁺ argument-related pA₀
  application-related = ·⊑·ᵀ inner⁺ argument-cast
  final-related =
    cast⊒⊑ᵀ mode seal★⁺ d⊒⁺ application-related pB
target-lambda-values-at-prefixᵀ
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique okM okM′
    (cast⊑⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ))
      inner .(pA ↦ pB))
    argument-related vV vW vR′ =
  world-coherent-source-keep-relationᵀ
    coherent exclusive unique final-related
    (pure-step (β-↦ vV vW))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ = seal★-weaken left-incl seal★
  c⊒⁺ = NW.narrow-weaken ≤-refl left-incl (c⊢ , cⁿ)
  d⊑⁺ = NW.widen-weaken ≤-refl left-incl (d⊢ , dʷ)
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-no =
    value-runtime-No• (ƛ _) (runtime-·₁ okM′)
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-function-no inner
  argument-cast =
    cast⊒⊑ᵀ mode seal★⁺ c⊒⁺ argument-related pA₀
  application-related = ·⊑·ᵀ inner⁺ argument-cast
  final-related =
    cast⊑⊑ᵀ mode seal★⁺ d⊑⁺ application-related pB
target-lambda-values-at-prefixᵀ
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique okM okM′
    (conv↑⊑ᵀ {p = pA₀ ↦ pB₀}
      (CV.reveal-fun c↓ d↑) inner .(pA ↦ pB))
    argument-related vV vW vR′ =
  world-coherent-source-keep-relationᵀ
    coherent exclusive unique final-related
    (pure-step (β-↦ vV vW))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  c↓⁺ = CV.weaken-conceal-conversion left-incl c↓
  d↑⁺ = CV.weaken-reveal-conversion left-incl d↑
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-no =
    value-runtime-No• (ƛ _) (runtime-·₁ okM′)
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-function-no inner
  argument-cast = conv↓⊑ᵀ c↓⁺ argument-related pA₀
  application-related = ·⊑·ᵀ inner⁺ argument-cast
  final-related = conv↑⊑ᵀ d↑⁺ application-related pB
target-lambda-values-at-prefixᵀ
    {pA = pA} {pB = pB}
    relation-prefix coherent exclusive unique okM okM′
    (conv↓⊑ᵀ {p = pA₀ ↦ pB₀}
      (CV.conceal-fun c↑ d↓) inner .(pA ↦ pB))
    argument-related vV vW vR′ =
  world-coherent-source-keep-relationᵀ
    coherent exclusive unique final-related
    (pure-step (β-↦ vV vW))
  where
  left-incl = leftStoreⁱ-prefix-inclusion relation-prefix
  c↑⁺ = CV.weaken-reveal-conversion left-incl c↑
  d↓⁺ = CV.weaken-conceal-conversion left-incl d↓
  source-function-no =
    value-runtime-No• (vV ⟨ _ C.↦ _ ⟩) (runtime-·₁ okM)
  source-V-no = cast-value-body-No• source-function-no
  target-function-no =
    value-runtime-No• (ƛ _) (runtime-·₁ okM′)
  inner⁺ =
    quotiented-store-prefix-no-bullet-proofᵀ
      relation-prefix source-V-no target-function-no inner
  argument-cast = conv↑⊑ᵀ c↑⁺ argument-related pA₀
  application-related = ·⊑·ᵀ inner⁺ argument-cast
  final-related = conv↓⊑ᵀ d↓⁺ application-related pB


world-coherent-source-function-cast-beta-target-lambda-values-proofᵀ :
  WorldCoherentSourceFunctionCastBetaTargetLambdaValuesᵀ
world-coherent-source-function-cast-beta-target-lambda-values-proofᵀ
    coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vR′ =
  target-lambda-values-at-prefixᵀ
    prefix-reflⁱ coherent exclusive unique okM okM′
    function-related argument-related vV vW vR′
