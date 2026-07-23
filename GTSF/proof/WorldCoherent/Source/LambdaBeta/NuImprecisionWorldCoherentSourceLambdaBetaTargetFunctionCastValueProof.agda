module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastValueProof
  where

-- File Charter:
--   * Proves the five target function-cast value cases by contravariant
--     argument casting, inner scheduling, codomain framing, and `β-↦`.
--   * Takes inner lambda/function-cast scheduling as higher-order boundaries;
--     their well-founded assembly is deliberately separate.
--   * Contains no catch-all, postulate, hole, or permissive option.

import Coercions as C
import Conversion as CV
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl; suc-injective)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (trans)

open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
import NarrowWiden as NW
open import NuReduction using (keep; pure-step)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ; seal★-tag-or-id)
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; Value
  ; ok-⟨⟩
  ; ok-·₂
  ; ƛ_
  ; _·_
  ; _⟨_⟩
  ; _[_]
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; nu-term-imprecision-target-typing
  ; nu-term-imprecision-source-typing
  ; prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (SealModeStore★; cast-tag-or-id; forget)
open import Types using (Ty; TyCtx; _⇒_)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef using
  (targetFunctionCastSpineRank)
open import proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureProof using
  (target-function-cast-spine-rank-unique)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastValueDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastRankedDef
  using
  ( WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ
  ; WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ
  )
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetLambdaDirectDef
  using (WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using
  ( WorldCoherentSourceOneStepTargetCastFrames
  ; sourceStepTargetConcealFrame
  ; sourceStepTargetIdWidenFrame
  ; sourceStepTargetNarrowFrame
  ; sourceStepTargetRevealFrame
  ; sourceStepTargetWidenFrame
  )
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependDef
  using (WorldCoherentSourceTargetKeepPrependᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; runtime-·₂; runtime-⟨⟩; value-runtime-No•)
open import proof.DGG.Core.NuProgress using
  (canonical-⇒; fv-ƛ; fv-↦)
open import proof.Core.Properties.TypePreservation using (seal★-weaken; term-weaken)


finish-inner-target-function-value-atᵀ :
  ∀ {n} →
  WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ n →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V W R′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((ƛ N) · V) →
  RuntimeOK (W · R′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ ƛ N ⊑ W
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  (vW : Value W) →
  targetFunctionCastSpineRank vW ≡ n →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V} {M′ = W · R′} {L = N [ V ]}
    {χ = keep} {ρ = ρ⁺} pB
finish-inner-target-function-value-atᵀ
    target-lambda target-function-cast
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW inner-rank
    with canonical-⇒ vW
      (forget (nu-term-imprecision-target-typing function-related))
finish-inner-target-function-value-atᵀ
    target-lambda target-function-cast
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW inner-rank
    | fv-ƛ refl =
  target-lambda prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV
finish-inner-target-function-value-atᵀ
    target-lambda target-function-cast
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW inner-rank
    | fv-↦ vU refl =
  target-function-cast prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vU
    (trans
      (target-function-cast-spine-rank-unique
        (vU ⟨ _ C.↦ _ ⟩) vW)
      inner-rank)


target-function-cast-value-suc-at-prefixᵀ :
  ∀ {n} →
  WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ n →
  WorldCoherentSourceOneStepTargetCastFrames →
  WorldCoherentSourceTargetKeepPrependᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V W V′ : Term} {c d : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ₀ →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((ƛ N) · V) →
  RuntimeOK ((W ⟨ c C.↦ d ⟩) · V′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ ƛ N ⊑ W ⟨ c C.↦ d ⟩
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  (vW : Value W) →
  Value V′ →
  suc (targetFunctionCastSpineRank vW) ≡ suc n →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V}
    {M′ = (W ⟨ c C.↦ d ⟩) · V′}
    {L = N [ V ]} {χ = keep} {ρ = ρ⁺} pB
target-function-cast-value-suc-at-prefixᵀ
    target-lambda target-function-cast target-frames prepend
    relation-prefix prefix coherent exclusive unique wfR okM okM′
    (allocation-prefixᵀ prefix₀ inner source⊢ target⊢)
    argument-related vV vW vV′ outer-rank =
  target-function-cast-value-suc-at-prefixᵀ
    target-lambda target-function-cast target-frames prepend
    (store-imp-prefix-transⁱ prefix₀ relation-prefix)
    prefix coherent exclusive unique wfR okM okM′ inner
    argument-related vV vW vV′ outer-rank
target-function-cast-value-suc-at-prefixᵀ
    target-lambda target-function-cast target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix prefix coherent exclusive unique wfR okM okM′
    (⊑cast⊒ᵀ {p = pA₀ ↦ pB₀} mode seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cʷ NW.↦ dⁿ)) inner .(pA ↦ pB))
    argument-related vV vW vV′ outer-rank =
  prepend (pure-step (NuReduction.β-↦ vW vV′))
    (sourceStepTargetNarrowFrame target-frames
      prefix mode seal★⁺ d⊒⁺ inner-result)
  where
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ = seal★-weaken right-incl seal★
  c⊑⁺ = NW.widen-weaken ≤-refl right-incl (c⊢ , cʷ)
  d⊒⁺ = NW.narrow-weaken ≤-refl right-incl (d⊢ , dⁿ)
  target-function-value = vW ⟨ _ C.↦ _ ⟩
  target-W-no =
    value-runtime-No• vW
      (runtime-⟨⟩ (runtime-·₁ okM′))
  target-argument-runtime =
    runtime-·₂ target-function-value okM′
  argument-cast =
    ⊑cast⊑ᵀ mode seal★⁺ c⊑⁺
      argument-related pA₀
  source-inner⊢⁺ =
    term-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion relation-prefix)
      (value-runtime-No• (ƛ _) (runtime-·₁ okM))
      (nu-term-imprecision-source-typing inner)
  target-inner⊢⁺ =
    term-weaken ≤-refl right-incl target-W-no
      (nu-term-imprecision-target-typing inner)
  inner⁺ =
    allocation-prefixᵀ relation-prefix inner
      source-inner⊢⁺ target-inner⊢⁺
  inner-result =
    finish-inner-target-function-value-atᵀ
      target-lambda target-function-cast
      prefix coherent exclusive unique wfR okM
      (ok-·₂ vW target-W-no (ok-⟨⟩ target-argument-runtime))
      inner⁺ argument-cast vV vW (suc-injective outer-rank)
target-function-cast-value-suc-at-prefixᵀ
    target-lambda target-function-cast target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix prefix coherent exclusive unique wfR okM okM′
    (⊑cast⊑ᵀ {p = pA₀ ↦ pB₀} mode seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ)) inner .(pA ↦ pB))
    argument-related vV vW vV′ outer-rank =
  prepend (pure-step (NuReduction.β-↦ vW vV′))
    (sourceStepTargetWidenFrame target-frames
      prefix mode seal★⁺ d⊑⁺ inner-result)
  where
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ = seal★-weaken right-incl seal★
  c⊒⁺ = NW.narrow-weaken ≤-refl right-incl (c⊢ , cⁿ)
  d⊑⁺ = NW.widen-weaken ≤-refl right-incl (d⊢ , dʷ)
  target-function-value = vW ⟨ _ C.↦ _ ⟩
  target-W-no =
    value-runtime-No• vW
      (runtime-⟨⟩ (runtime-·₁ okM′))
  target-argument-runtime =
    runtime-·₂ target-function-value okM′
  argument-cast =
    ⊑cast⊒ᵀ mode seal★⁺ c⊒⁺
      argument-related pA₀
  source-inner⊢⁺ =
    term-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion relation-prefix)
      (value-runtime-No• (ƛ _) (runtime-·₁ okM))
      (nu-term-imprecision-source-typing inner)
  target-inner⊢⁺ =
    term-weaken ≤-refl right-incl target-W-no
      (nu-term-imprecision-target-typing inner)
  inner⁺ =
    allocation-prefixᵀ relation-prefix inner
      source-inner⊢⁺ target-inner⊢⁺
  inner-result =
    finish-inner-target-function-value-atᵀ
      target-lambda target-function-cast
      prefix coherent exclusive unique wfR okM
      (ok-·₂ vW target-W-no (ok-⟨⟩ target-argument-runtime))
      inner⁺ argument-cast vV vW (suc-injective outer-rank)
target-function-cast-value-suc-at-prefixᵀ
    target-lambda target-function-cast target-frames prepend
    {ρ₀ = ρ₀} {pA = pA} {pB = pB}
    relation-prefix prefix coherent exclusive unique wfR okM okM′
    (⊑cast⊑idᵀ {p = pA₀ ↦ pB₀} seal★
      (C.cast-fun c⊢ d⊢ , NW.cross (cⁿ NW.↦ dʷ)) inner .(pA ↦ pB))
    argument-related vV vW vV′ outer-rank =
  prepend (pure-step (NuReduction.β-↦ vW vV′))
    (sourceStepTargetIdWidenFrame target-frames
      prefix seal★⁺ d⊑⁺ inner-result)
  where
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  seal★⁺ : SealModeStore★ C.id-onlyᵈ (rightStoreⁱ ρ₀)
  seal★⁺ =
    seal★-weaken {μ = C.id-onlyᵈ} right-incl seal★
  c⊒⁺ = NW.narrow-weaken ≤-refl right-incl (c⊢ , cⁿ)
  d⊑⁺ = NW.widen-weaken ≤-refl right-incl (d⊢ , dʷ)
  target-function-value = vW ⟨ _ C.↦ _ ⟩
  target-W-no =
    value-runtime-No• vW
      (runtime-⟨⟩ (runtime-·₁ okM′))
  target-argument-runtime =
    runtime-·₂ target-function-value okM′
  argument-cast =
    ⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
      (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ c⊒⁺)
      argument-related pA₀
  source-inner⊢⁺ =
    term-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion relation-prefix)
      (value-runtime-No• (ƛ _) (runtime-·₁ okM))
      (nu-term-imprecision-source-typing inner)
  target-inner⊢⁺ =
    term-weaken ≤-refl right-incl target-W-no
      (nu-term-imprecision-target-typing inner)
  inner⁺ =
    allocation-prefixᵀ relation-prefix inner
      source-inner⊢⁺ target-inner⊢⁺
  inner-result =
    finish-inner-target-function-value-atᵀ
      target-lambda target-function-cast
      prefix coherent exclusive unique wfR okM
      (ok-·₂ vW target-W-no (ok-⟨⟩ target-argument-runtime))
      inner⁺ argument-cast vV vW (suc-injective outer-rank)
target-function-cast-value-suc-at-prefixᵀ
    target-lambda target-function-cast target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix prefix coherent exclusive unique wfR okM okM′
    (⊑conv↑ᵀ {p = pA₀ ↦ pB₀}
      (CV.reveal-fun c↓ d↑) inner .(pA ↦ pB))
    argument-related vV vW vV′ outer-rank =
  prepend (pure-step (NuReduction.β-↦ vW vV′))
    (sourceStepTargetRevealFrame target-frames
      prefix d↑⁺ inner-result)
  where
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  c↓⁺ = CV.weaken-conceal-conversion right-incl c↓
  d↑⁺ = CV.weaken-reveal-conversion right-incl d↑
  target-function-value = vW ⟨ _ C.↦ _ ⟩
  target-W-no =
    value-runtime-No• vW
      (runtime-⟨⟩ (runtime-·₁ okM′))
  target-argument-runtime =
    runtime-·₂ target-function-value okM′
  argument-cast =
    ⊑conv↓ᵀ c↓⁺ argument-related pA₀
  source-inner⊢⁺ =
    term-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion relation-prefix)
      (value-runtime-No• (ƛ _) (runtime-·₁ okM))
      (nu-term-imprecision-source-typing inner)
  target-inner⊢⁺ =
    term-weaken ≤-refl right-incl target-W-no
      (nu-term-imprecision-target-typing inner)
  inner⁺ =
    allocation-prefixᵀ relation-prefix inner
      source-inner⊢⁺ target-inner⊢⁺
  inner-result =
    finish-inner-target-function-value-atᵀ
      target-lambda target-function-cast
      prefix coherent exclusive unique wfR okM
      (ok-·₂ vW target-W-no (ok-⟨⟩ target-argument-runtime))
      inner⁺ argument-cast vV vW (suc-injective outer-rank)
target-function-cast-value-suc-at-prefixᵀ
    target-lambda target-function-cast target-frames prepend
    {pA = pA} {pB = pB}
    relation-prefix prefix coherent exclusive unique wfR okM okM′
    (⊑conv↓ᵀ {p = pA₀ ↦ pB₀}
      (CV.conceal-fun c↑ d↓) inner .(pA ↦ pB))
    argument-related vV vW vV′ outer-rank =
  prepend (pure-step (NuReduction.β-↦ vW vV′))
    (sourceStepTargetConcealFrame target-frames
      prefix d↓⁺ inner-result)
  where
  right-incl = rightStoreⁱ-prefix-inclusion relation-prefix
  c↑⁺ = CV.weaken-reveal-conversion right-incl c↑
  d↓⁺ = CV.weaken-conceal-conversion right-incl d↓
  target-function-value = vW ⟨ _ C.↦ _ ⟩
  target-W-no =
    value-runtime-No• vW
      (runtime-⟨⟩ (runtime-·₁ okM′))
  target-argument-runtime =
    runtime-·₂ target-function-value okM′
  argument-cast =
    ⊑conv↑ᵀ c↑⁺ argument-related pA₀
  source-inner⊢⁺ =
    term-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion relation-prefix)
      (value-runtime-No• (ƛ _) (runtime-·₁ okM))
      (nu-term-imprecision-source-typing inner)
  target-inner⊢⁺ =
    term-weaken ≤-refl right-incl target-W-no
      (nu-term-imprecision-target-typing inner)
  inner⁺ =
    allocation-prefixᵀ relation-prefix inner
      source-inner⊢⁺ target-inner⊢⁺
  inner-result =
    finish-inner-target-function-value-atᵀ
      target-lambda target-function-cast
      prefix coherent exclusive unique wfR okM
      (ok-·₂ vW target-W-no (ok-⟨⟩ target-argument-runtime))
      inner⁺ argument-cast vV vW (suc-injective outer-rank)


world-coherent-source-lambda-beta-target-function-cast-value-suc-at-proofᵀ :
  ∀ {n} →
  WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ n →
  WorldCoherentSourceOneStepTargetCastFrames →
  WorldCoherentSourceTargetKeepPrependᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ (suc n)
world-coherent-source-lambda-beta-target-function-cast-value-suc-at-proofᵀ
    target-lambda target-function-cast target-frames prepend
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vV′ outer-rank =
  target-function-cast-value-suc-at-prefixᵀ
    target-lambda target-function-cast target-frames prepend
    prefix-reflⁱ prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vV′ outer-rank


world-coherent-source-lambda-beta-target-function-cast-value-proofᵀ :
  WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ →
  WorldCoherentSourceOneStepTargetCastFrames →
  WorldCoherentSourceTargetKeepPrependᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ
world-coherent-source-lambda-beta-target-function-cast-value-proofᵀ
    target-lambda target-function-cast target-frames prepend
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vV′ =
  world-coherent-source-lambda-beta-target-function-cast-value-suc-at-proofᵀ
    target-lambda target-function-cast-at target-frames prepend
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vV′ refl
  where
  target-function-cast-at :
    WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ
      (targetFunctionCastSpineRank vW)
  target-function-cast-at prefix₁ coherent₁ exclusive₁ unique₁ wfR₁
      okM₁ okM′₁ function-related₁ argument-related₁ vV₁ vW₁
      rank-eq =
    target-function-cast prefix₁ coherent₁ exclusive₁ unique₁ wfR₁
      okM₁ okM′₁ function-related₁ argument-related₁ vV₁ vW₁
